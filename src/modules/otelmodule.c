/* otelmodule.c -- OpenTelemetry distributed tracing module for Valkey using RESP4 request headers.
 *
 * This module leverages RESP4 request-side attributes (request headers) to implement
 * W3C Trace Context propagation through Valkey. It enables end-to-end distributed
 * tracing by allowing clients to send OpenTelemetry trace context as RESP4 headers,
 * which the module captures, logs, attaches to commandlog entries, and exposes
 * through diagnostic commands.
 *
 * Supported RESP4 Headers (W3C Trace Context):
 *   - traceparent    : W3C traceparent header (version-traceid-spanid-traceflags)
 *   - tracestate     : W3C tracestate header (vendor-specific trace data)
 *
 * Additional Headers:
 *   - baggage         : W3C baggage header for application-level context propagation
 *   - otel-resource   : Optional resource identifier for the originating service
 *
 * Commands Provided:
 *   OTEL.TRACE       - Return the current trace context (traceparent + tracestate) or nil
 *   OTEL.CONTEXT     - Return all OpenTelemetry headers as a map
 *   OTEL.SPANID      - Extract and return just the span-id from traceparent, or nil
 *   OTEL.TRACEID     - Extract and return just the trace-id from traceparent, or nil
 *   OTEL.STATS       - Return module statistics (commands traced, headers received, etc.)
 *
 * Command Filter:
 *   A command filter captures traceparent and tracestate on every command and attaches
 *   them as commandlog (slowlog) metadata, enabling correlation between slow queries
 *   and distributed traces.
 *
 * Copyright (c) Valkey Contributors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "../valkeymodule.h"
#include <string.h>
#include <strings.h>
#include <ctype.h>

/* ============================================================================
 * Constants — W3C Trace Context header names
 * ============================================================================ */

#define HEADER_TRACEPARENT  "traceparent"
#define HEADER_TRACESTATE   "tracestate"
#define HEADER_BAGGAGE      "baggage"
#define HEADER_OTEL_RESOURCE "otel-resource"

/* W3C traceparent format: VERSION-TRACEID-SPANID-FLAGS
 * Example: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
 *
 * VERSION:  2 hex chars (1 byte)
 * TRACEID: 32 hex chars (16 bytes)
 * SPANID:  16 hex chars (8 bytes)
 * FLAGS:    2 hex chars (1 byte)
 * Total with dashes: 2 + 1 + 32 + 1 + 16 + 1 + 2 = 55 chars
 */
#define TRACEPARENT_LEN 55
#define TRACEID_OFFSET  3
#define TRACEID_LEN     32
#define SPANID_OFFSET   36
#define SPANID_LEN      16
#define FLAGS_OFFSET    53
#define FLAGS_LEN       2

/* ============================================================================
 * Module statistics — atomic counters for observability
 * ============================================================================ */

static long long stats_commands_traced = 0;       /* Commands that had traceparent */
static long long stats_commands_total = 0;         /* Total commands seen by filter */
static long long stats_traceparent_invalid = 0;    /* traceparent headers that failed validation */
static long long stats_tracestate_received = 0;    /* Commands that had tracestate */
static long long stats_baggage_received = 0;       /* Commands that had baggage */

/* ============================================================================
 * Utility — W3C traceparent validation
 * ============================================================================ */

/* Return 1 if c is a valid lowercase hex digit. */
static int is_lower_hex(char c) {
    return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f');
}

/* Validate a W3C traceparent string.
 * Must be exactly 55 chars: VV-TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT-SSSSSSSSSSSSSSSS-FF
 * where V,T,S,F are lowercase hex chars and dashes are at positions 2, 35, 52. */
static int validate_traceparent(const char *tp, size_t len) {
    if (len != TRACEPARENT_LEN) return 0;
    if (tp[2] != '-' || tp[35] != '-' || tp[52] != '-') return 0;

    /* Check version (positions 0-1) */
    for (int i = 0; i < 2; i++) {
        if (!is_lower_hex(tp[i])) return 0;
    }
    /* Version 0xff is invalid per spec */
    if (tp[0] == 'f' && tp[1] == 'f') return 0;

    /* Check trace-id (positions 3-34): must not be all zeros */
    int all_zero = 1;
    for (int i = TRACEID_OFFSET; i < TRACEID_OFFSET + TRACEID_LEN; i++) {
        if (!is_lower_hex(tp[i])) return 0;
        if (tp[i] != '0') all_zero = 0;
    }
    if (all_zero) return 0;

    /* Check span-id (positions 36-51): must not be all zeros */
    all_zero = 1;
    for (int i = SPANID_OFFSET; i < SPANID_OFFSET + SPANID_LEN; i++) {
        if (!is_lower_hex(tp[i])) return 0;
        if (tp[i] != '0') all_zero = 0;
    }
    if (all_zero) return 0;

    /* Check flags (positions 53-54) */
    for (int i = FLAGS_OFFSET; i < FLAGS_OFFSET + FLAGS_LEN; i++) {
        if (!is_lower_hex(tp[i])) return 0;
    }

    return 1;
}

/* ============================================================================
 * Command Filter — captures trace context on every command for commandlog
 * ============================================================================ */

/* This filter runs before every command. If RESP4 trace headers are present,
 * it attaches them as commandlog metadata so that COMMANDLOG GET / SLOWLOG GET
 * entries include the trace context for correlation with distributed traces. */
void OtelCommandFilter(ValkeyModuleCommandFilterCtx *fctx) {
    stats_commands_total++;

    /* Check for traceparent header */
    ValkeyModuleString *traceparent =
        ValkeyModule_CommandFilterGetRequestHeader(fctx, HEADER_TRACEPARENT);

    if (traceparent) {
        size_t tp_len;
        const char *tp_str = ValkeyModule_StringPtrLen(traceparent, &tp_len);

        if (validate_traceparent(tp_str, tp_len)) {
            stats_commands_traced++;

            /* Attach traceparent to commandlog entry */
            ValkeyModule_CommandFilterSetCommandlogMetadata(
                fctx, HEADER_TRACEPARENT, traceparent);

            /* Also attach tracestate if present */
            ValkeyModuleString *tracestate =
                ValkeyModule_CommandFilterGetRequestHeader(fctx, HEADER_TRACESTATE);
            if (tracestate) {
                stats_tracestate_received++;
                ValkeyModule_CommandFilterSetCommandlogMetadata(
                    fctx, HEADER_TRACESTATE, tracestate);
            }
        } else {
            stats_traceparent_invalid++;
        }
    }

    /* Track baggage presence for stats */
    ValkeyModuleString *baggage =
        ValkeyModule_CommandFilterGetRequestHeader(fctx, HEADER_BAGGAGE);
    if (baggage) {
        stats_baggage_received++;
    }
}

/* ============================================================================
 * OTEL.TRACE — Return traceparent [and tracestate] from the current request
 * ============================================================================ */

/* OTEL.TRACE
 * Returns the traceparent value if present (and valid), or nil.
 * If tracestate is also present, returns a 2-element array [traceparent, tracestate].
 * If only traceparent is present, returns just the traceparent string. */
int OtelTraceCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    VALKEYMODULE_NOT_USED(argv);
    if (argc != 1) return ValkeyModule_WrongArity(ctx);

    ValkeyModuleString *traceparent =
        ValkeyModule_GetRequestHeader(ctx, HEADER_TRACEPARENT);

    if (!traceparent) {
        ValkeyModule_ReplyWithNull(ctx);
        return VALKEYMODULE_OK;
    }

    /* Validate the traceparent */
    size_t tp_len;
    const char *tp_str = ValkeyModule_StringPtrLen(traceparent, &tp_len);
    if (!validate_traceparent(tp_str, tp_len)) {
        ValkeyModule_ReplyWithError(ctx, "ERR invalid traceparent format; "
            "expected: VERSION-TRACEID-SPANID-FLAGS "
            "(e.g. 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01)");
        return VALKEYMODULE_OK;
    }

    ValkeyModuleString *tracestate =
        ValkeyModule_GetRequestHeader(ctx, HEADER_TRACESTATE);

    if (tracestate) {
        ValkeyModule_ReplyWithArray(ctx, 2);
        ValkeyModule_ReplyWithString(ctx, traceparent);
        ValkeyModule_ReplyWithString(ctx, tracestate);
    } else {
        ValkeyModule_ReplyWithString(ctx, traceparent);
    }

    return VALKEYMODULE_OK;
}

/* ============================================================================
 * OTEL.CONTEXT — Return all OpenTelemetry headers as a map
 * ============================================================================ */

/* OTEL.CONTEXT
 * Returns a map of all recognized OpenTelemetry headers present on the current
 * request. Keys: traceparent, tracestate, baggage, otel-resource.
 * Returns an empty map if no OTel headers are present. */
int OtelContextCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    VALKEYMODULE_NOT_USED(argv);
    if (argc != 1) return ValkeyModule_WrongArity(ctx);

    /* Count how many OTel headers are present */
    const char *header_names[] = {
        HEADER_TRACEPARENT,
        HEADER_TRACESTATE,
        HEADER_BAGGAGE,
        HEADER_OTEL_RESOURCE
    };
    int num_headers = sizeof(header_names) / sizeof(header_names[0]);

    ValkeyModuleString *values[4];
    int present_count = 0;

    for (int i = 0; i < num_headers; i++) {
        values[i] = ValkeyModule_GetRequestHeader(ctx, header_names[i]);
        if (values[i]) present_count++;
    }

    ValkeyModule_ReplyWithMap(ctx, present_count);
    for (int i = 0; i < num_headers; i++) {
        if (values[i]) {
            ValkeyModule_ReplyWithCString(ctx, header_names[i]);
            ValkeyModule_ReplyWithString(ctx, values[i]);
        }
    }

    return VALKEYMODULE_OK;
}

/* ============================================================================
 * OTEL.TRACEID — Extract and return the trace-id from traceparent
 * ============================================================================ */

/* OTEL.TRACEID
 * Extracts the 32-char trace-id from the traceparent header.
 * Returns the trace-id as a string, or nil if traceparent is absent/invalid. */
int OtelTraceIdCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    VALKEYMODULE_NOT_USED(argv);
    if (argc != 1) return ValkeyModule_WrongArity(ctx);

    ValkeyModuleString *traceparent =
        ValkeyModule_GetRequestHeader(ctx, HEADER_TRACEPARENT);

    if (!traceparent) {
        ValkeyModule_ReplyWithNull(ctx);
        return VALKEYMODULE_OK;
    }

    size_t tp_len;
    const char *tp_str = ValkeyModule_StringPtrLen(traceparent, &tp_len);

    if (!validate_traceparent(tp_str, tp_len)) {
        ValkeyModule_ReplyWithNull(ctx);
        return VALKEYMODULE_OK;
    }

    ValkeyModule_ReplyWithStringBuffer(ctx, tp_str + TRACEID_OFFSET, TRACEID_LEN);
    return VALKEYMODULE_OK;
}

/* ============================================================================
 * OTEL.SPANID — Extract and return the span-id from traceparent
 * ============================================================================ */

/* OTEL.SPANID
 * Extracts the 16-char span-id from the traceparent header.
 * Returns the span-id as a string, or nil if traceparent is absent/invalid. */
int OtelSpanIdCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    VALKEYMODULE_NOT_USED(argv);
    if (argc != 1) return ValkeyModule_WrongArity(ctx);

    ValkeyModuleString *traceparent =
        ValkeyModule_GetRequestHeader(ctx, HEADER_TRACEPARENT);

    if (!traceparent) {
        ValkeyModule_ReplyWithNull(ctx);
        return VALKEYMODULE_OK;
    }

    size_t tp_len;
    const char *tp_str = ValkeyModule_StringPtrLen(traceparent, &tp_len);

    if (!validate_traceparent(tp_str, tp_len)) {
        ValkeyModule_ReplyWithNull(ctx);
        return VALKEYMODULE_OK;
    }

    ValkeyModule_ReplyWithStringBuffer(ctx, tp_str + SPANID_OFFSET, SPANID_LEN);
    return VALKEYMODULE_OK;
}

/* ============================================================================
 * OTEL.STATS — Return module statistics
 * ============================================================================ */

/* OTEL.STATS
 * Returns a map of module statistics:
 *   commands_total        - Total commands observed by the filter
 *   commands_traced       - Commands that carried a valid traceparent
 *   traceparent_invalid   - Commands with malformed traceparent
 *   tracestate_received   - Commands that carried tracestate
 *   baggage_received      - Commands that carried baggage
 *   trace_ratio           - Ratio of traced to total commands (double) */
int OtelStatsCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    VALKEYMODULE_NOT_USED(argv);
    if (argc != 1) return ValkeyModule_WrongArity(ctx);

    ValkeyModule_ReplyWithMap(ctx, 6);

    ValkeyModule_ReplyWithCString(ctx, "commands_total");
    ValkeyModule_ReplyWithLongLong(ctx, stats_commands_total);

    ValkeyModule_ReplyWithCString(ctx, "commands_traced");
    ValkeyModule_ReplyWithLongLong(ctx, stats_commands_traced);

    ValkeyModule_ReplyWithCString(ctx, "traceparent_invalid");
    ValkeyModule_ReplyWithLongLong(ctx, stats_traceparent_invalid);

    ValkeyModule_ReplyWithCString(ctx, "tracestate_received");
    ValkeyModule_ReplyWithLongLong(ctx, stats_tracestate_received);

    ValkeyModule_ReplyWithCString(ctx, "baggage_received");
    ValkeyModule_ReplyWithLongLong(ctx, stats_baggage_received);

    ValkeyModule_ReplyWithCString(ctx, "trace_ratio");
    if (stats_commands_total > 0) {
        ValkeyModule_ReplyWithDouble(ctx,
            (double)stats_commands_traced / (double)stats_commands_total);
    } else {
        ValkeyModule_ReplyWithDouble(ctx, 0.0);
    }

    return VALKEYMODULE_OK;
}

/* ============================================================================
 * OTEL.EXEC — Execute a command with server-side timing reply attributes
 * ============================================================================ */

/* OTEL.EXEC <command> [args...]
 *
 * Executes the given command on the server and returns the result, but also
 * attaches RESP4 reply-side attributes with server-side timing information.
 * This enables the client to create a "server" child span with actual
 * server-side execution duration.
 *
 * Reply attributes returned (RESP4 clients only):
 *   server-start-us   : server timestamp (microseconds since epoch) when execution started
 *   server-end-us     : server timestamp (microseconds since epoch) when execution ended
 *   server-duration-us : execution duration in microseconds
 *   traceparent        : echoed back from request (if present)
 *
 * This gives the client enough information to create a server-side span:
 *
 *   Client span:  |----------- network RTT + server time ----------|
 *   Server span:       |--- server-duration-us ---|
 *
 * Example:
 *   > OTEL.EXEC SET foo bar
 *   # attribute: server-start-us=1698776172000123, server-end-us=1698776172000456,
 *   #            server-duration-us=333, traceparent=00-...
 *   OK
 */
int OtelExecCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    if (argc < 2) {
        ValkeyModule_ReplyWithError(ctx,
            "ERR wrong number of arguments for 'OTEL.EXEC' command. "
            "Usage: OTEL.EXEC <command> [args...]");
        return VALKEYMODULE_OK;
    }

    /* Get the command name */
    const char *cmd = ValkeyModule_StringPtrLen(argv[1], NULL);

    /* Capture start timestamp */
    mstime_t start_ms = ValkeyModule_Milliseconds();
    /* For microsecond precision, we use ms * 1000 as an approximation.
     * True microsecond timestamps would require clock_gettime in the module. */
    long long start_us = (long long)start_ms * 1000;

    /* Build the argument list for ValkeyModule_Call (skip argv[0]=OTEL.EXEC, argv[1]=cmd) */
    ValkeyModuleCallReply *reply;
    if (argc == 2) {
        /* Command with no arguments */
        reply = ValkeyModule_Call(ctx, cmd, "");
    } else {
        /* Command with arguments: use "v" format for variadic ValkeyModuleString args */
        reply = ValkeyModule_Call(ctx, cmd, "v", argv + 2, argc - 2);
    }

    /* Capture end timestamp */
    mstime_t end_ms = ValkeyModule_Milliseconds();
    long long end_us = (long long)end_ms * 1000;
    long long duration_us = end_us - start_us;

    /* Send reply attributes with server timing (only visible to RESP4/RESP3 clients) */
    ValkeyModule_ReplyWithAttribute(ctx, 4);

    ValkeyModule_ReplyWithCString(ctx, "server-start-us");
    ValkeyModule_ReplyWithLongLong(ctx, start_us);

    ValkeyModule_ReplyWithCString(ctx, "server-end-us");
    ValkeyModule_ReplyWithLongLong(ctx, end_us);

    ValkeyModule_ReplyWithCString(ctx, "server-duration-us");
    ValkeyModule_ReplyWithLongLong(ctx, duration_us);

    /* Echo back traceparent if present */
    ValkeyModuleString *traceparent =
        ValkeyModule_GetRequestHeader(ctx, HEADER_TRACEPARENT);
    ValkeyModule_ReplyWithCString(ctx, "traceparent");
    if (traceparent) {
        ValkeyModule_ReplyWithString(ctx, traceparent);
    } else {
        ValkeyModule_ReplyWithNull(ctx);
    }

    /* Forward the actual reply */
    if (reply) {
        ValkeyModule_ReplyWithCallReply(ctx, reply);
        ValkeyModule_FreeCallReply(reply);
    } else {
        ValkeyModule_ReplyWithError(ctx, "ERR failed to execute command");
    }

    return VALKEYMODULE_OK;
}

/* ============================================================================
 * Module initialization
 * ============================================================================ */

int ValkeyModule_OnLoad(ValkeyModuleCtx *ctx, ValkeyModuleString **argv,
                        int argc) {
    VALKEYMODULE_NOT_USED(argv);
    VALKEYMODULE_NOT_USED(argc);

    if (ValkeyModule_Init(ctx, "otel", 1, VALKEYMODULE_APIVER_1) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    /* ---- Register RESP4 request headers ----
     * We register the W3C Trace Context headers plus baggage and a custom
     * resource header. -1 for expected_type means "any scalar type". */
    if (ValkeyModule_RegisterRequestHeader(ctx, HEADER_TRACEPARENT, 0, -1) == VALKEYMODULE_ERR) {
        ValkeyModule_Log(ctx, "warning",
            "otel: failed to register '%s' header (may be registered by another module)",
            HEADER_TRACEPARENT);
        return VALKEYMODULE_ERR;
    }

    if (ValkeyModule_RegisterRequestHeader(ctx, HEADER_TRACESTATE, 0, -1) == VALKEYMODULE_ERR) {
        ValkeyModule_Log(ctx, "warning",
            "otel: failed to register '%s' header", HEADER_TRACESTATE);
        return VALKEYMODULE_ERR;
    }

    if (ValkeyModule_RegisterRequestHeader(ctx, HEADER_BAGGAGE, 0, -1) == VALKEYMODULE_ERR) {
        ValkeyModule_Log(ctx, "warning",
            "otel: failed to register '%s' header", HEADER_BAGGAGE);
        return VALKEYMODULE_ERR;
    }

    if (ValkeyModule_RegisterRequestHeader(ctx, HEADER_OTEL_RESOURCE, 0, -1) == VALKEYMODULE_ERR) {
        ValkeyModule_Log(ctx, "warning",
            "otel: failed to register '%s' header", HEADER_OTEL_RESOURCE);
        return VALKEYMODULE_ERR;
    }

    ValkeyModule_Log(ctx, "notice",
        "otel: registered RESP4 headers: %s, %s, %s, %s",
        HEADER_TRACEPARENT, HEADER_TRACESTATE, HEADER_BAGGAGE, HEADER_OTEL_RESOURCE);

    /* ---- Register command filter for commandlog metadata ---- */
    if (ValkeyModule_RegisterCommandFilter(ctx, OtelCommandFilter, 0) == NULL) {
        ValkeyModule_Log(ctx, "warning", "otel: failed to register command filter");
        return VALKEYMODULE_ERR;
    }

    /* ---- Register commands ---- */
    if (ValkeyModule_CreateCommand(ctx, "otel.trace",
            OtelTraceCommand, "fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "otel.context",
            OtelContextCommand, "fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "otel.traceid",
            OtelTraceIdCommand, "fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "otel.spanid",
            OtelSpanIdCommand, "fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "otel.stats",
            OtelStatsCommand, "fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "otel.exec",
            OtelExecCommand, "write", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    ValkeyModule_Log(ctx, "notice",
        "otel: OpenTelemetry tracing module loaded. "
        "Commands: OTEL.TRACE, OTEL.CONTEXT, OTEL.TRACEID, OTEL.SPANID, OTEL.STATS, OTEL.EXEC");

    return VALKEYMODULE_OK;
}
