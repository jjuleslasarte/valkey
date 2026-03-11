/* helloheaders.c -- A reference module demonstrating RESP4 request header APIs.
 *
 * This module:
 * 1. Registers a "trace-id" request header
 * 2. Uses a command filter to capture the trace-id and attach it as
 *    commandlog (slowlog) metadata via VM_CommandFilterSetCommandlogMetadata
 * 3. Provides HEADERS.ECHO to echo back all request headers
 * 4. Provides HEADERS.TRACEID to return the trace-id header value
 * 5. Provides HEADERS.EXISTS <name> to check if a header exists
 * 6. Provides HEADERS.GETLL <name> to get a header as a long long
 *
 * Copyright (c) Valkey Contributors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "../../src/valkeymodule.h"
#include <string.h>
#include <strings.h>

#define TRACE_ID_HEADER "trace-id"

/* Command filter callback — runs before every command.
 * If a trace-id header is present, attach it as commandlog metadata
 * so it appears in SLOWLOG / COMMANDLOG entries. */
void TraceIdCommandFilter(ValkeyModuleCommandFilterCtx *fctx) {
    ValkeyModuleString *trace_id =
        ValkeyModule_CommandFilterGetRequestHeader(fctx, TRACE_ID_HEADER);
    if (trace_id) {
        ValkeyModule_CommandFilterSetCommandlogMetadata(
            fctx, TRACE_ID_HEADER, trace_id);
    }
}

/* HEADERS.ECHO — echo all request headers back to the client as a map.
 * Useful for testing RESP4 header parsing and module API. */
int HeadersEchoCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    VALKEYMODULE_NOT_USED(argv);
    VALKEYMODULE_NOT_USED(argc);

    ValkeyModuleRequestHeaderIter *iter =
        ValkeyModule_RequestHeaderIterStart(ctx);
    if (!iter) {
        ValkeyModule_ReplyWithEmptyArray(ctx);
        return VALKEYMODULE_OK;
    }

    ValkeyModule_ReplyWithArray(ctx, VALKEYMODULE_POSTPONED_LEN);
    ValkeyModuleString *name, *value;
    long count = 0;
    while (ValkeyModule_RequestHeaderIterNext(iter, &name, &value)) {
        ValkeyModule_ReplyWithString(ctx, name);
        ValkeyModule_ReplyWithString(ctx, value);
        count++;
    }
    ValkeyModule_RequestHeaderIterStop(iter);
    ValkeyModule_ReplySetArrayLength(ctx, count * 2);
    return VALKEYMODULE_OK;
}

/* HEADERS.TRACEID — return the trace-id from the current request, or nil. */
int HeadersTraceIdCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    VALKEYMODULE_NOT_USED(argv);
    VALKEYMODULE_NOT_USED(argc);

    ValkeyModuleString *trace_id =
        ValkeyModule_GetRequestHeader(ctx, TRACE_ID_HEADER);
    if (trace_id) {
        ValkeyModule_ReplyWithString(ctx, trace_id);
    } else {
        ValkeyModule_ReplyWithNull(ctx);
    }
    return VALKEYMODULE_OK;
}

/* HEADERS.EXISTS <name> — check if a header exists, return 1 or 0. */
int HeadersExistsCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    if (argc != 2) return ValkeyModule_WrongArity(ctx);

    const char *name = ValkeyModule_StringPtrLen(argv[1], NULL);
    int exists = ValkeyModule_RequestHeaderExists(ctx, name);
    ValkeyModule_ReplyWithLongLong(ctx, exists ? 1 : 0);
    return VALKEYMODULE_OK;
}

/* HEADERS.GETLL <name> — get a header value as a long long, or error. */
int HeadersGetLLCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    if (argc != 2) return ValkeyModule_WrongArity(ctx);

    const char *name = ValkeyModule_StringPtrLen(argv[1], NULL);
    long long ll;
    if (ValkeyModule_GetRequestHeaderLongLong(ctx, name, &ll) == VALKEYMODULE_OK) {
        ValkeyModule_ReplyWithLongLong(ctx, ll);
    } else {
        ValkeyModule_ReplyWithNull(ctx);
    }
    return VALKEYMODULE_OK;
}

/* Module initialization. */
int ValkeyModule_OnLoad(ValkeyModuleCtx *ctx, ValkeyModuleString **argv,
                        int argc) {
    VALKEYMODULE_NOT_USED(argv);
    VALKEYMODULE_NOT_USED(argc);

    if (ValkeyModule_Init(ctx, "helloheaders", 1,
                          VALKEYMODULE_APIVER_1) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    /* Register the trace-id header. -1 means any type. */
    if (ValkeyModule_RegisterRequestHeader(
            ctx, TRACE_ID_HEADER, 0, -1) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    /* Register command filter to capture trace-id for commandlog. */
    ValkeyModule_RegisterCommandFilter(ctx, TraceIdCommandFilter, 0);

    /* Register commands. */
    if (ValkeyModule_CreateCommand(ctx, "headers.echo",
            HeadersEchoCommand, "fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "headers.traceid",
            HeadersTraceIdCommand, "fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "headers.exists",
            HeadersExistsCommand, "fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "headers.getll",
            HeadersGetLLCommand, "fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    return VALKEYMODULE_OK;
}
