/* idempotency.c -- Idempotency Token module for Valkey using RESP4 request headers.
 *
 * This module implements idempotent command execution using RESP4 request-side
 * attributes. Clients send an `idempotency-token` header with write commands,
 * and the module ensures each token is executed at most once:
 *
 *   - If the token is NEW:    execute the command, cache token -> result, return result
 *   - If the token is CACHED: skip execution, return the previously cached result
 *
 * Supported RESP4 Headers:
 *   - idempotency-token     : Unique token string (UUID, timestamp, etc). Max 128 bytes. Required.
 *   - idempotency-namespace : Logical namespace for token isolation. Default: "default".
 *   - idempotency-ttl       : Token retention in seconds (integer). Default: 86400 (24h).
 *
 * Commands Provided:
 *   IDEMPOTENT.EXEC <command> [args...]  - Execute a command idempotently using the token header
 *   IDEMPOTENT.INFO <token>              - Return info about a stored token
 *   IDEMPOTENT.INVALIDATE <token>        - Remove a token, allowing re-execution
 *   IDEMPOTENT.STATS                     - Return module statistics
 *   IDEMPOTENT.FLUSH [namespace]         - Remove all stored tokens (or all in a namespace)
 *
 * Token Storage:
 *   Tokens are stored in Valkey hashes: __idempotency:{namespace}
 *   A companion sorted set __idempotency_ttl:{namespace} tracks expiration times.
 *
 * Copyright (c) Valkey Contributors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "../valkeymodule.h"
#include <string.h>
#include <strings.h>
#include <stdlib.h>
#include <ctype.h>
#include <time.h>

/* ============================================================================
 * Constants
 * ============================================================================ */

#define HEADER_IDEMPOTENCY_TOKEN     "idempotency-token"
#define HEADER_IDEMPOTENCY_NAMESPACE "idempotency-namespace"
#define HEADER_IDEMPOTENCY_TTL       "idempotency-ttl"

#define DEFAULT_NAMESPACE   "default"
#define DEFAULT_TTL_SECONDS 86400  /* 24 hours */
#define MAX_TOKEN_LEN       128
#define CLEANUP_INTERVAL_MS 60000  /* Run cleanup every 60 seconds */

/* Key prefixes for internal storage */
#define HASH_PREFIX     "__idempotency:"
#define TTL_SET_PREFIX  "__idempotency_ttl:"

/* ============================================================================
 * Module statistics
 * ============================================================================ */

static long long stats_cache_hits = 0;
static long long stats_cache_misses = 0;
static long long stats_tokens_stored = 0;
static long long stats_tokens_expired = 0;
static long long stats_tokens_invalidated = 0;
static long long stats_exec_errors = 0;

/* Timer for periodic cleanup */
static ValkeyModuleTimerID cleanup_timer_id = 0;

/* ============================================================================
 * Utility functions
 * ============================================================================ */

/* Build the hash key name: __idempotency:{namespace} */
static ValkeyModuleString *build_hash_key(ValkeyModuleCtx *ctx, const char *ns) {
    char buf[256];
    snprintf(buf, sizeof(buf), "%s%s", HASH_PREFIX, ns);
    return ValkeyModule_CreateString(ctx, buf, strlen(buf));
}

/* Build the TTL sorted set key: __idempotency_ttl:{namespace} */
static ValkeyModuleString *build_ttl_key(ValkeyModuleCtx *ctx, const char *ns) {
    char buf[256];
    snprintf(buf, sizeof(buf), "%s%s", TTL_SET_PREFIX, ns);
    return ValkeyModule_CreateString(ctx, buf, strlen(buf));
}

/* Get the namespace from the RESP4 header, or return DEFAULT_NAMESPACE. */
static const char *get_namespace(ValkeyModuleCtx *ctx) {
    ValkeyModuleString *ns_str = ValkeyModule_GetRequestHeader(ctx, HEADER_IDEMPOTENCY_NAMESPACE);
    if (ns_str) {
        size_t len;
        const char *ns = ValkeyModule_StringPtrLen(ns_str, &len);
        if (len > 0 && len < 128) return ns;
    }
    return DEFAULT_NAMESPACE;
}

/* Get TTL from the RESP4 header, or return DEFAULT_TTL_SECONDS. */
static long long get_ttl(ValkeyModuleCtx *ctx) {
    long long ttl = DEFAULT_TTL_SECONDS;
    ValkeyModule_GetRequestHeaderLongLong(ctx, HEADER_IDEMPOTENCY_TTL, &ttl);
    if (ttl <= 0) ttl = DEFAULT_TTL_SECONDS;
    return ttl;
}

/* Store a token -> result mapping in the hash, and record the expiration time. */
static int store_token(ValkeyModuleCtx *ctx, const char *ns,
                       const char *token, size_t token_len,
                       const char *result, size_t result_len,
                       long long ttl_seconds) {
    ValkeyModuleString *hash_key = build_hash_key(ctx, ns);
    ValkeyModuleString *ttl_key = build_ttl_key(ctx, ns);
    ValkeyModuleString *token_str = ValkeyModule_CreateString(ctx, token, token_len);
    ValkeyModuleString *result_str = ValkeyModule_CreateString(ctx, result, result_len);

    /* HSET __idempotency:{ns} {token} {result} */
    ValkeyModuleCallReply *reply = ValkeyModule_Call(ctx, "HSET", "sss",
        hash_key, token_str, result_str);
    if (reply) ValkeyModule_FreeCallReply(reply);

    /* ZADD __idempotency_ttl:{ns} {expire_time_ms} {token} */
    mstime_t now = ValkeyModule_Milliseconds();
    double expire_score = (double)(now + ttl_seconds * 1000);
    ValkeyModuleString *score_str = ValkeyModule_CreateStringFromDouble(ctx, expire_score);

    reply = ValkeyModule_Call(ctx, "ZADD", "sss",
        ttl_key, score_str, token_str);
    if (reply) ValkeyModule_FreeCallReply(reply);

    ValkeyModule_FreeString(ctx, hash_key);
    ValkeyModule_FreeString(ctx, ttl_key);
    ValkeyModule_FreeString(ctx, token_str);
    ValkeyModule_FreeString(ctx, result_str);
    ValkeyModule_FreeString(ctx, score_str);

    stats_tokens_stored++;
    return VALKEYMODULE_OK;
}

/* Look up a token in the hash. Returns the cached result or NULL. */
static ValkeyModuleCallReply *lookup_token(ValkeyModuleCtx *ctx, const char *ns,
                                           const char *token, size_t token_len) {
    ValkeyModuleString *hash_key = build_hash_key(ctx, ns);
    ValkeyModuleString *token_str = ValkeyModule_CreateString(ctx, token, token_len);

    ValkeyModuleCallReply *reply = ValkeyModule_Call(ctx, "HGET", "ss",
        hash_key, token_str);

    ValkeyModule_FreeString(ctx, hash_key);
    ValkeyModule_FreeString(ctx, token_str);

    if (reply && ValkeyModule_CallReplyType(reply) == VALKEYMODULE_REPLY_NULL) {
        ValkeyModule_FreeCallReply(reply);
        return NULL;
    }
    return reply;
}

/* PLACEHOLDER: Forward declarations for commands */
static int IdempotentExecCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc);
static int IdempotentInfoCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc);
static int IdempotentInvalidateCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc);
static int IdempotentStatsCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc);
static int IdempotentFlushCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc);
static void CleanupTimerCallback(ValkeyModuleCtx *ctx, void *data);

/* ============================================================================
 * IDEMPOTENT.EXEC <command> [args...]
 * ============================================================================ */

static int IdempotentExecCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    if (argc < 2) {
        ValkeyModule_ReplyWithError(ctx,
            "ERR wrong number of arguments for 'IDEMPOTENT.EXEC' command. "
            "Usage: IDEMPOTENT.EXEC <command> [args...]");
        return VALKEYMODULE_OK;
    }

    /* Read the idempotency-token header */
    ValkeyModuleString *token_ms = ValkeyModule_GetRequestHeader(ctx, HEADER_IDEMPOTENCY_TOKEN);
    if (!token_ms) {
        ValkeyModule_ReplyWithError(ctx,
            "ERR IDEMPOTENT.EXEC requires the 'idempotency-token' RESP4 request header");
        return VALKEYMODULE_OK;
    }

    size_t token_len;
    const char *token = ValkeyModule_StringPtrLen(token_ms, &token_len);

    if (token_len == 0 || token_len > MAX_TOKEN_LEN) {
        ValkeyModule_ReplyWithError(ctx,
            "ERR idempotency-token must be between 1 and 128 bytes");
        return VALKEYMODULE_OK;
    }

    const char *ns = get_namespace(ctx);
    long long ttl = get_ttl(ctx);

    /* Check if this token already has a cached result */
    ValkeyModuleCallReply *cached = lookup_token(ctx, ns, token, token_len);
    if (cached) {
        /* Cache hit: return the stored result */
        stats_cache_hits++;

        /* Send reply attributes indicating this was a cached replay */
        ValkeyModule_ReplyWithAttribute(ctx, 3);
        ValkeyModule_ReplyWithCString(ctx, "idempotent");
        ValkeyModule_ReplyWithBool(ctx, 1);
        ValkeyModule_ReplyWithCString(ctx, "token-status");
        ValkeyModule_ReplyWithCString(ctx, "cached");
        ValkeyModule_ReplyWithCString(ctx, "token");
        ValkeyModule_ReplyWithStringBuffer(ctx, token, token_len);

        /* Return the cached RESP reply directly as a string
         * (the cached value is the raw RESP-encoded reply stored as a bulk string) */
        size_t cached_len;
        const char *cached_str = ValkeyModule_CallReplyStringPtr(cached, &cached_len);
        if (cached_str) {
            ValkeyModule_ReplyWithStringBuffer(ctx, cached_str, cached_len);
        } else {
            ValkeyModule_ReplyWithNull(ctx);
        }
        ValkeyModule_FreeCallReply(cached);
        return VALKEYMODULE_OK;
    }

    /* Cache miss: execute the command */
    stats_cache_misses++;

    const char *cmd = ValkeyModule_StringPtrLen(argv[1], NULL);

    ValkeyModuleCallReply *reply;
    if (argc == 2) {
        reply = ValkeyModule_Call(ctx, cmd, "");
    } else {
        reply = ValkeyModule_Call(ctx, cmd, "v", argv + 2, argc - 2);
    }

    if (!reply) {
        stats_exec_errors++;
        ValkeyModule_ReplyWithError(ctx, "ERR failed to execute command");
        return VALKEYMODULE_OK;
    }

    /* Capture the raw RESP-encoded reply to cache it */
    size_t reply_proto_len;
    const char *reply_proto = ValkeyModule_CallReplyProto(reply, &reply_proto_len);

    /* Store the token -> result mapping */
    if (reply_proto && reply_proto_len > 0 && reply_proto_len < 65536) {
        store_token(ctx, ns, token, token_len,
                    reply_proto, reply_proto_len, ttl);
    }

    /* Send reply attributes indicating this was a new execution */
    ValkeyModule_ReplyWithAttribute(ctx, 3);
    ValkeyModule_ReplyWithCString(ctx, "idempotent");
    ValkeyModule_ReplyWithBool(ctx, 1);
    ValkeyModule_ReplyWithCString(ctx, "token-status");
    ValkeyModule_ReplyWithCString(ctx, "new");
    ValkeyModule_ReplyWithCString(ctx, "token");
    ValkeyModule_ReplyWithStringBuffer(ctx, token, token_len);

    /* Forward the actual reply to the client */
    ValkeyModule_ReplyWithCallReply(ctx, reply);
    ValkeyModule_FreeCallReply(reply);

    return VALKEYMODULE_OK;
}

/* ============================================================================
 * IDEMPOTENT.INFO <token> [namespace]
 * ============================================================================ */

static int IdempotentInfoCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    if (argc < 2 || argc > 3) return ValkeyModule_WrongArity(ctx);

    size_t token_len;
    const char *token = ValkeyModule_StringPtrLen(argv[1], &token_len);

    const char *ns = DEFAULT_NAMESPACE;
    if (argc == 3) {
        ns = ValkeyModule_StringPtrLen(argv[2], NULL);
    }

    /* Check if the token exists */
    ValkeyModuleCallReply *cached = lookup_token(ctx, ns, token, token_len);
    if (!cached) {
        ValkeyModule_ReplyWithNull(ctx);
        return VALKEYMODULE_OK;
    }

    size_t cached_len;
    ValkeyModule_CallReplyStringPtr(cached, &cached_len);

    /* Get the TTL score from the sorted set */
    ValkeyModuleString *ttl_key = build_ttl_key(ctx, ns);
    ValkeyModuleString *token_str = ValkeyModule_CreateString(ctx, token, token_len);
    ValkeyModuleCallReply *score_reply = ValkeyModule_Call(ctx, "ZSCORE", "ss",
        ttl_key, token_str);

    ValkeyModule_ReplyWithMap(ctx, 4);

    ValkeyModule_ReplyWithCString(ctx, "token");
    ValkeyModule_ReplyWithStringBuffer(ctx, token, token_len);

    ValkeyModule_ReplyWithCString(ctx, "namespace");
    ValkeyModule_ReplyWithCString(ctx, ns);

    ValkeyModule_ReplyWithCString(ctx, "cached_result_bytes");
    ValkeyModule_ReplyWithLongLong(ctx, (long long)cached_len);

    ValkeyModule_ReplyWithCString(ctx, "expires_at_ms");
    if (score_reply && ValkeyModule_CallReplyType(score_reply) != VALKEYMODULE_REPLY_NULL) {
        size_t score_len;
        const char *score_str = ValkeyModule_CallReplyStringPtr(score_reply, &score_len);
        if (score_str) {
            double d = strtod(score_str, NULL);
            ValkeyModule_ReplyWithLongLong(ctx, (long long)d);
        } else {
            ValkeyModule_ReplyWithNull(ctx);
        }
    } else {
        ValkeyModule_ReplyWithNull(ctx);
    }

    if (score_reply) ValkeyModule_FreeCallReply(score_reply);
    ValkeyModule_FreeString(ctx, ttl_key);
    ValkeyModule_FreeString(ctx, token_str);
    ValkeyModule_FreeCallReply(cached);

    return VALKEYMODULE_OK;
}

/* ============================================================================
 * IDEMPOTENT.INVALIDATE <token> [namespace]
 * ============================================================================ */

static int IdempotentInvalidateCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    if (argc < 2 || argc > 3) return ValkeyModule_WrongArity(ctx);

    size_t token_len;
    const char *token = ValkeyModule_StringPtrLen(argv[1], &token_len);

    const char *ns = DEFAULT_NAMESPACE;
    if (argc == 3) {
        ns = ValkeyModule_StringPtrLen(argv[2], NULL);
    }

    ValkeyModuleString *hash_key = build_hash_key(ctx, ns);
    ValkeyModuleString *ttl_key = build_ttl_key(ctx, ns);
    ValkeyModuleString *token_str = ValkeyModule_CreateString(ctx, token, token_len);

    /* Remove from hash */
    ValkeyModuleCallReply *reply = ValkeyModule_Call(ctx, "HDEL", "ss",
        hash_key, token_str);
    long long removed = 0;
    if (reply) {
        if (ValkeyModule_CallReplyType(reply) == VALKEYMODULE_REPLY_INTEGER) {
            removed = ValkeyModule_CallReplyInteger(reply);
        }
        ValkeyModule_FreeCallReply(reply);
    }

    /* Remove from TTL sorted set */
    reply = ValkeyModule_Call(ctx, "ZREM", "ss", ttl_key, token_str);
    if (reply) ValkeyModule_FreeCallReply(reply);

    ValkeyModule_FreeString(ctx, hash_key);
    ValkeyModule_FreeString(ctx, ttl_key);
    ValkeyModule_FreeString(ctx, token_str);

    if (removed > 0) {
        stats_tokens_invalidated++;
        ValkeyModule_ReplyWithSimpleString(ctx, "OK");
    } else {
        ValkeyModule_ReplyWithNull(ctx);
    }

    return VALKEYMODULE_OK;
}

/* ============================================================================
 * IDEMPOTENT.STATS
 * ============================================================================ */

static int IdempotentStatsCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    VALKEYMODULE_NOT_USED(argv);
    if (argc != 1) return ValkeyModule_WrongArity(ctx);

    ValkeyModule_ReplyWithMap(ctx, 6);

    ValkeyModule_ReplyWithCString(ctx, "tokens_stored");
    ValkeyModule_ReplyWithLongLong(ctx, stats_tokens_stored);

    ValkeyModule_ReplyWithCString(ctx, "cache_hits");
    ValkeyModule_ReplyWithLongLong(ctx, stats_cache_hits);

    ValkeyModule_ReplyWithCString(ctx, "cache_misses");
    ValkeyModule_ReplyWithLongLong(ctx, stats_cache_misses);

    ValkeyModule_ReplyWithCString(ctx, "tokens_expired");
    ValkeyModule_ReplyWithLongLong(ctx, stats_tokens_expired);

    ValkeyModule_ReplyWithCString(ctx, "tokens_invalidated");
    ValkeyModule_ReplyWithLongLong(ctx, stats_tokens_invalidated);

    ValkeyModule_ReplyWithCString(ctx, "exec_errors");
    ValkeyModule_ReplyWithLongLong(ctx, stats_exec_errors);

    return VALKEYMODULE_OK;
}

/* ============================================================================
 * IDEMPOTENT.FLUSH [namespace]
 * ============================================================================ */

static int IdempotentFlushCommand(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    if (argc > 2) return ValkeyModule_WrongArity(ctx);

    const char *ns = DEFAULT_NAMESPACE;
    if (argc == 2) {
        ns = ValkeyModule_StringPtrLen(argv[1], NULL);
    }

    ValkeyModuleString *hash_key = build_hash_key(ctx, ns);
    ValkeyModuleString *ttl_key = build_ttl_key(ctx, ns);

    /* Count tokens before deletion for stats */
    ValkeyModuleCallReply *len_reply = ValkeyModule_Call(ctx, "HLEN", "s", hash_key);
    long long count = 0;
    if (len_reply) {
        if (ValkeyModule_CallReplyType(len_reply) == VALKEYMODULE_REPLY_INTEGER) {
            count = ValkeyModule_CallReplyInteger(len_reply);
        }
        ValkeyModule_FreeCallReply(len_reply);
    }

    /* Delete both keys */
    ValkeyModuleCallReply *reply = ValkeyModule_Call(ctx, "DEL", "ss", hash_key, ttl_key);
    if (reply) ValkeyModule_FreeCallReply(reply);

    ValkeyModule_FreeString(ctx, hash_key);
    ValkeyModule_FreeString(ctx, ttl_key);

    stats_tokens_invalidated += count;

    ValkeyModule_ReplyWithLongLong(ctx, count);
    return VALKEYMODULE_OK;
}

/* ============================================================================
 * Periodic cleanup timer — evict expired tokens
 * ============================================================================ */

static void CleanupTimerCallback(ValkeyModuleCtx *ctx, void *data) {
    VALKEYMODULE_NOT_USED(data);

    /* Scan for __idempotency_ttl:* keys using KEYS (simple approach for MVP).
     * In production, SCAN would be preferred. For now, we clean the default ns. */
    const char *ns = DEFAULT_NAMESPACE;
    ValkeyModuleString *ttl_key = build_ttl_key(ctx, ns);
    ValkeyModuleString *hash_key = build_hash_key(ctx, ns);

    mstime_t now = ValkeyModule_Milliseconds();
    char score_buf[32];
    snprintf(score_buf, sizeof(score_buf), "%lld", (long long)now);
    ValkeyModuleString *max_score = ValkeyModule_CreateString(ctx, score_buf, strlen(score_buf));
    ValkeyModuleString *min_score = ValkeyModule_CreateStringFromLongLong(ctx, 0);

    /* ZRANGEBYSCORE __idempotency_ttl:{ns} 0 {now} LIMIT 0 100 */
    ValkeyModuleCallReply *reply = ValkeyModule_Call(ctx, "ZRANGEBYSCORE", "sssccs",
        ttl_key, min_score, max_score, "LIMIT",
        "0", ValkeyModule_CreateStringFromLongLong(ctx, 100));

    if (reply && ValkeyModule_CallReplyType(reply) == VALKEYMODULE_REPLY_ARRAY) {
        size_t len = ValkeyModule_CallReplyLength(reply);
        for (size_t i = 0; i < len; i++) {
            ValkeyModuleCallReply *elem = ValkeyModule_CallReplyArrayElement(reply, i);
            size_t tk_len;
            const char *tk_str = ValkeyModule_CallReplyStringPtr(elem, &tk_len);
            if (tk_str && tk_len > 0) {
                ValkeyModuleString *tk = ValkeyModule_CreateString(ctx, tk_str, tk_len);
                /* Remove from hash */
                ValkeyModuleCallReply *del_r = ValkeyModule_Call(ctx, "HDEL", "ss", hash_key, tk);
                if (del_r) ValkeyModule_FreeCallReply(del_r);
                /* Remove from sorted set */
                del_r = ValkeyModule_Call(ctx, "ZREM", "ss", ttl_key, tk);
                if (del_r) ValkeyModule_FreeCallReply(del_r);
                ValkeyModule_FreeString(ctx, tk);
                stats_tokens_expired++;
            }
        }
    }

    if (reply) ValkeyModule_FreeCallReply(reply);
    ValkeyModule_FreeString(ctx, ttl_key);
    ValkeyModule_FreeString(ctx, hash_key);
    ValkeyModule_FreeString(ctx, max_score);
    ValkeyModule_FreeString(ctx, min_score);

    /* Re-arm the timer */
    cleanup_timer_id = ValkeyModule_CreateTimer(ctx, CLEANUP_INTERVAL_MS,
        CleanupTimerCallback, NULL);
}

/* ============================================================================
 * Module initialization
 * ============================================================================ */

int ValkeyModule_OnLoad(ValkeyModuleCtx *ctx, ValkeyModuleString **argv, int argc) {
    VALKEYMODULE_NOT_USED(argv);
    VALKEYMODULE_NOT_USED(argc);

    if (ValkeyModule_Init(ctx, "idempotency", 1, VALKEYMODULE_APIVER_1) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    /* ---- Register RESP4 request headers ---- */
    if (ValkeyModule_RegisterRequestHeader(ctx, HEADER_IDEMPOTENCY_TOKEN, 0, -1) == VALKEYMODULE_ERR) {
        ValkeyModule_Log(ctx, "warning",
            "idempotency: failed to register '%s' header", HEADER_IDEMPOTENCY_TOKEN);
        return VALKEYMODULE_ERR;
    }
    if (ValkeyModule_RegisterRequestHeader(ctx, HEADER_IDEMPOTENCY_NAMESPACE, 0, -1) == VALKEYMODULE_ERR) {
        ValkeyModule_Log(ctx, "warning",
            "idempotency: failed to register '%s' header", HEADER_IDEMPOTENCY_NAMESPACE);
        return VALKEYMODULE_ERR;
    }
    if (ValkeyModule_RegisterRequestHeader(ctx, HEADER_IDEMPOTENCY_TTL, 0, -1) == VALKEYMODULE_ERR) {
        ValkeyModule_Log(ctx, "warning",
            "idempotency: failed to register '%s' header", HEADER_IDEMPOTENCY_TTL);
        return VALKEYMODULE_ERR;
    }

    ValkeyModule_Log(ctx, "notice",
        "idempotency: registered RESP4 headers: %s, %s, %s",
        HEADER_IDEMPOTENCY_TOKEN, HEADER_IDEMPOTENCY_NAMESPACE, HEADER_IDEMPOTENCY_TTL);

    /* ---- Register commands ---- */
    if (ValkeyModule_CreateCommand(ctx, "idempotent.exec",
            IdempotentExecCommand, "write deny-oom", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "idempotent.info",
            IdempotentInfoCommand, "readonly fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "idempotent.invalidate",
            IdempotentInvalidateCommand, "write", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "idempotent.stats",
            IdempotentStatsCommand, "readonly fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "idempotent.flush",
            IdempotentFlushCommand, "write", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    /* ---- Start periodic cleanup timer ---- */
    cleanup_timer_id = ValkeyModule_CreateTimer(ctx, CLEANUP_INTERVAL_MS,
        CleanupTimerCallback, NULL);

    ValkeyModule_Log(ctx, "notice",
        "idempotency: module loaded. Commands: IDEMPOTENT.EXEC, IDEMPOTENT.INFO, "
        "IDEMPOTENT.INVALIDATE, IDEMPOTENT.STATS, IDEMPOTENT.FLUSH");

    return VALKEYMODULE_OK;
}
