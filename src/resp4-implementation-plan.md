# RESP4 Implementation Plan

## Table of Contents
1. [Design Augmentations](#1-design-augmentations)
2. [Architecture Overview](#2-architecture-overview)
3. [Implementation Phases](#3-implementation-phases)
4. [Phase 1: Protocol Negotiation](#phase-1)
5. [Phase 2: Request Header Parsing](#phase-2)
6. [Phase 3: Header Storage on Client](#phase-3)
7. [Phase 4: Module API for Request Headers](#phase-4)
8. [Phase 5: Header Lifecycle & Cleanup](#phase-5)
9. [Phase 6: Trace-ID Reference Module](#phase-6)
10. [Phase 7: Testing](#phase-7)
11. [Phase 8: valkey-cli Header Support](#phase-8)
12. [File Change Summary](#file-change-summary)

---

## 1. Design Augmentations

_Improvements and clarifications over the original resp4.md design._

### 1.1 Simplify Header Encoding — Use Only Bulk Strings for Keys

The original design says header keys can be "bulk or simple string." For implementation simplicity and to avoid ambiguity, **header keys MUST be bulk strings** (`$`). Header values may be any RESP3 scalar type (bulk string, simple string, integer, double, boolean). This simplifies parsing since we always know the key encoding. Arrays/maps as header values are deferred to a future extension.

### 1.2 Header Size Limits

The original design is silent on limits. We add:
- **Max header count per command**: configurable, default 8. Prevents clients from sending unbounded metadata.
- **Max header key length**: 64 bytes. Header names are identifiers, not data.
- **Max header value length**: 4096 bytes. Sufficient for trace IDs, tokens, timestamps.
- **Max total header bytes per command**: 8192 bytes. Bounded memory per request.
- These are enforced during parsing. Exceeding any limit produces `-ERR header limit exceeded` and the command is rejected.
- All limits are configurable via `CONFIG SET` (e.g., `resp4-max-headers`, `resp4-max-header-value-len`).

### 1.3 Unregistered Header Policy — Default Ignore with Config

The original design mentions both "ignore" and "optional strict mode." We formalize:
- **Default**: unregistered headers are silently ignored (forward-compatible).
- **Config `resp4-unknown-header-policy`**: `ignore` (default) or `error`. When `error`, unrecognized headers produce `-ERR unknown header 'name'`.
- This is a server-global setting, not per-module.

### 1.4 Header Visibility to Built-in Engine Features (Commandlog / Slowlog)

The original design focuses on module consumption. We extend:
- The engine itself MAY read well-known headers for built-in features. Example: a `trace-id` header that gets included in commandlog (slowlog) entries.
- We add a **header notification callback** mechanism: the engine can register internal consumers for specific headers, similar to how modules do, but for built-in features.
- For the initial implementation, **the trace-id → slowlog integration will be done via a reference module**, not hardcoded in the engine. This keeps the engine generic.

### 1.5 MULTI/EXEC Semantics

Headers sent before a command inside a MULTI/EXEC block apply to that specific command, not the entire transaction. This matches the "headers apply to the next command array only" rule. The MULTI and EXEC commands themselves can also carry headers (though this is unusual). Headers do NOT persist across commands within a transaction — each command in the pipeline needs its own headers if desired.

### 1.6 Replication and AOF

- **Request headers are NOT replicated** by default. They are metadata about the request context (trace IDs, auth tokens) that are meaningful only at the point of origin.
- If a module needs to propagate header-derived data, it must explicitly encode it into the replicated command arguments (as the CRDT module does with CRDTMETA).
- **AOF**: Headers are not written to AOF. Commands are logged as pure RESP command arrays.
- This matches HTTP semantics: headers are transport metadata, not persisted state.

### 1.7 Protocol Version Negotiation

- RESP4 is negotiated via `HELLO 4`. The `helloCommand` handler is extended to accept version 4.
- `client->resp` becomes `4` for RESP4 clients.
- RESP4 is a **strict superset of RESP3**: all RESP3 types and reply attributes continue to work. The only addition is that the server now accepts `|` (attribute) prefixes on the *request* side before command arrays.
- Clients speaking RESP2 or RESP3 are completely unaffected. The server never sends request-side attributes to clients.

### 1.8 Pipelining Behavior

When pipelining, each command that needs headers must be preceded by its own `|` attribute block:
```
|1\r\n$8\r\ntrace-id\r\n$12\r\nabc-123-def\r\n
*3\r\n$3\r\nSET\r\n$3\r\nfoo\r\n$3\r\nbar\r\n
|1\r\n$8\r\ntrace-id\r\n$12\r\ndef-456-ghi\r\n
*3\r\n$3\r\nSET\r\n$3\r\nbaz\r\n$3\r\nqux\r\n
*2\r\n$3\r\nGET\r\n$3\r\nfoo\r\n
```
The third command (GET) has no headers. The parser reads `|` → stores headers → reads `*` → associates. If `*` is seen without preceding `|`, no headers are set. If `|` is followed by another `|`, that's an error.

## 2. Architecture Overview

### 2.1 Data Flow

```
Client (RESP4)          Server Engine                    Module
    |                       |                              |
    |-- |N (attributes) --> |                              |
    |-- *M (command)  ----> |                              |
    |                       |-- parseRequestHeaders() -->  |
    |                       |   (stores in client->       |
    |                       |    request_headers dict)     |
    |                       |                              |
    |                       |-- processCommand() -------> |
    |                       |   moduleCallCommandFilters() |
    |                       |   (filters can read headers) |
    |                       |                              |
    |                       |-- cmd->proc() ------------> |
    |                       |   ValkeyModuleCommandDispatcher()
    |                       |   module calls:              |
    |                       |   VM_GetRequestHeader()      |
    |                       |   VM_RequestHeaderExists()   |
    |                       |                              |
    |                       |-- clearRequestHeaders() -->  |
    |                       |   (after command completes)  |
    | <-- reply ----------- |                              |
```

### 2.2 Key Data Structures

**On `client` struct** (`src/server.h`):
```c
typedef struct client {
    // ... existing fields ...
    dict *request_headers;  // NULL when no headers. Dict of sds->robj* pairs.
                            // Lazily allocated on first header receipt.
    // ... existing fields ...
} client;
```

**Header registration** (global, in `src/module.c`):
```c
typedef struct RequestHeaderRegistration {
    sds name;                    // Header name (case-insensitive, stored lowercase)
    struct ValkeyModule *module;  // Owning module
    int expected_type;           // RESP type constraint, or -1 for any
    int flags;                   // Reserved for future use
} RequestHeaderRegistration;

static dict *registeredRequestHeaders;  // Global dict: sds name -> RequestHeaderRegistration*
```

**Parsed command extension** (for pipelining, `src/server.h`):
```c
typedef struct parsedCommand {
    // ... existing fields ...
    dict *request_headers;  // Headers associated with this queued command
} parsedCommand;
```

### 2.3 Key Design Decisions

1. **dict (hashtable) for headers, not array**: Headers are accessed by name, so O(1) lookup matters. Max 8 headers means the dict is always tiny.

2. **Lazy allocation**: `client->request_headers` is NULL by default. Only allocated when a RESP4 client sends headers. Zero overhead for RESP2/3 clients.

3. **Headers stored as robj***: Reuse the existing robj infrastructure for memory management and type checking. Header values are robj with appropriate encoding.

4. **Case-insensitive header names**: All header names are normalized to lowercase at parse time, matching HTTP convention.

5. **Command filters get header access**: The `ValkeyModuleCommandFilterCtx` is extended to allow reading (but not modifying) headers. This is critical for middleware-style modules.

---

## 3. Implementation Phases

### Phase 1: Protocol Negotiation (`HELLO 4`) ✅ DONE

**Status**: Implemented and builds successfully. Tests in `tests/unit/resp4.tcl`.

**Changes made**:

1. `src/networking.c`: `helloCommand()` now accepts `HELLO 4` (`ver > 3` → `ver > 4`). Fixed `addReplyDouble()` from `resp == 3` to `resp >= 3`.
2. `src/cluster.c`: Fixed `resp == 3` → `resp >= 3` in cluster slot cache key.
3. `src/module.c`: Fixed `resp == 3` → `resp >= 3` in `VM_GetContextFlags()`.
4. `src/valkey-cli.c`: Added `resp4` config field and `--resp4` flag. `cliSwitchProto()` sends `HELLO 4` when `--resp4` is set.
5. `tests/unit/resp4.tcl`: 9 test cases for HELLO 4 negotiation, rejection of invalid versions, downgrade, and basic functionality.

**Run tests**: `./build/runtest --single unit/resp4`

---

### Phase 2: Request Header Parsing ✅ DONE

**Goal**: Parse `|N` attribute blocks on the request side for RESP4 clients.

**Files**: `src/networking.c`, `src/server.h`

**Changes**:

1. **Extend `parseInputBuffer()`** to detect the `|` prefix for RESP4 clients:

```c
void parseInputBuffer(client *c) {
    serverAssert(c->cmd_queue.len == 0);

    if (!c->reqtype) {
        char firstchar = c->querybuf[c->qb_pos];
        if (firstchar == '*') {
            c->reqtype = PROTO_REQ_MULTIBULK;
        } else if (firstchar == '|' && c->resp >= 4) {
            c->reqtype = PROTO_REQ_RESP4_HEADER;  // New request type
        } else {
            c->reqtype = PROTO_REQ_INLINE;
        }
    }

    if (c->reqtype == PROTO_REQ_INLINE) {
        parseInlineBuffer(c);
    } else if (c->reqtype == PROTO_REQ_RESP4_HEADER) {
        parseRequestHeaders(c);       // New function
    } else if (c->reqtype == PROTO_REQ_MULTIBULK) {
        parseMultibulkBuffer(c);
    } else {
        serverPanic("Unknown request type");
    }
}
```

2. **New function `parseRequestHeaders()`** in `src/networking.c`:

```c
/* Parse RESP4 request-side attributes (headers).
 * Format: |N\r\n followed by N key-value pairs, followed by *M command.
 * After parsing headers, the function transitions to parsing the command. */
void parseRequestHeaders(client *c) {
    // 1. Parse |N\r\n to get header count
    // 2. Validate count <= resp4_max_headers config
    // 3. For each key-value pair:
    //    a. Parse key (must be bulk string $)
    //    b. Validate key length <= resp4_max_header_key_len
    //    c. Normalize key to lowercase
    //    d. Parse value (any RESP3 scalar type)
    //    e. Validate value length <= resp4_max_header_value_len
    //    f. Store in client->request_headers dict
    // 4. After all headers parsed, set c->reqtype = 0 so next
    //    parseInputBuffer call picks up the command (*M)
    // 5. On any error: set read_flags error, return
}
```

Key implementation notes:
- The parser is **incremental** like `parseMultibulk()`. If the buffer doesn't have enough data, it returns 0 and will be called again when more data arrives.
- We need parser state on the client for partially-parsed headers. Add to client struct:
  ```c
  int header_count;       // Total headers to parse (from |N)
  int headers_parsed;     // How many parsed so far
  sds pending_header_key; // Key parsed but value not yet complete
  ```
- After headers are fully parsed, reset `c->reqtype = 0` so the next `parseInputBuffer` iteration detects `*` and calls `parseMultibulkBuffer`.

3. **Add `PROTO_REQ_RESP4_HEADER`** constant in `src/server.h`:
```c
#define PROTO_REQ_INLINE    1
#define PROTO_REQ_MULTIBULK 2
#define PROTO_REQ_RESP4_HEADER 3  // New
```

**Estimated effort**: ~3-4 days (parsing is the most complex part)

---

### Phase 3: Header Storage on Client ✅ DONE

**Goal**: Store parsed headers on the client struct, handle lifecycle.

**Files**: `src/server.h`, `src/networking.c`, `src/server.c`

**Changes**:

1. **Extend `client` struct** in `src/server.h`:
```c
typedef struct client {
    // After existing fields, in the "less frequently used" section:
    dict *request_headers;    // RESP4 request headers for current command
    // Parser state for incremental header parsing:
    int header_count;         // Total expected from |N
    int headers_parsed;       // Completed so far
    sds pending_header_key;   // Partially parsed header
} client;
```

2. **Initialize in `createClient()`** (`src/networking.c`):
```c
c->request_headers = NULL;  // Lazy allocation
c->header_count = 0;
c->headers_parsed = 0;
c->pending_header_key = NULL;
```

3. **Free in `freeClient()`** (`src/networking.c`):
```c
if (c->request_headers) {
    dictRelease(c->request_headers);
    c->request_headers = NULL;
}
if (c->pending_header_key) {
    sdsfree(c->pending_header_key);
    c->pending_header_key = NULL;
}
```

4. **Extend `parsedCommand`** for pipelining support in `src/server.h`:
```c
typedef struct parsedCommand {
    // ... existing fields ...
    dict *request_headers;  // Headers for this queued command
} parsedCommand;
```

5. **In `consumeCommandQueue()`**, transfer headers from queued command to client:
```c
// When popping a command from the queue:
if (c->request_headers) dictRelease(c->request_headers);
c->request_headers = p->request_headers;
p->request_headers = NULL;
```

6. **Dict type for headers** — create `requestHeadersDictType` with sds key comparison (case-insensitive), sds key dup/free, robj value decrRefCount:
```c
static dictType requestHeadersDictType = {
    dictSdsHash,               // hash function
    NULL,                      // key dup
    NULL,                      // val dup
    dictSdsCaseCompare,        // key compare (case-insensitive)
    dictSdsDestructor,         // key destructor
    dictObjectDestructor,      // val destructor
    NULL                       // allow resize
};
```

**Estimated effort**: ~1-2 days

---

### Phase 4: Module API for Request Headers ✅ DONE

**Goal**: Expose headers to modules through new VM_ functions.

**Files**: `src/module.c`, `src/valkeymodule.h` (or `src/redismodule.h`)

#### 4.1 New API Functions in `src/module.c`

```c
/* Register interest in a request header. Returns VALKEYMODULE_OK on
 * success, VALKEYMODULE_ERR if the name is already registered by
 * another module. */
int VM_RegisterRequestHeader(ValkeyModuleCtx *ctx,
                             const char *name,
                             int flags,
                             int expected_type) {
    // 1. Normalize name to lowercase
    // 2. Check if already registered by another module
    // 3. Create RequestHeaderRegistration, add to global dict
    // 4. Also track in module's own list for cleanup on unload
    // Return VALKEYMODULE_OK or VALKEYMODULE_ERR
}

/* Check if a header was present on the current request. */
int VM_RequestHeaderExists(ValkeyModuleCtx *ctx, const char *name) {
    client *c = ctx->client;
    if (!c || !c->request_headers) return 0;
    sds lower = sdsnew(name);
    sdstolower(lower);
    int exists = dictFind(c->request_headers, lower) != NULL;
    sdsfree(lower);
    return exists;
}

/* Get a header value. Returns NULL if absent. The returned
 * ValkeyModuleString is valid only for the command callback duration. */
ValkeyModuleString *VM_GetRequestHeader(ValkeyModuleCtx *ctx,
                                         const char *name) {
    client *c = ctx->client;
    if (!c || !c->request_headers) return NULL;
    sds lower = sdsnew(name);
    sdstolower(lower);
    dictEntry *de = dictFind(c->request_headers, lower);
    sdsfree(lower);
    if (!de) return NULL;
    return dictGetVal(de);
}

/* Get header as long long. Returns VALKEYMODULE_OK on success. */
int VM_GetRequestHeaderLongLong(ValkeyModuleCtx *ctx,
                                 const char *name,
                                 long long *ll) {
    ValkeyModuleString *val = VM_GetRequestHeader(ctx, name);
    if (!val) return VALKEYMODULE_ERR;
    if (getLongLongFromObject(val, ll) != C_OK) return VALKEYMODULE_ERR;
    return VALKEYMODULE_OK;
}

/* Iterator API for walking all headers on the current request. */
ValkeyModuleRequestHeaderIter *VM_RequestHeaderIterStart(
    ValkeyModuleCtx *ctx) {
    // Returns a wrapper around dictIterator
    // Returns NULL if no headers
}

int VM_RequestHeaderIterNext(
    ValkeyModuleRequestHeaderIter *iter,
    ValkeyModuleString **name,
    ValkeyModuleString **value) {
    // Wraps dictNext, returns 1 if entry found, 0 if done
}

void VM_RequestHeaderIterStop(
    ValkeyModuleRequestHeaderIter *iter) {
    // Releases the dictIterator
}
```

#### 4.2 Command Filter Header Access

Extend `ValkeyModuleCommandFilterCtx`:
```c
typedef struct ValkeyModuleCommandFilterCtx {
    ValkeyModuleString **argv;
    int argv_len;
    int argc;
    client *c;
    // Headers are accessed via c->request_headers, no new field needed.
    // We add a convenience function:
} ValkeyModuleCommandFilterCtx;
```

New filter API function:
```c
ValkeyModuleString *VM_CommandFilterGetRequestHeader(
    ValkeyModuleCommandFilterCtx *fctx, const char *name) {
    if (!fctx->c || !fctx->c->request_headers) return NULL;
    // Same lookup as VM_GetRequestHeader but using filter context
}
```

#### 4.3 Registration in API table

Add to `moduleRegisterCoreAPI()`:
```c
REGISTER_API(RegisterRequestHeader);
REGISTER_API(RequestHeaderExists);
REGISTER_API(GetRequestHeader);
REGISTER_API(GetRequestHeaderLongLong);
REGISTER_API(RequestHeaderIterStart);
REGISTER_API(RequestHeaderIterNext);
REGISTER_API(RequestHeaderIterStop);
REGISTER_API(CommandFilterGetRequestHeader);
```

#### 4.4 Public Header (`src/valkeymodule.h`)

Add declarations and `VALKEYMODULE_GET_API` entries for all new functions.
Add `typedef struct ValkeyModuleRequestHeaderIter ValkeyModuleRequestHeaderIter;`

#### 4.5 Module cleanup on unload

When a module is unloaded, remove its header registrations from the global dict.

**Estimated effort**: ~3-4 days

---

### Phase 5: Header Lifecycle & Cleanup

**Goal**: Ensure headers are properly cleared after each command.

**Files**: `src/server.c`, `src/networking.c`

**Changes**:

1. **Clear headers after command execution**. In `resetClient()` (called after each command completes):
```c
void resetClient(client *c) {
    // ... existing reset logic ...

    // Clear RESP4 request headers
    if (c->request_headers) {
        dictRelease(c->request_headers);
        c->request_headers = NULL;
    }
}
```

2. **Clear headers on client reset/reconnect/error** — ensure `freeClientArgv()` or equivalent cleanup paths also clear headers.

3. **Clear headers in MULTI/EXEC** — within `processCommand()`, after the command within a MULTI block is queued (not executed), clear headers. When the queued command is later executed, its headers will have been moved to the `parsedCommand` struct (or re-sent by the client for each command).

4. **Config registration** in `src/config.c`:
```c
// New config entries:
createIntConfig("resp4-max-headers", NULL, MODIFIABLE_CONFIG, 1, 64, 
    server.resp4_max_headers, 8, ...);
createIntConfig("resp4-max-header-value-len", NULL, MODIFIABLE_CONFIG, 64, 65536,
    server.resp4_max_header_value_len, 4096, ...);
createEnumConfig("resp4-unknown-header-policy", NULL, MODIFIABLE_CONFIG,
    resp4_unknown_header_policy_enum, server.resp4_unknown_header_policy, 
    RESP4_HEADER_POLICY_IGNORE, ...);
```

Add corresponding fields to `struct server` in `src/server.h`:
```c
int resp4_max_headers;
int resp4_max_header_value_len;
int resp4_unknown_header_policy;  // 0=ignore, 1=error
```

**Estimated effort**: ~1-2 days

---

### Phase 6: Trace-ID Reference Module (`helloheaders.c`)

**Goal**: A reference module demonstrating RESP4 headers by implementing trace-id integration with the commandlog (slowlog).

**File**: `src/modules/helloheaders.c` (new file)

#### 6.1 Module Overview

The module:
1. Registers a `trace-id` request header
2. Uses a command filter to capture the trace-id from every command
3. Stores trace-ids in a per-client or per-command structure
4. Hooks into the commandlog to add trace-id to slowlog entries
5. Provides a `HEADERS.GET` command to echo back all current request headers (for testing)

#### 6.2 Implementation

```c
#include "../valkeymodule.h"
#include <string.h>
#include <strings.h>

#define TRACE_ID_HEADER "trace-id"

/* Store the most recent trace-id per client for commandlog integration.
 * We use a simple approach: a command filter captures the trace-id
 * and stores it in a module-level dict keyed by client ID. */
static ValkeyModuleDict *client_trace_ids;

/* Command filter callback — runs before every command. */
void TraceIdCommandFilter(ValkeyModuleCommandFilterCtx *fctx) {
    ValkeyModuleString *trace_id =
        ValkeyModule_CommandFilterGetRequestHeader(fctx, TRACE_ID_HEADER);
    if (trace_id) {
        unsigned long long client_id =
            ValkeyModule_CommandFilterGetClientId(fctx);
        /* Store trace-id keyed by client_id for later retrieval. */
        char key[32];
        snprintf(key, sizeof(key), "%llu", client_id);
        ValkeyModule_DictSetC(client_trace_ids,
                              key, strlen(key), (void*)trace_id);
    }
}

/* HEADERS.ECHO — echo all request headers back to the client.
 * Useful for testing RESP4 header parsing. */
int HeadersEchoCommand(ValkeyModuleCtx *ctx, void **argv, int argc) {
    VALKEYMODULE_NOT_USED(argv);
    VALKEYMODULE_NOT_USED(argc);

    ValkeyModuleRequestHeaderIter *iter =
        ValkeyModule_RequestHeaderIterStart(ctx);
    if (!iter) {
        ValkeyModule_ReplyWithMap(ctx, 0);
        return VALKEYMODULE_OK;
    }

    ValkeyModule_ReplyWithMap(ctx, VALKEYMODULE_POSTPONED_LEN);
    ValkeyModuleString *name, *value;
    long count = 0;
    while (ValkeyModule_RequestHeaderIterNext(iter, &name, &value)) {
        ValkeyModule_ReplyWithString(ctx, name);
        ValkeyModule_ReplyWithString(ctx, value);
        count++;
    }
    ValkeyModule_RequestHeaderIterStop(iter);
    ValkeyModule_ReplySetMapLength(ctx, count);
    return VALKEYMODULE_OK;
}

/* HEADERS.TRACEID — return the trace-id from the current request. */
int HeadersTraceIdCommand(ValkeyModuleCtx *ctx, void **argv, int argc) {
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

/* Module initialization. */
int ValkeyModule_OnLoad(ValkeyModuleCtx *ctx, ValkeyModuleString **argv,
                        int argc) {
    VALKEYMODULE_NOT_USED(argv);
    VALKEYMODULE_NOT_USED(argc);

    if (ValkeyModule_Init(ctx, "helloheaders", 1,
                          VALKEYMODULE_APIVER_1) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    /* Register the trace-id header. */
    if (ValkeyModule_RegisterRequestHeader(
            ctx, TRACE_ID_HEADER, 0,
            VALKEYMODULE_HEADER_TYPE_BULK_STRING) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    /* Register command filter to capture trace-id. */
    ValkeyModule_RegisterCommandFilter(ctx, TraceIdCommandFilter, 0);

    /* Register commands. */
    if (ValkeyModule_CreateCommand(ctx, "headers.echo",
            HeadersEchoCommand, "fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    if (ValkeyModule_CreateCommand(ctx, "headers.traceid",
            HeadersTraceIdCommand, "fast", 0, 0, 0) == VALKEYMODULE_ERR)
        return VALKEYMODULE_ERR;

    client_trace_ids = ValkeyModule_CreateDict(ctx);
    return VALKEYMODULE_OK;
}
```

#### 6.3 Commandlog (Slowlog) Integration via Module

To add trace-id to slowlog entries, we extend the approach:

**Option A (Recommended for reference impl)**: The module subscribes to a new server event `VALKEYMODULE_EVENT_COMMANDLOG` that fires when a command is about to be logged to the commandlog. The event data includes the client ID and the commandlog entry, allowing the module to attach metadata.

This requires adding a new event type:
```c
// In server.h or valkeymodule.h:
#define VALKEYMODULE_EVENT_COMMANDLOG ...
```

And firing it from `commandlogPushCurrentCommand()` in `src/commandlog.c`.

**Option B (Simpler)**: Extend the `commandlogEntry` struct to include an optional `sds` metadata field. Add a module API `VM_CommandlogSetMetadata(ctx, key, value)` that a module can call during command execution to attach metadata that will be included if this command ends up in the commandlog. The metadata is stored temporarily on the client and transferred to the commandlog entry.

For the reference implementation, **Option B** is simpler:

1. Add to `client` struct: `dict *commandlog_metadata;`  
2. Add module API: `VM_SetCommandlogMetadata(ctx, "trace-id", trace_id_string);`
3. In `commandlogCreateEntry()`, copy `c->commandlog_metadata` into the entry
4. In `commandlogGetReply()`, include metadata in the reply

This lets the trace-id module do:
```c
void TraceIdCommandFilter(ValkeyModuleCommandFilterCtx *fctx) {
    ValkeyModuleString *trace_id =
        ValkeyModule_CommandFilterGetRequestHeader(fctx, TRACE_ID_HEADER);
    if (trace_id) {
        // This attaches metadata to the current command for slowlog
        ValkeyModule_SetCommandlogMetadata(fctx, "trace-id", trace_id);
    }
}
```

**Estimated effort**: ~2-3 days

---

### Phase 7: Testing

**Files**: `tests/unit/moduleapi/headers.tcl` (new), `src/modules/helloheaders.c`, various integration tests

#### 7.1 Unit Tests for Protocol Parsing

Test in `tests/unit/resp4.tcl` (new):
- HELLO 4 negotiation succeeds, returns proto=4
- HELLO 5 rejected
- RESP4 client can send command without headers (backward compat)
- RESP4 client sends headers + command, command executes correctly
- Header with multiple key-value pairs
- Header limits enforced (too many headers, key too long, value too long)
- Invalid header format (missing value, wrong key type) → error
- RESP2/3 client sending `|` → treated as unknown (error or inline parse fail)
- Pipelining: multiple commands with different headers
- Pipelining: some commands with headers, some without
- MULTI/EXEC with headers on individual commands

#### 7.2 Module API Tests

Test in `tests/unit/moduleapi/headers.tcl` (new):
- Load helloheaders module
- HELLO 4 + send headers + `HEADERS.ECHO` returns correct headers
- `HEADERS.TRACEID` returns trace-id value
- `HEADERS.TRACEID` returns nil when no trace-id header
- Multiple headers sent, only trace-id registered, others ignored
- Unregistered header with strict policy → error
- Command filter receives headers correctly
- Headers cleared between commands

#### 7.3 Commandlog Integration Tests

- Send command with trace-id header that triggers slowlog
- SLOWLOG GET shows trace-id in metadata
- Commands without trace-id have no metadata in slowlog

#### 7.4 Regression Tests

- All existing tests pass (RESP2/3 unaffected)
- Replication: headers not propagated to replicas
- AOF: headers not written, AOF replay works

**Estimated effort**: ~3-4 days

---

### Phase 8: valkey-cli Header Support

**Goal**: Allow `valkey-cli` users to attach RESP4 request headers to commands interactively, making it easy to test and use RESP4 headers without raw TCP.

**File**: `src/valkey-cli.c`

#### 8.1 Design

Add a `--header` CLI flag and a `HEADER` meta-command within the interactive REPL:

**Command-line flag** (for non-interactive / single-command mode):
```bash
# Attach a header to the next command
./valkey-cli --resp4 --header trace-id=abc-123 SET foo bar

# Multiple headers
./valkey-cli --resp4 --header trace-id=abc-123 --header request-id=42 SET foo bar
```

**Interactive REPL meta-command**:
```
127.0.0.1:6379> HEADER trace-id my-trace-value
OK (header queued for next command)
127.0.0.1:6379> SET foo bar
OK
127.0.0.1:6379> HEADERS.TRACEID
"my-trace-value"
```

The `HEADER` command is a client-side-only pseudo-command (not sent to the server). It stores headers in a local list. When the next real command is sent, the CLI prepends the `|N` attribute block to the RESP output, then clears the stored headers.

Alternatively, a single-line syntax could be supported:
```
127.0.0.1:6379> [trace-id=abc-123] SET foo bar
```

#### 8.2 Implementation Details

1. **Add `--header name=value` flag**: Parse in `main()`, store in a linked list of `{name, value}` pairs. Requires `--resp4` to be set (error otherwise).

2. **Add `HEADER` REPL pseudo-command**: In `cliSendCommand()` or the REPL loop, intercept commands starting with `HEADER` before they are sent to the server. Store the name/value pair in a client-local list.

3. **Modify `cliSendCommand()` to prepend headers**: Before writing the `*N` multibulk array for the command, if there are queued headers and the connection is RESP4, write the `|N` attribute block first:
   ```c
   // If we have pending headers and resp4 is active:
   if (config.resp4 && pendingHeaderCount() > 0) {
       // Write |N\r\n
       sds header_block = sdscatfmt(sdsempty(), "|%i\r\n", pendingHeaderCount());
       // For each header: write $keylen\r\nkey\r\n$vallen\r\nval\r\n
       for each header in pending_headers {
           header_block = sdscatfmt(header_block, "$%i\r\n%s\r\n$%i\r\n%s\r\n",
               sdslen(h->name), h->name, sdslen(h->value), h->value);
       }
       // Write to socket before the command
       cliWriteConn(header_block);
       sdsfree(header_block);
       clearPendingHeaders();
   }
   ```

4. **Add `CLEARHEADERS` pseudo-command**: Clears any queued headers without sending them.

5. **Display headers in output**: When `--resp4` is active and the server returns reply attributes (`|`), display them in a distinct format (e.g., `# attribute: key=value`).

#### 8.3 Testing

- `valkey-cli --resp4 --header trace-id=test123 HEADERS.TRACEID` → returns `test123`
- `valkey-cli --resp4 --header trace-id=abc --header custom=xyz HEADERS.ECHO` → returns both headers
- `HEADER` in REPL mode queues correctly and is consumed by next command
- Headers require `--resp4`; error message if used without it
- `CLEARHEADERS` clears pending headers

#### 8.4 Estimated Effort

~2-3 days. The main work is modifying the CLI's command output path to optionally prepend the `|N` attribute block.

---

## File Change Summary

| File | Change Type | Description |
|------|------------|-------------|
| `src/server.h` | Modify | Add `request_headers`, header parser state to `client`; add `PROTO_REQ_RESP4_HEADER`; add config fields to `server`; extend `parsedCommand`; extend `commandlogEntry` |
| `src/networking.c` | Modify | Extend `helloCommand` for RESP4; extend `parseInputBuffer`; add `parseRequestHeaders()`; extend `createClient`/`freeClient`/`resetClient` |
| `src/server.c` | Modify | Extend `processCommand` header cleanup; extend `resetClient` |
| `src/config.c` | Modify | Add RESP4 config entries |
| `src/module.c` | Modify | Add `VM_RegisterRequestHeader`, `VM_GetRequestHeader`, `VM_RequestHeaderExists`, `VM_GetRequestHeaderLongLong`, iterator APIs, `VM_CommandFilterGetRequestHeader`, `VM_SetCommandlogMetadata`; register all in API table |
| `src/valkeymodule.h` | Modify | Add new API declarations, types, `VALKEYMODULE_GET_API` entries |
| `src/redismodule.h` | Modify | Add compatibility aliases |
| `src/commandlog.c` | Modify | Extend entry creation to include metadata; extend reply to include metadata |
| `src/commandlog.h` | Modify | Add metadata field to `commandlogEntry` |
| `src/modules/helloheaders.c` | **New** | Trace-ID reference module |
| `src/modules/CMakeLists.txt` | Modify | Add helloheaders target |
| `src/modules/Makefile` | Modify | Add helloheaders target |
| `tests/unit/resp4.tcl` | **New** | Protocol-level RESP4 tests |
| `tests/unit/moduleapi/headers.tcl` | **New** | Module API header tests |

### Estimated Total Effort

| Phase | Days |
|-------|------|
| Phase 1: Protocol Negotiation | 0.5 |
| Phase 2: Request Header Parsing | 3-4 |
| Phase 3: Header Storage on Client | 1-2 |
| Phase 4: Module API | 3-4 |
| Phase 5: Lifecycle & Config | 1-2 |
| Phase 6: Trace-ID Module | 2-3 |
| Phase 7: Testing | 3-4 |
| Phase 8: valkey-cli Headers | 2-3 |
| **Total** | **~16-22 days** |

### Implementation Order

Phases 1-3 should be done sequentially (each builds on the prior). Phase 4 can begin once Phase 3 is stable. Phase 5 is done in parallel with Phase 4. Phase 6 depends on Phase 4. Phase 7 is incremental throughout.

Recommended commit structure:
1. **Commit 1**: Phase 1 (HELLO 4) — small, reviewable, testable independently
2. **Commit 2**: Phases 2+3 (parsing + storage) — the core engine change
3. **Commit 3**: Phase 4 (module API) — the module-facing interface
4. **Commit 4**: Phase 5 (config + lifecycle hardening)
5. **Commit 5**: Phase 6 (trace-id reference module)
6. **Commit 6**: Phase 7 (full test suite)
