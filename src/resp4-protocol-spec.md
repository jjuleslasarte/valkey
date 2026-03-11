# RESP4: Valkey Serialization Protocol Version 4

## Protocol Specification

**Version**: 1.0 (Draft)
**Status**: Implemented
**Authors**: Valkey Contributors
**Date**: 2026-03

---

## Table of Contents

1. [Introduction](#1-introduction)
2. [Motivation](#2-motivation)
3. [Protocol Overview](#3-protocol-overview)
4. [Protocol Negotiation](#4-protocol-negotiation)
5. [Request Header Encoding](#5-request-header-encoding)
6. [Header Semantics](#6-header-semantics)
7. [Header Limits](#7-header-limits)
8. [Unregistered Header Policy](#8-unregistered-header-policy)
9. [Pipelining Behavior](#9-pipelining-behavior)
10. [MULTI/EXEC Transactions](#10-multiexec-transactions)
11. [Replication and Persistence](#11-replication-and-persistence)
12. [Module API](#12-module-api)
13. [Configuration](#13-configuration)
14. [valkey-cli Support](#14-valkey-cli-support)
15. [Backward Compatibility](#15-backward-compatibility)
16. [Use Cases](#16-use-cases)
17. [Security Considerations](#17-security-considerations)
18. [References](#18-references)

---

## 1. Introduction

RESP4 is the fourth version of the Valkey (formerly Redis) Serialization Protocol. It is a **strict superset of RESP3** — all RESP3 data types, reply attributes, and client behavior remain unchanged. The single addition is that RESP4 permits clients to send **request-side attributes** (referred to as *request headers*) immediately before a command array.

Request headers are key-value metadata pairs that travel alongside a command but are not part of the command's arguments. They are parsed by the Valkey engine, stored on the connection for the duration of the command, and made available to server modules through a new set of Module APIs. After the command completes, headers are automatically cleared.

This design follows established patterns from HTTP headers, gRPC metadata, and messaging-system properties, bringing structured out-of-band metadata transport to the Valkey wire protocol.

### 1.1 Terminology

| Term | Definition |
|------|-----------|
| **Request header** | A key-value pair sent by a RESP4 client before a command array using the RESP3 attribute encoding (`\|`). |
| **Header key** | A bulk-string identifier for a header. Case-insensitive; normalized to lowercase by the server. |
| **Header value** | The value associated with a header key. May be any RESP3 scalar type. |
| **Registered header** | A header name that a loaded module has explicitly declared interest in via the Module API. |
| **Command array** | The standard RESP multibulk array (`*N\r\n...`) that encodes a Valkey command and its arguments. |

### 1.2 Notation Conventions

- `\r\n` denotes the two-byte CRLF sequence.
- `$N` denotes a RESP bulk string prefix where N is the byte length of the string.
- `*N` denotes a RESP array prefix where N is the element count.
- `|N` denotes a RESP attribute prefix where N is the number of key-value pairs.

## 2. Motivation

### 2.1 The Metadata Gap in RESP2/3

RESP2 and RESP3 define how clients send commands and how the server sends replies. RESP3 introduced **reply-side attributes** — metadata that the server can attach to responses. However, there is no corresponding mechanism for clients to send metadata *to* the server. This asymmetry means that any request-level context (correlation IDs, idempotency tokens, tracing information, authorization context) must be encoded as extra command arguments, which:

- **Pollutes command syntax**: Every command that needs metadata must be modified.
- **Breaks existing tooling**: Proxies, monitoring tools, and client libraries must understand the modified argument lists.
- **Prevents generic middleware**: Without a standard metadata channel, modules cannot implement cross-cutting concerns (tracing, auth, routing) without command-specific knowledge.

### 2.2 Industry Precedent

Most modern client-server protocols provide a metadata channel separate from the payload:

| Protocol | Mechanism |
|----------|-----------|
| HTTP/1.1, HTTP/2 | Request headers |
| gRPC | Metadata key-value pairs |
| AMQP | Message properties and headers |
| Apache Kafka | Record headers |
| Amazon SQS | Message attributes |

RESP4 brings Valkey in line with this universal pattern.

### 2.3 Concrete Use Case: Idempotency Tokens

A primary motivating use case is supporting **idempotent write operations**. Infrastructure layers (such as key-value abstraction layers built atop Valkey) need to safely retry or hedge requests without risking duplicate side effects. With RESP4, a module can register a header (e.g., `idempotency-token`) and use it to implement last-writer-wins (LWW), compare-and-set (CAS), or full idempotency semantics — all without modifying any Valkey command syntax.

## 3. Protocol Overview

### 3.1 Relationship to Prior Versions

| Version | Key Additions |
|---------|--------------|
| RESP2 | Simple strings, errors, integers, bulk strings, arrays |
| RESP3 | Doubles, booleans, big numbers, maps, sets, verbatim strings, pushes, **reply-side attributes** |
| **RESP4** | **Request-side attributes (request headers)** |

RESP4 does not introduce any new data types. It reuses the existing RESP3 attribute type (`|`) and extends its applicability to the request direction.

### 3.2 High-Level Data Flow

```
Client (RESP4)                     Server                          Module
    │                                 │                               │
    │── |N\r\n (request headers) ──►  │                               │
    │── *M\r\n (command array)   ──►  │                               │
    │                                 │── parse headers ──►           │
    │                                 │   store in client struct      │
    │                                 │                               │
    │                                 │── execute command ──────────► │
    │                                 │   module reads headers via    │
    │                                 │   VM_GetRequestHeader() etc.  │
    │                                 │                               │
    │                                 │── clear headers               │
    │◄── reply ────────────────────── │                               │
```

### 3.3 Key Properties

1. **Opt-in**: Only clients that negotiate RESP4 via `HELLO 4` can send request headers. RESP2 and RESP3 clients are completely unaffected.
2. **Per-command scope**: Each header block applies to exactly the next command array. Headers do not persist across commands.
3. **Module-consumed**: The engine parses and stores headers but does not interpret them. Modules register interest in headers and read them during command execution.
4. **Zero overhead for non-RESP4 clients**: Header storage is lazily allocated only when a RESP4 client sends headers. RESP2/3 connections incur no additional memory or CPU cost.
5. **Not replicated or persisted**: Headers are transport-level metadata. They are not written to AOF, not propagated to replicas, and not included in replication streams.

## 4. Protocol Negotiation

### 4.1 HELLO Command

RESP4 is negotiated using the existing `HELLO` command. A client requests RESP4 by sending:

```
HELLO 4 [AUTH username password] [SETNAME clientname]
```

The server responds with a map containing connection properties, including `proto` set to `4`:

```
%7
$6
server
$6
valkey
$7
version
$5
8.1.0
$5
proto
:4
$2
id
:1
$4
mode
$10
standalone
$4
role
$6
master
$7
modules
*0
```

### 4.2 Version Validation

- The server accepts `HELLO` with version values `2`, `3`, or `4`.
- `HELLO 5` or any version greater than `4` is rejected with `-NOPROTO unsupported protocol version`.
- `HELLO 0` or `HELLO 1` is rejected as invalid.

### 4.3 Downgrade

A client that has negotiated RESP4 may downgrade to RESP3 or RESP2 by sending `HELLO 3` or `HELLO 2` at any time. Upon downgrade:

- The connection's protocol version (`client->resp`) is updated.
- Any pending request headers are cleared.
- The server no longer accepts `|` attribute prefixes on the request side for that connection.

### 4.4 Server Internals

- The client's protocol version is stored in `client->resp` (integer field). RESP4 clients have `client->resp == 4`.
- All existing checks for `resp == 3` (e.g., in reply formatting, cluster slot caching, module context flags) are updated to `resp >= 3`, ensuring RESP4 clients receive RESP3-style replies. RESP4 does not change reply encoding.

## 5. Request Header Encoding

### 5.1 Wire Format

A request header block uses the RESP3 **attribute** type (prefix `|`) and is sent immediately before the command array. The general form is:

```
|<n>\r\n
$<key1_len>\r\n<key1>\r\n <value1_type><value1>\r\n
$<key2_len>\r\n<key2>\r\n <value2_type><value2>\r\n
... (repeated for n key-value pairs)
*<m>\r\n
$<cmd_len>\r\n<command>\r\n
$<arg1_len>\r\n<arg1>\r\n
...
```

Where:
- `<n>` is the number of header key-value pairs (attribute count).
- Each **key** MUST be a bulk string (`$` prefix). Simple string keys are not permitted.
- Each **value** may be any RESP3 scalar type: bulk string (`$`), simple string (`+`), integer (`:`), double (`,`), boolean (`#`), or null (`_`).
- `<m>` is the number of elements in the command array (command name + arguments).

### 5.2 Complete Example

A `SET foo bar` command with a `trace-id` header and an `idempotency-token` header:

```
|2\r\n
$8\r\ntrace-id\r\n$12\r\nabc-123-def\r\n
$17\r\nidempotency-token\r\n:1698776172000000\r\n
*3\r\n
$3\r\nSET\r\n
$3\r\nfoo\r\n
$3\r\nbar\r\n
```

Breakdown:
- `|2\r\n` — attribute block with 2 key-value pairs.
- `$8\r\ntrace-id\r\n` — first key: bulk string "trace-id" (8 bytes).
- `$12\r\nabc-123-def\r\n` — first value: bulk string "abc-123-def" (12 bytes).
- `$17\r\nidempotency-token\r\n` — second key: bulk string "idempotency-token" (17 bytes).
- `:1698776172000000\r\n` — second value: integer 1698776172000000.
- `*3\r\n...\r\n` — the standard `SET foo bar` command array.

### 5.3 Command Without Headers

A RESP4 client MAY send commands without any header block. In this case, the command array begins directly with `*`, and the server processes it identically to RESP3:

```
*3\r\n
$3\r\nSET\r\n
$3\r\nfoo\r\n
$3\r\nbar\r\n
```

### 5.4 Parsing Rules

1. When the parser encounters `|` as the first byte of a new request from a RESP4 client, it enters **header parsing mode**.
2. The parser reads the attribute count `N` and then reads `N` key-value pairs incrementally (supporting partial reads across TCP segments).
3. After all `N` pairs are parsed, the parser transitions back to normal mode and expects the next byte to be `*` (a command array).
4. If a RESP2 or RESP3 client sends `|` at the start of a request, it is treated as an unknown/inline command character and results in a parse error.
5. Two consecutive `|` attribute blocks without an intervening `*` command array is a protocol error.

## 6. Header Semantics

### 6.1 Scope

A header block applies to **exactly the next command array** that follows it. Once the command completes (whether successfully or with an error), all headers associated with that command are cleared from the client connection. Headers never carry over to subsequent commands.

### 6.2 Key Normalization

All header keys are normalized to **lowercase** at parse time. The header key `Trace-ID` is stored as `trace-id`. This matches HTTP header convention and ensures case-insensitive matching.

### 6.3 Duplicate Keys

If a header block contains duplicate keys, the **last value wins**. For example:

```
|2\r\n
$8\r\ntrace-id\r\n$3\r\naaa\r\n
$8\r\ntrace-id\r\n$3\r\nbbb\r\n
```

The effective value of `trace-id` is `bbb`.

### 6.4 Immutability

Request headers are **read-only** from the module's perspective. Modules cannot modify, delete, or inject request headers. They can only read what the client sent. If a module needs to propagate header-derived data, it must explicitly encode it into command arguments or separate commands (e.g., how the CRDT module uses `CRDTMETA`).

### 6.5 Reply Attributes

RESP4 does not change reply-side attributes. Reply attributes continue to use the existing RESP3 mechanism (`ValkeyModule_ReplyWithAttribute`). Request headers and reply attributes are independent — a request header does not automatically become a reply attribute.

### 6.6 Inline Commands

Request headers are only supported with the **multibulk** (binary-safe) command format. Inline commands (plain text commands not prefixed with `*`) cannot carry headers. This is consistent with the fact that inline commands are a simplified format intended for human use, not programmatic clients.

## 7. Header Limits

To prevent abuse and bound memory consumption, the server enforces configurable limits on request headers. All limits are checked during parsing; exceeding any limit causes the server to reject the command with `-ERR header limit exceeded` before execution.

### 7.1 Default Limits

| Limit | Config Key | Default | Min | Max | Description |
|-------|-----------|---------|-----|-----|-------------|
| Max headers per command | `resp4-max-headers` | 8 | 1 | 64 | Maximum number of key-value pairs in a single `\|N` block. |
| Max header key length | — | 64 bytes | — | — | Header names are short identifiers, not data. Enforced at parse time. |
| Max header value length | `resp4-max-header-value-len` | 4096 bytes | 64 | 65536 | Sufficient for trace IDs, tokens, timestamps. |
| Max total header bytes | — | 8192 bytes | — | — | Total wire bytes consumed by all header key-value pairs for a single command. |

### 7.2 Rationale

- **Max 8 headers by default**: Practical use cases (tracing, idempotency, auth, routing) rarely need more than a handful of headers. The limit prevents clients from using headers as a general-purpose data channel.
- **64-byte key limit**: Header names are identifiers (e.g., `trace-id`, `idempotency-token`). Long names suggest misuse.
- **4096-byte value limit**: Accommodates UUIDs, JWTs, timestamps, and similar tokens. Values needing more space should be command arguments, not headers.
- **8192-byte total limit**: A hard cap on per-command header memory, independent of the individual limits.

### 7.3 Error Behavior

When a limit is exceeded:

1. The server sends `-ERR header limit exceeded` to the client.
2. The partially parsed headers are discarded.
3. The subsequent command array (if any) is also discarded — the entire request (headers + command) is treated as one unit.
4. The client connection remains open and can send subsequent commands.

## 8. Unregistered Header Policy

### 8.1 Default Behavior: Ignore

By default, if a client sends a header that no loaded module has registered, the server **silently ignores** it. The header is parsed, stored on the client for the command's duration, and discarded after the command completes — but no module reads it.

This behavior is forward-compatible: clients can send headers that will be consumed by modules not yet deployed, and modules can be loaded/unloaded without breaking existing clients.

### 8.2 Strict Mode

The server supports an optional strict mode configured via:

```
CONFIG SET resp4-unknown-header-policy error
```

When set to `error`, the server checks each header key against the set of registered headers. If any header name is not registered by a loaded module, the server rejects the command with:

```
-ERR unknown header 'header-name'
```

This mode is useful in controlled environments where accidental or misspelled headers should be caught early.

### 8.3 Policy Values

| Value | Behavior |
|-------|----------|
| `ignore` (default) | Unregistered headers are silently accepted and discarded after the command. |
| `error` | Unregistered headers cause the command to be rejected before execution. |

This is a **server-global** setting, not per-module or per-connection.

## 9. Pipelining Behavior

### 9.1 One Header Block Per Command

When pipelining, each command that needs headers MUST be preceded by its own `|` attribute block. A header block applies only to the immediately following command array. Example of three pipelined commands:

```
|1\r\n$8\r\ntrace-id\r\n$12\r\nabc-123-def\r\n
*3\r\n$3\r\nSET\r\n$3\r\nfoo\r\n$3\r\nbar\r\n
|1\r\n$8\r\ntrace-id\r\n$12\r\ndef-456-ghi\r\n
*3\r\n$3\r\nSET\r\n$3\r\nbaz\r\n$3\r\nqux\r\n
*2\r\n$3\r\nGET\r\n$3\r\nfoo\r\n
```

- The first `SET` carries `trace-id: abc-123-def`.
- The second `SET` carries `trace-id: def-456-ghi`.
- The `GET` has no headers.

### 9.2 Parser State Machine

When processing a pipelined input buffer, the parser follows this state machine:

```
  ┌──────────┐
  │ START    │
  └────┬─────┘
       │ read first byte
       ▼
  ┌──────────┐     '|' (RESP4 only)     ┌──────────────┐
  │ DISPATCH ├──────────────────────────►│ PARSE HEADERS│
  │          │                           └──────┬───────┘
  │          │     '*'                          │ headers complete
  │          ├─────────────┐                    │ expect '*'
  └──────────┘             │                    ▼
                           │             ┌──────────────┐
                           └────────────►│ PARSE COMMAND│
                                         └──────┬───────┘
                                                │ command complete
                                                │ associate headers
                                                ▼
                                         ┌──────────────┐
                                         │ QUEUE/EXECUTE│
                                         └──────┬───────┘
                                                │
                                                ▼
                                           back to START
```

### 9.3 Queued Commands

For pipelined commands, parsed headers are stored alongside the command in the `parsedCommand` queue structure. When a queued command is dequeued for execution, its headers are transferred to the active `client->request_headers` dict and cleared after execution.

## 10. MULTI/EXEC Transactions

### 10.1 Per-Command Headers

Headers sent before a command inside a `MULTI/EXEC` block apply to **that specific command**, not the entire transaction. Each queued command within a transaction independently carries its own headers (or no headers).

```
*1\r\n$5\r\nMULTI\r\n
|1\r\n$17\r\nidempotency-token\r\n:1698776172000000\r\n
*3\r\n$3\r\nSET\r\n$4\r\nkey1\r\n$6\r\nvalue1\r\n
|1\r\n$17\r\nidempotency-token\r\n:1698776173000000\r\n
*3\r\n$3\r\nSET\r\n$4\r\nkey2\r\n$6\r\nvalue2\r\n
*3\r\n$3\r\nSET\r\n$4\r\nkey3\r\n$6\r\nvalue3\r\n
*1\r\n$4\r\nEXEC\r\n
```

In this example:
- `SET key1 value1` carries `idempotency-token: 1698776172000000`.
- `SET key2 value2` carries `idempotency-token: 1698776173000000`.
- `SET key3 value3` has no headers (server generates its own metadata as applicable).

### 10.2 Headers on MULTI and EXEC

The `MULTI` and `EXEC` commands themselves MAY carry headers, though this is uncommon. Headers on `MULTI` are available during the `MULTI` command processing; headers on `EXEC` are available during `EXEC` processing. They do not propagate to the queued commands within the transaction.

### 10.3 No Nested Transactions

Valkey does not support nested `MULTI/EXEC` blocks. There is no mechanism to apply a single header to all commands in a transaction simultaneously. Clients that need the same header on every command in a transaction must prepend the header block to each individual command.

## 11. Replication and Persistence

### 11.1 Headers Are Not Replicated

Request headers are **not propagated** to replicas. When a write command is replicated (via the replication stream or via PSYNC), only the command array is sent. Headers are transport-level metadata meaningful at the point of origin and are not part of the durable command.

This matches HTTP semantics: request headers are per-hop metadata, not persisted state.

### 11.2 Headers Are Not Persisted to AOF

The Append-Only File (AOF) records commands as pure RESP command arrays. Request headers are not written to AOF. When an AOF file is replayed (e.g., during server restart), commands execute without any headers.

### 11.3 Module-Level Propagation

If a module needs to replicate header-derived information, it MUST explicitly encode that information into the replicated command. For example, a CRDT module receiving an `idempotency-token` header might:

1. Extract the token value from the header during command processing.
2. Replicate the command wrapped in a `MULTI/EXEC` block with an internal metadata command (e.g., `CRDTMETA`) that carries the token value.

This explicit approach ensures that replication semantics are controlled by the module, not assumed by the protocol.

### 11.4 Cluster Forwarding

When a command is redirected to a different node via `-MOVED` or `-ASK`, the client is responsible for re-sending the headers with the redirected command. The server does not forward headers on behalf of the client during cluster redirections.

## 12. Module API

RESP4 request headers are consumed by Valkey modules through a set of new C API functions. These APIs are available only when the client connection has negotiated RESP4. For RESP2/3 clients, the APIs behave as if no headers were supplied (returning NULL or 0).

### 12.1 Header Registration

A module declares interest in specific header names so the server can optionally validate type constraints and enforce the unknown-header policy.

```c
int ValkeyModule_RegisterRequestHeader(
    ValkeyModuleCtx *ctx,
    const char *name,
    int flags,
    int expected_type
);
```

**Parameters**:
- `ctx` — Module context.
- `name` — Header name (case-insensitive; stored lowercase). Must not exceed 64 bytes.
- `flags` — Reserved for future use. Pass `0`.
- `expected_type` — RESP type constraint (e.g., `VALKEYMODULE_HEADER_TYPE_BULK_STRING`, `VALKEYMODULE_HEADER_TYPE_INTEGER`), or `-1` for any scalar type.

**Returns**: `VALKEYMODULE_OK` on success, `VALKEYMODULE_ERR` if the header name is already registered by another module.

**Behavior**:
- Registration does not make a header mandatory — it only declares recognition.
- If `expected_type` is set and a client sends a mismatched type, the server rejects the command with `-ERR header type mismatch` before execution.
- If multiple modules attempt to register the same header name, the first registration succeeds and subsequent ones fail.
- When a module is unloaded, its header registrations are automatically removed.

### 12.2 Header Retrieval

#### Existence Check

```c
int ValkeyModule_RequestHeaderExists(
    ValkeyModuleCtx *ctx,
    const char *name
);
```

Returns non-zero if the header `name` was present on the current request, zero otherwise.

#### Get Value as String

```c
ValkeyModuleString *ValkeyModule_GetRequestHeader(
    ValkeyModuleCtx *ctx,
    const char *name
);
```

Returns the header value as a `ValkeyModuleString *` if present, or `NULL` if absent. The returned pointer is owned by the server and is valid only for the duration of the current command callback. Modules MUST NOT free or retain it beyond the callback lifetime.

#### Get Value as Integer

```c
int ValkeyModule_GetRequestHeaderLongLong(
    ValkeyModuleCtx *ctx,
    const char *name,
    long long *ll
);
```

Attempts to coerce the header value to a `long long` and stores it in `*ll`. Returns `VALKEYMODULE_OK` on success, `VALKEYMODULE_ERR` if the header is absent or cannot be converted.

### 12.3 Header Iteration

Modules may iterate over all headers on the current request without knowing their names in advance. This supports generic middleware-style modules (logging, tracing, policy engines).

```c
ValkeyModuleRequestHeaderIter *ValkeyModule_RequestHeaderIterStart(
    ValkeyModuleCtx *ctx
);
```

Returns an iterator over all request headers, or `NULL` if no headers are present.

```c
int ValkeyModule_RequestHeaderIterNext(
    ValkeyModuleRequestHeaderIter *iter,
    ValkeyModuleString **name,
    ValkeyModuleString **value
);
```

Advances the iterator. Returns `1` if a header was retrieved (name and value are set), `0` if iteration is complete.

```c
void ValkeyModule_RequestHeaderIterStop(
    ValkeyModuleRequestHeaderIter *iter
);
```

Releases the iterator. Must be called after iteration is complete.

### 12.4 Command Filter Header Access

Command filters (registered via `ValkeyModule_RegisterCommandFilter`) can read request headers through a dedicated function:

```c
ValkeyModuleString *ValkeyModule_CommandFilterGetRequestHeader(
    ValkeyModuleCommandFilterCtx *fctx,
    const char *name
);
```

This allows filters to inspect headers before the command is dispatched, enabling middleware patterns such as attaching trace IDs to logging or rejecting commands based on authorization headers.

### 12.5 Commandlog Metadata

Modules can attach metadata to the current command that will be included in commandlog (slowlog) entries if the command qualifies:

```c
int ValkeyModule_SetCommandlogMetadata(
    ValkeyModuleCtx *ctx,
    const char *key,
    ValkeyModuleString *value
);
```

This is typically called from a command filter to propagate header values (e.g., `trace-id`) into commandlog entries for observability. The metadata is stored on the client for the command's duration and transferred to the commandlog entry upon creation.

### 12.6 API Summary Table

| Function | Purpose | Available In |
|----------|---------|-------------|
| `VM_RegisterRequestHeader` | Declare interest in a header name | Module `OnLoad` |
| `VM_RequestHeaderExists` | Check if a header is present | Command callback, filter |
| `VM_GetRequestHeader` | Get header value as string | Command callback, filter |
| `VM_GetRequestHeaderLongLong` | Get header value as integer | Command callback, filter |
| `VM_RequestHeaderIterStart` | Begin iterating all headers | Command callback |
| `VM_RequestHeaderIterNext` | Get next header in iteration | Command callback |
| `VM_RequestHeaderIterStop` | End iteration | Command callback |
| `VM_CommandFilterGetRequestHeader` | Read header from filter context | Command filter |
| `VM_SetCommandlogMetadata` | Attach metadata for commandlog | Command callback, filter |

## 13. Configuration

### 13.1 New Configuration Directives

All RESP4-related configuration is managed through standard `CONFIG SET`/`CONFIG GET` commands and can also be specified in `valkey.conf`.

| Directive | Type | Default | Range | Description |
|-----------|------|---------|-------|-------------|
| `resp4-max-headers` | Integer | `8` | 1–64 | Maximum number of header key-value pairs per command. |
| `resp4-max-header-value-len` | Integer | `4096` | 64–65536 | Maximum byte length of a single header value. |
| `resp4-unknown-header-policy` | Enum | `ignore` | `ignore`, `error` | Behavior when a client sends an unregistered header. |

### 13.2 Runtime Modification

All RESP4 configuration directives are **modifiable at runtime** via `CONFIG SET`:

```
CONFIG SET resp4-max-headers 16
CONFIG SET resp4-max-header-value-len 8192
CONFIG SET resp4-unknown-header-policy error
```

Changes take effect immediately for all subsequent commands. In-flight commands are not affected.

### 13.3 Configuration File Example

```
# RESP4 Request Header Settings
resp4-max-headers 8
resp4-max-header-value-len 4096
resp4-unknown-header-policy ignore
```

### 13.4 INFO Output

RESP4-related statistics are included in the `INFO` output under a dedicated section:

```
# RESP4
resp4_clients_connected:3
resp4_headers_received:12847
resp4_headers_rejected:0
```

## 14. valkey-cli Support

### 14.1 Command-Line Flags

`valkey-cli` supports RESP4 through new flags:

| Flag | Description |
|------|-------------|
| `--resp4` | Negotiate RESP4 with the server (sends `HELLO 4` on connect). |
| `--header name=value` | Attach a header to the command. May be specified multiple times. |

**Examples**:

```bash
# Single header
valkey-cli --resp4 --header trace-id=abc-123 SET foo bar

# Multiple headers
valkey-cli --resp4 --header trace-id=abc-123 --header request-id=42 SET foo bar
```

The `--header` flag requires `--resp4` to be set. Using `--header` without `--resp4` produces an error.

### 14.2 Interactive REPL Commands

In interactive mode, `valkey-cli` provides pseudo-commands for managing headers:

```
127.0.0.1:6379> HEADER trace-id my-trace-value
OK (header queued for next command)
127.0.0.1:6379> SET foo bar
OK
```

| Pseudo-Command | Description |
|----------------|-------------|
| `HEADER name value` | Queue a header for the next command sent to the server. |
| `CLEARHEADERS` | Clear all queued headers without sending them. |

**Behavior**:
- `HEADER` is a client-side-only pseudo-command — it is not sent to the server.
- Queued headers are consumed by the next real command and then cleared.
- Multiple `HEADER` commands can be issued before a single command to attach multiple headers.

### 14.3 Wire Output

When `valkey-cli` sends a command with queued headers, it prepends the `|N` attribute block to the RESP output before the `*M` command array. The headers are written to the socket in a single write with the command for efficiency.

### 14.4 Reply Attribute Display

When the server returns reply-side attributes (using the `|` prefix in responses), `valkey-cli --resp4` displays them in a distinct format above the reply:

```
127.0.0.1:6379> GET foo
# attribute: ttl=3600
"bar"
```

## 15. Backward Compatibility

### 15.1 RESP2 and RESP3 Clients

RESP4 is fully backward compatible with existing clients:

- **No behavior change**: Clients that do not send `HELLO 4` continue to operate under RESP2 or RESP3 exactly as before. The server never sends request-side attributes to clients.
- **No memory overhead**: The `client->request_headers` dict is `NULL` by default and only allocated when a RESP4 client sends headers. RESP2/3 connections incur zero additional memory.
- **No parsing overhead**: The `|` prefix is only recognized as a header when `client->resp >= 4`. For RESP2/3 clients, `|` at the start of input is treated as an inline command character (resulting in a parse error, same as before).

### 15.2 Reply Encoding

RESP4 clients receive replies encoded in RESP3 format. RESP4 does not introduce new reply types. All existing `resp >= 3` code paths apply to RESP4 clients. This means:

- Maps, sets, doubles, booleans, verbatim strings, and reply-side attributes all work as in RESP3.
- `addReplyDouble()`, cluster slot caching, module context flags, and similar functions use `resp >= 3` checks.

### 15.3 Proxy and Middleware Compatibility

Proxies and middleware that sit between RESP clients and Valkey servers should:

1. **Pass through `|` blocks**: If the proxy speaks RESP4 on both sides, it should forward header blocks transparently.
2. **Strip `|` blocks on downgrade**: If the proxy speaks RESP4 to the client but RESP3 to the server, it should strip header blocks (the server would reject them anyway).
3. **Be aware of the `|` prefix**: Proxies that parse RESP must be updated to recognize `|` as an attribute prefix on the request side for RESP4 connections.

### 15.4 Client Library Upgrade Path

Client libraries need the following changes to support RESP4:

1. Send `HELLO 4` during connection setup.
2. Provide an API for users to attach headers to commands (e.g., `client.set("foo", "bar", headers={"trace-id": "abc"})`).
3. Encode headers as a `|N` attribute block before the `*M` command array.
4. Handle reply-side attributes as in RESP3 (no change needed).

Libraries that do not implement RESP4 continue to work unchanged with RESP2/3.

## 16. Use Cases

### 16.1 Idempotency Tokens

A key-value abstraction layer sends idempotency tokens with write commands to enable safe retries and request hedging:

```
|1\r\n
$17\r\nidempotency-token\r\n
:1698776172000000\r\n
*3\r\n$3\r\nSET\r\n$3\r\nfoo\r\n$3\r\nbar\r\n
```

A module registers `idempotency-token`, extracts it during command processing, and uses it for last-writer-wins conflict resolution. Duplicate requests with the same token are idempotent.

### 16.2 Distributed Tracing

An OpenTelemetry-instrumented application propagates trace context through Valkey:

```
|2\r\n
$8\r\ntrace-id\r\n$32\r\n4bf92f3577b34da6a3ce929d0e0e4736\r\n
$7\r\nspan-id\r\n$16\r\n00f067aa0ba902b7\r\n
*2\r\n$3\r\nGET\r\n$8\r\nuser:123\r\n
```

A tracing module captures the trace and span IDs, correlates them with server-side processing, and optionally attaches them to commandlog entries for end-to-end observability.

### 16.3 Authentication and Authorization

A security module validates bearer tokens passed as headers, without modifying command syntax:

```
|1\r\n
$13\r\nauthorization\r\n
$24\r\nBearer eyJhbGciOiJSUz...\r\n
*2\r\n$3\r\nGET\r\n$3\r\nfoo\r\n
```

The module validates the token and applies ACLs before the command executes. This separates authentication from command logic.

### 16.4 Tenant Routing

In a multi-tenant environment, a routing module uses a `tenant` header to enforce isolation:

```
|1\r\n
$6\r\ntenant\r\n
$6\r\nacme01\r\n
*2\r\n$3\r\nGET\r\n$8\r\nuser:123\r\n
```

The module maps tenant IDs to specific databases or key prefixes, enforcing isolation without the client needing to manage key namespaces.

### 16.5 Request Correlation

A `request-id` header enables server-side logging and debugging:

```
|1\r\n
$10\r\nrequest-id\r\n
$12\r\nreq-9f812aa2\r\n
*2\r\n$4\r\nINCR\r\n$7\r\ncounter\r\n
```

A logging module captures the request ID and includes it in server logs, enabling correlation between client requests and server-side processing across microservice architectures.

## 17. Security Considerations

### 17.1 Header Size Limits

The configurable header limits (Section 7) prevent denial-of-service attacks through oversized headers. Without these limits, a malicious client could consume excessive server memory by sending large numbers of headers or headers with very large values.

Operators should review the default limits and adjust them based on their threat model and expected header usage patterns.

### 17.2 Header Content Validation

The server performs only structural validation of headers (correct RESP encoding, within size limits). It does **not** validate header content semantics. Modules that consume headers MUST validate the content according to their requirements. For example:

- A security module MUST validate bearer tokens, not assume they are well-formed.
- An idempotency module MUST validate that token values are within expected ranges.

### 17.3 Information Leakage

Headers may contain sensitive information (authorization tokens, internal identifiers). Operators should be aware that:

- Headers are visible in the server's memory during command processing.
- If a module attaches header values to commandlog entries, those values become visible via `COMMANDLOG GET` (slowlog).
- Headers are not encrypted by the RESP protocol. Use TLS (`--tls`) for transport encryption.

### 17.4 ACL Considerations

RESP4 headers are not subject to ACL rules. ACLs control command access, not header content. If header-based access control is needed, a module must implement it.

### 17.5 Strict Mode for Controlled Environments

The `resp4-unknown-header-policy error` configuration (Section 8.2) is recommended for production environments where the set of expected headers is known. This prevents clients from accidentally sending misspelled or unexpected headers that could indicate misconfiguration or attempted abuse.

## 18. References

1. **Valkey RESP Protocol Specification**: [https://valkey.io/topics/protocol/](https://valkey.io/topics/protocol/) — Official documentation for RESP2 and RESP3.
2. **RESP3 Specification**: [https://github.com/antirez/RESP3/blob/master/spec.md](https://github.com/antirez/RESP3/blob/master/spec.md) — The original RESP3 specification by Salvatore Sanfilippo.
3. **Valkey Module API Reference**: [https://valkey.io/topics/modules-api-ref/](https://valkey.io/topics/modules-api-ref/) — Documentation for the Valkey Module API.
4. **HTTP/1.1 Header Fields (RFC 9110)**: [https://www.rfc-editor.org/rfc/rfc9110#section-6.3](https://www.rfc-editor.org/rfc/rfc9110#section-6.3) — HTTP header semantics that influenced RESP4 header design.
5. **gRPC Metadata**: [https://grpc.io/docs/guides/metadata/](https://grpc.io/docs/guides/metadata/) — gRPC's metadata mechanism, a comparable pattern.
6. **OpenTelemetry Context Propagation**: [https://opentelemetry.io/docs/concepts/context-propagation/](https://opentelemetry.io/docs/concepts/context-propagation/) — Distributed tracing context propagation, a key use case for RESP4 headers.

---

*End of specification.*
