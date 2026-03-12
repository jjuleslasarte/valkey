# Idempotency Token Module for Valkey (RESP4)

## Design Document

**Status:** Draft  
**Author:** Valkey Contributors  
**Date:** 2026-03  
**Depends on:** RESP4 request headers (this branch)

---

## 1. Problem Statement

From the [RESP4 motivation doc](../resp4.md): Netflix's Key-Value Data Abstraction Layer (KV DAL) requires the underlying databases to be idempotent to support:

1. **Request hedging** — submitting multiple attempts of the same request in parallel to achieve best-of-N latency
2. **Retry after timeouts** — retaining a queue of timed-out requests and retrying them safely

**Valkey is not idempotent.** If a client sends `INCR counter` and the response is lost (timeout), retrying the same `INCR counter` increments twice. There's no way for Valkey to know the second request is a retry of the first.

Netflix currently works around this by maintaining per-key timestamps in separate data structures and using Lua scripts to atomically check-and-set. This is fragile, doesn't work cross-region, and adds significant complexity.

## 2. Solution: `idempotency-token` RESP4 Header

With RESP4, the client sends an **idempotency token** as a request header alongside any write command. The module intercepts every write, and:

- If the token is **new**: execute the command, store the token → result mapping, return the result
- If the token is **seen before**: skip execution, return the cached result

```
|1\r\n
$17\r\nidempotency-token\r\n
$36\r\n550e8400-e29b-41d4-a716-446655440000\r\n
*3\r\n$3\r\nSET\r\n$3\r\nfoo\r\n$3\r\nbar\r\n
```

The command executes only once, regardless of how many times this exact request is sent.

## 3. Architecture

```
Client (KV DAL)                    Valkey + idempotency module
    │                                     │
    │── RESP4 header: idempotency-token ──►│
    │── SET foo bar ─────────────────────►│
    │                                     │
    │                              ┌──────┴──────┐
    │                              │ Command      │
    │                              │ Filter       │
    │                              │              │
    │                              │ token seen?  │
    │                              │   YES → skip │──► return cached result
    │                              │   NO  → pass │──► execute command
    │                              │              │       │
    │                              │ store token  │◄──────┘
    │                              │ + result     │
    │                              └──────┬──────┘
    │                                     │
    │◄── reply (+ reply attributes) ──────│
    │     idempotent: true/false          │
    │     token-status: new/cached        │
```

## 4. Detailed Design

### 4.1 Token Storage

Tokens are stored in a **Valkey hash** per logical namespace:

```
HSET __idempotency:{namespace} {token} {serialized_result}
```

- **Key:** `__idempotency:{namespace}` — a Valkey hash. Namespace defaults to the DB index or can be provided via a `idempotency-namespace` header.
- **Field:** The idempotency token (UUID, timestamp, or any string ≤ 128 bytes)
- **Value:** Serialized result of the original execution (RESP-encoded reply)

Using a hash allows efficient cleanup (HSCAN + HDEL for expired tokens) and keeps all tokens in a single key per namespace.

### 4.2 Token Lifecycle

```
                    ┌─────────────┐
                    │ Token       │
         ┌────────►│ received    │
         │         └──────┬──────┘
         │                │
         │          token exists?
         │           /         \
         │         NO           YES
         │         │             │
         │    ┌────▼────┐  ┌────▼────┐
         │    │ Execute  │  │ Return  │
         │    │ command  │  │ cached  │
         │    └────┬────┘  │ result  │
         │         │       └────┬────┘
         │    ┌────▼────┐       │
         │    │ Store    │       │
         │    │ token +  │       │
         │    │ result   │       │
         │    └────┬────┘       │
         │         │             │
         │    ┌────▼─────────────▼────┐
         │    │ Set TTL on token      │
         │    │ (default: 24 hours)   │
         └────┤ Reply to client       │
              │ + reply attributes:   │
              │   token-status: new   │
              │   or: cached          │
              └───────────────────────┘
```

### 4.3 RESP4 Headers

| Header | Required | Type | Description |
|--------|----------|------|-------------|
| `idempotency-token` | Yes (for idempotent behavior) | bulk string | Unique token (UUID, timestamp, request-id). Max 128 bytes. |
| `idempotency-namespace` | No | bulk string | Logical namespace for token isolation. Default: `default`. |
| `idempotency-ttl` | No | integer | Token retention in seconds. Default: 86400 (24h). |

### 4.4 Reply Attributes

When the module processes an idempotent request, it adds reply attributes:

| Attribute | Type | Description |
|-----------|------|-------------|
| `idempotent` | boolean | `true` if the module processed this request |
| `token-status` | string | `new` (first execution), `cached` (replay), `expired` (token was evicted) |
| `token` | string | Echo of the idempotency token |

### 4.5 Module Commands

#### IDEMPOTENT.INFO `<token>`
Returns information about a stored token: when it was created, its TTL, the cached result type.

#### IDEMPOTENT.INVALIDATE `<token>`
Explicitly removes a token, allowing the command to be re-executed.

#### IDEMPOTENT.STATS
Returns module statistics:
- `tokens_stored` — current number of stored tokens
- `cache_hits` — number of times a cached result was returned
- `cache_misses` — number of new executions
- `tokens_expired` — number of tokens that aged out
- `tokens_invalidated` — number of explicit invalidations

#### IDEMPOTENT.FLUSH [`<namespace>`]
Remove all stored tokens (or all in a namespace).

### 4.6 Conflict Resolution: Last-Writer-Wins (LWW)

For the Netflix use case, idempotency isn't just "execute once" — it's **LWW conflict resolution** using timestamps as tokens. The module supports this via a configurable mode:

**Mode 1: Exact Idempotency (default)**
- Token is an opaque string (UUID)
- Same token → return cached result
- Different token → execute normally

**Mode 2: LWW with Timestamps**
- Token is a numeric timestamp (microseconds since epoch)
- For each key, the module tracks the highest timestamp that wrote to it
- A write with a **lower** timestamp than the stored one is **rejected** (stale write)
- A write with a **higher** timestamp proceeds and updates the stored timestamp
- A write with the **same** timestamp returns the cached result (retry)

```
|1\r\n
$17\r\nidempotency-token\r\n
:1698776172000000\r\n          ← integer: microsecond timestamp
*3\r\n$3\r\nSET\r\n$3\r\nfoo\r\n$3\r\nbar\r\n
```

This maps directly to the CRDT module's sequence number mechanism described in the [RESP4 motivation doc](../resp4.md#321-high-level-idea).

### 4.7 Which Commands Get Intercepted?

The module uses a **command filter** that checks for the `idempotency-token` header. It only intercepts commands that have the header — commands without it pass through untouched.

Write commands where idempotency is meaningful:
- `SET`, `SETNX`, `SETEX`, `PSETEX`, `MSET`, `MSETNX`
- `DEL`, `UNLINK`
- `INCR`, `INCRBY`, `INCRBYFLOAT`, `DECR`, `DECRBY`
- `HSET`, `HMSET`, `HDEL`, `HINCRBY`
- `LPUSH`, `RPUSH`, `LPOP`, `RPOP`, `LSET`
- `SADD`, `SREM`, `SMOVE`
- `ZADD`, `ZREM`, `ZINCRBY`
- `XADD`
- `EXPIRE`, `PEXPIRE`, `EXPIREAT`, `PERSIST`

Read commands are naturally idempotent and don't need interception.

### 4.8 Storage Overhead

Per token stored:
- Hash field: token string (≤128 bytes)
- Hash value: serialized RESP reply (typically 3-50 bytes for simple replies like OK, integers)
- Estimated: ~200 bytes per token

At 1M active tokens: ~200MB. Tokens expire via TTL.

## 5. Implementation Plan

### 5.1 Module Structure

```c
// idempotency.c

// OnLoad:
//   RegisterRequestHeader("idempotency-token", ...)
//   RegisterRequestHeader("idempotency-namespace", ...)
//   RegisterRequestHeader("idempotency-ttl", ...)
//   RegisterCommandFilter(IdempotencyFilter, VALKEYMODULE_CMDFILTER_NOSELF)
//   CreateCommand("idempotent.info", ...)
//   CreateCommand("idempotent.invalidate", ...)
//   CreateCommand("idempotent.stats", ...)
//   CreateCommand("idempotent.flush", ...)

// Filter callback (runs before every command):
//   1. Check if idempotency-token header present
//   2. If not → pass through (return)
//   3. Look up token in __idempotency:{namespace} hash
//   4. If found → replace command args with cached reply, set reply attributes
//   5. If not found → let command execute, then in post-notification:
//      store token → result in hash, set EXPIRE
```

### 5.2 Key Challenge: Capturing the Reply

The command filter runs **before** the command executes. To implement idempotency, we need to:

1. **Before execution:** Check if token exists → if yes, we need to prevent execution and return cached result
2. **After execution:** Store the result for the token

**Approach A: OTEL.EXEC-style wrapper command**
- Provide `IDEMPOTENT.EXEC <token> <command> [args...]` — module executes via `ValkeyModule_Call()`, captures the reply, stores it, returns it
- Pro: Clean, no filter hacks. Con: Changes client command syntax.

**Approach B: Command filter + MULTI/EXEC interception**  
- Filter detects token, replaces the command with an internal module command that wraps the original
- Pro: Transparent. Con: More complex.

**Approach C: Command filter for cache hits, `AddPostNotificationJob` for cache misses**
- Filter checks token. If found → reply with cached result (block original command by replacing args)
- If not found → let command proceed. Use `AddPostNotificationJob` callback to capture and store the result
- Pro: Transparent for the client. Con: `AddPostNotificationJob` doesn't have access to the command reply.

**Recommendation: Approach A (wrapper command) for v1**, with Approach B as a future enhancement.

The wire protocol for the client becomes:
```
|2\r\n
$17\r\nidempotency-token\r\n$36\r\n550e8400-e29b-41d4-a716-446655440000\r\n
$15\r\nidempotency-ttl\r\n:86400\r\n
*4\r\n$15\r\nIDEMPOTENT.EXEC\r\n$3\r\nSET\r\n$3\r\nfoo\r\n$3\r\nbar\r\n
```

The client library can abstract this — the user calls `client.set("foo", "bar", idempotency_token="...")` and the library wraps it in `IDEMPOTENT.EXEC`.

### 5.3 Serialization of Cached Replies

Replies are stored as RESP-encoded strings:
- `+OK\r\n` → 5 bytes for a simple OK
- `:42\r\n` → 4 bytes for an integer
- `$3\r\nbar\r\n` → 9 bytes for a bulk string
- `*2\r\n$3\r\nfoo\r\n$3\r\nbar\r\n` → array reply

We use `ValkeyModule_CallReplyProto()` to get the raw RESP encoding of the reply and store it directly.

### 5.4 Phase 1 Scope (MVP)

1. `IDEMPOTENT.EXEC` command with token from RESP4 header
2. Token storage in `__idempotency:default` hash
3. TTL-based expiration (EXPIRE on the hash key per-token is not possible — use a separate sorted set for TTL tracking, or periodic HSCAN cleanup)
4. Reply attributes: `token-status: new|cached`
5. `IDEMPOTENT.STATS` command
6. Basic demo with Python client

### 5.5 Phase 2 (Future)

1. LWW mode with timestamp-based conflict resolution
2. Transparent command filter (no `IDEMPOTENT.EXEC` wrapper needed)
3. Namespace support
4. Configurable TTL per-token
5. Memory limit with LRU eviction of tokens
6. Cluster-aware token storage

## 6. Client Integration Example

### Python (with RESP4 client)

```python
import uuid

def idempotent_set(client, key, value, token=None):
    """SET with idempotency — safe to retry."""
    if token is None:
        token = str(uuid.uuid4())
    
    headers = {"idempotency-token": token}
    result = client.command("IDEMPOTENT.EXEC", "SET", key, value, headers=headers)
    
    attrs = client.last_reply_attributes or {}
    status = attrs.get("token-status", "unknown")
    
    if status == "cached":
        print(f"  Idempotent replay: token {token[:8]}... → cached result")
    else:
        print(f"  New execution: token {token[:8]}... → fresh result")
    
    return result

# First call: executes SET
token = str(uuid.uuid4())
idempotent_set(client, "order:123", "confirmed", token=token)
# → New execution: token 550e8400... → fresh result

# Retry with same token: returns cached result, no re-execution
idempotent_set(client, "order:123", "confirmed", token=token)
# → Idempotent replay: token 550e8400... → cached result

# Different token: new execution
idempotent_set(client, "order:123", "shipped", token=str(uuid.uuid4()))
# → New execution: token 7c9e6679... → fresh result
```

### Netflix KV DAL Pattern (Request Hedging)

```python
import asyncio

async def hedged_set(client, key, value, token):
    """Send same request to 3 replicas, first response wins."""
    headers = {"idempotency-token": token}
    
    tasks = [
        asyncio.create_task(
            client.command("IDEMPOTENT.EXEC", "SET", key, value, headers=headers)
        )
        for _ in range(3)  # 3 parallel attempts
    ]
    
    # First to complete wins — other two are idempotent replays
    done, pending = await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
    for t in pending:
        t.cancel()
    
    return done.pop().result()
```

## 7. Relationship to RESP4

This module is the **primary motivating use case** for RESP4 request headers. Without RESP4, implementing idempotency requires:

- Wrapping every command in MULTI/EXEC with a custom timestamp command (the Option I approach from the spec doc)
- Maintaining separate timestamp data structures per key
- Using Lua scripts for atomic check-and-set

With RESP4, the idempotency token travels as out-of-band metadata — no command syntax changes, no MULTI/EXEC overhead, no Lua scripts. The module reads the header in a command filter and handles everything transparently.

## 8. Open Questions

1. **Should cached replies have a maximum size?** Large replies (e.g., LRANGE with thousands of elements) could consume significant memory. Should we cap at N bytes and fall back to re-execution for large replies?

2. **Token collision handling?** If two different commands use the same token, the second will get the first's cached result. Should we hash the command+args alongside the token to detect this?

3. **Cluster behavior?** In a cluster, should tokens be local to each node, or should there be a coordination mechanism? Local-per-node matches the "transport-level metadata" design of RESP4.

4. **Interaction with transactions?** Should `IDEMPOTENT.EXEC` work inside MULTI/EXEC? The token would apply to the single command, not the whole transaction.
