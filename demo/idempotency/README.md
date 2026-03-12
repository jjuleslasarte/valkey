# Idempotency Token Module — RESP4 Demo

This demo showcases Valkey's RESP4 Idempotency Token module, which makes any Valkey write command **idempotent** — safely retryable without side effects.

## The Problem

Without idempotency, retrying a command can cause bugs:

```
Client: INCR counter    → counter = 1
        (timeout, no response received)
Client: INCR counter    → counter = 2   ← WRONG! Should still be 1
```

With the idempotency module, the same token always returns the same result:

```
Client: INCR counter  + token=abc123  → counter = 1, status=new
        (timeout, no response received)
Client: INCR counter  + token=abc123  → counter = 1, status=cached  ← CORRECT!
```

## Quick Start

### 1. One-command demo (automated)

```bash
bash demo/idempotency/run-demo.sh
```

This starts a server, runs 4 demo scenarios, and stops the server. Takes ~3 seconds.

### 2. Interactive with valkey-cli

Start the server with the module:

```bash
# Build if needed
make -C src/modules idempotency.so

# Start server with module
./src/valkey-server --loadmodule src/modules/idempotency.so --enable-module-command yes
```

In another terminal, use `valkey-cli` with RESP4:

```bash
# Connect with RESP4 protocol
./src/valkey-cli --resp4

# === Demo: Idempotent SET ===

# First execution — SET key with a token
127.0.0.1:6379> HEADER idempotency-token my-unique-token-001
OK (header queued for next command)
127.0.0.1:6379> IDEMPOTENT.EXEC SET order:123 confirmed
# attribute: idempotent=true, token-status=new, token=my-unique-token-001
OK

# Retry with SAME token — returns cached result, key NOT re-written
127.0.0.1:6379> HEADER idempotency-token my-unique-token-001
OK (header queued for next command)
127.0.0.1:6379> IDEMPOTENT.EXEC SET order:123 DIFFERENT_VALUE
# attribute: idempotent=true, token-status=cached, token=my-unique-token-001
"+OK\r\n"

# Value is still "confirmed" (the second SET was skipped!)
127.0.0.1:6379> GET order:123
"confirmed"


# === Demo: Idempotent INCR (no double-counting) ===

127.0.0.1:6379> SET counter 0
OK

127.0.0.1:6379> HEADER idempotency-token incr-token-001
OK (header queued for next command)
127.0.0.1:6379> IDEMPOTENT.EXEC INCR counter
# attribute: token-status=new
(integer) 1

# Retry — cached! Counter stays at 1
127.0.0.1:6379> HEADER idempotency-token incr-token-001
OK (header queued for next command)
127.0.0.1:6379> IDEMPOTENT.EXEC INCR counter
# attribute: token-status=cached
":1\r\n"

127.0.0.1:6379> GET counter
"1"    # Would be "2" without idempotency!


# === Management Commands ===

# Check stats
127.0.0.1:6379> IDEMPOTENT.STATS
 1) "tokens_stored"
 2) (integer) 2
 3) "cache_hits"
 4) (integer) 2
 5) "cache_misses"
 6) (integer) 2
 ...

# Inspect a specific token
127.0.0.1:6379> IDEMPOTENT.INFO my-unique-token-001
 1) "token"
 2) "my-unique-token-001"
 3) "namespace"
 4) "default"
 5) "cached_result_bytes"
 6) (integer) 5
 7) "expires_at_ms"
 8) (integer) 1741919832000

# Invalidate a token (allow re-execution)
127.0.0.1:6379> IDEMPOTENT.INVALIDATE my-unique-token-001
OK

# Flush all tokens
127.0.0.1:6379> IDEMPOTENT.FLUSH
(integer) 1
```

### 3. Python client example

```python
import uuid
import sys, os
sys.path.insert(0, "demo/otel")
from resp4_client import Resp4Client

client = Resp4Client(host="127.0.0.1", port=6379)
client.connect()

# Generate a unique token per logical operation
token = str(uuid.uuid4())

# First call — executes SET
result = client.command("IDEMPOTENT.EXEC", "SET", "order:123", "confirmed",
                        headers={"idempotency-token": token})
print(f"Result: {result}")                        # OK
print(f"Status: {client.last_reply_attributes}")  # {'token-status': 'new', ...}

# Retry (e.g., after timeout) — returns cached result, no re-execution
result = client.command("IDEMPOTENT.EXEC", "SET", "order:123", "confirmed",
                        headers={"idempotency-token": token})
print(f"Result: {result}")                        # +OK\r\n (cached)
print(f"Status: {client.last_reply_attributes}")  # {'token-status': 'cached', ...}
```

## How It Works

### RESP4 Headers (the key innovation)

The idempotency token travels as **out-of-band metadata** using RESP4 request headers — no command syntax changes needed:

```
Wire format:
|1\r\n                              ← RESP4 attribute block (1 header)
$17\r\nidempotency-token\r\n       ← header key
$36\r\n550e8400-...-446655440000\r\n ← header value (UUID)
*3\r\n                              ← normal command follows
$3\r\nSET\r\n
$3\r\nfoo\r\n
$3\r\nbar\r\n
```

### Module Architecture

```
Client (KV DAL)                    Valkey + idempotency module
    │                                     │
    │── RESP4 header: idempotency-token ──►│
    │── IDEMPOTENT.EXEC SET foo bar ─────►│
    │                                     │
    │                              ┌──────┴──────┐
    │                              │ token seen?  │
    │                              │   YES → skip │──► return cached result
    │                              │   NO  → exec │──► execute, cache, return
    │                              └──────┬──────┘
    │                                     │
    │◄── reply (+ reply attributes) ──────│
    │     token-status: new/cached        │
```

### Token Storage

- **Hash:** `__idempotency:{namespace}` — maps token → cached RESP reply
- **Sorted Set:** `__idempotency_ttl:{namespace}` — tracks expiration times
- **TTL:** Default 24 hours, configurable via `idempotency-ttl` header
- **Cleanup:** Periodic timer (every 60s) evicts expired tokens

## RESP4 Headers Reference

| Header | Required | Type | Default | Description |
|--------|----------|------|---------|-------------|
| `idempotency-token` | Yes | string | — | Unique token (UUID, request-id). Max 128 bytes. |
| `idempotency-namespace` | No | string | `default` | Logical namespace for token isolation |
| `idempotency-ttl` | No | integer | `86400` | Token retention in seconds |

## Commands Reference

| Command | Description |
|---------|-------------|
| `IDEMPOTENT.EXEC <cmd> [args...]` | Execute command idempotently (requires `idempotency-token` header) |
| `IDEMPOTENT.INFO <token> [ns]` | Get info about a stored token |
| `IDEMPOTENT.INVALIDATE <token> [ns]` | Remove a token (allow re-execution) |
| `IDEMPOTENT.STATS` | Module statistics |
| `IDEMPOTENT.FLUSH [ns]` | Remove all tokens (optionally per namespace) |

## Use Cases

1. **Safe retries after timeout** — Client doesn't know if the command executed. Retry with same token is safe.
2. **Request hedging** — Send 3 parallel requests with same token. First executes, other 2 return cached result.
3. **Exactly-once processing** — Each message/event gets a unique token. Processing is idempotent even with at-least-once delivery.
