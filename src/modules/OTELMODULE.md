# OpenTelemetry Tracing Module for Valkey (RESP4)

A Valkey module that implements **W3C Trace Context** propagation using **RESP4 request headers**. This module enables end-to-end distributed tracing through Valkey by allowing OpenTelemetry-instrumented clients to send trace context alongside commands, without modifying command syntax.

## Overview

Modern distributed systems use [OpenTelemetry](https://opentelemetry.io/) and the [W3C Trace Context](https://www.w3.org/TR/trace-context/) standard to correlate requests across service boundaries. Before RESP4, there was no way to pass trace context through Valkey — the protocol had no mechanism for client-to-server metadata.

RESP4 introduces **request-side attributes** (request headers) that travel alongside commands as out-of-band key-value pairs. This module registers the standard OpenTelemetry headers and provides:

1. **Automatic commandlog integration** — trace context is attached to slow-query log entries, enabling correlation between slow Valkey commands and distributed traces.
2. **Diagnostic commands** — inspect trace context on the current connection for debugging and verification.
3. **Statistics** — track how many commands carry trace context for observability into tracing coverage.

## Requirements

- **Valkey 8.1+** with RESP4 support (this branch)
- Client that supports RESP4 (`HELLO 4`) and can send request headers

## Building

The module is built automatically as part of the Valkey module build:

```bash
# Using CMake (recommended)
cd /path/to/valkey
mkdir -p build && cd build
cmake .. && make otelmodule

# Using Make (standalone)
cd src/modules
make otelmodule.so
```

## Loading

```bash
# At startup (valkey.conf)
loadmodule /path/to/otelmodule.so

# At runtime
MODULE LOAD /path/to/otelmodule.so
```

## RESP4 Headers

The module registers these RESP4 request headers:

| Header | Standard | Description |
|--------|----------|-------------|
| `traceparent` | [W3C Trace Context](https://www.w3.org/TR/trace-context/#traceparent-header) | Trace context: `VERSION-TRACEID-SPANID-FLAGS` |
| `tracestate` | [W3C Trace Context](https://www.w3.org/TR/trace-context/#tracestate-header) | Vendor-specific trace data (optional) |
| `baggage` | [W3C Baggage](https://www.w3.org/TR/baggage/) | Application-level key-value context (optional) |
| `otel-resource` | Custom | Originating service/resource identifier (optional) |

### traceparent Format

The `traceparent` header follows the W3C specification:

```
VERSION-TRACEID-SPANID-FLAGS

Example: 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
         ── ──────────────────────────────── ──────────────── ──
         │               │                        │           │
         │               │                        │           └─ flags (2 hex, 01 = sampled)
         │               │                        └─ span-id (16 hex, 8 bytes)
         │               └─ trace-id (32 hex, 16 bytes)
         └─ version (2 hex, currently "00")
```

Validation rules:
- Exactly 55 characters
- All hex characters must be lowercase
- Version `ff` is invalid
- trace-id must not be all zeros
- span-id must not be all zeros

## Wire Protocol Example

A RESP4 client sends trace context as an attribute block (`|`) before the command:

```
|2\r\n
$11\r\ntraceparent\r\n
$55\r\n00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01\r\n
$10\r\ntracestate\r\n
$18\r\nvendor1=val1,rojo=\r\n
*3\r\n
$3\r\nSET\r\n
$3\r\nfoo\r\n
$3\r\nbar\r\n
```

This sends `SET foo bar` with trace context attached. The module captures the headers automatically via the command filter.

## Commands

### OTEL.TRACE

Returns the trace context from the current request.

- If `traceparent` and `tracestate` are both present: returns a 2-element array `[traceparent, tracestate]`.
- If only `traceparent` is present: returns the traceparent string.
- If no traceparent: returns nil.
- If traceparent is malformed: returns an error.

```
# With traceparent only
127.0.0.1:6379> OTEL.TRACE
"00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01"

# With traceparent + tracestate
127.0.0.1:6379> OTEL.TRACE
1) "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01"
2) "vendor1=val1"

# Without headers
127.0.0.1:6379> OTEL.TRACE
(nil)
```

### OTEL.CONTEXT

Returns all recognized OpenTelemetry headers as a map.

```
127.0.0.1:6379> OTEL.CONTEXT
1# "traceparent" => "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01"
2# "tracestate" => "vendor1=val1"
3# "baggage" => "userId=alice,serverNode=DF28"
```

### OTEL.TRACEID

Extracts and returns the 32-character trace-id from the traceparent header.

```
127.0.0.1:6379> OTEL.TRACEID
"4bf92f3577b34da6a3ce929d0e0e4736"
```

### OTEL.SPANID

Extracts and returns the 16-character span-id from the traceparent header.

```
127.0.0.1:6379> OTEL.SPANID
"00f067aa0ba902b7"
```

### OTEL.STATS

Returns module statistics as a map.

```
127.0.0.1:6379> OTEL.STATS
1# "commands_total" => (integer) 15234
2# "commands_traced" => (integer) 12891
3# "traceparent_invalid" => (integer) 3
4# "tracestate_received" => (integer) 10456
5# "baggage_received" => (integer) 892
6# "trace_ratio" => (double) 0.8462
```

| Field | Description |
|-------|-------------|
| `commands_total` | Total commands observed by the filter |
| `commands_traced` | Commands with a valid `traceparent` |
| `traceparent_invalid` | Commands with malformed `traceparent` |
| `tracestate_received` | Commands that also included `tracestate` |
| `baggage_received` | Commands that included `baggage` |
| `trace_ratio` | Ratio of `commands_traced / commands_total` |

## Commandlog (Slowlog) Integration

The module installs a **command filter** that runs on every command. When a command carries a valid `traceparent` header, the module attaches it (and `tracestate`, if present) as commandlog metadata. This means slow query log entries will include the trace context:

```
127.0.0.1:6379> COMMANDLOG GET 1
1) 1) (integer) 1          # entry id
   2) (integer) 1698776172 # timestamp
   3) (integer) 15230      # duration (microseconds)
   4) 1) "SET"
      2) "foo"
      3) "bar"
   5) "127.0.0.1:52340"
   6) ""
   7) 1# "traceparent" => "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01"
      2# "tracestate" => "vendor1=val1"
```

This enables operators to:
- Correlate slow Valkey queries with specific distributed traces in Jaeger, Zipkin, Grafana Tempo, or AWS X-Ray
- Find the originating service and request that caused a slow command
- Build dashboards linking Valkey latency to upstream service behavior

## Client Integration Examples

### Python (with OpenTelemetry)

```python
from opentelemetry import trace
from opentelemetry.trace.propagation.tracecontext import TraceContextTextMapPropagator

# Assuming a RESP4-capable client library
def valkey_set_with_tracing(client, key, value):
    """Send a SET command with the current trace context as RESP4 headers."""
    carrier = {}
    TraceContextTextMapPropagator().inject(carrier)

    headers = {}
    if 'traceparent' in carrier:
        headers['traceparent'] = carrier['traceparent']
    if 'tracestate' in carrier:
        headers['tracestate'] = carrier['tracestate']

    # Client library sends headers as RESP4 attribute block before the command
    client.set(key, value, headers=headers)
```

### Java (with OpenTelemetry)

```java
import io.opentelemetry.api.trace.Span;
import io.opentelemetry.context.Context;
import io.opentelemetry.context.propagation.TextMapSetter;

// Assuming a RESP4-capable GLIDE client
public void setWithTracing(ValkeyClient client, String key, String value) {
    Map<String, String> headers = new HashMap<>();
    GlobalOpenTelemetry.getPropagators()
        .getTextMapPropagator()
        .inject(Context.current(), headers, Map::put);

    // Client sends headers as RESP4 attribute block
    client.set(key, value, SetOptions.builder()
        .headers(headers)
        .build());
}
```

### valkey-cli

```bash
# Using the --resp4 and --header flags
valkey-cli --resp4 \
  --header traceparent=00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01 \
  --header tracestate=vendor1=val1 \
  SET foo bar

# Interactive mode
127.0.0.1:6379> HEADER traceparent 00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01
OK (header queued for next command)
127.0.0.1:6379> SET foo bar
OK
```

## Architecture

```
┌────────────────────┐     RESP4 headers        ┌─────────────┐
│  Application       │    (traceparent, etc.)    │   Valkey     │
│  (OTel SDK)        ├─────────────────────────►│   Server     │
│                    │     + command (SET, GET)   │              │
└────────────────────┘                           │  ┌─────────┐ │
                                                 │  │  otel   │ │
┌────────────────────┐                           │  │ module  │ │
│  Tracing Backend   │                           │  │         │ │
│  (Jaeger, Zipkin,  │◄── correlate via ──────── │  │ filter: │ │
│   Grafana Tempo)   │    trace-id               │  │ attach  │ │
└────────────────────┘                           │  │ to cmd- │ │
                                                 │  │ log     │ │
┌────────────────────┐                           │  └─────────┘ │
│  Ops Dashboard     │◄── COMMANDLOG GET ─────── │              │
│  (with trace-id    │    includes traceparent   └─────────────┘
│   correlation)     │
└────────────────────┘
```

## Design Decisions

1. **Header validation is strict**: The module validates `traceparent` against the W3C spec (format, no all-zero IDs, lowercase hex). Invalid headers are counted in stats but silently dropped by the filter (not propagated to commandlog). The `OTEL.TRACE` command returns an explicit error for invalid traceparent.

2. **Statistics are module-global**: Stats counters are simple `long long` values. Since Valkey is single-threaded for command processing, no atomic operations are needed. Stats reset on module reload.

3. **Headers are not replicated**: Per the RESP4 spec, request headers are transport-level metadata and are not persisted to AOF or sent to replicas. Trace context is meaningful at the originating connection only.

4. **No external dependencies**: The module uses only the Valkey Module API. It does not link to the OpenTelemetry C SDK, libcurl, or any external library. It is purely a header consumer — trace export is handled by the client-side OTel SDK.

## Relationship to RESP4

This module is a reference implementation of the **distributed tracing** use case described in the [RESP4 Protocol Specification](../resp4-protocol-spec.md) (Section 16.2). It demonstrates:

- Registering request headers via `ValkeyModule_RegisterRequestHeader()`
- Reading headers in command callbacks via `ValkeyModule_GetRequestHeader()`
- Reading headers in command filters via `ValkeyModule_CommandFilterGetRequestHeader()`
- Attaching metadata to commandlog via `ValkeyModule_CommandFilterSetCommandlogMetadata()`
- Iterating all headers via `ValkeyModule_RequestHeaderIterStart/Next/Stop()`
