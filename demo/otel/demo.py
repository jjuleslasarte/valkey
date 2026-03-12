#!/usr/bin/env python3
"""
OpenTelemetry + RESP4 Demo for Valkey

Demonstrates 4 distinct tracing patterns, each producing a separate trace
in Jaeger/Grafana. Each trace tells a clear story.

Usage:
    python3 demo.py [--host HOST] [--port PORT] [--jaeger-endpoint URL]
"""

import argparse
import sys
import time
import json

from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.sdk.resources import Resource
from opentelemetry.trace.propagation.tracecontext import TraceContextTextMapPropagator
from opentelemetry.exporter.otlp.proto.http.trace_exporter import OTLPSpanExporter

from resp4_client import Resp4Client


def setup_otel(jaeger_endpoint, service_name="valkey-otel-demo"):
    resource = Resource.create({
        "service.name": service_name,
        "service.version": "1.0.0",
    })
    provider = TracerProvider(resource=resource)
    provider.add_span_processor(BatchSpanProcessor(
        OTLPSpanExporter(endpoint=f"{jaeger_endpoint}/v1/traces")))
    trace.set_tracer_provider(provider)
    return trace.get_tracer("valkey-resp4-demo")


def inject_headers():
    """Get W3C traceparent from current span context."""
    carrier = {}
    TraceContextTextMapPropagator().inject(carrier)
    return carrier


def valkey_cmd(client, tracer, *args):
    """Execute a Valkey command as a child span with RESP4 trace headers."""
    cmd = args[0].upper()
    stmt = " ".join(str(a) for a in args)

    with tracer.start_as_current_span(
        f"valkey {cmd}",
        kind=trace.SpanKind.CLIENT,
        attributes={
            "db.system": "valkey",
            "db.operation": cmd,
            "db.statement": stmt,
            "server.address": client.host,
            "server.port": client.port,
        },
    ) as span:
        headers = inject_headers()
        result = client.command(*args, headers=headers)
        if isinstance(result, Exception):
            span.set_status(trace.StatusCode.ERROR, str(result))
        else:
            span.set_status(trace.StatusCode.OK)
            span.set_attribute("db.response", str(result)[:100])
        return result


def valkey_exec(client, tracer, *args):
    """Execute via OTEL.EXEC — returns server timing + internal events as child spans.
    
    For a single command like SET key value, the trace looks like:
    
      valkey SET (client)            ← network RTT + server time
        └── valkey SET (server)      ← server-reported execution  
              ├── keyspace: set key  ← hook: keyspace notification fired
              └── new_key: key       ← hook: new key created
    """
    cmd = args[0].upper()
    stmt = " ".join(str(a) for a in args)

    with tracer.start_as_current_span(
        f"valkey {cmd}",
        kind=trace.SpanKind.CLIENT,
        attributes={
            "db.system": "valkey",
            "db.operation": cmd,
            "db.statement": stmt,
        },
    ) as span:
        headers = inject_headers()
        result = client.command("OTEL.EXEC", *args, headers=headers)
        attrs = client.last_reply_attributes or {}
        dur = attrs.get("server-duration-us", 0)
        events = attrs.get("events", [])

        span.set_attribute("server.duration_us", dur if isinstance(dur, int) else 0)
        span.set_status(trace.StatusCode.OK)
        span.set_attribute("db.response", str(result)[:100])
        span.set_attribute("server.events_count", len(events) if isinstance(events, list) else 0)

        # Create server-side span with hook events as children
        with tracer.start_as_current_span(
            f"valkey.server {cmd}",
            kind=trace.SpanKind.SERVER,
            attributes={
                "db.system": "valkey",
                "db.operation": cmd,
                "server.duration_us": dur if isinstance(dur, int) else 0,
            },
        ):
            # Each hook event that fired DURING this command becomes a child span
            if isinstance(events, list):
                for ev in events:
                    if not isinstance(ev, dict):
                        continue
                    etype = ev.get('type', '?')
                    detail = ev.get('detail', '')
                    ts = ev.get('timestamp_ms', 0)

                    # Parse detail for descriptive name
                    parts = detail.split(' ', 1) if detail else ['?']
                    ev_cmd = parts[0] if parts else '?'
                    ev_key = parts[1] if len(parts) > 1 else ''

                    if etype == 'new_key':
                        name = f"hook: NEW_KEY {ev_key}"
                    elif etype == 'key_overwrite':
                        name = f"hook: OVERWRITE {ev_key}"
                    elif etype == 'keyspace':
                        name = f"hook: {ev_cmd} {ev_key}"
                    else:
                        name = f"hook: {etype} {detail}"

                    with tracer.start_as_current_span(
                        name,
                        kind=trace.SpanKind.INTERNAL,
                        attributes={
                            "event.type": etype,
                            "event.detail": detail,
                            "event.timestamp_ms": ts,
                        },
                    ):
                        pass

        return result


# ============================================================================
# Trace 1: Simple SET → GET flow
# ============================================================================
# Shows: Client app → valkey SET → valkey GET
# In Jaeger this looks like:
#   user-request
#     ├── valkey SET user:alice
#     └── valkey GET user:alice

def trace_simple_set_get(client, tracer):
    print("\n" + "=" * 60)
    print("  Trace 1: Simple SET → GET (2 spans)")
    print("  One trace, two commands, clear parent-child")
    print("=" * 60)

    with tracer.start_as_current_span(
        "user-request: store and read user",
        attributes={"user.id": "alice"},
    ):
        result = valkey_cmd(client, tracer, "SET", "user:alice", "Alice Smith")
        print(f"  SET user:alice -> {result}")

        result = valkey_cmd(client, tracer, "GET", "user:alice")
        print(f"  GET user:alice -> {result}")

    print("  → In Grafana: 1 trace, 3 spans (parent + SET + GET)")


# ============================================================================
# Trace 2: Cache-aside pattern
# ============================================================================
# Shows: HTTP request → cache SET → cache EXPIRE → cache GET
# Simulates: app stores data in cache, then reads it back

def trace_cache_aside(client, tracer):
    print("\n" + "=" * 60)
    print("  Trace 2: Cache-aside pattern (store + read)")
    print("  HTTP request → write cache → read cache")
    print("=" * 60)

    with tracer.start_as_current_span(
        "GET /api/product/42",
        kind=trace.SpanKind.SERVER,
        attributes={"http.method": "GET", "http.route": "/api/product/:id"},
    ):
        # Simulate DB fetch
        with tracer.start_as_current_span("postgresql.query"):
            time.sleep(0.005)
            data = json.dumps({"id": 42, "name": "Widget", "price": 9.99})

        # Store in Valkey cache
        valkey_cmd(client, tracer, "SET", "cache:product:42", data)
        valkey_cmd(client, tracer, "EXPIRE", "cache:product:42", "300")
        print(f"  Cached product:42 with 300s TTL")

        # Read back from cache
        result = valkey_cmd(client, tracer, "GET", "cache:product:42")
        print(f"  Cache hit -> {result[:40]}...")

    print("  → In Grafana: 1 trace, 5 spans (HTTP → DB + SET + EXPIRE + GET)")


# ============================================================================
# Trace 3: OTEL.EXEC — server-side timing
# ============================================================================
# Shows: For each command, TWO spans: client-side and server-side
# The server span comes from OTEL.EXEC reply attributes

def trace_server_timing(client, tracer):
    print("\n" + "=" * 60)
    print("  Trace 3: Server-side timing via OTEL.EXEC")
    print("  Each command shows client span + server span")
    print("=" * 60)

    with tracer.start_as_current_span(
        "instrumented-write: SET with server timing",
    ):
        result = valkey_exec(client, tracer, "SET", "timed:key", "hello-with-timing")
        attrs = client.last_reply_attributes or {}
        print(f"  OTEL.EXEC SET -> {result}")
        print(f"    server-duration-us: {attrs.get('server-duration-us', '?')}")

        result = valkey_exec(client, tracer, "INCR", "timed:counter")
        attrs = client.last_reply_attributes or {}
        print(f"  OTEL.EXEC INCR -> {result}")
        print(f"    server-duration-us: {attrs.get('server-duration-us', '?')}")

    print("  → In Grafana: 1 trace with client+server span pairs")


# ============================================================================
# Trace 4: Server events — what the hooks captured
# ============================================================================
# Shows: Query OTEL.EVENTS, create one span per server event
# These are keyspace notifications and client lifecycle events

def trace_server_events(client, tracer):
    print("\n" + "=" * 60)
    print("  Trace 4: Server hook events (keyspace + lifecycle)")
    print("  Each event from OTEL.EVENTS becomes a span")
    print("=" * 60)

    with tracer.start_as_current_span(
        "server-event-log",
        attributes={"description": "Events from Valkey keyspace hooks"},
    ):
        events = client.command("OTEL.EVENTS", "15")
        if isinstance(events, list) and events:
            print(f"  {len(events)} server events captured:")
            for ev in events:
                if not isinstance(ev, dict):
                    continue
                ts = ev.get('timestamp_ms', 0)
                etype = ev.get('type', '?')
                detail = ev.get('detail', '')

                # Parse detail: "command key" → descriptive span name
                parts = detail.split(' ', 1) if detail else ['?']
                cmd = parts[0].upper() if parts else '?'
                key = parts[1] if len(parts) > 1 else ''

                if etype == 'keyspace':
                    name = f"valkey.server {cmd} {key}"
                elif etype == 'new_key':
                    name = f"valkey.server NEW_KEY {key}"
                elif etype == 'key_overwrite':
                    name = f"valkey.server OVERWRITE {key}"
                elif etype == 'client_connect':
                    name = "valkey.server CLIENT_CONNECT"
                elif etype == 'client_disconnect':
                    name = "valkey.server CLIENT_DISCONNECT"
                else:
                    name = f"valkey.server {etype}"

                print(f"    {name}")

                with tracer.start_as_current_span(
                    name,
                    kind=trace.SpanKind.SERVER,
                    attributes={
                        "db.system": "valkey",
                        "db.operation": cmd,
                        "db.key": key,
                        "event.type": etype,
                        "event.timestamp_ms": ts,
                    },
                ):
                    pass
        else:
            print("  No events yet")

    print("  → In Grafana: 1 trace, one span per server event")


# ============================================================================
# Stats summary
# ============================================================================

def show_stats(client):
    print("\n" + "=" * 60)
    print("  Module Statistics (OTEL.STATS)")
    print("=" * 60)
    stats = client.command("OTEL.STATS")
    if isinstance(stats, dict):
        for k, v in stats.items():
            print(f"    {k}: {v}")


# ============================================================================
# Main
# ============================================================================

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=6379)
    parser.add_argument("--jaeger-endpoint", default="http://localhost:4318")
    args = parser.parse_args()

    print("╔══════════════════════════════════════════════════════════╗")
    print("║     RESP4 + OpenTelemetry Tracing Demo                  ║")
    print("║     4 distinct traces, each tells a different story     ║")
    print("╚══════════════════════════════════════════════════════════╝")

    tracer = setup_otel(args.jaeger_endpoint)

    print(f"\n→ Connecting to Valkey at {args.host}:{args.port} with RESP4...")
    client = Resp4Client(host=args.host, port=args.port)
    try:
        r = client.connect()
        print(f"  Connected! proto={r.get('proto')}, version={r.get('version')}")
    except Exception as e:
        print(f"\n✗ Connection failed: {e}")
        sys.exit(1)

    try:
        trace_simple_set_get(client, tracer)
        trace_cache_aside(client, tracer)
        trace_server_timing(client, tracer)
        trace_server_events(client, tracer)
        show_stats(client)

        print("\n→ Flushing traces...")
        trace.get_tracer_provider().force_flush()
        time.sleep(1)

        print("\n╔══════════════════════════════════════════════════════════╗")
        print("║  ✓ Done! 4 traces exported to Grafana/Jaeger            ║")
        print("║                                                          ║")
        print("║  In Grafana Explore (Jaeger datasource):                 ║")
        print("║    Trace 1: 'user-request: store and read user'          ║")
        print("║    Trace 2: 'GET /api/product/42'                        ║")
        print("║    Trace 3: 'instrumented-write: SET with server timing' ║")
        print("║    Trace 4: 'server-event-log'                           ║")
        print("╚══════════════════════════════════════════════════════════╝")

    finally:
        client.close()
        trace.get_tracer_provider().shutdown()


if __name__ == "__main__":
    main()
