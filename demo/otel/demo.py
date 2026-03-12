#!/usr/bin/env python3
"""
OpenTelemetry + RESP4 Demo for Valkey

Demonstrates how RESP4 request headers enable distributed tracing between
a client application and Valkey. The client sends W3C traceparent as a
RESP4 header, and the server participates in the trace by reporting
execution timing and internal events.

Generates many traces with randomized keys across different commands
(SET, GET, INCR, DEL, EXPIRE) so you can explore query and filtering
capabilities in Jaeger/Grafana (search by operation, tag, duration, etc.)

Usage:
    python3 demo.py [--host HOST] [--port PORT] [--jaeger-endpoint URL]
                    [--count N]
"""

import argparse
import random
import string
import sys
import time

from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor
from opentelemetry.sdk.resources import Resource
from opentelemetry.trace.propagation.tracecontext import TraceContextTextMapPropagator
from opentelemetry.exporter.otlp.proto.http.trace_exporter import OTLPSpanExporter

from resp4_client import Resp4Client

# Key prefixes to simulate different application domains
KEY_PREFIXES = ["user", "session", "cache", "counter", "config", "cart", "order"]


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


def random_key():
    """Generate a random key like 'user:a3f2', 'cache:x9b1', etc."""
    prefix = random.choice(KEY_PREFIXES)
    suffix = ''.join(random.choices(string.ascii_lowercase + string.digits, k=4))
    return f"{prefix}:{suffix}"


def random_value():
    """Generate a random value."""
    return ''.join(random.choices(string.ascii_letters + string.digits, k=random.randint(8, 32)))


def valkey_exec(client, tracer, *args):
    """Execute via OTEL.EXEC with RESP4 trace context propagation.

    The client sends traceparent as a RESP4 request header, so the server
    can correlate its execution to the client's trace and report:
      - Server-side execution duration (microseconds)
      - Internal events (keyspace notifications, hook activity)

    Each call produces one trace:
      valkey SET (client)            ← measures network RTT
        └── valkey.server SET        ← server-reported execution time
              ├── hook: set key      ← keyspace notification
              └── hook: NEW_KEY key  ← new key created
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
            "server.address": client.host,
            "server.port": client.port,
        },
    ) as span:
        headers = inject_headers()
        result = client.command("OTEL.EXEC", *args, headers=headers)
        attrs = client.last_reply_attributes or {}
        dur = attrs.get("server-duration-us", 0)
        events = attrs.get("events", [])

        span.set_attribute("server.duration_us", dur if isinstance(dur, int) else 0)
        if isinstance(result, Exception):
            span.set_status(trace.StatusCode.ERROR, str(result))
        else:
            span.set_status(trace.StatusCode.OK)
        span.set_attribute("db.response", str(result)[:100])
        span.set_attribute("server.events_count", len(events) if isinstance(events, list) else 0)

        # Server-side span with hook events as children
        with tracer.start_as_current_span(
            f"valkey.server {cmd}",
            kind=trace.SpanKind.SERVER,
            attributes={
                "db.system": "valkey",
                "db.operation": cmd,
                "server.duration_us": dur if isinstance(dur, int) else 0,
            },
        ):
            if isinstance(events, list):
                for ev in events:
                    if not isinstance(ev, dict):
                        continue
                    etype = ev.get('type', '?')
                    detail = ev.get('detail', '')
                    ts = ev.get('timestamp_ms', 0)

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


def generate_traces(client, tracer, count):
    """Generate many traces with randomized keys and mixed commands."""
    keys_written = []

    print(f"\n→ Generating {count} traced commands with random keys...\n")

    for i in range(count):
        # Pick a random operation, weighted toward SET/GET/INCR
        op = random.choices(
            ["SET", "GET", "INCR", "DEL", "EXPIRE"],
            weights=[30, 25, 20, 10, 15],
            k=1,
        )[0]

        if op == "SET":
            key = random_key()
            val = random_value()
            result = valkey_exec(client, tracer, "SET", key, val)
            keys_written.append(key)
            print(f"  [{i+1:3d}/{count}] SET {key} -> {result}")

        elif op == "GET":
            # GET a key we've written, or a random one
            if keys_written and random.random() < 0.7:
                key = random.choice(keys_written)
            else:
                key = random_key()
            result = valkey_exec(client, tracer, "GET", key)
            print(f"  [{i+1:3d}/{count}] GET {key} -> {str(result)[:30]}")

        elif op == "INCR":
            key = f"counter:{random.choice(KEY_PREFIXES)}:hits"
            result = valkey_exec(client, tracer, "INCR", key)
            keys_written.append(key)
            print(f"  [{i+1:3d}/{count}] INCR {key} -> {result}")

        elif op == "DEL":
            if keys_written:
                key = keys_written.pop(random.randrange(len(keys_written)))
            else:
                key = random_key()
            result = valkey_exec(client, tracer, "DEL", key)
            print(f"  [{i+1:3d}/{count}] DEL {key} -> {result}")

        elif op == "EXPIRE":
            if keys_written:
                key = random.choice(keys_written)
            else:
                key = random_key()
            ttl = random.choice([60, 120, 300, 600, 3600])
            result = valkey_exec(client, tracer, "EXPIRE", key, str(ttl))
            print(f"  [{i+1:3d}/{count}] EXPIRE {key} {ttl}s -> {result}")

        # Small delay to spread traces over time for better visualization
        time.sleep(0.02)


def show_stats(client):
    print("\n" + "=" * 60)
    print("  Module Statistics (OTEL.STATS)")
    print("=" * 60)
    stats = client.command("OTEL.STATS")
    if isinstance(stats, dict):
        for k, v in stats.items():
            print(f"    {k}: {v}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=6379)
    parser.add_argument("--jaeger-endpoint", default="http://localhost:4318")
    parser.add_argument("--count", type=int, default=50,
                        help="Number of traced commands to generate (default: 50)")
    args = parser.parse_args()

    print("╔══════════════════════════════════════════════════════════╗")
    print("║  RESP4 Distributed Tracing Demo                        ║")
    print("║                                                          ║")
    print("║  Generates many traces with random keys so you can      ║")
    print("║  explore query/filter capabilities in Jaeger/Grafana.   ║")
    print("║                                                          ║")
    print("║  Each command = 1 trace with client + server spans.     ║")
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
        generate_traces(client, tracer, args.count)
        show_stats(client)

        print("\n→ Flushing traces...")
        trace.get_tracer_provider().force_flush()
        time.sleep(1)

        print(f"\n╔══════════════════════════════════════════════════════════╗")
        print(f"║  ✓ Done! {args.count} traces exported to Grafana/Jaeger          ║")
        print(f"║                                                          ║")
        print(f"║  Try these queries in Grafana Explore (Jaeger):          ║")
        print(f"║                                                          ║")
        print(f"║  • Service: valkey-otel-demo                             ║")
        print(f"║  • Operation: valkey SET / valkey GET / valkey INCR      ║")
        print(f"║  • Tag: db.operation=SET  or  db.statement=SET user:*    ║")
        print(f"║  • Min Duration: 1ms (find slow commands)                ║")
        print(f"╚══════════════════════════════════════════════════════════╝")

    finally:
        client.close()
        trace.get_tracer_provider().shutdown()


if __name__ == "__main__":
    main()
