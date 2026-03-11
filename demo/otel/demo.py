#!/usr/bin/env python3
"""
OpenTelemetry + RESP4 Demo for Valkey

This demo shows end-to-end distributed tracing through Valkey using RESP4
request headers. It creates OpenTelemetry spans, injects W3C Trace Context
into RESP4 headers, and exports traces to Jaeger for visualization.

Usage:
    python3 demo.py [--host HOST] [--port PORT] [--jaeger-endpoint URL]

After running, open Jaeger UI at http://localhost:16686 and search for
service "valkey-otel-demo" to see the traces.
"""

import argparse
import os
import sys
import time
import random
import json

# OpenTelemetry imports
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import BatchSpanProcessor, ConsoleSpanExporter, SimpleSpanProcessor
from opentelemetry.sdk.resources import Resource
from opentelemetry.trace.propagation.tracecontext import TraceContextTextMapPropagator
from opentelemetry.exporter.otlp.proto.http.trace_exporter import OTLPSpanExporter

# Our minimal RESP4 client
from resp4_client import Resp4Client


# ============================================================================
# Setup OpenTelemetry
# ============================================================================

def setup_otel(jaeger_endpoint, service_name="valkey-otel-demo"):
    """Configure OpenTelemetry with OTLP exporter (to Jaeger) + console exporter."""
    resource = Resource.create({
        "service.name": service_name,
        "service.version": "1.0.0",
        "deployment.environment": "demo",
    })

    provider = TracerProvider(resource=resource)

    # OTLP HTTP exporter -> Jaeger
    otlp_exporter = OTLPSpanExporter(endpoint=f"{jaeger_endpoint}/v1/traces")
    provider.add_span_processor(BatchSpanProcessor(otlp_exporter))

    # Uncomment below to also see spans printed to console (verbose):
    # provider.add_span_processor(SimpleSpanProcessor(ConsoleSpanExporter()))

    trace.set_tracer_provider(provider)
    return trace.get_tracer("valkey-resp4-demo")


# ============================================================================
# RESP4 + OTel Integration
# ============================================================================

def inject_trace_headers():
    """
    Extract W3C Trace Context from the current span into a dict
    suitable for RESP4 request headers.
    """
    propagator = TraceContextTextMapPropagator()
    carrier = {}
    propagator.inject(carrier)
    return carrier


def traced_command(client, tracer, *args):
    """
    Execute a Valkey command within an OTel span, sending trace context
    as RESP4 headers.
    """
    cmd_name = args[0].upper()
    key = args[1] if len(args) > 1 else ""

    with tracer.start_as_current_span(
        f"valkey {cmd_name}",
        kind=trace.SpanKind.CLIENT,
        attributes={
            "db.system": "valkey",
            "db.operation": cmd_name,
            "db.statement": " ".join(str(a) for a in args),
            "server.address": client.host,
            "server.port": client.port,
            "network.transport": "tcp",
        },
    ) as span:
        # Inject W3C trace context into RESP4 headers
        headers = inject_trace_headers()

        try:
            result = client.command(*args, headers=headers)

            if isinstance(result, Exception):
                span.set_status(trace.StatusCode.ERROR, str(result))
                span.record_exception(result)
            else:
                span.set_status(trace.StatusCode.OK)
                span.set_attribute("db.response", str(result)[:200])

            return result

        except Exception as e:
            span.set_status(trace.StatusCode.ERROR, str(e))
            span.record_exception(e)
            raise


# ============================================================================
# Demo Scenarios
# ============================================================================

def demo_basic_operations(client, tracer):
    """Demo 1: Basic SET/GET with trace context."""
    print("\n" + "=" * 60)
    print("  Demo 1: Basic SET/GET with trace context")
    print("=" * 60)

    with tracer.start_as_current_span("demo.basic_operations") as parent:
        # SET
        result = traced_command(client, tracer, "SET", "user:1001", "Alice")
        print(f"  SET user:1001 Alice -> {result}")

        # GET (key exists — avoids nil-return server issue)
        result = traced_command(client, tracer, "GET", "user:1001")
        print(f"  GET user:1001 -> {result}")

        # SET another key
        result = traced_command(client, tracer, "SET", "user:1002", "Bob")
        print(f"  SET user:1002 Bob -> {result}")

    print("  ✓ 3 commands traced with W3C traceparent headers")


def demo_pipeline_simulation(client, tracer):
    """Demo 2: Simulate a request pipeline (e.g., web request handling)."""
    print("\n" + "=" * 60)
    print("  Demo 2: Simulated web request pipeline")
    print("=" * 60)

    with tracer.start_as_current_span(
        "http.request GET /api/user/42",
        kind=trace.SpanKind.SERVER,
        attributes={"http.method": "GET", "http.url": "/api/user/42"},
    ):
        # Simulate DB query
        with tracer.start_as_current_span("db.query", attributes={"db.system": "postgresql"}):
            time.sleep(0.01)  # Simulate DB latency
            user_data = json.dumps({"id": 42, "name": "Bob", "email": "bob@example.com"})

        # Store in cache
        with tracer.start_as_current_span("cache.store"):
            traced_command(client, tracer, "SET", "cache:user:42", user_data)
            traced_command(client, tracer, "EXPIRE", "cache:user:42", "300")
            print(f"  Stored user data in cache with 300s TTL")

        # Read back from cache (key now exists)
        with tracer.start_as_current_span("cache.lookup"):
            result = traced_command(client, tracer, "GET", "cache:user:42")
            print(f"  Cache lookup -> {str(result)[:60]}")

        # Increment request counter
        traced_command(client, tracer, "INCR", "stats:api:requests")
        print(f"  Incremented request counter")

    print("  ✓ Multi-step pipeline traced end-to-end")


def demo_batch_operations(client, tracer):
    """Demo 3: Batch operations (e.g., leaderboard update)."""
    print("\n" + "=" * 60)
    print("  Demo 3: Leaderboard batch update")
    print("=" * 60)

    players = [
        ("player:alice", random.randint(100, 999)),
        ("player:bob", random.randint(100, 999)),
        ("player:charlie", random.randint(100, 999)),
        ("player:diana", random.randint(100, 999)),
        ("player:eve", random.randint(100, 999)),
    ]

    with tracer.start_as_current_span(
        "leaderboard.update",
        attributes={"leaderboard.player_count": len(players)},
    ):
        for player, score in players:
            traced_command(client, tracer, "ZADD", "leaderboard:weekly", str(score), player)
            print(f"  ZADD leaderboard:weekly {score} {player}")

        # Get top 3
        result = traced_command(client, tracer, "ZREVRANGE", "leaderboard:weekly", "0", "2", "WITHSCORES")
        print(f"  Top 3: {result}")

    print(f"  ✓ {len(players)} score updates + 1 query, all traced")


def demo_server_side_tracing(client, tracer):
    """Demo 4: Server-side execution tracing via OTEL.EXEC."""
    print("\n" + "=" * 60)
    print("  Demo 4: Server-side execution tracing (OTEL.EXEC)")
    print("=" * 60)

    with tracer.start_as_current_span(
        "demo.server_side_tracing",
        attributes={"description": "Demonstrates server-side timing via reply attributes"},
    ):
        # Use OTEL.EXEC to wrap a SET command — server returns timing as reply attributes
        headers = inject_trace_headers()
        result = client.command("OTEL.EXEC", "SET", "traced:key1", "hello-from-otel-exec", headers=headers)
        attrs = client.last_reply_attributes
        print(f"  OTEL.EXEC SET traced:key1 -> {result}")
        if attrs:
            duration = attrs.get('server-duration-us', '?')
            print(f"    ↳ Reply attributes (server timing):")
            print(f"      server-start-us:    {attrs.get('server-start-us', 'N/A')}")
            print(f"      server-end-us:      {attrs.get('server-end-us', 'N/A')}")
            print(f"      server-duration-us:  {duration}")
            print(f"      traceparent echoed:  {attrs.get('traceparent', 'N/A')[:40]}...")

            # Create a server-side child span using the reported timing
            with tracer.start_as_current_span(
                "valkey.server SET (server-reported)",
                kind=trace.SpanKind.SERVER,
                attributes={
                    "db.system": "valkey",
                    "db.operation": "SET",
                    "server.duration_us": duration if isinstance(duration, int) else 0,
                    "server.reported": True,
                    "note": "Timing from OTEL.EXEC reply attributes",
                },
            ):
                pass  # Span represents the server-side execution window

        # Wrap a ZADD with server timing
        headers = inject_trace_headers()
        result = client.command("OTEL.EXEC", "ZADD", "traced:scores", "100", "player:traced", headers=headers)
        attrs = client.last_reply_attributes
        print(f"  OTEL.EXEC ZADD traced:scores 100 player:traced -> {result}")
        if attrs:
            print(f"    ↳ server-duration-us: {attrs.get('server-duration-us', '?')}")

        # Wrap an INCR
        headers = inject_trace_headers()
        result = client.command("OTEL.EXEC", "INCR", "traced:counter", headers=headers)
        attrs = client.last_reply_attributes
        print(f"  OTEL.EXEC INCR traced:counter -> {result}")
        if attrs:
            print(f"    ↳ server-duration-us: {attrs.get('server-duration-us', '?')}")

    print("  ✓ Server-side timing captured via RESP4 reply attributes")
    print("    In Jaeger, you'll see both client AND server-reported spans")


def demo_otel_commands(client, tracer):
    """Demo 5: Use the OTEL module diagnostic commands."""
    print("\n" + "=" * 60)
    print("  Demo 5: OTEL module diagnostic commands")
    print("=" * 60)

    with tracer.start_as_current_span("demo.otel_commands") as span:
        headers = inject_trace_headers()

        # OTEL.TRACE — echo back the trace context
        result = client.command("OTEL.TRACE", headers=headers)
        print(f"  OTEL.TRACE -> {result}")

        # OTEL.TRACEID — extract trace-id
        result = client.command("OTEL.TRACEID", headers=headers)
        print(f"  OTEL.TRACEID -> {result}")

        # OTEL.SPANID — extract span-id
        result = client.command("OTEL.SPANID", headers=headers)
        print(f"  OTEL.SPANID -> {result}")

        # OTEL.CONTEXT — all headers
        headers_with_extras = dict(headers)
        headers_with_extras["baggage"] = "userId=42,region=us-west-2"
        headers_with_extras["otel-resource"] = "valkey-otel-demo"
        result = client.command("OTEL.CONTEXT", headers=headers_with_extras)
        print(f"  OTEL.CONTEXT -> {result}")

    print("  ✓ Module diagnostic commands working")


def demo_stats(client):
    """Demo 5: Show module statistics."""
    print("\n" + "=" * 60)
    print("  Demo 5: Module statistics")
    print("=" * 60)

    result = client.command("OTEL.STATS")
    print(f"  Module stats:")
    if isinstance(result, dict):
        for k, v in result.items():
            print(f"    {k}: {v}")
    else:
        print(f"    {result}")

    print("  ✓ Statistics collected across all demos")


# ============================================================================
# Main
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="OpenTelemetry + RESP4 Demo for Valkey"
    )
    parser.add_argument("--host", default="127.0.0.1", help="Valkey host")
    parser.add_argument("--port", type=int, default=6379, help="Valkey port")
    parser.add_argument(
        "--jaeger-endpoint",
        default="http://localhost:4318",
        help="Jaeger OTLP HTTP endpoint",
    )
    args = parser.parse_args()

    print("╔══════════════════════════════════════════════════════════╗")
    print("║     OpenTelemetry + RESP4 Request Headers Demo          ║")
    print("║     Distributed Tracing through Valkey                  ║")
    print("╚══════════════════════════════════════════════════════════╝")

    # Setup OpenTelemetry
    print(f"\n→ Configuring OpenTelemetry (exporting to {args.jaeger_endpoint})...")
    tracer = setup_otel(args.jaeger_endpoint)

    # Connect to Valkey with RESP4
    print(f"→ Connecting to Valkey at {args.host}:{args.port} with RESP4...")
    client = Resp4Client(host=args.host, port=args.port)
    try:
        hello_reply = client.connect()
        print(f"  Connected! HELLO reply: proto={hello_reply.get('proto', '?')}, "
              f"server={hello_reply.get('server', '?')}, "
              f"version={hello_reply.get('version', '?')}")
    except Exception as e:
        print(f"\n✗ Failed to connect to Valkey: {e}")
        print(f"  Make sure Valkey is running with the otelmodule loaded:")
        print(f"  ./src/valkey-server --loadmodule ./src/modules/otelmodule.so")
        sys.exit(1)

    try:
        # Run demos
        demo_basic_operations(client, tracer)
        demo_pipeline_simulation(client, tracer)
        demo_batch_operations(client, tracer)
        demo_server_side_tracing(client, tracer)
        demo_otel_commands(client, tracer)
        demo_stats(client)

        # Flush traces
        print("\n→ Flushing traces to Jaeger...")
        trace.get_tracer_provider().force_flush()
        time.sleep(1)

        print("\n╔══════════════════════════════════════════════════════════╗")
        print("║  ✓ Demo complete!                                       ║")
        print("║                                                          ║")
        print("║  Open Jaeger UI to see traces:                           ║")
        print("║    http://localhost:16686                                 ║")
        print("║                                                          ║")
        print("║  Search for service: valkey-otel-demo                    ║")
        print("║                                                          ║")
        print("║  Each Valkey command appears as a span with:             ║")
        print("║    - traceparent sent as RESP4 header                    ║")
        print("║    - Full parent/child span hierarchy                    ║")
        print("║    - Command details in span attributes                  ║")
        print("╚══════════════════════════════════════════════════════════╝")

    finally:
        client.close()
        trace.get_tracer_provider().shutdown()


if __name__ == "__main__":
    main()
