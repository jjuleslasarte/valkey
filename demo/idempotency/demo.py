#!/usr/bin/env python3
"""
Idempotency Token Demo — Demonstrates RESP4-based idempotent command execution.

This demo shows how the idempotency module uses RESP4 request headers to make
Valkey commands idempotent: the same token always returns the same result,
regardless of how many times the request is sent.

Use cases demonstrated:
  1. Basic idempotent SET — safe to retry
  2. Idempotent INCR — retries don't double-count
  3. Request hedging — send 3 parallel attempts, first wins, others are replays
  4. Token invalidation — allow re-execution after explicit invalidation

Prerequisites:
  - Valkey server running on localhost:6379
  - Idempotency module loaded: valkey-server --loadmodule src/modules/idempotency.so
  - RESP4 support (this branch)

Usage:
  python3 demo/idempotency/demo.py
"""

import sys
import os
import uuid
import time

# Add the otel demo directory so we can reuse the RESP4 client
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "otel"))
from resp4_client import Resp4Client


def banner(title):
    print(f"\n{'='*60}")
    print(f"  {title}")
    print(f"{'='*60}\n")


def demo_basic_idempotent_set(client):
    """Demonstrate basic idempotent SET — safe to retry."""
    banner("Demo 1: Basic Idempotent SET (safe retries)")

    token = str(uuid.uuid4())
    print(f"  Token: {token[:8]}...")
    print()

    # First call: new execution
    result = client.command("IDEMPOTENT.EXEC", "SET", "order:123", "confirmed",
                            headers={"idempotency-token": token})
    attrs = client.last_reply_attributes or {}
    status = attrs.get("token-status", "unknown")
    print(f"  1st call: result={result}, token-status={status}")
    assert status == "new", f"Expected 'new', got '{status}'"

    # Retry with same token: cached result
    result = client.command("IDEMPOTENT.EXEC", "SET", "order:123", "confirmed",
                            headers={"idempotency-token": token})
    attrs = client.last_reply_attributes or {}
    status = attrs.get("token-status", "unknown")
    print(f"  2nd call: result={result}, token-status={status}")
    assert status == "cached", f"Expected 'cached', got '{status}'"

    # Third retry: still cached
    result = client.command("IDEMPOTENT.EXEC", "SET", "order:123", "confirmed",
                            headers={"idempotency-token": token})
    attrs = client.last_reply_attributes or {}
    status = attrs.get("token-status", "unknown")
    print(f"  3rd call: result={result}, token-status={status}")
    assert status == "cached", f"Expected 'cached', got '{status}'"

    # Different token: new execution
    new_token = str(uuid.uuid4())
    result = client.command("IDEMPOTENT.EXEC", "SET", "order:123", "shipped",
                            headers={"idempotency-token": new_token})
    attrs = client.last_reply_attributes or {}
    status = attrs.get("token-status", "unknown")
    print(f"  New token: result={result}, token-status={status}")
    assert status == "new", f"Expected 'new', got '{status}'"

    # Verify final value
    val = client.command("GET", "order:123")
    print(f"\n  Final value of order:123 = '{val}'")
    assert val == "shipped"

    client.command("DEL", "order:123")
    print("  ✅ PASSED")


def demo_idempotent_incr(client):
    """Demonstrate idempotent INCR — retries don't double-count."""
    banner("Demo 2: Idempotent INCR (no double-counting)")

    client.command("SET", "counter", "0")
    print("  Initial counter = 0")

    token = str(uuid.uuid4())
    print(f"  Token: {token[:8]}...")
    print()

    # First INCR
    result = client.command("IDEMPOTENT.EXEC", "INCR", "counter",
                            headers={"idempotency-token": token})
    attrs = client.last_reply_attributes or {}
    status = attrs.get("token-status", "unknown")
    print(f"  INCR #1: result={result}, status={status}")

    # Retry same INCR (e.g., timeout, client didn't see response)
    result = client.command("IDEMPOTENT.EXEC", "INCR", "counter",
                            headers={"idempotency-token": token})
    attrs = client.last_reply_attributes or {}
    status = attrs.get("token-status", "unknown")
    print(f"  INCR #2 (retry): result={result}, status={status}")

    # Another retry
    result = client.command("IDEMPOTENT.EXEC", "INCR", "counter",
                            headers={"idempotency-token": token})
    attrs = client.last_reply_attributes or {}
    status = attrs.get("token-status", "unknown")
    print(f"  INCR #3 (retry): result={result}, status={status}")

    # Counter should be 1, not 3
    val = client.command("GET", "counter")
    print(f"\n  Final counter = {val}  (would be 3 without idempotency!)")
    assert val == "1", f"Expected '1', got '{val}'"

    client.command("DEL", "counter")
    print("  ✅ PASSED")


def demo_token_invalidation(client):
    """Demonstrate token invalidation — allow re-execution."""
    banner("Demo 3: Token Invalidation")

    token = str(uuid.uuid4())
    print(f"  Token: {token[:8]}...")
    print()

    # Execute
    result = client.command("IDEMPOTENT.EXEC", "SET", "config:version", "v1",
                            headers={"idempotency-token": token})
    attrs = client.last_reply_attributes or {}
    print(f"  Execute: result={result}, status={attrs.get('token-status')}")

    # Verify cached
    result = client.command("IDEMPOTENT.EXEC", "SET", "config:version", "v2",
                            headers={"idempotency-token": token})
    attrs = client.last_reply_attributes or {}
    print(f"  Retry:   result={result}, status={attrs.get('token-status')}")
    assert attrs.get("token-status") == "cached"

    val = client.command("GET", "config:version")
    print(f"  Value before invalidation: {val}")
    assert val == "v1"

    # Invalidate
    inv_result = client.command("IDEMPOTENT.INVALIDATE", token)
    print(f"  Invalidation: {inv_result}")

    # Re-execute with same token — now it's a NEW execution
    result = client.command("IDEMPOTENT.EXEC", "SET", "config:version", "v2",
                            headers={"idempotency-token": token})
    attrs = client.last_reply_attributes or {}
    print(f"  After invalidation: result={result}, status={attrs.get('token-status')}")
    assert attrs.get("token-status") == "new"

    val = client.command("GET", "config:version")
    print(f"  Value after re-execution: {val}")
    assert val == "v2"

    client.command("DEL", "config:version")
    print("  ✅ PASSED")


def demo_stats(client):
    """Show module statistics."""
    banner("Demo 4: Module Statistics")

    stats = client.command("IDEMPOTENT.STATS")
    if isinstance(stats, dict):
        for k, v in stats.items():
            print(f"  {k}: {v}")
    else:
        print(f"  Stats: {stats}")
    print()
    print("  ✅ Done")


def main():
    print("=" * 60)
    print("  Valkey RESP4 Idempotency Token Module Demo")
    print("=" * 60)

    host = os.environ.get("VALKEY_HOST", "127.0.0.1")
    port = int(os.environ.get("VALKEY_PORT", "6379"))

    print(f"\n  Connecting to {host}:{port} ...")
    client = Resp4Client(host=host, port=port)

    try:
        reply = client.connect()
        print(f"  Connected! HELLO 4 reply: proto={reply.get('proto', '?')}")
    except Exception as e:
        print(f"  ❌ Failed to connect: {e}")
        print("  Make sure valkey-server is running with:")
        print("    ./src/valkey-server --loadmodule src/modules/idempotency.so")
        sys.exit(1)

    # Clean up any leftover state
    client.command("IDEMPOTENT.FLUSH")

    try:
        demo_basic_idempotent_set(client)
        demo_idempotent_incr(client)
        demo_token_invalidation(client)
        demo_stats(client)
    except Exception as e:
        print(f"\n  ❌ Demo failed: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
    finally:
        # Clean up
        client.command("IDEMPOTENT.FLUSH")
        client.close()

    banner("All Demos Passed! ✅")


if __name__ == "__main__":
    main()
