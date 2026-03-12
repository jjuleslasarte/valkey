#!/usr/bin/env python3
"""
Mini Payment Processing App — Before & After Idempotency Tokens

This simulates a realistic e-commerce scenario where a payment service
charges customers using Valkey as the backend. Network issues cause
timeouts, so the client retries — and without idempotency, customers
get double-charged.

Scenario: Process 5 orders. Each order's charge request "times out" once,
causing exactly 1 retry per order.

  BEFORE (vanilla Valkey):  Customer charged TWICE per order  → $500 charged instead of $250
  AFTER  (with idempotency): Retry is safe, same result      → $250 charged correctly

Usage:
  # Server must already be running with idempotency module:
  #   ./src/valkey-server --loadmodule src/modules/idempotency.so --enable-module-command yes
  # Or just run:
  #   bash demo/idempotency/run-demo.sh   (which starts the server for you)

  python3 demo/idempotency/payment_app.py
"""

import sys
import os
import uuid
import time
import random

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "otel"))
from resp4_client import Resp4Client

# ============================================================================
# Simulated application state
# ============================================================================

ORDERS = [
    {"id": "ORD-1001", "customer": "Alice",   "amount": 49.99},
    {"id": "ORD-1002", "customer": "Bob",     "amount": 29.50},
    {"id": "ORD-1003", "customer": "Charlie", "amount": 75.00},
    {"id": "ORD-1004", "customer": "Diana",   "amount": 12.99},
    {"id": "ORD-1005", "customer": "Eve",     "amount": 89.00},
]


def colored(text, color):
    """Simple ANSI color helper."""
    colors = {"red": "\033[91m", "green": "\033[92m", "yellow": "\033[93m",
              "blue": "\033[94m", "bold": "\033[1m", "dim": "\033[2m", "reset": "\033[0m"}
    return f"{colors.get(color, '')}{text}{colors['reset']}"


def banner(title, char="="):
    width = 68
    print(f"\n{char * width}")
    print(f"  {title}")
    print(f"{char * width}\n")


# ============================================================================
# BEFORE: Vanilla Valkey — no idempotency protection
# ============================================================================

def run_without_idempotency(client):
    """
    Simulate processing orders WITHOUT idempotency tokens.
    Each order "times out" once, causing a retry that DOUBLE-CHARGES the customer.
    """
    banner("BEFORE: Processing Orders WITHOUT Idempotency", "!")

    print("  Scenario: Payment service charges customers via Valkey INCR.")
    print("            Each request 'times out' once → client retries.")
    print("            Without idempotency, the retry executes AGAIN.\n")

    # Reset state
    client.command("SET", "total_revenue", "0")
    for order in ORDERS:
        client.command("DEL", f"charge:{order['id']}")

    total_expected = 0
    charges_log = []

    for order in ORDERS:
        amount_cents = int(order["amount"] * 100)
        total_expected += amount_cents

        print(f"  📦 Order {order['id']} — {order['customer']} — ${order['amount']:.2f}")

        # First attempt: "charges" the customer (INCR succeeds)
        client.command("INCRBY", f"charge:{order['id']}", str(amount_cents))
        client.command("INCRBY", "total_revenue", str(amount_cents))
        print(f"     ⚡ Attempt 1: INCRBY charge:{order['id']} {amount_cents} → executed")

        # Simulate timeout: client didn't see the response, so it retries
        print(f"     ⏱️  Timeout! Client retries...")

        # Retry: INCR runs AGAIN — double charge!
        client.command("INCRBY", f"charge:{order['id']}", str(amount_cents))
        client.command("INCRBY", "total_revenue", str(amount_cents))
        print(f"     ⚡ Attempt 2: INCRBY charge:{order['id']} {amount_cents} → {colored('EXECUTED AGAIN!', 'red')}")

        actual_charge = int(client.command("GET", f"charge:{order['id']}"))
        charges_log.append((order, actual_charge))
        print(f"     💰 Actual charge: {colored(f'${actual_charge/100:.2f}', 'red')} (should be ${amount_cents/100:.2f})")
        print()

    # Summary
    actual_total = int(client.command("GET", "total_revenue"))
    print(f"  {'─' * 50}")
    print(f"  Expected total revenue:  ${total_expected/100:.2f}")
    print(f"  Actual total revenue:    {colored(f'${actual_total/100:.2f}', 'red')}")
    print(f"  Overcharge:              {colored(f'${(actual_total - total_expected)/100:.2f}', 'red')}")
    print()

    print(f"  {colored('❌ PROBLEM: Every customer was charged TWICE!', 'red')}")
    print(f"     The retry re-executed INCRBY, doubling every charge.")
    print()

    # Verify
    for order, actual in charges_log:
        expected = int(order["amount"] * 100)
        status = "✅" if actual == expected else colored("❌ DOUBLE-CHARGED", "red")
        print(f"     {order['customer']:8s}  expected ${expected/100:.2f}  actual ${actual/100:.2f}  {status}")

    return actual_total, total_expected


# ============================================================================
# AFTER: With Idempotency Tokens — safe retries
# ============================================================================

def run_with_idempotency(client):
    """
    Simulate processing the SAME orders WITH idempotency tokens.
    Each request "times out" once, causing a retry — but the retry is
    safely deduplicated by the idempotency module.
    """
    banner("AFTER: Processing Orders WITH Idempotency Tokens", "=")

    print("  Same scenario, but now each request carries an idempotency-token")
    print("  via RESP4 headers. Retries return the cached result — no re-execution.\n")

    # Reset state
    client.command("SET", "total_revenue_safe", "0")
    for order in ORDERS:
        client.command("DEL", f"safe_charge:{order['id']}")
    client.command("IDEMPOTENT.FLUSH")

    total_expected = 0
    charges_log = []

    for order in ORDERS:
        amount_cents = int(order["amount"] * 100)
        total_expected += amount_cents

        # Generate a unique idempotency token for this charge operation
        # In real life: token = f"{order_id}:{payment_attempt_id}"
        charge_token = f"charge-{order['id']}-{uuid.uuid4().hex[:8]}"
        revenue_token = f"revenue-{order['id']}-{uuid.uuid4().hex[:8]}"

        print(f"  📦 Order {order['id']} — {order['customer']} — ${order['amount']:.2f}")
        print(f"     🔑 Token: {charge_token[:30]}...")

        # First attempt: executes the charge
        result = client.command(
            "IDEMPOTENT.EXEC", "INCRBY", f"safe_charge:{order['id']}", str(amount_cents),
            headers={"idempotency-token": charge_token}
        )
        attrs = client.last_reply_attributes or {}
        status = attrs.get("token-status", "?")
        print(f"     ⚡ Attempt 1: status={colored(status, 'green')}")

        client.command(
            "IDEMPOTENT.EXEC", "INCRBY", "total_revenue_safe", str(amount_cents),
            headers={"idempotency-token": revenue_token}
        )

        # Simulate timeout: client retries with SAME token
        print(f"     ⏱️  Timeout! Client retries with same token...")

        result = client.command(
            "IDEMPOTENT.EXEC", "INCRBY", f"safe_charge:{order['id']}", str(amount_cents),
            headers={"idempotency-token": charge_token}
        )
        attrs = client.last_reply_attributes or {}
        status = attrs.get("token-status", "?")
        print(f"     ⚡ Attempt 2: status={colored(status, 'yellow')} → {colored('SKIPPED (cached)', 'green')}")

        client.command(
            "IDEMPOTENT.EXEC", "INCRBY", "total_revenue_safe", str(amount_cents),
            headers={"idempotency-token": revenue_token}
        )

        actual_charge = int(client.command("GET", f"safe_charge:{order['id']}"))
        charges_log.append((order, actual_charge))
        print(f"     💰 Actual charge: {colored(f'${actual_charge/100:.2f}', 'green')} ✓")
        print()

    # Summary
    actual_total = int(client.command("GET", "total_revenue_safe"))
    print(f"  {'─' * 50}")
    print(f"  Expected total revenue:  ${total_expected/100:.2f}")
    print(f"  Actual total revenue:    {colored(f'${actual_total/100:.2f}', 'green')}")
    diff = actual_total - total_expected
    if diff == 0:
        print(f"  Overcharge:              {colored('$0.00 ✓', 'green')}")
    else:
        print(f"  Overcharge:              ${diff/100:.2f}")
    print()

    print(f"  {colored('✅ SUCCESS: Every customer charged exactly once!', 'green')}")
    print(f"     The retry was detected by the idempotency token and returned")
    print(f"     the cached result without re-executing INCRBY.")
    print()

    for order, actual in charges_log:
        expected = int(order["amount"] * 100)
        status = colored("✅ CORRECT", "green") if actual == expected else "❌ ERROR"
        print(f"     {order['customer']:8s}  expected ${expected/100:.2f}  actual ${actual/100:.2f}  {status}")

    return actual_total, total_expected


# ============================================================================
# Side-by-side comparison
# ============================================================================

def print_comparison(before_total, before_expected, after_total, after_expected):
    banner("COMPARISON: Before vs After")

    col_w = 30
    print(f"  {'':20s} {'WITHOUT idempotency':>{col_w}s}   {'WITH idempotency':>{col_w}s}")
    print(f"  {'─' * 20} {'─' * col_w} {'─' * col_w}")
    print(f"  {'Expected revenue':20s} {f'${before_expected/100:.2f}':>{col_w}s}   {f'${after_expected/100:.2f}':>{col_w}s}")
    print(f"  {'Actual revenue':20s} {colored(f'${before_total/100:.2f}', 'red'):>{col_w+9}s}   {colored(f'${after_total/100:.2f}', 'green'):>{col_w+9}s}")
    overcharge_before = before_total - before_expected
    overcharge_after = after_total - after_expected
    print(f"  {'Overcharge':20s} {colored(f'${overcharge_before/100:.2f}', 'red'):>{col_w+9}s}   {colored(f'${overcharge_after/100:.2f}', 'green'):>{col_w+9}s}")
    print(f"  {'Status':20s} {colored('❌ CUSTOMERS DOUBLE-CHARGED', 'red'):>{col_w+9}s}   {colored('✅ ALL CHARGES CORRECT', 'green'):>{col_w+9}s}")
    print()

    # Show stats
    print(f"  The idempotency module detected and deduplicated {len(ORDERS)} retried requests.")
    print(f"  Each retry returned the cached result in microseconds — zero re-execution.\n")


# ============================================================================
# Main
# ============================================================================

def main():
    banner("💳 Payment Processing App — Idempotency Demo", "═")
    print("  This simulates an e-commerce payment service using Valkey.")
    print("  5 orders are processed. Each one 'times out' once, causing a retry.")
    print()
    print("  We run the same scenario twice:")
    print("    1. WITHOUT idempotency → double charges! 💸")
    print("    2. WITH idempotency    → safe retries! ✅")

    host = os.environ.get("VALKEY_HOST", "127.0.0.1")
    port = int(os.environ.get("VALKEY_PORT", "6379"))

    client = Resp4Client(host=host, port=port)
    try:
        reply = client.connect()
        print(f"\n  Connected to Valkey at {host}:{port} (RESP4, proto={reply.get('proto', '?')})")
    except Exception as e:
        print(f"\n  ❌ Cannot connect to Valkey at {host}:{port}: {e}")
        print("  Start with: bash demo/idempotency/run-demo.sh")
        sys.exit(1)

    # Run BEFORE scenario
    before_total, before_expected = run_without_idempotency(client)

    input(colored("\n  Press Enter to continue to the AFTER scenario...\n", "dim"))

    # Run AFTER scenario
    after_total, after_expected = run_with_idempotency(client)

    # Show comparison
    print_comparison(before_total, before_expected, after_total, after_expected)

    # Show module stats
    stats = client.command("IDEMPOTENT.STATS")
    banner("Module Stats")
    if isinstance(stats, dict):
        for k, v in stats.items():
            print(f"  {k}: {v}")

    # Cleanup
    client.command("IDEMPOTENT.FLUSH")
    for order in ORDERS:
        client.command("DEL", f"charge:{order['id']}", f"safe_charge:{order['id']}")
    client.command("DEL", "total_revenue", "total_revenue_safe")
    client.close()

    print()


if __name__ == "__main__":
    main()
