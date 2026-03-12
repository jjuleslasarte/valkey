#!/bin/bash
# Run the Idempotency Token Module demo.
#
# This script:
#   1. Builds valkey-server and the idempotency module (if needed)
#   2. Starts a valkey-server with the module loaded
#   3. Runs the Python demo
#   4. Stops the server
#
# Usage:
#   cd /path/to/valkey
#   bash demo/idempotency/run-demo.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

cd "$REPO_ROOT"

echo "============================================"
echo "  Idempotency Token Module Demo"
echo "============================================"
echo

# Determine server binary
if [ -f src/valkey-server ]; then
    VALKEY_SERVER=./src/valkey-server
elif [ -f build/bin/valkey-server ]; then
    VALKEY_SERVER=./build/bin/valkey-server
else
    echo "Building valkey-server and modules..."
    make -j$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)
    VALKEY_SERVER=./src/valkey-server
fi

# Build module if needed
if [ ! -f src/modules/idempotency.so ]; then
    echo "Building idempotency module..."
    make -C src/modules idempotency.so
fi

# Check module exists
if [ ! -f src/modules/idempotency.so ]; then
    echo "ERROR: src/modules/idempotency.so not found."
    exit 1
fi

echo "Using server: $VALKEY_SERVER"

PORT=6399
PIDFILE="/tmp/valkey-idempotency-demo.pid"
LOGFILE="/tmp/valkey-idempotency-demo.log"

# Kill any existing demo server
if [ -f "$PIDFILE" ]; then
    kill "$(cat "$PIDFILE")" 2>/dev/null || true
    rm -f "$PIDFILE"
fi

echo "Starting valkey-server on port $PORT with idempotency module..."
$VALKEY_SERVER \
    --port $PORT \
    --daemonize yes \
    --pidfile "$PIDFILE" \
    --logfile "$LOGFILE" \
    --loadmodule src/modules/idempotency.so \
    --enable-module-command yes \
    --save ""

# Wait for server to start
sleep 1

if [ ! -f "$PIDFILE" ]; then
    echo "ERROR: Server failed to start. Check $LOGFILE"
    cat "$LOGFILE"
    exit 1
fi

echo "Server started (PID $(cat $PIDFILE))"
echo

# Run the demo
VALKEY_PORT=$PORT python3 "$SCRIPT_DIR/demo.py"
DEMO_EXIT=$?

# Stop the server
echo
echo "Stopping server..."
kill "$(cat "$PIDFILE")" 2>/dev/null || true
rm -f "$PIDFILE"
rm -f "$LOGFILE"

exit $DEMO_EXIT
