#!/bin/bash
# Run the Payment Processing App demo (before & after idempotency).
#
# Usage:
#   cd /path/to/valkey
#   bash demo/idempotency/run-payment-app.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

cd "$REPO_ROOT"

# Determine server binary
if [ -f src/valkey-server ]; then
    VALKEY_SERVER=./src/valkey-server
elif [ -f build/bin/valkey-server ]; then
    VALKEY_SERVER=./build/bin/valkey-server
else
    echo "Building valkey-server..."
    make -j$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)
    VALKEY_SERVER=./src/valkey-server
fi

# Build module if needed
if [ ! -f src/modules/idempotency.so ]; then
    echo "Building idempotency module..."
    make -C src/modules idempotency.so
fi

PORT=6399
PIDFILE="/tmp/valkey-payment-demo.pid"
LOGFILE="/tmp/valkey-payment-demo.log"

# Kill any existing demo server
if [ -f "$PIDFILE" ]; then
    kill "$(cat "$PIDFILE")" 2>/dev/null || true
    rm -f "$PIDFILE"
    sleep 0.5
fi

echo "Starting valkey-server on port $PORT..."
$VALKEY_SERVER \
    --port $PORT \
    --daemonize yes \
    --pidfile "$PIDFILE" \
    --logfile "$LOGFILE" \
    --loadmodule src/modules/idempotency.so \
    --enable-module-command yes \
    --save ""

sleep 1

if [ ! -f "$PIDFILE" ]; then
    echo "ERROR: Server failed to start. Check $LOGFILE"
    cat "$LOGFILE" 2>/dev/null
    exit 1
fi

echo "Server started (PID $(cat $PIDFILE))"

# Run the payment app
VALKEY_PORT=$PORT python3 "$SCRIPT_DIR/payment_app.py"
EXIT_CODE=$?

# Stop the server
kill "$(cat "$PIDFILE")" 2>/dev/null || true
rm -f "$PIDFILE" "$LOGFILE"

exit $EXIT_CODE
