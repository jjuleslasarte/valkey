#!/usr/bin/env bash
# ============================================================================
# RESP4 OpenTelemetry Demo — Full orchestration script (no Docker required)
#
# This script:
#   1. Downloads Jaeger binary (if needed) for trace visualization
#   2. Starts Jaeger as a local process
#   3. Starts Valkey with the otelmodule loaded
#   4. Sets up a Python venv with OpenTelemetry SDK
#   5. Runs the demo (sends traced commands to Valkey)
#   6. Opens Jaeger UI in the browser
#
# Usage:
#   ./run-demo.sh          # Run the full demo
#   ./run-demo.sh clean    # Tear down everything (including downloaded Jaeger)
# ============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
VALKEY_SERVER="$PROJECT_ROOT/src/valkey-server"
VALKEY_CLI="$PROJECT_ROOT/src/valkey-cli"
OTEL_MODULE="$PROJECT_ROOT/src/modules/otelmodule.so"
VENV_DIR="$SCRIPT_DIR/.venv"
JAEGER_DIR="$SCRIPT_DIR/.jaeger"
VALKEY_PORT=6399  # Use non-default port to avoid conflicts
VALKEY_PID=""
JAEGER_PID=""

JAEGER_VERSION="2.16.0"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

log()  { echo -e "${CYAN}[demo]${NC} $*"; }
ok()   { echo -e "${GREEN}[  ok]${NC} $*"; }
warn() { echo -e "${YELLOW}[warn]${NC} $*"; }
err()  { echo -e "${RED}[ err]${NC} $*"; }

# ============================================================================
# Cleanup
# ============================================================================

cleanup() {
    log "Cleaning up..."

    # Stop Valkey
    if [ -n "${VALKEY_PID:-}" ] && kill -0 "$VALKEY_PID" 2>/dev/null; then
        log "Stopping Valkey (PID $VALKEY_PID)..."
        kill "$VALKEY_PID" 2>/dev/null || true
        wait "$VALKEY_PID" 2>/dev/null || true
        ok "Valkey stopped"
    fi

    # Stop Jaeger
    if [ -n "${JAEGER_PID:-}" ] && kill -0 "$JAEGER_PID" 2>/dev/null; then
        log "Stopping Jaeger (PID $JAEGER_PID)..."
        kill "$JAEGER_PID" 2>/dev/null || true
        wait "$JAEGER_PID" 2>/dev/null || true
        ok "Jaeger stopped"
    fi
}

if [ "${1:-}" = "clean" ]; then
    cleanup
    log "Removing venv..."
    rm -rf "$VENV_DIR"
    log "Removing Jaeger binary..."
    rm -rf "$JAEGER_DIR"
    ok "All cleaned up!"
    exit 0
fi

trap cleanup EXIT

# ============================================================================
# Detect platform
# ============================================================================

detect_platform() {
    local os arch
    os="$(uname -s | tr '[:upper:]' '[:lower:]')"
    arch="$(uname -m)"

    case "$os" in
        darwin) os="darwin" ;;
        linux)  os="linux" ;;
        *)      err "Unsupported OS: $os"; exit 1 ;;
    esac

    case "$arch" in
        x86_64|amd64)   arch="amd64" ;;
        arm64|aarch64)   arch="arm64" ;;
        *)               err "Unsupported architecture: $arch"; exit 1 ;;
    esac

    echo "${os}-${arch}"
}

# ============================================================================
# Pre-flight checks
# ============================================================================

log "Running pre-flight checks..."

if [ ! -f "$VALKEY_SERVER" ]; then
    err "Valkey server not found at $VALKEY_SERVER"
    err "Build Valkey first: cd $PROJECT_ROOT && make"
    exit 1
fi

if [ ! -f "$OTEL_MODULE" ]; then
    err "otelmodule.so not found at $OTEL_MODULE"
    log "Building module..."
    (cd "$PROJECT_ROOT/src/modules" && make otelmodule.so)
fi

if ! command -v python3 &>/dev/null; then
    err "Python 3 is required but not found."
    exit 1
fi

if ! command -v curl &>/dev/null && ! command -v wget &>/dev/null; then
    err "curl or wget is required to download Jaeger."
    exit 1
fi

ok "All pre-flight checks passed"

# ============================================================================
# Step 1: Download & Start Jaeger (binary, no Docker)
# ============================================================================

echo ""
log "━━━ Step 1: Starting Jaeger (trace backend) ━━━"

# Check if Jaeger is already running
if curl -sf http://localhost:16686/ >/dev/null 2>&1; then
    ok "Jaeger is already running at http://localhost:16686"
else
    PLATFORM="$(detect_platform)"
    JAEGER_BINARY="$JAEGER_DIR/jaeger"

    if [ ! -f "$JAEGER_BINARY" ]; then
        mkdir -p "$JAEGER_DIR"
        TARBALL="jaeger-${JAEGER_VERSION}-${PLATFORM}.tar.gz"
        DOWNLOAD_URL="https://github.com/jaegertracing/jaeger/releases/download/v${JAEGER_VERSION}/${TARBALL}"

        log "Downloading Jaeger v${JAEGER_VERSION} for ${PLATFORM}..."
        log "  URL: ${DOWNLOAD_URL}"

        if command -v curl &>/dev/null; then
            curl -fSL --progress-bar "$DOWNLOAD_URL" -o "$JAEGER_DIR/$TARBALL"
        else
            wget -q --show-progress "$DOWNLOAD_URL" -O "$JAEGER_DIR/$TARBALL"
        fi

        log "Extracting..."
        tar -xzf "$JAEGER_DIR/$TARBALL" -C "$JAEGER_DIR" --strip-components=1
        rm -f "$JAEGER_DIR/$TARBALL"

        if [ ! -f "$JAEGER_BINARY" ]; then
            # Some releases use jaeger-all-in-one or different naming
            for candidate in "$JAEGER_DIR"/jaeger*; do
                if [ -x "$candidate" ] && file "$candidate" | grep -qi executable; then
                    mv "$candidate" "$JAEGER_BINARY"
                    break
                fi
            done
        fi

        chmod +x "$JAEGER_BINARY"
        ok "Jaeger downloaded to $JAEGER_BINARY"
    else
        ok "Jaeger binary already exists at $JAEGER_BINARY"
    fi

    log "Starting Jaeger..."
    "$JAEGER_BINARY" \
        --set receivers.otlp.protocols.http.endpoint=0.0.0.0:4318 \
        --set receivers.otlp.protocols.grpc.endpoint=0.0.0.0:4317 \
        >"$JAEGER_DIR/jaeger.log" 2>&1 &
    JAEGER_PID=$!

    # Wait for Jaeger UI to be ready
    log "Waiting for Jaeger to start (PID $JAEGER_PID)..."
    for i in $(seq 1 30); do
        if curl -sf http://localhost:16686/ >/dev/null 2>&1; then
            break
        fi
        if ! kill -0 "$JAEGER_PID" 2>/dev/null; then
            err "Jaeger process died. Check logs: $JAEGER_DIR/jaeger.log"
            tail -20 "$JAEGER_DIR/jaeger.log" 2>/dev/null || true
            exit 1
        fi
        sleep 1
    done

    if curl -sf http://localhost:16686/ >/dev/null 2>&1; then
        ok "Jaeger running at http://localhost:16686 (PID $JAEGER_PID)"
    else
        err "Jaeger did not start within 30 seconds"
        tail -20 "$JAEGER_DIR/jaeger.log" 2>/dev/null || true
        exit 1
    fi
fi

# ============================================================================
# Step 2: Start Valkey with otelmodule
# ============================================================================

echo ""
log "━━━ Step 2: Starting Valkey with otelmodule ━━━"

# Check if something is already on our port
if "$VALKEY_CLI" -p "$VALKEY_PORT" PING >/dev/null 2>&1; then
    warn "Valkey already running on port $VALKEY_PORT, reusing it"
    # Check if module is loaded
    if ! "$VALKEY_CLI" -p "$VALKEY_PORT" COMMAND INFO otel.stats >/dev/null 2>&1; then
        warn "otelmodule not loaded, attempting MODULE LOAD..."
        "$VALKEY_CLI" -p "$VALKEY_PORT" MODULE LOAD "$OTEL_MODULE" || true
    fi
else
    "$VALKEY_SERVER" \
        --port "$VALKEY_PORT" \
        --loadmodule "$OTEL_MODULE" \
        --daemonize no \
        --loglevel notice \
        --save "" \
        --appendonly no &
    VALKEY_PID=$!

    # Wait for Valkey to be ready
    log "Waiting for Valkey to start (port $VALKEY_PORT)..."
    for i in $(seq 1 30); do
        if "$VALKEY_CLI" -p "$VALKEY_PORT" PING >/dev/null 2>&1; then
            break
        fi
        sleep 0.5
    done

    if "$VALKEY_CLI" -p "$VALKEY_PORT" PING >/dev/null 2>&1; then
        ok "Valkey running on port $VALKEY_PORT (PID $VALKEY_PID)"
    else
        err "Valkey failed to start"
        exit 1
    fi
fi

# Verify module is loaded
MODULE_INFO=$("$VALKEY_CLI" -p "$VALKEY_PORT" MODULE LIST 2>&1)
if echo "$MODULE_INFO" | grep -qi "otel"; then
    ok "otelmodule loaded successfully"
else
    err "otelmodule does not appear in MODULE LIST"
    echo "$MODULE_INFO"
    exit 1
fi

# ============================================================================
# Step 3: Setup Python venv
# ============================================================================

echo ""
log "━━━ Step 3: Setting up Python environment ━━━"

if [ ! -d "$VENV_DIR" ]; then
    log "Creating virtual environment..."
    python3 -m venv "$VENV_DIR"
    ok "Virtual environment created"
fi

# shellcheck disable=SC1091
source "$VENV_DIR/bin/activate"

log "Installing OpenTelemetry SDK..."
pip install -q \
    opentelemetry-api \
    opentelemetry-sdk \
    opentelemetry-exporter-otlp-proto-http 2>&1 | tail -1

ok "Python dependencies installed"

# ============================================================================
# Step 4: Run the demo
# ============================================================================

echo ""
log "━━━ Step 4: Running OpenTelemetry demo ━━━"

cd "$SCRIPT_DIR"
python3 demo.py --port "$VALKEY_PORT" --jaeger-endpoint http://localhost:4318

# ============================================================================
# Step 5: Open Jaeger UI
# ============================================================================

echo ""
log "━━━ Step 5: Opening Jaeger UI ━━━"

JAEGER_URL="http://localhost:16686/search?service=valkey-otel-demo&limit=20"

if command -v open &>/dev/null; then
    open "$JAEGER_URL"
    ok "Opened Jaeger UI in browser"
elif command -v xdg-open &>/dev/null; then
    xdg-open "$JAEGER_URL"
    ok "Opened Jaeger UI in browser"
else
    log "Open this URL in your browser: $JAEGER_URL"
fi

echo ""
log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
log "Demo is running. Press Ctrl+C to stop."
log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
log "Useful commands while running:"
log "  $VALKEY_CLI -p $VALKEY_PORT --resp4 --header traceparent=00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01 SET test hello"
log "  $VALKEY_CLI -p $VALKEY_PORT OTEL.STATS"
log "  $VALKEY_CLI -p $VALKEY_PORT COMMANDLOG GET 5"
echo ""

# Keep running until Ctrl+C (cleanup trap handles shutdown)
if [ -n "${VALKEY_PID:-}" ]; then
    wait "$VALKEY_PID" 2>/dev/null || true
elif [ -n "${JAEGER_PID:-}" ]; then
    wait "$JAEGER_PID" 2>/dev/null || true
fi
