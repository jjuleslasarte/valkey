#!/usr/bin/env bash
# ============================================================================
# RESP4 OpenTelemetry Demo — Grafana + Jaeger (no Docker required)
#
# This script:
#   1. Downloads Jaeger binary (OTLP trace collector + storage)
#   2. Downloads Grafana OSS binary (trace visualization UI)
#   3. Starts both with Grafana auto-configured to read from Jaeger
#   4. Starts Valkey with the otelmodule loaded
#   5. Sets up a Python venv with OpenTelemetry SDK
#   6. Runs the demo (sends traced commands to Valkey)
#   7. Opens Grafana Explore in the browser
#
# Usage:
#   ./run-demo.sh          # Run the full demo
#   ./run-demo.sh clean    # Tear down everything
# ============================================================================

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
VALKEY_SERVER="$PROJECT_ROOT/src/valkey-server"
VALKEY_CLI="$PROJECT_ROOT/src/valkey-cli"
OTEL_MODULE="$PROJECT_ROOT/src/modules/otelmodule.so"
VENV_DIR="$SCRIPT_DIR/.venv"
JAEGER_DIR="$SCRIPT_DIR/.jaeger"
GRAFANA_DIR="$SCRIPT_DIR/.grafana"
VALKEY_PORT=6399
VALKEY_PID=""
JAEGER_PID=""
GRAFANA_PID=""

JAEGER_VERSION="2.16.0"
GRAFANA_VERSION="11.6.0"

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

    if [ -n "${VALKEY_PID:-}" ] && kill -0 "$VALKEY_PID" 2>/dev/null; then
        log "Stopping Valkey (PID $VALKEY_PID)..."
        kill "$VALKEY_PID" 2>/dev/null || true
        wait "$VALKEY_PID" 2>/dev/null || true
        ok "Valkey stopped"
    fi

    if [ -n "${GRAFANA_PID:-}" ] && kill -0 "$GRAFANA_PID" 2>/dev/null; then
        log "Stopping Grafana (PID $GRAFANA_PID)..."
        kill "$GRAFANA_PID" 2>/dev/null || true
        wait "$GRAFANA_PID" 2>/dev/null || true
        ok "Grafana stopped"
    fi

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
    log "Removing Jaeger..."
    rm -rf "$JAEGER_DIR"
    log "Removing Grafana..."
    rm -rf "$GRAFANA_DIR"
    rm -rf "$SCRIPT_DIR/.grafana-data"
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

download_file() {
    local url="$1" dest="$2"
    if command -v curl &>/dev/null; then
        curl -fSL --progress-bar "$url" -o "$dest"
    else
        wget -q --show-progress "$url" -O "$dest"
    fi
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
    log "Building otelmodule..."
    (cd "$PROJECT_ROOT/src/modules" && make otelmodule.so)
fi

if ! command -v python3 &>/dev/null; then
    err "Python 3 is required but not found."
    exit 1
fi

ok "All pre-flight checks passed"

# ============================================================================
# Step 1: Download & Start Jaeger (OTLP collector)
# ============================================================================

echo ""
log "━━━ Step 1: Starting Jaeger (trace collector) ━━━"

PLATFORM="$(detect_platform)"

if curl -sf http://localhost:16686/ >/dev/null 2>&1; then
    ok "Jaeger is already running at http://localhost:16686"
else
    JAEGER_BINARY="$JAEGER_DIR/jaeger"

    if [ ! -f "$JAEGER_BINARY" ]; then
        mkdir -p "$JAEGER_DIR"
        TARBALL="jaeger-${JAEGER_VERSION}-${PLATFORM}.tar.gz"
        DOWNLOAD_URL="https://github.com/jaegertracing/jaeger/releases/download/v${JAEGER_VERSION}/${TARBALL}"

        log "Downloading Jaeger v${JAEGER_VERSION} for ${PLATFORM}..."
        download_file "$DOWNLOAD_URL" "$JAEGER_DIR/$TARBALL"

        log "Extracting..."
        tar -xzf "$JAEGER_DIR/$TARBALL" -C "$JAEGER_DIR" --strip-components=1
        rm -f "$JAEGER_DIR/$TARBALL"

        if [ ! -f "$JAEGER_BINARY" ]; then
            for candidate in "$JAEGER_DIR"/jaeger*; do
                if [ -x "$candidate" ] && file "$candidate" | grep -qi executable; then
                    mv "$candidate" "$JAEGER_BINARY"
                    break
                fi
            done
        fi
        chmod +x "$JAEGER_BINARY"
        ok "Jaeger downloaded"
    fi

    log "Starting Jaeger..."
    "$JAEGER_BINARY" \
        --set receivers.otlp.protocols.http.endpoint=0.0.0.0:4318 \
        --set receivers.otlp.protocols.grpc.endpoint=0.0.0.0:4317 \
        >"$JAEGER_DIR/jaeger.log" 2>&1 &
    JAEGER_PID=$!

    for i in $(seq 1 30); do
        if curl -sf http://localhost:16686/ >/dev/null 2>&1; then break; fi
        if ! kill -0 "$JAEGER_PID" 2>/dev/null; then
            err "Jaeger died. Logs:"; tail -20 "$JAEGER_DIR/jaeger.log" 2>/dev/null; exit 1
        fi
        sleep 1
    done
    ok "Jaeger running (OTLP on :4318, API on :16686)"
fi

# ============================================================================
# Step 2: Download & Start Grafana
# ============================================================================

echo ""
log "━━━ Step 2: Starting Grafana (trace visualization) ━━━"

if curl -sf http://localhost:3000/api/health >/dev/null 2>&1; then
    ok "Grafana is already running at http://localhost:3000"
else
    # Determine Grafana home directory
    GRAFANA_HOME=""
    GRAFANA_SERVER=""

    if [ ! -d "$GRAFANA_DIR/bin" ]; then
        mkdir -p "$GRAFANA_DIR"

        # Grafana uses os/arch format: darwin-arm64, linux-amd64
        GRAFANA_TARBALL="grafana-${GRAFANA_VERSION}.${PLATFORM}.tar.gz"
        GRAFANA_URL="https://dl.grafana.com/oss/release/${GRAFANA_TARBALL}"

        log "Downloading Grafana v${GRAFANA_VERSION} for ${PLATFORM}..."
        log "  URL: ${GRAFANA_URL}"
        download_file "$GRAFANA_URL" "$GRAFANA_DIR/$GRAFANA_TARBALL"

        log "Extracting..."
        tar -xzf "$GRAFANA_DIR/$GRAFANA_TARBALL" -C "$GRAFANA_DIR" --strip-components=1
        rm -f "$GRAFANA_DIR/$GRAFANA_TARBALL"
        ok "Grafana downloaded"
    fi

    GRAFANA_HOME="$GRAFANA_DIR"
    GRAFANA_SERVER="$GRAFANA_HOME/bin/grafana"
    if [ ! -f "$GRAFANA_SERVER" ]; then
        GRAFANA_SERVER="$GRAFANA_HOME/bin/grafana-server"
    fi

    if [ ! -f "$GRAFANA_SERVER" ]; then
        err "Grafana binary not found in $GRAFANA_HOME/bin/"
        ls -la "$GRAFANA_HOME/bin/" 2>/dev/null || true
        exit 1
    fi

    # Grafana needs a data dir and provisioning
    GRAFANA_DATA="$SCRIPT_DIR/.grafana-data"
    mkdir -p "$GRAFANA_DATA/plugins"

    log "Starting Grafana with Jaeger datasource..."
    GF_PATHS_DATA="$GRAFANA_DATA" \
    GF_PATHS_LOGS="$GRAFANA_DATA/log" \
    GF_PATHS_PLUGINS="$GRAFANA_DATA/plugins" \
    GF_PATHS_PROVISIONING="$SCRIPT_DIR/grafana-provisioning" \
    GF_SERVER_HTTP_PORT=3000 \
    GF_SECURITY_ADMIN_USER=admin \
    GF_SECURITY_ADMIN_PASSWORD=admin \
    GF_AUTH_ANONYMOUS_ENABLED=true \
    GF_AUTH_ANONYMOUS_ORG_ROLE=Admin \
    GF_AUTH_DISABLE_LOGIN_FORM=false \
    GF_LOG_LEVEL=warn \
    "$GRAFANA_SERVER" server \
        --homepath "$GRAFANA_HOME" \
        --config "$GRAFANA_HOME/conf/defaults.ini" \
        >"$GRAFANA_DATA/grafana.log" 2>&1 &
    GRAFANA_PID=$!

    log "Waiting for Grafana to start (PID $GRAFANA_PID)..."
    for i in $(seq 1 30); do
        if curl -sf http://localhost:3000/api/health >/dev/null 2>&1; then break; fi
        if ! kill -0 "$GRAFANA_PID" 2>/dev/null; then
            err "Grafana died. Logs:"
            tail -20 "$GRAFANA_DATA/grafana.log" 2>/dev/null
            exit 1
        fi
        sleep 1
    done

    if curl -sf http://localhost:3000/api/health >/dev/null 2>&1; then
        ok "Grafana running at http://localhost:3000 (PID $GRAFANA_PID)"
        ok "  → Jaeger datasource auto-provisioned"
        ok "  → Anonymous access enabled (no login required)"
    else
        err "Grafana did not start within 30 seconds"
        tail -20 "$GRAFANA_DATA/grafana.log" 2>/dev/null
        exit 1
    fi
fi

# ============================================================================
# Step 3: Start Valkey with otelmodule
# ============================================================================

echo ""
log "━━━ Step 3: Starting Valkey with otelmodule ━━━"

if "$VALKEY_CLI" -p "$VALKEY_PORT" PING >/dev/null 2>&1; then
    warn "Valkey already running on port $VALKEY_PORT, reusing it"
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

    log "Waiting for Valkey to start (port $VALKEY_PORT)..."
    for i in $(seq 1 30); do
        if "$VALKEY_CLI" -p "$VALKEY_PORT" PING >/dev/null 2>&1; then break; fi
        sleep 0.5
    done

    if "$VALKEY_CLI" -p "$VALKEY_PORT" PING >/dev/null 2>&1; then
        ok "Valkey running on port $VALKEY_PORT (PID $VALKEY_PID)"
    else
        err "Valkey failed to start"; exit 1
    fi
fi

MODULE_INFO=$("$VALKEY_CLI" -p "$VALKEY_PORT" MODULE LIST 2>&1)
if echo "$MODULE_INFO" | grep -qi "otel"; then
    ok "otelmodule loaded successfully"
else
    err "otelmodule not found in MODULE LIST"; echo "$MODULE_INFO"; exit 1
fi

# ============================================================================
# Step 4: Setup Python venv
# ============================================================================

echo ""
log "━━━ Step 4: Setting up Python environment ━━━"

if [ ! -d "$VENV_DIR" ]; then
    python3 -m venv "$VENV_DIR"
fi
# shellcheck disable=SC1091
source "$VENV_DIR/bin/activate"

pip install -q \
    opentelemetry-api \
    opentelemetry-sdk \
    opentelemetry-exporter-otlp-proto-http 2>&1 | tail -1
ok "Python dependencies installed"

# ============================================================================
# Step 5: Run the demo
# ============================================================================

echo ""
log "━━━ Step 5: Running OpenTelemetry demo ━━━"

cd "$SCRIPT_DIR"
python3 demo.py --port "$VALKEY_PORT" --jaeger-endpoint http://localhost:4318

# ============================================================================
# Step 6: Open Grafana Explore
# ============================================================================

echo ""
log "━━━ Step 6: Opening Grafana ━━━"

# Simple Explore URL that opens Jaeger datasource - user clicks "Run query" to search
GRAFANA_URL="http://localhost:3000/explore?orgId=1&left=%7B%22datasource%22:%22jaeger%22,%22queries%22:%5B%7B%22refId%22:%22A%22,%22datasource%22:%7B%22type%22:%22jaeger%22,%22uid%22:%22jaeger%22%7D,%22queryType%22:%22search%22,%22service%22:%22valkey-otel-demo%22,%22limit%22:20%7D%5D%7D"

if command -v open &>/dev/null; then
    open "$GRAFANA_URL"
    ok "Opened Grafana Explore in browser"
elif command -v xdg-open &>/dev/null; then
    xdg-open "$GRAFANA_URL"
    ok "Opened Grafana Explore in browser"
else
    log "Open this URL in your browser: $GRAFANA_URL"
fi

echo ""
log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
log "Demo is running. Press Ctrl+C to stop."
log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
log "Open in browser:"
log "  Grafana:  http://localhost:3000/explore  (no login required)"
log "  Jaeger:   http://localhost:16686"
echo ""
log "Useful commands:"
log "  $VALKEY_CLI -p $VALKEY_PORT --resp4 --header traceparent=00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01 SET test hello"
log "  $VALKEY_CLI -p $VALKEY_PORT OTEL.STATS"
log "  $VALKEY_CLI -p $VALKEY_PORT OTEL.EVENTS 10"
log "  $VALKEY_CLI -p $VALKEY_PORT COMMANDLOG GET 5"
echo ""

# Keep running until Ctrl+C — wait on Grafana (the primary UI)
# If Grafana exits, we clean up. If user presses Ctrl+C, trap handles it.
log "All services running. Waiting..."
while true; do
    # Check if any critical process died
    if [ -n "${GRAFANA_PID:-}" ] && ! kill -0 "$GRAFANA_PID" 2>/dev/null; then
        warn "Grafana exited"
        break
    fi
    if [ -n "${JAEGER_PID:-}" ] && ! kill -0 "$JAEGER_PID" 2>/dev/null; then
        warn "Jaeger exited"
        break
    fi
    sleep 2
done
