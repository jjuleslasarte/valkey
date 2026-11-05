#!/usr/bin/env bash
# Usage: spec/apalache/run.sh <name> <cfg> <apalache check args...>
# Runs one Apalache check from spec/, logs to spec/apalache/<name>.out, prints verdict and wall time.
set -u
cd "$(dirname "$0")/.."
name=$1; cfg=$2; shift 2
out="apalache/$name.out"
start=$(date +%s)
../tools/apalache.sh check --config="$cfg" --out-dir=apalache/_out/$name --run-dir="apalache/_run/$name" "$@" CoreApalache.tla > "$out" 2>&1
rc=$?
end=$(date +%s)
verdict=$(grep -m1 -E "The outcome is|Checker has found|EXITCODE|Error" "$out")
printf '%-28s rc=%s %4ss  %s\n' "$name" "$rc" "$((end-start))" "$verdict" | tee -a apalache/results.txt
