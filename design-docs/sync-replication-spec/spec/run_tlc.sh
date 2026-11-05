#!/usr/bin/env bash
# Usage: ./run_tlc.sh [cfg...]   (default: every *.cfg here)
# The module is the cfg name up to its first "_" (SyncCommit_safe.cfg -> SyncCommit.tla).
# Needs Java 11+. Uses ../tools/tla2tools.jar unless TLA2TOOLS is set.
set -u
cd "$(dirname "$0")"
JAR="${TLA2TOOLS:-$(cd .. && pwd)/tools/tla2tools.jar}"
cfgs=("$@"); [ ${#cfgs[@]} -eq 0 ] && cfgs=(*.cfg)
mkdir -p results
for c in "${cfgs[@]}"; do
  name="${c%.cfg}"; mod="${name%%_*}"
  out="results/$name.out"
  md="${TMPDIR:-/tmp}/tlc-$name-$$"
  # Refuse to start with less than 20 GB free: TLC state dirs grow fast.
  avail=$(df -Pk "${TMPDIR:-/tmp}" | awk 'NR==2{print $4}')
  if [ "$avail" -lt 20971520 ]; then echo "$c: SKIPPED, less than 20 GB free"; continue; fi
  java -XX:+UseParallelGC -cp "$JAR" tlc2.TLC -config "$c" -workers auto -deadlock \
       -metadir "$md" "$mod.tla" > "$out" 2>&1
  rm -rf "$md"
  verdict=$(grep -m1 -E "No error has been found|is violated|Error:" "$out")
  states=$(grep -E "^[0-9,]+ states generated" "$out" | tail -1 | sed "s/ states left on queue.*//")
  printf '%-42s %s | %s\n' "$c" "$verdict" "$states"
done
