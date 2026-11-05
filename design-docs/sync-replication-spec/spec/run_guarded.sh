#!/usr/bin/env bash
# Usage: run_guarded.sh MAXSECONDS cfg...
# Like run_tlc.sh, but kills TLC if free disk drops below 20 GB or the time
# limit passes, and always removes the TLC state directory.
cd "$(dirname "$0")"
LIMIT=$1; shift
JAR="$(cd .. && pwd)/tools/tla2tools.jar"
mkdir -p results
for c in "$@"; do
  name="${c%.cfg}"; mod="${name%%_*}"; out="results/$name.out"
  md="${TMPDIR:-/tmp}/tlc-$name-$$"
  mode=""; [ -n "${SIM:-}" ] && mode="-simulate num=${SIMN:-100000000} -depth $SIM"
  java -XX:+UseParallelGC -cp "$JAR" tlc2.TLC -config "$c" -workers auto -deadlock $mode \
       -metadir "$md" "$mod.tla" > "$out" 2>&1 &
  pid=$!; start=$(date +%s); why=""
  while kill -0 $pid 2>/dev/null; do
    sleep 10
    avail=$(df -Pk "${TMPDIR:-/tmp}" | awk 'NR==2{print $4}')
    if [ "$avail" -lt 20971520 ]; then why="disk"; kill $pid; fi
    if [ $(( $(date +%s) - start )) -gt "$LIMIT" ]; then why="time"; kill $pid; fi
  done
  wait $pid 2>/dev/null
  rm -rf "$md"
  verdict=$(grep -m1 -E "No error has been found|is violated|^Error:" "$out")
  [ -n "${SIM:-}" ] && [ -z "$verdict" ] && verdict="no violation in simulation"
  states=$(grep -E "states generated" "$out" | tail -1 | sed "s/ states left on queue.*//" | sed 's/^Progress.*: //')
  [ -n "$why" ] && verdict="STOPPED ($why limit)"
  printf '%-40s %s | %s\n' "$c" "$verdict" "$states"
done
