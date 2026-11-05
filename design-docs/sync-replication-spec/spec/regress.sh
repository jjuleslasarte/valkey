#!/usr/bin/env bash
# Regression runner.
#
# Usage: regress.sh [TIER] [OUT]
#   TIER  ci (default) or large or all
#   OUT   results file to write (default results/regress.tsv)
#
# Reads expected.tsv (tab-separated: cfg, tier, expected outcome), runs every
# config in the tier, classifies the outcome and compares it with the
# expected one. Outcomes:
#   pass                 TLC completed with no error
#   violated:<Name>      an invariant or property <Name> was violated
#   error                any other TLC error (parse, semantic, exception)
#   timeout              the per-config time limit was reached
#   skipped:disk         not enough free disk to start
# An expected outcome of "?" is recorded but not compared.
#
# Environment: EXPECTED (expectations file, default expected.tsv),
#              TIMEOUT (seconds per config, default 240),
#              MINFREE_GB (default 2; the run is stopped below it),
#              COVERAGE=1 (dead-action gate, see below).
#
# Dead-action gate (COVERAGE=1): for every config whose outcome is "pass",
# TLC runs with -coverage and the actions that generated no state are listed.
# They must equal the allowlist in coverage.tsv (cfg, then a comma-separated
# list of actions that are switched off in that config). A config that is
# missing from coverage.tsv is reported as "coverage:new" with its list, so
# the list can be reviewed and added. An action that never fires in a
# passing run usually means the run proved nothing about it.
set -u
cd "$(dirname "$0")"
TIER=${1:-ci}; OUT=${2:-results/regress.tsv}
TIMEOUT=${TIMEOUT:-240}; MINFREE_GB=${MINFREE_GB:-2}
JAR="$(cd .. && pwd)/tools/tla2tools.jar"
mkdir -p results traces
: > "$OUT"
fail=0; n=0
minkb=$((MINFREE_GB * 1024 * 1024))

classify() {  # $1 = TLC output file
  local f=$1 v
  if grep -q "Model checking completed. No error has been found" "$f"; then echo pass; return; fi
  v=$(grep -m1 -oE "(Invariant|Action property|Temporal properties were) [A-Za-z0-9_]+ (is|are) violated" "$f" | awk '{print $(NF-2)}')
  [ -z "$v" ] && v=$(grep -m1 -oE "Invariant [A-Za-z0-9_]+ is violated|property [A-Za-z0-9_]+ is violated" "$f" | awk '{print $2}')
  if [ -n "$v" ]; then echo "violated:$v"; return; fi
  if grep -q "Action property line" "$f"; then echo "violated:Refinement"; return; fi
  if grep -qE "Temporal properties were violated" "$f"; then echo "violated:Liveness"; return; fi
  echo error
}

while IFS=$'\t' read -r cfg tier expected; do
  case "$cfg" in ''|\#*) continue;; esac
  [ "$TIER" != all ] && [ "$tier" != "$TIER" ] && continue
  n=$((n + 1))
  name=${cfg%.cfg}; mod=${name%%_*}; out="results/$name.out"
  md="${TMPDIR:-/tmp}/tlc-$name-$$"
  avail=$(df -Pk "${TMPDIR:-/tmp}" | awk 'NR==2{print $4}')
  if [ "$avail" -lt "$minkb" ]; then got="skipped:disk"
  else
    cov=""; [ "${COVERAGE:-0}" = 1 ] && [ "$expected" = pass ] && cov="-coverage 60"
    timeout "$TIMEOUT" java -XX:+UseParallelGC -cp "$JAR" tlc2.TLC -config "$cfg" \
        -workers auto -deadlock $cov -metadir "$md" "$mod.tla" > "$out" 2>&1 &
    pid=$!; why=""
    while kill -0 $pid 2>/dev/null; do
      sleep 2
      avail=$(df -Pk "${TMPDIR:-/tmp}" | awk 'NR==2{print $4}')
      if [ "$avail" -lt "$minkb" ]; then why=disk; kill $pid 2>/dev/null; fi
    done
    wait $pid; rc=$?
    find "$md" -delete 2>/dev/null
    mv -f ${mod}_TTrace_*.tla traces/ 2>/dev/null
    if [ -n "$why" ]; then got="skipped:disk"
    elif [ $rc -eq 124 ]; then got=timeout
    else got=$(classify "$out"); fi
  fi
  mark=ok
  if [ "$expected" != "?" ] && [ "$got" != "$expected" ]; then mark=MISMATCH; fail=$((fail + 1)); fi
  if [ "${COVERAGE:-0}" = 1 ] && [ "$got" = pass ]; then
    # Last coverage block only; action lines look like "<Name line ...>: 0:0".
    zero=$(awk '/The coverage statistics/{blk=""} /^<[A-Za-z_][A-Za-z0-9_]* line [0-9]+, col.*>: [0-9]+:[0-9]+$/{blk=blk"\n"$0} END{print blk}' "$out" \
           | grep -E ': 0:0$' | sed -E 's/^<([A-Za-z0-9_]+) .*/\1/' | sort -u | paste -sd, -)
    allowed=$(awk -F'\t' -v c="$cfg" '$1==c{print $2}' coverage.tsv 2>/dev/null)
    if ! grep -q "^$cfg	" coverage.tsv 2>/dev/null; then
      mark="$mark coverage:new[$zero]"
    elif [ "$zero" != "$allowed" ]; then
      mark="$mark coverage:MISMATCH[got=$zero allowed=$allowed]"; fail=$((fail + 1))
    fi
  fi
  printf '%s\t%s\t%s\t%s\n' "$cfg" "$expected" "$got" "$mark" | tee -a "$OUT"
done < "${EXPECTED:-expected.tsv}"

echo "ran $n configs, $fail mismatches"
[ $fail -eq 0 ]
