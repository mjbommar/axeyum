#!/usr/bin/env bash
# REAL-OPAQUE R7, second half -- does the CHANGED CODE actually execute on the
# control division?
#
# `control-nonvacuity.py` answers "did the zero have room" (93 of 200 undecided)
# and reports which route BOUND each row. It found the binding routes are `nra`
# and `NONE`, not an `lra` one -- so "the edited functions run here" is NOT an
# inference this lane gets to make from the route name. It has to be observed.
#
# The observation: `lra_entries` / `cube_decisions` / `cube_collect_ms` on the
# `lazy-smt` counter line count entries into `lra::decide_within`, which is the
# function this change threads its mode through and whose `nvars` it altered.
# A nonzero count on a control row is direct evidence that the column-space
# refactor ran there and produced the same verdict.
#
# Prints one row per file and a PASS/FAIL whose exit status depends on the
# finding.
#
# Usage: control-executes.sh <bin> <list> [n]
set -u
AX="$1"; LIST="$2"; N="${3:-20}"
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

resolve() { case "$1" in /*) printf '%s' "$1" ;; *) printf '%s/%s' "$CORPUS" "$1" ;; esac; }

hits=0; seen=0
printf '%-72s %10s %10s %12s\n' file lra_entries cube_dec cube_collect_ms
while IFS= read -r f; do
  seen=$((seen + 1))
  [ "$seen" -gt "$N" ] && break
  raw=$(AXEYUM_LAZY_SMT_COUNTERS=1 AXEYUM_TRACE=1 timeout 40 \
          "$AX" "$(resolve "$f")" --timeout-ms 24000 2>&1)
  e=$(printf '%s' "$raw" | grep -oE 'lra_entries=[0-9]+' | head -1 | cut -d= -f2)
  d=$(printf '%s' "$raw" | grep -oE 'cube_decisions=[0-9]+' | head -1 | cut -d= -f2)
  m=$(printf '%s' "$raw" | grep -oE 'cube_collect_ms=[0-9]+' | head -1 | cut -d= -f2)
  e=${e:-0}; d=${d:-0}; m=${m:-0}
  [ "$e" -gt 0 ] || [ "$d" -gt 0 ] && hits=$((hits + 1))
  printf '%-72s %10s %10s %12s\n' "$(basename "$f")" "$e" "$d" "$m"
done < "$LIST"

echo
echo "files probed: $((seen > N ? N : seen))   files where lra::decide_within ran: $hits"
if [ "$hits" -eq 0 ]; then
  echo "FAIL: the changed code does not execute on this division -- the control's"
  echo "      zero is VACUOUS and must not be reported as a control."
  exit 1
fi
echo "PASS: the control exercises the changed code and still moved 0 rows."
