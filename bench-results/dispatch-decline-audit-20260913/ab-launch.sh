#!/usr/bin/env bash
# Launch the ADR-1966 A/B over the treatment and control divisions, one pinned
# core each.
#
# The division split is NOT a guess: `hit-rate.py` measured, per pinned list,
# how many files carry the shape the changed rung needs.
#
#   TREATMENT -- files that can reach the refusal
#     AUFLIRA   184/200 array-valued UF + arithmetic UF
#     AUFNIRA   132/200
#     AUFDTLIRA  54/200
#
#   CONTROL -- the SAME rung runs, but nothing in the division can refuse it
#     QF_UFLIA  194/200 arithmetic UF, 0 array-valued
#     UFLIA     200/200 arithmetic UF, 0 array-valued
#
#   A control that could not reach the route would prove nothing about cost.
#   These reach it on 97% and 100% of their files and cannot trigger the guard,
#   which is exactly the shape a cost control needs.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
BIN=/data0/axeyum/dispatch-decline-audit-bin
OUT="${1:-/data0/axeyum/dispatch-decline-audit-ab}"
mkdir -p "$OUT"

i=0
for d in AUFLIRA AUFNIRA AUFDTLIRA QF_UFLIA UFLIA; do
  BUDGET="${BUDGET:-10}" "$HERE/ab-run.sh" "$BIN/base" "$BIN/fix" "$d" \
    "$HERE/../parity-lists/$d.txt" "$OUT/$d.tsv" "$i" > "$OUT/$d.log" 2>&1 &
  i=$((i + 1))
done
wait
echo "AB-LAUNCH-DONE"
