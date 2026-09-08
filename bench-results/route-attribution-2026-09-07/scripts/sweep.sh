#!/usr/bin/env bash
# Drives run_division.sh across all 12 parity divisions.
#
# Divisions run in PARALLEL (one process per division, 12 of 16 cores), files
# within a division serially. That split is deliberate: `wall_ms` and the
# `bound_ms` / `total_ms` trace fields are load-sensitive, and running 12
# single-threaded solves on a 16-core idle box keeps each one on its own core
# rather than contending. Even so, the timing columns from this run are
# COMPARABLE WITHIN a run and should not be compared against a differently
# loaded one -- the same reference-frame caveat the frontier ratchet carries.
#
# The DECIDING-ROUTE column is not load-sensitive at all (dispatch order is
# deterministic), so the virtual-best-over-our-own-routes analysis, which is
# what this sweep exists for, is unaffected by the parallelism.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT="$(cd "$HERE/.." && pwd)"
BIN="${BIN:-$OUT/../../target/release/examples/smtcomp_cli}"
LISTS="${LISTS:-$OUT/../parity-lists}"
N="${N:-100}"
BUDGET_S="${BUDGET_S:-10}"

DIVS="QF_ABV QF_BV QF_IDL QF_LIA QF_LRA QF_NIA QF_NRA QF_RDL QF_SLIA QF_UF QF_UFLIA UF"

pids=""
for div in $DIVS; do
  bash "$HERE/run_division.sh" "$div" "$LISTS/$div.txt" "$BIN" \
    "$OUT/$div.tsv" "$OUT/logs" "$N" "$BUDGET_S" &
  pids="$pids $!"
done

fail=0
for p in $pids; do
  wait "$p" || fail=1
done

echo "sweep complete (fail=$fail)" >&2
exit "$fail"
