#!/usr/bin/env bash
# Drive the ADR-2131 A/B on the sweep host.
#
# Four divisions, four shards each, one shard per pinned core (s5 physical core
# pairs 1/9 and 3/11), 24 s wall and 8 GiB `ulimit -v`, divisions SERIAL so the
# four cores carry one division at a time and an interleaved pair never has
# another division's shard beside it.
#
# The arms, and why these two:
#
#   A = `AXEYUM_NRA_CAD` set and EMPTY. `parse_cad_arm("")` is `CAD_DEFAULT`,
#       which ADR-2126 moved to `CadPolicy::SINGLE_CELL` -- so arm A is THE
#       SHIPPED DEFAULT, and its score reproducing the sizing pass is the control
#       on the whole measurement.
#   B = `clause-loop`. ADR-2131 REBASED that arm onto `SINGLE_CELL`, so the two
#       now differ in EXACTLY `clause_loop`. Before the rebase they also differed
#       in `emit_unsat`, and every verdict the single-cell route's `unsat` half
#       contributes would have read as a loss caused by the loop -- a confounded
#       A/B that prints a clean number.
#       `the_single_cell_arm_differs_in_exactly_the_route` is what holds it, and
#       it reads the comparison arm out of `CAD_DEFAULT` rather than naming it,
#       so repointing the default without rebasing the arm fails the test.
#
# QF_NRA is the target division. QF_NIA shares the nonlinear code, so a
# regression there is the one a QF_NRA-only sweep would miss. QF_LRA is the
# CONTROL: nothing linear goes near this route, so a mover there is a finding
# about the harness and not about the lever. The held-out QF_NRA draw is
# ADR-2126's, reused with its own seed and checked disjoint from the pinned one.
#
# Usage: ab-launch.sh <dir-on-the-sweep-host> [tag]
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
TAG="${1:-clauseloop}"
BIN=/nas3/data/axeyum/lanes/nra-clause-loop/smtcomp_cli
CORES=(1 9 3 11)

[ -x "$BIN" ] || { echo "ab-launch: $BIN is not executable" >&2; exit 2; }
sha256sum "$BIN" > "$HERE/ab-$TAG-binary-sha256.txt"

for div in qfnra qfnia qflra qfnraheldout; do
  echo "=== $div ===" >&2
  pids=()
  for i in 0 1 2 3; do
    "$HERE/ab-run.sh" \
      --list "$HERE/shard$i-$div.txt" \
      --out "$HERE/ab-$TAG-$div-shard$i.tsv" \
      --shard "$i" --core "${CORES[$i]}" \
      --binary "$BIN" --arm-b clause-loop --budget-s 24 \
      > "$HERE/ab-$TAG-$div-shard$i.log" 2>&1 &
    pids+=($!)
  done
  rc=0
  for p in "${pids[@]}"; do wait "$p" || rc=1; done
  echo "=== $div done (rc=$rc) ===" >&2
done
echo "AB_SWEEP_COMPLETE" > "$HERE/ab-$TAG.done"
echo "ab-launch: complete" >&2
