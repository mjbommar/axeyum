#!/usr/bin/env bash
# Drive the ADR-2126 A/B over three divisions, four shards each, one shard per
# pinned core.
#
# The two arms, and why they are these two:
#
#   A = the env var SET and EMPTY. `parse_cad_arm("")` is `CAD_DEFAULT`, which
#       ADR-2121 moved to `CadPolicy::SINGLE_CELL_SAT` -- so arm A is THE SHIPPED
#       DEFAULT, not the pre-route engine. A baseline arm that reproduces the
#       board is the control on the whole measurement.
#   B = `single-cell`, the full arm. The two differ in EXACTLY `emit_unsat`
#       (ADR-2121 decision 1), so this A/B prices the route's `unsat` half ALONE
#       -- which is precisely the half ADR-2121 withheld, and precisely the half
#       ADR-2126's exact delineability check exists to make shippable.
#
# The binary is the same for both arms and its sha256 is recorded beside the
# results, because "one binary, two env values" is a claim and not a convention.
#
# QF_NRA is the target division. QF_NIA shares the nonlinear code, so a
# regression there is the one a QF_NRA-only sweep would miss. QF_LRA is the
# CONTROL: nothing linear goes anywhere near this route, so a mover there is a
# finding about the harness and not about the lever, and `ab-report.py` exits
# non-zero when it moves.
#
# Divisions run in sequence and shards in parallel, so the four cores carry one
# division at a time and the interleaved pairs stay on the same core.
#
# Usage: ab-sweep.sh /path/to/smtcomp_cli [arm-b] [tag]
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
BIN="${1:?usage: ab-sweep.sh /path/to/smtcomp_cli [arm-b] [tag]}"
ARM_B="${2:-single-cell}"
TAG="${3:-$ARM_B}"
CORES=(1 9 3 11)

sha256sum "$BIN" > "$HERE/ab-$TAG-binary-sha256.txt"

for div in qfnra qfnia qflra; do
  echo "=== $div ===" >&2
  pids=()
  for i in 0 1 2 3; do
    "$HERE/ab-run.sh" \
      --list "$HERE/shard$i-$div.txt" \
      --out "$HERE/ab-$TAG-$div-shard$i.tsv" \
      --shard "$i" --core "${CORES[$i]}" \
      --binary "$BIN" --arm-b "$ARM_B" --budget-s 24 \
      > "$HERE/ab-$TAG-$div-shard$i.log" 2>&1 &
    pids+=($!)
  done
  rc=0
  for p in "${pids[@]}"; do wait "$p" || rc=1; done
  echo "=== $div done (rc=$rc) ===" >&2
done
echo "ab-sweep: complete" >&2
