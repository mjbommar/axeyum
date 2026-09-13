#!/usr/bin/env bash
# The interleaved per-file A/B for ADR-1960.
#
# One shard per division, each pinned to its own physical core, running the two
# axeyum binaries BACK TO BACK ON ONE FILE before either moves on. That
# interleave is the point: at a 24 s budget roughly 1-1.5% of files flip on
# ambient load alone, and load only cancels in the difference when the two arms
# see the same load on the same file (`interleave the arms per file`).
#
# Divisions:
#   AUFLIRA AUFNIRA — the two Real divisions this change targets
#   ALIA ABV        — the same array families with NO Real: the change must not
#                     move these, and if it does the cause is not the Real gate
#   QF_ABV QF_BV    — divisions we already decide ~93% of: the regression
#                     control, where any loss is visible against a high floor
#
# Usage: ab.sh <arm-A-binary> <arm-B-binary> <out-dir> [division...]
set -eu
AX_A="${1:?usage: ab.sh <arm-A-binary> <arm-B-binary> <out-dir> [division...]}"
AX_B="${2:?usage: ab.sh <arm-A-binary> <arm-B-binary> <out-dir> [division...]}"
OUT="${3:?usage: ab.sh <arm-A-binary> <arm-B-binary> <out-dir> [division...]}"
shift 3
DIVS="${*:-AUFLIRA AUFNIRA ALIA ABV QF_ABV QF_BV}"
LANE="$(cd "$(dirname "$0")" && pwd)"
SHARD="$LANE/../nested-array-ir-20260913/shard-run.sh"

[ -x "$AX_A" ] || { echo "ABORT: arm A '$AX_A' is not executable"; exit 2; }
[ -x "$AX_B" ] || { echo "ABORT: arm B '$AX_B' is not executable"; exit 2; }
[ -x "$SHARD" ] || { echo "ABORT: $SHARD missing"; exit 2; }

mkdir -p "$OUT"
core=0
pids=""
for d in $DIVS; do
  list="$LANE/../parity-lists/$d.txt"
  [ -s "$list" ] || { echo "ABORT: $list missing or empty"; exit 2; }
  AX_BIN="$AX_A" AX_BIN_B="$AX_B" ARMS="axeyum axeyumb" \
    "$SHARD" "$d" "$list" "$OUT/$d.tsv" "$core" > "$OUT/$d.log" 2>&1 &
  pids="$pids $!"
  core=$((core + 1))
done
echo "launched:$pids"
wait
echo "ALL-SHARDS-DONE"
