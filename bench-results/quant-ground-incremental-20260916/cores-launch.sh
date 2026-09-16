#!/usr/bin/env bash
# QUANT-GROUND-INCREMENTAL (ADR-2124) -- launch the 53-core probe, both arms,
# interleaved PER FILE on four pinned physical cores of s6.
#
#   cores-launch.sh <list> <outdir> <bin> [budget_s]
#
# INTERLEAVED PER FILE, not arm-after-arm.  The two arms of one file run back to
# back on the SAME core, so whatever load the box carries during that pair
# cancels in the difference.  Running all of OFF and then all of ON puts the two
# arms in different load regimes and has moved 23 verdicts on a fixed binary.
# `cores-run.sh` runs one shard and does both arms of a file before moving on.
#
# ONE BINARY, TWO ENV VALUES.  The lever ships at 0, so the OFF arm is the
# shipped configuration of the very binary under test and the comparison has no
# second build in it.
set -u
LIST="$1"; OUT="$2"; AX="$3"; BUDGET="${4:-24}"
PINS=(1,9 3,11 5,13 6,14)
N=${#PINS[@]}

mkdir -p "$OUT/raw"
for i in $(seq 0 $((N - 1))); do
  rm -f "$OUT/shard$i.off.progress" "$OUT/shard$i.on.progress"
done

HERE="$(cd "$(dirname "$0")" && pwd)"
for i in $(seq 0 $((N - 1))); do
  nohup setsid bash "$HERE/cores-pair.sh" \
    "$LIST" "$OUT" "${PINS[$i]}" "$AX" "$i" "$N" "$BUDGET" \
    > "$OUT/shard$i.log" 2>&1 &
done
echo "launched $N shards on ${PINS[*]}"
