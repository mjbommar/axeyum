#!/usr/bin/env bash
# QUANT-SESSION-ARITH (ADR-2130) -- launch the 53-core probe, both arms,
# interleaved PER FILE on four pinned physical core pairs.
#
#   cores-launch.sh <list> <outdir> <bin> <on_level> [budget_s]
#
# `on_level` is the value of AXEYUM_QINST_GROUND_SESSION the ON arm uses: `2`
# for this lane (hosting), `1` for ADR-2124's abstraction arm.  Both are worth
# running: `2` against the SHIPPED arm is the ship question, and `2` against `1`
# is what isolates hosting from the schedule change ADR-2124 already measured.
set -u
LIST="$1"; OUT="$2"; AX="$3"; ON_LEVEL="$4"; BUDGET="${5:-24}"
PINS=(1,9 3,11 5,13 6,14)
N=${#PINS[@]}

mkdir -p "$OUT/raw"
for i in $(seq 0 $((N - 1))); do
  rm -f "$OUT/shard$i.off.progress" "$OUT/shard$i.on.progress"
done

HERE="$(cd "$(dirname "$0")" && pwd)"
for i in $(seq 0 $((N - 1))); do
  nohup setsid bash "$HERE/cores-pair.sh" \
    "$LIST" "$OUT" "${PINS[$i]}" "$AX" "$i" "$N" "$ON_LEVEL" "$BUDGET" \
    > "$OUT/shard$i.log" 2>&1 &
done
echo "launched $N shards on ${PINS[*]} at ON=$ON_LEVEL budget=${BUDGET}s"
