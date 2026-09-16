#!/usr/bin/env bash
# DT-FIELD-EXPANSION -- shard one division's interleaved A/B across this lane's
# two pinned physical core pairs on s7, DIVISIONS SERIAL.
#
#   ab-launch.sh <division> [budget_s] [depth]
#
# Divisions are run SERIALLY (one call per division, waited on) rather than all
# at once: three divisions on two cores would put three jobs on two cores and
# the interleaving that makes the A/B honest only cancels load that BOTH arms
# of one file see.
#
# Cores 5 and 6 -- one thread of each of this lane's physical pairs (5,13 /
# 6,14), never both threads of a pair.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
DIV="$1"; BUDGET="${2:-24}"; DEPTH="${3:-5}"
HOST="${DTFE_HOST:-s7}"
STAGE=/nas3/data/axeyum/harness/dt-field-expansion/stage
AX="${DTFE_AX:-/nas3/data/axeyum/harness/dt-field-expansion/bin/smtcomp_cli-arm}"
CORES="${DTFE_CORES:-5 6}"

mkdir -p "$STAGE"
cp "$HERE/ab-run.sh" "$STAGE/"
cp "$HERE/lists/ab-$DIV.paths" "$STAGE/ab-$DIV.list"

# Round-robin, NOT a contiguous block: these lists are path-sorted and a
# contiguous shard is a prefix of a sorted list.
i=0
n=$(echo "$CORES" | wc -w)
for c in $CORES; do
  awk -v n="$n" -v k="$i" 'NR % n == k' "$STAGE/ab-$DIV.list" \
    > "$STAGE/ab-$DIV.shard$i.list"
  i=$((i + 1))
done

i=0
for c in $CORES; do
  ssh "$HOST" "nohup setsid $STAGE/ab-run.sh $STAGE/ab-$DIV.shard$i.list \
    $STAGE/ab-$DIV.shard$i.tsv $c $AX $BUDGET $DEPTH \
    > $STAGE/ab-$DIV.shard$i.log 2>&1 < /dev/null &" || true
  i=$((i + 1))
done
echo "ab-$DIV: launched $i shards on $HOST cores [$CORES] depth=$DEPTH budget=${BUDGET}s"
