#!/usr/bin/env bash
# DT-QUANT-TRACE -- stage this lane's scripts to /nas3 and shard a sweep across
# this lane's four pinned PHYSICAL core pairs on s7.
#
#   launch.sh <tag> <runner> <list> [budget_s] [extra args to the runner...]
#
# `runner` is a script name in this directory (`ax-trace.sh`, `ref-trace.sh`).
#
# Pinned cores are 1 3 5 6 -- one thread of each of this lane's four physical
# pairs (1,9 / 3,11 / 5,13 / 6,14), never both threads of a pair. Sharing a
# physical core with yourself is the contention that moves these numbers most,
# and CLAUDE.md records the same sweep reading 35 / 39 / 40 on one commit
# purely from load.
#
# `nohup setsid` and NOT a foreground wait: CLAUDE.md records the harness
# killing background tasks under memory pressure, and a `timeout` returning is
# not the process ending. The caller watches the ARTIFACT.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
TAG="$1"; RUNNER="$2"; LIST="$3"; BUDGET="${4:-24}"
shift 4 2>/dev/null || shift 3
HOST="${DT_HOST:-s7}"
STAGE=/nas3/data/axeyum/harness/dt-quant-trace/stage
AX="${DT_AX:-/nas3/data/axeyum/harness/dt-quant-trace/bin/smtcomp_cli-base}"
CORES="${DT_CORES:-1 3 5 6}"

mkdir -p "$STAGE"
cp "$HERE/$RUNNER" "$HERE/dtshape.py" "$STAGE/"
cp "$LIST" "$STAGE/$TAG.list"

# Shard round-robin, NOT by contiguous block: these lists are path-sorted, and
# a contiguous shard is a prefix of a sorted list -- CLAUDE.md's "never read a
# prefix of a sorted benchmark list", which published two false nulls.
i=0
for c in $CORES; do
  awk -v n="$(echo "$CORES" | wc -w)" -v k="$i" 'NR % n == k' "$STAGE/$TAG.list" \
    > "$STAGE/$TAG.shard$i.list"
  i=$((i + 1))
done

i=0
for c in $CORES; do
  ssh "$HOST" "nohup setsid $STAGE/$RUNNER $STAGE/$TAG.shard$i.list \
    $STAGE/$TAG.shard$i.tsv $c $AX $BUDGET $* \
    > $STAGE/$TAG.shard$i.log 2>&1 < /dev/null &" || true
  i=$((i + 1))
done
echo "$TAG: launched $i shards on $HOST cores [$CORES]; artifacts $STAGE/$TAG.shard*.tsv"
