#!/usr/bin/env bash
# DT-FIELD-EXPANSION -- stage this lane's runner to /nas3 and shard a sweep
# across this lane's two pinned PHYSICAL core pairs on s7.
#
#   launch.sh <tag> <list> [budget_s] [extra env assignments for the runner...]
#
# Pinned cores are 5 and 6 -- ONE thread of each of this lane's two physical
# pairs (5,13 / 6,14), never both threads of a pair.  Sharing a physical core
# with yourself is the contention that moves these numbers most, and CLAUDE.md
# records one sweep reading 35 / 39 / 40 on a single commit purely from load.
#
# `nohup setsid` and NOT a foreground wait: the harness kills background tasks
# under memory pressure, and a `timeout` returning is not the process ending.
# The caller watches the ARTIFACT.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
TAG="$1"; LIST="$2"; BUDGET="${3:-24}"
shift 3 2>/dev/null || shift 2
HOST="${DTFE_HOST:-s7}"
STAGE=/nas3/data/axeyum/harness/dt-field-expansion/stage
AX="${DTFE_AX:-/nas3/data/axeyum/harness/dt-field-expansion/bin/smtcomp_cli-base}"
CORES="${DTFE_CORES:-5 6}"

mkdir -p "$STAGE"
# The runner is [ADR-2114]'s, reused verbatim: it already carries the
# `AXEYUM_QPROBE` channel and the VERBATIM give-up detail, and a second copy of
# a census runner is a second thing to keep in step.
cp "$HERE/../dt-quant-trace-20260915/ax-trace.sh" "$STAGE/"
cp "$LIST" "$STAGE/$TAG.list"

# Shard round-robin, NOT by contiguous block: these lists are path-sorted, and a
# contiguous shard is a prefix of a sorted list -- CLAUDE.md's "never read a
# prefix of a sorted benchmark list", which published two false nulls.
i=0
n=$(echo "$CORES" | wc -w)
for c in $CORES; do
  awk -v n="$n" -v k="$i" 'NR % n == k' "$STAGE/$TAG.list" \
    > "$STAGE/$TAG.shard$i.list"
  i=$((i + 1))
done

i=0
for c in $CORES; do
  ssh "$HOST" "nohup setsid $STAGE/ax-trace.sh $STAGE/$TAG.shard$i.list \
    $STAGE/$TAG.shard$i.tsv $c $AX $BUDGET $* \
    > $STAGE/$TAG.shard$i.log 2>&1 < /dev/null &" || true
  i=$((i + 1))
done
echo "$TAG: launched $i shards on $HOST cores [$CORES]; artifacts $STAGE/$TAG.shard*.tsv"
