#!/usr/bin/env bash
# Launches ADR-2112's interleaved one-binary A/B across three divisions.
#
# A = AXEYUM_INT_BLAST_WIDTH_FLOOR=0 (shipped, floor disarmed)
# B = AXEYUM_INT_BLAST_WIDTH_FLOOR=1 (floor armed)
#
# One shard per PHYSICAL core, and only one sibling of each hyperthread pair:
# this lane owns s6 pairs (1,9) and (3,11), so the shards run on 1 and 3 and
# leave 9 and 11 idle. Running both siblings would halve each shard's
# throughput and put the two arms of DIFFERENT files on one physical core,
# which is the contention the interleaving exists to cancel.
#
# Divisions run SERIALLY within a shard. `QF_NRA` is a CONTROL, not a target:
# the floor sits in `dispatch_int_blast_width_ladder`, which a Real-sorted
# query should not reach, so anything but zero movement there is a finding
# about reach and not about the lever. `UFNIA` is included because
# `q:skolem-qf` hands off to the whole quantifier-free ladder and therefore
# does reach the integer tail (ADR-2106 measured losses there).
#
# usage: launch-ab.sh <axeyum-binary> <outdir> [budget_s]
set -uo pipefail

AX=${1:?axeyum binary}
OUTDIR=${2:?output directory}
BUDGET=${3:-24}
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
RUNNER=$HERE/ab-run-floor.sh

[ -x "$AX" ] || { echo "ABORT: $AX is not executable"; exit 2; }
[ -x "$RUNNER" ] || { echo "ABORT: $RUNNER is not executable"; exit 2; }
mkdir -p "$OUTDIR"

# Divisions split across the two shards so each shard carries comparable work,
# and so a shard dying does not take a whole division with it.
shard_one=(QF_NIA UFNIA)
shard_two=(QF_NRA)

run_shard() {
    local core=$1; shift
    for division in "$@"; do
        local list=$HERE/ab-list-$division.txt
        local out=$OUTDIR/ab-$division.tsv
        [ -s "$list" ] || { echo "ABORT core $core: $list missing or empty"; return 2; }
        "$RUNNER" "$division" "$list" "$out" "$core" "$AX" 0 1 "$BUDGET"
    done
    echo "SHARD-DONE core $core"
}

run_shard 1 "${shard_one[@]}" &
one=$!
run_shard 3 "${shard_two[@]}" &
two=$!
wait "$one"; rc_one=$?
wait "$two"; rc_two=$?
echo "LAUNCH-DONE shard1=$rc_one shard3=$rc_two out=$OUTDIR"
