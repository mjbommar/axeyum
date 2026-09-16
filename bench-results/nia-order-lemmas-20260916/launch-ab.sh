#!/usr/bin/env bash
# Launches ADR-2136's interleaved one-binary A/B across three divisions.
# Lane NIA-ORDER-LEMMAS.
#
# A = AXEYUM_NIA_ORDER_LEMMAS=0 (shipped, the pass disarmed)
# B = AXEYUM_NIA_ORDER_LEMMAS=1 (order + monotonicity lemmas armed)
#
# One shard per PHYSICAL core, and only one sibling of each hyperthread pair:
# this lane owns s6 pairs (5,13) and (6,14), so the shards run on 5 and 6 and
# leave 13 and 14 idle. Running both siblings would halve each shard's
# throughput and put the two arms of DIFFERENT files on one physical core,
# which is the contention the interleaving exists to cancel.
#
# Divisions run SERIALLY within a shard.
#
# `QF_NRA` is a CONTROL and not a target: the lever sits in
# `nia_linearize.rs`'s refinement loop, which is the INTEGER route, so a
# Real-sorted query should not reach it and anything but zero movement there is
# a finding about reach rather than about the lever. `UFNIA` is a target: ADR-2106
# measured losses in `q:skolem-qf`'s hand-off to the quantifier-free ladder, so
# the nonlinear integer tail really is reached from there.
#
# usage: launch-ab.sh <axeyum-binary> <listdir> <outdir> [budget_s]
set -uo pipefail

AX=${1:?axeyum binary}
LISTDIR=${2:?directory holding ab-list-<division>.txt}
OUTDIR=${3:?output directory}
BUDGET=${4:-24}
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
RUNNER=$HERE/ab-run-env.sh

[ -x "$AX" ] || { echo "ABORT: $AX is not executable"; exit 2; }
[ -x "$RUNNER" ] || { echo "ABORT: $RUNNER is not executable"; exit 2; }
mkdir -p "$OUTDIR"

shard_one=(QF_NIA UFNIA)
shard_two=(QF_NRA)

run_shard() {
    local core=$1; shift
    for division in "$@"; do
        local list=$LISTDIR/ab-list-$division.txt
        local out=$OUTDIR/ab-$division.tsv
        [ -s "$list" ] || { echo "ABORT core $core: $list missing or empty"; return 2; }
        "$RUNNER" "$division" "$list" "$out" "$core" "$AX" \
            "AXEYUM_NIA_ORDER_LEMMAS=0" "AXEYUM_NIA_ORDER_LEMMAS=1" "$BUDGET"
    done
    echo "SHARD-DONE core $core"
}

run_shard 5 "${shard_one[@]}" &
one=$!
run_shard 6 "${shard_two[@]}" &
two=$!
wait "$one"; rc_one=$?
wait "$two"; rc_two=$?
echo "LAUNCH-DONE shard5=$rc_one shard6=$rc_two out=$OUTDIR"
