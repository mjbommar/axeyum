#!/usr/bin/env bash
# Lane euf-driver-mbtc: the three arms over the 58-file loss population, run
# CONCURRENTLY on one host.
#
# Concurrent rather than sequential on purpose. This box carries other lanes and
# its load average moved between 8 and 34 during this lane's own runs, so three
# arms run back to back are three different machines. Run together they share
# one machine — the contention is common-mode and cancels in the comparison,
# which is what a paired A/B needs. The cost is that every arm's absolute wall
# clock is inflated: read the DECIDED SET, not the milliseconds. Each TSV
# records the load average it started under so that caveat is checkable.
set -uo pipefail
cd "$(dirname "$0")/.."

LANE=.lane-euf-driver-mbtc
LOSSES=$LANE/QF_UFLIA-losses.txt

$LANE/sweep.sh "$LOSSES" "$LANE/smtcomp_cli.base" "$LANE/base-QF_UFLIA58.tsv"          > /dev/null 2>&1 &
P1=$!
$LANE/sweep.sh "$LOSSES" "$LANE/smtcomp_cli.new"  "$LANE/probe-QF_UFLIA58.tsv" probe   > /dev/null 2>&1 &
P2=$!
$LANE/sweep.sh "$LOSSES" "$LANE/smtcomp_cli.new"  "$LANE/skip-QF_UFLIA58.tsv"  skip    > /dev/null 2>&1 &
P3=$!
wait $P1 $P2 $P3
echo LOSSES_ARMS_COMPLETE
