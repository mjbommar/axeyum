#!/usr/bin/env bash
# Lane euf-driver-mbtc: the shipped default (ladder reserve = 1/4) over both
# populations, against the already-collected base arms.
set -uo pipefail
cd "$(dirname "$0")/.."

LANE=.lane-euf-driver-mbtc

$LANE/sweep.sh "$LANE/QF_UFLIA-losses.txt" "$LANE/smtcomp_cli.reserve" \
  "$LANE/reserve-QF_UFLIA58.tsv" probe > /dev/null 2>&1 &
P1=$!
$LANE/sweep.sh "$LANE/QF_UFLIA-all200.txt" "$LANE/smtcomp_cli.reserve" \
  "$LANE/reserve-QF_UFLIA200.tsv" probe > /dev/null 2>&1 &
P2=$!
wait $P1 $P2
echo RESERVE_ARMS_COMPLETE
