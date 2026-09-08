#!/usr/bin/env bash
# Lane euf-driver-mbtc: the regression check. The 58-file loss population says
# what the change WINS; this says what it costs on the 142 files we already
# decide, which is where a budget split can only hurt. Both arms concurrent, for
# the same common-mode reason as run-ab-parallel.sh.
set -uo pipefail
cd "$(dirname "$0")/.."

LANE=.lane-euf-driver-mbtc
ALL=$LANE/QF_UFLIA-all200.txt

$LANE/sweep.sh "$ALL" "$LANE/smtcomp_cli.base" "$LANE/base-QF_UFLIA200.tsv"        > /dev/null 2>&1 &
P1=$!
$LANE/sweep.sh "$ALL" "$LANE/smtcomp_cli.new"  "$LANE/probe-QF_UFLIA200.tsv" probe > /dev/null 2>&1 &
P2=$!
wait $P1 $P2
echo REGRESSION_COMPLETE
