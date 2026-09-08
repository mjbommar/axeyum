#!/usr/bin/env bash
# Lane euf-driver-mbtc: the A/B. Two PINNED binaries (see build-pinned.sh) so a
# later build cannot swap the file a sweep is reading — that happened once, and
# split one baseline across two solvers with nothing in the TSV to say so.
#
# Order is deliberate: the 58-file loss population (the question this lane was
# sent to answer) runs FIRST under all three arms; the 200-file regression check
# runs after, because it is the check on the answer, not the answer.
set -uo pipefail
cd "$(dirname "$0")/.."

LANE=.lane-euf-driver-mbtc
LOSSES=$LANE/QF_UFLIA-losses.txt
ALL=$LANE/QF_UFLIA-all200.txt

$LANE/sweep.sh "$LOSSES" "$LANE/smtcomp_cli.base" "$LANE/base-QF_UFLIA58.tsv"
echo LOSSES_BASE_DONE
$LANE/sweep.sh "$LOSSES" "$LANE/smtcomp_cli.new" "$LANE/probe-QF_UFLIA58.tsv" probe
echo LOSSES_PROBE_DONE
$LANE/sweep.sh "$LOSSES" "$LANE/smtcomp_cli.new" "$LANE/skip-QF_UFLIA58.tsv" skip
echo LOSSES_SKIP_DONE

$LANE/sweep.sh "$ALL" "$LANE/smtcomp_cli.base" "$LANE/base-QF_UFLIA200.tsv"
echo ALL_BASE_DONE
$LANE/sweep.sh "$ALL" "$LANE/smtcomp_cli.new" "$LANE/probe-QF_UFLIA200.tsv" probe
echo AB_COMPLETE
