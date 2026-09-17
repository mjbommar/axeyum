#!/usr/bin/env bash
# ADR-2148's four-population A/B: ONE binary, the shipped setting against the
# chosen arm, interleaved per file (ADR-2136's `ab-run-env.sh`, reused
# verbatim), 24 s / 8 GiB, on s7 cores 1, 9, 3, 11 -- the two hyperthread
# pairs this lane owns, all four logical cores at once so the 800 files fit
# the window. As in ADR-2136 that inflates timeouts on BOTH arms of every
# file, which is conservative for a ship gate and not for a gain; every mover
# is re-checked 3x per arm on a quiet core afterwards.
#
# usage: launch-ab.sh <bin> <listdir> <outdir> "<envA>" "<envB>" [budget_s]
set -uo pipefail
AX=${1:?bin}; LISTDIR=${2:?listdir}; OUTDIR=${3:?outdir}; ENV_A=${4?envA}; ENV_B=${5?envB}; BUDGET=${6:-24}
HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
RUNNER=$HERE/ab-run-env.sh
[ -x "$AX" ] || { echo "ABORT: $AX not executable"; exit 2; }
[ -x "$RUNNER" ] || { echo "ABORT: $RUNNER missing"; exit 2; }
mkdir -p "$OUTDIR"

# Clock self-check once, up front (uutils `date`; $EPOCHREALTIME is the unit).
t0=$EPOCHREALTIME; sleep 0.2; t1=$EPOCHREALTIME
ms=$(python3 -c "print(int(($t1-$t0)*1000))")
{ [ "$ms" -ge 150 ] && [ "$ms" -le 400 ]; } || { echo "ABORT: clock self-check ${ms} ms"; exit 3; }
echo "clock self-check ${ms} ms OK; bin=$(sha256sum "$AX" | cut -c1-16) A=[$ENV_A] B=[$ENV_B]"

run_one() {  # core division list
    local core=$1 div=$2 list=$3
    "$RUNNER" "$div" "$list" "$OUTDIR/ab-$div.tsv" "$core" "$AX" "$ENV_A" "$ENV_B" "$BUDGET" \
        > "$OUTDIR/ab-$div.log" 2>&1
    echo "SHARD-DONE $div core=$core rc=$?"
}
run_one 1  QF_NIA         "$LISTDIR/ab-list-QF_NIA.txt" &
run_one 9  QF_NRA         "$LISTDIR/ab-list-QF_NRA.txt" &
run_one 3  UFNIA          "$LISTDIR/ab-list-UFNIA.txt" &
run_one 11 QF_NIA-heldout "$LISTDIR/heldout-QF_NIA.txt" &
wait
echo "LAUNCH-DONE out=$OUTDIR"
