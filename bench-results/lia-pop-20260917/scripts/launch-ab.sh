#!/usr/bin/env bash
# Launch the ADR-2143 A/B on s7: each division's 200-file list is split into
# two halves by line parity, one half per pinned physical core pair (1,9 and
# 3,11), and each core pair walks its four half-lists in sequence so both
# pairs work on every division.
#
# The lane's worktree is NOT mounted on s7 (only /nas3 is), so `ab-run.sh` and
# the four lists are read from REMOTE, a copy of this directory on the NAS.
#
# Usage: launch-ab.sh <binA> <binB> <outdir> <budget_s> <remote_scripts_dir> <lists_dir>
set -eu
AX_A="$1"; AX_B="$2"; OUTDIR="$3"; BUDGET="$4"; REMOTE="$5"; LISTS="$6"
HOST=${AB_HOST:-s7}
CORES=("1,9" "3,11")

mkdir -p "$OUTDIR/lists"
for DIV in QF_LIA QF_LRA QF_UFLIA QF_IDL; do
  awk -v out="$OUTDIR/lists" -v div="$DIV" \
    '{ print > sprintf("%s/%s.%d.txt", out, div, NR % 2) }' "$LISTS/$DIV.txt"
done

for s in 0 1; do
  c=${CORES[$s]}
  cmd=""
  for DIV in QF_LIA QF_LRA QF_UFLIA QF_IDL; do
    so="$OUTDIR/$DIV.shard$s.tsv"
    [ -s "$so" ] && { echo "ABORT: $so already non-empty"; exit 2; }
    cmd="$cmd bash $REMOTE/ab-run.sh $DIV-$s $OUTDIR/lists/$DIV.$s.txt $so '$c' $AX_A $AX_B $BUDGET;"
  done
  ssh -n -f -- "$HOST" "cd /tmp && nohup setsid bash -c \"$cmd\" > $OUTDIR/shard$s.log 2>&1 < /dev/null &"
  echo "LAUNCHED shard $s on $HOST cores $c"
done
echo "LAUNCH-OK"
