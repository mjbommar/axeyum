#!/usr/bin/env bash
# ADR-2125: run this shard's queue of A/B jobs SERIALLY on its pinned core pair.
#
# Serial per shard, not parallel: the two arms of a file run back to back on the
# same core so ambient load cancels in the difference, and that argument is void
# if this shard is also running a second job on the same cores. The two shards
# are the only parallelism, and they own disjoint physical core pairs.
#
# The QUEUE puts the two datasets the SHIP DECISION rests on first and in
# parallel with each other -- `QF_LRA` pinned on one shard, the held-out draw on
# the other -- rather than both waiting behind a division-by-division sweep. The
# five exposure divisions follow, split across both shards; they answer the
# regression question, not the ship question.
#
# A MISSING LIST REFUSES THE WHOLE SHARD rather than skipping to the next job.
# ADR-2122 recorded why: a skip silently REORDERS the queue, so the run measures
# a different set of divisions from the one it was asked for, and the only trace
# is one line in a log nobody reads until the numbers are wrong.
#
# Usage: launch-ab.sh <shard> <cores> <bin>
set -u
SHARD="$1"; PIN="$2"; AX="$3"

if [ "$SHARD" = "00" ]; then
  JOBS="QF_LRA:QF_LRA.txt QF_LIA:QF_LIA.00.txt QF_UFLRA:QF_UFLRA.00.txt \
        QF_UFLIA:QF_UFLIA.00.txt QF_IDL:QF_IDL.00.txt QF_RDL:QF_RDL.00.txt"
else
  JOBS="QF_LRA_HELD:QF_LRA-heldout.txt QF_LIA:QF_LIA.01.txt QF_UFLRA:QF_UFLRA.01.txt \
        QF_UFLIA:QF_UFLIA.01.txt QF_IDL:QF_IDL.01.txt QF_RDL:QF_RDL.01.txt"
fi

for job in $JOBS; do
  tag="${job%%:*}"
  list="lists/${job#*:}"
  out="ab.$tag.$SHARD.tsv"
  if [ -s "$out" ]; then
    echo "SKIP $tag $SHARD: $out already has rows"
    continue
  fi
  if [ ! -r "$list" ]; then
    echo "ABORT $SHARD: $list unreadable -- refusing the whole queue"
    exit 2
  fi
  echo "START $tag $SHARD $(date -Is)"
  ./ab-run.sh "$tag.$SHARD" "$list" "$out" "$PIN" "$AX" 24
  echo "END   $tag $SHARD $(date -Is)"
done
echo "LAUNCH-DONE $SHARD"
