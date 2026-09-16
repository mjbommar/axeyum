#!/usr/bin/env bash
# ADR-2122: run this shard's queue of A/B jobs SERIALLY on its pinned core pair.
#
# Serial per shard, not parallel: the two arms of a file run back to back on the
# same core so ambient load cancels in the difference, and that argument is void
# if this shard is also running a second job on the same cores. The two shards
# are the only parallelism, and they own disjoint physical core pairs.
#
# The QUEUE is ordered so the two datasets the SHIP DECISION rests on finish
# first and in parallel with each other -- `QF_LRA` pinned on one shard,
# `QF_LRA` held-out on the other -- rather than both waiting behind a
# division-by-division sweep. The five exposure divisions follow, split across
# both shards; they answer the regression question, not the ship question.
#
# Usage: launch-ab.sh <shard> <cores> <bin>   e.g. launch-ab.sh 00 5,13 ./smtcomp_cli.arm-c
set -u
SHARD="$1"; PIN="$2"; AX="$3"

# `tag:listfile` pairs. Shard 00 takes the pinned draw whole, shard 01 the
# held-out draw whole; then each takes its half of the five exposure divisions.
if [ "$SHARD" = "00" ]; then
  JOBS="QF_LRA:QF_LRA.txt QF_LIA:QF_LIA.00.txt QF_UFLRA:QF_UFLRA.00.txt \
        QF_UFLIA:QF_UFLIA.00.txt QF_IDL:QF_IDL.00.txt QF_RDL:QF_RDL.00.txt"
else
  JOBS="QF_LRA_HELD:QF_LRA-heldout.txt QF_LIA:QF_LIA.01.txt QF_UFLRA:QF_UFLRA.01.txt \
        QF_UFLIA:QF_UFLIA.01.txt QF_IDL:QF_IDL.01.txt QF_RDL:QF_RDL.01.txt"
fi

for job in $JOBS; do
  tag="${job%%:*}"
  list="${job#*:}"
  out="ab.$tag.$SHARD.tsv"
  if [ -s "$out" ]; then
    echo "SKIP $tag $SHARD: $out already has rows"
    continue
  fi
  if [ ! -r "$list" ]; then
    echo "ABORT $tag $SHARD: $list unreadable"
    continue
  fi
  echo "START $tag $SHARD $(date -Is)"
  ./ab-run.sh "$tag.$SHARD" "$list" "$out" "$PIN" "$AX" 24
  echo "END   $tag $SHARD $(date -Is)"
done
echo "LAUNCH-DONE $SHARD"
