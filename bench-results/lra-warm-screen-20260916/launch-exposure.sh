#!/usr/bin/env bash
# ADR-2132: the five EXPOSURE divisions, serially per shard, two arms each.
#
# The ship criterion has two halves and they need different populations. The two
# `QF_LRA` draws decide whether the screen keeps ADR-2125's gain without its
# losses, and those run three arms. These five ask only "did the screen regress
# a division it was not aimed at", which `off` vs `screened` answers -- so they
# run `AXEYUM_AB3_ARMS=AC` and the compute saved goes to the draws the decision
# rests on. `on` is simply absent from these tables, written EMPTY rather than as
# zeros, and the summarizer says DID NOT RUN.
#
# `QF_LIA` FIRST on both shards, and that ordering is deliberate rather than
# alphabetical: it drives the same simplex, ADR-2125 got 7 rows of it and
# labelled that a partial rather than a division, and a queue that runs out of
# wall clock should run out of it having finished the division that matters most.
#
# A MISSING LIST REFUSES THE WHOLE SHARD rather than skipping to the next job.
# ADR-2122 recorded why: a skip silently REORDERS the queue, so the run measures
# a different set of divisions from the one it was asked for, and the only trace
# is one line in a log nobody reads until the numbers are wrong.
#
# Usage: launch-exposure.sh <shard 00|01> <cores> <bin>
set -u
SHARD="$1"; PIN="$2"; AX="$3"

if [ "$SHARD" = "00" ]; then
  JOBS="QF_LIA:QF_LIA.00.txt QF_UFLRA:QF_UFLRA.00.txt QF_UFLIA:QF_UFLIA.00.txt \
        QF_IDL:QF_IDL.00.txt QF_RDL:QF_RDL.00.txt"
else
  JOBS="QF_LIA:QF_LIA.01.txt QF_UFLRA:QF_UFLRA.01.txt QF_UFLIA:QF_UFLIA.01.txt \
        QF_IDL:QF_IDL.01.txt QF_RDL:QF_RDL.01.txt"
fi

export AXEYUM_AB3_ARMS=AC

for job in $JOBS; do
  tag="${job%%:*}"
  list="lists/${job#*:}"
  out="ab3.$tag.$SHARD.tsv"
  if [ -s "$out" ]; then
    echo "SKIP $tag $SHARD: $out already has rows"
    continue
  fi
  if [ ! -r "$list" ]; then
    echo "ABORT $SHARD: $list unreadable -- refusing the whole queue"
    exit 2
  fi
  echo "START $tag $SHARD $(date -Is)"
  ./ab3-run.sh "$tag.$SHARD" "$list" "$out" "$PIN" "$AX" 24
  echo "END   $tag $SHARD $(date -Is)"
done
echo "EXPOSURE-DONE $SHARD"
