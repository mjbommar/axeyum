#!/usr/bin/env bash
# ADR-2122: run the six divisions SERIALLY on one shard's pinned core pair.
#
# Serial per shard, not parallel: the two arms of a file run back to back on the
# same core so ambient load cancels in the difference, and that argument is void
# if this shard is also running a second division on the same cores. The two
# shards are the only parallelism, and they own disjoint physical core pairs.
#
# Usage: launch-ab.sh <shard> <cores> <bin>     e.g. launch-ab.sh 00 5,13 ./smtcomp_cli.arm-b
set -u
SHARD="$1"; PIN="$2"; AX="$3"
DIVS="QF_LRA QF_LIA QF_UFLRA QF_UFLIA QF_IDL QF_RDL"
for d in $DIVS; do
  out="ab.$d.$SHARD.tsv"
  if [ -s "$out" ]; then
    echo "SKIP $d $SHARD: $out already has rows"
    continue
  fi
  echo "START $d $SHARD $(date -Is)"
  ./ab-run.sh "$d.$SHARD" "$d.$SHARD.txt" "$out" "$PIN" "$AX" 24
  echo "END   $d $SHARD $(date -Is)"
done
echo "LAUNCH-DONE $SHARD"
