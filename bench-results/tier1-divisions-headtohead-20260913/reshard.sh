#!/usr/bin/env bash
# Re-split ONE division's pinned 200 into K modulo-interleaved shards and print
# the split, so a slow division can be spread over more cores than the initial
# two-shard layout gives it.
#
# UFNIA is why this exists: at ~1.7 min per file it was a 3.3 h division on two
# shards while AUFLIRA finished 200 files in nine minutes.  Modulo-interleaving
# means every shard still spans the whole division, and `merge-division.py`
# discovers however many shards exist and ABORTS unless they cover the pinned
# list exactly -- so re-sharding cannot quietly shrink the denominator.
#
# It refuses to overwrite a shard list while rows exist for it, because
# re-splitting mid-run would leave rows keyed to a list that no longer matches.
#
# Usage: reshard.sh <DIV> <K>
set -eu
LANE="$(cd "$(dirname "$0")" && pwd)"
H=/nas3/data/axeyum/harness/tier1-divisions
DIV="$1"; K="$2"
declare -A STEM=([FP]=FP-fullspan)
SRC="$LANE/../parity-lists/${STEM[$DIV]:-$DIV}.txt"

[ -f "$SRC" ] || { echo "ABORT: $SRC missing"; exit 2; }
for f in "$H"/out/"$DIV".s*.tsv; do
  [ -e "$f" ] || continue
  echo "ABORT: $f exists -- move or delete the old shard output first"
  exit 2
done

tot=0
for i in $(seq 0 $((K - 1))); do
  awk -v k="$K" -v i="$i" 'NR%k==i' "$SRC" > "$H/lists/$DIV.s$i"
  c=$(wc -l < "$H/lists/$DIV.s$i")
  tot=$((tot + c))
  echo "  $DIV.s$i: $c files"
done
[ "$tot" = 200 ] || { echo "ABORT: $DIV shards total $tot, not 200"; exit 2; }
echo "RESHARD-OK $DIV into $K shards"
