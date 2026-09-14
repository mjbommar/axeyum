#!/usr/bin/env bash
# SKELETON-REACH -- launch the static skeleton census across a FIXED shard set.
#
#   skel-launch.sh <tag> <list> [tlimit_s]
#
# SHARD CONFIGURATION, HELD FIXED FOR EVERY PHASE OF THIS LANE:
#   s5 cores {1,3,5,7}   s6 cores {1,3,5,7}   = 8 pinned pairs, never more.
#
# Files go to shards ROUND-ROBIN by line index, never in contiguous blocks:
# the lists are path-sorted and concatenated per division, so a contiguous
# split would put a whole division on one core and confound shard with
# subject.
#
# Results land in $STAGE/<tag>.shard*.tsv. Collect with skel-collect.sh, which
# watches the ARTIFACT -- never a `pgrep -f` waiter, whose own command line
# contains its pattern and matches itself.
set -eu
TAG="$1"
LIST="$2"
TL="${3:-20}"
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGE=/nas3/data/axeyum/harness/skeleton-reach/stage
SHARDS=("s5:1" "s5:3" "s5:5" "s5:7" "s6:1" "s6:3" "s6:5" "s6:7")

mkdir -p "$STAGE"
cp "$HERE/skel-census.sh" "$HERE/abstract-quantifiers.py" "$STAGE/"
chmod +x "$STAGE/skel-census.sh"

rm -f "$STAGE/$TAG".shard*.list "$STAGE/$TAG".shard*.tsv "$STAGE/$TAG".shard*.log
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  printf '%s\n' "$f" >> "$STAGE/$TAG.shard$((n % ${#SHARDS[@]})).list"
  n=$((n + 1))
done < "$LIST"
echo "$TAG: $n files over ${#SHARDS[@]} shards, tlimit=${TL}s"

i=0
for sh in "${SHARDS[@]}"; do
  host="${sh%%:*}"
  core="${sh##*:}"
  L="$STAGE/$TAG.shard$i.list"
  if [ -f "$L" ]; then
    ssh -o BatchMode=yes "$host" \
      "nohup setsid env SKEL_WORK=/tmp/skelw-$TAG-$i $STAGE/skel-census.sh $L $STAGE/$TAG.shard$i.tsv $core $TL \
         > $STAGE/$TAG.shard$i.log 2>&1 < /dev/null &" >/dev/null 2>&1
    echo "  launched $TAG shard$i on $host core $core ($(wc -l < "$L") files)"
  fi
  i=$((i + 1))
done
echo "$TAG: all shards launched; artifacts at $STAGE/$TAG.shard*.tsv"
