#!/usr/bin/env bash
# SKELETON-REACH -- launch fd-census.sh across the lane's FIXED shard set.
#
#   fd-launch.sh <tag> <list> [budget_s] [extra_env]
#
# SHARD CONFIGURATION, HELD FIXED FOR EVERY PHASE OF THIS LANE:
#   s5 cores {1,3,5,7}   s6 cores {1,3,5,7}   = 8 pinned pairs, never more.
#
# Round-robin by line index, never contiguous: the lists are path-sorted, so a
# contiguous split confounds shard with family.
#
# `extra_env` is passed verbatim to `env` on the remote side, so an arm can be
# selected WITHOUT rebuilding -- one binary, two env values.
set -eu
TAG="$1"
LIST="$2"
BUDGET="${3:-24}"
EXTRA="${4:-}"
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGE=/nas3/data/axeyum/harness/skeleton-reach/stage
SHARDS=("s5:1" "s5:3" "s5:5" "s5:7" "s6:1" "s6:3" "s6:5" "s6:7")

mkdir -p "$STAGE"
cp "$HERE/fd-census.sh" "$STAGE/"
chmod +x "$STAGE/fd-census.sh"

rm -f "$STAGE/$TAG".shard*.list "$STAGE/$TAG".shard*.tsv "$STAGE/$TAG".shard*.log
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  printf '%s\n' "$f" >> "$STAGE/$TAG.shard$((n % ${#SHARDS[@]})).list"
  n=$((n + 1))
done < "$LIST"
echo "$TAG: $n files over ${#SHARDS[@]} shards, budget=${BUDGET}s env='${EXTRA:-<none>}'"

i=0
for sh in "${SHARDS[@]}"; do
  host="${sh%%:*}"
  core="${sh##*:}"
  L="$STAGE/$TAG.shard$i.list"
  if [ -f "$L" ]; then
    ssh -o BatchMode=yes "$host" \
      "nohup setsid env $EXTRA $STAGE/fd-census.sh $L $STAGE/$TAG.shard$i.tsv $core $BUDGET \
         > $STAGE/$TAG.shard$i.log 2>&1 < /dev/null &" >/dev/null 2>&1
    echo "  launched $TAG shard$i on $host core $core ($(wc -l < "$L") files)"
  fi
  i=$((i + 1))
done
echo "$TAG: all shards launched; artifacts at $STAGE/$TAG.shard*.tsv"
