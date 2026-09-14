#!/usr/bin/env bash
# SKELETON-REACH -- launch one A/B phase across the lane's FIXED shard set.
#
#   ab-launch.sh <phase-tag> <list> <phase:ab|noise> [budget_s]
#
# SHARD CONFIGURATION, HELD FIXED ACROSS ARMS AND PHASES:
#   s5 cores {1,3,5,7}   s6 cores {1,3,5,7}   = 8 pinned pairs, never more.
# Both arms of a file run INSIDE one shard, back to back on one core, so a
# shard cannot move one arm relative to the other. Round-robin by line index,
# never contiguous blocks: the lists are path-sorted.
set -eu
TAG="$1"
LIST="$2"
PHASE="$3"
BUDGET="${4:-24}"
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGE=/nas3/data/axeyum/harness/skeleton-reach/stage
AX=${SKEL_AX:-/nas3/data/axeyum/harness/skeleton-reach/bin/smtcomp_cli-arm}
SHARDS=("s5:1" "s5:3" "s5:5" "s5:7" "s6:1" "s6:3" "s6:5" "s6:7")

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
mkdir -p "$STAGE"
cp "$HERE/ab-run.sh" "$STAGE/"
chmod +x "$STAGE/ab-run.sh"

rm -f "$STAGE/$TAG".shard*.list "$STAGE/$TAG".shard*.tsv "$STAGE/$TAG".shard*.log
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  printf '%s\n' "$f" >> "$STAGE/$TAG.shard$((n % ${#SHARDS[@]})).list"
  n=$((n + 1))
done < "$LIST"
echo "$TAG: $n files over ${#SHARDS[@]} shards, phase=$PHASE budget=${BUDGET}s bin=$AX"

i=0
for sh in "${SHARDS[@]}"; do
  host="${sh%%:*}"
  core="${sh##*:}"
  L="$STAGE/$TAG.shard$i.list"
  if [ -f "$L" ]; then
    ssh -o BatchMode=yes "$host" \
      "nohup setsid $STAGE/ab-run.sh $L $STAGE/$TAG.shard$i.tsv $core $AX $BUDGET $PHASE \
         > $STAGE/$TAG.shard$i.log 2>&1 < /dev/null &" >/dev/null 2>&1
    echo "  launched $TAG shard$i on $host core $core ($(wc -l < "$L") files)"
  fi
  i=$((i + 1))
done
echo "$TAG: all shards launched; artifacts at $STAGE/$TAG.shard*.tsv"
