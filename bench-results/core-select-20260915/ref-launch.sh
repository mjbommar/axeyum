#!/usr/bin/env bash
# CORE-SELECT -- A5's sampled half: re-ask REF-NONE rows on the ORIGINAL file.
#
#   ref-launch.sh <tag> <list> <shardspec> [budget_s]
#
# The census asks z3 about the SPLIT file, which is an equivalence but not a
# performance-neutral one. This re-asks a seeded sample on the original, so a
# REF-NONE bucket the split itself produced would be visible rather than
# assumed away.
set -eu
TAG="$1"; LIST="$2"; SHARDSPEC="$3"; BUDGET="${4:-60}"
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGE=/nas3/data/axeyum/harness/core-select/stage
read -r -a SHARDS <<< "$SHARDSPEC"

mkdir -p "$STAGE"
cp "$HERE/ref-run.sh" "$STAGE/"
chmod +x "$STAGE/ref-run.sh"
rm -f "$STAGE/$TAG".shard*.list "$STAGE/$TAG".shard*.tsv "$STAGE/$TAG".shard*.log
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  printf '%s\n' "$f" >> "$STAGE/$TAG.shard$((n % ${#SHARDS[@]})).list"
  n=$((n + 1))
done < "$LIST"
echo "$TAG: $n files over ${#SHARDS[@]} shards (${SHARDS[*]}) budget=${BUDGET}s"

i=0
for sh in "${SHARDS[@]}"; do
  host="${sh%%:*}"; core="${sh##*:}"
  L="$STAGE/$TAG.shard$i.list"
  if [ -f "$L" ]; then
    ssh -o BatchMode=yes "$host" \
      "nohup setsid $STAGE/ref-run.sh $L $STAGE/$TAG.shard$i.tsv $core $BUDGET \
         > $STAGE/$TAG.shard$i.log 2>&1 < /dev/null &" >/dev/null 2>&1
    echo "  launched $TAG shard$i on $host core $core ($(wc -l < "$L") files)"
  fi
  i=$((i + 1))
done
echo "$TAG: artifacts at $STAGE/$TAG.shard*.tsv"
