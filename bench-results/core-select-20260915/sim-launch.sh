#!/usr/bin/env bash
# CORE-SELECT -- launch the subset simulation across a named shard set.
#
#   sim-launch.sh <tag> <list-of-subset-paths> <shardspec> [budget_s]
set -eu
TAG="$1"; LIST="$2"; SHARDSPEC="$3"; BUDGET="${4:-24}"
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGE=/nas3/data/axeyum/harness/core-select/stage
AX=${CS_AX:-/nas3/data/axeyum/harness/core-select/bin/smtcomp_cli-base}
read -r -a SHARDS <<< "$SHARDSPEC"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ "${#SHARDS[@]}" -gt 0 ] || { echo "ABORT: empty shardspec"; exit 2; }

mkdir -p "$STAGE"
cp "$HERE/sim-run.sh" "$STAGE/"
chmod +x "$STAGE/sim-run.sh"
rm -f "$STAGE/$TAG".shard*.list "$STAGE/$TAG".shard*.tsv "$STAGE/$TAG".shard*.log

n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  printf '%s\n' "$f" >> "$STAGE/$TAG.shard$((n % ${#SHARDS[@]})).list"
  n=$((n + 1))
done < "$LIST"
echo "$TAG: $n subsets over ${#SHARDS[@]} shards (${SHARDS[*]}) budget=${BUDGET}s bin=$AX"

i=0
for sh in "${SHARDS[@]}"; do
  host="${sh%%:*}"; core="${sh##*:}"
  L="$STAGE/$TAG.shard$i.list"
  if [ -f "$L" ]; then
    ssh -o BatchMode=yes "$host" \
      "nohup setsid $STAGE/sim-run.sh $L $STAGE/$TAG.shard$i.tsv $core $AX $BUDGET \
         > $STAGE/$TAG.shard$i.log 2>&1 < /dev/null &" >/dev/null 2>&1
    echo "  launched $TAG shard$i on $host core $core ($(wc -l < "$L") subsets)"
  fi
  i=$((i + 1))
done
echo "$TAG: artifacts at $STAGE/$TAG.shard*.tsv"
