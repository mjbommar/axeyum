#!/usr/bin/env bash
# CORE-SELECT -- launch the traced pass across a named shard set.
#
#   trace-launch.sh <tag> <list-of-subset-paths> <shardspec> [budget_s]
#
# Runs over ALL cores, not only the ones the ceiling is negative on: the
# give-up reason is only informative as a COMPARISON between the rows we refute
# and the rows we do not, and a pass restricted to the failures has no contrast
# to offer.
set -eu
TAG="$1"; LIST="$2"; SHARDSPEC="$3"; BUDGET="${4:-24}"
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGE=/nas3/data/axeyum/harness/core-select/stage
AX=${CS_AX:-/nas3/data/axeyum/harness/core-select/bin/smtcomp_cli-base}
read -r -a SHARDS <<< "$SHARDSPEC"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

mkdir -p "$STAGE"
cp "$HERE/trace-run.sh" "$STAGE/"
chmod +x "$STAGE/trace-run.sh"
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
      "nohup setsid $STAGE/trace-run.sh $L $STAGE/$TAG.shard$i.tsv $core $AX $BUDGET \
         > $STAGE/$TAG.shard$i.log 2>&1 < /dev/null &" >/dev/null 2>&1
    echo "  launched $TAG shard$i on $host core $core ($(wc -l < "$L") files)"
  fi
  i=$((i + 1))
done
echo "$TAG: artifacts at $STAGE/$TAG.shard*.tsv"
