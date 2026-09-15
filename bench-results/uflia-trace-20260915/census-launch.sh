#!/usr/bin/env bash
# UFLIA-TRACE -- launch the traced census across this lane's pinned cores.
#
#   census-launch.sh <tag> <list> <shardspec> [budget_s]
#
# This lane owns s6 physical core pairs 5,13 and 6,14 and nothing else.
set -eu
TAG="$1"; LIST="$2"; SHARDSPEC="$3"; BUDGET="${4:-24}"
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGE=/nas3/data/axeyum/harness/uflia-trace/stage
AX=${UT_AX:-/nas3/data/axeyum/harness/uflia-trace/bin/smtcomp_cli-base}
read -r -a SHARDS <<< "$SHARDSPEC"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

mkdir -p "$STAGE"
cp "$HERE/census-run.sh" "$HERE/probe-shape.py" "$STAGE/"
chmod +x "$STAGE/census-run.sh"
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
      "nohup setsid $STAGE/census-run.sh $L $STAGE/$TAG.shard$i.tsv $core $AX $BUDGET \
         > $STAGE/$TAG.shard$i.log 2>&1 < /dev/null &" >/dev/null 2>&1
    echo "  launched $TAG shard$i on $host core $core ($(wc -l < "$L") files)"
  fi
  i=$((i + 1))
done
echo "$TAG: artifacts at $STAGE/$TAG.shard*.tsv"
