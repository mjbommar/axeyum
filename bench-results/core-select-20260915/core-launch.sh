#!/usr/bin/env bash
# CORE-SELECT -- launch the core census across a named shard set.
#
#   core-launch.sh <tag> <list> <shardspec> [tlimit] [min-cap] [min-tlimit] [min-budget]
#
# `shardspec` is a space-separated list of `host:core` pairs, quoted.  This lane
# takes at most SIX pinned physical cores at a time and names them in the ADR:
#   s7 {0,1,2,3} (measured idle, load 0.08), s5 {1}, s6 {3}.
# Reference measurements are preferred on s7 because a lane read z3 at 155
# against a true 166 by running six concurrent shards.
#
# Round-robin by line index, never contiguous blocks: the lists are path-sorted,
# so contiguous blocks would put one benchmark family on one core and make a
# per-shard effect indistinguishable from a per-family one.
set -eu
TAG="$1"; LIST="$2"; SHARDSPEC="$3"
TL="${4:-60}"; MINCAP="${5:-64}"; MINTL="${6:-10}"; MINBUD="${7:-600}"
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGE=/nas3/data/axeyum/harness/core-select/stage
OUTDIR=${CS_COREDIR:-/nas3/data/axeyum/harness/core-select/cores}
read -r -a SHARDS <<< "$SHARDSPEC"
[ "${#SHARDS[@]}" -gt 0 ] || { echo "ABORT: empty shardspec"; exit 2; }

mkdir -p "$STAGE" "$OUTDIR"
cp "$HERE/core-run.sh" "$HERE/core.py" "$HERE/smtsplit.py" "$STAGE/"
chmod +x "$STAGE/core-run.sh" "$STAGE/core.py"
rm -f "$STAGE/$TAG".shard*.list "$STAGE/$TAG".shard*.tsv "$STAGE/$TAG".shard*.log

n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  printf '%s\n' "$f" >> "$STAGE/$TAG.shard$((n % ${#SHARDS[@]})).list"
  n=$((n + 1))
done < "$LIST"
echo "$TAG: $n files over ${#SHARDS[@]} shards (${SHARDS[*]}) tlimit=${TL}s min-cap=$MINCAP"

i=0
for sh in "${SHARDS[@]}"; do
  host="${sh%%:*}"; core="${sh##*:}"
  L="$STAGE/$TAG.shard$i.list"
  if [ -f "$L" ]; then
    ssh -o BatchMode=yes "$host" \
      "nohup setsid $STAGE/core-run.sh $L $STAGE/$TAG.shard$i.tsv $core $OUTDIR $TL $MINCAP $MINTL $MINBUD \
         > $STAGE/$TAG.shard$i.log 2>&1 < /dev/null &" >/dev/null 2>&1
    echo "  launched $TAG shard$i on $host core $core ($(wc -l < "$L") files)"
  fi
  i=$((i + 1))
done
echo "$TAG: artifacts at $STAGE/$TAG.shard*.tsv, cores at $OUTDIR"
