#!/usr/bin/env bash
# CORE-SELECT -- launch the re-derivation sweep across this lane's FIXED shards.
#
#   ax-launch.sh <tag> <list> [budget_s]
#
# SHARDS, held fixed for every phase of this lane: s7 cores {0,1,2,3}.
# s7 was measured IDLE (load 0.08) when this lane started; s5 and s6 carry
# another lane's 16-division board A/B.  A verdict sweep at a 24 s budget is
# load-sensitive at the boundary -- a file deciding at 23.5 s on an idle core
# misses at 25 s on a loaded one -- so the whole population is re-derived on one
# host, and the host and core are columns in the output.
#
# Round-robin by line index, never contiguous blocks: the lists are path-sorted
# and contiguous blocks would put one benchmark family on one core.
set -eu
TAG="$1"; LIST="$2"; BUDGET="${3:-24}"
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGE=/nas3/data/axeyum/harness/core-select/stage
AX=${CS_AX:-/nas3/data/axeyum/harness/core-select/bin/smtcomp_cli-base}
SHARDS=("s7:0" "s7:1" "s7:2" "s7:3")

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
mkdir -p "$STAGE"
cp "$HERE/ax-run.sh" "$STAGE/"
chmod +x "$STAGE/ax-run.sh"
rm -f "$STAGE/$TAG".shard*.list "$STAGE/$TAG".shard*.tsv "$STAGE/$TAG".shard*.log

n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  printf '%s\n' "$f" >> "$STAGE/$TAG.shard$((n % ${#SHARDS[@]})).list"
  n=$((n + 1))
done < "$LIST"
echo "$TAG: $n files over ${#SHARDS[@]} shards, budget=${BUDGET}s bin=$AX"

i=0
for sh in "${SHARDS[@]}"; do
  host="${sh%%:*}"; core="${sh##*:}"
  L="$STAGE/$TAG.shard$i.list"
  if [ -f "$L" ]; then
    ssh -o BatchMode=yes "$host" \
      "nohup setsid $STAGE/ax-run.sh $L $STAGE/$TAG.shard$i.tsv $core $AX $BUDGET \
         > $STAGE/$TAG.shard$i.log 2>&1 < /dev/null &" >/dev/null 2>&1
    echo "  launched $TAG shard$i on $host core $core ($(wc -l < "$L") files)"
  fi
  i=$((i + 1))
done
echo "$TAG: artifacts at $STAGE/$TAG.shard*.tsv"
