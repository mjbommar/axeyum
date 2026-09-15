#!/usr/bin/env bash
# CORE-SELECT -- partition a list into WEIGHTED shards once, then start each
# shard on its own host when that host becomes free.
#
#   core-shard.sh split  <tag> <list> <weight-spec>
#   core-shard.sh start  <tag> <shard-index> <host> <core> [tlimit] [min-cap] [min-tlimit] [min-budget]
#
# Two phases because this lane's six cores do NOT free up at the same time: s5
# and s6 are available now and s7 only when the re-derivation sweep releases it.
# Partitioning ONCE, up front, and starting shards later is what keeps two hosts
# from censusing the same file -- the alternative (round-robin now, "the rest"
# later) has no way to know what the running shards have already consumed,
# because `while read` is still holding their lists open.
#
# `weight-spec` is a comma-separated list of integer weights, one per shard.
# Shards that start earlier get the larger weights, so all six finish together.
# Assignment is round-robin by line index over the weights: the lists are
# path-sorted, so contiguous blocks would put one benchmark family on one core.
set -eu
CMD="$1"; TAG="$2"
HERE="$(cd "$(dirname "$0")" && pwd)"
STAGE=/nas3/data/axeyum/harness/core-select/stage
OUTDIR=${CS_COREDIR:-/nas3/data/axeyum/harness/core-select/cores}

case "$CMD" in
split)
  LIST="$3"; WSPEC="$4"
  IFS=',' read -r -a W <<< "$WSPEC"
  mkdir -p "$STAGE" "$OUTDIR"
  cp "$HERE/core-run.sh" "$HERE/core.py" "$HERE/smtsplit.py" "$STAGE/"
  chmod +x "$STAGE/core-run.sh" "$STAGE/core.py"
  rm -f "$STAGE/$TAG".shard*.list
  # expand the weights into a round-robin pattern, e.g. 3,3,2 -> 0 1 2 0 1 2 0 1
  pat=(); for ((s = 0; s < ${#W[@]}; s++)); do for ((r = 0; r < W[s]; r++)); do pat+=("$s"); done; done
  n=0
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    printf '%s\n' "$f" >> "$STAGE/$TAG.shard${pat[n % ${#pat[@]}]}.list"
    n=$((n + 1))
  done < "$LIST"
  echo "$TAG: $n files over ${#W[@]} shards, weights=$WSPEC"
  for ((s = 0; s < ${#W[@]}; s++)); do
    printf '  shard%d weight=%s files=%s\n' "$s" "${W[s]}" \
      "$(wc -l < "$STAGE/$TAG.shard$s.list" 2>/dev/null || echo 0)"
  done
  ;;
start)
  I="$3"; HOST="$4"; CORE="$5"
  TL="${6:-60}"; MINCAP="${7:-64}"; MINTL="${8:-10}"; MINBUD="${9:-600}"
  L="$STAGE/$TAG.shard$I.list"
  [ -f "$L" ] || { echo "ABORT: $L missing -- run split first"; exit 2; }
  ssh -o BatchMode=yes "$HOST" \
    "nohup setsid $STAGE/core-run.sh $L $STAGE/$TAG.shard$I.tsv $CORE $OUTDIR $TL $MINCAP $MINTL $MINBUD \
       > $STAGE/$TAG.shard$I.log 2>&1 < /dev/null &" >/dev/null 2>&1
  echo "started $TAG shard$I on $HOST core $CORE ($(wc -l < "$L") files)"
  ;;
*)
  echo "usage: core-shard.sh split|start ..."; exit 2;;
esac
