#!/usr/bin/env bash
# Round-robin any board division into the same 6 shards.
# Usage: shard-div.sh <DIVISION>
set -eu
L=/nas3/data/axeyum/harness/qflra-gap
DIV="$1"
SRC=/nas3/data/axeyum/harness/postmerge-board-dt/lists/BOARD_$DIV.txt
[ -f "$SRC" ] || { echo "no such list: $SRC"; exit 2; }
for i in 0 1 2 3 4 5; do : > "$L/lists/$DIV.sh$i.txt"; done
n=0
while read -r f; do
  [ -z "$f" ] && continue
  echo "$f" >> "$L/lists/$DIV.sh$((n % 6)).txt"
  n=$((n + 1))
done < "$SRC"
echo "sharded $DIV: $n files"
