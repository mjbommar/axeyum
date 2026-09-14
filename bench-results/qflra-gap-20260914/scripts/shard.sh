#!/usr/bin/env bash
# Round-robin the 200-file board list into 6 shards, so every shard sees a
# comparable mix of hardness (a contiguous split would put whole benchmark
# families on one core).
set -eu
L=/nas3/data/axeyum/harness/qflra-gap
SRC=/nas3/data/axeyum/harness/postmerge-board-dt/lists/BOARD_QF_LRA.txt
for i in 0 1 2 3 4 5; do : > "$L/lists/QF_LRA.sh$i.txt"; done
n=0
while read -r f; do
  [ -z "$f" ] && continue
  echo "$f" >> "$L/lists/QF_LRA.sh$((n % 6)).txt"
  n=$((n + 1))
done < "$SRC"
echo "sharded $n files"
wc -l "$L"/lists/QF_LRA.sh*.txt
