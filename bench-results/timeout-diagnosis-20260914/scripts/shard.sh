#!/usr/bin/env bash
# Round-robin the 200-file QF_LRA board into 4 shards.
#
# Round-robin and not a contiguous split: the board list is path-sorted, so a
# contiguous split puts whole benchmark families on one core and each shard then
# measures a different population's hardness rather than a quarter of the same
# one.
#
# FOUR and not six: this lane needs very little compute and shares the hosts
# with two other lanes, so it takes 4 pinned pairs (s5 0,8 / s5 1,9 / s6 0,8 /
# s7 0,8) rather than all six.
set -eu
L=/nas3/data/axeyum/harness/timeout-diagnosis
SRC=/nas3/data/axeyum/harness/postmerge-board-dt/lists/BOARD_QF_LRA.txt
mkdir -p "$L/lists" "$L/out" "$L/logs" "$L/bin"
for i in 0 1 2 3; do : > "$L/lists/QF_LRA.sh$i.txt"; done
n=0
while read -r f; do
  [ -z "$f" ] && continue
  echo "$f" >> "$L/lists/QF_LRA.sh$((n % 4)).txt"
  n=$((n + 1))
done < "$SRC"
echo "sharded $n files"
wc -l "$L"/lists/QF_LRA.sh*.txt
