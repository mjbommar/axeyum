#!/usr/bin/env bash
set -u
L=/nas3/data/axeyum/harness/qflra-gap
SRC="$L/lists/admission-screen.txt"
for i in 0 1 2 3 4 5; do : > "$L/lists/reach.sh$i.txt"; done
n=0
while read -r f; do
  [ -z "$f" ] && continue
  echo "$f" >> "$L/lists/reach.sh$((n % 6)).txt"
  n=$((n + 1))
done < "$SRC"
echo "sharded $n reach files"
launch() {
  ssh -o BatchMode=yes "$1" \
    "nohup setsid bash $L/scripts/reached-probe.sh $L/lists/reach.sh$2.txt \
       $L/out/reach.sh$2.tsv $3 8192 > $L/logs/reach.sh$2.log 2>&1 < /dev/null &" \
    && echo "launched reach shard $2 on $1 pin $3"
}
launch s5 0 0,8
launch s5 1 1,9
launch s6 2 0,8
launch s6 3 1,9
launch s7 4 0,8
launch s7 5 1,9
echo "ALL_REACH_LAUNCHED"
