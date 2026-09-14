#!/usr/bin/env bash
set -u
L=/nas3/data/axeyum/harness/qflra-gap
for i in 0 1 2 3 4 5; do : > "$L/lists/nobody.sh$i.txt"; done
n=0
while read -r f; do
  [ -z "$f" ] && continue
  echo "$f" >> "$L/lists/nobody.sh$((n % 6)).txt"
  n=$((n + 1))
done < "$L/lists/nobody.txt"
echo "sharded $n nobody-rows"
rm -f "$L"/out/nobody.sh*.tsv
launch() {
  ssh -o BatchMode=yes "$1" \
    "nohup setsid bash $L/scripts/recheck-nobody.sh $L/lists/nobody.sh$2.txt \
       $L/out/nobody.sh$2.tsv $3 > $L/logs/nobody.sh$2.log 2>&1 < /dev/null &" \
    && echo "launched nobody-recheck shard $2 on $1 pin $3"
}
launch s5 0 0,8
launch s5 1 1,9
launch s6 2 0,8
launch s6 3 1,9
launch s7 4 0,8
launch s7 5 1,9
echo "ALL_RECHECK_LAUNCHED"
