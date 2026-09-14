#!/usr/bin/env bash
# Launch the interleaved A/B on the 6 pinned pairs.
# Usage: launch-ab.sh <division> <arm_mb>
set -u
L=/nas3/data/axeyum/harness/qflra-gap
BIN=$L/bin/smtcomp_cli-cfcae7fa7
DIV="$1"; ARM="$2"
launch() {  # $1=host $2=shard $3=pin
  ssh -o BatchMode=yes "$1" \
    "nohup setsid bash $L/scripts/ab-run.sh ab-$DIV-$2 $L/lists/$DIV.sh$2.txt \
       $L/out/ab.$DIV.sh$2.tsv $3 $BIN $ARM 24 \
       > $L/logs/ab.$DIV.sh$2.log 2>&1 < /dev/null &" \
    && echo "launched ab $DIV shard $2 on $1 pin $3"
}
launch s5 0 0,8
launch s5 1 1,9
launch s6 2 0,8
launch s6 3 1,9
launch s7 4 0,8
launch s7 5 1,9
echo "ALL_AB_LAUNCHED div=$DIV arm_mb=$ARM"
