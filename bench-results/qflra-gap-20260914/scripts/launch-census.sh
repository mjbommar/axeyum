#!/usr/bin/env bash
# Launch the 6-shard QF_LRA census: 2 pinned pairs on each of s5, s6, s7.
#
# TWO shards per host, not three: the OOM files in this division reach ~7.8 GiB
# RSS against the 8 GiB `ulimit -v`, and these hosts have 27 GiB. Three
# concurrent shards could put 24 GiB of live RSS on a 27 GiB box and have the
# kernel OOM-killer decide which lane dies. Two caps live RSS at ~16 GiB.
set -u
L=/nas3/data/axeyum/harness/qflra-gap
BIN=$L/bin/smtcomp_cli-cfcae7fa7

launch() {  # $1=host $2=shard $3=pin
  ssh -o BatchMode=yes "$1" \
    "nohup setsid bash $L/scripts/census-run.sh sh$2 $L/lists/QF_LRA.sh$2.txt \
       $L/out/census.sh$2.tsv $L/logs/sh$2 $3 $BIN 24 \
       > $L/logs/census.sh$2.log 2>&1 < /dev/null &" \
    && echo "launched shard $2 on $1 pin $3"
}

launch s5 0 0,8
launch s5 1 1,9
launch s6 2 0,8
launch s6 3 1,9
launch s7 4 0,8
launch s7 5 1,9
echo "ALL_LAUNCHED"
