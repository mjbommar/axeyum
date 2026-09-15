#!/usr/bin/env bash
# Launch the 6-shard DENSE74 budget-attribution run: 2 pinned pairs per host.
set -u
L=/nas3/data/axeyum/harness/lra-dense
BIN=$L/bin/smtcomp_cli-4abc994a0

launch() {  # $1=host $2=shard $3=pin
  ssh -o BatchMode=yes "$1" \
    "nohup setsid bash $L/scripts/attrib-run.sh sh$2 $L/lists/DENSE74.sh$2.txt \
       $L/out/attrib.sh$2.tsv $L/logs/attrib-sh$2 $3 $BIN 24 \
       > $L/logs/attrib.sh$2.log 2>&1 < /dev/null &" \
    && echo "launched attrib shard $2 on $1 pin $3"
}

launch s5 0 0,8
launch s5 1 1,9
launch s6 2 0,8
launch s6 3 1,9
launch s7 4 0,8
launch s7 5 1,9
echo "ALL_LAUNCHED"
