#!/usr/bin/env bash
# Launch the interleaved A/B on the 4 pinned pairs named in PREREGISTRATION.md R7.
set -u
L=/nas3/data/axeyum/harness/timeout-diagnosis
BASE=$L/bin/smtcomp_cli-base-91c721f8e
ARM=$L/bin/smtcomp_cli-arm-3f587710a
launch() {  # $1=host $2=shard $3=pin
  ssh -o BatchMode=yes -- "$1" \
    "nohup setsid bash $L/scripts/ab-run.sh ab-$2 $L/lists/QF_LRA.sh$2.txt \
       $L/out/ab.QF_LRA.sh$2.tsv $L/logs/raw.sh$2 $3 $BASE $ARM 24 \
       > $L/logs/ab.sh$2.log 2>&1 < /dev/null &" \
    && echo "launched shard $2 on $1 pin $3"
}
launch s5 0 0,8
launch s5 1 1,9
launch s6 2 0,8
launch s7 3 0,8
echo "ALL_AB_LAUNCHED"
