#!/usr/bin/env bash
# Reference verdicts (z3 + cvc5) on the same 6 pinned pairs, same budget.
set -u
L=/nas3/data/axeyum/harness/qflra-gap
launch() {  # $1=host $2=shard $3=pin
  ssh -o BatchMode=yes "$1" \
    "nohup setsid bash $L/scripts/ref-run.sh rsh$2 $L/lists/QF_LRA.sh$2.txt \
       $L/out/ref.sh$2.tsv $3 24 > $L/logs/ref.sh$2.log 2>&1 < /dev/null &" \
    && echo "launched ref shard $2 on $1 pin $3"
}
launch s5 0 0,8
launch s5 1 1,9
launch s6 2 0,8
launch s6 3 1,9
launch s7 4 0,8
launch s7 5 1,9
echo "ALL_REF_LAUNCHED"
