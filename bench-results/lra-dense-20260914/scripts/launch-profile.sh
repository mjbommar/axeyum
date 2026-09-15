#!/usr/bin/env bash
# Launch the 6-shard DENSE74 profile: 2 pinned pairs on each of s5, s6, s7.
#
# TWO shards per host, not three, for ADR-2045's measured reason: the OOM rows in
# this division reach ~7.8 GiB against the 8 GiB `ulimit -v`, and these hosts
# have 27 GiB. Three concurrent shards could put 24 GiB of live RSS on a 27 GiB
# box and let the kernel OOM killer choose which lane dies.
#
# All three hosts read load average 0.00-0.09 before launch.
set -u
L=/nas3/data/axeyum/harness/lra-dense
BIN=$L/bin/smtcomp_cli-4abc994a0

launch() {  # $1=host $2=shard $3=pin
  ssh -o BatchMode=yes "$1" \
    "nohup setsid bash $L/scripts/profile-run.sh sh$2 $L/lists/DENSE74.sh$2.txt \
       $L/out/profile.sh$2.tsv $L/logs/prof-sh$2 $3 $BIN 24 \
       > $L/logs/profile.sh$2.log 2>&1 < /dev/null &" \
    && echo "launched profile shard $2 on $1 pin $3"
}

launch s5 0 0,8
launch s5 1 1,9
launch s6 2 0,8
launch s6 3 1,9
launch s7 4 0,8
launch s7 5 1,9
echo "ALL_LAUNCHED"
