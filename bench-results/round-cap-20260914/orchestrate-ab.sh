#!/usr/bin/env bash
# ADR-2035 -- launch the interleaved A/B on EIGHT pinned cores across three hosts.
#
# Shard configuration, FIXED ACROSS ARMS and stated here rather than inferred:
#
#   main        s5 cores 1, 3, 5, 7   main-129, AXEYUM_PRESAT_RESCUE=1
#   control     s6 cores 1, 3         control-qflia-200, same lever
#   noise floor s7 cores 1, 3         main-129, AXEYUM_NOT_A_LEVER=1
#
# Both arms of every pair run INSIDE one shard on one core, back to back, with
# the order rotating per file, so a shard or a host can never move one arm
# relative to the other.
#
# The noise floor uses a variable NO code reads. Both flags in this lane fail
# CLOSED, so an unrecognised name degenerates to a second copy of the shipped
# arm -- which is exactly what a same-arm band measurement is.
set -eu
DEST=/tmp/round-cap
launch() {
  local host="$1" list="$2" out="$3" core="$4" var="$5" value="$6"
  ssh -o BatchMode=yes "$host" "cd $DEST && nohup setsid ./ab-run.sh \
      lists/${list} ab/${out}.tsv ${core} ./smtcomp_cli ${var} ${value} 24 \
      > ab/${out}.log 2>&1 < /dev/null &" \
    && echo "launched ${out} on ${host} core ${core} (${var}=${value})"
}
for h in s5 s6 s7; do
  ssh -o BatchMode=yes "$h" "cd $DEST && rm -f ab/main-*.tsv ab/main-*.log ab/control-*.tsv ab/control-*.log ab/noise-*.tsv ab/noise-*.log"
done
launch s5 main-129.shard0.txt main.shard0 1 AXEYUM_PRESAT_RESCUE 1
launch s5 main-129.shard1.txt main.shard1 3 AXEYUM_PRESAT_RESCUE 1
launch s5 main-129.shard2.txt main.shard2 5 AXEYUM_PRESAT_RESCUE 1
launch s5 main-129.shard3.txt main.shard3 7 AXEYUM_PRESAT_RESCUE 1
launch s6 control-qflia-200.shard0.txt control.shard0 1 AXEYUM_PRESAT_RESCUE 1
launch s6 control-qflia-200.shard1.txt control.shard1 3 AXEYUM_PRESAT_RESCUE 1
launch s7 main-129-half.shard0.txt noise.shard0 1 AXEYUM_NOT_A_LEVER 1
launch s7 main-129-half.shard1.txt noise.shard1 3 AXEYUM_NOT_A_LEVER 1
