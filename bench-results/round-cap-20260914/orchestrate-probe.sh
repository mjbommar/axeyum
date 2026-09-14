#!/usr/bin/env bash
# ADR-2035 GATE 0 -- launch the ordered probe over the whole 129-file population.
#
# FOUR pinned cores on s7, both arms inside the one host so a host can never move
# one arm relative to the other. The A/B that follows uses eight, and the two
# phases are SEQUENTIAL, so peak concurrent pinned cores is eight.
#
# OFF arm (cores 1, 3) is the SHIPPED build: it yields the crossing census and,
# from the same stderr stream, the CEGAR round distribution over the WHOLE
# population -- including the rows that decide, which the committed census
# structurally cannot cover.
# ON arm (cores 5, 7) answers the only question that can justify an A/B: does the
# rescue, when offered, ever DECIDE?
set -eu
DEST=/tmp/round-cap
ssh -o BatchMode=yes s7 "cd $DEST && rm -f ab/probe-*.tsv ab/probe-*.log ab/probe-*.fcprobe.log"
launch() {
  local shard="$1" core="$2" mode="$3"
  ssh -o BatchMode=yes s7 "cd $DEST && nohup setsid ./probe-run.sh \
      lists/main-129-half.shard${shard}.txt ab/probe-${mode}.shard${shard}.tsv ${core} \
      ./smtcomp_cli ${mode} 24 > ab/probe-${mode}.shard${shard}.log 2>&1 < /dev/null &" \
    && echo "launched probe ${mode} shard${shard} on s7 core ${core}"
}
launch 0 1 off
launch 1 3 off
launch 0 5 on
launch 1 7 on
