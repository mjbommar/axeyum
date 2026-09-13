#!/usr/bin/env bash
# Launch the Tier-1 board: two shards per box on distinct physical cores
# (0,8) and (2,10) -- a Ryzen 7 7840HS is 8 physical cores with SMT siblings at
# +8, so those two pins do not share a core.
#
# SEVEN divisions over THREE boxes does not divide.  Rather than give one box a
# permanent 50 % overhang, six are launched two per box and the seventh (FP) is
# dispatched by `launch-fp.sh` to whichever box finishes its pair first.  Every
# solver on a given file still runs back to back on the same pinned core, which
# is what the comparison rests on; which box a division landed on does not
# enter any per-file difference.
#
# Pairing: the two monsters (AUFLIRA 20,011 files, UFNIA 13,464) start first,
# each with a smaller partner behind it.
set -eu
H=/nas3/data/axeyum/harness/tier1-divisions

launch() { # $1 host  $2... divisions
  local host="$1"; shift
  ssh -o BatchMode=yes "$host" \
    "nohup $H/chain-run.sh $* > $H/out/chain.$host.log 2>&1 & sleep 1; \
     echo launched $* on \$(hostname)"
}

launch s5 AUFLIRA AUFBV
launch s6 UFNIA AUFNIRA
launch s7 ABV ALIA
