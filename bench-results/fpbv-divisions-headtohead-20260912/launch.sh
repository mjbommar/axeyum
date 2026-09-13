#!/usr/bin/env bash
# Launch the six board shards: one division per idle homogeneous box, two
# modulo-interleaved shards per box on DISTINCT physical cores (0,8) and (2,10)
# -- a Ryzen 7 7840HS is 8 physical cores with SMT siblings at +8, so those two
# pins do not share a core.
#
# Two shards per box, not three: the 8 GiB address-space cap is per run and
# these boxes have 26 GB.
#
# Shards are NR%2 through the pinned list, so each shard spans the whole
# division; the merged TSV is re-ordered back into the pinned list's order, so
# the artifact does not encode the shard split.
set -eu
H=/nas3/data/axeyum/harness/fpbv-divisions

launch() { # $1 host  $2 division
  local host="$1" div="$2"
  ssh -o BatchMode=yes "$host" \
    "nohup $H/shard-run.sh $div.s0 $H/lists/$div.s0 $H/out/$div.s0.tsv 0,8 \
       > $H/out/$div.s0.log 2>&1 &
     nohup $H/shard-run.sh $div.s1 $H/lists/$div.s1 $H/out/$div.s1.tsv 2,10 \
       > $H/out/$div.s1.log 2>&1 &
     sleep 1; echo launched $div on \$(hostname)"
}

launch s5 QF_ABVFP
launch s6 QF_BVFP
launch s7 QF_UFBV
