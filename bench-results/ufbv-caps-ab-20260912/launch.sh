#!/usr/bin/env bash
# Launch the QF_UFBV cap A/B: 6 shards, 2 per box on DISTINCT PHYSICAL CORES.
#
# Two shards per box, not three: the 8 GiB address-space cap is per RUN and
# these boxes have 26 GB, so three concurrent shards can reach 24 GiB.
# Ryzen 7 7840HS is 8 physical cores with SMT siblings at +8, so `0,8` is one
# physical core and `2,10` is another.
set -u
H=/nas3/data/axeyum/harness/ufbv-caps
LIST="$1"; TAG="$2"; shift 2
ARMS=("$@")
mkdir -p "$H/out/$TAG" "$H/log/$TAG"
i=0
for host in s5 s6 s7; do
  for pin in 0,8 2,10; do
    ssh -o BatchMode=yes -n "$host" \
      "nohup setsid $H/ab-run.sh $i 6 $LIST $pin $H/out/$TAG/shard$i.tsv $(printf '%q ' "${ARMS[@]}") \
       > $H/log/$TAG/shard$i.log 2>&1 < /dev/null &" &
    echo "launched shard $i on $host pin $pin"
    i=$((i + 1))
  done
done
wait
echo "all 6 shards launched for $TAG"
