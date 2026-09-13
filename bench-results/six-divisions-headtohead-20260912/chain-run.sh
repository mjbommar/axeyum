#!/usr/bin/env bash
# Run TWO divisions in sequence on one box, two shards each on distinct
# physical cores.  Six divisions over three boxes at two shards per box means
# each box takes two divisions one after the other; running all six at once
# would need three shards per box and the 8 GiB per-run cap makes that a 24 GiB
# peak on a 26 GB box.
#
# Usage: chain-run.sh <divA> <divB>
set -u
H=/nas3/data/axeyum/harness/six-divisions
for d in "$1" "$2"; do
  "$H/shard-run.sh" "$d.s0" "$H/lists/$d.s0" "$H/out/$d.s0.tsv" 0,8 \
    > "$H/out/$d.s0.log" 2>&1 &
  p0=$!
  "$H/shard-run.sh" "$d.s1" "$H/lists/$d.s1" "$H/out/$d.s1.tsv" 2,10 \
    > "$H/out/$d.s1.log" 2>&1 &
  p1=$!
  wait $p0 $p1
  echo "CHAIN: $d complete on $(hostname) at $(date +%H:%M:%S)"
done
echo "CHAIN-DONE $1 $2 on $(hostname)"
