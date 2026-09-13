#!/usr/bin/env bash
# Run a QUEUE of divisions in sequence on one box, two shards each on distinct
# physical cores 5 and 6 (logical 5,13 and 6,14).
#
# NOT 0,8 and 2,10, which is what board-six used and what this lane launched
# with at 07:13.  `loadframe.sh` reported 3-4 FOREIGN taskset pins immediately
# and `ps -eo args` named them: a concurrent `quant-rounds` lane pinned to
# logical 0 and 2, and a `nested-array-ir` lane pinned to logical 4.  Logical 0
# and 2 are the SAME PHYSICAL CORES as 0,8 and 2,10, so both of this board's
# shards were sharing a core with another lane's solver.  The run was stopped
# and relaunched here; cores 5 and 6 were unoccupied by any lane.
#
# The per-file interleaving means ambient drift cancels in the DIFFERENCE
# between solvers either way -- but the ABSOLUTE counts are this lane's
# deliverable (it exists to confirm or refute seven probe rates), and a
# contended core depresses all three absolutely.
#
# Seven divisions over three boxes at two shards per box means a box takes two
# or three divisions one after the other; running more at once would need more
# shards per box and the 8 GiB per-run cap makes three shards a 24 GiB peak on
# a 26 GB box.
#
# Usage: chain-run.sh <div> [<div> ...]
set -u
H=/nas3/data/axeyum/harness/tier1-divisions
for d in "$@"; do
  "$H/shard-run.sh" "$d.s0" "$H/lists/$d.s0" "$H/out/$d.s0.tsv" 5,13 \
    > "$H/out/$d.s0.log" 2>&1 &
  p0=$!
  "$H/shard-run.sh" "$d.s1" "$H/lists/$d.s1" "$H/out/$d.s1.tsv" 6,14 \
    > "$H/out/$d.s1.log" 2>&1 &
  p1=$!
  wait $p0 $p1
  echo "CHAIN: $d complete on $(hostname) at $(date +%H:%M:%S)"
done
echo "CHAIN-DONE $* on $(hostname)"
