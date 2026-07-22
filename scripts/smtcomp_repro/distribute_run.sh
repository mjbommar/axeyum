#!/usr/bin/env bash
# Distribute an axeyum inventory run across the s4..s7 /nas3-mounted hosts.
#
# Shards a benchmark file-list across N worker processes spread over the hosts
# (one process per assigned shard), each dumping raw results to a shared /nas3
# output dir. Execution is hardware-bound and parallel; scoring/merging is done
# centrally afterward (inventory.py) — the SMT-COMP BenchExec -> central-tool split.
#
# Usage:
#   distribute_run.sh <file_list> <ceiling_s> <out_dir> [tag]
set -euo pipefail

FILELIST="$1"; CEILING="$2"; OUTDIR="$3"; TAG="${4:-run}"
H=/nas3/data/axeyum/harness
BIN=$H/bin/axeyum-smtcomp
INT=$(( CEILING * 1000 - 1000 ))
mkdir -p "$OUTDIR"

# host plan: name first_shard n_workers mem_gb  (total shards = sum of n_workers)
# Thermally-limited: these boxes hit 92-99C at full core load, so we cap workers
# per host well below core count to hold temps under ~80C (verified live).
PLAN=(
  "s4 0 8 8"
)
NSHARDS=8

echo "distributing $TAG: $(wc -l < "$FILELIST") files, ${CEILING}s ceiling, $NSHARDS shards -> $OUTDIR"
for entry in "${PLAN[@]}"; do
  read -r host first n mem <<<"$entry"
  last=$(( first + n - 1 ))
  ssh -o BatchMode=yes "$host" bash -s <<REMOTE 2>&1 | sed "s/^/[$host] /"
cd $H
export RAYON_NUM_THREADS=1 OMP_NUM_THREADS=1 AYU_THREADS=1
for s in \$(seq $first $last); do
  nohup python3 smtcomp_repro/compete.py \
    --file-list $FILELIST --shard \${s}/$NSHARDS \
    --solver axeyum=$BIN \
    --wall-limit $CEILING --internal-timeout-ms $INT --mem-gb $mem \
    --dump-raw $OUTDIR/raw_\${s}.json \
    > $OUTDIR/log_\${s}.log 2>&1 &
done
echo "launched shards $first..$last (mem ${mem}GB); running=\$(pgrep -cf 'compete.py --file-list')"
REMOTE
done
echo "all workers launched. shards expected: $NSHARDS ; watch $OUTDIR/raw_*.json"
