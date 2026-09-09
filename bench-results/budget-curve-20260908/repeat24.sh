#!/usr/bin/env bash
# Second 24 s pass, run AFTER the 60 s pass finishes, on whatever the box looks
# like then. Two jobs:
#   1. it is a load-matched partner for the 60 s row, so the 24 -> 60 increment
#      is not read off two different machines;
#   2. 24 vs 24-repeat on the same list, same binary, same day IS the
#      contention noise floor for this whole exercise.
set -uo pipefail
div="${1:?usage: repeat24.sh <division>}"
root="${2:-$HOME/axeyum-budget-curve}"
out="$HOME/budget-curve-out"
log="$HOME/budget-curve-${div}.log"
mkdir -p "$out" || exit 2
# Wait for the first driver to finish; never run two sweeps of one division.
for _ in $(seq 1 720); do
  if grep -Fq "### ALLDONE ${div}" "$log" 2>/dev/null; then break; fi
  sleep 60
done
if ! grep -Fq "### ALLDONE ${div}" "$log" 2>/dev/null; then
  echo "### REPEAT24 ${div} ABORTED — first driver never printed ALLDONE"
  exit 2
fi
cd "$root" || exit 2
export AXEYUM_AGENT=budget-curve
echo "### ${div} budget=24-REPEAT START $(date -u +%Y-%m-%dT%H:%M:%SZ) load=$(cut -d' ' -f1-3 /proc/loadavg)"
PARITY_BUDGET_S=24 PARITY_MEM_GB=8 ./scripts/parity-run.sh "$div"
rc=$?
echo "### ${div} budget=24-REPEAT END rc=${rc} $(date -u +%Y-%m-%dT%H:%M:%SZ) load=$(cut -d' ' -f1-3 /proc/loadavg)"
cp "bench-results/parity-details/${div}.tsv" "${out}/${div}-b24r.tsv" 2>/dev/null
cp bench-results/PARITY.md "${out}/${div}-PARITY.md"
echo "### REPEATDONE ${div} $(date -u +%Y-%m-%dT%H:%M:%SZ)"
