#!/usr/bin/env bash
# budget-curve lane: solved-count-versus-budget sweep for one division.
# Runs the committed protocol harness at four budgets, headline (24s) FIRST so
# an interrupted run still yields the externally comparable number.
set -uo pipefail
div="${1:?usage: driver.sh <division>}"
root="$HOME/axeyum-budget-curve"
out="$HOME/budget-curve-out"
mkdir -p "$out" || exit 2
cd "$root" || exit 2
export AXEYUM_AGENT=budget-curve
for b in 24 6 12 60; do
  echo "### ${div} budget=${b} START $(date -u +%Y-%m-%dT%H:%M:%SZ) load=$(cut -d' ' -f1-3 /proc/loadavg)"
  PARITY_BUDGET_S="$b" PARITY_MEM_GB=8 ./scripts/parity-run.sh "$div"
  rc=$?
  echo "### ${div} budget=${b} END rc=${rc} $(date -u +%Y-%m-%dT%H:%M:%SZ) load=$(cut -d' ' -f1-3 /proc/loadavg)"
  cp "bench-results/parity-details/${div}.tsv" "${out}/${div}-b${b}.tsv" 2>/dev/null
done
cp bench-results/PARITY.md "${out}/${div}-PARITY.md"
echo "### ALLDONE ${div} $(date -u +%Y-%m-%dT%H:%M:%SZ)"
