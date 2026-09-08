#!/usr/bin/env bash
# One arm of the subsumption work-meter sweep.
#
# Usage:
#   scripts/subsume-meter-sweep.sh <arm-label> <harness-arm> <cpu> <out.jsonl>
#
# `arm-label` selects the levers; `harness-arm` is what `inprocess_ab` is asked
# for (off / inproc / inproc-vivify). The levers are environment variables read
# by `sat_bv_backend`, so every arm is the SAME BINARY -- a sweep that compared
# two builds would have to argue their differences were irrelevant, and this one
# does not have to.
#
# Arms:
#   off              baseline, no inprocessing at all
#   base             shipped defaults: BVE budgeted at 2000 x setup, subsumption
#                    unbudgeted, no compaction. Also the CALIBRATION arm for
#                    pricing a subsumption budget.
#   bve-free         BVE unbudgeted, no compaction -- the "neither fix" point
#   bve-free-compact BVE unbudgeted WITH occurrence-list compaction: compaction
#                    alone, so it can be compared against budgeting alone
#   bve-budget-compact  both fixes
#   subsume-gated    shipped defaults plus the subsumption budget under test
#                    (SUBSUME_K in the environment, default the shipped constant)
set -uo pipefail
cd "$(dirname "$0")/.."

label="${1:?arm-label}"
harness_arm="${2:?harness-arm}"
cpu="${3:?cpu}"
out="${4:?out.jsonl}"
list="${LIST:-bench-results/parity-lists/QF_BV.txt}"
budget_ms="${BUDGET_MS:-24000}"

case "$label" in
  off|base) ;;
  bve-free)            export AXEYUM_BVE_BUDGET_MULTIPLE=off ;;
  bve-free-compact)    export AXEYUM_BVE_BUDGET_MULTIPLE=off AXEYUM_OCC_COMPACT=1 ;;
  bve-budget-compact)  export AXEYUM_OCC_COMPACT=1 ;;
  subsume-gated)       export AXEYUM_SUBSUME_BUDGET_MULTIPLE="${SUBSUME_K:?SUBSUME_K required}" ;;
  subsume-gated-compact)
                       export AXEYUM_SUBSUME_BUDGET_MULTIPLE="${SUBSUME_K:?SUBSUME_K required}"
                       export AXEYUM_OCC_COMPACT=1 ;;
  *) echo "FAIL: unknown arm label $label" >&2; exit 2 ;;
esac

echo "arm=$label harness=$harness_arm cpu=$cpu" \
     "bve_mult=${AXEYUM_BVE_BUDGET_MULTIPLE:-shipped}" \
     "subsume_mult=${AXEYUM_SUBSUME_BUDGET_MULTIPLE:-shipped}" \
     "compact=${AXEYUM_OCC_COMPACT:-shipped}" >&2

SWEEP_CPUS="$cpu" exec scripts/inprocess-cost-sweep.sh "$list" "$budget_ms" "$harness_arm" "$out"
