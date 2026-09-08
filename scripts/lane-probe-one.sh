#!/usr/bin/env bash
# Run one benchmark through the inprocessing A/B harness and print its
# subsumption / BVE counters. A lane helper for probing a single file, not a
# sweep: `scripts/inprocess-cost-sweep.sh` is the sweep.
#
# Usage: scripts/lane-probe-one.sh <file.smt2> <budget_ms> <arm> [cpu]
set -uo pipefail
cd "$(dirname "$0")/.."

file="${1:?file}"
budget_ms="${2:?budget_ms}"
arm="${3:?arm}"
cpu="${4:-0}"

bin="target/release/examples/inprocess_ab"
if [[ ! -x "$bin" ]]; then
  echo "FAIL: missing $bin" >&2
  exit 2
fi

taskset -c "$cpu" "$bin" "$file" "$budget_ms" "$arm" 2>/dev/null
