#!/usr/bin/env bash
# One arm of the inprocessing cost sweep over a committed parity list.
#
# Usage:
#   scripts/inprocess-cost-sweep.sh <list.txt> <budget_ms> <arm> <out.jsonl>
#
# Env:
#   SWEEP_CPUS  taskset CPU list for this arm (default 0-5). On the i5-12600K
#               here, CPUs 0-11 are P-cores and 12-15 are E-cores, and the same
#               binary is measured 1.84x slower on an E-core. An arm that
#               floats across both core classes produces a number whose spread
#               is the scheduler, not the pass — so pin, and pin the arms of one
#               comparison to DISTINCT PHYSICAL cores (0, 2, 4: siblings 1, 3, 5
#               left idle) when running them concurrently.
#   MEM_GB      per-file address-space cap (default 8, the parity protocol's).
#
# WHY A SEPARATE DRIVER AND NOT `scripts/parity-run.sh`
#
# parity-run scores us against a reference solver and appends to a ledger; it
# records a verdict per file and nothing about where the time went. This sweep
# needs the opposite: no reference, no ledger, and every backend counter the run
# produced -- specifically the per-pass spend, the budget slice inprocessing was
# granted, and whether each pass returned with that deadline already expired.
# Those three are what separate "the pass is expensive" from "the clock cut the
# pass off after it paid its setup cost", and an aggregate solved-count cannot.
#
# WHAT IT PRINTS ON stderr, AND WHY YOU MUST READ IT
#
#   measured=<n>
#
# An empty or short output file is indistinguishable from a strong negative
# result ("inprocessing changed nothing") unless the count of files actually
# attempted is stated. A run whose `measured=` does not equal the list length is
# not a measurement of that list.
#
# A file that the external `timeout` or the memory cap kills still gets a row,
# stamped `verdict":"killed"`, so the denominator is the whole list exactly as
# the parity protocol requires: killed, unknown and timed-out all count as NOT
# SOLVED, and none of them silently vanishes from the file.
set -uo pipefail

cd "$(dirname "$0")/.."

list="${1:-}"
budget_ms="${2:-}"
arm="${3:-}"
out="${4:-}"
if [[ -z "$list" || -z "$budget_ms" || -z "$arm" || -z "$out" ]]; then
  echo "usage: scripts/inprocess-cost-sweep.sh <list.txt> <budget_ms> <arm> <out.jsonl>" >&2
  exit 2
fi
if [[ ! -f "$list" ]]; then
  echo "FAIL: no benchmark list at $list" >&2
  exit 2
fi

bin="target/release/examples/inprocess_ab"
if [[ ! -x "$bin" ]]; then
  echo "FAIL: missing $bin — build it first:" >&2
  echo "  scripts/cargo-serialized.sh build --release -p axeyum-bench --example inprocess_ab" >&2
  exit 2
fi

cpus="${SWEEP_CPUS:-0-5}"
mem_gb="${MEM_GB:-8}"
# The external kill is the real enforcement; the binary's own watchdog is the
# courtesy that lets it print an honest `unknown` first. Same split as
# parity-run.sh, and for the same reason: a solver killed mid-parse prints
# nothing at all, and nothing is not a verdict.
kill_after=$(( budget_ms / 1000 + 15 ))

echo "sweep arm=$arm budget_ms=$budget_ms cpus=$cpus load_start=$(cut -d' ' -f1-3 /proc/loadavg)" >&2

: > "$out"
attempted=0
while IFS= read -r file; do
  [[ -z "${file// }" ]] && continue
  attempted=$(( attempted + 1 ))
  if ! MEM_LIMIT_GB="$mem_gb" timeout "$kill_after" \
       taskset -c "$cpus" ./scripts/mem-run.sh "$bin" "$file" "$budget_ms" "$arm" \
       >>"$out" 2>/dev/null; then
    printf '{"file":"%s","arm":"%s","budget_ms":%s,"verdict":"killed","wall_ms":0,"counters":{}}\n' \
      "$file" "$arm" "$budget_ms" >>"$out"
  fi
done <"$list"

rows=$(grep -c '"verdict"' "$out")
echo "sweep arm=$arm measured=$attempted rows=$rows load_end=$(cut -d' ' -f1-3 /proc/loadavg)" >&2
# A row per attempted file, or the run is not a measurement of this list.
if [[ "$rows" != "$attempted" ]]; then
  echo "FAIL: $rows rows for $attempted attempted files — output is incomplete" >&2
  exit 1
fi
