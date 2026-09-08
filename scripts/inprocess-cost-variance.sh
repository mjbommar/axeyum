#!/usr/bin/env bash
# Repeat the SAME file, SAME arm, SAME budget N times and record every run.
#
# Usage:
#   scripts/inprocess-cost-variance.sh <files.txt> <budget_ms> <arm> <repeats> <out.jsonl>
#
# WHAT THIS SEPARATES
#
# Two explanations produce the same aggregate "inprocessing does not pay off
# inside 24 s", and they call for opposite work:
#
#   (A) the passes are simply expensive at any budget. Then repeated identical
#       runs agree, and the break-even is a property of the pass.
#   (B) a wall-clock cutoff halts a pass part-way, after it has paid its setup
#       cost and before it collects the benefit. Then the SAME instance at the
#       SAME budget gives materially different results run to run, and the
#       spread tracks host load.
#
# A mean over one run each cannot tell them apart. The spread can, and so can
# the `*_deadline_expired` counters each row carries — which is why this records
# every repeat rather than reducing them to a mean.
#
# The repeats of one file run BACK TO BACK (file outer, repeat inner) rather
# than as N passes over the whole list. Either arrangement is defensible, and
# this one is chosen because a slow drift in host load then falls on all five
# repeats of a file roughly equally, instead of separating repeat 1 from repeat
# 5 by the length of the whole sweep and reporting that drift as the pass's own
# variance. Each row records the 1-minute load it ran under, so the choice is
# checkable rather than assumed.
#
# `taskset` is not optional. On the i5-12600K here CPUs 12-15 are E-cores and
# the same binary is 1.84x slower on one, so an unpinned repeat set measures the
# scheduler's core choice and reports it as run-to-run spread.
set -uo pipefail

cd "$(dirname "$0")/.."

files="${1:-}"
budget_ms="${2:-}"
arm="${3:-}"
repeats="${4:-5}"
out="${5:-}"
if [[ -z "$files" || -z "$budget_ms" || -z "$arm" || -z "$out" ]]; then
  echo "usage: scripts/inprocess-cost-variance.sh <files.txt> <budget_ms> <arm> <repeats> <out.jsonl>" >&2
  exit 2
fi

bin="target/release/examples/inprocess_ab"
if [[ ! -x "$bin" ]]; then
  echo "FAIL: missing $bin" >&2
  exit 2
fi

cpus="${SWEEP_CPUS:-0-5}"
mem_gb="${MEM_GB:-8}"
kill_after=$(( budget_ms / 1000 + 15 ))

echo "variance arm=$arm budget_ms=$budget_ms repeats=$repeats cpus=$cpus load_start=$(cut -d' ' -f1-3 /proc/loadavg)" >&2

: > "$out"
expected=0
while IFS= read -r file; do
  [[ -z "${file// }" ]] && continue
  for (( r = 1; r <= repeats; r++ )); do
    expected=$(( expected + 1 ))
    # The repeat index rides along in the row so a later reader can tell a
    # first run from a fifth without re-deriving it from line order.
    line=$(MEM_LIMIT_GB="$mem_gb" timeout "$kill_after" \
           taskset -c "$cpus" ./scripts/mem-run.sh "$bin" "$file" "$budget_ms" "$arm" 2>/dev/null)
    if [[ -z "$line" ]]; then
      line=$(printf '{"file":"%s","arm":"%s","budget_ms":%s,"verdict":"killed","wall_ms":0,"counters":{}}' \
             "$file" "$arm" "$budget_ms")
    fi
    printf '%s\n' "${line%\}}, \"repeat\": $r, \"load\": $(cut -d' ' -f1 /proc/loadavg)}" >>"$out"
  done
done <"$files"

rows=$(grep -c '"verdict"' "$out")
echo "variance arm=$arm expected=$expected rows=$rows load_end=$(cut -d' ' -f1-3 /proc/loadavg)" >&2
if [[ "$rows" != "$expected" ]]; then
  echo "FAIL: $rows rows for $expected expected runs" >&2
  exit 1
fi
