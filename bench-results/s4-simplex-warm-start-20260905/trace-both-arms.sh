#!/usr/bin/env bash
# Emits the `; theory-layer …` line from both arms for each traced file,
# interleaved, so the load a shared host is under is the same for the pair.
#
# Usage: trace-both-arms.sh <before_binary> <after_binary> <filelist> <out.txt>
#
# The BEFORE binary predates S4's `engine_counters`, so its line carries no
# `simplex_*` / `bound_*` / `propagations_offered` fields at all. That absence is
# the honest record: those counters did not exist in that arm, and printing `0`
# for them would be a fabricated measurement.
set -uo pipefail

before_bin=$1
after_bin=$2
filelist=$3
out=$4

while read -r file; do
  [ -z "$file" ] && continue
  {
    echo "=== $file"
    echo "--- load $(cut -d' ' -f1 /proc/loadavg)"
    echo -n "before: "
    taskset -c 0-7 "$before_bin" "$file" --timeout-ms 24000 --trace 2>/dev/null | tail -2 | tr '\n' ' '
    echo
    echo -n "after:  "
    taskset -c 0-7 "$after_bin" "$file" --timeout-ms 24000 --trace 2>/dev/null | tail -2 | tr '\n' ' '
    echo
  } >>"$out"
  echo "traced $(basename "$file")" >&2
done <"$filelist"
