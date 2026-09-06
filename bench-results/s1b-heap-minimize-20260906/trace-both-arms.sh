#!/usr/bin/env bash
# S1b traced runs on the five profiled QF_IDL files, both arms, interleaved.
# usage: trace.sh <listfile> <start> <count> <rep> <outfile>
set -uo pipefail
list="$1"; start="$2"; count="$3"; rep="$4"; out="$5"
B="$HOME/s1b-before/target/release/examples/smtcomp_cli"
A="$HOME/s1b-after/target/release/examples/smtcomp_cli"
sed -n "$((start+1)),$((start+count))p" "$list" | while IFS= read -r f; do
  for arm in before after; do
    case $arm in before) bin="$B";; after) bin="$A";; esac
    t0=$(date +%s%N)
    raw=$(MEM_LIMIT_GB=8 taskset -c 0-7 timeout 29 "$bin" "$f" --timeout-ms 24000 --trace 2>&1)
    t1=$(date +%s%N)
    echo "### $(basename "$f") [$arm rep=$rep] wall_ms=$(( (t1-t0)/1000000 ))" >> "$out"
    printf '%s\n' "$raw" >> "$out"
  done
done
echo "TRACE_DONE $start+$count rep=$rep"
