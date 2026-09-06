#!/usr/bin/env bash
# S1b mutation runs: intact vs one mutant, interleaved, on the traced files.
# usage: mut-run.sh <nomin|noheap> <listfile> <start> <count> <rep> <outfile>
set -uo pipefail
which="$1"; list="$2"; start="$3"; count="$4"; rep="$5"; out="$6"
I="$HOME/s1b-after/target/release/examples/smtcomp_cli"
M="$HOME/s1b-$which/target/release/examples/smtcomp_cli"
sed -n "$((start+1)),$((start+count))p" "$list" | while IFS= read -r f; do
  for arm in intact mutant; do
    case $arm in intact) bin="$I";; mutant) bin="$M";; esac
    t0=$(date +%s%N)
    raw=$(MEM_LIMIT_GB=8 taskset -c 0-7 timeout 29 "$bin" "$f" --timeout-ms 24000 --trace 2>&1)
    t1=$(date +%s%N)
    echo "### $(basename "$f") [$which $arm rep=$rep] wall_ms=$(( (t1-t0)/1000000 ))" >> "$out"
    printf '%s\n' "$raw" >> "$out"
  done
done
echo "MUT_DONE $which $start+$count rep=$rep"
