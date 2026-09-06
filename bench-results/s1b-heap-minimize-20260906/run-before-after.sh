#!/usr/bin/env bash
# S1b before/after: interleaved per file, both arms, one TSV row per (file, arm).
# usage: ab.sh <populationtsv> <start> <count> <outfile>
set -uo pipefail
pop="$1"; start="$2"; count="$3"; out="$4"
B="$HOME/s1b-before/target/release/examples/smtcomp_cli"
A="$HOME/s1b-after/target/release/examples/smtcomp_cli"
run_one() { # bin file -> "verdict<TAB>ms"
  local bin="$1" f="$2" t0 t1 raw v
  t0=$(date +%s%N)
  raw=$(MEM_LIMIT_GB=8 taskset -c 0-7 timeout 29 "$bin" "$f" --timeout-ms 24000 2>&1)
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -E '^(sat|unsat|unknown)$')
  [ -z "$v" ] && v="unsolved"
  printf '%s\t%s' "$v" "$(( (t1 - t0) / 1000000 ))"
}
# Skip the header row of the population file.
tail -n +2 "$pop" | sed -n "$((start+1)),$((start+count))p" | while IFS=$'\t' read -r f declared rest; do
  bres=$(run_one "$B" "$f")
  ares=$(run_one "$A" "$f")
  printf 'before\t%s\t%s\t%s\n' "$declared" "$bres" "$f" >> "$out"
  printf 'after\t%s\t%s\t%s\n'  "$declared" "$ares" "$f" >> "$out"
done
echo "AB_DONE $start+$count"
