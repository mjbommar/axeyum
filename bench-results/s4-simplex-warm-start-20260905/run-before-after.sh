#!/usr/bin/env bash
# S4 before/after runner over the QF_LRA timeout population.
#
# Interleaved per file (before, after, next file) so the two arms see the same
# machine load, which on a shared fleet host moves more than the change under
# test. Appends one TSV row per file:
#   file  declared  before_verdict  before_ms  after_verdict  after_ms
#
# Usage: run-before-after.sh <before_binary> <after_binary> <population.tsv> <out.tsv> [start] [count]
#
# `declared` is column 2 of the population TSV (the benchmark's own `:status`,
# which reads `unknown` for several of these files); column 7 carries z3's
# verdict from the 2026-08-21 diagnosis run. A verdict CONTRADICTING a
# non-`unknown` `declared` is a P0 and stops the lane, so this script prints
# `P0 ...` on stderr for such a row rather than only recording it.
set -uo pipefail

before_bin=$1
after_bin=$2
population=$3
out=$4
start=${5:-1}
count=${6:-1000}

run_one() {
  local bin=$1 file=$2
  local t0 t1 verdict rc
  t0=$(date +%s%N)
  verdict=$(timeout -k 2 30s taskset -c 0-7 "$bin" "$file" --timeout-ms 24000 2>/dev/null | tail -1)
  rc=$?
  t1=$(date +%s%N)
  case "$verdict" in
    sat | unsat | unknown) ;;
    *) verdict=HARDKILL ;;
  esac
  [ "$rc" -ne 0 ] && [ "$verdict" = unknown ] && verdict=HARDKILL
  printf '%s\t%s' "$verdict" "$(((t1 - t0) / 1000000))"
}

row=0
while IFS=$'\t' read -r file declared _rest; do
  row=$((row + 1))
  [ "$row" -lt "$start" ] && continue
  [ "$row" -ge $((start + count)) ] && break
  b=$(run_one "$before_bin" "$file")
  a=$(run_one "$after_bin" "$file")
  bv=${b%%$'\t'*}
  av=${a%%$'\t'*}
  printf '%s\t%s\t%s\t%s\n' "$file" "$declared" "$b" "$a" >>"$out"
  if [ "$declared" != unknown ]; then
    for v in "$bv" "$av"; do
      case "$v" in
        sat | unsat)
          [ "$v" = "$declared" ] || echo "P0 $file declared=$declared got=$v" >&2
          ;;
      esac
    done
  fi
  echo "row $row $(basename "$file") before=$bv after=$av load=$(cut -d' ' -f1 /proc/loadavg)" >&2
done < <(tail -n +2 "$population")
