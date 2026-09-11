#!/usr/bin/env bash
# The fair head-to-head: one box, one problem at a time, three solvers.
#
# FAIRNESS DESIGN, and why each piece is here:
#   - ONE BOX, serial. No two solves ever run at once, so no contention.
#   - SAME CORE SET for all three (taskset). Identical CPU treatment; on a
#     hybrid CPU an unpinned sweep drifts onto slower cores (measured 1.84x in
#     this repo), which is why this runs on s6, whose cores are homogeneous.
#   - INTERLEAVED per problem: all three solvers run file N before any runs
#     file N+1. Cancels drift -- thermal, background, time of day.
#   - ROTATING ORDER: the solver that goes first rotates per file, so no one
#     benefits systematically from a cold or warm page cache.
#   - SAME BUDGET: 24 s wall, 8 GiB, the board protocol. Units differ per
#     solver and are set accordingly: z3 -T: SECONDS, cvc5 --tlimit MILLISECONDS.
#   - Every binary is probed before any measurement. z3 was absent on one host
#     earlier today and 800 files scored a silent 0/200 that read as a result.
#
# WHICH BOX, AND WHY -- measured 2026-09-11, not assumed. Same compute-bound
# probe (QF_LRA/LassoRanker firewire.t2.c_Iteration3_Loop_4, ~5.5 s of real
# work for z3), 7 runs, pinned to one core, each host otherwise quiet:
#
#   box  median   spread  cores
#   s6   5.569 s  0.51%   homogeneous Ryzen 7 7840HS   <- chosen
#   s4   5.814 s  0.68%   HYBRID i5-12600K
#   s7   5.811 s  1.10%   homogeneous
#   s5   --       --      contaminated: a stray cvc5 was still running
#
# s6 wins on both speed and consistency, and consistency is what matters: its
# variance becomes noise in every delta. s4 matches on spread only because the
# pin landed on a P-core -- it is a hybrid CPU, and this repo has already
# measured a 1.84x penalty when work drifts onto the E-cores. s4 is also the
# box lanes work on. s5's first-round numbers were rejected once the stray
# process was found, which is why the benchmark was repeated with load printed.
#
set -u
BUDGET=24
OUT="${FAIR_OUT:-bench-results/fair}"
PIN="${FAIR_PIN:-0-3}"
mkdir -p "$OUT"
declare -A BIN=( [axeyum]="target/release/examples/smtcomp_cli"
                 [z3]="/usr/bin/z3"
                 [cvc5]="/nas3/data/axeyum/harness/bin/cvc5" )
for s in axeyum z3 cvc5; do
  [ -x "${BIN[$s]}" ] || { echo "ABORT: $s missing at ${BIN[$s]}"; exit 2; }
done
# live probe: each solver must DECIDE a known-easy file, not merely exist
probe=$(head -1 bench-results/parity-lists/QF_UF.txt)
for s in axeyum z3 cvc5; do
  case $s in
    axeyum) v=$(timeout 30 "${BIN[$s]}" "$probe" --timeout-ms 20000 2>/dev/null | grep -m1 -oE '^(sat|unsat)$') ;;
    z3)     v=$(timeout 30 "${BIN[$s]}" -T:20 "$probe" 2>/dev/null | grep -m1 -oE '^(sat|unsat)$') ;;
    cvc5)   v=$(timeout 30 "${BIN[$s]}" --tlimit=20000 "$probe" 2>/dev/null | grep -m1 -oE '^(sat|unsat)$') ;;
  esac
  [ -n "$v" ] || { echo "ABORT: $s did not decide the probe -- broken invocation"; exit 3; }
  echo "probe ok: $s -> $v"
done
run() {  # $1 solver  $2 file  -> "verdict<TAB>seconds"
  local t0 t1 v
  t0=$(date +%s.%N)
  case $1 in
    axeyum) v=$(MEM_LIMIT_GB=8 timeout $((BUDGET+5)) taskset -c "$PIN" ./scripts/mem-run.sh "${BIN[$1]}" "$2" --timeout-ms $((BUDGET*1000)) 2>/dev/null | grep -m1 -oE '^(sat|unsat)$') ;;
    z3)     v=$(MEM_LIMIT_GB=8 timeout $((BUDGET+5)) taskset -c "$PIN" ./scripts/mem-run.sh "${BIN[$1]}" -T:$BUDGET "$2" 2>/dev/null | grep -m1 -oE '^(sat|unsat)$') ;;
    cvc5)   v=$(MEM_LIMIT_GB=8 timeout $((BUDGET+5)) taskset -c "$PIN" ./scripts/mem-run.sh "${BIN[$1]}" --tlimit=$((BUDGET*1000)) "$2" 2>/dev/null | grep -m1 -oE '^(sat|unsat)$') ;;
  esac
  t1=$(date +%s.%N)
  printf '%s\t%.2f' "${v:-unknown}" "$(echo "$t1-$t0" | bc)"
}
i=0
for div in "$@"; do
  out="$OUT/$div.tsv"
  printf 'file\taxeyum\tax_s\tz3\tz3_s\tcvc5\tcvc5_s\n' > "$out"
  while read -r f; do
    i=$((i+1))
    case $((i % 3)) in   # rotate who goes first
      0) o=(axeyum z3 cvc5) ;;
      1) o=(z3 cvc5 axeyum) ;;
      2) o=(cvc5 axeyum z3) ;;
    esac
    declare -A R=()
    for s in "${o[@]}"; do R[$s]=$(run "$s" "$f"); done
    printf '%s\t%s\t%s\t%s\n' "$(basename "$f")" "${R[axeyum]}" "${R[z3]}" "${R[cvc5]}" >> "$out"
  done < "bench-results/parity-lists/$div.txt"
  a=$(awk -F'\t' 'NR>1 && $2!="unknown"' "$out" | wc -l)
  z=$(awk -F'\t' 'NR>1 && $4!="unknown"' "$out" | wc -l)
  c=$(awk -F'\t' 'NR>1 && $6!="unknown"' "$out" | wc -l)
  echo "FAIR $div  axeyum=$a  z3=$z  cvc5=$c  of $(( $(wc -l < "$out") - 1 ))"
done
echo FAIR-DONE
