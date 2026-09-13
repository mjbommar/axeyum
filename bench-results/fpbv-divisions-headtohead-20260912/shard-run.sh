#!/usr/bin/env bash
# One shard of the fair head-to-head for QF_ABVFP / QF_BVFP / QF_UFBV.
# Same protocol as bench-results/dt-divisions-headtohead-20260912/shard-run.sh,
# which this is a copy of; only the axeyum binary path and the concurrency
# comment below differ.
#
# FAIRNESS: all three solvers run file N before any runs file N+1, on the same
# pinned physical core (both SMT threads) of the same idle homogeneous box, so
# ambient drift cancels in the difference.  The solver that goes first rotates
# per file so nobody systematically benefits from a cold or warm page cache.
#
# CONCURRENCY: at most TWO shards per host, on DISTINCT physical cores.  The
# 8 GiB address-space cap is per run, so three concurrent shards can reach
# 24 GiB on a 26 GB box.  Two cannot.
#
# Usage: shard-run.sh <tag> <list> <out.tsv> <cores>
set -u
BUDGET=24            # board protocol: 24 s wall, 8 GiB address space
HEADROOM=16          # wrapper timeout = BUDGET + HEADROOM.  A previous census
                     # used +8 under load, killed 17 processes, and produced
                     # false "no reason" rows.  Killed runs are RECORDED here
                     # in a per-solver kill column rather than silently scored.
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"
AX=/nas3/data/axeyum/harness/fpbv-divisions/bin/smtcomp_cli
Z3=/usr/bin/z3
CVC5=/nas3/data/axeyum/harness/bin/cvc5
VLIM=$((8 * 1024 * 1024))   # ulimit -v is KiB -> 8 GiB

for b in "$AX" "$Z3" "$CVC5"; do
  [ -x "$b" ] || { echo "ABORT $TAG: $b missing or not executable"; exit 2; }
done

run() { # $1 solver  $2 file -> "verdict<TAB>seconds<TAB>flag"
  local t0 t1 raw rc v k
  t0=$(date +%s.%N)
  case "$1" in
    axeyum) raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
              bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
              "$AX" "$2" 2>/dev/null) ;;
    z3)     raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
              bash -c "ulimit -v $VLIM; exec \"\$0\" -T:$BUDGET \"\$1\"" \
              "$Z3" "$2" 2>/dev/null) ;;
    cvc5)   raw=$(timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
              bash -c "ulimit -v $VLIM; exec \"\$0\" --tlimit=$((BUDGET * 1000)) \"\$1\"" \
              "$CVC5" "$2" 2>/dev/null) ;;
  esac
  rc=$?
  t1=$(date +%s.%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat)$')
  k=ok
  [ "$rc" = 124 ] && k=wrapper-killed
  [ "$rc" = 134 ] && k=rc134
  [ "$rc" = 137 ] && k=sigkill
  printf '%s\t%.2f\t%s' "${v:-unknown}" "$(echo "$t1-$t0" | bc)" "$k"
}

# The row key is the path RELATIVE TO THE CORPUS ROOT, not the basename the DT
# lane used: basenames COLLIDE in these divisions (200 QF_ABVFP files carry 198
# distinct basenames, 200 QF_BVFP files carry 196), so a basename key would
# silently merge two different benchmarks when the TSV is joined back to a list.
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

printf 'file\taxeyum\tax_s\tax_k\tz3\tz3_s\tz3_k\tcvc5\tcvc5_s\tcvc5_k\tstatus\n' > "$OUT"
i=0
while read -r f; do
  i=$((i + 1))
  case $((i % 3)) in
    0) order=(axeyum z3 cvc5) ;;
    1) order=(z3 cvc5 axeyum) ;;
    2) order=(cvc5 axeyum z3) ;;
  esac
  declare -A R=()
  for s in "${order[@]}"; do R[$s]=$(run "$s" "$f"); done
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' "$f" | awk '{print $2}')
  printf '%s\t%s\t%s\t%s\t%s\n' \
    "${f#"$CORPUS"}" "${R[axeyum]}" "${R[z3]}" "${R[cvc5]}" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "SHARD-DONE $TAG $(($(wc -l < "$OUT") - 1)) rows"
