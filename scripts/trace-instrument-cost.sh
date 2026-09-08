#!/usr/bin/env bash
# Paired hot-path cost measurement: base and HEAD run back-to-back on the SAME
# file, and the reported number is the median of the per-pair ratios.
#
#   scripts/trace-instrument-cost.sh <base-bin> <head-bin> <file-list> <default|trace> [reps]
#
# # Why paired, and why a control ran first
#
# The blocked form of this measurement — all of base, then all of HEAD — gave
# `delta_pct=-7.59` on this box, i.e. HEAD apparently 7.6% FASTER, which no
# instrument addition can do. The negative control says why: running the BASE
# binary as both arms gave `+13.68%`. Another lane's corpus sweep is on this
# machine, so its speed drifts by more over ten minutes than this change could
# possibly cost, and a blocked A/B charges that drift entirely to whichever arm
# ran during it.
#
# Pairing bounds the drift to the gap between two adjacent runs of one file.
# The order also ALTERNATES per file, so a systematic first-runs-warmer effect
# (page cache, frequency ramp) cancels instead of being charged to one arm.
#
# RUN THE CONTROL: pass the base binary as BOTH arguments. That number is this
# box's noise floor today, and a delta inside it is not a measurement. Measured
# 2026-09-08 on a contended box: blocked A/B floor +13.68%, paired floor -0.18%
# with an IQR of [-1.94%, +1.68%].
set -u
BASE="$1"
HEAD="$2"
LIST="$3"
MODE="$4"
REPS="${5:-5}"

FLAGS=()
[ "$MODE" = "trace" ] && FLAGS+=(--trace)

time_one() {
  local bin="$1" f="$2" start end
  start=$(date +%s%N)
  taskset -c 8-15 "$bin" "$f" --timeout-ms 9000 "${FLAGS[@]}" >/dev/null 2>&1
  end=$(date +%s%N)
  echo $(( (end - start) / 1000 ))   # microseconds
}

ratios=()
n=0
for _ in $(seq 1 "$REPS"); do
  while IFS= read -r f; do
    [ -z "$f" ] && continue
    n=$((n + 1))
    if [ $((n % 2)) -eq 0 ]; then
      b=$(time_one "$BASE" "$f"); h=$(time_one "$HEAD" "$f")
    else
      h=$(time_one "$HEAD" "$f"); b=$(time_one "$BASE" "$f")
    fi
    [ "$b" -gt 0 ] && ratios+=("$(awk -v h="$h" -v b="$b" 'BEGIN{printf "%.6f", h/b}')")
  done <"$LIST"
done

printf '%s\n' "${ratios[@]}" | sort -n | awk -v mode="$MODE" '
  {a[NR]=$1}
  END{
    med = (NR%2) ? a[(NR+1)/2] : (a[NR/2]+a[NR/2+1])/2
    q1  = a[int(NR*0.25)+1]
    q3  = a[int(NR*0.75)+1]
    printf "mode=%s pairs=%d median_ratio=%.4f (%+.2f%%) IQR=[%.4f, %.4f] (%+.2f%%, %+.2f%%)\n",
      mode, NR, med, (med-1)*100, q1, q3, (q1-1)*100, (q3-1)*100
  }'
