#!/usr/bin/env bash
# How OFTEN does the one mover actually land?
#
# `recheck-movers.sh` classified it UNSTABLE on 3 runs (1 of 3). Three runs give
# a rate of 1/3 with a 95 % interval of [2 %, 87 %], which is not a number. This
# runs the arm N times on one pinned core and reports the rate.
#
# The BASE arm is run too, and its rate must be 0/N: at this arity the pairwise
# expansion is refused deterministically at ingest, so a base `unsat` here would
# mean the file is not what the sizing says it is.
#
# Usage: mover-rate.sh <file> <out.tsv> <cores> <bin> [runs] [budget_s]
set -u
F="$1"; OUT="$2"; PIN="$3"; AX="$4"; RUNS="${5:-10}"; BUDGET="${6:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

one() {
  local raw t0 t1
  t0=$(date +%s%N)
  if [ "$1" = base ]; then
    raw=$(env -u AXEYUM_DISTINCT_LINEAR timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$F" 2>/dev/null)
  else
    raw=$(AXEYUM_DISTINCT_LINEAR=on timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$F" 2>/dev/null)
  fi
  t1=$(date +%s%N)
  printf '%s\t%s' "$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo none)" \
    "$(( (t1 - t0) / 1000000 ))"
}

printf 'run\tarm\tverdict\tms\n' > "$OUT"
for i in $(seq 1 "$RUNS"); do
  printf '%s\tbase\t%s\n' "$i" "$(one base)" >> "$OUT"
  printf '%s\tarm\t%s\n' "$i" "$(one arm)" >> "$OUT"
done

arm_dec=$(awk -F'\t' 'NR>1 && $2=="arm" && ($3=="sat"||$3=="unsat")' "$OUT" | wc -l)
base_dec=$(awk -F'\t' 'NR>1 && $2=="base" && ($3=="sat"||$3=="unsat")' "$OUT" | wc -l)
echo "MOVER-RATE runs=$RUNS arm_decided=$arm_dec/$RUNS base_decided=$base_dec/$RUNS budget=${BUDGET}s"
awk -F'\t' 'NR>1 && $2=="arm"{n++; s+=$4} END{if(n) printf "MOVER-RATE arm mean_ms=%.0f\n", s/n}' "$OUT"
if [ "$base_dec" -ne 0 ]; then
  echo "FAIL: the base arm decided $base_dec/$RUNS -- this file is not refused at ingest"
  exit 1
fi
exit 0
