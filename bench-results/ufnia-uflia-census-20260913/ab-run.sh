#!/usr/bin/env bash
# Interleaved per-file A/B of two `AXEYUM_QUANT_EGRAPH_RESERVE` arms.
#
# ONE BINARY, two env values -- the lever ships off, so the `base` arm is the
# shipped default and an A/B cannot accidentally compare two builds (the
# unpinned-baseline failure the `uf-arith-overbound` protocol had to fix).
#
# The two arms run BACK TO BACK on the SAME file on the SAME pinned core, so
# ambient load -- which has moved 23 verdicts in one division at fixed code on
# these boxes -- cancels in the DIFFERENCE rather than landing entirely on
# whichever arm ran second.  Arm order alternates per file for the same reason.
#
# Same envelope as the census and both pinned boards: 24 s wall, 8 GiB
# `ulimit -v`, one pinned physical core.
#
# Usage: ab-run.sh <tag> <list> <out.tsv> <cores> <bin> <arm-env-value> [budget_s]
#   <arm-env-value> is what the ARM sets AXEYUM_QUANT_EGRAPH_RESERVE to; the
#   base arm always runs with the variable UNSET (`env -u`), not set to "off",
#   so the base arm is literally an environment with no lever in it.
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; ARM="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }

run_arm() {  # $1 = "base" | "arm"
  local t0 t1 raw v ms
  t0=$(date +%s%N)
  if [ "$1" = base ]; then
    raw=$(env -u AXEYUM_QUANT_EGRAPH_RESERVE timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    raw=$(AXEYUM_QUANT_EGRAPH_RESERVE="$ARM" timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  fi
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  ms=$(( (t1 - t0) / 1000000 ))
  printf '%s\t%s\t%s' "${v:-none}" "$ms" "$rc"
}

printf 'file\tbase\tbase_ms\tbase_rc\tarm\tarm_ms\tarm_rc\tfirst\tstatus\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if [ $((n % 2)) -eq 1 ]; then
    first=base; b=$(run_arm base); a=$(run_arm arm)
  else
    first=arm;  a=$(run_arm arm);  b=$(run_arm base)
  fi
  printf '%s\t%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$b" "$a" "$first" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "AB-DONE $TAG $n files -> $OUT"
