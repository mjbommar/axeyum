#!/usr/bin/env bash
# SILENT-HANG -- interleaved per-file A/B for `AXEYUM_EQ_ATOM_DAG_WALK`.
#
# POLARITY, stated here so no reader has to infer it:
#   BASE  = the lever UNSET  = the shipped tree walk
#   ARM   = AXEYUM_EQ_ATOM_DAG_WALK=1 = the DAG walk
#   A GAIN is a row that is `unknown` under BASE and decided under ARM.
#   A LOSS is a row decided under BASE and `unknown`/worse under ARM.
#   A FLIP is a row whose VERDICT changes between sat and unsat -- which for a
#          change claiming identical atom collection would be a soundness
#          finding, not a performance one.
#
# ONE BINARY, TWO ENVIRONMENT VALUES.  Both walks are compiled in; the arms
# differ only by `env`.  That removes the build-difference confound a two-binary
# A/B carries.
#
# INTERLEAVED PER FILE, arms back to back, order ALTERNATING per row, one pinned
# core for the whole sweep.  Back-to-back on one core is what makes machine load
# cancel in the difference; alternating the order is what stops a monotone drift
# in load from being read as an effect.
#
#   ab.sh <list> <out.tsv> <pin> [budget_s] [passes]
set -u
W="$(cd "$(dirname "$0")" && pwd)"
LIST="$1"; OUT="$2"; PIN="${3:-2}"; BUDGET="${4:-24}"; PASSES="${5:-1}"
CORPUS="${SH_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${SH_AX_AB:-/nas3/data/axeyum/harness/silent-hang/bin/smtcomp_cli-ab}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

run() { # run <envmode> <file>  -> "verdict<TAB>ms<TAB>rc"
  local mode="$1" f="$2" t0 t1 out rc
  t0=$(( $(date +%s%N) / 1000000 ))
  if [ "$mode" = arm ]; then
    out=$(AXEYUM_EQ_ATOM_DAG_WALK=1 timeout $((BUDGET + 90)) taskset -c "$PIN" \
            "$AX" "$CORPUS/$f" --timeout-ms $((BUDGET * 1000)) 2>&1); rc=$?
  else
    out=$(env -u AXEYUM_EQ_ATOM_DAG_WALK timeout $((BUDGET + 90)) taskset -c "$PIN" \
            "$AX" "$CORPUS/$f" --timeout-ms $((BUDGET * 1000)) 2>&1); rc=$?
  fi
  t1=$(( $(date +%s%N) / 1000000 ))
  printf '%s\t%s\t%s' "$(printf '%s\n' "$out" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo NONE)" \
    "$((t1-t0))" "$rc"
}

printf 'file\tpass\torder\tbase\tbase_ms\tbase_rc\tarm\tarm_ms\tarm_rc\n' > "$OUT"
p=1
while [ "$p" -le "$PASSES" ]; do
  i=0
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    if [ $(((i + p) % 2)) -eq 0 ]; then ord=base-first; else ord=arm-first; fi
    if [ "$ord" = base-first ]; then
      b=$(run base "$f"); a=$(run arm "$f")
    else
      a=$(run arm "$f"); b=$(run base "$f")
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' "$f" "$p" "$ord" "$b" "$a" >> "$OUT"
    printf '%-46s p%s %-10s base=%-8s arm=%-8s\n' "$(basename "$f" | cut -c1-46)" "$p" "$ord" \
      "$(printf '%s' "$b" | cut -f1)" "$(printf '%s' "$a" | cut -f1)"
    i=$((i + 1))
  done < "$LIST"
  p=$((p + 1))
done
echo "DONE $OUT"
