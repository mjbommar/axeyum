#!/usr/bin/env bash
# ZERO-INST -- NOISE FLOOR. Byte-identical configuration in BOTH arms.
#
# ============================ POLARITY ============================
#   ARM "off"  : AXEYUM_ZERO_INST_SKELETON unset  (the shipped arm)
#   ARM "on"   : AXEYUM_ZERO_INST_SKELETON unset  (the SAME shipped arm)
# There is no lever here. Both `run_arm` branches use `env -u`, deliberately
# and identically, so every row that "moves" is run-to-run variance and
# nothing else. Any effect the real A/B reports that is SMALLER than what
# this run produces is not an effect.
# ==================================================================
#
# Written out in full rather than derived from `ab-run.sh` by substitution: a
# derived control that silently fails to substitute becomes a second copy of
# the real A/B while still being labelled a noise floor. `ab-verify-noise.sh`
# asserts, on this file, that neither branch sets the variable.
#
# Usage: ab-run-noise.sh <list> <out.tsv> <core> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=${ZERO_INST_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }

run_arm() {
  local mode="$1" f="$2" t0 t1 raw v rung
  t0=$(date +%s%N)
  if [ "$mode" = off ]; then
    raw=$(env -u AXEYUM_ZERO_INST_SKELETON AXEYUM_TRACE=1 \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
  else
    raw=$(env -u AXEYUM_ZERO_INST_SKELETON AXEYUM_TRACE=1 \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
  fi
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'); v="${v:-NONE}"
  if printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton","outcome":"decided"'; then
    rung=decided
  elif printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton"'; then
    rung=declined
  else
    rung=absent
  fi
  printf '%s\t%s\t%s' "$v" "$(((t1 - t0) / 1000000))" "$rung"
}

printf 'file\torder\toff_verdict\toff_ms\toff_rung\ton_verdict\ton_ms\ton_rung\n' > "$OUT"
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  n=$((n + 1))
  if [ $((n % 2)) -eq 1 ]; then
    ORDER="off-on"; A=$(run_arm off "$f"); B=$(run_arm on "$f")
  else
    ORDER="on-off"; B=$(run_arm on "$f"); A=$(run_arm off "$f")
  fi
  printf '%s\t%s\t%s\t%s\n' "$f" "$ORDER" "$A" "$B" >> "$OUT"
done < "$LIST"
echo "DONE $OUT rows=$n core=$PIN budget=${BUDGET}s NOISE-FLOOR(both arms shipped)"
