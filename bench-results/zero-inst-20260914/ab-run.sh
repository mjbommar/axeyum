#!/usr/bin/env bash
# ZERO-INST -- interleaved per-file A/B of the Boolean-skeleton refutation rung.
#
# ============================ POLARITY ============================
#   ARM "off" : AXEYUM_ZERO_INST_SKELETON **unset** = the SHIPPED arm.
#               The rung early-returns and the ladder is unchanged.
#   ARM "on"  : AXEYUM_ZERO_INST_SKELETON=1        = the LEVER arm.
#
# The shipped arm is the one with the variable REMOVED, and it is removed with
# `env -u` rather than merely left unset, because the harness environment is
# inherited. A runner whose polarity is the other way round measures the shipped
# arm against itself and reports a confident zero, so the polarity is stated
# here and asserted at startup below.
# ==================================================================
#
# ONE BINARY, TWO ENV VALUES -- never two builds.
#
# Both arms run BACK TO BACK on the SAME file on the SAME pinned physical core,
# with the arm ORDER ROTATING per file, because ambient load has moved 23
# verdicts in one division at fixed code on these boxes (ADR-2000).
#
# THE ARM IS VISIBLE BY MECHANISM, not inferred from verdicts: under
# `AXEYUM_TRACE=1` the route trail names `q:bool-skeleton` with its outcome, so
# a silently ignored variable shows `declined/not-applicable` in BOTH arms.
# `ab-preflight.sh` asserts the two arms differ before any measuring starts.
#
# Usage: ab-run.sh <list> <out.tsv> <core> <bin> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=${ZERO_INST_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }

# Prints "<verdict>\t<ms>\t<rung_outcome>".  The third field is the mechanism
# column: `decided-unsat` means the rung fired, `declined` means it ran and said
# no, `absent` means the rung never appeared in the trail at all.
run_arm() {
  local mode="$1" f="$2" t0 t1 raw v rung
  t0=$(date +%s%N)
  if [ "$mode" = off ]; then
    raw=$(env -u AXEYUM_ZERO_INST_SKELETON AXEYUM_TRACE=1 \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
  else
    raw=$(AXEYUM_ZERO_INST_SKELETON=1 AXEYUM_TRACE=1 \
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
echo "DONE $OUT rows=$n core=$PIN budget=${BUDGET}s"
