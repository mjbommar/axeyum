#!/usr/bin/env bash
# ADR-2020 -- interleaved per-file A/B of the pre-SAT skeleton envelope.
#
# ============================ POLARITY ============================
#   ARM "off"  : AXEYUM_GROUND_DECIDE_PRESAT_ENVELOPE **unset**  = the SHIPPED
#                arm (envelope 10,240 / 16,384).
#   ARM "on"   : AXEYUM_GROUND_DECIDE_PRESAT_ENVELOPE=$ENVELOPE   = the LEVER
#                arm (envelope raised).
# The shipped arm is the one with the variable REMOVED, and it is removed with
# `env -u` rather than merely not set, because the harness environment is
# inherited. Copying a runner whose polarity is the other way round measures the
# shipped arm against itself and reports a confident zero -- so the polarity is
# stated here, in the header, and asserted at startup below.
# ==================================================================
#
# ONE BINARY, TWO ENV VALUES -- never two builds.
#
# Both arms run BACK TO BACK on the SAME file on the SAME pinned physical core,
# with the arm ORDER ROTATING per file, because ambient load has moved 23
# verdicts in one division at fixed code on these boxes (ADR-2000).
#
# Usage: ab-run.sh <list> <out.tsv> <core> <bin> [budget_s] [envelope]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"; ENVELOPE="${6:-40960,65536}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }

# The arm must be visible BY MECHANISM, not inferred from verdicts. The give-up
# string prints the EFFECTIVE envelope, so a silently ignored variable prints
# the shipped pair in both arms. Assert the two arms differ before measuring.
run_arm() {
  # $1 = off|on, $2 = file.  Prints "<verdict>\t<ms>"
  local mode="$1" f="$2" t0 t1 raw v
  t0=$(date +%s%N)
  if [ "$mode" = off ]; then
    raw=$(env -u AXEYUM_GROUND_DECIDE_PRESAT_ENVELOPE \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
  else
    raw=$(AXEYUM_GROUND_DECIDE_PRESAT_ENVELOPE="$ENVELOPE" \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
  fi
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'); v="${v:-NONE}"
  printf '%s\t%s' "$v" "$(( (t1 - t0) / 1000000 ))"
}

printf 'file\torder\toff_verdict\toff_ms\ton_verdict\ton_ms\n' > "$OUT"
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
echo "DONE $OUT rows=$n core=$PIN envelope=$ENVELOPE"
