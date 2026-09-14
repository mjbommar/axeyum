#!/usr/bin/env bash
# ADR-2035 -- REUSED VERBATIM from bench-results/decline-wiring-20260914/ab-run.sh
#
# ============================ POLARITY ============================
#   ARM "off" : the lever variable is REMOVED with `env -u`  = the SHIPPED arm.
#   ARM "on"  : <VAR>=<VALUE>                                = the LEVER arm.
# The shipped arm is the one with the variable REMOVED, not merely unset,
# because the harness environment is inherited. Copying a runner whose polarity
# is the other way round measures the shipped arm against itself and reports a
# confident zero -- so the polarity is stated here, in the header.
#
# BOTH levers in this lane fail CLOSED (unset / empty / malformed / zero all
# return the shipped constant), so "on" with a bad VALUE degenerates to a second
# copy of the shipped arm, which is a NOISE FLOOR run, not a lever run. That is
# exactly how the noise floor below is produced: VAR=AXEYUM_NOT_A_LEVER.
# ==================================================================
#
# ONE BINARY, TWO ENV VALUES -- never two builds. The binary's sha256 is
# recorded in the run log so a stale-artifact substitution is visible.
#
# Both arms run BACK TO BACK on the SAME file on the SAME pinned physical core,
# with the arm ORDER ROTATING per file, because ambient load has moved 23
# verdicts in one division at fixed code on these boxes (ADR-2000). Both arms
# live INSIDE one shard, so a shard can never move one arm relative to the other.
#
# Usage: ab-run.sh <list> <out.tsv> <core> <bin> <VAR> <VALUE> [budget_s]
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; VAR="$5"; VALUE="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT: $OUT is non-empty; refusing to overwrite"; exit 2; }
echo "RUNNER core=$PIN var=$VAR value=$VALUE budget=${BUDGET}s sha256=$(sha256sum "$AX" | cut -d' ' -f1)"

run_arm() {
  # $1 = off|on, $2 = file.  Prints "<verdict>\t<ms>"
  local mode="$1" f="$2" t0 t1 raw v
  t0=$(date +%s%N)
  if [ "$mode" = off ]; then
    raw=$(env -u "$VAR" \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$CORPUS/$f" 2>&1)
  else
    raw=$(env "$VAR=$VALUE" \
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
echo "DONE $OUT rows=$n core=$PIN var=$VAR value=$VALUE"
