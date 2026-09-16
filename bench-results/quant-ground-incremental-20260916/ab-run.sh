#!/usr/bin/env bash
# QUANT-GROUND-INCREMENTAL -- interleaved per-file A/B of ONE BINARY at TWO ENV VALUES
# (ADR-2124, `AXEYUM_QINST_GROUND_SESSION`).
#
#   ab-run.sh <tag> <list> <out.tsv> <pin> <bin> <valueB> [budget_s]
#
# A = the shipped arm, the variable UNSET (not `=0`): an explicitly-set `0` and
#     an unset variable take different code paths through `cap_lever!`, and the
#     arm that ships is the unset one. Measuring `0` against `1` would leave the
#     shipped path itself untested by the A/B.
# B = the same binary with `AXEYUM_QINST_GROUND_SESSION=<valueB>`.
#
# Both arms run BACK TO BACK on the SAME file on the SAME pinned core, so
# ambient load -- which has moved 23 verdicts in one division at fixed code on
# these boxes -- cancels in the DIFFERENCE. Arm order alternates per file, so a
# systematic advantage to running second cannot accrue to one arm.
#
# EXIT STATUS is its own column, never folded into the verdict: a run can report
# `losses=0` by verdict while creating new aborts underneath it.
#
# Envelope: 24 s wall, 8 GiB `ulimit -v`, one pinned physical core.
set -u
TAG="$1"; LIST="$2"; OUT="$3"; PIN="$4"; AX="$5"; VB="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

[ -x "$AX" ] || { echo "ABORT $TAG: $AX missing"; exit 2; }
[ -s "$OUT" ] && { echo "ABORT $TAG: $OUT is non-empty; refusing to overwrite"; exit 2; }
case "$VB" in
  ''|0) echo "ABORT $TAG: arm B value '$VB' is the shipped arm; both arms would be A"; exit 2 ;;
esac

run_arm() {  # $1 = "" for the shipped arm, else the level value
  local t0 t1 raw rc v
  t0=$(date +%s%N)
  if [ -z "$1" ]; then
    raw=$(env -u AXEYUM_QINST_GROUND_SESSION \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    raw=$(AXEYUM_QINST_GROUND_SESSION="$1" \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  fi
  rc=$?
  t1=$(date +%s%N)
  v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
  printf '%s\t%s\t%s' "${v:-none}" "$(( (t1 - t0) / 1000000 ))" "$rc"
}

printf 'file\tA\tA_ms\tA_rc\tB\tB_ms\tB_rc\tfirst\n' > "$OUT"
n=0
while read -r f; do
  [ -z "$f" ] && continue
  if [ $((n % 2)) -eq 0 ]; then
    a=$(run_arm ""); b=$(run_arm "$VB"); first=A
  else
    b=$(run_arm "$VB"); a=$(run_arm ""); first=B
  fi
  printf '%s\t%s\t%s\t%s\n' "${f#"$CORPUS"}" "$a" "$b" "$first" >> "$OUT"
  n=$((n + 1))
done < "$LIST"
echo "AB-DONE $TAG $n files -> $OUT"
