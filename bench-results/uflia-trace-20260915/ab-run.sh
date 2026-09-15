#!/usr/bin/env bash
# UFLIA-TRACE -- interleaved per-file A/B of ONE BINARY at TWO ENV VALUES
# (ADR-2113, `AXEYUM_QINST_TRIGGER_ALTERNATIVES`).
#
#   ab-run.sh <tag> <list> <out.tsv> <pin> <bin> <valueB> [budget_s]
#
# A = the shipped arm, the variable UNSET (not `=1`): an explicitly-set `1` and
#     an unset variable take different code paths through `cap_lever!`, and the
#     arm that ships is the unset one. Measuring `1` against `4` would leave the
#     shipped path itself untested by the A/B.
# B = the same binary with `AXEYUM_QINST_TRIGGER_ALTERNATIVES=<valueB>`.
#
# ONE binary, so `ab-run.sh`'s same-binary abort does not apply -- but the
# failure it guards against does, in a different shape: if the variable never
# reaches the solve, both arms are the shipped arm and the run produces a
# perfect zero that looks exactly like agreement. `--self-check` runs the two
# arms over a fixture whose PROPOSED INSTANCES differ between them and refuses
# unless they actually differ. Run it before believing any zero here.
#
# Both arms run BACK TO BACK on the SAME file on the SAME pinned core, so
# ambient load -- which has moved 23 verdicts in one division at fixed code on
# these boxes -- cancels in the DIFFERENCE. Arm order alternates per file.
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
  ''|1|0) echo "ABORT $TAG: arm B value '$VB' is the shipped arm; both arms would be A"; exit 2 ;;
esac

run_arm() {  # $1 = "" for the shipped arm, else the cap value
  local t0 t1 raw rc v
  t0=$(date +%s%N)
  if [ -z "$1" ]; then
    raw=$(env -u AXEYUM_QINST_TRIGGER_ALTERNATIVES \
            timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
            bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --timeout-ms $((BUDGET * 1000))" \
            "$AX" "$f" 2>/dev/null)
  else
    raw=$(AXEYUM_QINST_TRIGGER_ALTERNATIVES="$1" \
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
