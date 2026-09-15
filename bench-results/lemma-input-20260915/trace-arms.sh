#!/usr/bin/env bash
# LEMMA-INPUT -- one row's traced stdout under BOTH arms, kept verbatim, so the
# claim about WHICH LINES EXIST can be checked against the bytes.
#
# The question this answers is not a timing one.  ADR-2075's characterisation of
# its 9-row bucket is "the rows whose running code polls no deadline": a
# graceful decline records a `; route ` line on the way out, a watchdog kill
# records `; partial route `.  If bounding the rescan moves a row from the
# second to the first, the row has changed CATEGORY even when the verdict has
# not, and the next blocker becomes nameable.
#
# POLARITY: base = lever unset; arm = AXEYUM_LIA_INITIAL_BOUND_INDEX=1.
set -u
F="$1"; BUDGET="${2:-24}"; PIN="${3:-12}"; OUT="$4"
CORPUS="${LI_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${LI_AB_AX:-/data0/axeyum/lemma-input-bin/smtcomp_cli-A}"
mkdir -p "$OUT"
safe=$(printf '%s' "$F" | tr '/' '_')

env -u AXEYUM_LIA_INITIAL_BOUND_INDEX AXEYUM_TRACE=1 \
  taskset -c "$PIN" timeout $((BUDGET + 120)) \
  "$AX" "$CORPUS/$F" --timeout-ms $((BUDGET * 1000)) > "$OUT/$safe.base.txt" 2>&1
echo "base exit=$?"

AXEYUM_LIA_INITIAL_BOUND_INDEX=1 AXEYUM_TRACE=1 \
  taskset -c "$PIN" timeout $((BUDGET + 120)) \
  "$AX" "$CORPUS/$F" --timeout-ms $((BUDGET * 1000)) > "$OUT/$safe.arm.txt" 2>&1
echo "arm exit=$?"

for a in base arm; do
  echo "--- $a ---"
  echo "  lines: $(grep -c . "$OUT/$safe.$a.txt")"
  echo "  complete route line: $(grep -c '^; route ' "$OUT/$safe.$a.txt")"
  echo "  PARTIAL route line:  $(grep -c '^; partial route ' "$OUT/$safe.$a.txt")"
  echo "  give-up kind:        $(grep -m1 '^; give-up ' "$OUT/$safe.$a.txt" || echo NONE)"
  grep -m1 -E '^; (partial )?route ' "$OUT/$safe.$a.txt" | cut -c1-200 || true
done
