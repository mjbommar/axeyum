#!/usr/bin/env bash
# ZERO-INST -- of the 15 files whose Boolean skeleton two independent solvers
# refute, 9 converted. This asks what stopped the other 6, and separates the
# two causes rather than reporting one number.
#
#   why-not-more.sh <list> <bin> <out.tsv> [core]
#
# Each file is run at the A/B budget and at 5x it. The pairing is what makes
# the answer a diagnosis instead of a description:
#
#   declines at BOTH budgets  -> a CAPABILITY limit. Our own ground checker
#                                cannot refute the skeleton that cvc5 and z3
#                                both refute, so more time does not help.
#   decides at 5x only        -> a BUDGET limit. The rung gets one tenth of
#                                the query budget and the skeleton needs more.
#   rung ABSENT at both       -> the ladder never REACHES the rung; the route
#                                trail stops earlier and this rung is not the
#                                thing to fix.
set -u
LIST="$1"
AX="$2"
OUT="$3"
PIN="${4:-2}"
CORPUS=${ZERO_INST_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

verdict() { grep -m1 -oE '^(sat|unsat|unknown)$' || true; }
rung_of() {
  if printf '%s' "$1" | grep -qF '"route":"q:bool-skeleton","outcome":"decided"'; then
    echo decided
  elif printf '%s' "$1" | grep -qF '"route":"q:bool-skeleton"'; then
    echo declined
  else
    echo absent
  fi
}

printf 'file\tv24s\trung24s\tv120s\trung120s\tdiagnosis\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  a=$(env -u AXEYUM_ZERO_INST_SKELETON AXEYUM_TRACE=1 timeout 60 taskset -c "$PIN" \
        "$AX" "$CORPUS/$f" --timeout-ms 24000 2>&1)
  b=$(env -u AXEYUM_ZERO_INST_SKELETON AXEYUM_TRACE=1 timeout 200 taskset -c "$PIN" \
        "$AX" "$CORPUS/$f" --timeout-ms 120000 2>&1)
  va=$(printf '%s\n' "$a" | verdict); vb=$(printf '%s\n' "$b" | verdict)
  ra=$(rung_of "$a"); rb=$(rung_of "$b")
  if [ "$ra" = decided ]; then
    d=CONVERTED
  elif [ "$ra" = absent ] && [ "$rb" = absent ]; then
    d=RUNG-NEVER-REACHED
  elif [ "$rb" = decided ]; then
    d=BUDGET-LIMIT
  else
    d=CAPABILITY-LIMIT
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "${va:-NONE}" "$ra" "${vb:-NONE}" "$rb" "$d" >> "$OUT"
  printf '%-58s %s\n' "$(basename "$f" | cut -c1-56)" "$d"
done < "$LIST"
echo "DONE $OUT"
awk -F'\t' 'NR>1{c[$6]++} END{for (k in c) print c[k], k}' "$OUT" | sort -rn
