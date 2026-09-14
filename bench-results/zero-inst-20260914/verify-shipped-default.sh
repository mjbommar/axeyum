#!/usr/bin/env bash
# ZERO-INST -- the A/B's ON arm was produced by an ENV VAR. The shipped build
# produces it by DEFAULT. Those are different binaries' behaviours until
# somebody checks, so this checks rather than predicting.
#
#   verify-shipped-default.sh <list> <bin> <out.tsv> [core] [budget_s]
#
# Three columns per file:
#   default    no environment variable at all -- what a user gets
#   killed     AXEYUM_ZERO_INST_SKELETON=0    -- the kill switch, i.e. the
#              pre-ADR-2025 ladder
#   rung       the route-trail outcome under `default`
#
# The kill column is what makes the default column a measurement: if both
# spellings gave the same verdict, the default would not be doing anything and
# the row would prove nothing. Exit status depends on the finding.
set -u
LIST="$1"
AX="$2"
OUT="$3"
PIN="${4:-2}"
BUDGET="${5:-24}"
CORPUS=${ZERO_INST_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

verdict() { grep -m1 -oE '^(sat|unsat|unknown)$' || true; }

printf 'file\tdefault\tkilled\trung_under_default\n' > "$OUT"
bad=0
n=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  n=$((n + 1))
  raw=$(env -u AXEYUM_ZERO_INST_SKELETON AXEYUM_TRACE=1 timeout $((BUDGET + 16)) \
          taskset -c "$PIN" "$AX" "$CORPUS/$f" --timeout-ms $((BUDGET * 1000)) 2>&1)
  d=$(printf '%s\n' "$raw" | verdict)
  if printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton","outcome":"decided"'; then
    rung=decided
  elif printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton"'; then
    rung=declined
  else
    rung=absent
  fi
  k=$(AXEYUM_ZERO_INST_SKELETON=0 timeout $((BUDGET + 16)) \
        taskset -c "$PIN" "$AX" "$CORPUS/$f" --timeout-ms $((BUDGET * 1000)) 2>&1 | verdict)
  printf '%s\t%s\t%s\t%s\n' "$f" "${d:-NONE}" "${k:-NONE}" "$rung" >> "$OUT"
  if [ "${d:-NONE}" != unsat ] || [ "$rung" != decided ]; then
    echo "FAIL $f: default=${d:-NONE} rung=$rung (expected unsat/decided)"
    bad=$((bad + 1))
  fi
  if [ "${k:-NONE}" = unsat ]; then
    echo "VACUOUS $f: the kill switch ALSO decides it, so the default proves nothing"
    bad=$((bad + 1))
  fi
done < "$LIST"

echo "rows=$n problems=$bad"
if [ "$bad" -ne 0 ]; then
  echo "SHIPPED-DEFAULT-FAIL"
  exit 3
fi
echo "SHIPPED-DEFAULT-OK: $n/$n decided by the rung with NO environment variable, \
and $n/$n undecided under the kill switch"
