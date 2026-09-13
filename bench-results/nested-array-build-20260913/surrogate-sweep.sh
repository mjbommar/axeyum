#!/usr/bin/env bash
# Sweep the array-free surrogate (nested_array_surrogate.py) over a division's
# pinned winnable list and record, per file, what axeyum and z3 say about the
# SURROGATE and what the board already recorded about the ORIGINAL.
#
# Columns: file  surrogate_state  ax_surrogate  ax_s  z3_surrogate  z3_s  declared_status
#
#   surrogate_state = ok | REFUSED (outside the sound fragment)
#
# The reading rule, and it is one-directional: the rewrite deletes axioms, so
#   surrogate unsat ==> original unsat   (a file the build can reach)
#   surrogate sat   ==> nothing at all   (reported, never counted)
#
# The z3 column is the CONTROL on that argument, not a performance comparison:
# a z3 `unsat` on a surrogate whose original is `sat` would refute the
# soundness claim above.  `check-surrogate-soundness.py` is what reads it.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
DIV="${1:?division}"
LIST="${2:?winnable list}"
OUTDIR="${3:?output dir}"
BUDGET_S="${4:-24}"
AX="${AXEYUM_CLI:-/nas3/data/axeyum/harness/tier1-divisions/bin/smtcomp_cli}"
Z3="${Z3_BIN:-/usr/bin/z3}"

mkdir -p "$OUTDIR/rewritten/$DIV"
OUT="$OUTDIR/$DIV.tsv"
printf 'file\tsurrogate\tax\tax_s\tz3\tz3_s\n' > "$OUT"

n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  base="$(basename -- "$f")"
  tgt="$OUTDIR/rewritten/$DIV/$n-$base"
  if ! python3 "$HERE/nested_array_surrogate.py" "$f" "$tgt" 2> "$tgt.why"; then
    printf '%s\tREFUSED\t-\t-\t-\t-\n' "$f" >> "$OUT"
    continue
  fi
  t0=$(date +%s.%N)
  a=$(timeout $((BUDGET_S * 2 + 10)) "$AX" "$tgt" --timeout-ms $((BUDGET_S * 1000)) 2>/dev/null \
        | grep -m1 -E '^(sat|unsat|unknown)$')
  t1=$(date +%s.%N)
  z=$(timeout $((BUDGET_S * 2 + 10)) "$Z3" -T:"$BUDGET_S" "$tgt" 2>/dev/null \
        | grep -m1 -E '^(sat|unsat|unknown)$')
  t2=$(date +%s.%N)
  printf '%s\tok\t%s\t%.2f\t%s\t%.2f\n' \
    "$f" "${a:-unknown}" "$(echo "$t1 - $t0" | bc)" "${z:-unknown}" "$(echo "$t2 - $t1" | bc)" >> "$OUT"
done < "$LIST"

echo "wrote $OUT ($n files)"
