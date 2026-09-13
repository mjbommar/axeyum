#!/usr/bin/env bash
# Sweep the outer-read-over-write surrogate over a division's pinned winnable
# list.  Per file it records what axeyum says about the SURROGATE, and what z3
# says about the SURROGATE and about the ORIGINAL.
#
# Columns: file  surrogate  ax  ax_s  z3_surrogate  z3s_s  z3_original  z3o_s  status
#
#   surrogate = ok | REFUSED
#
# The reading rule, one-directional by choice even though the rewrite is
# equisatisfiable on the accepted fragment:
#   surrogate unsat ==> original unsat   (a file the named gate reaches)
#   surrogate sat   ==> counted nowhere, reported in its own column
#
# The two z3 columns are the SOUNDNESS CONTROL on that argument and they have an
# opportunity to fire on every accepted file, not only the refutable ones: a
# disagreement between z3-on-original and z3-on-surrogate, in either direction,
# refutes the rewrite.  `check-surrogate-soundness.py` reads them.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
DIV="${1:?division}"
LIST="${2:?winnable list}"
OUTDIR="${3:?output dir}"
BUDGET_S="${4:-24}"
# "" for the plain currying, "--distribute" to also push `select` through the
# array-sorted `ite` the read-over-write expansion produces.  The two arms
# separate "needs outer read-over-write" from "needs one rewrite we lack".
EXTRA="${5:-}"
AX="${AXEYUM_CLI:-/nas3/data/axeyum/harness/tier1-divisions/bin/smtcomp_cli}"
Z3="${Z3_BIN:-/usr/bin/z3}"

mkdir -p "$OUTDIR/rewritten/$DIV"
OUT="$OUTDIR/$DIV.tsv"
printf 'file\tsurrogate\tax\tax_s\tz3_surr\tz3s_s\tz3_orig\tz3o_s\tstatus\n' > "$OUT"

n=0
while read -r f; do
  [ -z "$f" ] && continue
  n=$((n + 1))
  base="$(basename -- "$f")"
  tgt="$OUTDIR/rewritten/$DIV/$n-$base"
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" 2>/dev/null | awk '{print $2}')
  if ! python3 "$HERE/outer_row_surrogate.py" $EXTRA "$f" "$tgt" 2> "$tgt.why"; then
    printf '%s\tREFUSED\t-\t-\t-\t-\t-\t-\t%s\n' "$f" "${st:-none}" >> "$OUT"
    continue
  fi
  t0=$(date +%s.%N)
  a=$(timeout $((BUDGET_S * 2 + 10)) "$AX" "$tgt" --timeout-ms $((BUDGET_S * 1000)) 2>/dev/null \
        | grep -m1 -E '^(sat|unsat|unknown)$')
  t1=$(date +%s.%N)
  zs=$(timeout $((BUDGET_S * 2 + 10)) "$Z3" -T:"$BUDGET_S" "$tgt" 2>/dev/null \
        | grep -m1 -E '^(sat|unsat|unknown)$')
  t2=$(date +%s.%N)
  zo=$(timeout $((BUDGET_S * 2 + 10)) "$Z3" -T:"$BUDGET_S" "$f" 2>/dev/null \
        | grep -m1 -E '^(sat|unsat|unknown)$')
  t3=$(date +%s.%N)
  printf '%s\tok\t%s\t%.2f\t%s\t%.2f\t%s\t%.2f\t%s\n' \
    "$f" "${a:-unknown}" "$(echo "$t1 - $t0" | bc)" \
    "${zs:-unknown}" "$(echo "$t2 - $t1" | bc)" \
    "${zo:-unknown}" "$(echo "$t3 - $t2" | bc)" \
    "${st:-none}" >> "$OUT"
done < "$LIST"

echo "wrote $OUT ($n files)"
