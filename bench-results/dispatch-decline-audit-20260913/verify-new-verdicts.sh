#!/usr/bin/env bash
# Every verdict the fix produces that the baseline did not, checked against
# THREE independent authorities: the file's declared `:status`, z3 and cvc5.
#
# This is the check that matters. Converting a refusal into a decline lets
# later rungs answer a query they previously never saw, and a later rung that
# answers WRONGLY was masked by the early return. A disagreement here is a
# wrong answer that was previously hidden.
#
# **The units differ and mixing them silently corrupts the result**:
#   z3   -T:<SECONDS>
#   cvc5 --tlimit <MILLISECONDS>
#
# ADR-1957: a zero-disagreement claim must publish its COMPARABLE denominator,
# so every row records whether each authority actually produced a verdict.
#
# Usage: verify-new-verdicts.sh <file-with-"path<TAB>verdict"-rows> <out.tsv>
set -u
IN="$1"; OUT="$2"
Z3=z3
CVC5=/nas3/data/axeyum/harness/bin/cvc5
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
SECS=24

command -v "$Z3" >/dev/null || { echo "ABORT: z3 not on PATH"; exit 2; }
[ -x "$CVC5" ] || { echo "ABORT: $CVC5 missing"; exit 2; }

printf 'file\tours\tstatus\tz3\tcvc5\tagree\n' > "$OUT"
while IFS=$'\t' read -r rel ours; do
  [ -n "$rel" ] || continue
  f="$CORPUS$rel"
  [ -f "$f" ] || { echo "MISSING $rel"; continue; }
  st=$(grep -m1 -oE '\(set-info :status (sat|unsat|unknown)\)' "$f" \
        | grep -oE '(sat|unsat|unknown)$')
  z=$(timeout $((SECS + 10)) "$Z3" -T:$SECS "$f" 2>/dev/null \
        | grep -m1 -oE '^(sat|unsat|unknown)$')
  c=$(timeout $((SECS + 10)) "$CVC5" --tlimit $((SECS * 1000)) "$f" 2>/dev/null \
        | grep -m1 -oE '^(sat|unsat|unknown)$')
  bad=""
  for a in "st:$st" "z3:$z" "cvc5:$c"; do
    name=${a%%:*}; v=${a#*:}
    [ -z "$v" ] && continue
    [ "$v" = "unknown" ] && continue
    [ "$v" != "$ours" ] && bad="$bad $name=$v"
  done
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$rel" "$ours" "${st:-none}" "${z:-none}" "${c:-none}" \
    "${bad:-DISAGREEMENT-NONE}" >> "$OUT"
done < "$IN"

n=$(($(wc -l < "$OUT") - 1))
d=$(grep -cv 'DISAGREEMENT-NONE' "$OUT" || true)
d=$((d - 1))
echo "VERIFY-DONE rows=$n disagreements=$d"
# The exit status depends on the FINDING, not on the script having run.
[ "$d" -eq 0 ]
