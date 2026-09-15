#!/usr/bin/env bash
# SILENT-HANG -- what two independent solvers say about the 9, so "we do not
# decide these" can be read against "these are decidable at this budget".
#
# ADR-1957: a zero-disagreement claim must publish its COMPARABLE denominator.
# A row where an authority also says `unknown` or times out is a NO-OPINION and
# is counted in its own column, never as an agreement and never as a zero.
#
# The unit trap, which has been paid for here before:
#   z3   -T:<SECONDS>
#   cvc5 --tlimit=<MILLISECONDS>
# The two flags below are deliberately NOT written to look alike.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
LIST="$1"; OUT="$2"; BUDGET="${3:-24}"; PIN="${4:-14}"
CORPUS="${SH_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
Z3="${SH_Z3:-/usr/bin/z3}"
CVC5="${SH_CVC5:-/nas3/data/axeyum/harness/bin/cvc5}"
for b in "$Z3" "$CVC5"; do [ -x "$b" ] || { echo "ABORT: $b missing"; exit 2; }; done
echo "z3:   $("$Z3" --version 2>&1 | head -1)"
echo "cvc5: $("$CVC5" --version 2>&1 | head -1)"
echo "budget: ${BUDGET}s  (z3 -T:${BUDGET}  |  cvc5 --tlimit=$((BUDGET * 1000)))"

printf 'file\tz3\tz3_ms\tcvc5\tcvc5_ms\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  t0=$(( $(date +%s%N) / 1000000 ))
  z=$(timeout $((BUDGET + 30)) taskset -c "$PIN" "$Z3" -T:"$BUDGET" "$CORPUS/$f" 2>&1 \
        | grep -m1 -oE '^(sat|unsat|unknown|timeout)' || true)
  t1=$(( $(date +%s%N) / 1000000 ))
  c=$(timeout $((BUDGET + 30)) taskset -c "$PIN" "$CVC5" --tlimit=$((BUDGET * 1000)) "$CORPUS/$f" 2>&1 \
        | grep -m1 -oE '^(sat|unsat|unknown)' || true)
  t2=$(( $(date +%s%N) / 1000000 ))
  printf '%s\t%s\t%s\t%s\t%s\n' "$f" "${z:-NO-OUTPUT}" "$((t1-t0))" "${c:-NO-OUTPUT}" "$((t2-t1))" >> "$OUT"
  printf '%-52s z3=%-9s %6sms  cvc5=%-9s %6sms\n' "$(basename "$f" | cut -c1-52)" \
    "${z:-NO-OUTPUT}" "$((t1-t0))" "${c:-NO-OUTPUT}" "$((t2-t1))"
done < "$LIST"

echo
echo "=== the comparable denominator (ADR-1957) ==="
awk -F'\t' 'NR>1{
  n++;
  zd = ($2=="sat"||$2=="unsat"); cd = ($4=="sat"||$4=="unsat");
  if (zd) z++; if (cd) c++;
  if (zd && cd) both++;
  if (!zd && !cd) neither++;
} END {
  printf "rows                       : %d\n", n;
  printf "z3 decided                 : %d\n", z;
  printf "cvc5 decided               : %d\n", c;
  printf "BOTH decided (comparable)  : %d   <- the only denominator an agreement claim may use\n", both;
  printf "NEITHER decided (no-opinion): %d\n", neither;
}' "$OUT"
echo "DONE $OUT"
