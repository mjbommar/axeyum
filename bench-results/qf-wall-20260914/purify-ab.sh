#!/usr/bin/env bash
# QF-WALL -- the mechanism test. One solver, two queries that differ on ONE
# axis: whether the arithmetic atoms have non-arithmetic LEAVES (UF
# applications, array selects) or fresh arithmetic constants in their place.
#
# If axeyum answers `unknown` on the first and `unsat` on the second, the
# missing capability is purification of the arithmetic atoms, named by
# mechanism rather than inferred from a verdict count.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
SRC="${1:-core}"; SUF="${2:-.core.smt2}"; OUT="${3:-$W/purify-ab.tsv}"
CVC5=/nas3/data/axeyum/harness/bin/cvc5
mkdir -p "$W/pur"
printf 'id\tpurified\tz3_pur\tcvc5_pur\tax_orig\tax_pur\n' > "$OUT"
for i in $(seq -w 1 13); do
  id="f$i"
  in="$W/$SRC/$id$SUF"
  [ -r "$in" ] || continue
  o="$W/pur/$id.pur.smt2"
  rm -f "$o"
  meta=$(timeout 300 python3 "$W/purify.py" "$in" "$o" 2>&1 >/dev/null) || {
    printf '%s\tDID-NOT-RUN\t-\t-\t-\t-\n' "$id" >> "$OUT"; echo "$id DID-NOT-RUN"; continue; }
  np=$(printf '%s' "$meta" | grep -oE 'purified_terms=[0-9]+' | cut -d= -f2)
  zp=$(timeout 200 z3 -T:60 "$o" 2>&1 | head -1)
  cp5=$(timeout 200 "$CVC5" --tlimit 60000 "$o" 2>&1 | head -1)
  ao=$(timeout 120 taskset -c 2 "$AX" "$in" --timeout-ms 20000 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  ap=$(timeout 120 taskset -c 2 "$AX" "$o" --timeout-ms 20000 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$np" "$zp" "$cp5" "${ao:-NONE}" "${ap:-NONE}" >> "$OUT"
  printf '%-4s purified=%-5s z3=%-7s cvc5=%-7s axeyum_orig=%-8s axeyum_purified=%s\n' \
    "$id" "$np" "$zp" "$cp5" "${ao:-NONE}" "${ap:-NONE}"
done
echo DONE
