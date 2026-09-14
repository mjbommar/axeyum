#!/usr/bin/env bash
# QF-WALL -- SIZING. For each row, run OUR solver on three queries that differ
# only in how much of the theory has been abstracted away, and on nothing else:
#
#   skel  the quantifier-free skeleton as the census produced it
#   pur   the same, with UF applications / array selects inside the arithmetic
#         replaced by fresh constants of the same sort (purification)
#   prop  the same, with EVERY theory atom replaced by an opaque Bool
#
# `pur` and `prop` are both weakenings, so an `unsat` on either entails `unsat`
# on `skel`.  A row that we answer on `pur` but not on `skel` is converted by
# purification; a row we answer on `prop` is converted by opaque-atom
# abstraction alone, which needs no theory solver at all.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
CVC5=/nas3/data/axeyum/harness/bin/cvc5
PIN="${1:-3}"
mkdir -p "$W/pur"
printf 'id\tax_skel\tax_pur\tax_prop\tz3_pur\tcvc5_pur\tpur_terms\n' > "$W/sizing.tsv"
ax() { timeout 120 taskset -c "$PIN" "$AX" "$1" --timeout-ms 24000 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$' || true; }
for i in $(seq -w 1 13); do
  id="f$i"
  s="$W/skel/$id.smt2"
  p="$W/pur/$id.full.smt2"
  q="$W/prop/$id.full.smt2"
  rm -f "$p"
  meta=$(timeout 600 python3 "$W/purify.py" "$s" "$p" 2>&1 >/dev/null) || true
  if [ -s "$p" ]; then
    np=$(printf '%s' "$meta" | grep -oE 'purified_terms=[0-9]+' | cut -d= -f2)
    zp=$(timeout 200 z3 -T:60 "$p" 2>&1 | head -1)
    c5=$(timeout 200 "$CVC5" --tlimit 60000 "$p" 2>&1 | head -1)
    ap=$(ax "$p")
  else
    np=DID-NOT-RUN; zp=-; c5=-; ap=-
  fi
  as=$(ax "$s")
  if [ -s "$q" ]; then aq=$(ax "$q"); else aq=DID-NOT-RUN; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "${as:-NONE}" "${ap:-NONE}" "${aq:-NONE}" "$zp" "$c5" "$np" >> "$W/sizing.tsv"
  printf '%-4s skel=%-8s pur=%-8s prop=%-11s | z3_pur=%-7s cvc5_pur=%-7s pur_terms=%s\n' \
     "$id" "${as:-NONE}" "${ap:-NONE}" "${aq:-NONE}" "$zp" "$c5" "$np"
done
echo DONE
