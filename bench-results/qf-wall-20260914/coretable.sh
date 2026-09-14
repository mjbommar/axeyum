#!/usr/bin/env bash
# QF-WALL -- the per-row capability table, taken on the MINIMAL unsat subset.
#
# Four queries per row, each a weakening of the one before it, all handed to
# ONE solver.  The first one we answer names the capability the refutation
# needs, because the only difference between consecutive columns is the axis
# named:
#
#   core   the minimal unsat subset of the skeleton (selection already done
#          FOR us -- so an `unknown` here is a capability limit, and an `unsat`
#          here on a row we miss on the full skeleton is a SELECTION limit)
#   pur    the same with UF applications / array selects inside the arithmetic
#          replaced by fresh constants of the same sort  [purification]
#   prop   the same with EVERY theory atom replaced by an opaque Bool
#          [opaque-atom abstraction; needs no theory solver at all]
set -u
W="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
CVC5=/nas3/data/axeyum/harness/bin/cvc5
PIN="${1:-4}"
mkdir -p "$W/pur" "$W/prop"
ax() { timeout 120 taskset -c "$PIN" "$AX" "$1" --timeout-ms 24000 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$' || true; }
printf 'id\tconjuncts\tax_core\tax_corepur\tax_coreprop\tz3_corepur\tcvc5_corepur\tz3_coreprop\tcvc5_coreprop\tpur_n\tprop_n\n' > "$W/coretable.tsv"
for i in $(seq -w 1 13); do
  id="f$i"
  c="$W/core/$id.core.smt2"
  [ -r "$c" ] || { printf '%s\tNO-CORE\t-\t-\t-\t-\t-\t-\t-\t-\t-\n' "$id" >> "$W/coretable.tsv"; echo "$id NO-CORE"; continue; }
  nc=$(grep -c '^(assert' "$c")
  p="$W/pur/$id.corepur.smt2"; q="$W/prop/$id.coreprop.smt2"
  rm -f "$p" "$q"
  mp=$(timeout 600 python3 "$W/purify.py" "$c" "$p" 2>&1 >/dev/null) || true
  mq=$(timeout 600 python3 "$W/propabstract.py" "$c" "$q" 2>&1 >/dev/null) || true
  pn=$(printf '%s' "$mp" | grep -oE 'purified_terms=[0-9]+' | cut -d= -f2); pn=${pn:-DID-NOT-RUN}
  qn=$(printf '%s' "$mq" | grep -oE 'atoms=[0-9]+' | cut -d= -f2); qn=${qn:-DID-NOT-RUN}
  a1=$(ax "$c")
  if [ -s "$p" ]; then a2=$(ax "$p"); z2=$(timeout 200 z3 -T:60 "$p" 2>&1|head -1); c2=$(timeout 200 "$CVC5" --tlimit 60000 "$p" 2>&1|head -1); else a2=DID-NOT-RUN; z2=-; c2=-; fi
  if [ -s "$q" ]; then a3=$(ax "$q"); z3v=$(timeout 200 z3 -T:60 "$q" 2>&1|head -1); c3=$(timeout 200 "$CVC5" --tlimit 60000 "$q" 2>&1|head -1); else a3=DID-NOT-RUN; z3v=-; c3=-; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$nc" "${a1:-NONE}" "${a2:-NONE}" "${a3:-NONE}" "$z2" "$c2" "$z3v" "$c3" "$pn" "$qn" >> "$W/coretable.tsv"
  printf '%-4s n=%-4s core=%-8s pur=%-11s prop=%-11s | z3/cvc5 pur=%s/%s prop=%s/%s\n' "$id" "$nc" "${a1:-NONE}" "${a2:-NONE}" "${a3:-NONE}" "$z2" "$c2" "$z3v" "$c3"
done
echo DONE
