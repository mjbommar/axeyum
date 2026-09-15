#!/usr/bin/env bash
# QF-WALL -- our verdict on the ADMISSIBLE quantifier-free query.
#
# The census's skeleton uses the shared-BY-TEXT atom map, which is not
# unconditionally sound. `scopeskel.py`'s is (sharing only after `let`
# expansion). So the scope-correct skeleton is the query the headline claim is
# actually about: "a quantifier-free query z3 and cvc5 both refute and we
# cannot". This measures the `and we cannot` half against the right file.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
PIN="${1:-8}"
printf 'id\tax_24\tax_120\tbound_by24\tgiveup24\n' > "$W/scope-ax.tsv"
for i in $(seq -w 1 13); do
  id="f$i"; f="$W/scope/$id.smt2"
  [ -r "$f" ] || { printf '%s\tNO-FILE\t-\t-\t-\n' "$id" >> "$W/scope-ax.tsv"; printf '%-4s NO-FILE\n' "$id"; continue; }
  a=$(env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on AXEYUM_TRACE=1 timeout 200 taskset -c "$PIN" "$AX" "$f" --timeout-ms 24000 2>&1)
  b=$(env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on timeout 400 taskset -c "$PIN" "$AX" "$f" --timeout-ms 120000 2>&1)
  va=$(printf '%s\n' "$a" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo NONE)
  vb=$(printf '%s\n' "$b" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo NONE)
  bb=$(printf '%s' "$a" | grep -oE 'bound_by=[^ ]*' | head -1 | cut -d= -f2)
  g=$(printf '%s' "$a" | grep -oE '^; give-up .*' | head -1 | cut -c1-150)
  printf '%s\t%s\t%s\t%s\t%s\n' "$id" "$va" "$vb" "${bb:-NONE}" "${g:-none}" >> "$W/scope-ax.tsv"
  printf '%-4s 24s=%-8s 120s=%-8s bound_by=%-22s %s\n' "$id" "$va" "$vb" "${bb:-NONE}" "${g:-none}"
done
echo DONE
