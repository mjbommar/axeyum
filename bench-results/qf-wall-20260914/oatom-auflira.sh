#!/usr/bin/env bash
# QF-WALL -- lever simulation on the remaining AUFLIRA rows, taken on BOTH the
# minimal core and the FULL quantifier-free skeleton. The full skeleton is the
# one that matters for sizing: it is the query the rung actually hands the
# ground checker.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
CVC5=/nas3/data/axeyum/harness/bin/cvc5
PIN="${2:-8}"
mkdir -p "$W/oatom"
ax() { env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on timeout 140 taskset -c "$PIN" "$AX" "$1" --timeout-ms 24000 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$' || true; }
printf 'id\tsrc\tkept\topaqued\tax_before\tax_after\tz3_after\tcvc5_after\n' > "$W/oatom-auflira.tsv"
for id in $1; do
  for src in core skel; do
    [ "$src" = core ] && suf=.core.smt2 || suf=.smt2
    in="$W/$src/$id$suf"; [ -r "$in" ] || continue
    o="$W/oatom/$id.$src.smt2"; rm -f "$o"
    m=$(timeout 600 python3 "$W/opaqueatom.py" "$in" "$o" 2>&1 >/dev/null) || true
    [ -s "$o" ] || { printf '%s\t%s\tDID-NOT-RUN\t-\t-\t-\t-\t-\n' "$id" "$src" >> "$W/oatom-auflira.tsv"; echo "$id $src DID-NOT-RUN"; continue; }
    k=$(printf '%s' "$m" | grep -oE 'atoms_kept=[0-9]+' | cut -d= -f2)
    q=$(printf '%s' "$m" | grep -oE 'atoms_opaqued=[0-9]+' | cut -d= -f2)
    b=$(ax "$in"); a=$(ax "$o")
    z=$(timeout 200 z3 -T:60 "$o" 2>&1|head -1); c=$(timeout 200 "$CVC5" --tlimit 60000 "$o" 2>&1|head -1)
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$src" "$k" "$q" "${b:-NONE}" "${a:-NONE}" "$z" "$c" >> "$W/oatom-auflira.tsv"
    printf '%-4s %-5s kept=%-5s opaqued=%-6s before=%-8s after=%-8s z3=%-7s cvc5=%s\n' "$id" "$src" "$k" "$q" "${b:-NONE}" "${a:-NONE}" "$z" "$c"
  done
done
echo DONE
