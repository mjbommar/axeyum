#!/usr/bin/env bash
# QF-WALL -- run the LEVER SIMULATION over both the minimal cores and the full
# skeletons. See opaqueatom.py: this is the query the proposed
# `ArithAbstractor` change would hand the Boolean skeleton, built outside the
# solver so the lever can be sized before it is written.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
CVC5=/nas3/data/axeyum/harness/bin/cvc5
PIN="${1:-5}"
mkdir -p "$W/oatom"
ax() { timeout 140 taskset -c "$PIN" "$AX" "$1" --timeout-ms 24000 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$' || true; }
printf 'id\tsrc\tkept\topaqued\tax\tz3\tcvc5\n' > "$W/oatom.tsv"
for src in core skel; do
  [ "$src" = core ] && suf=.core.smt2 || suf=.smt2
  for i in $(seq -w 1 13); do
    id="f$i"; in="$W/$src/$id$suf"
    [ -r "$in" ] || continue
    o="$W/oatom/$id.$src.smt2"; rm -f "$o"
    m=$(timeout 900 python3 "$W/opaqueatom.py" "$in" "$o" 2>&1 >/dev/null) || true
    if [ ! -s "$o" ]; then
      printf '%s\t%s\tDID-NOT-RUN\t-\t-\t-\t-\n' "$id" "$src" >> "$W/oatom.tsv"
      printf '%-4s %-5s DID-NOT-RUN\n' "$id" "$src"; continue
    fi
    k=$(printf '%s' "$m" | grep -oE 'atoms_kept=[0-9]+' | cut -d= -f2)
    q=$(printf '%s' "$m" | grep -oE 'atoms_opaqued=[0-9]+' | cut -d= -f2)
    a=$(ax "$o"); z=$(timeout 200 z3 -T:60 "$o" 2>&1|head -1); c=$(timeout 200 "$CVC5" --tlimit 60000 "$o" 2>&1|head -1)
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$src" "$k" "$q" "${a:-NONE}" "$z" "$c" >> "$W/oatom.tsv"
    printf '%-4s %-5s kept=%-5s opaqued=%-6s axeyum=%-8s z3=%-7s cvc5=%s\n' "$id" "$src" "$k" "$q" "${a:-NONE}" "$z" "$c"
  done
done
echo DONE
