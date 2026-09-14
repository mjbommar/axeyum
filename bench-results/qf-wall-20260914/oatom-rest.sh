#!/usr/bin/env bash
# QF-WALL -- complete the lever-simulation column on the rows the first run did
# not reach. Under `ulimit -v`, for the reason recorded in scopeskel-rest.sh.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
CVC5=/nas3/data/axeyum/harness/bin/cvc5
PIN="${2:-8}"
mkdir -p "$W/oatom"
ax() { env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on timeout 140 taskset -c "$PIN" "$AX" "$1" --timeout-ms 24000 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$' || true; }
for id in $1; do
  in="$W/skel/$id.smt2"; [ -r "$in" ] || continue
  o="$W/oatom/$id.skel.smt2"; rm -f "$o"
  m=$( (ulimit -v 8388608; timeout 600 python3 "$W/opaqueatom.py" "$in" "$o") 2>&1 >/dev/null ) || true
  if [ ! -s "$o" ]; then
    printf '%s\tskel\tDID-NOT-RUN\t-\t-\t-\t-\t-\n' "$id" >> "$W/oatom-auflira.tsv"
    printf '%-4s skel DID-NOT-RUN\n' "$id"; continue
  fi
  k=$(printf '%s' "$m" | grep -oE 'atoms_kept=[0-9]+' | cut -d= -f2)
  q=$(printf '%s' "$m" | grep -oE 'atoms_opaqued=[0-9]+' | cut -d= -f2)
  b=$(ax "$in"); a=$(ax "$o")
  z=$(timeout 300 z3 -T:120 "$o" 2>&1|head -1); c=$(timeout 300 "$CVC5" --tlimit 120000 "$o" 2>&1|head -1)
  printf '%s\tskel\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$k" "$q" "${b:-NONE}" "${a:-NONE}" "$z" "$c" >> "$W/oatom-auflira.tsv"
  printf '%-4s skel kept=%-6s opaqued=%-6s before=%-8s after=%-8s z3=%-7s cvc5=%s\n' "$id" "$k" "$q" "${b:-NONE}" "${a:-NONE}" "$z" "$c"
done
echo DONE
