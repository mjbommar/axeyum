#!/usr/bin/env bash
# Re-validate every newly decided file against BOTH independent oracles and its
# declared :status. Units differ and getting one wrong cripples a reference
# silently: z3 takes SECONDS (-T:), cvc5 takes MILLISECONDS (--tlimit).
set -u
LIST="$1"; OUT="$2"; BUDGET="${3:-24}"
Z3=/usr/bin/z3
CVC5=/nas3/data/axeyum/harness/bin/cvc5
AX=/nas3/data/axeyum/harness/dt-capability/bin/smtcomp_cli.new
VLIM=$((8 * 1024 * 1024))

one() { # $1 cmd... -> verdict
  local raw rc
  raw=$(timeout $((BUDGET + 16)) bash -c "ulimit -v $VLIM; exec \"\$@\"" _ "$@" 2>&1)
  rc=$?
  [ "$rc" = 124 ] && { echo "wrapper-killed"; return; }
  [ "$rc" = 134 ] && { echo "rc134"; return; }
  printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$' || echo "none"
}

printf 'file\taxeyum\tz3\tcvc5\tstatus\n' > "$OUT"
while read -r f; do
  [ -n "$f" ] || continue
  a=$(one "$AX" "$f" --timeout-ms $((BUDGET * 1000)))
  z=$(one "$Z3" -T:"$BUDGET" "$f")
  c=$(one "$CVC5" --tlimit "$((BUDGET * 1000))" "$f")
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' "$f" | awk '{print $2}')
  printf '%s\t%s\t%s\t%s\t%s\n' "$f" "$a" "$z" "$c" "${st:-none}" >> "$OUT"
done < "$LIST"
echo "VERIFY-DONE $(($(wc -l < "$OUT") - 1)) rows"
