#!/usr/bin/env bash
# QF-WALL R1 -- re-derive the population on the CURRENT tree, on the ORIGINAL
# benchmark files (not the skeletons), with both reach levers armed, which is
# the condition ADR-2040 measured. 24 s and 5x, the pairing that separates a
# capability limit from a budget one.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
PIN="${1:-7}"
go() { env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on AXEYUM_TRACE=1 \
        timeout $(($1 + 90)) taskset -c "$PIN" "$AX" "$CORPUS/$2" --timeout-ms $(($1 * 1000)) 2>&1; }
printf 'id\tfile\tv24\trung24\tv120\trung120\tbound_by24\tdiagnosis\n' > "$W/rederive.tsv"
while IFS=$'\t' read -r id f; do
  [ -n "$f" ] || continue
  a=$(go 24 "$f"); b=$(go 120 "$f")
  va=$(printf '%s\n' "$a" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  vb=$(printf '%s\n' "$b" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  bb=$(printf '%s' "$a" | grep -oE 'bound_by=[^ ]*' | head -1 | cut -d= -f2)
  r() { if printf '%s' "$1" | grep -qF '"route":"q:bool-skeleton","outcome":"decided"'; then echo decided
        elif printf '%s' "$1" | grep -qF '"route":"q:bool-skeleton"'; then echo declined
        else echo absent; fi; }
  ra=$(r "$a"); rb=$(r "$b")
  if [ "${va:-}" = unsat ] || [ "${va:-}" = sat ]; then d=DECIDED
  elif [ "$ra" = decided ]; then d=CONVERTED
  elif [ "$ra" = absent ] && [ "$rb" = absent ]; then d=RUNG-NEVER-REACHED
  elif [ "$rb" = decided ]; then d=BUDGET-LIMIT
  else d=CAPABILITY-LIMIT; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$f" "${va:-NONE}" "$ra" "${vb:-NONE}" "$rb" "${bb:-NONE}" "$d" >> "$W/rederive.tsv"
  printf '%-4s %-8s %-9s %-8s %s\n' "$id" "${va:-NONE}" "$ra" "${bb:-NONE}" "$d"
done < "$W/idmap.tsv"
echo DONE
awk -F'\t' 'NR>1{c[$8]++} END{for (k in c) print c[k], k}' "$W/rederive.tsv" | sort -rn
