#!/usr/bin/env bash
# SKELETON-REACH -- split the NOT-REFUTABLE bucket the way ADR-2025 split its
# own: is the rung's decline a CAPABILITY limit or a BUDGET limit?
#
#   capability-vs-budget.sh <list> <out.tsv> [core] [bin]
#
# Each row is run at the A/B budget and at 5x it. The PAIRING is what makes
# this a diagnosis rather than a description:
#
#   declines at BOTH       -> CAPABILITY: our ground checker cannot refute a
#                             skeleton cvc5 AND z3 both refute. More time does
#                             not help and a budget lever buys nothing.
#   decides at 5x only     -> BUDGET: the rung takes one tenth of the query
#                             budget and this skeleton needs more.
#   rung absent at both    -> NOT REACHED; a different problem entirely.
#
# Both levers are ARMED here, because the not-reached rows are only reachable
# with them and the point is to classify what happens AFTER reaching.
set -u
LIST="$1"
OUT="$2"
PIN="${3:-10}"
AX="${4:-/nas3/data/axeyum/harness/skeleton-reach/bin/smtcomp_cli-arm}"
CORPUS="${SKEL_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

go() { # $1=budget_s $2=file
  env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on AXEYUM_TRACE=1 \
    timeout $(($1 + 60)) taskset -c "$PIN" "$AX" "$CORPUS/$2" --timeout-ms $(($1 * 1000)) 2>&1
}
rung() {
  if printf '%s' "$1" | grep -qF '"route":"q:bool-skeleton","outcome":"decided"'; then echo decided
  elif printf '%s' "$1" | grep -qF '"route":"q:bool-skeleton"'; then echo declined
  else echo absent; fi
}

printf 'file\tv24\trung24\tv120\trung120\tdiagnosis\n' > "$OUT"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  a=$(go 24 "$f"); b=$(go 120 "$f")
  va=$(printf '%s\n' "$a" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  vb=$(printf '%s\n' "$b" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  ra=$(rung "$a"); rb=$(rung "$b")
  if [ "$ra" = decided ]; then d=CONVERTED
  elif [ "$ra" = absent ] && [ "$rb" = absent ]; then d=RUNG-NEVER-REACHED
  elif [ "$rb" = decided ]; then d=BUDGET-LIMIT
  else d=CAPABILITY-LIMIT; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$f" "${va:-NONE}" "$ra" "${vb:-NONE}" "$rb" "$d" >> "$OUT"
  printf '%-58s %s\n' "$(basename "$f" | cut -c1-56)" "$d"
done < "$LIST"
echo "DONE $OUT"
awk -F'\t' 'NR>1{c[$6]++} END{for (k in c) print c[k], k}' "$OUT" | sort -rn
