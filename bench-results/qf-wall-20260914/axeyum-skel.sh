#!/usr/bin/env bash
# QF-WALL -- hand OUR solver the QUANTIFIER-FREE skeleton directly, as a
# standalone query. This removes the quantified ladder, the rung, the budget
# split and the instantiation machinery from the picture entirely: whatever
# happens here is the ground checker's own answer on a ground query.
#
#   axeyum-skel.sh <dir> <suffix> <out.tsv> [budget_s] [core]
set -u
W="$(cd "$(dirname "$0")" && pwd)"
DIR="$1"; SUF="$2"; OUT="$3"; TL="${4:-24}"; PIN="${5:-2}"
AX=/nas3/data/axeyum/harness/qf-wall/bin/smtcomp_cli-qfwall
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
printf 'id\tverdict\tms\tbound_by\tgiveup\n' > "$OUT"
for i in $(seq -w 1 13); do
  id="f$i"
  f="$DIR/$id$SUF"
  [ -r "$f" ] || { printf '%s\tNO-FILE\t-\t-\t-\n' "$id" >> "$OUT"; printf '%-4s NO-FILE\n' "$id"; continue; }
  t0=$(date +%s%3N)
  o=$(env AXEYUM_TRACE=1 timeout $((TL + 60)) taskset -c "$PIN" "$AX" "$f" --timeout-ms $((TL * 1000)) 2>&1)
  t1=$(date +%s%3N)
  v=$(printf '%s\n' "$o" | grep -m1 -oE '^(sat|unsat|unknown)$' || true)
  b=$(printf '%s' "$o" | grep -oE '"bound_by":"[^"]*"' | head -1 | cut -d'"' -f4)
  g=$(printf '%s' "$o" | grep -oE '"giveup"[^,}]*' | head -1 | cut -c1-110)
  printf '%s\t%s\t%s\t%s\t%s\n' "$id" "${v:-NONE}" "$((t1-t0))" "${b:-NONE}" "${g:-none}" >> "$OUT"
  printf '%-4s %-8s %6sms  bound_by=%-16s %s\n' "$id" "${v:-NONE}" "$((t1-t0))" "${b:-NONE}" "${g:-none}"
done
echo "DONE $OUT"
