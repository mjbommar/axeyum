#!/usr/bin/env bash
# Do the references decide the files our front door refuses on the `distinct`
# pair-expansion cap? This is the SIZING of that handoff, measured rather than
# inherited from another lane's winnable set.
# z3 -T:<SECONDS>, cvc5 --tlimit <MILLISECONDS>. The units differ.
set -u
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/
CVC5=/nas3/data/axeyum/harness/bin/cvc5
printf 'file\tstatus\tz3\tz3_ms\tcvc5\tcvc5_ms\n'
while read -r rel; do
  [ -n "$rel" ] || continue
  f="$CORPUS$rel"
  st=$(grep -m1 -oE ':status +(sat|unsat|unknown)' -- "$f" | awk '{print $2}')
  t0=$(date +%s%N); z=$(timeout 34 z3 -T:24 "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$'); t1=$(date +%s%N)
  t2=$(date +%s%N); c=$(timeout 34 "$CVC5" --tlimit 24000 "$f" 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$'); t3=$(date +%s%N)
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$rel" "${st:-none}" "${z:-none}" \
    "$(( (t1-t0)/1000000 ))" "${c:-none}" "$(( (t3-t2)/1000000 ))"
done
