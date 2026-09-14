#!/usr/bin/env bash
# QF-WALL R2 -- the ADMISSIBLE re-derivation of the population. Three atom maps
# over the SAME 13 files, all three verdicts printed:
#   shared-by-text      what the census used (not unconditionally sound)
#   fresh-per-occurrence  the abstractor's own control (sound, weakest)
#   structural-after-let  sound AND sharing (scopeskel.py) -- the decider
set -u
W="$(cd "$(dirname "$0")" && pwd)"
CVC5=/nas3/data/axeyum/harness/bin/cvc5
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
mkdir -p "$W/scope"
printf 'id\tocc\tatoms\tz3\tcvc5\tadmissible\n' > "$W/scopeskel.tsv"
while IFS=$'\t' read -r id f; do
  [ -n "$f" ] || continue
  o="$W/scope/$id.smt2"; rm -f "$o"
  m=$(timeout 900 python3 "$W/scopeskel.py" "$CORPUS/$f" "$o" 2>&1 >/dev/null) || true
  if [ ! -s "$o" ]; then
    printf '%s\tDID-NOT-RUN\t-\t-\t-\tDID-NOT-RUN\n' "$id" >> "$W/scopeskel.tsv"
    printf '%-4s DID-NOT-RUN\n' "$id"; continue
  fi
  oc=$(printf '%s' "$m" | grep -oE 'occurrences=[0-9]+' | cut -d= -f2)
  at=$(printf '%s' "$m" | grep -oE 'distinct_atoms=[0-9]+' | cut -d= -f2)
  z=$(timeout 300 z3 -T:120 "$o" 2>&1 | head -1)
  c=$(timeout 300 "$CVC5" --tlimit 120000 "$o" 2>&1 | head -1)
  if [ "$z" = unsat ] && [ "$c" = unsat ]; then a=ADMISSIBLE
  elif [ "$z" = "$c" ]; then a="NOT-ADMISSIBLE($z)"
  else a="DISAGREE($z/$c)"; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$oc" "$at" "$z" "$c" "$a" >> "$W/scopeskel.tsv"
  printf '%-4s occ=%-5s atoms=%-5s z3=%-7s cvc5=%-7s %s\n' "$id" "$oc" "$at" "$z" "$c" "$a"
done < "$W/idmap.tsv"
echo DONE
awk -F'\t' 'NR>1{c[$6]++} END{for (k in c) print c[k], k}' "$W/scopeskel.tsv" | sort -rn
