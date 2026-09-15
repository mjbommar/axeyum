#!/usr/bin/env bash
# QF-WALL -- the decisive per-file classification: does the refutation need a
# THEORY SOLVER AT ALL, or only propositional resolution over opaque atoms?
# Run over the FULL quantifier skeleton, so no minimisation is presupposed.
#
# `let`-expansion can blow up, so each row is bounded and a row that does not
# finish is reported as DID-NOT-RUN rather than folded into either bucket.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
CVC5=/nas3/data/axeyum/harness/bin/cvc5
mkdir -p "$W/prop"
printf 'id\tabs_status\tbytes\tatoms\tz3\tcvc5\n' > "$W/propsweep.tsv"
for i in $(seq -w 1 13); do
  id="f$i"
  o="$W/prop/$id.full.smt2"
  rm -f "$o"
  meta=$(timeout 300 python3 "$W/propabstract.py" "$W/skel/$id.smt2" "$o" 2>&1 >/dev/null)
  rc=$?
  if [ $rc -ne 0 ] || [ ! -s "$o" ]; then
    printf '%s\tDID-NOT-RUN(rc=%s)\t-\t-\t-\t-\n' "$id" "$rc" >> "$W/propsweep.tsv"
    printf '%-4s DID-NOT-RUN rc=%s\n' "$id" "$rc"
    continue
  fi
  at=$(printf '%s' "$meta" | grep -oE 'atoms=[0-9]+' | cut -d= -f2)
  z=$(timeout 300 z3 -T:120 "$o" 2>&1 | head -1)
  c=$(timeout 300 "$CVC5" --tlimit 120000 "$o" 2>&1 | head -1)
  printf '%s\tOK\t%s\t%s\t%s\t%s\n' "$id" "$(stat -c%s "$o")" "$at" "$z" "$c" >> "$W/propsweep.tsv"
  printf '%-4s atoms=%-6s z3=%-7s cvc5=%s\n' "$id" "$at" "$z" "$c"
done
echo DONE
