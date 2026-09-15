#!/usr/bin/env bash
# QF-WALL R1: re-derive the population's AUTHORITY half.
# Both reference solvers, both atom maps. The fresh-per-occurrence map is the
# soundness control (unconditionally a weakening); if shared and fresh disagree
# the shared map manufactured the unsat and the row is NOT admissible.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
CVC5=/nas3/data/axeyum/harness/bin/cvc5
printf 'id\tz3_shared\tz3_ms\tcvc5_shared\tcvc5_ms\tz3_fresh\tcvc5_fresh\n' > "$W/authority.tsv"
for i in $(seq -w 1 13); do
  id="f$i"
  t0=$(date +%s%3N)
  zs=$(timeout 90 z3 -T:60 "$W/skel/$id.smt2" 2>&1 | head -1)
  t1=$(date +%s%3N)
  cs=$(timeout 90 "$CVC5" --tlimit 60000 "$W/skel/$id.smt2" 2>&1 | head -1)
  t2=$(date +%s%3N)
  zf=$(timeout 90 z3 -T:60 "$W/skel/$id.fresh.smt2" 2>&1 | head -1)
  cf=$(timeout 90 "$CVC5" --tlimit 60000 "$W/skel/$id.fresh.smt2" 2>&1 | head -1)
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$zs" "$((t1-t0))" "$cs" "$((t2-t1))" "$zf" "$cf" >> "$W/authority.tsv"
  printf '%s z3=%s cvc5=%s fresh z3=%s cvc5=%s\n' "$id" "$zs" "$cs" "$zf" "$cf"
done
echo "DONE"
