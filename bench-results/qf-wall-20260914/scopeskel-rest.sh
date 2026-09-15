#!/usr/bin/env bash
# QF-WALL R2, remainder -- under a HARD address-space ceiling.
#
# WHY THE CEILING. The first run of this script had none, and `let`-expansion
# on UFNIA/lahiri-cav09-storm-queries/usbsamp_bug_example_2_3_8_1.smt2 (724 KB,
# 107 nested `let` bindings, expansion exponential in the nesting) reached
# 63.4 GB resident and the kernel OOM-killer fired globally on s4, taking the
# session with it. `cargo-serialized.sh` bounds cargo; NOTHING bounds a lane's
# own Python. `ulimit -v` is that bound, and it must be set by every script
# here that expands a `let`, not only this one.
#
# f07 and f10 are SKIPPED BY NAME, not by ceiling: they are the two files whose
# expansion cannot finish, so running them only buys a MemoryError. They are
# reported DID-NOT-RUN and are counted in no bucket.
set -u
W="$(cd "$(dirname "$0")" && pwd)"
CVC5=/nas3/data/axeyum/harness/bin/cvc5
CORPUS=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental
mkdir -p "$W/scope"
for id in f07 f08 f09 f10 f11 f12 f13; do
  f=$(awk -F'\t' -v i="$id" '$1==i{print $2}' "$W/idmap.tsv")
  [ -n "$f" ] || continue
  if [ "$id" = f07 ] || [ "$id" = f10 ]; then
    printf '%s\tDID-NOT-RUN\t-\t-\t-\tDID-NOT-RUN(let-expansion does not terminate in bounded memory)\n' "$id" >> "$W/scopeskel.tsv"
    printf '%-4s DID-NOT-RUN (let-expansion unbounded)\n' "$id"; continue
  fi
  o="$W/scope/$id.smt2"; rm -f "$o"
  m=$( (ulimit -v 8388608; timeout 900 python3 "$W/scopeskel.py" "$CORPUS/$f" "$o") 2>&1 >/dev/null ) || true
  if [ ! -s "$o" ]; then
    printf '%s\tDID-NOT-RUN\t-\t-\t-\tDID-NOT-RUN\n' "$id" >> "$W/scopeskel.tsv"
    printf '%-4s DID-NOT-RUN\n' "$id"; continue
  fi
  oc=$(printf '%s' "$m" | grep -oE 'occurrences=[0-9]+' | cut -d= -f2)
  at=$(printf '%s' "$m" | grep -oE 'distinct_atoms=[0-9]+' | cut -d= -f2)
  z=$(timeout 400 z3 -T:180 "$o" 2>&1 | head -1)
  c=$(timeout 400 "$CVC5" --tlimit 180000 "$o" 2>&1 | head -1)
  if [ "$z" = unsat ] && [ "$c" = unsat ]; then a=ADMISSIBLE
  elif [ "$z" = "$c" ]; then a="NOT-ADMISSIBLE($z)"
  else a="DISAGREE($z/$c)"; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$oc" "$at" "$z" "$c" "$a" >> "$W/scopeskel.tsv"
  printf '%-4s occ=%-5s atoms=%-5s z3=%-7s cvc5=%-7s %s\n' "$id" "$oc" "$at" "$z" "$c" "$a"
done
echo DONE
awk -F'\t' 'NR>1{c[$6]++} END{for (k in c) print c[k], k}' "$W/scopeskel.tsv" | sort -rn
