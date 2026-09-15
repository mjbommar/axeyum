#!/usr/bin/env bash
# LEMMA-INPUT -- R17/D3: what an INPUT CAP on the mutex pass COSTS.
#
# POLARITY: BASE is every lever unset -- the shipped pass, which reads whatever
# it is given.  CAP is `AXEYUM_LIA_INITIAL_BOUND_MUTEX_ATOM_CAP=1`, which makes
# the pass DECLINE above 512 atoms, the value its sibling already uses.  A
# "cost" is a row decided under BASE and not decided under CAP.
#
# This is deliberately run against the DECIDED half of the census, because a cap
# that only makes undecided rows finish sooner costs nothing and proves nothing:
# ADR-2055 measured a cap of this shape costing 18 clean exits, and that is only
# visible on rows that were exiting cleanly.
#
# One binary, two environment values, same pinned core, arms back to back,
# order alternating.
set -u
IFS=$'\t' read -r core file budget ordinal <<< "$1"
CORPUS="${LI_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${LI_AB_AX:-/data0/axeyum/lemma-input-bin/smtcomp_cli-B}"

run_arm() {
  local arm="$1" out t0 t1 status verdict
  out=$(mktemp -t "li-cap-XXXXXX")
  t0=$(date +%s%N)
  if [ "$arm" = cap ]; then
    AXEYUM_LIA_INITIAL_BOUND_MUTEX_ATOM_CAP=1 \
      taskset -c "$core" timeout $((budget + 120)) \
      "$AX" "$CORPUS/$file" --timeout-ms $((budget * 1000)) > "$out" 2>/dev/null
  else
    env -u AXEYUM_LIA_INITIAL_BOUND_MUTEX_ATOM_CAP \
      taskset -c "$core" timeout $((budget + 120)) \
      "$AX" "$CORPUS/$file" --timeout-ms $((budget * 1000)) > "$out" 2>/dev/null
  fi
  status=$?
  t1=$(date +%s%N)
  verdict=$(grep -m1 -E '^(sat|unsat|unknown)$' "$out" || true)
  [ -n "$verdict" ] || verdict=NOVERDICT
  printf '%s\t%s\t%s\t%s\t%s\tNA\n' \
    "$file" "$arm" "$verdict" "$status" "$(((t1 - t0) / 1000000))"
  rm -f "$out"
}

if [ $((ordinal % 2)) -eq 0 ]; then
  run_arm base
  run_arm cap
else
  run_arm cap
  run_arm base
fi
