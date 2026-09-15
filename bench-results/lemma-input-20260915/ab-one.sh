#!/usr/bin/env bash
# LEMMA-INPUT -- the interleaved per-file A/B, one row.
#
# POLARITY, stated here rather than inferred from a column name:
#   BASE = `AXEYUM_LIA_INITIAL_BOUND_INDEX` UNSET -- the shipped refresh, which
#          rebuilds the bound set from scratch on every assertion.
#   ARM  = `AXEYUM_LIA_INITIAL_BOUND_INDEX=1`     -- the incremental,
#          expression-indexed refresh.
#   A "gain" is therefore a row that is `unknown` under BASE and decided under
#   ARM.  A "loss" is the reverse.
#
# ONE BINARY, TWO ENVIRONMENT VALUES.  Both paths are compiled in, so this is
# not a build comparison.  Same file, same pinned core, arms back to back, and
# the ORDER ALTERNATES with the row's ordinal so a warm-cache advantage cannot
# accumulate on one arm.
#
# Emits, per arm:  file, arm, verdict, exit status, wall ms, peak RSS KB.
set -u
IFS=$'\t' read -r core file budget ordinal <<< "$1"
CORPUS="${LI_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${LI_AB_AX:-/data0/axeyum/lemma-input-target-ab/release/examples/smtcomp_cli}"

run_arm() {
  local arm="$1" out rss t0 t1 status verdict
  out=$(mktemp -t "li-ab-XXXXXX")
  t0=$(date +%s%N)
  if [ "$arm" = arm ]; then
    AXEYUM_LIA_INITIAL_BOUND_INDEX=1 /usr/bin/time -f '%M' -o "$out.rss" \
      taskset -c "$core" timeout $((budget + 120)) \
      "$AX" "$CORPUS/$file" --timeout-ms $((budget * 1000)) > "$out" 2>/dev/null
  else
    env -u AXEYUM_LIA_INITIAL_BOUND_INDEX /usr/bin/time -f '%M' -o "$out.rss" \
      taskset -c "$core" timeout $((budget + 120)) \
      "$AX" "$CORPUS/$file" --timeout-ms $((budget * 1000)) > "$out" 2>/dev/null
  fi
  status=$?
  t1=$(date +%s%N)
  verdict=$(grep -m1 -E '^(sat|unsat|unknown)$' "$out" || true)
  [ -n "$verdict" ] || verdict=NOVERDICT
  rss=$(tail -1 "$out.rss" 2>/dev/null || echo NA)
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$file" "$arm" "$verdict" "$status" "$(((t1 - t0) / 1000000))" "$rss"
  rm -f "$out" "$out.rss"
}

if [ $((ordinal % 2)) -eq 0 ]; then
  run_arm base
  run_arm arm
else
  run_arm arm
  run_arm base
fi
