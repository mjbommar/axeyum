#!/usr/bin/env bash
# LEMMA-INPUT -- read the traced stdout pairs and report, per row, whether the
# arm moved it OUT of ADR-2075's bucket.
#
# The bucket's definition is three conditions together, so all three are read:
# undecided, `give-up kind=Watchdog`, and NO complete `; route ` line.  A row
# that keeps its verdict but gains a route line and a named give-up kind has
# changed category, and the census that files it can now see why.
#
# Both prefixes are grepped -- `^; route ` AND `^; partial route ` -- because
# grepping only the first is the exact defect ADR-2075 is about.
set -u
OUT="${1:-bench-results/lemma-input-20260915/prof}"
printf 'row\tarm\tverdict\tgive_up_kind\troute_line\tattempts\tbound_by\n'
for base in "$OUT"/*.base.txt; do
  [ -e "$base" ] || continue
  stem="${base%.base.txt}"
  for a in base arm; do
    f="$stem.$a.txt"
    [ -r "$f" ] || continue
    verdict=$(grep -m1 -E '^(sat|unsat|unknown)$' "$f" || echo NOVERDICT)
    kind=$(grep -m1 '^; give-up ' "$f" | sed -E 's/^; give-up kind=([A-Za-z]+).*/\1/' || true)
    [ -n "$kind" ] || kind=NONE
    if grep -q '^; route ' "$f"; then
      rl=COMPLETE
    elif grep -q '^; partial route ' "$f"; then
      rl=PARTIAL
    else
      rl=ABSENT
    fi
    line=$(grep -m1 -E '^; (partial )?route ' "$f" || true)
    attempts=$(printf '%s' "$line" | sed -nE 's/.*attempts=([0-9]+).*/\1/p')
    bound=$(printf '%s' "$line" | sed -nE 's/.*bound_by=([^ ]+).*/\1/p')
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$(basename "$stem")" "$a" "$verdict" "$kind" "$rl" "${attempts:-NA}" "${bound:-NA}"
  done
done
