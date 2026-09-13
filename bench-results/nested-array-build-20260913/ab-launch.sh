#!/usr/bin/env bash
# The A/B over the four nested-array divisions plus two controls we already do
# well (QF_ABV 93.5%, QF_BV 93%), one division at a time, pinned.
#
# The controls are not decoration: ADR-1965 touches `ArraySortKey::to_sort`,
# `Sort::array_sorts` and `Features::note_sort`, all of which every flat array
# query goes through. A regression there would be invisible in the four
# divisions this lane is aimed at, because they decide almost nothing today.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
LISTS="$HERE/../parity-lists"
OUT="${1:?output dir}"
BASE="${2:?baseline binary}"
LANE="${3:?lane binary}"
BUDGET="${4:-24}"
CORES="${5:-8,9}"

mkdir -p "$OUT"
for div in AUFLIRA AUFNIRA ALIA ABV QF_ABV QF_BV; do
  echo "=== $div $(date -Is) ==="
  taskset -c "$CORES" "$HERE/ab-run.sh" \
    "$div" "$LISTS/$div.txt" "$OUT/$div.tsv" "$BASE" "$LANE" "$BUDGET"
done
echo "AB-DONE $(date -Is)"
