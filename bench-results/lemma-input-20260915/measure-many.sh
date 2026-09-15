#!/usr/bin/env bash
# LEMMA-INPUT -- run a LIST of rows under the attribution binary on 8 pinned
# cores (0-7, the P-core class on this box), one row per core at a time.
#
# R2: attribution only.  No verdict, wall time or decision in this lane comes
# from this binary -- it carries an instrument that costs an atomic per pair
# iteration and would poison any timing read.
set -u
LIST="$1"; BUDGET="${2:-24}"; OUT="$3"
HERE="$(cd "$(dirname "$0")" && pwd)"
: > "$OUT"
awk -v b="$BUDGET" 'NF{printf "%d\t%s\t%s\n", (NR-1)%8, $0, b}' "$LIST" \
  | xargs -P 8 -d '\n' -I{} bash "$HERE/measure-row.sh" "{}" >> "$OUT"
echo "rows in list: $(grep -c . "$LIST")   rows written: $(grep -c . "$OUT")"
