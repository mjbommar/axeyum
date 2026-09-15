#!/usr/bin/env bash
# LEMMA-INPUT -- drive `cap-arm.sh` over a list on 8 pinned cores.
# Usage: cap-run.sh <list> <budget-seconds> <out.tsv> [passes]
set -u
LIST="$1"; BUDGET="${2:-24}"; OUT="$3"; PASSES="${4:-1}"
HERE="$(cd "$(dirname "$0")" && pwd)"
: > "$OUT"
for pass in $(seq 1 "$PASSES"); do
  awk -v b="$BUDGET" -v p="$pass" 'NF{printf "%d\t%s\t%s\t%d\n", (NR-1)%8, $0, b, NR+p}' "$LIST" \
    | xargs -P 8 -d '\n' -I{} bash "$HERE/cap-row.sh" "{}" \
    | sed "s/^/pass$pass\t/" >> "$OUT"
done
echo "rows in list: $(grep -c . "$LIST")   arm-runs written: $(grep -c . "$OUT")"
