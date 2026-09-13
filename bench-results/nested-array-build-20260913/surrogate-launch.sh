#!/usr/bin/env bash
# Run the surrogate sweep over all four nested-array divisions' pinned winnable
# lists, one division at a time, pinned to a fixed pair of P-core threads so the
# numbers are comparable to each other.  Board budget: 24 s.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
BOARD="$HERE/../tier1-divisions-headtohead-20260913"
OUT="${1:?output dir}"
BUDGET="${2:-24}"
CORES="${3:-8,9}"

mkdir -p "$OUT"
for div in AUFLIRA AUFNIRA ALIA ABV; do
  echo "=== $div $(date -Is) ==="
  taskset -c "$CORES" "$HERE/surrogate-sweep.sh" \
    "$div" "$BOARD/winnable/$div.txt" "$OUT" "$BUDGET"
done
echo "SWEEP-DONE $(date -Is)"
