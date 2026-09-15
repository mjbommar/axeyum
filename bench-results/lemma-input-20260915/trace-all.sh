#!/usr/bin/env bash
# LEMMA-INPUT -- `trace-arms.sh` over a list, one row at a time, on the cores
# the A/B is NOT pinned to (12-15), so a traced run never shares a core with a
# timed one.
set -u
LIST="$1"; BUDGET="${2:-24}"; OUT="$3"
HERE="$(cd "$(dirname "$0")" && pwd)"
i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  echo "===== $f"
  bash "$HERE/trace-arms.sh" "$f" "$BUDGET" $((12 + i % 4)) "$OUT"
  i=$((i + 1))
done < "$LIST"
