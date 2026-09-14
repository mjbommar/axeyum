#!/usr/bin/env bash
# One shard = ONE pinned core pair running its slice of EVERY division, SERIALLY.
# Divisions must not run concurrently on the same core: that oversubscribes it
# and depresses both arms. (The interleaved DIFFERENCE survives it; the level
# does not, and files near the budget get pushed over.)
set -u
H=/nas3/data/axeyum/harness/postmerge-board-dt
IDX="$1"; PIN="$2"; A="$3"; B="$4"; shift 4
for d in "$@"; do
  sl=$(printf '%s/lists/BOARD_%s.%02d.txt' "$H" "$d" "$IDX")
  so=$(printf '%s/out/BOARD_%s.shard%02d.tsv' "$H" "$d" "$IDX")
  [ -f "$sl" ] || continue
  [ -s "$so" ] && continue
  bash "$H/scripts/ab-two-bins.sh" "$d-$IDX" "$sl" "$so" "$PIN" "$A" "$B" 24
done
echo "BOARD_AB_DRIVER_FINISHED idx=$IDX"
