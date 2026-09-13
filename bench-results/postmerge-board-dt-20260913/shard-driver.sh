#!/usr/bin/env bash
# One shard = ONE pinned core pair running its slice of EVERY division, one
# division after another. The divisions must be serial: launching them
# concurrently on the same pinned core oversubscribes it and biases the board
# DOWN, which is exactly the caveat the 2026-09-13 board carried.
set -u
H=/nas3/data/axeyum/harness/postmerge-board-dt
IDX="$1"; PIN="$2"; BIN="$3"; shift 3
for d in "$@"; do
  sl=$(printf '%s/lists/%s.%02d.txt' "$H" "$d" "$IDX")
  so=$(printf '%s/out/%s.shard%02d.tsv' "$H" "$d" "$IDX")
  [ -f "$sl" ] || continue
  bash "$H/scripts/board-run.sh" "$d-$IDX" "$sl" "$so" "$PIN" "$BIN" 24
done
echo "SHARD_DRIVER_FINISHED idx=$IDX"
