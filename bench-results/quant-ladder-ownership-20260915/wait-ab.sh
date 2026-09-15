#!/usr/bin/env bash
# Wait for the ADR-2103 A/B by counting ROWS IN THE SHARD TSVs, not processes.
#
# Watch the artifact, not the process. A `pgrep` loop whose own command line
# contains the pattern it greps for never exits, and "the runner is gone" and
# "the runner finished" are different findings that a process check cannot tell
# apart -- a shard killed by the box is silent in exactly the same way a shard
# that completed is.
#
# Prints a line only when the count MOVES, so the event stream is progress
# rather than a heartbeat, and exits when the expected row total is in.
#
# Usage: wait-ab.sh <outdir> [expected_rows]
set -u
OUT="${1:-/nas3/data/axeyum/harness/quant-ladder-ownership/out}"
WANT="${2:-1800}"
prev=-1
stalled=0
while :; do
  rows=$(cat "$OUT"/*.shard*.tsv 2>/dev/null | grep -vc '^file')
  divs=$(ls "$OUT"/*.shard*.tsv 2>/dev/null | sed 's#.*/##; s/\.shard.*//' | sort -u | wc -l)
  if [ "$rows" != "$prev" ]; then
    echo "AB rows=$rows/$WANT divisions=$divs/9"
    prev="$rows"
    stalled=0
  else
    stalled=$((stalled + 1))
  fi
  if [ "$rows" -ge "$WANT" ]; then
    echo "AB-ALL-ROWS-IN rows=$rows divisions=$divs"
    exit 0
  fi
  # A stall is reported, never waited out silently: thirty minutes without a
  # single new row means the run is stuck, and saying nothing looks identical to
  # saying "still going".
  if [ "$stalled" -ge 15 ]; then
    echo "AB-STALLED rows=$rows divisions=$divs -- no new row in ~30 min"
    stalled=0
  fi
  sleep 120
done
