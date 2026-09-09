#!/usr/bin/env bash
# Wait for a complement run to reach its expected line count, then start the
# next one on the same cores. Watches the OUTPUT, never `pgrep -f` -- a pgrep
# pattern that appears in the waiting script's own command line never exits.
#
# Usage: queue-comp.sh <wait-tsv> <wait-lines> <cores> <next-division>
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
tsv="$1"; want="$2"; cores="$3"; div="$4"
while :; do
  have=$(wc -l < "$tsv" 2>/dev/null || echo 0)
  if [ "${have:-0}" -ge "$want" ]; then break; fi
  sleep 15
done
exec bash "$here/run-one.sh" "$cores" "$here/../complement/$div.txt" "$div" comp
