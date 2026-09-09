#!/usr/bin/env bash
# Wait for the sweep holding <cores> to finish, then run the given pass on it.
#
# The wait watches the OUTPUT (`sweep/<DIV>.tsv` reaching the input's line
# count), not a process name: a `pgrep -f` whose pattern appears in this
# script's own command line never exits, which is a trap this repository has
# already paid for once.
#
# Usage: queue-after.sh <expected-tsv> <expected-lines> <run-confirm-spec>
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
tsv="$1"; want="$2"; spec="$3"
while :; do
  have=$(wc -l < "$tsv" 2>/dev/null || echo 0)
  if [ "${have:-0}" -ge "$want" ]; then break; fi
  sleep 15
done
exec bash "$here/run-confirm.sh" "$spec"
