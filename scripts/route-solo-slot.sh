#!/usr/bin/env bash
# One measurement slot of the solo-route sweep: a pinned core set running a list
# of divisions one after another, so no two divisions inside a slot contend.
#
# Usage:  route-solo-slot.sh <cores> <div> [<div>...]
#
# Run from the staging directory holding `route_solo`, `route-solo-sweep.py` and
# `lists/<DIV>.txt`; results land in `solo/<DIV>.tsv` and `solo/<DIV>.err`.
#
# The sweep script exits 2 on a cross-route verdict disagreement.  That status is
# carried out of the loop deliberately -- a soundness alarm must not be averaged
# into "the slot finished".
set -uo pipefail

cores="$1"
shift
mkdir -p solo
worst=0

for div in "$@"; do
  {
    echo "cores=${cores}"
    echo "host=$(hostname)"
    echo "before=$(cut -d' ' -f1-3 /proc/loadavg)"
    echo "start=$(date -Is)"
  } > "solo/${div}.frame"

  python3 route-solo-sweep.py \
    --binary ./route_solo \
    --files "lists/${div}.txt" \
    --out "solo/${div}.tsv" \
    --division "${div}" \
    --budget-ms 24000 \
    --memory-limit-mb 8192 \
    --cores "${cores}" \
    > "solo/${div}.out" 2> "solo/${div}.err"
  status=$?
  [ "$status" -gt "$worst" ] && worst=$status

  {
    echo "after=$(cut -d' ' -f1-3 /proc/loadavg)"
    echo "end=$(date -Is)"
    echo "exit=${status}"
  } >> "solo/${div}.frame"

  echo "SOLO ${cores} DONE ${div} exit=${status}"
done

exit "$worst"
