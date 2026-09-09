#!/usr/bin/env bash
# One measurement slot of the portfolio oracle sweep: a pinned core set running
# a list of divisions one after another, so no two divisions inside a slot ever
# contend with each other.
#
# Usage:  portfolio-oracle-slot.sh <cores> <div> [<div>...]
#
# Run from the staging directory that holds `smtcomp_cli`, `portfolio-oracle.py`
# and `lists/<DIV>.txt`; results land in `out/<DIV>.tsv` and `out/<DIV>.err`.
#
# Slots are pinned with `taskset` because these hosts share the box with other
# lanes' sweeps and an unpinned run measures the queue rather than the solver
# (docs/research/08-planning/frontier-ratchet-reference-frame.md).  The reference
# frame is recorded per division in `out/<DIV>.frame` -- load average before and
# after -- so a reader can tell a comparable run from an advisory one instead of
# guessing.
set -euo pipefail

cores="$1"
shift

for div in "$@"; do
  {
    echo "cores=${cores}"
    echo "host=$(hostname)"
    echo "before=$(cut -d' ' -f1-3 /proc/loadavg)"
    echo "start=$(date -Is)"
  } > "out/${div}.frame"

  python3 portfolio-oracle.py \
    --binary ./smtcomp_cli \
    --files "lists/${div}.txt" \
    --out "out/${div}.tsv" \
    --division "${div}" \
    --budget-ms 24000 \
    --probe-ms 120000 \
    --memory-limit-mb 8192 \
    --cores "${cores}" \
    --confirm \
    2> "out/${div}.err"

  {
    echo "after=$(cut -d' ' -f1-3 /proc/loadavg)"
    echo "end=$(date -Is)"
  } >> "out/${div}.frame"

  echo "SLOT ${cores} DONE ${div}"
done
