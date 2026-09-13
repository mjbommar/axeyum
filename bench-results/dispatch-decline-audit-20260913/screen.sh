#!/usr/bin/env bash
# Screening pass: where does the ADR-1966 defect actually FIRE?
#
# A rung that refuses and propagates does so in milliseconds (ADR-1927 measured
# `attempts=2` after 1 ms), so a 2 s budget is enough to enumerate every
# `give-up kind=Error` row in a division. It is NOT enough to measure verdicts,
# and this script does not claim to -- it exists only to say which divisions
# are worth the 24 s A/B, so that the expensive run is aimed rather than
# sprayed.
#
# Usage: screen.sh <binary> <outdir> <core-start> <division>...
set -u
AX="$1"; OUTDIR="$2"; CORE0="$3"; shift 3
HERE="$(cd "$(dirname "$0")" && pwd)"
LISTS="$HERE/../parity-lists"
mkdir -p "$OUTDIR"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

i=0
for d in "$@"; do
  core=$((CORE0 + i))
  BUDGET=2 "$HERE/census-run.sh" "$AX" "$d" "$LISTS/$d.txt" "$OUTDIR/$d.tsv" "$core" \
    > "$OUTDIR/$d.log" 2>&1 &
  i=$((i + 1))
done
wait
echo "SCREEN-DONE $*"
