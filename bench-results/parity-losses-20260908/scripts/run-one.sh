#!/usr/bin/env bash
# One division on one pinned core pair, into this set's `sweep/` (pass 1) or
# `confirm/` (pass 2). Same runner as `run-all.sh` uses; separate entry point so
# a division can be added or re-run without re-running the whole population.
#
# Usage: run-one.sh <cores> <list-file> <division> [subdir]
set -uo pipefail
cores="$1"; list="$2"; division="$3"; sub="${4:-sweep}"
here="$(cd "$(dirname "$0")" && pwd)"
outdir="$here/.."
mkdir -p "$outdir/$sub" "$outdir/frames"
echo "$division ($sub) start $(date -Is) cores=$cores load=$(cut -d' ' -f1-3 /proc/loadavg)" \
  >> "$outdir/frames/$division.$sub.frame"
taskset -c "$cores" bash "$here/sweep.sh" "$list" "$division" "$outdir/$sub/$division.tsv"
echo "$division ($sub) end   $(date -Is) load=$(cut -d' ' -f1-3 /proc/loadavg)" \
  >> "$outdir/frames/$division.$sub.frame"
