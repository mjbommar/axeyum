#!/usr/bin/env bash
# Second pass over the COMPLEMENT's unsolved files, for the divisions where
# `reconcile.py` reports a POSITIVE residual (we decide fewer files than the
# ledger entry implies).
#
# A positive residual is either a regression or contention, and those are not
# distinguishable from one sweep: the ledger entries were measured at load 1-3
# (their own `load average` row says so) and this sweep ran at 11-27. Re-running
# only the complement's unsolved files is the same one-sided trick the confirm
# pass uses -- it can only move the residual DOWN toward the ledger, so a
# residual that survives it is not explained by this sweep's contention.
#
# Usage: comp-confirm.sh <cores> <DIV>
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="$here/../comp-pending"
mkdir -p "$out" "$here/../comp2"
cores="$1"; div="$2"
awk -F'\t' 'NR > 1 && $3 == "unsolved" { print $1 }' "$here/../comp/$div.tsv" > "$out/$div.txt"
echo "$div $(wc -l < "$out/$div.txt") complement files to re-run"
taskset -c "$cores" bash "$here/sweep.sh" "$out/$div.txt" "$div" "$here/../comp2/$div.tsv"
awk -F'\t' 'NR > 1 { n++; if ($3 != "unsolved") w++ } END { printf "%s comp-confirm rerun=%d recovered=%d\n", "'"$div"'", n, w+0 }' "$here/../comp2/$div.tsv"
