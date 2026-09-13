#!/usr/bin/env bash
# Second A/B batch, aimed by the guard-firing measurement rather than by the
# text hit rate.
#
# `guard-firing.sh` over 1,521 corpus files found the ONLY route whose refusal
# actually reaches a guard on real files: `abv-online-cdclt`, 6 of 200 QF_ABV
# files, refusing with "online AUFBV lazy-ROW abstraction does not admit this
# array shape" -- while `dispatch_array_fast_paths`, the rung IMMEDIATELY
# below it, is the route that owns array shapes.
#
# The first batch was aimed by `hit-rate.py`, which reads declarations out of
# the file text. That was wrong about AUFLIRA: 184 of its 200 files declare an
# array-valued UF, and 186 of 200 never get past the PARSER (nested array
# element sort), so the division cannot exercise the change at all. A
# structural hit rate is an upper bound on reachability, not a measure of it.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
BIN=/data0/axeyum/dispatch-decline-audit-bin
OUT="${1:-/data0/axeyum/dispatch-decline-audit-ab}"
mkdir -p "$OUT"

i=5
for d in QF_ABV ABV QF_AUFLIA; do
  BUDGET="${BUDGET:-10}" "$HERE/ab-run.sh" "$BIN/base" "$BIN/fix" "$d" \
    "$HERE/../parity-lists/$d.txt" "$OUT/$d.tsv" "$i" > "$OUT/$d.log" 2>&1 &
  i=$((i + 1))
done
wait
echo "AB2-DONE"
