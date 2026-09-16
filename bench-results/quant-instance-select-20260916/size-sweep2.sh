#!/usr/bin/env bash
# Same sizing sweep with the per-universal admission census ON
# (AXEYUM_QPROBE_CENSUS). Without it `flood_slices`, `flood_eager_kept` and
# every `rej_*` counter are hard-zero regardless of what the loop did --
# `census.flood_slices += usize::from(census.enabled)` -- so the first arm
# could only report their ABSENCE, never their value.
set -u
BIN=/nas3/data/axeyum/lanes/quant-instance-select/smtcomp_cli
OUT="$1"; PIN="$2"
mkdir -p "$OUT/cap"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  b=$(basename "$f")
  ( ulimit -v 8388608
    AXEYUM_QPROBE=1 AXEYUM_QPROBE_CENSUS=1 \
    timeout -k 5 40 taskset -c "$PIN" "$BIN" "$f" --timeout-ms 24000 --trace
    echo "EXIT=$?" ) > "$OUT/cap/$b.txt" 2>&1
done
