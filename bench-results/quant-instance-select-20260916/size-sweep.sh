#!/usr/bin/env bash
# Sizing sweep for lane QUANT-INSTANCE-SELECT: per-core admitted-instance count,
# generation histogram, and whether the flood throttle engages at all.
# Reads a core path on stdin per line; writes per-core capture files.
set -u
BIN=/nas3/data/axeyum/lanes/quant-instance-select/smtcomp_cli
OUT="$1"; PIN="$2"
mkdir -p "$OUT/dump" "$OUT/cap"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  b=$(basename "$f")
  D="$OUT/dump/$b.dump"; C="$OUT/cap/$b.txt"
  rm -f "$D"
  ( ulimit -v 8388608
    AXEYUM_QGROUNDDUMP="$D" AXEYUM_QPROBE=1 \
    timeout -k 5 40 taskset -c "$PIN" "$BIN" "$f" --timeout-ms 24000 --trace
    echo "EXIT=$?" ) > "$C" 2>&1
done
