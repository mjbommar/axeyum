#!/usr/bin/env bash
# ADR-2133 non-vacuity probe: with the ladder ON, how many of the 53 cores
# actually REACH `generation_ladder_check`, and how many layers does it run?
# Without this, "the ladder changed no verdict" and "the ladder never ran" are
# the same observation.
set -u
BIN=/nas3/data/axeyum/lanes/quant-instance-select/smtcomp_cli_probe
OUT="$1"; PIN="$2"
mkdir -p "$OUT/cap"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  b=$(basename "$f")
  ( ulimit -v 8388608
    AXEYUM_QINST_GEN_LADDER=1 AXEYUM_QPROBE=1 \
    timeout -k 5 40 taskset -c "$PIN" "$BIN" "$f" --timeout-ms 24000
    echo "EXIT=$?" ) > "$OUT/cap/$b.txt" 2>&1
done
