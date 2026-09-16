#!/usr/bin/env bash
# ADR-2133 A/B on the 53 UFLIA cores: ladder OFF vs ON, INTERLEAVED per file --
# same file, same pinned core, back to back -- so ambient load cancels in the
# difference rather than being attributed to one arm.
set -u
BIN=/nas3/data/axeyum/lanes/quant-instance-select/smtcomp_cli_ladder
OUT="$1"; PIN="$2"
mkdir -p "$OUT/off" "$OUT/on"
while IFS= read -r f; do
  [ -n "$f" ] || continue
  b=$(basename "$f")
  for arm in off on; do
    if [ "$arm" = off ]; then L=0; else L=1; fi
    ( ulimit -v 8388608
      AXEYUM_QINST_GEN_LADDER=$L \
      timeout -k 5 40 taskset -c "$PIN" "$BIN" "$f" --timeout-ms 24000 --trace
      echo "EXIT=$?" ) > "$OUT/$arm/$b.txt" 2>&1
  done
done
