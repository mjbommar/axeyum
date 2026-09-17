#!/usr/bin/env bash
# One shard = ONE pinned core pair running ITS list, which interleaves all 16
# divisions (file i of every division in turn), so a partial read of the shard
# is a sample of the board and not a prefix of one division.
# Writes <out>/shard<idx>.DONE when finished; nothing else notifies the
# coordinator.
#
# Usage: board-ab-driver.sh <harness-root> <shard-idx> <cores> <binA> <binB>
set -u
H="$1"; IDX="$2"; PIN="$3"; A="$4"; B="$5"
LOG="$H/out/shard$IDX.log"
{
  echo "host=$(hostname) idx=$IDX pin=$PIN start=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "load=$(cut -d' ' -f1-3 /proc/loadavg) smtcomp_before=$(pgrep -c smtcomp)"
  # Clock self-check: a 200 ms sleep must read 150-400 ms in $EPOCHREALTIME.
  t0=$EPOCHREALTIME; sleep 0.2; t1=$EPOCHREALTIME
  d=$(( (${t1%.*} * 1000 + 10#${t1#*.} / 1000) - (${t0%.*} * 1000 + 10#${t0#*.} / 1000) ))
  echo "clock_selfcheck_200ms_read=${d}ms"
  if [ "$d" -lt 150 ] || [ "$d" -gt 400 ]; then echo "CLOCK_SELFCHECK_FAILED"; exit 3; fi
  echo "binA=$(sha256sum "$A" | cut -d' ' -f1)"
  echo "binB=$(sha256sum "$B" | cut -d' ' -f1)"
  bash "$H/scripts/ab-two-bins.sh" "shard$IDX" "$H/lists/shard$IDX.txt" "$H/out/shard$IDX.tsv" "$PIN" "$A" "$B" 24
  echo "end=$(date -u +%Y-%m-%dT%H:%M:%SZ) load=$(cut -d' ' -f1-3 /proc/loadavg)"
  echo "BOARD_AB_DRIVER_FINISHED idx=$IDX"
} >> "$LOG" 2>&1
touch "$H/out/shard$IDX.DONE"
