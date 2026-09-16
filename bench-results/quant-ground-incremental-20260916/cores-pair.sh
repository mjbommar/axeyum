#!/usr/bin/env bash
# QUANT-GROUND-INCREMENTAL (ADR-2124) -- one shard: both arms of each file, back
# to back, on one pinned physical core.
#
#   cores-pair.sh <list> <outdir> <pin> <bin> <shard> <nshards> [budget_s]
#
# See `cores-launch.sh` for why the arms are interleaved per file rather than
# run one after the other.
#
# BOTH ARMS GET THE SAME INSTRUMENTATION.  `AXEYUM_QTRACE=1` costs time, and an
# arm traced while the other is not is an arm given a different budget.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; SHARD="$5"; NSHARDS="$6"; BUDGET="${7:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
mkdir -p "$OUT/raw"

run_one() {  # $1 = arm, $2 = file
  local base rc
  base="$OUT/raw/$(basename "$2").$1"
  if [ "$1" = "off" ]; then
    env -u AXEYUM_QINST_GROUND_SESSION AXEYUM_QTRACE=1 \
      timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
      "$AX" "$2" > "$base.out" 2> "$base.err"
  else
    AXEYUM_QINST_GROUND_SESSION=1 AXEYUM_QTRACE=1 \
      timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
      "$AX" "$2" > "$base.out" 2> "$base.err"
  fi
  rc=$?
  echo "$(basename "$2") $1 rc=$rc" >> "$OUT/shard$SHARD.$1.progress"
}

i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  if [ $((i % NSHARDS)) -ne "$SHARD" ]; then i=$((i + 1)); continue; fi
  i=$((i + 1))
  run_one off "$f"
  run_one on "$f"
done < "$LIST"
echo "SHARD-DONE $SHARD" >> "$OUT/shard$SHARD.off.progress"
echo "SHARD-DONE $SHARD" >> "$OUT/shard$SHARD.on.progress"
