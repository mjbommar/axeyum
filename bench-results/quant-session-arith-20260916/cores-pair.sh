#!/usr/bin/env bash
# QUANT-SESSION-ARITH (ADR-2130) -- one shard: both arms of each file, back to
# back, on one pinned physical core.
#
#   cores-pair.sh <list> <outdir> <pin> <bin> <shard> <nshards> <on_level> [budget_s]
#
# INTERLEAVED PER FILE, not arm-after-arm.  The two arms of one file run back to
# back on the SAME core, so whatever load the box carries during that pair
# cancels in the difference.  Running all of OFF and then all of ON puts the two
# arms in different load regimes and has moved 23 verdicts on a fixed binary.
#
# ONE BINARY, TWO ENV VALUES.  The lever ships at 0, so the OFF arm is the
# shipped configuration of the very binary under test and the comparison has no
# second build in it.  The OFF arm UNSETS the variable rather than setting it to
# `0`: an explicit `0` is not the same path through `cap_lever!`.
#
# BOTH ARMS GET THE SAME INSTRUMENTATION.  `AXEYUM_QTRACE=1` costs time, and an
# arm traced while the other is not is an arm given a different budget.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; SHARD="$5"; NSHARDS="$6"; ON_LEVEL="$7"
BUDGET="${8:-24}"
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
    AXEYUM_QINST_GROUND_SESSION="$ON_LEVEL" AXEYUM_QTRACE=1 \
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
