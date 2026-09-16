#!/usr/bin/env bash
# QUANT-GROUND-INCREMENTAL (ADR-2124) -- run one shard of the 53 UFLIA cores
# under `AXEYUM_QTRACE=1` so every interleaved ground check prints its OWN wall
# clock, and capture the route trail beside it.
#
#   cores-run.sh <list> <outdir> <pin> <bin> <arm> <shard> <nshards> [budget_s]
#
# `<arm>` is "off" (the lever unset -- the shipped configuration) or "on"
# (AXEYUM_QINST_GROUND_SESSION=1).  BOTH ARMS GET THE SAME INSTRUMENTATION:
# tracing costs time, and an arm traced while the other is not is an arm given a
# different budget.
#
# WHY QTRACE AND NOT FLOODPROBE.  `qinst_egraph.rs` prints the interleaved check
# two ways.  `FLOODPROBE qf-check` (gated on AXEYUM_QINST_FLOODPROBE) prints the
# check's own ms but only from `quantifier_qf_refutation_check`'s wrapper, and it
# also prints a second line per cap-hit.  `[qtrace] egraph-seg +<s> qf-check
# round=N ground=M` is emitted at the loop's own call site and is the line the
# round cadence actually produces, one per interleaved check.  The summarizer
# reads THAT and nothing else.
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; ARM="$5"; SHARD="$6"; NSHARDS="$7"; BUDGET="${8:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
mkdir -p "$OUT/raw"

i=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  if [ $((i % NSHARDS)) -ne "$SHARD" ]; then i=$((i + 1)); continue; fi
  i=$((i + 1))
  base="$OUT/raw/$(basename "$f").$ARM"
  if [ "$ARM" = "off" ]; then
    env -u AXEYUM_QINST_GROUND_SESSION \
      AXEYUM_QTRACE=1 \
      timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
      "$AX" "$f" > "$base.out" 2> "$base.err"
  else
    AXEYUM_QINST_GROUND_SESSION=1 \
      AXEYUM_QTRACE=1 \
      timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
      "$AX" "$f" > "$base.out" 2> "$base.err"
  fi
  echo "$(basename "$f") $ARM rc=$?" >> "$OUT/shard$SHARD.$ARM.progress"
done < "$LIST"
echo "SHARD-DONE $SHARD $ARM" >> "$OUT/shard$SHARD.$ARM.progress"
