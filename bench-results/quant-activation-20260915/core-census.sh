#!/usr/bin/env bash
# QUANT-ACTIVATION -- ADR-2113's 53 reference-minimal UFLIA cores, LEVER OFF and
# ON, fully traced (ADR-2120 §7).
#
#   core-census.sh <list> <outdir> <pin> <bin> [budget_s]
#
# WHY THESE 53 AND NOT THE DIVISION. ADR-2113 measured that z3 refutes every one
# of them E-MATCHING-ONLY (`smt.mbqi=false`, 53 of 53, median 108 ms) and that
# its proofs use a MEDIAN OF 6 instantiations. So they are the population where
# "the instances are findable and sufficient" is already established by an
# independent solver, and anything we still fail on is OUR engine rather than
# the problem. A `+0` on the whole division cannot say that; 53 cores with a
# reference verdict can.
#
# WHAT IS CAPTURED, per core per arm, and why each channel is separate:
#
#   stdout -> <core>.<arm>.out    the `; route-trail` JSON. Read by
#                                 `scripts/route_trace_reader.py` and NEVER by a
#                                 grep over the prose -- three ADRs record a
#                                 census that got a bucket wrong by parsing the
#                                 rendering instead of the artifact.
#   stderr -> <core>.<arm>.err    `[qtrace]` stage lines and `QPROBE` per-
#                                 universal lines. These are the only channel
#                                 that carries instance counts, handoffs and
#                                 whether the interleaved ground check ran.
#   ground dump                   `AXEYUM_QGROUNDDUMP`, the accumulated ground
#                                 set at loop exit, so the ON arm's set can be
#                                 asked whether it holds the terms z3's own
#                                 proof substitutes.
#
# BOTH ARMS GET THE SAME INSTRUMENTATION. Tracing costs time, and an arm traced
# while the other is not would be an arm given a different budget.
#
# `AXEYUM_QPROBE_CENSUS=1` is required ON TOP of `AXEYUM_QPROBE=1`: without it
# every `rej_*` field prints 0, and reading those zeros as "nothing was
# rejected" attributes a cause to a measurement nobody took (ADR-2113 §6).
set -u
LIST="$1"; OUT="$2"; PIN="$3"; AX="$4"; BUDGET="${5:-24}"
HEADROOM=16
VLIM=$((8 * 1024 * 1024))

[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
mkdir -p "$OUT/raw" "$OUT/dump"

run_arm() {  # $1 = "" for OFF (unset), else the level; $2 = arm tag
  local base dump
  base="$OUT/raw/$(basename "$f").$2"
  dump="$OUT/dump/$(basename "$f").$2.ground"
  if [ -z "$1" ]; then
    env -u AXEYUM_QINST_POSITIVE_PATH \
      AXEYUM_QTRACE=1 AXEYUM_QPROBE=1 AXEYUM_QPROBE_CENSUS=1 \
      AXEYUM_QGROUNDDUMP="$dump" \
      timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
      "$AX" "$f" > "$base.out" 2> "$base.err"
  else
    AXEYUM_QINST_POSITIVE_PATH="$1" \
      AXEYUM_QTRACE=1 AXEYUM_QPROBE=1 AXEYUM_QPROBE_CENSUS=1 \
      AXEYUM_QGROUNDDUMP="$dump" \
      timeout $((BUDGET + HEADROOM)) taskset -c "$PIN" \
      bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
      "$AX" "$f" > "$base.out" 2> "$base.err"
  fi
  # The exit status is recorded beside the verdict, never folded into it.
  printf '%s' "$?" > "$base.rc"
}

n=0
while read -r f; do
  [ -z "$f" ] && continue
  # Arm order alternates per core, so a systematic advantage to running second
  # cannot accrue to one arm.
  if [ $((n % 2)) -eq 0 ]; then
    run_arm "" off; run_arm 1 on
  else
    run_arm 1 on; run_arm "" off
  fi
  n=$((n + 1))
  printf 'CORE %3d %s\n' "$n" "$(basename "$f")"
done < "$LIST"
echo "CORE-CENSUS-DONE $n cores -> $OUT"
