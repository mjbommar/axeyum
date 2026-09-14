#!/usr/bin/env bash
# SKELETON-REACH -- full output of ONE file in ONE arm of the 2x2.
#
#   trace-arm.sh <A|B|C|D> <relative-file> [budget_s] [core]
#
# Polarity, restated at the point of use (the two levers invert relative to
# each other and a reader who gets this backwards measures the shipped arm in
# both halves):
#   AXEYUM_DISTINCT_LINEAR    ships Off -- `on` ARMS it
#   AXEYUM_ZERO_INST_SKELETON ships On  -- `0`  KILLS it
set -u
ARM="$1"
F="$2"
B="${3:-24}"
PIN="${4:-9}"
CORPUS="${SKEL_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${SKEL_AX:-/nas3/data/axeyum/harness/skeleton-reach/bin/smtcomp_cli-base}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
case "$ARM" in
  A|C) exec env -u AXEYUM_DISTINCT_LINEAR -u AXEYUM_ZERO_INST_SKELETON AXEYUM_TRACE=1 \
         timeout $((B + 40)) taskset -c "$PIN" "$AX" "$CORPUS/$F" --timeout-ms $((B * 1000)) ;;
  B)   exec env AXEYUM_DISTINCT_LINEAR=on AXEYUM_ZERO_INST_SKELETON=0 AXEYUM_TRACE=1 \
         timeout $((B + 40)) taskset -c "$PIN" "$AX" "$CORPUS/$F" --timeout-ms $((B * 1000)) ;;
  D)   exec env -u AXEYUM_ZERO_INST_SKELETON AXEYUM_DISTINCT_LINEAR=on AXEYUM_TRACE=1 \
         timeout $((B + 40)) taskset -c "$PIN" "$AX" "$CORPUS/$F" --timeout-ms $((B * 1000)) ;;
  *)   echo "ABORT: arm must be A, B, C or D"; exit 2 ;;
esac
