#!/usr/bin/env bash
# SKELETON-REACH -- dump the full stdout+stderr of one file at a given budget,
# with the route trail on. Used to READ what a bucket's rows actually print
# before any label is believed (pre-registration R3).
#
#   trace-one.sh <relative-file> [budget_ms] [core]
set -u
F="$1"
MS="${2:-24000}"
PIN="${3:-9}"
CORPUS="${SKEL_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${SKEL_AX:-/nas3/data/axeyum/harness/skeleton-reach/bin/smtcomp_cli-base}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
AXEYUM_TRACE=1 timeout $(((MS / 1000) + 40)) taskset -c "$PIN" \
  "$AX" "$CORPUS/$F" --timeout-ms "$MS" 2>&1
echo "EXIT=$?"
