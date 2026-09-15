#!/usr/bin/env bash
# SILENT-HANG -- one row's WHOLE traced stdout, verbatim, so the claim about
# which lines exist can be checked against the bytes rather than a grep.
set -u
F="$1"; BUDGET="${2:-24}"; PIN="${3:-6}"
CORPUS="${SH_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
AX="${SH_AX:-/nas3/data/axeyum/harness/silent-hang/bin/smtcomp_cli-sh}"
AXEYUM_TRACE=1 timeout $((BUDGET + 120)) taskset -c "$PIN" "$AX" "$CORPUS/$F" \
  --timeout-ms $((BUDGET * 1000)) 2>&1
