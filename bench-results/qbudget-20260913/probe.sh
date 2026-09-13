#!/usr/bin/env bash
# Decide ONE file at the board envelope and print the raw tail, so a missing
# binary, a missing corpus and a hard division are distinguishable before any
# sweep is launched -- each of them otherwise produces the same empty TSV.
#
# Usage: probe.sh <bin> <file> [core-pair] [budget_s]
set -u
AX="$1"; F="$2"; PIN="${3:-2,10}"; BUDGET="${4:-24}"
VLIM=$((8 * 1024 * 1024))
[ -x "$AX" ] || { echo "ABORT: $AX missing or not executable"; exit 2; }
[ -r "$F" ]  || { echo "ABORT: $F missing or unreadable"; exit 2; }
t0=$(date +%s%N)
raw=$(timeout $((BUDGET + 16)) taskset -c "$PIN" \
        bash -c "ulimit -v $VLIM; exec \"\$0\" \"\$1\" --trace --timeout-ms $((BUDGET * 1000))" \
        "$AX" "$F" 2>&1)
rc=$?
t1=$(date +%s%N)
echo "rc=$rc wall_ms=$(( (t1 - t0) / 1000000 ))"
printf '%s\n' "$raw" | tail -12
