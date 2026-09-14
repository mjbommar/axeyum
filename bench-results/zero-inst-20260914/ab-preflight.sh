#!/usr/bin/env bash
# ZERO-INST -- assert, before any measuring, that the two arms are DIFFERENT.
#
#   ab-preflight.sh <bin> <file> [core]
#
# A lever that is silently ignored produces two identical arms and an A/B that
# reports a confident zero. The check is on the MECHANISM, not the verdict: the
# route trail must show `q:bool-skeleton` DECLINED in the off arm and DECIDED in
# the on arm. Exit status depends on the finding.
set -u
AX="$1"
F="$2"
PIN="${3:-3}"
CORPUS=${ZERO_INST_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

rung() {
  local raw="$1"
  if printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton","outcome":"decided"'; then
    echo decided
  elif printf '%s' "$raw" | grep -qF '"route":"q:bool-skeleton"'; then
    echo declined
  else
    echo absent
  fi
}

OFF_RAW=$(env -u AXEYUM_ZERO_INST_SKELETON AXEYUM_TRACE=1 \
  timeout 90 taskset -c "$PIN" "$AX" "$CORPUS/$F" --timeout-ms 24000 2>&1)
ON_RAW=$(AXEYUM_ZERO_INST_SKELETON=1 AXEYUM_TRACE=1 \
  timeout 90 taskset -c "$PIN" "$AX" "$CORPUS/$F" --timeout-ms 24000 2>&1)

OFF_RUNG=$(rung "$OFF_RAW")
ON_RUNG=$(rung "$ON_RAW")
OFF_V=$(printf '%s\n' "$OFF_RAW" | grep -m1 -oE '^(sat|unsat|unknown)$')
ON_V=$(printf '%s\n' "$ON_RAW" | grep -m1 -oE '^(sat|unsat|unknown)$')

echo "file      $F"
echo "arm off   rung=$OFF_RUNG verdict=${OFF_V:-NONE}"
echo "arm on    rung=$ON_RUNG verdict=${ON_V:-NONE}"

if [ "$OFF_RUNG" = absent ]; then
  echo "FAIL: the rung is ABSENT from the trail -- this binary predates it"
  exit 3
fi
if [ "$OFF_RUNG" = "$ON_RUNG" ]; then
  echo "FAIL: both arms report rung=$OFF_RUNG -- the lever is not live"
  exit 3
fi
if [ "$OFF_RUNG" != declined ] || [ "$ON_RUNG" != decided ]; then
  echo "FAIL: expected off=declined on=decided; POLARITY may be inverted"
  exit 3
fi
echo "PREFLIGHT-OK: the arms differ by mechanism, polarity as documented"
