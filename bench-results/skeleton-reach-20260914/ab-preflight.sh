#!/usr/bin/env bash
# SKELETON-REACH -- assert, BEFORE any measuring, that the two arms differ.
#
#   ab-preflight.sh <bin> <file> [core]
#
# A lever that is silently ignored produces two identical arms and an A/B that
# reports a confident zero. The check is on the MECHANISM, not on the verdict:
# the base arm must die at ingest with a give-up, and the arm must not. Exit
# status depends on the finding.
set -u
AX="$1"
F="$2"
PIN="${3:-9}"
CORPUS="${SKEL_CORPUS:-/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }

B=$(env -u AXEYUM_DECLARED_NAME_WINS -u AXEYUM_DISTINCT_LINEAR AXEYUM_TRACE=1 \
     timeout 90 taskset -c "$PIN" "$AX" "$CORPUS/$F" --timeout-ms 24000 2>&1)
A=$(env AXEYUM_DECLARED_NAME_WINS=on AXEYUM_DISTINCT_LINEAR=on AXEYUM_TRACE=1 \
     timeout 90 taskset -c "$PIN" "$AX" "$CORPUS/$F" --timeout-ms 24000 2>&1)

bb=$(printf '%s\n' "$B" | grep -m1 '^; route ' | grep -oE 'bound_by=[^ ]+' | cut -d= -f2)
ab=$(printf '%s\n' "$A" | grep -m1 '^; \(partial \)\?route ' | grep -oE 'bound_by=[^ ]+' | cut -d= -f2)
bv=$(printf '%s\n' "$B" | grep -m1 -oE '^(sat|unsat|unknown)$')
av=$(printf '%s\n' "$A" | grep -m1 -oE '^(sat|unsat|unknown)$')
bg=$(printf '%s\n' "$B" | grep -m1 '^; give-up ' | sed -n 's/.*detail=//p' | cut -c1-70)
ag=$(printf '%s\n' "$A" | grep -m1 '^; give-up ' | sed -n 's/.*detail=//p' | cut -c1-70)

echo "file      $F"
echo "arm base  bound_by=${bb:-NONE} verdict=${bv:-NONE} giveup=${bg:-none}"
echo "arm arm   bound_by=${ab:-NONE} verdict=${av:-NONE} giveup=${ag:-none}"

if [ "$bb" != "fd:parse" ]; then
  echo "FAIL: the BASE arm does not stop at fd:parse on this file -- wrong fixture"
  exit 3
fi
if [ "$ab" = "fd:parse" ]; then
  echo "FAIL: the ARM also stops at fd:parse -- the lever is not live in this binary"
  exit 3
fi
echo "PREFLIGHT-OK: the arms differ by MECHANISM (base refused at ingest, arm was not)"
