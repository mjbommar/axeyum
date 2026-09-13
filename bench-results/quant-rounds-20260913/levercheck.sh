#!/usr/bin/env bash
# Is the env lever actually READ by the shipped CLI?
#
# The sweep's "every arm agrees" is consistent with BOTH "the lever works and
# the ceiling is not binding" AND "the lever is never read". The mutation
# control proves the LOOP reads the accessor; this proves the ENVIRONMENT
# reaches it through the shipped binary.
#
# Two independent checks:
#   1. `--trace`'s `; config` line names a variable only when it is a registered
#      env_override that is SET, so it is the check for a misspelled NAME.
#   2. A ceiling of 2 must flip some file we decide into `unknown`. If nothing
#      flips, check 1 could still be a registry lookup rather than a read.
set -u
AX=/nas3/data/axeyum/harness/quant-rounds/bin/smtcomp_cli
POP=/nas3/data/axeyum/harness/quant-rounds/pop
BUDGET=20000

echo "=== check 1: does --trace name the variable? ==="
F=$(head -1 "$POP/decided-UFLIA.txt")
echo "shipped:"
timeout 40 env -u AXEYUM_QINST_ROUNDS "$AX" "$F" --trace --timeout-ms $BUDGET 2>&1 \
  | grep -oE '; config .*' | head -1
echo "ceiling 2:"
timeout 40 env AXEYUM_QINST_ROUNDS=2 "$AX" "$F" --trace --timeout-ms $BUDGET 2>&1 \
  | grep -oE '; config .*' | head -1

echo
echo "=== check 2: does a ceiling of 2 flip anything we decide? ==="
flipped=0
n=0
while read -r f; do
  n=$((n + 1))
  [ "$n" -gt 40 ] && break
  a=$(timeout 40 taskset -c 6 env -u AXEYUM_QINST_ROUNDS "$AX" "$f" --timeout-ms $BUDGET 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$')
  b=$(timeout 40 taskset -c 6 env AXEYUM_QINST_ROUNDS=2 "$AX" "$f" --timeout-ms $BUDGET 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$')
  if [ "$a" != "$b" ]; then
    flipped=$((flipped + 1))
    echo "FLIP  shipped=$a  ceiling2=$b  $f"
  fi
done < "$POP/decided-ALL.txt"
echo "checked $((n - 1)) decided files; flipped at ceiling 2: $flipped"
echo "LEVERCHECK DONE"
