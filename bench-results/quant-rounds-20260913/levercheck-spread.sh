#!/usr/bin/env bash
# Check 2, over a SPREAD sample rather than a prefix.
#
# The prefix run checked 40 files and they were all LRA, because `decided-ALL`
# is in division order -- reading a prefix of a sorted list is how this repo
# has published false nulls before. Every 12th row instead, so every division
# is represented.
set -u
AX=/nas3/data/axeyum/harness/quant-rounds/bin/smtcomp_cli
POP=/nas3/data/axeyum/harness/quant-rounds/pop
BUDGET=20000

awk 'NR % 12 == 1' "$POP/decided-ALL.txt" > /tmp/qr-spread.$$
echo "spread sample: $(wc -l < /tmp/qr-spread.$$) of $(wc -l < "$POP/decided-ALL.txt")"
flipped=0
while read -r f; do
  a=$(timeout 40 taskset -c 6 env -u AXEYUM_QINST_ROUNDS "$AX" "$f" --timeout-ms $BUDGET 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$')
  b=$(timeout 40 taskset -c 6 env AXEYUM_QINST_ROUNDS=2 "$AX" "$f" --timeout-ms $BUDGET 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$')
  if [ "$a" != "$b" ]; then
    flipped=$((flipped + 1))
    echo "FLIP  shipped=$a  ceiling2=$b  ${f##*non-incremental/}"
  fi
done < /tmp/qr-spread.$$
echo "flipped at ceiling 2: $flipped"
rm -f /tmp/qr-spread.$$
echo "LEVER2 DONE"
