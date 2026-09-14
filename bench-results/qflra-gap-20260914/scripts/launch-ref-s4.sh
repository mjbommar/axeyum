#!/usr/bin/env bash
# Reference verdicts on s4's six P-core pairs.
#
# s4 is an i5-12600K: P-cores 0-11 (six SMT pairs), E-cores 12-15.  The E-cores
# are ~1.84x slower here and this run is DEADLINE-SENSITIVE (a reference that
# misses 24 s understates addressability), so it never touches them.
#
# Run here rather than on s5/s6/s7 so it cannot perturb the interleaved A/B:
# z3 and cvc5 peak around 150 MB on this division, against the 8 GiB our own
# undecided rows reach.
set -u
L=/nas3/data/axeyum/harness/qflra-gap
i=0
for pin in 0-1 2-3 4-5 6-7 8-9 10-11; do
  nohup setsid bash "$L/scripts/ref-run.sh" "rsh$i" \
      "$L/lists/QF_LRA.sh$i.txt" "$L/out/ref.sh$i.tsv" "$pin" 24 \
      > "$L/logs/ref.sh$i.log" 2>&1 < /dev/null &
  echo "launched ref shard $i on s4 pin $pin"
  i=$((i + 1))
done
echo "ALL_REF_LAUNCHED_S4"
