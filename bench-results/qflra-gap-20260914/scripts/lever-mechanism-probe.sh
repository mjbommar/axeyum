#!/usr/bin/env bash
# MECHANISM proof that AXEYUM_MEMORY_LIMIT_MB is live, not silently ignored.
#
# A verdict count cannot show this -- a silently-ignored flag prints the same
# number. What CAN show it: the refusal string is FORMATTED FROM THE VALUE.
# `lra::fm_admission` prints "... over memory_limit_mb {budget/1MiB} ...".
# So if two different values print two different numbers, and the unset run
# prints NO such line at all, the value reached the admission screen. No other
# code path can produce those digits.
BIN=/nas3/data/axeyum/harness/qflra-gap/bin/smtcomp_cli-cfcae7fa7
F=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/QF_LRA/2017-Heizmann-UltimateInvariantSynthesis/_sanfoundry_10_ground.i_6_3_3.bpl_13.smt2

probe() {  # $1 = label, $2 = env value ("" = unset)
  echo "### $1"
  if [ -z "$2" ]; then
    ( ulimit -v $((8 * 1024 * 1024)); timeout 60 "$BIN" "$F" --timeout-ms 24000 --trace )
  else
    ( ulimit -v $((8 * 1024 * 1024)); AXEYUM_MEMORY_LIMIT_MB="$2" timeout 60 "$BIN" "$F" --timeout-ms 24000 --trace )
  fi
  echo "rc=$?"
  echo
}

probe "UNSET (the board's configuration)" ""
probe "AXEYUM_MEMORY_LIMIT_MB=8192" 8192
probe "AXEYUM_MEMORY_LIMIT_MB=2048" 2048
