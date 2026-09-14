#!/usr/bin/env bash
# The arm makes five files abort that exited cleanly in the base.  Why?
#
# Hypothesis, from the code: `AXEYUM_MEMORY_LIMIT_MB=8192` does TWO things
# through ONE knob.  It makes the OFFLINE screens (`fm_admission`,
# `simplex_admission`) bind -- the intended effect -- but it ALSO raises the
# ONLINE CDCL(T) LRA construction's budget from `DEFAULT_ONLINE_LRA_BUDGET_BYTES`
# (640 MiB) to 8 GiB, because `NormalizationLimits::for_budget` reads the same
# number.  So a file the online engine previously refused at admission is now
# admitted, builds a far larger construction, and IT becomes the allocator.
#
# Read it off the screen's own report (`online_probe=`) and the peak RSS, with
# 24 GiB of room so neither arm dies before it can say anything.
BIN=/nas3/data/axeyum/harness/qflra-gap/bin/smtcomp_cli-cfcae7fa7
C=/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/

probe() {  # $1 = rel path, $2 = "" or MiB
  local tag="base(UNSET)"; [ -n "$2" ] && tag="arm($2)"
  printf '%-14s ' "$tag"
  if [ -z "$2" ]; then
    /usr/bin/time -f 'peak_rss_kb=%M' timeout 90 taskset -c 4-5 \
      "$BIN" "$C$1" --timeout-ms 24000 --trace 2>&1
  else
    AXEYUM_MEMORY_LIMIT_MB="$2" /usr/bin/time -f 'peak_rss_kb=%M' timeout 90 taskset -c 4-5 \
      "$BIN" "$C$1" --timeout-ms 24000 --trace 2>&1
  fi | grep -oE 'online_probe=[a-z-]+|peak_rss_kb=[0-9]+|^(sat|unsat|unknown)$|coefficient|budget' | tr '\n' ' '
  echo
}

ulimit -v $((24 * 1024 * 1024))
for f in \
  "QF_LRA/LassoRanker/Ultimate/Gcd.bpl_Iteration1_Lasso_7-phaseTemplate.smt2" \
  "QF_LRA/LassoRanker/CooperatingT2/collatz.t2.c_Iteration3_Loop_7-phaseTemplate.smt2" \
  "QF_LRA/LassoRanker/SV-COMP/NoriSharma-2013FSE-Fig8_true-termination.c_Iteration1_Loop_5-phaseTemplate.smt2"
do
  echo "### $f"
  probe "$f" ""
  probe "$f" 8192
  echo
done
