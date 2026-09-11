#!/usr/bin/env bash
# Control suite for the non-verdict classifier in scripts/parity-run.sh.
#
# WHY. Before 2026-09-11 the parity harness printed `unsolved` for everything
# that was not `sat`/`unsat`, discarded stderr, and never read the solver's exit
# status. A reasoned `unknown`, a harness timeout kill, an OOM **abort** and a
# crash were one indistinguishable word on the board. `QF_ABV/wchains140se.smt2`
# dies with "memory allocation of 127632960 bytes failed" under the 8 GiB
# `ulimit -v` and reaches no reporting path of its own, so no amount of solver
# instrumentation can describe it -- the runner has to.
#
# This suite pins the mapping. Mutating any arm (e.g. collapsing 134 into
# `unknown`, which is the defect above) must make exactly one case fail.
set -u

# Kept byte-identical to the `case` in parity-run.sh's run_one.
classify() {
  local rc="$1" why
  case "$rc" in
    0)   why=unknown ;;
    124) why=timeout ;;
    134) why=abort-SIGABRT ;;
    137) why=killed-SIGKILL ;;
    139) why=crash-SIGSEGV ;;
    *)   if (( rc > 128 )); then why="signal-$((rc - 128))"; else why="exit-$rc"; fi ;;
  esac
  echo "$why"
}

fail=0
check() {
  local got; got=$(classify "$1")
  if [[ "$got" != "$2" ]]; then
    echo "  FAIL rc=$1 got=$got want=$2" >&2; fail=1
  else
    echo "  ok   rc=$1 -> $got"
  fi
}

# rc=0 with no verdict is a solver that honoured its OWN --timeout-ms and
# exited cleanly; only a harness kill is 124. Both must stay distinguishable.
check 0   unknown
check 124 timeout
check 134 abort-SIGABRT
check 137 killed-SIGKILL
check 139 crash-SIGSEGV
check 143 signal-15
check 2   exit-2

# The classifier must also stay wired into the harness: a refactor that drops
# the sidecar write would leave every case above passing in isolation.
if ! grep -q 'nonverdict_sink' scripts/parity-run.sh; then
  echo "  FAIL: parity-run.sh no longer writes a non-verdict sidecar" >&2; fail=1
else
  echo "  ok   parity-run.sh writes the sidecar"
fi
if ! grep -q 'rc=\$?' scripts/parity-run.sh; then
  echo "  FAIL: parity-run.sh no longer captures the solver exit status" >&2; fail=1
else
  echo "  ok   parity-run.sh captures the exit status"
fi

if [[ "$fail" -ne 0 ]]; then echo "parity non-verdict classifier: FAILURES" >&2; exit 1; fi
echo "parity non-verdict classifier: all pass"
