#!/usr/bin/env bash
# UFLIA-TRACE -- does `AXEYUM_QINST_TRIGGER_ALTERNATIVES` actually reach the
# solve in this binary, through this harness, on this host?
#
#   ab-self-check.sh <bin> [valueB] [fixture]
#
# A one-binary A/B cannot be sabotaged by using the same build twice, but it has
# the same failure in a different shape: if the variable never arrives, BOTH arms
# are the shipped arm and the run prints a perfect zero indistinguishable from
# agreement. Four ways that happens here, each real somewhere in this repository:
# the CLI solves on a WATCHDOG WORKER THREAD (a thread-local override would be
# inert, the environment is not); the cap resolves through a `OnceLock` (a value
# set after the first read is ignored); `taskset`/`bash -c` wrappers can drop the
# environment; and the shipped `1` and an unset variable are different code paths
# through `cap_lever!`.
#
# So this asserts a DIFFERENCE, reading the `QPROBE auto-triggers` line the
# compile loop emits. The shipped arm must report `alternatives=1` on every
# universal and arm B must report more on at least one.
#
# THE FIXTURE MUST REACH `q:egraph`, AND A HAND-WRITTEN TWO-CANDIDATE QUERY DOES
# NOT. The first draft used `forall x. f(x) = g(x)` with `f(b) != g(b)`, which
# `q:mbqi-quick` refutes at attempt 9 of the ladder: the e-matching compile loop
# never runs, no probe line is emitted, and the check reported MISSING on both
# arms. It failed honestly, which is the only reason this is a comment and not a
# silent PASS. The default fixture is a real UFLIA core that reaches the loop;
# override it with argument 3.
set -u
AX="${1:?usage: ab-self-check.sh <bin> [valueB] [fixture]}"
VB="${2:-4}"
FIXTURE="${3:-/nas3/data/axeyum/harness/core-select/cores/UFLIA_boogie_Cast_Cast.R_System.Object_System.Int32.smt2.core.smt2}"
[ -x "$AX" ] || { echo "ABORT: $AX missing"; exit 2; }
[ -r "$FIXTURE" ] || { echo "ABORT: fixture $FIXTURE unreadable"; exit 2; }

# The MAXIMUM `alternatives=` over the run, not the first: the two arms agree on
# every universal that has only one full-cover candidate, and a `grep -m1` would
# read one of those and report agreement.
alts() {  # $1 = "" for the shipped arm, else the cap value
  local raw
  if [ -z "$1" ]; then
    raw=$(env -u AXEYUM_QINST_TRIGGER_ALTERNATIVES AXEYUM_QPROBE=1 \
            timeout 60 "$AX" "$FIXTURE" --timeout-ms 10000 2>&1)
  else
    raw=$(AXEYUM_QINST_TRIGGER_ALTERNATIVES="$1" AXEYUM_QPROBE=1 \
            timeout 60 "$AX" "$FIXTURE" --timeout-ms 10000 2>&1)
  fi
  printf '%s\n' "$raw" | grep -oE 'QPROBE auto-triggers vars=[0-9]+ alternatives=[0-9]+' \
    | grep -oE 'alternatives=[0-9]+' | cut -d= -f2 | sort -n | tail -1
}

A=$(alts "")
B=$(alts "$VB")
echo "fixture:     $FIXTURE"
echo "shipped arm: max alternatives=${A:-MISSING}"
echo "arm B ($VB):  max alternatives=${B:-MISSING}"

if [ -z "${A:-}" ] || [ -z "${B:-}" ]; then
  echo "SELF-CHECK FAILED: no QPROBE auto-triggers line. The compile loop did not"
  echo "  run on this fixture, so this check cannot tell the arms apart."
  exit 3
fi
if [ "$A" != 1 ]; then
  echo "SELF-CHECK FAILED: the shipped arm reported max alternatives=$A, not 1."
  echo "  The lever is not OFF by default in this binary."
  exit 4
fi
if [ "$B" -le "$A" ]; then
  echo "SELF-CHECK FAILED: arm B reported max alternatives=$B, no more than the"
  echo "  shipped arm's $A. The variable is not reaching the solve, so both arms"
  echo "  are the shipped arm and every number the A/B prints is vacuous."
  exit 5
fi
echo "SELF-CHECK PASSED: the two arms differ ($A vs $B) through this binary and harness."
