#!/usr/bin/env bash
# QUANT-ACTIVATION -- refuse the A/B unless the two arms are actually different.
#
#   ab-self-check.sh <binary> <valueB>
#
# ONE binary at TWO environment values has a failure mode that a verdict check
# cannot see: if the variable never reaches the solve -- wrong name, resolved
# before the worker thread, a `OnceLock` already warm -- then BOTH arms are the
# shipped arm and the sweep prints a perfect zero that reads exactly like
# agreement. `the_positive_path_guard_does_not_cross_a_thread_boundary` is the
# in-process half of this; this is the out-of-process half, and it is the one
# that matters because `smtcomp_cli` solves on a watchdog worker thread.
#
# The fixture is chosen so the arms DISAGREE ON THE VERDICT: its only universal
# is nested under a disjunction whose other disjunct is false, so level 0
# returns `unknown` ("no universal is asserted") and level 1 refutes. A fixture
# the two arms merely time differently would not do -- timing is exactly what
# ambient load moves.
set -u
AX="${1:?usage: ab-self-check.sh <binary> <valueB>}"
VB="${2:?usage: ab-self-check.sh <binary> <valueB>}"
[ -x "$AX" ] || { echo "SELF-CHECK ABORT: $AX missing or not executable"; exit 2; }
case "$VB" in
  ''|0) echo "SELF-CHECK ABORT: arm B value '$VB' IS the shipped arm; both arms would be A"; exit 2 ;;
esac

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cat > "$WORK/conv.smt2" <<'SMT'
(set-logic UF)
(declare-sort U 0)
(declare-fun q (U) Bool)
(declare-const w U)
(declare-const p Bool)
(assert (not p))
(assert (or p (forall ((y U)) (q y))))
(assert (not (q w)))
(check-sat)
SMT

verdict() {  # $1 = "" for the shipped arm, else the level
  local raw
  if [ -z "$1" ]; then
    raw=$(env -u AXEYUM_QINST_POSITIVE_PATH timeout 30 "$AX" "$WORK/conv.smt2" --timeout-ms 20000 2>/dev/null)
  else
    raw=$(AXEYUM_QINST_POSITIVE_PATH="$1" timeout 30 "$AX" "$WORK/conv.smt2" --timeout-ms 20000 2>/dev/null)
  fi
  printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$'
}

A=$(verdict "")
B=$(verdict "$VB")
echo "self-check: arm A (unset) = ${A:-none}"
echo "self-check: arm B ($VB)     = ${B:-none}"

# BOTH directions are asserted, because each failure reads as the other's
# success. A == unsat would mean the shipped arm already converts and the lever
# is measuring nothing; A == B would mean the variable never arrived.
if [ "$A" = "unsat" ]; then
  echo "SELF-CHECK FAIL: the SHIPPED arm refutes the conversion fixture, so the"
  echo "  A/B's arm A is not the shipped behaviour this lever is measured against."
  exit 3
fi
if [ "$B" != "unsat" ]; then
  echo "SELF-CHECK FAIL: arm B did not refute the conversion fixture. Either the"
  echo "  variable never reached the solve (both arms are arm A and a zero result"
  echo "  would be a variable that never arrived, not agreement), or the binary"
  echo "  predates the lever."
  exit 4
fi
echo "SELF-CHECK PASS: the arms disagree on a VERDICT, so a zero in the sweep"
echo "  would be a measurement rather than a variable that never arrived."
