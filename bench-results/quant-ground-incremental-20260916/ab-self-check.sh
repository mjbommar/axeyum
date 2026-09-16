#!/usr/bin/env bash
# QUANT-GROUND-INCREMENTAL -- refuse the A/B unless the two arms are actually
# different (ADR-2124).
#
#   ab-self-check.sh <binary> <valueB>
#
# ONE binary at TWO environment values has a failure mode a verdict check cannot
# see: if the variable never reaches the solve -- wrong name, resolved before the
# worker thread, a `OnceLock` already warm -- then BOTH arms are the shipped arm
# and the sweep prints a perfect zero that reads exactly like agreement.
# `smtcomp_cli` solves on a watchdog worker thread, which is exactly where a
# thread-local guard would be lost, so this has to be checked out of process.
#
# WHY THIS ONE CANNOT USE A VERDICT FIXTURE, and why that is not a weakening.
# ADR-2120's lever was a CAPABILITY lever: level 1 refutes a small query level 0
# returns `unknown` on, so a five-line fixture separates the arms by verdict.
# This lever is a REGIME lever. It changes nothing about what the loop can
# conclude -- the abstraction is a weakening and the session's `unsat` is
# re-established by the cold route either way -- it changes only whether the
# accumulated ground set is re-solved from scratch each due round. Every query
# small enough to be a self-check fixture decides before the difference can
# show, and the one place the arms DID separate on this lane's 53-core probe is
# a 24-second core. A fixture the two arms merely time differently would be
# worthless here: timing is exactly what ambient load moves.
#
# So the hard gate is a DIRECT OBSERVATION that the variable arrived and was
# consulted, taken from the binary's own configuration line rather than from any
# behaviour that load could imitate:
#
#   ; config digest=<hex> entries=... env:AXEYUM_QINST_GROUND_SESSION=1 ...
#
# The digest is computed over the resolved configuration, so arm B's differing
# from arm A's is not a claim about the lever's effect -- it is the statement
# that the two arms ARE two configurations. That is precisely what a zero in the
# sweep needs to be a measurement.
set -u
AX="${1:?usage: ab-self-check.sh <binary> <valueB>}"
VB="${2:?usage: ab-self-check.sh <binary> <valueB>}"
[ -x "$AX" ] || { echo "SELF-CHECK ABORT: $AX missing or not executable"; exit 2; }
case "$VB" in
  ''|0) echo "SELF-CHECK ABORT: arm B value '$VB' IS the shipped arm; both arms would be A"; exit 2 ;;
esac

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cat > "$WORK/probe.smt2" <<'SMT'
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const c Int)
(assert (< a 10))
(assert (forall ((x Int)) (= (f x) c)))
(assert (not (= (f a) c)))
(check-sat)
SMT

line() {  # $1 = "" for the shipped arm, else the level
  if [ -z "$1" ]; then
    env -u AXEYUM_QINST_GROUND_SESSION timeout 30 "$AX" "$WORK/probe.smt2" \
      --trace --timeout-ms 20000 2>/dev/null | grep -m1 '^; config digest='
  else
    AXEYUM_QINST_GROUND_SESSION="$1" timeout 30 "$AX" "$WORK/probe.smt2" \
      --trace --timeout-ms 20000 2>/dev/null | grep -m1 '^; config digest='
  fi
}

verdict() {
  if [ -z "$1" ]; then
    env -u AXEYUM_QINST_GROUND_SESSION timeout 30 "$AX" "$WORK/probe.smt2" \
      --timeout-ms 20000 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$'
  else
    AXEYUM_QINST_GROUND_SESSION="$1" timeout 30 "$AX" "$WORK/probe.smt2" \
      --timeout-ms 20000 2>/dev/null | grep -m1 -oE '^(sat|unsat|unknown)$'
  fi
}

LA=$(line "")
LB=$(line "$VB")
DA=$(printf '%s\n' "$LA" | grep -oE 'digest=[0-9a-f]+')
DB=$(printf '%s\n' "$LB" | grep -oE 'digest=[0-9a-f]+')
VA=$(verdict "")
VBV=$(verdict "$VB")

echo "self-check: arm A (unset) config $DA  verdict ${VA:-none}"
echo "self-check: arm B ($VB)     config $DB  verdict ${VBV:-none}"

if [ -z "$DA" ] || [ -z "$DB" ]; then
  echo "SELF-CHECK FAIL: no `; config digest=` line from one or both arms, so"
  echo "  nothing was observed. This is a run that did not happen, not a result."
  exit 3
fi
if [ "$DA" = "$DB" ]; then
  echo "SELF-CHECK FAIL: the two arms resolved the SAME configuration, so the"
  echo "  variable never reached the solve. A zero in the sweep would be a"
  echo "  variable that never arrived, not agreement."
  exit 4
fi
case "$LB" in
  *"env:AXEYUM_QINST_GROUND_SESSION=$VB"*) ;;
  *)
    echo "SELF-CHECK FAIL: arm B's configuration line does not NAME the override."
    echo "  The digests differ for some other reason, which is not the thing"
    echo "  this check exists to establish."
    exit 5 ;;
esac
case "$LA" in
  *"env:AXEYUM_QINST_GROUND_SESSION"*)
    echo "SELF-CHECK FAIL: arm A's configuration line names the override, so arm A"
    echo "  is not the shipped configuration this lever is measured against."
    exit 6 ;;
esac
# CORROBORATION, not a gate: the arms must still agree on a query both decide.
# A disagreement here would be a soundness defect and must stop the sweep even
# though the sweep's own summariser would also catch it -- catching it before
# spending four hours is the point.
if [ -n "$VA" ] && [ -n "$VBV" ] && [ "$VA" != "$VBV" ] \
   && [ "$VA" != "unknown" ] && [ "$VBV" != "unknown" ]; then
  echo "SELF-CHECK FAIL: the arms DECIDED a refutable query differently"
  echo "  (A=$VA, B=$VBV). That is a soundness defect, not a lever effect."
  exit 7
fi
echo "SELF-CHECK PASS: the arms are two distinct configurations and arm B's own"
echo "  line names the override, so a zero in the sweep would be a measurement"
echo "  rather than a variable that never arrived. Both decided the control"
echo "  query as ${VA:-none}/${VBV:-none}."
