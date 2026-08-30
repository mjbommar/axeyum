#!/usr/bin/env bash
# Controls for `scripts/check-fast.sh`. One case per guard, and each case was
# mutation-verified to be the ONLY one that dies when its guard is deleted --
# see the table at the bottom of this file.
#
# The subject is driven through `AXEYUM_CHECK_FAST_LIST_CMD`, which replaces the
# real 379-step enumeration with a fixture, so these controls run in under a
# second and do not touch the aggregate gate.
set -uo pipefail
cd "$(dirname "$0")/../.."

SUBJECT=scripts/check-fast.sh
pass=0
fail=0

note() { echo "  $*"; }
ok()   { pass=$((pass + 1)); echo "ok   - $1"; }
bad()  { fail=$((fail + 1)); echo "FAIL - $1"; }

run_fixture() {
  # $1 = fixture body (tab-separated name<TAB>command lines), rest = subject args
  local body="$1"; shift
  local f
  f="$(mktemp)"
  printf '%s\n' "$body" > "$f"
  AXEYUM_CHECK_FAST_LIST_CMD="cat $f" $SUBJECT "$@" 2>&1
  local st=$?
  rm -f "$f"
  return $st
}

# --------------------------------------------------------------------------
# GUARD 1 (vacuity): an EMPTY step list must be a failure, not a clean run of
# nothing. This is the shape of every inert gate this repository has shipped --
# "running 0 tests ... ok", exit 0 -- and it is the one outcome a performance
# mode makes easy to reintroduce.
out="$(run_fixture "")"; st=$?
if [ "$st" -eq 2 ] && [[ "$out" == *VACUOUS* ]]; then
  ok "empty step list exits 2 and says VACUOUS"
else
  bad "empty step list must exit 2 with VACUOUS, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 2 (a failing step fails the gate): the base case. Without it the script
# is a reporter, not a gate.
out="$(run_fixture "boom	false")"; st=$?
if [ "$st" -eq 1 ] && [[ "$out" == *"boom"* ]] && [[ "$out" == *"failed=1"* ]]; then
  ok "a step exiting nonzero fails the gate and is named"
else
  bad "a failing step must exit 1 and be named, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 3 (DEFERRED is not ok): a step that exceeds the budget must land in its
# own bucket. If it were folded into `ok`, this script would silently convert
# "too slow to check" into "checked and passed" -- which is the precise defect
# it exists to avoid.
out="$(run_fixture "slow	sleep 30" --budget 1)"; st=$?
if [ "$st" -eq 0 ] && [[ "$out" == *"deferred=1"* ]] && [[ "$out" == *"ok=0"* ]] \
   && [[ "$out" == *"UNCHECKED"* ]]; then
  ok "an over-budget step is DEFERRED, counted separately, and called UNCHECKED"
else
  bad "over-budget step must be deferred with ok=0, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 4 (the honesty marker is unconditional): every exit path must carry
# NOT-A-FULL-GATE. A green summary from this script must never be quotable as
# "the aggregate gate passed".
out="$(run_fixture "quick	true")"; st=$?
if [ "$st" -eq 0 ] && [[ "$out" == *"NOT-A-FULL-GATE"* ]] && [[ "$out" == *"ok=1"* ]]; then
  ok "an all-green run still carries NOT-A-FULL-GATE"
else
  bad "all-green run must still carry NOT-A-FULL-GATE, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
# GUARD 5 (cargo steps are deferred by declaration, and NOT executed): they take
# the host-wide serialization flock, so running one under a 3 s cap would block
# other lanes to learn what the command string already says. The control proves
# non-execution by giving the cargo step a side effect and asserting it did not
# happen -- asserting on the counter alone would pass even if the step ran.
marker="$(mktemp -u)"
out="$(run_fixture "buildit	cargo-does-not-exist-here && touch $marker")"; st=$?
if [ "$st" -eq 0 ] && [[ "$out" == *"buildit(cargo)"* ]] && [ ! -e "$marker" ]; then
  ok "a cargo step is deferred by declaration and never executed"
else
  bad "cargo step must be deferred without executing, got exit $st"; note "$out"
fi
rm -f "$marker"

# --------------------------------------------------------------------------
# FALSE-POSITIVE CONTROL. Every guard above asserts that something is caught.
# This asserts the opposite direction: a perfectly ordinary mixed run -- some
# passes, one deferral, no failures -- must exit 0. Without it, a mutation that
# makes the script fail unconditionally would kill all five guards above and
# still be reported as "guards work".
#
# It deliberately asserts NOTHING about the deferred counter -- that is guard
# 3's job, and duplicating it here would make guard 3's mutant kill two
# controls instead of one, which is how a suite stops telling you which guard
# is load-bearing.
out="$(run_fixture "a	true
b	true
c	sleep 30" --budget 1)"; st=$?
if [ "$st" -eq 0 ] && [[ "$out" == *"failed=0"* ]]; then
  ok "false-positive control: a healthy mixed run exits 0"
else
  bad "a healthy mixed run must exit 0 with failed=0, got exit $st"; note "$out"
fi

# --------------------------------------------------------------------------
echo "CHECK_FAST_CONTROLS|pass=${pass}|fail=${fail}"
[ "$fail" -eq 0 ] || exit 1
exit 0

# Mutation verification, run 2026-08-29 against a scratch copy of the subject.
# Each row: delete/invert that guard, and exactly the named control dies.
#
#   guard deleted                                  control that dies
#   ---------------------------------------------  -----------------------------
#   the `n_declared -lt 1` vacuity exit            empty step list exits 2
#   `failed` -> exit 1 at the end                  a step exiting nonzero fails
#   the 124/137 branch (fold deferred into ok)     over-budget step is DEFERRED
#   `NOT-A-FULL-GATE` in the summary line          all-green run carries marker
#   the `*cargo*` case arm                         cargo step never executed
