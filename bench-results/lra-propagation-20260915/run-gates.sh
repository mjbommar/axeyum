#!/usr/bin/env bash
# ADR-2122 -- the pre-merge gates this lane's diff requires, by name.
#
#   run-gates.sh [target-dir]
#
# Every suite prints its own test count and this script REFUSES a zero: a
# feature-gated suite compiles to nothing and exits 0, which is a green-looking
# gate that checks nothing. An ABSENT `test result:` line is refused too -- that
# is an OOM or a build failure, not a pass.
#
# The dispatch/reason suite list is READ OUT OF `hooks/pre-push` at run time
# rather than copied here. A copied list measures the maintainer's memory of
# what the hook runs; a shrinking list would then report as a passing one. The
# count it extracts is printed so a reader can see the list was found at all --
# an empty extraction would otherwise look exactly like "every suite passed".
set -u
cd "$(dirname "$0")/../.."
export CARGO_TARGET_DIR="${1:-/data0/axeyum/lra-propagation-target}"

fail=0
run() {  # $1 = label, rest = the command
  local label="$1"; shift
  local out rc counts passed failed
  out=$("$@" 2>&1)
  rc=$?
  counts=$(printf '%s\n' "$out" | grep -oE 'test result: (ok|FAILED)\. [0-9]+ passed; [0-9]+ failed' || true)
  if [ -z "$counts" ]; then
    echo "GATE $label: NO 'test result:' LINE (rc=$rc) -- an absent result line is"
    echo "  an OOM or a build failure, not a pass"
    printf '%s\n' "$out" | tail -5
    fail=1
    return
  fi
  passed=$(printf '%s\n' "$counts" | grep -oE '[0-9]+ passed' | grep -oE '[0-9]+' | paste -sd+ | bc)
  failed=$(printf '%s\n' "$counts" | grep -oE '[0-9]+ failed' | grep -oE '[0-9]+' | paste -sd+ | bc)
  if [ "$rc" != 0 ] || [ "${failed:-1}" != 0 ]; then
    echo "GATE $label: FAILED (rc=$rc, passed=$passed, failed=$failed)"
    printf '%s\n' "$out" | grep -E '^(test .* FAILED|error)' | head -5
    fail=1
  elif [ "${passed:-0}" = 0 ]; then
    echo "GATE $label: ZERO TESTS RAN -- exits 0 and checks nothing"
    fail=1
  else
    echo "GATE $label: ok, $passed passed"
  fi
}

# --- the theory this lane changed ------------------------------------------
run "lra unit" cargo test -p axeyum-solver --lib --features full lra
run "simplex unit" cargo test -p axeyum-solver --lib --features full simplex
run "config_registry" cargo test -p axeyum-solver --lib --features full config_registry::tests

# --- the dispatch/reason suites, read from the hook -------------------------
SUITES=$(awk '/^  for suite in unknown_reason_coverage/,/; do$/' hooks/pre-push \
         | sed 's/^  for suite in //; s/; do$//; s/\\$//' | tr -s ' \n' ' ')
N=$(printf '%s\n' "$SUITES" | tr ' ' '\n' | grep -cvE '^$')
echo "dispatch/reason suites extracted from hooks/pre-push: $N"
if [ "$N" -lt 15 ]; then
  echo "REFUSING: only $N suites extracted; the parse has drifted from the hook"
  exit 2
fi
for suite in $SUITES; do
  run "dispatch/$suite" cargo test -p axeyum-solver --features full --test "$suite"
done

if [ "$fail" != 0 ]; then
  echo "GATES: FAILED"
  exit 1
fi
echo "GATES: all green"
