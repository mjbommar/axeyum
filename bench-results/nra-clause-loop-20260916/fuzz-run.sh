#!/usr/bin/env bash
# The WHOLE `nra_differential_fuzz` file against the z3 oracle (~23 min).
#
# The whole file, not the one test this lane changed. ADR-2131's change to the
# clause loop made a sibling test's PREMISE stale -- `clause_loop_differential_
# fuzz_disagree_zero` panicked on `unsat` because the arm used to withhold every
# one -- and running only the test you edited is how the next one of those
# reaches main.
#
# `--features z3` IS MANDATORY: without it this file compiles to ZERO tests,
# prints "running 0 tests ... ok" and exits 0. The count is printed below and a
# zero count fails, because a green gate that ran nothing is worse than a red
# one.
set -u
cd "$(dirname "$0")/../.." || exit 2
LOG="${1:?usage: fuzz-run.sh <log-path>}"

scripts/cargo-serialized.sh test -p axeyum-solver --features z3 \
  --test nra_differential_fuzz -- --nocapture > "$LOG" 2>&1
rc=$?

line=$(grep -E "^test result" "$LOG" | tail -1)
if [ -z "$line" ]; then
  echo "FUZZ NO RESULT LINE (rc=$rc) -- a kill, not a result; check journalctl for oom-kill"
  exit 1
fi
# A NONZERO count, spelled out: "0 passed" here would mean the feature flag was
# dropped and the file compiled empty.
case "$line" in
  *" 0 passed"*) echo "FUZZ RAN ZERO TESTS -- the z3 feature did not take: $line"; exit 1 ;;
esac
echo "FUZZ rc=$rc :: $line"
grep -E 'clause-loop fuzz:|single-cell fuzz:|decline causes:' "$LOG"
[ "$rc" -eq 0 ] || exit 1
echo FUZZ_PASS
