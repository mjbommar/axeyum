#!/usr/bin/env bash
# ADR-2125: the pre-merge gate list, with a NONZERO test count confirmed for each.
#
# The 22 dispatch/reason suites are read out of `hooks/pre-push` AT RUN TIME, not
# copied. A copied list measures the maintainer's memory of what the hook runs,
# and a SHRINKING list then reports as a passing one; this extraction refuses if
# it finds fewer than 15, so an extraction that silently matched nothing cannot
# look like a clean sweep. (ADR-2122's `run-gates.sh` made the same choice for
# the same reason; this is that guard, kept.)
#
# Every `cargo test` line here prints a count and this script FAILS on zero, for
# the reason CLAUDE.md gives six times over: a feature-gated suite compiles to
# nothing and exits 0.
#
# Usage: run-gates.sh            (from the repository root)
set -u

fail=0
note() { printf '%-58s %s\n' "$1" "$2"; }

run_counted() {
  # $1 label, rest: cargo args
  local label="$1"; shift
  local log; log="$(mktemp)"
  scripts/cargo-serialized.sh "$@" > "$log" 2>&1
  local rc=$?
  local n
  n=$(sed -n 's/^test result: .* \([0-9][0-9]*\) passed.*/\1/p' "$log" | head -1)
  n="${n:-0}"
  local f
  f=$(sed -n 's/^test result: .*; \([0-9][0-9]*\) failed.*/\1/p' "$log" | head -1)
  f="${f:-0}"
  if [ "$rc" -ne 0 ]; then
    note "$label" "FAILED rc=$rc ($n passed, $f failed)"; tail -30 "$log"; fail=1
  elif [ "$n" = "0" ]; then
    note "$label" "INERT (0 tests) -- not evidence"; fail=1
  else
    note "$label" "ok ($n passed, $f failed)"
  fi
  rm -f "$log"
}

run_plain() {
  local label="$1"; shift
  local log; log="$(mktemp)"
  "$@" > "$log" 2>&1
  local rc=$?
  if [ "$rc" -ne 0 ]; then
    note "$label" "FAILED rc=$rc"; tail -30 "$log"; fail=1
  else
    note "$label" "ok"
  fi
  rm -f "$log"
}

echo "=== ADR-2125 gates ==="

run_plain "cargo fmt --all --check" cargo fmt --all --check
run_plain "cargo check --workspace --all-targets (default features)" \
  scripts/cargo-serialized.sh check --workspace --all-targets
run_plain "clippy -D warnings: solver + bench + cnf, --features full" \
  scripts/cargo-serialized.sh clippy -p axeyum-solver -p axeyum-bench -p axeyum-cnf \
  --all-targets --features full -- -D warnings

run_counted "--lib --features full lra" test -p axeyum-solver --lib --features full lra
run_counted "--lib --features full simplex" test -p axeyum-solver --lib --features full simplex
run_counted "--lib --features full config_registry::tests" \
  test -p axeyum-solver --lib --features full config_registry::tests
run_counted "--lib --features full lazy_smt_counters" \
  test -p axeyum-solver --lib --features full lazy_smt_counters

# The dispatch/reason suites, EXTRACTED from the hook.
SUITES=$(sed -n '/^  for suite in unknown_reason_coverage/,/done$/p' hooks/pre-push \
         | sed 's/^  for suite in //; s/\\$//; s/; do$//' \
         | tr ' ' '\n' | sed '/^$/d; /^do$/d; /^gated_test/,$d')
n_suites=$(printf '%s\n' "$SUITES" | sed '/^$/d' | wc -l)
if [ "$n_suites" -lt 15 ]; then
  echo "ABORT: extracted only $n_suites dispatch suites from hooks/pre-push -- the extraction matched too little to be a sweep"
  exit 2
fi
echo "--- $n_suites dispatch/reason suites, extracted from hooks/pre-push ---"
for suite in $SUITES; do
  run_counted "dispatch/reason: $suite" test -p axeyum-solver --features full --test "$suite"
done

echo "--- the lib sweep ---"
run_counted "--lib --features full -- --skip reconstruct::" \
  test -p axeyum-solver --lib --features full -- --skip 'reconstruct::'

echo "--- the capability ratchet ---"
#
# `--nocapture`, and the output is KEPT, because a pass count is not a result
# here. Each family calibrates the machine before and after its sweep and marks
# the run `NOT COMPARABLE` (ratchet not enforced) or `ADVISORY ONLY` (do not
# raise a baseline from it). A bare "12 passed" is compatible with every family
# being NOT COMPARABLE, i.e. with the ratchet having been enforced on nothing --
# which is exactly the shape of a gate that cannot fail.
#
# This was a REAL defect in this script: its first run through here reported
# "ok (12 passed, 0 failed)" and `run_counted` then deleted the only copy of the
# lines that say whether those 12 meant anything.
ratchet_log="$(dirname "$0")/frontier-ratchet.log"
scripts/cargo-serialized.sh test -p axeyum-solver --test progress_frontier \
  --features full -- --test-threads=1 --nocapture > "$ratchet_log" 2>&1
rc=$?
n=$(sed -n 's/^test result: .* \([0-9][0-9]*\) passed.*/\1/p' "$ratchet_log" | head -1)
n="${n:-0}"
grep -E 'FRONTIER|TIMING|reference frame|NOT COMPARABLE|ADVISORY|REGRESSION' "$ratchet_log" || true
if [ "$rc" -ne 0 ]; then
  note "progress_frontier (--nocapture, log kept)" "FAILED rc=$rc"; fail=1
elif [ "$n" = "0" ]; then
  note "progress_frontier (--nocapture, log kept)" "INERT (0 tests) -- not evidence"; fail=1
else
  incomparable=$(grep -c 'NOT COMPARABLE' "$ratchet_log" || true)
  note "progress_frontier (--nocapture, log kept)" \
    "ok ($n passed; $incomparable family/families NOT COMPARABLE -- read $ratchet_log)"
fi

if [ "$fail" -ne 0 ]; then
  echo "GATES FAILED"
  exit 1
fi
echo "GATES PASSED"
