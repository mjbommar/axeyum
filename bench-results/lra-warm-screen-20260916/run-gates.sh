#!/usr/bin/env bash
# ADR-2132: the pre-merge gate list, with a NONZERO test count confirmed for each.
#
# Adapted from `bench-results/lra-warm-basis-20260916/run-gates.sh` (ADR-2125),
# keeping every guard in it and changing two things.
#
#   1. The clippy line is the BATTERY'S EXACT LINT --
#      `--workspace --all-targets --all-features -D warnings` -- and not
#      ADR-2125's three-crate narrowing. CLAUDE.md's own measurement is that a
#      lib-only clippy hides `examples/` and `tests/`, and this lane added a
#      test file and touched `lib.rs`. If `z3-sys` cannot fetch its asset in a
#      fresh worktree the narrower form runs INSTEAD and the substitution is
#      PRINTED, because a fallback nobody is told about is a gate that quietly
#      became a different gate.
#   2. The dispatch/reason suites go through
#      `bench-results/real-opaque-20260914/run-dispatch-reason-suites.sh`, which
#      reads the block out of the hook itself and whose own two first-run bugs
#      (a substring match on "0 passed", and a missing result line reported as a
#      suite result) are fixed there rather than re-introduced here.
#
# Every `cargo test` line prints a count and this script FAILS on zero, for the
# reason CLAUDE.md gives six times over: a feature-gated suite compiles to
# nothing and exits 0.
#
# Usage: run-gates.sh            (from the repository root)
set -u

fail=0
note() { printf '%-64s %s\n' "$1" "$2"; }

run_counted() {
  # $1 label, rest: cargo args
  local label="$1"; shift
  local log; log="$(mktemp)"
  scripts/cargo-serialized.sh "$@" > "$log" 2>&1
  local rc=$?
  local n f
  n=$(sed -n 's/^test result: .* \([0-9][0-9]*\) passed.*/\1/p' "$log" | head -1)
  n="${n:-0}"
  f=$(sed -n 's/^test result: .*; \([0-9][0-9]*\) failed.*/\1/p' "$log" | head -1)
  f="${f:-0}"
  if [ "$rc" -ne 0 ]; then
    note "$label" "FAILED rc=$rc ($n passed, $f failed)"; tail -40 "$log"; fail=1
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
    note "$label" "FAILED rc=$rc"; tail -40 "$log"; fail=1
  else
    note "$label" "ok"
  fi
  rm -f "$log"
}

echo "=== ADR-2132 gates ==="

run_plain "cargo fmt --all --check" cargo fmt --all --check
run_plain "cargo check --workspace --all-targets (default features)" \
  scripts/cargo-serialized.sh check --workspace --all-targets

# THE BATTERY'S LINT. Tried first; the narrower form is a stated substitution.
clippy_log="$(mktemp)"
if scripts/cargo-serialized.sh clippy --workspace --all-targets --all-features \
     -- -D warnings > "$clippy_log" 2>&1; then
  note "clippy --workspace --all-targets --all-features -D warnings" "ok"
else
  crc=$?
  if grep -qE 'z3-sys|failed to (download|fetch)|Could not find libz3|No such file.*z3' "$clippy_log"; then
    note "clippy --workspace --all-targets --all-features" \
      "COULD NOT RUN (z3-sys asset, rc=$crc) -- SUBSTITUTING the narrower form"
    run_plain "clippy -p solver -p bench -p cnf --all-targets --all-features -D warnings" \
      scripts/cargo-serialized.sh clippy -p axeyum-solver -p axeyum-bench -p axeyum-cnf \
      --all-targets --all-features -- -D warnings
  else
    note "clippy --workspace --all-targets --all-features -D warnings" "FAILED rc=$crc"
    tail -40 "$clippy_log"; fail=1
  fi
fi
rm -f "$clippy_log"

run_counted "--lib --features full lra" test -p axeyum-solver --lib --features full lra
run_counted "--lib --features full simplex" test -p axeyum-solver --lib --features full simplex
run_counted "--lib --features full config_registry::tests" \
  test -p axeyum-solver --lib --features full config_registry::tests
run_counted "--lib --features full lazy_smt_counters" \
  test -p axeyum-solver --lib --features full lazy_smt_counters
run_counted "--lib --features full dpll_t::tests" \
  test -p axeyum-solver --lib --features full dpll_t::tests
run_counted "--test lra_warm_screen_2132 (release)" \
  test --release -p axeyum-solver --features full --test lra_warm_screen_2132

echo "--- the dispatch/reason suites, read out of the hook by the shared runner ---"
run_plain "run-dispatch-reason-suites.sh" \
  bash bench-results/real-opaque-20260914/run-dispatch-reason-suites.sh

echo "--- the static checks ---"
run_plain "check-suite-gating.py" python3 scripts/check-suite-gating.py
run_plain "check-config-registry-staleness.py" python3 scripts/check-config-registry-staleness.py
run_plain "check-merge-hygiene.sh" bash scripts/check-merge-hygiene.sh
run_plain "check-links.sh" bash scripts/check-links.sh
run_plain "mutation_controls.py --check-anchors" \
  python3 scripts/tests/mutation_controls.py --check-anchors

echo "--- the lib sweep ---"
run_counted "--lib --features full -- --skip reconstruct::" \
  test -p axeyum-solver --lib --features full -- --skip 'reconstruct::'

echo "--- the capability ratchet ---"
#
# `--nocapture`, and the output is KEPT, because a pass count is not a result
# here. Each family calibrates the machine before and after its sweep and marks
# the run `NOT COMPARABLE` (ratchet not enforced) or `ADVISORY ONLY` (do not
# raise a baseline from it). A bare "12 passed" is compatible with every family
# being NOT COMPARABLE -- the ratchet enforced on nothing, which is exactly the
# shape of a gate that cannot fail. ADR-2125 §5.8 needed THREE runs and kept all
# three because the disagreement between them was the finding: `nra_degree` read
# 24.1 ms on a contended frame and 7.2 ms on an idle one against the same 23.0 ms
# ceiling, a 3.3x swing at fixed code.
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
