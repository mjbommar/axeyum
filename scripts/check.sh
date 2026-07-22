#!/usr/bin/env bash
# Plain-shell fallback for `just check`: runs every gate CI runs (except
# cargo-deny, which needs the tool installed) so the preferred aggregate check
# is runnable on a fresh machine without `just`. Mirrors the `check` recipe in
# the justfile; keep the two in sync.
#
# Usage: ./scripts/check.sh
# Honor CARGO_BUILD_JOBS / a low -j on memory-constrained hosts, e.g.
#   CARGO_BUILD_JOBS=4 ./scripts/check.sh
set -uo pipefail

cd "$(dirname "$0")/.."

fail=0
step() {
  local name="$1"; shift
  echo "=== $name ==="
  if "$@"; then
    echo "--- $name: ok"
  else
    echo "--- $name: FAILED"
    fail=1
  fi
}

step fmt    cargo fmt --all --check
step clippy cargo clippy --workspace --all-targets --all-features -- -D warnings
step test   cargo test --workspace --all-features
export RUSTDOCFLAGS="-D warnings" # match CI's deny-warnings rustdoc
step doc    cargo doc --workspace --all-features --no-deps
step lean-construct-matrix-tests python3 -m unittest scripts.tests.test_lean_official_construct_matrix
step lean-construct-matrix python3 scripts/check-lean-official-construct-matrix.py
step foundational-resources ./scripts/check-foundational-resources.sh
step rules-as-code-generate python3 scripts/gen-rules-as-code-dashboard.py
step rules-as-code-validate python3 scripts/validate-rules-as-code.py
step rules-as-code-query-summary python3 scripts/query-rules-as-code.py summary
step rules-as-code-query-coverage-domain python3 scripts/query-rules-as-code.py coverage --by domain --require-any
step rules-as-code-query-coverage-validation python3 scripts/query-rules-as-code.py coverage --by validation --require-any
step rules-as-code-query-coverage-fragment-json python3 scripts/query-rules-as-code.py coverage --by fragment --format json --require-any
step rules-as-code-query-pack python3 scripts/query-rules-as-code.py packs --text procurement --require-any
step rules-as-code-query-checks python3 scripts/query-rules-as-code.py checks --pack procurement_scoring_v0 --proof-status checked --require-any
step rules-as-code-query-families python3 scripts/query-rules-as-code.py families --pack procurement_scoring_v0 --text quality --require-any
step rules-as-code-query-rows python3 scripts/query-rules-as-code.py rows --pack procurement_scoring_v0 --family bounded_awards --text 2026-08-02 --limit 3 --require-any
step rules-as-code-query-grant-pack python3 scripts/query-rules-as-code.py packs --pack grant_allocation_v0 --require-any
step rules-as-code-query-grant-checks python3 scripts/query-rules-as-code.py checks --pack grant_allocation_v0 --validation qf_lra_farkas_solver_regression --proof-status checked --require-any
step rules-as-code-query-grant-families python3 scripts/query-rules-as-code.py families --pack grant_allocation_v0 --text balanced --require-any
step rules-as-code-query-grant-rows python3 scripts/query-rules-as-code.py rows --pack grant_allocation_v0 --family balanced_budget_allocations --text 1/2 --limit 3 --require-any
step rules-as-code-query-monotonicity python3 scripts/query-rules-as-code.py checks --text monotonicity --require-any
step rules-as-code-query-adjacent python3 scripts/query-rules-as-code.py families --text adjacent --require-any
step rules-as-code-query-quality-rows python3 scripts/query-rules-as-code.py rows --pack procurement_scoring_v0 --family quality_monotonicity_adjacent --limit 3 --require-any
step rules-as-code-generated-clean git diff --exit-code docs/rules-as-code/generated
step links         ./scripts/check-links.sh

if [ "$fail" -ne 0 ]; then
  echo "check: one or more gates FAILED" >&2
  exit 1
fi
echo "check: all gates passed"
