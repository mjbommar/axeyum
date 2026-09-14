#!/usr/bin/env bash
# SKELETON-REACH -- the pre-merge gates this lane's change requires, run in one
# place so the `test result:` line of each is quotable and its COUNT visible.
#
# A feature-gated suite compiles to nothing and exits 0, so a NONZERO count is
# the evidence, never the exit status.
set -u
cd "$(dirname "$0")/../.."
export CARGO_TARGET_DIR=/data0/axeyum/skeleton-reach-target-base

run() {
  echo "=== $* ==="
  scripts/cargo-serialized.sh "$@" 2>&1 | grep -E '^(test result:|error|warning: unused|running [0-9]+ tests)' || true
}

run test -p axeyum-smtlib --lib
run test -p axeyum-solver --features full --test corpus_regression
run test -p axeyum-solver --lib --features full -- --test-threads=4
run test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1
echo "GATES-DONE"
