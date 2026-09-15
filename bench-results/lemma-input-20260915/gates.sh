#!/usr/bin/env bash
# LEMMA-INPUT -- the gate battery, each gate named and each count quoted.
# `check-clippy-complete.sh` is run separately (it is the long one).
set -u
cd "$(dirname "$0")/../.." || exit 2
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-/data0/axeyum/lemma-input-target-gate}"
rc=0
step() { echo; echo "===== $* ====="; }

step "cargo fmt --all --check"
cargo fmt --all --check && echo "fmt: exit 0" || { echo "fmt: FAILED"; rc=1; }

step "cargo check --workspace --all-targets"
scripts/cargo-serialized.sh check --workspace --all-targets 2>&1 | tail -3 || rc=1

step "cargo check -p axeyum-solver --all-targets (DEFAULT features)"
scripts/cargo-serialized.sh check -p axeyum-solver --all-targets 2>&1 | tail -3 || rc=1

step "RUSTDOCFLAGS=-D warnings cargo doc --workspace --all-features --no-deps"
RUSTDOCFLAGS="-D warnings" scripts/cargo-serialized.sh doc --workspace --all-features --no-deps 2>&1 | tail -3 || rc=1

step "cargo test -p axeyum-solver --features full --test corpus_regression"
scripts/cargo-serialized.sh test -p axeyum-solver --features full --test corpus_regression 2>&1 | grep -E "^test result|^error" || rc=1

step "cargo test -p axeyum-solver --lib --features full -- --test-threads=4"
scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full -- --test-threads=4 2>&1 | grep -E "^test result|^error" || rc=1

step "cargo test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1"
scripts/cargo-serialized.sh test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1 2>&1 | grep -E "^test result|reference frame|^error" || rc=1

step "scripts/check-merge-hygiene.sh"
scripts/check-merge-hygiene.sh 2>&1 | tail -5 || rc=1

step "python3 scripts/check-suite-gating.py"
python3 scripts/check-suite-gating.py 2>&1 | tail -4 || rc=1

step "python3 scripts/check-config-registry-staleness.py"
python3 scripts/check-config-registry-staleness.py 2>&1 | tail -4 || rc=1

echo
echo "===== gate battery rc=$rc ====="
exit "$rc"
