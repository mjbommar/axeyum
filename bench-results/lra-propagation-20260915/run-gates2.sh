#!/usr/bin/env bash
# ADR-2122 -- the whole-workspace half of the pre-merge gates.
#
# `run-gates.sh` covers the suites this lane's theory changes; this covers the
# ones a change anywhere can break. Each step prints what it MEASURED (a count,
# not a word) so a step that silently examined nothing is visible.
set -u
cd "$(dirname "$0")/../.."
export CARGO_TARGET_DIR="${1:-/data0/axeyum/lra-propagation-target}"
fail=0

echo "=== cargo fmt --all --check (read-only) ==="
if cargo fmt --all --check; then echo "FMT: ok"; else echo "FMT: FAILED"; fail=1; fi

echo "=== cargo check --workspace --all-targets ==="
scripts/cargo-serialized.sh check --workspace --all-targets \
  > /tmp/lra-prop-check.log 2>&1
rc=$?
n=$(grep -cE '^error' /tmp/lra-prop-check.log || true)
echo "CHECK: rc=$rc errors=$n"
[ "$rc" = 0 ] && [ "$n" = 0 ] || { fail=1; grep -E '^error' /tmp/lra-prop-check.log | head -5; }

echo "=== clippy -D warnings (solver + bench + cnf, --features full) ==="
scripts/cargo-serialized.sh clippy -p axeyum-solver -p axeyum-bench -p axeyum-cnf \
  --all-targets --features full -- -D warnings > /tmp/lra-prop-clippy.log 2>&1
rc=$?
n=$(grep -cE '^error' /tmp/lra-prop-clippy.log || true)
echo "CLIPPY: rc=$rc errors=$n"
[ "$rc" = 0 ] && [ "$n" = 0 ] || { fail=1; grep -E '^error' /tmp/lra-prop-clippy.log | head -5; }

echo "=== lib sweep --features full --skip reconstruct:: ==="
scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full \
  -- --skip 'reconstruct::' > /tmp/lra-prop-libsweep.log 2>&1
rc=$?
line=$(grep -E '^test result' /tmp/lra-prop-libsweep.log | tail -1)
echo "LIB SWEEP: rc=$rc  $line"
# An ABSENT result line is an OOM or a build failure, not a pass.
[ -n "$line" ] || { echo "  NO 'test result:' LINE -- not a pass"; fail=1; }
case "$line" in *" 0 failed"*) ;; *) fail=1;; esac

if [ "$fail" != 0 ]; then echo "GATES2: FAILED"; exit 1; fi
echo "GATES2: all green"
