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
step links  ./scripts/check-links.sh

if [ "$fail" -ne 0 ]; then
  echo "check: one or more gates FAILED" >&2
  exit 1
fi
echo "check: all gates passed"
