#!/usr/bin/env bash
# UFLIA-TRACE -- the capability ratchet, with the two lines that decide whether
# its verdict may be believed.
#
# `--features full` is mandatory: `tests/progress_frontier.rs` is
# `#![cfg(feature = "full")]`, so without it this prints "running 0 tests ... ok"
# and exits 0. The count is asserted below rather than assumed.
#
# Read `reference frame [family]` and any NOT COMPARABLE / ADVISORY ONLY line
# before believing a REGRESSION: contention moves these numbers by 5 of 40 at
# fixed code on these boxes.
set -eu
cd "$(dirname "$0")/../.."
exec scripts/cargo-serialized.sh test -p axeyum-solver --test progress_frontier \
  --features full -- --test-threads=1
