#!/usr/bin/env bash
# ADR-2122 -- the capability ratchet.
#
# Pinned to `taskset -c 0-7` because this box is hybrid and the sweep is 1.84x
# slower on the E-cores; an unpinned run has reported a REGRESSION that never
# happened. Read the `reference frame [family]` lines before believing any
# verdict this prints: a run marked NOT COMPARABLE does not enforce the ratchet,
# and one marked ADVISORY ONLY must not raise a baseline.
#
# `--features full` is MANDATORY: `tests/progress_frontier.rs` is
# `#![cfg(feature = "full")]` and without it this prints "running 0 tests ... ok"
# and exits 0. Confirm a NONZERO count (10).
#
# Do NOT commit `bench-results/frontier/*.json` from this run.
set -u
cd "$(dirname "$0")/../.."
export CARGO_TARGET_DIR="${1:-/data0/axeyum/lra-propagation-target}"
taskset -c 0-7 scripts/cargo-serialized.sh test -p axeyum-solver \
  --test progress_frontier --features full -- --test-threads=1 --nocapture
