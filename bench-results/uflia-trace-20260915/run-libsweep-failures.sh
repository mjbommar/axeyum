#!/usr/bin/env bash
# UFLIA-TRACE -- re-run, in isolation, the two `--lib --features full` tests that
# failed during a sweep taken at host load 51-93.
#
# Both are WALL-CLOCK BOUNDED and neither is in this lane's diff:
# `check_qf_uf_with_config_is_bounded_by_timeout` (euf_egraph.rs) asserts a 50 ms
# budget finishes inside 2 s, and `pathological_overbound_stays_terminal_under_
# every_policy` (auto.rs) asserts a policy takes a refusal inside its budget.
#
# "It looks load-sensitive" is an argument, not a measurement, so this runs them
# and prints the counts. No `timeout` around cargo: `cargo-serialized.sh` takes a
# host-wide flock, so a timeout here measures the queue.
set -eu
cd "$(dirname "$0")/../.."
export CARGO_TARGET_DIR="${1:-/data0/axeyum/uflia-trace-target-base}"
echo "load at start: $(uptime)"
scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full \
  check_qf_uf_with_config_is_bounded_by_timeout
scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full \
  pathological_overbound_stays_terminal_under_every_policy
echo "load at end: $(uptime)"
