#!/usr/bin/env bash
# The `axeyum-solver` lib sweep, bounded so it reports a RESULT rather than a
# kill.
#
# Run unbounded on 2026-09-16 it exited 143 with no `test result:` line at all,
# and `journalctl` says why: `oom-kill`, 24G peak, the `cargo-serialized.sh`
# memory ceiling firing on the `reconstruct::` module -- which builds kernel
# proof terms and is the heaviest thing in the crate. Exit 143 describes the
# CEILING, not a failing test, and an absent `test result:` line IS the finding.
#
# Two changes, and both are bounds rather than exclusions of inconvenient
# results:
#
#   --skip reconstruct::   those tests are gated elsewhere and are not what an
#                          NRA route change can break; running them here buys
#                          nothing and costs the whole sweep.
#   --test-threads=4       the peak is the SUM over concurrent tests, so the
#                          thread count is the actual lever on it.
#
# The count is printed and must be NONZERO: a feature-gated suite that compiles
# to nothing prints "running 0 tests ... ok" and exits 0.
set -u
cd "$(dirname "$0")/../.." || exit 2
LOG="${1:?usage: lib-sweep.sh <log-path>}"

scripts/cargo-serialized.sh test -p axeyum-solver --lib --features full \
  -- --skip reconstruct:: --test-threads=4 > "$LOG" 2>&1
rc=$?

line=$(grep -E "^test result" "$LOG" | tail -1)
if [ -z "$line" ]; then
  echo "LIB_SWEEP NO RESULT LINE (rc=$rc) -- this is a kill, not a result."
  echo "  check: journalctl | grep oom-kill"
  exit 1
fi
echo "LIB_SWEEP rc=$rc :: $line"
[ "$rc" -eq 0 ] || exit 1
echo LIB_SWEEP_PASS
