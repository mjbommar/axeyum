#!/usr/bin/env bash
# QUANT-SESSION-ARITH (ADR-2130) -- the re-run after the clippy fixes.
#
#   gates2.sh <logfile>
#
# Clippy first, because it is the step that found real defects in this lane's
# own code (a `build`/`built` near-collision, a doc backtick split across a line
# break, and `new_with_limits` crossing the 100-line ceiling once the level-2
# atom pass was added). The per-crate `-p ... --features full` form does not run
# it; the battery's own workspace/all-targets/all-features form does.
set -u
LOG="${1:-/tmp/qsa-gates2.log}"
cd "$(dirname "$0")/../.." || exit 2
: > "$LOG"

step() {
  local label="$1"; shift
  echo "=== STEP $label ===" >> "$LOG"
  "$@" >> "$LOG" 2>&1
  echo "=== RC $label = $? ===" >> "$LOG"
}

CS=scripts/cargo-serialized.sh

step clippy-workspace $CS clippy --workspace --all-targets --all-features -- -D warnings
step cert $CS test -p axeyum-solver --features full --test quant_session_arith_certificate
step session-theory $CS test -p axeyum-solver --features full --lib qinst_session_theory
step ground-session $CS test -p axeyum-solver --features full --lib ground_session
step schedule $CS test -p axeyum-solver --features full --lib schedule
step fmt cargo fmt --all --check
echo "ALL-STEPS-DONE" >> "$LOG"
