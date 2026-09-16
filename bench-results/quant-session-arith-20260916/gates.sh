#!/usr/bin/env bash
# QUANT-SESSION-ARITH (ADR-2130) -- this lane's gate battery, in one pass.
#
#   gates.sh <logfile>
#
# Batched deliberately: `cargo-serialized.sh` takes a host-wide flock, so eight
# separate invocations queue eight times behind every other lane on the box.
#
# EVERY STEP PRINTS ITS OWN TEST COUNT. A feature-gated suite compiles to
# nothing and exits 0, so an exit status alone is not evidence that anything
# ran. The summary at the end reports each step's status AND its count.
set -u
LOG="${1:-/tmp/qsa-gates.log}"
cd "$(dirname "$0")/../.." || exit 2
: > "$LOG"

step() {  # $1 = label, rest = command
  local label="$1"; shift
  echo "=== STEP $label ===" >> "$LOG"
  "$@" >> "$LOG" 2>&1
  local rc=$?
  echo "=== RC $label = $rc ===" >> "$LOG"
}

CS=scripts/cargo-serialized.sh

step fmt cargo fmt --all --check
step cert $CS test -p axeyum-solver --features full --test quant_session_arith_certificate
step session-theory $CS test -p axeyum-solver --features full --lib qinst_session_theory
step ground-session $CS test -p axeyum-solver --features full --lib ground_session
step schedule $CS test -p axeyum-solver --features full --lib ground_check_schedule
step config-registry $CS test -p axeyum-solver --features full --lib config_registry::
step quant-route-trace $CS test -p axeyum-solver --features full --test quantified_route_trace
step quant-positive $CS test -p axeyum-solver --features full --test quantifier_positive_path
step quant-triggers $CS test -p axeyum-solver --features full --test quantifier_trigger_alternatives
step quant-ground-soundness $CS test -p axeyum-solver --features full --test quant_ground_session_soundness
step check-default $CS check --workspace --all-targets
step clippy-workspace $CS clippy --workspace --all-targets --all-features -- -D warnings

echo "ALL-STEPS-DONE" >> "$LOG"

echo
echo "== SUMMARY =="
awk '
  /^=== STEP /   { label=$3 }
  /^test result:/ { counts[label] = counts[label] $0 " " }
  /^=== RC /     { rc[$3]=$5; order[++n]=$3 }
  END {
    for (i=1; i<=n; i++) {
      l=order[i]
      printf "%-24s rc=%-3s %s\n", l, rc[l], (counts[l] ? counts[l] : "(no test-result line)")
    }
  }
' "$LOG"
