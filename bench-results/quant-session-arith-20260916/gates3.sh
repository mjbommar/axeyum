#!/usr/bin/env bash
# QUANT-SESSION-ARITH (ADR-2130) -- the suites that predate the helper
# extraction, then the mutations, then the z3 differentials.
#
#   gates3.sh <logfile>
#
# Re-run rather than inherited: `new_with_limits` was split into
# `append_session_lia_atoms` and `within_online_quantifier_limits` after the
# first battery ran, and "the earlier run was green" is a claim about earlier
# code. A ZERO test count on a z3 suite is an INERT gate, not a pass.
set -u
LOG="${1:-/tmp/qsa-gates3.log}"
cd "$(dirname "$0")/../.." || exit 2
: > "$LOG"

step() {
  local label="$1"; shift
  echo "=== STEP $label ===" >> "$LOG"
  "$@" >> "$LOG" 2>&1
  echo "=== RC $label = $? ===" >> "$LOG"
}

CS=scripts/cargo-serialized.sh

step check-default $CS check --workspace --all-targets
step config-registry $CS test -p axeyum-solver --features full --lib config_registry::
for suite in quantified_route_trace quantifier_positive_path \
             quantifier_trigger_alternatives quant_ground_session_soundness; do
  step "$suite" $CS test -p axeyum-solver --features full --test "$suite"
done
step mutation-session-arith python3 scripts/tests/mutation_controls.py qinst-session-arith
step mutation-certificate python3 scripts/tests/mutation_controls.py qinst-refuted-certificate
for suite in qf_uflra_differential_fuzz qf_lia_differential_fuzz qf_lra_differential_fuzz; do
  step "z3:$suite" $CS test -p axeyum-solver --features z3 --test "$suite"
done
echo "ALL-STEPS-DONE" >> "$LOG"
