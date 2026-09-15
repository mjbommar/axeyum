#!/usr/bin/env bash
# UFLIA-TRACE -- the pre-merge gates this lane's diff requires, by name.
#
#   run-gates.sh [target-dir]
#
# Every suite prints its own test count and this script REFUSES a zero: a
# feature-gated suite compiles to nothing and exits 0, which is a green-looking
# gate that checks nothing. The 20 dispatch suites are the list `hooks/pre-push`
# runs, copied by name rather than by a pattern, because a pattern that stops
# matching reports a shrinking list as a passing one.
set -u
cd "$(dirname "$0")/../.."
export CARGO_TARGET_DIR="${1:-/data0/axeyum/uflia-trace-target-base}"

fail=0
run() {  # $1 = label, rest = cargo args
  local label="$1"; shift
  local out rc
  out=$("$@" 2>&1)
  rc=$?
  local counts
  counts=$(printf '%s\n' "$out" | grep -oE 'test result: (ok|FAILED)\. [0-9]+ passed; [0-9]+ failed' || true)
  if [ -z "$counts" ]; then
    echo "GATE $label: NO 'test result:' LINE (rc=$rc) -- an absent result line is"
    echo "  an OOM or a build failure, not a pass"
    fail=1
    return
  fi
  local passed failed
  passed=$(printf '%s\n' "$counts" | grep -oE '[0-9]+ passed' | grep -oE '[0-9]+' | paste -sd+ | bc)
  failed=$(printf '%s\n' "$counts" | grep -oE '[0-9]+ failed' | grep -oE '[0-9]+' | paste -sd+ | bc)
  if [ "$rc" != 0 ] || [ "${failed:-1}" != 0 ]; then
    echo "GATE $label: FAILED (rc=$rc, passed=$passed, failed=$failed)"
    printf '%s\n' "$out" | grep -E '^(test .* FAILED|error)' | head -5
    fail=1
  elif [ "${passed:-0}" = 0 ]; then
    echo "GATE $label: ZERO TESTS RAN -- exits 0 and checks nothing"
    fail=1
  else
    echo "GATE $label: ok, $passed passed"
  fi
}

run "config_registry" cargo test -p axeyum-solver --lib --features full config_registry::tests
run "qinst_egraph unit" cargo test -p axeyum-solver --lib --features full qinst_egraph::tests
run "trigger-alternatives integration" \
  cargo test -p axeyum-solver --features full --test quantifier_trigger_alternatives

for suite in unknown_reason_coverage dt_uf_gate dt_capability_1935 \
             dt_constructor_arg_1942 dt_valued_result_1946 \
             datatype_solve_path quant_ladder_rung_refusal_declines \
             nested_array_gate_map nested_array_row real_element_array_row \
             dispatch_rung_refusal_declines quant_egraph_reserve_row \
             quant_valid_universal_reserve_row qinst_egraph_retry_share_row \
             distinct_linear_soundness parser_desugar_soundness \
             replay_pairing_soundness \
             additive_no_overflow_never_becomes_unsat \
             lra_opaque_real_apps decline_detail_typed; do
  run "dispatch/$suite" cargo test -p axeyum-solver --features full --test "$suite"
done

echo
[ "$fail" = 0 ] && echo "UFLIA-TRACE GATES: PASS" || echo "UFLIA-TRACE GATES: FAIL"
exit "$fail"
