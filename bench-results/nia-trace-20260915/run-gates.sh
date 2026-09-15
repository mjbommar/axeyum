#!/usr/bin/env bash
# ADR-2112's remaining pre-merge gates, run detached so a harness timeout does
# not report a killed wrapper as a finished gate (lane NIA-TRACE).
#
# Each step prints its own NAME and its own test COUNT, because a
# feature-gated suite compiles to nothing and exits 0 -- a green gate that
# checked nothing. A step with a zero count is reported as such rather than
# folded into an overall pass.
set -uo pipefail
cd -- "$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)" || exit 2

step() {
    local name=$1; shift
    echo "=== STEP $name ==="
    scripts/cargo-serialized.sh "$@" 2>&1 | grep -E "^test result:|^error|panicked|FAILED" | head -20
    echo "=== END $name ==="
}

case "${1:-all}" in
  lib)
    step lib-sweep test -p axeyum-solver --lib --features full
    ;;
  dispatch)
    for suite in route_trace route_attribution decline_detail_typed \
                 dispatch_rung_refusal_declines quant_ladder_rung_refusal_declines \
                 quantified_route_trace lazy_bv_dispatch nra_fbbt_route ufnra_route \
                 cas_ideal_route cas_bridge_routes int_pow2_evidence_decline \
                 math_resource_bv_routes math_resource_lia_routes \
                 math_resource_lra_routes math_resource_uf_routes \
                 decision_and_evidence_routes_agree dispatch_interpolant_certified \
                 string_route_parity word_equation_route; do
        step "$suite" test -p axeyum-solver --features full --test "$suite"
    done
    ;;
  frontier)
    step progress-frontier test -p axeyum-solver --test progress_frontier \
        --features full -- --test-threads=1
    ;;
  *)
    echo "usage: run-gates.sh {lib|dispatch|frontier}"; exit 2;;
esac
echo "GATES-SCRIPT-DONE"
