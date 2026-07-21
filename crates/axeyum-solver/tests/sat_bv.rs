//! Conformance tests for the pure Rust SAT-backed BV backend.
//!
//! These tests exercise the Phase 5 composition path: query terms lower to
//! AIG/CNF, solve through the pure Rust `BatSat` adapter, lift a model, and
//! replay the original formula before returning `sat`.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_query::Query;
use axeyum_solver::{
    BitLoweringMode, BvLayerStats, CheckResult, RangeDemandDecision, RangeDemandPolicy,
    SatBvBackend, SolverBackend, SolverConfig, UnknownKind,
};

fn check(arena: &TermArena, assertions: &[TermId]) -> CheckResult {
    SatBvBackend::new()
        .check(arena, assertions, &SolverConfig::default())
        .expect("pure Rust backend invocation succeeds")
}

fn expect_sat_checked(arena: &TermArena, assertions: &[TermId]) -> axeyum_solver::Model {
    let CheckResult::Sat(model) = check(arena, assertions) else {
        panic!("expected sat");
    };
    let assignment = model.to_assignment();
    for &term in assertions {
        assert_eq!(
            eval(arena, term, &assignment).unwrap(),
            Value::Bool(true),
            "model must satisfy every original assertion"
        );
    }
    model
}

#[test]
fn supported_bv_formula_solves_and_replays() {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(4)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(4)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let two = arena.bv_const(4, 2).unwrap();
    let five = arena.bv_const(4, 5).unwrap();
    let x_is_two = arena.eq(x, two).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let sum_is_five = arena.eq(sum, five).unwrap();

    let model = expect_sat_checked(&arena, &[x_is_two, sum_is_five]);
    assert_eq!(model.get(x_sym), Some(Value::Bv { width: 4, value: 2 }));
    assert_eq!(model.get(y_sym), Some(Value::Bv { width: 4, value: 3 }));
}

#[test]
fn deterministic_sat_resource_limit_is_classified_unknown() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let target = arena.bv_const(8, 0xa5).unwrap();
    let assertion = arena.eq(x, target).unwrap();
    let config = SolverConfig::default().with_resource_limit(0);

    assert!(matches!(
        SatBvBackend::new()
            .check(&arena, &[assertion], &config)
            .unwrap(),
        CheckResult::Unknown(reason)
            if reason.kind == UnknownKind::ResourceLimit
                && reason.detail.contains("progress-check budget 0 exhausted")
    ));
}

#[test]
fn unsat_is_drat_proof_checked_when_requested() {
    // `x != x` is unsatisfiable; with `prove_unsat`, the backend now uses the
    // native proof-producing core as the primary engine and verifies its INLINE
    // DRAT proof in a single solve — no separate re-derivation. The accepted
    // `unsat` is backed by a checked proof by construction.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let eq_self = arena.eq(x, x).unwrap();
    let contradiction = arena.not(eq_self).unwrap();
    let config = SolverConfig {
        prove_unsat: true,
        ..SolverConfig::default()
    };

    let mut backend = SatBvBackend::new();
    assert_eq!(
        backend.check(&arena, &[contradiction], &config).unwrap(),
        CheckResult::Unsat
    );
    let stats = backend.last_stats().expect("stats recorded");
    let inline = stats.backend.iter().any(|(name, value)| {
        name == "unsat_proof_checked_inline" && (*value - 1.0).abs() < f64::EPSILON
    });
    assert!(
        inline,
        "unsat should be recorded as inline-DRAT-proof-checked (one solve), \
         got stats: {:?}",
        stats.backend
    );
    // The single-solve inline path must NOT trigger the separate re-derivation.
    let rederived = stats
        .backend
        .iter()
        .any(|(name, _)| name == "unsat_proof_checked");
    assert!(
        !rederived,
        "the native inline path must not re-derive the proof via verify_unsat_proof; \
         got stats: {:?}",
        stats.backend
    );
}

#[test]
fn prove_unsat_native_inline_proof_matches_batsat_verdict() {
    // DISAGREE=0 sanity: a small BV corpus must reach the same sat/unsat verdict
    // whether prove_unsat (native inline-proof engine) or the default batsat
    // engine is used. The native unsat additionally carries a checked proof.
    fn build(arena: &mut TermArena, idx: usize) -> (TermId, bool) {
        let x = arena.bv_var(&format!("x{idx}"), 4).unwrap();
        let y = arena.bv_var(&format!("y{idx}"), 4).unwrap();
        match idx {
            // unsat: x < 0 (unsigned) is never satisfiable.
            0 => {
                let zero = arena.bv_const(4, 0).unwrap();
                (arena.bv_ult(x, zero).unwrap(), false)
            }
            // unsat: x != x.
            1 => {
                let e = arena.eq(x, x).unwrap();
                (arena.not(e).unwrap(), false)
            }
            // unsat: x = 1 AND x = 2.
            2 => {
                let one = arena.bv_const(4, 1).unwrap();
                let two = arena.bv_const(4, 2).unwrap();
                let a = arena.eq(x, one).unwrap();
                let b = arena.eq(x, two).unwrap();
                (arena.and(a, b).unwrap(), false)
            }
            // sat: x + y = 5.
            3 => {
                let five = arena.bv_const(4, 5).unwrap();
                let sum = arena.bv_add(x, y).unwrap();
                (arena.eq(sum, five).unwrap(), true)
            }
            // sat: x = 3.
            _ => {
                let three = arena.bv_const(4, 3).unwrap();
                (arena.eq(x, three).unwrap(), true)
            }
        }
    }

    for idx in 0..5usize {
        let mut arena = TermArena::new();
        let (term, expected_sat) = build(&mut arena, idx);

        let prove_cfg = SolverConfig {
            prove_unsat: true,
            ..SolverConfig::default()
        };
        let native = SatBvBackend::new()
            .check(&arena, &[term], &prove_cfg)
            .unwrap();
        let batsat = SatBvBackend::new()
            .check(&arena, &[term], &SolverConfig::default())
            .unwrap();

        if expected_sat {
            assert!(
                matches!(native, CheckResult::Sat(_)),
                "case {idx}: prove_unsat (native) should be sat, got {native:?}"
            );
            assert!(
                matches!(batsat, CheckResult::Sat(_)),
                "case {idx}: batsat should be sat, got {batsat:?}"
            );
        } else {
            assert_eq!(native, CheckResult::Unsat, "case {idx}: native verdict");
            assert_eq!(batsat, CheckResult::Unsat, "case {idx}: batsat verdict");
        }
    }
}

#[test]
fn prove_unsat_sat_query_returns_sat_via_native() {
    // Auto-enabling native for prove_unsat must not break SAT prove_unsat
    // queries: a satisfiable formula simply returns Sat (no proof needed), with
    // a model that checks against the original terms.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(4)).unwrap();
    let x = arena.var(x_sym);
    let three = arena.bv_const(4, 3).unwrap();
    let x_is_three = arena.eq(x, three).unwrap();
    let config = SolverConfig {
        prove_unsat: true,
        ..SolverConfig::default()
    };

    let CheckResult::Sat(model) = SatBvBackend::new()
        .check(&arena, &[x_is_three], &config)
        .unwrap()
    else {
        panic!("prove_unsat over a satisfiable formula should return Sat");
    };
    assert_eq!(model.get(x_sym), Some(Value::Bv { width: 4, value: 3 }));
}

#[test]
fn supported_bv_contradiction_is_unsat() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let x_below_zero = arena.bv_ult(x, zero).unwrap();

    assert_eq!(check(&arena, &[x_below_zero]), CheckResult::Unsat);
}

#[test]
fn query_assertions_and_assumptions_solve_through_same_backend() {
    let mut arena = TermArena::new();
    let p_sym = arena.declare("p", Sort::Bool).unwrap();
    let q_sym = arena.declare("q", Sort::Bool).unwrap();
    let p = arena.var(p_sym);
    let q = arena.var(q_sym);
    let mut builder = Query::builder(&arena);
    builder.assert(p).unwrap();
    builder.assume(q).unwrap();
    let query = builder.build();

    let CheckResult::Sat(model) = SatBvBackend::new()
        .check_query(&arena, &query, &SolverConfig::default())
        .unwrap()
    else {
        panic!("expected sat");
    };
    assert_eq!(model.get(p_sym), Some(Value::Bool(true)));
    assert_eq!(model.get(q_sym), Some(Value::Bool(true)));
}

#[test]
fn model_completion_assigns_unconstrained_symbols() {
    let mut arena = TermArena::new();
    let used_sym = arena.declare("used", Sort::BitVec(8)).unwrap();
    let unused_sym = arena.declare("unused", Sort::BitVec(16)).unwrap();
    let used = arena.var(used_sym);
    let three = arena.bv_const(8, 3).unwrap();
    let used_is_three = arena.eq(used, three).unwrap();

    let model = expect_sat_checked(&arena, &[used_is_three]);
    assert_eq!(model.get(used_sym), Some(Value::Bv { width: 8, value: 3 }));
    assert_eq!(
        model.get(unused_sym),
        Some(Value::Bv {
            width: 16,
            value: 0
        })
    );
}

#[test]
fn full_scalar_qf_bv_operator_set_is_supported() {
    // The whole scalar QF_BV operator set now lowers, including multiplication
    // and signed/unsigned division and remainder. A formula mixing them must
    // produce a decision, never a `SolverError::Unsupported` (there is no silent
    // oracle fallback; the unsupported path is reserved for future non-scalar
    // constructs such as arrays).
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let y = arena.bv_var("y", 4).unwrap();
    let product = arena.bv_mul(x, y).unwrap();
    let udiv = arena.bv_udiv(product, y).unwrap();
    let urem = arena.bv_urem(product, y).unwrap();
    let sdiv = arena.bv_sdiv(x, y).unwrap();
    let srem = arena.bv_srem(x, y).unwrap();
    let smod = arena.bv_smod(x, y).unwrap();
    let c1 = arena.eq(udiv, x).unwrap();
    let c2 = arena.bv_ule(urem, y).unwrap();
    let c3 = arena.bv_sle(sdiv, srem).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let c4 = arena.bv_sge(smod, zero).unwrap();

    let result = SatBvBackend::new()
        .check(&arena, &[c1, c2, c3, c4], &SolverConfig::default())
        .expect("supported operators never error");
    assert!(
        matches!(result, CheckResult::Sat(_) | CheckResult::Unsat),
        "expected a decision for the full operator set, got {result:?}"
    );
}

#[test]
fn node_budget_refuses_before_lowering() {
    let mut arena = TermArena::new();
    let mut term = arena.bv_var("x", 8).unwrap();
    for _ in 0..10 {
        term = arena.bv_add(term, term).unwrap();
    }
    let zero = arena.bv_const(8, 0).unwrap();
    let formula = arena.eq(term, zero).unwrap();
    let config = SolverConfig {
        node_budget: Some(4),
        ..SolverConfig::default()
    };

    let result = SatBvBackend::new()
        .check(&arena, &[formula], &config)
        .unwrap();
    let CheckResult::Unknown(reason) = result else {
        panic!("expected node-budget unknown, got {result:?}");
    };
    assert_eq!(reason.kind, UnknownKind::NodeBudget);
}

#[test]
fn timeout_is_classified_unknown_before_sat_solve() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let formula = arena.eq(x, one).unwrap();
    let config = SolverConfig {
        timeout: Some(Duration::ZERO),
        ..SolverConfig::default()
    };

    let result = SatBvBackend::new()
        .check(&arena, &[formula], &config)
        .unwrap();
    let CheckResult::Unknown(reason) = result else {
        panic!("expected timeout unknown, got {result:?}");
    };
    assert_eq!(reason.kind, UnknownKind::Timeout);
}

#[test]
fn cnf_budget_refuses_before_sat_solve() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let formula = arena.eq(x, one).unwrap();
    let config = SolverConfig {
        cnf_clause_budget: Some(1),
        ..SolverConfig::default()
    };

    let result = SatBvBackend::new()
        .check(&arena, &[formula], &config)
        .unwrap();
    let CheckResult::Unknown(reason) = result else {
        panic!("expected encoding-budget unknown, got {result:?}");
    };
    assert_eq!(reason.kind, UnknownKind::EncodingBudget);
    // The clause budget is now enforced *before lowering* via the pre-lowering
    // size estimate (graceful oversized refusal), so the refusal reports the
    // estimated clause count rather than the post-encoding "CNF has N clauses".
    // Either way it is an EncodingBudget refusal that mentions clauses.
    assert!(
        reason.detail.contains("clauses"),
        "expected a clause-budget refusal mentioning clauses, got: {}",
        reason.detail
    );
}

#[test]
fn stats_report_phase5_layer_counts() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let sum = arena.bv_add(x, one).unwrap();
    let formula = arena.eq(sum, two).unwrap();
    let mut backend = SatBvBackend::new();

    let result = backend
        .check(&arena, &[formula], &SolverConfig::default())
        .unwrap();
    assert!(matches!(result, CheckResult::Sat(_)));
    let stats = backend.last_stats().expect("stats recorded");
    assert_eq!(stats.assertion_count, 1);
    assert!(stats.terms_translated >= 5);
    assert!(stats.translate.as_nanos() > 0);
    assert!(stats.solve.as_nanos() > 0);
    assert!(stats.model_lift.as_nanos() > 0);
    for key in [
        "bit_blast_ms",
        "cnf_encode_ms",
        "aig_nodes",
        "aig_inputs",
        "aig_and_requests",
        "aig_and_trivial_simplifications",
        "aig_and_absorption_simplifications",
        "aig_and_structural_hash_hits",
        "aig_and_nodes_created",
        "bit_demand_profile_complete",
        "bit_demand_lowering_applied",
        "range_demand_decision",
        "range_demand_admission_ms",
        "range_demand_estimated_bits_avoided",
        "range_demand_analysis_work_budget",
        "range_demand_analysis_work",
        "range_demand_merges",
        "range_demand_promotions",
        "bit_demand_analysis_ms",
        "term_bit_requests",
        "term_bits_available",
        "term_bits_demanded",
        "term_bits_lowered",
        "symbol_bit_requests",
        "symbol_bits_available",
        "symbol_bits_demanded",
        "symbol_bits_lowered",
        "bit_lowering_memo_profile_complete",
        "bit_lowering_memo_representation",
        "bit_lowering_memo_source_terms",
        "bit_lowering_memo_slots",
        "bit_lowering_memo_occupied",
        "bit_lowering_memo_lookups",
        "bit_lowering_memo_hits",
        "bit_lowering_memo_writes",
        "bit_lowering_memo_payload_literals",
        "bit_lowering_memo_payload_capacity_literals",
        "bit_lowering_memo_logical_header_bytes",
        "bit_lowering_memo_logical_payload_bytes",
        "bit_lowering_memo_logical_total_bytes",
        "bit_lowering_memo_payload_capacity_bytes",
        "bit_lowering_memo_root_bits",
        "bit_lowering_memo_expected_root_bits",
        "bit_lowering_memo_invariants_hold",
        "cnf_variables",
        "cnf_clauses",
        "cnf_plan_ms",
        "cnf_allocate_ms",
        "cnf_gate_encode_ms",
        "cnf_root_encode_ms",
        "cnf_reachable_nodes",
        "cnf_skipped_helper_nodes",
        "cnf_direct_root_nodes",
        "cnf_clause_attempts",
        "cnf_clauses_emitted",
    ] {
        assert!(
            stats.backend.iter().any(|(name, _)| name == key),
            "missing backend stat {key}"
        );
    }
    let layers = BvLayerStats::from_solve_stats(stats).expect("typed layer stats");
    assert!(!layers.bit_demand_profile_complete);
    assert!(!layers.bit_demand_lowering_applied);
    assert!(!layers.bit_lowering_memo_profile_complete);
    assert_eq!(
        layers.bit_lowering_memo_representation,
        axeyum_solver::BitLoweringMemoRepresentation::Unavailable
    );
    assert_eq!(layers.bit_lowering_structure_digest, 0);
    assert_eq!(layers.cnf_structure_digest, 0);
    assert_eq!(
        layers.range_demand_decision,
        RangeDemandDecision::NotRequested
    );
    assert_eq!(layers.bit_demand_analysis, Duration::ZERO);
    assert!(layers.term_bits_lowered > 0);
}

#[test]
fn structural_bit_demand_profile_is_explicitly_opt_in() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 64).unwrap();
    let low = arena.extract(7, 0, x).unwrap();
    let value = arena.bv_const(8, 0x5a).unwrap();
    let formula = arena.eq(low, value).unwrap();
    let config = SolverConfig::default().with_bit_demand_profile(true);
    let mut backend = SatBvBackend::new();

    let result = backend.check(&arena, &[formula], &config).unwrap();
    assert!(matches!(result, CheckResult::Sat(_)));
    let stats = backend.last_stats().expect("stats recorded");
    let layers = BvLayerStats::from_solve_stats(stats).expect("typed layer stats");
    assert!(layers.bit_demand_profile_complete);
    assert!(!layers.bit_demand_lowering_applied);
    assert_eq!(layers.term_bits_demanded, 25);
    assert_eq!(layers.term_bits_lowered, 81);
    assert_eq!(layers.symbol_bits_demanded, 8);
    assert_eq!(layers.symbol_bits_lowered, 64);
    assert!(layers.bit_lowering_memo_profile_complete);
    for key in [
        "bit_lowering_structure_digest_hi",
        "bit_lowering_structure_digest_lo",
        "cnf_structure_digest_hi",
        "cnf_structure_digest_lo",
    ] {
        assert!(
            stats.backend.iter().any(|(name, _)| name == key),
            "missing profiled structure digest {key}"
        );
    }
    assert_eq!(
        layers.bit_lowering_memo_representation,
        axeyum_solver::BitLoweringMemoRepresentation::BtreeV1
    );
    assert_eq!(
        layers.bit_lowering_memo_payload_literals,
        layers.term_bits_lowered
    );
    assert!(layers.bit_lowering_memo_invariants_hold);
    assert_eq!(
        layers.bit_lowering_memo_root_bits,
        layers.bit_lowering_memo_expected_root_bits
    );
    assert_ne!(layers.bit_lowering_structure_digest, 0);
    assert_ne!(layers.cnf_structure_digest, 0);
}

#[test]
fn demand_driven_lowering_is_opt_in_replay_checked_and_decides_both_verdicts() {
    let mut arena = TermArena::new();
    let x_symbol = arena.declare("x", Sort::BitVec(64)).unwrap();
    let x = arena.var(x_symbol);
    let low = arena.extract(7, 0, x).unwrap();
    let value = arena.bv_const(8, 0x5a).unwrap();
    let equal = arena.eq(low, value).unwrap();
    let config = SolverConfig::default()
        .with_bit_demand_profile(true)
        .with_demand_bit_slicing(true);
    let mut backend = SatBvBackend::new();

    let CheckResult::Sat(model) = backend.check(&arena, &[equal], &config).unwrap() else {
        panic!("expected demand-lowered formula to be sat");
    };
    assert_eq!(
        eval(&arena, equal, &model.to_assignment()).unwrap(),
        Value::Bool(true),
        "the sparse lifted model must replay against the original assertion"
    );
    assert_eq!(
        model.get(x_symbol),
        Some(Value::Bv {
            width: 64,
            value: 0x5a,
        }),
        "omitted high symbol bits are deterministically zero-completed"
    );
    let layers = BvLayerStats::from_solve_stats(backend.last_stats().unwrap()).unwrap();
    assert!(layers.bit_demand_profile_complete);
    assert!(layers.bit_demand_lowering_applied);
    assert_eq!(layers.term_bits_demanded, 25);
    assert_eq!(layers.term_bits_lowered, 25);
    assert_eq!(layers.symbol_bits_demanded, 8);
    assert_eq!(layers.symbol_bits_lowered, 8);

    let other = arena.bv_const(8, 0xa5).unwrap();
    let unequal_constraint = arena.eq(low, other).unwrap();
    assert!(matches!(
        backend
            .check(&arena, &[equal, unequal_constraint], &config)
            .unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn admission_controlled_range_demand_reports_policy_and_fallback() {
    let mut arena = TermArena::new();
    let x_symbol = arena.declare("x", Sort::BitVec(64)).unwrap();
    let x = arena.var(x_symbol);
    let low = arena.extract(7, 0, x).unwrap();
    let value = arena.bv_const(8, 0x5a).unwrap();
    let equal = arena.eq(low, value).unwrap();
    let policy = RangeDemandPolicy {
        min_term_bits_available: 64,
        min_estimated_bits_avoided: 32,
        min_estimated_avoided_percent: 50,
        min_exact_bits_avoided: 32,
        min_exact_avoided_percent: 50,
        analysis_work_budget: 1_000,
    };
    let config = SolverConfig::default().with_range_demand_slicing(policy);
    let mut backend = SatBvBackend::new();

    let CheckResult::Sat(model) = backend.check(&arena, &[equal], &config).unwrap() else {
        panic!("expected range-demanded formula to be sat");
    };
    assert_eq!(
        eval(&arena, equal, &model.to_assignment()).unwrap(),
        Value::Bool(true)
    );
    let layers = BvLayerStats::from_solve_stats(backend.last_stats().unwrap()).unwrap();
    assert_eq!(layers.range_demand_decision, RangeDemandDecision::Applied);
    assert!(layers.bit_demand_lowering_applied);
    assert_eq!(layers.range_demand_estimated_bits_avoided, 56);
    assert!(layers.range_demand_analysis_work <= layers.range_demand_analysis_work_budget);
    assert_eq!(layers.term_bits_lowered, 25);
    assert_eq!(layers.symbol_bits_lowered, 8);

    let no_slice = arena.eq(x, x).unwrap();
    assert!(matches!(
        backend.check(&arena, &[no_slice], &config).unwrap(),
        CheckResult::Sat(_)
    ));
    let fallback = BvLayerStats::from_solve_stats(backend.last_stats().unwrap()).unwrap();
    assert_eq!(
        fallback.range_demand_decision,
        RangeDemandDecision::NoCandidate
    );
    assert!(!fallback.bit_demand_lowering_applied);
    assert_eq!(fallback.term_bits_lowered, fallback.term_bits_available);
}

#[test]
fn demand_lowering_mode_is_one_typed_choice() {
    let policy = RangeDemandPolicy::default();
    let eager = SolverConfig::default();
    assert_eq!(eager.bit_lowering_mode, BitLoweringMode::Eager);
    assert!(!eager.demand_bit_slicing());
    assert_eq!(eager.range_demand_slicing(), None);

    let dense = eager.clone().with_demand_bit_slicing(true);
    assert_eq!(dense.bit_lowering_mode, BitLoweringMode::DemandSliced);
    assert!(dense.demand_bit_slicing());
    assert_eq!(dense.range_demand_slicing(), None);

    let range = dense.with_range_demand_slicing(policy);
    assert_eq!(
        range.bit_lowering_mode,
        BitLoweringMode::RangeSliced(policy)
    );
    assert!(!range.demand_bit_slicing());
    assert_eq!(range.range_demand_slicing(), Some(policy));

    let dense_again = range.with_demand_bit_slicing(true);
    assert_eq!(dense_again.bit_lowering_mode, BitLoweringMode::DemandSliced);

    let eager_again = dense_again
        .with_demand_bit_slicing(false)
        .with_bit_lowering_mode(BitLoweringMode::Eager);
    assert_eq!(eager_again.bit_lowering_mode, BitLoweringMode::Eager);
}

#[cfg(feature = "z3")]
#[test]
fn supported_subset_decisions_match_z3_oracle() {
    use axeyum_solver::Z3Backend;

    fn outcome_tag(result: &CheckResult) -> &'static str {
        match result {
            CheckResult::Sat(_) => "sat",
            CheckResult::Unsat => "unsat",
            CheckResult::Unknown(_) => "unknown",
        }
    }

    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 4).unwrap();
    let y = arena.bv_var("y", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let seven = arena.bv_const(4, 7).unwrap();
    let shifted = arena.bv_shl(x, one).unwrap();
    let sum = arena.bv_add(shifted, y).unwrap();
    let sat_formula = arena.eq(sum, seven).unwrap();
    let zero = arena.bv_const(4, 0).unwrap();
    let unsat_formula = arena.bv_ult(x, zero).unwrap();

    for assertions in [vec![sat_formula], vec![unsat_formula]] {
        let pure = SatBvBackend::new()
            .check(&arena, &assertions, &SolverConfig::default())
            .unwrap();
        let z3 = Z3Backend::new()
            .check(&arena, &assertions, &SolverConfig::default())
            .unwrap();
        assert_eq!(outcome_tag(&pure), outcome_tag(&z3));
    }
}

#[test]
fn wide_bit_vector_solves_and_replays() {
    // A 200-bit bit-vector exceeds the old u128 ceiling; with wide-BV it solves
    // and the model (a WideBv) replays through the evaluator. x + 1 = 5 => x = 4.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(200)).unwrap();
    let xv = arena.var(x);
    let one = arena.bv_const(200, 1).unwrap();
    let sum = arena.bv_add(xv, one).unwrap();
    let five = arena.bv_const(200, 5).unwrap();
    let eq = arena.eq(sum, five).unwrap();
    let model = expect_sat_checked(&arena, &[eq]);
    // The lifted value is a wide bit-vector equal to 4.
    let want = axeyum_ir::WideUint::from_u128(4, 200);
    assert_eq!(model.get(x), Some(Value::WideBv(want)));
}

#[test]
fn wide_bit_vector_variable_shift_solves_and_replays() {
    // A variable left-shift at 200 bits exercises the wide shift-lowering path,
    // whose in-range `width_constant` is a >128-bit constant (regression: that
    // constant's lowering shifted a u128 past bit 127 and panicked). Find s with
    // (1 << s) == 2^150; s = 150 works, and the model replays.
    let mut arena = TermArena::new();
    let s = arena.declare("s", Sort::BitVec(200)).unwrap();
    let sv = arena.var(s);
    let one = arena.bv_const(200, 1).unwrap();
    let shifted = arena.bv_shl(one, sv).unwrap();
    // 2^150 as a wide constant: 1 shifted left 150 from a u128 base is too wide
    // for bv_const(value:u128); build it as (one << 150) over wide constants.
    let onefifty = arena.bv_const(200, 150).unwrap();
    let target = arena.bv_shl(one, onefifty).unwrap();
    let eq = arena.eq(shifted, target).unwrap();
    let model = expect_sat_checked(&arena, &[eq]);
    assert_eq!(
        model.get(s),
        Some(Value::WideBv(axeyum_ir::WideUint::from_u128(150, 200)))
    );
}

fn outcome_tag(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

#[test]
fn cnf_inprocessing_agrees_with_baseline_and_replays() {
    // For both a SAT and an UNSAT instance, inprocessing (subsumption + BVE)
    // must reach the same decision as the un-inprocessed encoding, and a `sat`
    // model reconstructed through the BVE stack must still satisfy the original
    // terms (the backend replays it before returning, so a bad reconstruction
    // would surface as a `Backend` error, not a wrong `sat`).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y_sym = arena.declare("y", Sort::BitVec(8)).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let seven = arena.bv_const(8, 7).unwrap();
    let x_is_seven = arena.eq(x, seven).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let sum_is_ten = arena.eq(sum, ten).unwrap();
    let sat_case = vec![x_is_seven, sum_is_ten];

    // x*y = 0 with x = 3 and y odd is contradictory at 8 bits (3 is invertible).
    let product = arena.bv_mul(x, y).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let prod_zero = arena.eq(product, zero).unwrap();
    let three = arena.bv_const(8, 3).unwrap();
    let x_is_three = arena.eq(x, three).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let y_odd_bit = arena.bv_and(y, one).unwrap();
    let y_is_odd = arena.eq(y_odd_bit, one).unwrap();
    let unsat_case = vec![prod_zero, x_is_three, y_is_odd];

    for assertions in [sat_case, unsat_case] {
        let baseline = SatBvBackend::new()
            .check(&arena, &assertions, &SolverConfig::default())
            .unwrap();
        // Two inprocessing arms: subsumption+BVE only, and the same plus vivify.
        // Both are model-preserving / equisatisfiable, so both must match the
        // baseline verdict, and any `sat` model must replay against the originals.
        let inprocess_only = SolverConfig::default().with_cnf_inprocessing(true);
        let inprocess_plus_vivify = SolverConfig::default()
            .with_cnf_inprocessing(true)
            .with_cnf_vivify(true);
        for config in [inprocess_only, inprocess_plus_vivify] {
            let inprocessed = SatBvBackend::new()
                .check(&arena, &assertions, &config)
                .unwrap();
            assert_eq!(
                outcome_tag(&baseline),
                outcome_tag(&inprocessed),
                "inprocessing (vivify={}) changed the decision",
                config.cnf_vivify
            );
            if let CheckResult::Sat(model) = &inprocessed {
                let assignment = model.to_assignment();
                for &term in &assertions {
                    assert_eq!(
                        eval(&arena, term, &assignment).unwrap(),
                        Value::Bool(true),
                        "reconstructed model must satisfy every original assertion"
                    );
                }
            }
        }
    }
}

#[test]
fn cnf_inprocessing_records_stats_and_eliminates_variables() {
    // A formula dense with Tseitin gate variables: inprocessing should fire and
    // BVE should eliminate at least one variable, leaving an audit trail.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let prod = arena.bv_mul(sum, x).unwrap();
    let nine = arena.bv_const(8, 9).unwrap();
    let formula = arena.eq(prod, nine).unwrap();

    let mut backend = SatBvBackend::new();
    let result = backend
        .check(
            &arena,
            &[formula],
            &SolverConfig::default().with_cnf_inprocessing(true),
        )
        .unwrap();
    assert!(matches!(
        result,
        CheckResult::Sat(_) | CheckResult::Unsat | CheckResult::Unknown(_)
    ));
    let stats = backend.last_stats().expect("stats recorded");
    let stat = |key: &str| {
        stats
            .backend
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| *value)
    };
    assert_eq!(stat("cnf_inprocessing"), Some(1.0), "inprocessing must run");
    assert!(
        stat("bve_variables_eliminated").is_some_and(|v| v >= 1.0),
        "BVE should eliminate at least one Tseitin variable"
    );
    assert!(
        stat("cnf_clauses_solved").is_some(),
        "the reduced clause count must be recorded"
    );
}

#[test]
fn cnf_inprocessing_unsat_is_drat_proof_checked() {
    // Inprocessing + prove_unsat: the reduced (equisatisfiable) formula is solved
    // by the native proof-producing core, whose inline DRAT proof is verified in
    // a single solve. The reduced-formula unsat is still DRAT-checked (now via the
    // inline path rather than a separate re-derivation).
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 6).unwrap();
    let zero = arena.bv_const(6, 0).unwrap();
    let below_zero = arena.bv_ult(x, zero).unwrap();
    let config = SolverConfig::default()
        .with_cnf_inprocessing(true)
        .with_prove_unsat(true);

    let mut backend = SatBvBackend::new();
    assert_eq!(
        backend.check(&arena, &[below_zero], &config).unwrap(),
        CheckResult::Unsat
    );
    let stats = backend.last_stats().expect("stats recorded");
    assert!(
        stats
            .backend
            .iter()
            .any(|(name, value)| name == "unsat_proof_checked_inline"
                && (*value - 1.0).abs() < f64::EPSILON),
        "reduced-formula unsat should be DRAT-proof-checked inline (single solve), \
         got stats: {:?}",
        stats.backend
    );
}

#[test]
fn cnf_vivify_records_stats_when_enabled() {
    // With vivify enabled the `vivify_*` stat keys must appear in the backend
    // audit trail (alongside the existing subsume_*/bve_* keys). A formula dense
    // with Tseitin gates gives the pass clauses to strengthen.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let prod = arena.bv_mul(sum, x).unwrap();
    let nine = arena.bv_const(8, 9).unwrap();
    let formula = arena.eq(prod, nine).unwrap();

    let mut backend = SatBvBackend::new();
    let result = backend
        .check(
            &arena,
            &[formula],
            &SolverConfig::default()
                .with_cnf_inprocessing(true)
                .with_cnf_vivify(true),
        )
        .unwrap();
    assert!(matches!(
        result,
        CheckResult::Sat(_) | CheckResult::Unsat | CheckResult::Unknown(_)
    ));
    let stats = backend.last_stats().expect("stats recorded");
    let has = |key: &str| stats.backend.iter().any(|(name, _)| name == key);
    assert!(
        has("vivify_clauses_strengthened"),
        "vivify_clauses_strengthened must be recorded when vivify is on"
    );
    assert!(
        has("vivify_literals_removed"),
        "vivify_literals_removed must be recorded when vivify is on"
    );
    assert!(
        has("vivify_clauses_removed"),
        "vivify_clauses_removed must be recorded when vivify is on"
    );
}

#[test]
fn cnf_vivify_off_records_no_vivify_stats() {
    // Sanity: with vivify off (inprocessing on) the vivify_* keys are absent, so
    // the stats above are genuinely gated by the flag.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let prod = arena.bv_mul(sum, x).unwrap();
    let nine = arena.bv_const(8, 9).unwrap();
    let formula = arena.eq(prod, nine).unwrap();

    let mut backend = SatBvBackend::new();
    backend
        .check(
            &arena,
            &[formula],
            &SolverConfig::default().with_cnf_inprocessing(true),
        )
        .unwrap();
    let stats = backend.last_stats().expect("stats recorded");
    assert!(
        !stats
            .backend
            .iter()
            .any(|(name, _)| name.starts_with("vivify_")),
        "no vivify_* stats should appear when cnf_vivify is off"
    );
}

#[test]
fn cnf_vivify_prove_unsat_stays_green() {
    // Vivify is model-preserving, so enabling it with prove_unsat on a small UNSAT
    // instance must still return Unsat (the proof path stays green) and the
    // standalone vivify-DRAT step-guard must hold (recorded as 1.0 when fired).
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 6).unwrap();
    let zero = arena.bv_const(6, 0).unwrap();
    let below_zero = arena.bv_ult(x, zero).unwrap();
    let config = SolverConfig::default()
        .with_cnf_inprocessing(true)
        .with_cnf_vivify(true)
        .with_prove_unsat(true);

    let mut backend = SatBvBackend::new();
    assert_eq!(
        backend.check(&arena, &[below_zero], &config).unwrap(),
        CheckResult::Unsat
    );
    let stats = backend.last_stats().expect("stats recorded");
    // The step-guard either did not run (vivify produced no proof to check on this
    // tiny formula) or ran and passed; it must never have been recorded as failed.
    let step_checked = stats
        .backend
        .iter()
        .find(|(name, _)| name == "vivify_drat_step_checked")
        .map(|(_, value)| *value);
    assert!(
        step_checked.is_none_or(|v| (v - 1.0).abs() < f64::EPSILON),
        "vivify DRAT step-guard must hold when it fires, got {step_checked:?}"
    );
}

#[test]
fn cnf_compaction_lowers_variable_count_and_replays() {
    // Compaction (after BVE) densely renumbers the live CNF variables, so the
    // formula submitted to the SAT solver reports a strictly lower
    // `variable_count` than the un-compacted Tseitin encoding. This test asserts
    // BOTH halves of the soundness contract:
    //   1. the var-count actually drops (compaction_variables_after <= before,
    //      and below the un-inprocessed cnf_variables), and
    //   2. a `sat` model lifted through expand→extend still satisfies every
    //      original assertion (the backend replays it before returning `sat`, so
    //      a bad lift would surface as a backend error, never a wrong `sat`).
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let x_is_seven = arena.eq(x, seven).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let sum_is_ten = arena.eq(sum, ten).unwrap();
    let assertions = vec![x_is_seven, sum_is_ten];

    let mut backend = SatBvBackend::new();
    let result = backend
        .check(
            &arena,
            &assertions,
            &SolverConfig::default().with_cnf_inprocessing(true),
        )
        .unwrap();

    let stats = backend.last_stats().expect("stats recorded");
    let stat = |key: &str| {
        stats
            .backend
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| *value)
    };
    let before = stat("cnf_compaction_variables_before").expect("before recorded");
    let after = stat("cnf_compaction_variables_after").expect("after recorded");
    let dropped = stat("cnf_compaction_variables_dropped").expect("dropped recorded");
    let baseline_vars = stat("cnf_variables").expect("un-inprocessed var count recorded");
    assert!(after <= before, "compaction must not raise the var count");
    assert!(
        after < baseline_vars,
        "compacted var count {after} must be below the un-inprocessed count {baseline_vars}"
    );
    assert!(
        (dropped - (before - after)).abs() < f64::EPSILON,
        "dropped stat must equal before - after"
    );

    // The lifted sat model replays against the original terms.
    let CheckResult::Sat(model) = result else {
        panic!("expected sat");
    };
    let assignment = model.to_assignment();
    for &term in &assertions {
        assert_eq!(
            eval(&arena, term, &assignment).unwrap(),
            Value::Bool(true),
            "compacted+reconstructed model must satisfy every original assertion"
        );
    }
}

#[test]
fn cnf_compaction_admits_a_var_budget_the_uncompacted_count_exceeds() {
    // Soundness + the admission-change point: pick a CNF variable budget that the
    // un-inprocessed Tseitin var count EXCEEDS but the compacted count clears.
    // Without compaction the backend would refuse with Unknown(EncodingBudget);
    // with inprocessing+compaction it is admitted, solves, and the lifted model
    // replays.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let nine = arena.bv_const(8, 9).unwrap();
    let x_is_nine = arena.eq(x, nine).unwrap();
    let twenty = arena.bv_const(8, 20).unwrap();
    let sum_is_twenty = arena.eq(sum, twenty).unwrap();
    let assertions = vec![x_is_nine, sum_is_twenty];

    // Measure the un-inprocessed var count and the compacted var count first.
    let mut probe = SatBvBackend::new();
    let _ = probe
        .check(
            &arena,
            &assertions,
            &SolverConfig::default().with_cnf_inprocessing(true),
        )
        .unwrap();
    let pstats = probe.last_stats().expect("stats recorded");
    let stat = |key: &str| {
        pstats
            .backend
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| *value)
    };
    // The stat values are small non-negative integer counts stored as f64. The
    // cast is guarded by the bounds assert: non-negative, integral, well under
    // u64::MAX, so neither truncation nor sign loss can occur.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let to_count = |v: f64| -> u64 {
        assert!(
            v >= 0.0 && v.fract() == 0.0 && v < 1e18,
            "count stat must be a small non-negative integer"
        );
        v.round() as u64
    };
    let baseline_vars = to_count(stat("cnf_variables").expect("un-inprocessed var count"));
    let compacted_vars =
        to_count(stat("cnf_compaction_variables_after").expect("compacted var count"));

    // Only meaningful if compaction actually moved the count below the baseline.
    if compacted_vars < baseline_vars {
        // A budget strictly between the compacted and un-inprocessed counts: the
        // un-compacted formula would be refused, the compacted one admitted.
        let budget = compacted_vars + (baseline_vars - compacted_vars) / 2;
        assert!(budget >= compacted_vars && budget < baseline_vars);

        let config = SolverConfig::default()
            .with_cnf_inprocessing(true)
            .with_cnf_variable_budget(budget);
        let result = SatBvBackend::new()
            .check(&arena, &assertions, &config)
            .unwrap();
        let CheckResult::Sat(model) = result else {
            panic!("compacted formula within budget must solve to sat, not be refused");
        };
        let assignment = model.to_assignment();
        for &term in &assertions {
            assert_eq!(
                eval(&arena, term, &assignment).unwrap(),
                Value::Bool(true),
                "admitted-via-compaction model must satisfy every original assertion"
            );
        }

        // And confirm the un-compacted (inprocessing off) path is refused at this
        // budget, proving admission actually changed.
        let no_inprocess = SolverConfig::default().with_cnf_variable_budget(budget);
        let refused = SatBvBackend::new()
            .check(&arena, &assertions, &no_inprocess)
            .unwrap();
        assert!(
            matches!(
                refused,
                CheckResult::Unknown(ref r) if r.kind == UnknownKind::EncodingBudget
            ),
            "without compaction the var-bound budget must refuse the encoding, got {refused:?}"
        );
    }
}

#[test]
fn wide_bit_vector_contradiction_is_unsat() {
    // x + 1 = 5 (so x = 4) and x = 10 contradict, at 200 bits.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(200)).unwrap();
    let xv = arena.var(x);
    let one = arena.bv_const(200, 1).unwrap();
    let sum = arena.bv_add(xv, one).unwrap();
    let five = arena.bv_const(200, 5).unwrap();
    let ten = arena.bv_const(200, 10).unwrap();
    let c1 = arena.eq(sum, five).unwrap();
    let c2 = arena.eq(xv, ten).unwrap();
    assert_eq!(check(&arena, &[c1, c2]), CheckResult::Unsat);
}

#[test]
fn oversized_multiply_is_refused_gracefully_not_oom() {
    // A single wide multiply bit-blasts to ~width² gates. The pre-lowering
    // estimate must refuse it as Unknown(EncodingBudget) WITHOUT allocating the
    // AIG/CNF — degrading cleanly instead of aborting out of memory. 8192-bit
    // `a·b` is ~8192²·3 ≈ 200M estimated clauses, over the 64M absolute ceiling
    // that applies when no explicit CNF budget is set.
    let mut arena = TermArena::new();
    let w = 8192;
    let a = arena
        .declare("a", Sort::BitVec(w))
        .map(|s| arena.var(s))
        .unwrap();
    let b = arena
        .declare("b", Sort::BitVec(w))
        .map(|s| arena.var(s))
        .unwrap();
    let prod = arena.bv_mul(a, b).unwrap();
    let zero = arena.bv_const(w, 0).unwrap();
    let goal = arena.eq(prod, zero).unwrap();
    let result = SatBvBackend::new()
        .check(&arena, &[goal], &SolverConfig::default())
        .unwrap();
    assert!(
        matches!(&result, CheckResult::Unknown(r) if matches!(r.kind, UnknownKind::EncodingBudget)),
        "wide multiply must degrade to an EncodingBudget unknown, got {result:?}"
    );
}

#[test]
fn just_under_ceiling_4096bit_multiply_is_refused_not_trapped() {
    // Regression (documentation-agent / wasm-playground find): a 4096-bit `a·b`
    // estimated to only `4096²·3 ≈ 50M` clauses under the OLD `w²`-gate model — *just*
    // under the 64M ceiling — so it was NOT refused and OOM-trapped (wasm
    // `unreachable`) during lowering instead of returning `unknown`. The estimate now
    // charges the multiplier's adder tree (~8·w²), so this is refused before
    // allocation: a graceful `EncodingBudget` unknown, never a crash.
    let mut arena = TermArena::new();
    let w = 4096;
    let a = arena
        .declare("a", Sort::BitVec(w))
        .map(|s| arena.var(s))
        .unwrap();
    let b = arena
        .declare("b", Sort::BitVec(w))
        .map(|s| arena.var(s))
        .unwrap();
    let prod = arena.bv_mul(a, b).unwrap();
    let one = arena.bv_const(w, 1).unwrap();
    let goal = arena.eq(prod, one).unwrap(); // a·b = 1, a constrained multiply
    let result = SatBvBackend::new()
        .check(&arena, &[goal], &SolverConfig::default())
        .unwrap();
    assert!(
        matches!(&result, CheckResult::Unknown(r) if matches!(r.kind, UnknownKind::EncodingBudget)),
        "4096-bit constrained multiply must refuse gracefully (EncodingBudget), got {result:?}"
    );
}

/// End-to-end checks of the flag-gated native CDCL primary search (slice 1):
/// the native core decides BV queries, its `sat` models still replay against the
/// original terms, and its verdicts agree with the default `BatSat` path.
mod native_cdcl {
    use super::{CheckResult, SatBvBackend, SolverBackend, SolverConfig, Value};
    use axeyum_ir::{Sort, TermArena, TermId, eval};

    fn native_config() -> SolverConfig {
        SolverConfig {
            native_cdcl: true,
            ..SolverConfig::default()
        }
    }

    fn check_native(arena: &TermArena, assertions: &[TermId]) -> CheckResult {
        SatBvBackend::new()
            .check(arena, assertions, &native_config())
            .expect("native CDCL backend invocation succeeds")
    }

    fn check_batsat(arena: &TermArena, assertions: &[TermId]) -> CheckResult {
        SatBvBackend::new()
            .check(arena, assertions, &SolverConfig::default())
            .expect("batsat backend invocation succeeds")
    }

    /// A satisfiable BV query solved by the native core must produce a model that
    /// replays against the original terms (replay runs inside `check`, and we
    /// re-evaluate here for belt-and-suspenders).
    #[test]
    fn native_sat_model_replays() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(4)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(4)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let two = arena.bv_const(4, 2).unwrap();
        let five = arena.bv_const(4, 5).unwrap();
        let x_is_two = arena.eq(x, two).unwrap();
        let sum = arena.bv_add(x, y).unwrap();
        let sum_is_five = arena.eq(sum, five).unwrap();

        let CheckResult::Sat(model) = check_native(&arena, &[x_is_two, sum_is_five]) else {
            panic!("native core should find this satisfiable");
        };
        let assignment = model.to_assignment();
        for &term in &[x_is_two, sum_is_five] {
            assert_eq!(eval(&arena, term, &assignment).unwrap(), Value::Bool(true));
        }
        assert_eq!(model.get(x_sym), Some(Value::Bv { width: 4, value: 2 }));
        assert_eq!(model.get(y_sym), Some(Value::Bv { width: 4, value: 3 }));
    }

    /// An unsatisfiable BV query is reported `unsat` by the native core (its DRAT
    /// proof is independently re-checked when `prove_unsat` is also set).
    #[test]
    fn native_unsat_agrees_and_proof_checks() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 4).unwrap();
        let eq_self = arena.eq(x, x).unwrap();
        let contradiction = arena.not(eq_self).unwrap();

        assert_eq!(
            check_native(&arena, &[contradiction]),
            CheckResult::Unsat,
            "native core must decide x != x unsat"
        );

        let config = SolverConfig {
            prove_unsat: true,
            ..native_config()
        };
        assert_eq!(
            SatBvBackend::new()
                .check(&arena, &[contradiction], &config)
                .unwrap(),
            CheckResult::Unsat
        );
    }

    /// The native core and the default `BatSat` path agree (sat-vs-unsat) on a
    /// spread of small BV queries — the soundness agreement gate for the wiring.
    #[test]
    fn native_agrees_with_batsat_on_bv_queries() {
        // (a) sat: x = 3 over 4 bits.
        let mut a = TermArena::new();
        let xa = a.bv_var("x", 4).unwrap();
        let three = a.bv_const(4, 3).unwrap();
        let q_a = a.eq(xa, three).unwrap();

        // (b) unsat: x < 1 and x > 0 over unsigned 4-bit (no value strictly
        // between, since `bvult`).
        let mut b = TermArena::new();
        let xb = b.bv_var("x", 4).unwrap();
        let zero = b.bv_const(4, 0).unwrap();
        let one = b.bv_const(4, 1).unwrap();
        let lt_one = b.bv_ult(xb, one).unwrap();
        let gt_zero = b.bv_ult(zero, xb).unwrap();

        // (c) sat: bitwise — x & 0b1010 = 0b1010 over 4 bits.
        let mut c = TermArena::new();
        let xc = c.bv_var("x", 4).unwrap();
        let mask = c.bv_const(4, 0b1010).unwrap();
        let anded = c.bv_and(xc, mask).unwrap();
        let q_c = c.eq(anded, mask).unwrap();

        for (arena, terms) in [
            (&a, vec![q_a]),
            (&b, vec![lt_one, gt_zero]),
            (&c, vec![q_c]),
        ] {
            let native = check_native(arena, &terms);
            let batsat = check_batsat(arena, &terms);
            let agree = matches!(
                (&native, &batsat),
                (CheckResult::Sat(_), CheckResult::Sat(_))
                    | (CheckResult::Unsat, CheckResult::Unsat)
            );
            assert!(agree, "native={native:?} batsat={batsat:?} must agree");
        }
    }
}
