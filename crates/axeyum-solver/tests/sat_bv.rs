//! Conformance tests for the pure Rust SAT-backed BV backend.
//!
//! These tests exercise the Phase 5 composition path: query terms lower to
//! AIG/CNF, solve through the pure Rust `BatSat` adapter, lift a model, and
//! replay the original formula before returning `sat`.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_query::Query;
use axeyum_solver::{CheckResult, SatBvBackend, SolverBackend, SolverConfig, UnknownKind};

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
fn unsat_is_drat_proof_checked_when_requested() {
    // `x != x` is unsatisfiable; with `prove_unsat`, the backend re-derives the
    // UNSAT with the proof core and verifies its DRAT proof end to end.
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
    assert!(
        stats
            .backend
            .iter()
            .any(|(name, value)| name == "unsat_proof_checked"
                && (*value - 1.0).abs() < f64::EPSILON),
        "unsat should be recorded as DRAT-proof-checked"
    );
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
    assert!(reason.detail.contains("CNF has"));
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
        "cnf_variables",
        "cnf_clauses",
    ] {
        assert!(
            stats.backend.iter().any(|(name, _)| name == key),
            "missing backend stat {key}"
        );
    }
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
        let inprocessed = SatBvBackend::new()
            .check(
                &arena,
                &assertions,
                &SolverConfig::default().with_cnf_inprocessing(true),
            )
            .unwrap();
        assert_eq!(
            outcome_tag(&baseline),
            outcome_tag(&inprocessed),
            "inprocessing changed the decision"
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
    // Inprocessing + prove_unsat: the reduced (equisatisfiable) formula is the
    // one independently re-derived and DRAT-checked.
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
            .any(|(name, value)| name == "unsat_proof_checked"
                && (*value - 1.0).abs() < f64::EPSILON),
        "reduced-formula unsat should be DRAT-proof-checked"
    );
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
