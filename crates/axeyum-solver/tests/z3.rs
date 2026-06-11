//! Conformance tests for the Z3 oracle backend (feature `z3`).
//!
//! Every `sat` result is replayed through the trusted evaluator against the
//! original assertions — the level-1 evidence check is part of the test
//! harness itself, not an afterthought.

#![cfg(feature = "z3")]

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverBackend, SolverConfig, SolverError, Z3Backend};

fn check(arena: &TermArena, assertions: &[TermId]) -> CheckResult {
    Z3Backend::new()
        .check(arena, assertions, &SolverConfig::default())
        .expect("backend invocation succeeds")
}

/// Asserts `sat`, replays the model through the evaluator, returns it.
fn expect_sat_checked(arena: &TermArena, assertions: &[TermId]) -> axeyum_solver::Model {
    let CheckResult::Sat(model) = check(arena, assertions) else {
        panic!("expected sat");
    };
    let asg = model.to_assignment();
    for &t in assertions {
        assert_eq!(
            eval(arena, t, &asg).unwrap(),
            Value::Bool(true),
            "model must satisfy every original assertion"
        );
    }
    model
}

#[test]
fn unique_solution_is_found_and_replays() {
    let mut a = TermArena::new();
    let x_sym = a.declare("x", Sort::BitVec(8)).unwrap();
    let x = a.var(x_sym);
    let one = a.bv_const(8, 1).unwrap();
    let five = a.bv_const(8, 5).unwrap();
    let sum = a.bv_add(x, one).unwrap();
    let formula = a.eq(sum, five).unwrap();

    let model = expect_sat_checked(&a, &[formula]);
    assert_eq!(model.get(x_sym), Some(Value::Bv { width: 8, value: 4 }));
}

#[test]
fn contradiction_is_unsat() {
    let mut a = TermArena::new();
    let x = a.bv_var("x", 8).unwrap();
    let zero = a.bv_const(8, 0).unwrap();
    // x < 0 is unsatisfiable for unsigned comparison.
    let f = a.bv_ult(x, zero).unwrap();
    assert_eq!(check(&a, &[f]), CheckResult::Unsat);
}

#[test]
fn boolean_structure_solves() {
    let mut a = TermArena::new();
    let p_sym = a.declare("p", Sort::Bool).unwrap();
    let q_sym = a.declare("q", Sort::Bool).unwrap();
    let p = a.var(p_sym);
    let q = a.var(q_sym);
    // p xor q, and not p  =>  q must be true, p false.
    let x = a.xor(p, q).unwrap();
    let np = a.not(p).unwrap();
    let model = expect_sat_checked(&a, &[x, np]);
    assert_eq!(model.get(p_sym), Some(Value::Bool(false)));
    assert_eq!(model.get(q_sym), Some(Value::Bool(true)));
}

#[test]
fn model_completion_assigns_unconstrained_symbols() {
    let mut a = TermArena::new();
    let used = a.bv_var("used", 8).unwrap();
    let unused_sym = a.declare("unused", Sort::BitVec(16)).unwrap();
    let three = a.bv_const(8, 3).unwrap();
    let f = a.eq(used, three).unwrap();
    let model = expect_sat_checked(&a, &[f]);
    // The unconstrained symbol still gets a value (model completion), so
    // check-by-evaluation never hits an unbound symbol.
    assert!(model.get(unused_sym).is_some());
}

#[test]
fn wide_bitvectors_lift_correctly() {
    // Width 80 exceeds u64; the model lift goes through 64-bit chunks.
    let mut a = TermArena::new();
    let x_sym = a.declare("x", Sort::BitVec(80)).unwrap();
    let x = a.var(x_sym);
    let big = a.bv_const(80, (1u128 << 79) | 0xDEAD_BEEF).unwrap();
    let f = a.eq(x, big).unwrap();
    let model = expect_sat_checked(&a, &[f]);
    assert_eq!(
        model.get(x_sym),
        Some(Value::Bv {
            width: 80,
            value: (1u128 << 79) | 0xDEAD_BEEF
        })
    );
}

#[test]
fn ite_and_extract_concat_round_trip_through_z3() {
    let mut a = TermArena::new();
    let x_sym = a.declare("x", Sort::BitVec(8)).unwrap();
    let x = a.var(x_sym);
    // concat(extract[7:4](x), extract[3:0](x)) == 0xA5, picked via ite(true, ..).
    let hi = a.extract(7, 4, x).unwrap();
    let lo = a.extract(3, 0, x).unwrap();
    let back = a.concat(hi, lo).unwrap();
    let target = a.bv_const(8, 0xA5).unwrap();
    let cond = a.bool_const(true);
    let picked = a.ite(cond, back, target).unwrap();
    let f = a.eq(picked, target).unwrap();
    let model = expect_sat_checked(&a, &[f]);
    assert_eq!(
        model.get(x_sym),
        Some(Value::Bv {
            width: 8,
            value: 0xA5
        })
    );
}

#[test]
fn non_boolean_assertion_is_a_typed_error() {
    let mut a = TermArena::new();
    let x = a.bv_var("x", 8).unwrap();
    let err = Z3Backend::new()
        .check(&a, &[x], &SolverConfig::default())
        .unwrap_err();
    assert!(matches!(err, SolverError::NonBooleanAssertion(_)));
}

#[test]
fn capabilities_report_models() {
    let caps = Z3Backend::new().capabilities();
    assert!(caps.name.starts_with("z3 "));
    assert!(caps.produces_models);
    assert!(caps.complete);
}

// ----- resource governance (observability note) ----------------------------

#[test]
fn node_budget_refuses_admission_with_diagnosis() {
    use axeyum_solver::UnknownKind;
    let mut a = TermArena::new();
    let mut t = a.bv_var("x", 64).unwrap();
    for _ in 0..50 {
        t = a.bv_add(t, t).unwrap();
    }
    let zero = a.bv_const(64, 0).unwrap();
    let f = a.eq(t, zero).unwrap();
    let config = SolverConfig {
        node_budget: Some(10),
        ..SolverConfig::default()
    };
    let result = Z3Backend::new().check(&a, &[f], &config).unwrap();
    let CheckResult::Unknown(reason) = result else {
        panic!("expected Unknown, got {result:?}");
    };
    assert_eq!(reason.kind, UnknownKind::NodeBudget);
    assert!(reason.detail.contains("budget 10"), "{}", reason.detail);
}

#[test]
fn resource_limit_yields_classified_unknown() {
    use axeyum_solver::UnknownKind;
    // Wide multiplication inversion with a tiny deterministic budget: Z3
    // must give up and say why, reproducibly.
    let mut a = TermArena::new();
    let x = a.bv_var("x", 64).unwrap();
    let y = a.bv_var("y", 64).unwrap();
    let prod = a.bv_mul(x, y).unwrap();
    let target = a.bv_const(64, 0xDEAD_BEEF_CAFE_F00D).unwrap();
    let f = a.eq(prod, target).unwrap();
    let one = a.bv_const(64, 1).unwrap();
    let x_big = a.bv_ugt(x, one).unwrap();
    let y_big = a.bv_ugt(y, one).unwrap();
    let config = SolverConfig {
        resource_limit: Some(100),
        ..SolverConfig::default()
    };
    let result = Z3Backend::new()
        .check(&a, &[f, x_big, y_big], &config)
        .unwrap();
    let CheckResult::Unknown(reason) = result else {
        panic!("expected Unknown under rlimit, got {result:?}");
    };
    assert!(
        matches!(
            reason.kind,
            UnknownKind::ResourceLimit | UnknownKind::Timeout
        ),
        "unexpected kind {:?} ({})",
        reason.kind,
        reason.detail
    );
}

#[test]
fn solve_stats_attribute_layers() {
    let mut a = TermArena::new();
    let x = a.bv_var("x", 8).unwrap();
    let one = a.bv_const(8, 1).unwrap();
    let five = a.bv_const(8, 5).unwrap();
    let sum = a.bv_add(x, one).unwrap();
    let f = a.eq(sum, five).unwrap();
    let mut backend = Z3Backend::new();
    assert!(backend.last_stats().is_none());
    let _ = backend.check(&a, &[f], &SolverConfig::default()).unwrap();
    let stats = backend.last_stats().expect("stats recorded");
    assert_eq!(stats.assertion_count, 1);
    assert_eq!(stats.terms_translated, 5); // x, 1, 5, x+1, eq
    assert!(stats.translate.as_nanos() > 0);
    assert!(stats.solve.as_nanos() > 0);
    assert!(stats.model_lift.as_nanos() > 0);
}

// ----- SMT-LIB ingestion through the trait (Phase 2) ------------------------

#[test]
fn parsed_benchmark_solves_and_replays() {
    let text = r"
        (set-info :status sat)
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (= (bvadd (bvmul x y) (_ bv1 8)) (_ bv16 8)))
        (assert (bvult y x))
        (check-sat)
    ";
    let script = axeyum_smtlib::parse_script(text).unwrap();
    let result = Z3Backend::new()
        .check(&script.arena, &script.assertions, &SolverConfig::default())
        .unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("ground truth says sat");
    };
    // Level-1 evidence: replay through the evaluator.
    let asg = model.to_assignment();
    for &t in &script.assertions {
        assert_eq!(eval(&script.arena, t, &asg).unwrap(), Value::Bool(true));
    }
    // And the sharing-preserving export round-trips through Z3 too.
    let exported = axeyum_smtlib::write_script(&script.arena, &script.assertions);
    let reparsed = axeyum_smtlib::parse_script(&exported).unwrap();
    let again = Z3Backend::new()
        .check(
            &reparsed.arena,
            &reparsed.assertions,
            &SolverConfig::default(),
        )
        .unwrap();
    assert!(matches!(again, CheckResult::Sat(_)));
}
