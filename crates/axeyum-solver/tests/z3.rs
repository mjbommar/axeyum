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
    assert!(caps.produces_models);
    assert!(caps.complete);
}
