//! Integration tests for word-level preprocessing (P1.2) through the real
//! pure-Rust sat-bv backend: `check_with_preprocessing` must eliminate variables
//! before solving and return a model over the *original* symbols that satisfies
//! the *original* assertions.

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SatBvBackend, SolverConfig, check_with_preprocessing};

fn check(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    let mut backend = SatBvBackend::new();
    check_with_preprocessing(&mut backend, arena, assertions, &SolverConfig::default())
        .expect("preprocessing + sat-bv backend succeeds")
}

fn assert_model_satisfies(arena: &TermArena, model: &axeyum_solver::Model, originals: &[TermId]) {
    let assignment = model.to_assignment();
    for &a in originals {
        assert_eq!(
            eval(arena, a, &assignment).unwrap(),
            Value::Bool(true),
            "returned model must satisfy original assertion #{}",
            a.index()
        );
    }
}

#[test]
fn constant_pin_is_eliminated_and_reconstructed() {
    // x = 7 ∧ x + y = 10. propagate_values pins x; the model must still assign it.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let seven = arena.bv_const(8, 7).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let x_is_7 = arena.eq(xv, seven).unwrap();
    let sum = arena.bv_add(xv, yv).unwrap();
    let sum_is_10 = arena.eq(sum, ten).unwrap();
    let originals = [x_is_7, sum_is_10];

    let CheckResult::Sat(model) = check(&mut arena, &originals) else {
        panic!("expected sat");
    };
    assert_eq!(model.get(x), Some(Value::Bv { width: 8, value: 7 }));
    assert_eq!(model.get(y), Some(Value::Bv { width: 8, value: 3 }));
    assert_model_satisfies(&arena, &model, &originals);
}

#[test]
fn variable_definition_is_solved_and_reconstructed() {
    // x = y + 1 ∧ x * y = 12. solve_eqs substitutes x := y + 1.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let one = arena.bv_const(8, 1).unwrap();
    let y1 = arena.bv_add(yv, one).unwrap();
    let x_def = arena.eq(xv, y1).unwrap();
    let prod = arena.bv_mul(xv, yv).unwrap();
    let twelve = arena.bv_const(8, 12).unwrap();
    let prod_is_12 = arena.eq(prod, twelve).unwrap();
    let originals = [x_def, prod_is_12];

    let CheckResult::Sat(model) = check(&mut arena, &originals) else {
        panic!("expected sat");
    };
    // Whatever y the backend chose, x = y + 1 must hold and x*y = 12.
    assert_model_satisfies(&arena, &model, &originals);
}

#[test]
fn conflicting_constants_are_unsat_after_preprocessing() {
    // x = 5 ∧ x = 6: propagate_values pins x = 5, leaving the false (5 = 6).
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let five = arena.bv_const(8, 5).unwrap();
    let six = arena.bv_const(8, 6).unwrap();
    let x_is_5 = arena.eq(xv, five).unwrap();
    let x_is_6 = arena.eq(xv, six).unwrap();

    assert_eq!(check(&mut arena, &[x_is_5, x_is_6]), CheckResult::Unsat);
}

#[test]
fn pure_problem_without_facts_passes_through() {
    // No top-level variable=term fact; the backend solves the whole thing and the
    // model still satisfies the originals.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(4)).unwrap();
    let y = arena.declare("y", Sort::BitVec(4)).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let sum = arena.bv_add(xv, yv).unwrap();
    let nine = arena.bv_const(4, 9).unwrap();
    let sum_is_9 = arena.eq(sum, nine).unwrap();
    let lt = arena.bv_ult(xv, yv).unwrap();
    let originals = [sum_is_9, lt];

    let CheckResult::Sat(model) = check(&mut arena, &originals) else {
        panic!("expected sat");
    };
    assert_model_satisfies(&arena, &model, &originals);
}

#[test]
fn chained_definitions_all_reconstruct() {
    // x = y + 1 ∧ y = z ∧ z + 0 = 4  (z anchored via an arithmetic fact).
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let z = arena.declare("z", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let zv = arena.var(z);
    let one = arena.bv_const(8, 1).unwrap();
    let y1 = arena.bv_add(yv, one).unwrap();
    let x_def = arena.eq(xv, y1).unwrap();
    let y_def = arena.eq(yv, zv).unwrap();
    let four = arena.bv_const(8, 4).unwrap();
    let z_is_4 = arena.eq(zv, four).unwrap();
    let originals = [x_def, y_def, z_is_4];

    let CheckResult::Sat(model) = check(&mut arena, &originals) else {
        panic!("expected sat");
    };
    assert_eq!(model.get(z), Some(Value::Bv { width: 8, value: 4 }));
    assert_eq!(model.get(y), Some(Value::Bv { width: 8, value: 4 }));
    assert_eq!(model.get(x), Some(Value::Bv { width: 8, value: 5 }));
    assert_model_satisfies(&arena, &model, &originals);
}

/// Multiplier-commutativity is refuted by canonicalization alone — no multiplier
/// bit-blasting. `(not (= (a*b) (b*a)))` is unsat; commutative-operand ordering
/// makes the two products coincide, so the canonicalizer folds the equality to
/// `true` and the negation to `false`. Wide operands (32-bit) would make a
/// genuine multiplier blast slow; this returns immediately.
#[test]
fn multiplier_commutativity_is_refuted_by_canonicalization() {
    let mut arena = TermArena::new();
    let a = arena.declare("a", Sort::BitVec(32)).unwrap();
    let b = arena.declare("b", Sort::BitVec(32)).unwrap();
    let av = arena.var(a);
    let bv = arena.var(b);
    let ab = arena.bv_mul(av, bv).unwrap();
    let ba = arena.bv_mul(bv, av).unwrap();
    let eq = arena.eq(ab, ba).unwrap();
    let neq = arena.not(eq).unwrap();

    assert_eq!(
        check(&mut arena, &[neq]),
        CheckResult::Unsat,
        "a*b = b*a, so its negation is unsat — decided by canonicalization, not blasting"
    );
}
