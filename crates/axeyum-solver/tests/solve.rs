//! The unified `solve` front door: one call decides anything supported —
//! quantifier-free or quantified, any theory combination.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn run(arena: &mut TermArena, assertions: &[axeyum_ir::TermId]) -> CheckResult {
    solve(arena, assertions, &config()).expect("supported query decides without error")
}

#[test]
fn solves_quantifier_free_bitvector() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let sum = arena.bv_add(x, one).unwrap();
    let eq = arena.eq(sum, five).unwrap();
    assert!(matches!(run(&mut arena, &[eq]), CheckResult::Sat(_)));
}

#[test]
fn solves_mixed_real_and_bitvector() {
    // r > 0 and b = 1 — combined real + bit-vector, one call.
    let mut arena = TermArena::new();
    let r_sym = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(r_sym);
    let zero = arena.real_ratio(0, 1);
    let r_pos = arena.real_gt(r, zero).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let b_eq = arena.eq(b, one).unwrap();
    let both = arena.and(r_pos, b_eq).unwrap();
    let CheckResult::Sat(model) = run(&mut arena, &[both]) else {
        panic!("expected sat");
    };
    assert_eq!(
        eval(&arena, both, &model.to_assignment()).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn solves_finite_domain_quantifier() {
    // forall x:BV3. x | x == x — valid, decided by finite expansion.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
    let x = arena.var(x_sym);
    let or = arena.bv_or(x, x).unwrap();
    let body = arena.eq(or, x).unwrap();
    let all = arena.forall(x_sym, body).unwrap();
    assert!(matches!(run(&mut arena, &[all]), CheckResult::Sat(_)));
}

#[test]
fn refutes_infinite_domain_quantifier_via_instantiation() {
    // forall r:Real. r < 1, with ground 1 present → refuted (unsat) by the
    // instantiation fallback, since finite expansion cannot enumerate reals.
    let mut arena = TermArena::new();
    let r_sym = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(r_sym);
    let one = arena.real_ratio(1, 1);
    let body = arena.real_lt(r, one).unwrap();
    let all = arena.forall(r_sym, body).unwrap();
    let s = arena.declare("s", Sort::Real).unwrap();
    let sv = arena.var(s);
    let s_is_1 = arena.eq(sv, one).unwrap();
    assert_eq!(run(&mut arena, &[all, s_is_1]), CheckResult::Unsat);
}

/// With `with_preprocess(true)`, the `solve` façade canonicalizes first, so a wide
/// multiplier-commutativity refutation is decided WITHOUT bit-blasting the
/// multiplier: `(not (= (a*b) (b*a)))` over 32-bit operands returns unsat instantly.
#[test]
fn preprocess_flag_refutes_multiplier_commutativity_without_blasting() {
    let mut arena = TermArena::new();
    let a = arena.bv_var("a", 32).unwrap();
    let b = arena.bv_var("b", 32).unwrap();
    let ab = arena.bv_mul(a, b).unwrap();
    let ba = arena.bv_mul(b, a).unwrap();
    let eq = arena.eq(ab, ba).unwrap();
    let neq = arena.not(eq).unwrap();

    let cfg = SolverConfig::new()
        .with_timeout(Duration::from_secs(30))
        .with_preprocess(true);
    assert_eq!(
        solve(&mut arena, &[neq], &cfg).expect("decides"),
        CheckResult::Unsat,
    );
}
