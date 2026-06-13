//! End-to-end lazy SMT (DPLL(T)) over `QF_LRA`: Boolean structure over real
//! order atoms (ADR-0015 follow-on).
//!
//! These tests exercise [`check_with_lra_dpll`], which lifts the
//! conjunction-only limit of `check_with_lra` by case-splitting `or`/`not`/`ite`
//! via the SAT backend and consulting the exact-rational theory solver. Every
//! `sat` model is replayed against the original query.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, check_with_lra_dpll};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn solve(arena: &mut TermArena, assertions: &[axeyum_ir::TermId]) -> CheckResult {
    check_with_lra_dpll(arena, assertions, &config())
        .expect("supported lazy-SMT query decides without error")
}

#[test]
fn disjunction_of_real_constraints_is_satisfiable() {
    // (x < 0) or (x > 10) : satisfiable (the conjunctive solver rejected this).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let ten = arena.real_ratio(10, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, ten).unwrap();
    let disj = arena.or(lt, gt).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[disj]) else {
        panic!("expected the disjunction to be satisfiable");
    };
    // The model replays, and it satisfies one of the disjuncts.
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, disj, &assignment).unwrap(), Value::Bool(true));
}

#[test]
fn case_split_finds_the_only_feasible_branch() {
    // (x < 0 or x > 0) and x >= 0  =>  must take x > 0 ; satisfiable.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let split = arena.or(lt, gt).unwrap();
    let nonneg = arena.real_ge(x, zero).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[split, nonneg]) else {
        panic!("expected the feasible branch to be found");
    };
    let xv = model.get(x_sym).unwrap().as_real().unwrap();
    assert!(xv > axeyum_ir::Rational::zero(), "must satisfy x > 0");
}

#[test]
fn boolean_unsatisfiable_combination_is_unsat() {
    // (x < 0 or x > 0) and (x >= 0 and x <= 0)  =>  x == 0, contradicting the
    // disjunction; every case split conflicts, so the result is unsat.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let lt = arena.real_lt(x, zero).unwrap();
    let gt = arena.real_gt(x, zero).unwrap();
    let split = arena.or(lt, gt).unwrap();
    let ge = arena.real_ge(x, zero).unwrap();
    let le = arena.real_le(x, zero).unwrap();
    let pinned = arena.and(ge, le).unwrap();

    assert_eq!(solve(&mut arena, &[split, pinned]), CheckResult::Unsat);
}

#[test]
fn mixed_boolean_variable_and_theory_atoms() {
    // (p or x > 5) and (not p) and x < 3  =>  forces x > 5 and x < 3 under
    // not-p ... which is unsat; flip: (p or x > 5) and (not p) and x > 6 is sat.
    let mut arena = TermArena::new();
    let p_sym = arena.declare("p", Sort::Bool).unwrap();
    let p = arena.var(p_sym);
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let five = arena.real_ratio(5, 1);
    let six = arena.real_ratio(6, 1);
    let big = arena.real_gt(x, five).unwrap();
    let clause = arena.or(p, big).unwrap();
    let not_p = arena.not(p).unwrap();
    let above6 = arena.real_gt(x, six).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[clause, not_p, above6]) else {
        panic!("expected sat: not-p forces x>5, and x>6 satisfies it");
    };
    assert_eq!(model.get(p_sym), Some(Value::Bool(false)));
    let assignment = model.to_assignment();
    assert_eq!(
        eval(&arena, clause, &assignment).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn disjunction_of_real_equalities_is_satisfiable() {
    // (x == 1) or (x == 2) : satisfiable via equality-as-two-inequalities and
    // the SAT case split.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let one = arena.real_ratio(1, 1);
    let two = arena.real_ratio(2, 1);
    let eq1 = arena.eq(x, one).unwrap();
    let eq2 = arena.eq(x, two).unwrap();
    let disj = arena.or(eq1, eq2).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[disj]) else {
        panic!("expected sat");
    };
    let assignment = model.to_assignment();
    assert_eq!(eval(&arena, disj, &assignment).unwrap(), Value::Bool(true));
}

#[test]
fn real_disequality_forces_inequality() {
    // x != 0 && x <= 0 && x >= 0 : the disequality contradicts x pinned to 0.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let eq0 = arena.eq(x, zero).unwrap();
    let ne0 = arena.not(eq0).unwrap();
    let le = arena.real_le(x, zero).unwrap();
    let ge = arena.real_ge(x, zero).unwrap();
    assert_eq!(solve(&mut arena, &[ne0, le, ge]), CheckResult::Unsat);
}

#[test]
fn real_disequality_is_satisfiable_with_room() {
    // x != 0 && x <= 5  is satisfiable (e.g. x = anything != 0 below 5).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let five = arena.real_ratio(5, 1);
    let eq0 = arena.eq(x, zero).unwrap();
    let ne0 = arena.not(eq0).unwrap();
    let le5 = arena.real_le(x, five).unwrap();

    let CheckResult::Sat(model) = solve(&mut arena, &[ne0, le5]) else {
        panic!("expected sat");
    };
    let xv = model.get(x_sym).unwrap().as_real().unwrap();
    assert_ne!(xv, axeyum_ir::Rational::zero(), "x must differ from 0");
}

#[test]
fn small_conflict_core_among_many_atoms_is_unsat() {
    // The infeasible core is just {x > 5, x < 1}; the other atoms over y/z are
    // irrelevant. Farkas-based conflict minimization blocks only the core, but
    // the verdict must be `unsat` regardless. (x > 5 ∧ x < 1) ∧ (y < 10) ∧
    // (z > 0 ∨ z <= 0) — the y/z parts are all satisfiable.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let y = arena.real_var("y").unwrap();
    let z = arena.real_var("z").unwrap();
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let five = arena.real_ratio(5, 1);
    let ten = arena.real_ratio(10, 1);

    let x_big = arena.real_gt(x, five).unwrap();
    let x_small = arena.real_lt(x, one).unwrap();
    let y_bounded = arena.real_lt(y, ten).unwrap();
    let z_pos = arena.real_gt(z, zero).unwrap();
    let z_nonpos = arena.real_le(z, zero).unwrap();
    let z_either = arena.or(z_pos, z_nonpos).unwrap();

    assert_eq!(
        solve(&mut arena, &[x_big, x_small, y_bounded, z_either]),
        CheckResult::Unsat,
        "the x core is infeasible, so the whole query is unsat"
    );
}

#[test]
fn boolean_structured_real_conflict_is_unsat() {
    // (x < 0 ∨ x < 1) ∧ x > 2 ∧ x > 3 : every branch conflicts with x > 3,
    // so the query is unsatisfiable through the case split + theory conflicts.
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let two = arena.real_ratio(2, 1);
    let three = arena.real_ratio(3, 1);
    let lt0 = arena.real_lt(x, zero).unwrap();
    let lt1 = arena.real_lt(x, one).unwrap();
    let branch = arena.or(lt0, lt1).unwrap();
    let gt2 = arena.real_gt(x, two).unwrap();
    let gt3 = arena.real_gt(x, three).unwrap();
    assert_eq!(solve(&mut arena, &[branch, gt2, gt3]), CheckResult::Unsat);
}

#[test]
fn pure_conjunction_still_works() {
    // No Boolean structure: a plain conjunction routes through and is sat.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let gt = arena.real_gt(x, zero).unwrap();
    let lt = arena.real_lt(x, one).unwrap();
    assert!(matches!(solve(&mut arena, &[gt, lt]), CheckResult::Sat(_)));
}
