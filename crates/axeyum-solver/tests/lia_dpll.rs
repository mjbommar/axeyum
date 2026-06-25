//! Boolean-structured `QF_LIA` (disjunctions/implications of integer atoms) via
//! the lazy-SMT loop over the integer simplex, combined `QF_LIRA` (integers and
//! reals together), and through the dispatcher.

use axeyum_ir::{Rational, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    ArithDpllOutcome, CheckResult, SolverConfig, certify_arith_dpll_unsat, check_with_lia_dpll,
    solve,
};

fn int_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Int).unwrap();
    arena.var(sym)
}

fn real_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Real).unwrap();
    arena.var(sym)
}

fn bool_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Bool).unwrap();
    arena.var(sym)
}

#[test]
fn disjunction_is_satisfiable_and_replayed() {
    // (x < 0 OR x > 10) AND x == 15  ->  sat at x = 15.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = arena.int_const(0);
    let ten = arena.int_const(10);
    let fifteen = arena.int_const(15);
    let lo = arena.int_lt(x, zero).unwrap();
    let hi = arena.int_gt(x, ten).unwrap();
    let disj = arena.or(lo, hi).unwrap();
    let pin = arena.eq(x, fifteen).unwrap();

    match check_with_lia_dpll(&mut arena, &[disj, pin], &SolverConfig::default()).unwrap() {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            assert_eq!(eval(&arena, disj, &assignment).unwrap(), Value::Bool(true));
            assert_eq!(eval(&arena, pin, &assignment).unwrap(), Value::Bool(true));
        }
        other => panic!("expected sat, got {other:?}"),
    }
}

#[test]
fn disjunction_with_excluded_value_is_unsat() {
    // (x < 0 OR x > 10) AND x == 5 : 5 is neither < 0 nor > 10 -> unsat. This
    // needs the lazy loop to refute *both* disjuncts under x == 5.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = arena.int_const(0);
    let ten = arena.int_const(10);
    let five = arena.int_const(5);
    let lo = arena.int_lt(x, zero).unwrap();
    let hi = arena.int_gt(x, ten).unwrap();
    let disj = arena.or(lo, hi).unwrap();
    let pin = arena.eq(x, five).unwrap();

    assert!(matches!(
        check_with_lia_dpll(&mut arena, &[disj, pin], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn boolean_leaf_sat_replays_after_online_decline() {
    // The online LIA probe can decide the arithmetic atoms but does not complete
    // original Boolean leaves in its model. `check_with_lia_dpll` must therefore
    // fall back to the legacy path and still return a replaying SAT model.
    let mut arena = TermArena::new();
    let p = bool_var(&mut arena, "p");
    let x = int_var(&mut arena, "x");
    let one = arena.int_const(1);
    let pin = arena.eq(x, one).unwrap();

    match check_with_lia_dpll(&mut arena, &[p, pin], &SolverConfig::default()).unwrap() {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            assert_eq!(eval(&arena, p, &assignment).unwrap(), Value::Bool(true));
            assert_eq!(eval(&arena, pin, &assignment).unwrap(), Value::Bool(true));
        }
        other => panic!("expected sat, got {other:?}"),
    }
}

#[test]
fn equality_disjunction_is_unsat_via_dispatcher() {
    // (x == 2 OR x == 4) AND x == 3 -> unsat, decided through the top-level
    // dispatcher (which routes Boolean-structured integer queries to the loop).
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let two = arena.int_const(2);
    let four = arena.int_const(4);
    let three = arena.int_const(3);
    let is2 = arena.eq(x, two).unwrap();
    let is4 = arena.eq(x, four).unwrap();
    let disj = arena.or(is2, is4).unwrap();
    let pin = arena.eq(x, three).unwrap();

    assert!(matches!(
        solve(&mut arena, &[disj, pin], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn combined_lira_disjunction_is_unsat() {
    // (x:Int > 0 OR r:Real > 0) AND x < 0 AND r < 0  ->  both disjuncts are
    // theory-false, so the disjunction is unsat. Exercises BOTH the integer and
    // real theory oracles in the combined loop (QF_LIRA), through the dispatcher.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let r = real_var(&mut arena, "r");
    let izero = arena.int_const(0);
    let rzero = arena.real_const(Rational::integer(0));
    let x_pos = arena.int_gt(x, izero).unwrap();
    let r_pos = arena.real_gt(r, rzero).unwrap();
    let disj = arena.or(x_pos, r_pos).unwrap();
    let x_neg = arena.int_lt(x, izero).unwrap();
    let r_neg = arena.real_lt(r, rzero).unwrap();

    assert!(matches!(
        solve(&mut arena, &[disj, x_neg, r_neg], &SolverConfig::default()),
        Ok(CheckResult::Unsat)
    ));
}

#[test]
fn combined_lira_is_satisfiable_and_replayed() {
    // x:Int == 3 AND r:Real > 1 AND (x > 0 AND r > 0) -> sat; both models merge.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let r = real_var(&mut arena, "r");
    let three = arena.int_const(3);
    let izero = arena.int_const(0);
    let rone = arena.real_const(Rational::integer(1));
    let rzero = arena.real_const(Rational::integer(0));
    let x_is_3 = arena.eq(x, three).unwrap();
    let r_gt_1 = arena.real_gt(r, rone).unwrap();
    let x_pos = arena.int_gt(x, izero).unwrap();
    let r_pos = arena.real_gt(r, rzero).unwrap();
    let both = arena.and(x_pos, r_pos).unwrap();

    match solve(
        &mut arena,
        &[x_is_3, r_gt_1, both],
        &SolverConfig::default(),
    )
    .unwrap()
    {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            for &c in &[x_is_3, r_gt_1, both] {
                assert_eq!(eval(&arena, c, &assignment).unwrap(), Value::Bool(true));
            }
        }
        other => panic!("expected sat, got {other:?}"),
    }
}

#[test]
fn unsat_certificate_verifies_independently() {
    // (x == 2 OR x == 4) AND x == 3 is unsat; the lazy loop must produce a
    // refutation (skeleton + learned theory lemmas) that re-checks on its own.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let two = arena.int_const(2);
    let four = arena.int_const(4);
    let three = arena.int_const(3);
    let is2 = arena.eq(x, two).unwrap();
    let is4 = arena.eq(x, four).unwrap();
    let disj = arena.or(is2, is4).unwrap();
    let pin = arena.eq(x, three).unwrap();

    match certify_arith_dpll_unsat(&mut arena, &[disj, pin], &SolverConfig::default()).unwrap() {
        ArithDpllOutcome::Unsat(refutation) => {
            // certify_* already self-checked, but verify again explicitly.
            assert!(refutation.verify(&arena).unwrap(), "refutation must verify");
            assert!(!refutation.lemmas.is_empty(), "should have learned lemmas");
        }
        other => panic!("expected a verified unsat refutation, got {other:?}"),
    }
}

#[test]
fn implication_chain_is_satisfiable() {
    // (x > 5 => y > 10) AND x == 6 : sat, with y > 10 forced.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let five = arena.int_const(5);
    let ten = arena.int_const(10);
    let six = arena.int_const(6);
    let xgt5 = arena.int_gt(x, five).unwrap();
    let ygt10 = arena.int_gt(y, ten).unwrap();
    let imp = arena.implies(xgt5, ygt10).unwrap();
    let pin = arena.eq(x, six).unwrap();

    match solve(&mut arena, &[imp, pin], &SolverConfig::default()).unwrap() {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            assert_eq!(eval(&arena, imp, &assignment).unwrap(), Value::Bool(true));
            assert_eq!(eval(&arena, pin, &assignment).unwrap(), Value::Bool(true));
        }
        other => panic!("expected sat, got {other:?}"),
    }
}
