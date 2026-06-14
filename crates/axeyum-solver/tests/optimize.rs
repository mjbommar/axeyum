//! Linear integer optimization (optimization modulo theories, integer slice).

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{
    OptOutcome, maximize_bv, maximize_bv_signed, maximize_lia, minimize_bv, minimize_bv_signed,
    minimize_lia,
};

fn int_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Int).unwrap();
    arena.var(sym)
}

#[test]
fn maximize_within_bounds() {
    // maximize x s.t. 0 <= x <= 10  ->  10.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = arena.int_const(0);
    let ten = arena.int_const(10);
    let lo = arena.int_ge(x, zero).unwrap();
    let hi = arena.int_le(x, ten).unwrap();

    assert_eq!(
        maximize_lia(&mut arena, &[lo, hi], x).unwrap(),
        OptOutcome::Optimal(10)
    );
}

#[test]
fn minimize_within_bounds() {
    // minimize x s.t. 3 <= x <= 100  ->  3.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let three = arena.int_const(3);
    let hundred = arena.int_const(100);
    let lo = arena.int_ge(x, three).unwrap();
    let hi = arena.int_le(x, hundred).unwrap();

    assert_eq!(
        minimize_lia(&mut arena, &[lo, hi], x).unwrap(),
        OptOutcome::Optimal(3)
    );
}

#[test]
fn maximize_linear_objective() {
    // maximize x + y s.t. 0<=x<=3, 0<=y<=4  ->  7.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let zero = arena.int_const(0);
    let three = arena.int_const(3);
    let four = arena.int_const(4);
    let xlo = arena.int_ge(x, zero).unwrap();
    let xhi = arena.int_le(x, three).unwrap();
    let ylo = arena.int_ge(y, zero).unwrap();
    let yhi = arena.int_le(y, four).unwrap();
    let objective = arena.int_add(x, y).unwrap();

    assert_eq!(
        maximize_lia(&mut arena, &[xlo, xhi, ylo, yhi], objective).unwrap(),
        OptOutcome::Optimal(7)
    );
}

#[test]
fn maximize_over_disjunctive_constraints() {
    // maximize x s.t. (x <= 5 OR x == 8) AND x <= 8  ->  8 (the disjunct's island
    // beats the <=5 region). Requires the Boolean-structured oracle.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = arena.int_const(0);
    let five = arena.int_const(5);
    let eight = arena.int_const(8);
    let le5 = arena.int_le(x, five).unwrap();
    let is8 = arena.eq(x, eight).unwrap();
    let disj = arena.or(le5, is8).unwrap();
    let lo = arena.int_ge(x, zero).unwrap();
    let hi = arena.int_le(x, eight).unwrap();

    assert_eq!(
        maximize_lia(&mut arena, &[disj, lo, hi], x).unwrap(),
        OptOutcome::Optimal(8)
    );
}

#[test]
fn unbounded_objective_is_detected() {
    // maximize x s.t. x >= 0  ->  unbounded.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = arena.int_const(0);
    let lo = arena.int_ge(x, zero).unwrap();

    assert_eq!(
        maximize_lia(&mut arena, &[lo], x).unwrap(),
        OptOutcome::Unbounded
    );
}

#[test]
fn infeasible_constraints_have_no_optimum() {
    // 5 <= x <= 2 is unsatisfiable.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let two = arena.int_const(2);
    let five = arena.int_const(5);
    let lo = arena.int_ge(x, five).unwrap();
    let hi = arena.int_le(x, two).unwrap();

    assert_eq!(
        maximize_lia(&mut arena, &[lo, hi], x).unwrap(),
        OptOutcome::Infeasible
    );
}

#[test]
fn bv_maximize_respects_upper_bound() {
    // maximize unsigned x:BV8 s.t. x <=u 200  ->  200.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let lim = arena.bv_const(8, 200).unwrap();
    let c = arena.bv_ule(x, lim).unwrap();
    assert_eq!(
        maximize_bv(&mut arena, &[c], x).unwrap(),
        OptOutcome::Optimal(200)
    );
}

#[test]
fn bv_minimize_respects_lower_bound() {
    // minimize unsigned x:BV8 s.t. x >=u 50  ->  50.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let lim = arena.bv_const(8, 50).unwrap();
    let c = arena.bv_uge(x, lim).unwrap();
    assert_eq!(
        minimize_bv(&mut arena, &[c], x).unwrap(),
        OptOutcome::Optimal(50)
    );
}

#[test]
fn bv_maximize_unconstrained_is_all_ones() {
    // maximize unsigned x:BV8 with no constraints  ->  255.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    assert_eq!(
        maximize_bv(&mut arena, &[], x).unwrap(),
        OptOutcome::Optimal(255)
    );
}

#[test]
fn bv_infeasible_has_no_optimum() {
    // x <=u 10 AND x >=u 20 is unsatisfiable.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let twenty = arena.bv_const(8, 20).unwrap();
    let lo = arena.bv_ule(x, ten).unwrap();
    let hi = arena.bv_uge(x, twenty).unwrap();
    assert_eq!(
        maximize_bv(&mut arena, &[lo, hi], x).unwrap(),
        OptOutcome::Infeasible
    );
}

#[test]
fn bv_signed_maximize_respects_upper_bound() {
    // maximize signed x:BV8 s.t. x <=s 100  ->  100.
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let lim = arena.bv_const(8, 100).unwrap();
    let c = arena.bv_sle(x, lim).unwrap();
    assert_eq!(
        maximize_bv_signed(&mut arena, &[c], x).unwrap(),
        OptOutcome::Optimal(100)
    );
}

#[test]
fn bv_signed_minimize_respects_lower_bound() {
    // minimize signed x:BV8 s.t. x >=s -50  ->  -50. (-50 as BV8 = 206)
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let lim = arena.bv_const(8, 206).unwrap(); // two's complement of -50
    let c = arena.bv_sge(x, lim).unwrap();
    assert_eq!(
        minimize_bv_signed(&mut arena, &[c], x).unwrap(),
        OptOutcome::Optimal(-50)
    );
}

#[test]
fn bv_signed_unconstrained_spans_the_signed_range() {
    // signed BV8 ranges over [-128, 127].
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    assert_eq!(
        maximize_bv_signed(&mut arena, &[], x).unwrap(),
        OptOutcome::Optimal(127)
    );
    let mut arena2 = TermArena::new();
    let y = arena2.bv_var("y", 8).unwrap();
    assert_eq!(
        minimize_bv_signed(&mut arena2, &[], y).unwrap(),
        OptOutcome::Optimal(-128)
    );
}
