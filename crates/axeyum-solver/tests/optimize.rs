//! Linear integer optimization (optimization modulo theories, integer slice).

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{OptOutcome, maximize_lia, minimize_lia};

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
