//! Unbounded `QF_LIA` by branch-and-bound over the exact-rational simplex.
//!
//! The key property versus bounded bit-blasting: this decides `unsat` soundly
//! (integer-infeasible systems whose *real* relaxation is feasible), and reasons
//! about unbounded integer magnitudes. Every `sat` is replayed via the
//! evaluator.

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, check_with_lia_simplex};

fn int_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Int).unwrap();
    arena.var(sym)
}

#[test]
fn linear_system_is_satisfied_and_replayed() {
    // x + y == 10  AND  x - y == 2   ->  x = 6, y = 4.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let ten = arena.int_const(10);
    let two = arena.int_const(2);
    let sum = arena.int_add(x, y).unwrap();
    let diff = arena.int_sub(x, y).unwrap();
    let c1 = arena.eq(sum, ten).unwrap();
    let c2 = arena.eq(diff, two).unwrap();

    match check_with_lia_simplex(&arena, &[c1, c2]).unwrap() {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            for &c in &[c1, c2] {
                assert_eq!(eval(&arena, c, &assignment).unwrap(), Value::Bool(true));
            }
        }
        other => panic!("expected sat, got {other:?}"),
    }
}

#[test]
fn requires_branching_then_finds_integer_point() {
    // 2x >= 1  AND  2x <= 3 : the real relaxation allows x in [0.5, 1.5], so the
    // simplex returns a fractional vertex; branch-and-bound must find x = 1.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let two = arena.int_const(2);
    let one = arena.int_const(1);
    let three = arena.int_const(3);
    let two_x = arena.int_mul(two, x).unwrap();
    let lo = arena.int_ge(two_x, one).unwrap();
    let hi = arena.int_le(two_x, three).unwrap();

    match check_with_lia_simplex(&arena, &[lo, hi]).unwrap() {
        CheckResult::Sat(model) => {
            assert_eq!(model.get(arena_symbol(&arena, "x")), Some(Value::Int(1)));
        }
        other => panic!("expected sat (x=1), got {other:?}"),
    }
}

#[test]
fn integer_infeasible_but_real_feasible_is_unsat() {
    // 2x == 1 has no integer solution, though the real relaxation x = 0.5 is
    // feasible. Bounded bit-blasting could only say `unknown` here; the simplex
    // branch-and-bound proves `unsat`.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let two = arena.int_const(2);
    let one = arena.int_const(1);
    let two_x = arena.int_mul(two, x).unwrap();
    let eq = arena.eq(two_x, one).unwrap();

    assert!(matches!(
        check_with_lia_simplex(&arena, &[eq]).unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn empty_integer_interval_is_unsat() {
    // x > 0 AND x < 1 : no integer between.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let gt = arena.int_gt(x, zero).unwrap();
    let lt = arena.int_lt(x, one).unwrap();

    assert!(matches!(
        check_with_lia_simplex(&arena, &[gt, lt]).unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn unbounded_magnitude_is_handled() {
    // x == 1000000  AND  x > 999999 : large integer, sat at x = 1_000_000.
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let big = arena.int_const(1_000_000);
    let near = arena.int_const(999_999);
    let eq = arena.eq(x, big).unwrap();
    let gt = arena.int_gt(x, near).unwrap();

    match check_with_lia_simplex(&arena, &[eq, gt]).unwrap() {
        CheckResult::Sat(model) => {
            assert_eq!(
                model.get(arena_symbol(&arena, "x")),
                Some(Value::Int(1_000_000))
            );
        }
        other => panic!("expected sat, got {other:?}"),
    }
}

/// Looks up a declared symbol id by name (test helper).
fn arena_symbol(arena: &TermArena, name: &str) -> axeyum_ir::SymbolId {
    arena
        .symbols()
        .find(|(_, n, _)| *n == name)
        .map(|(id, _, _)| id)
        .expect("symbol declared")
}
