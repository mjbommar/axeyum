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

// --- Lexicographic multi-objective optimization (P4.3) ------------------------

use axeyum_solver::{LexObjective, LexOutcome, optimize_lia_lexicographic};

/// Helper: `0 <= v <= 10`.
fn bound_0_10(arena: &mut TermArena, v: TermId) -> [TermId; 2] {
    let zero = arena.int_const(0);
    let ten = arena.int_const(10);
    [
        arena.int_ge(v, zero).unwrap(),
        arena.int_le(v, ten).unwrap(),
    ]
}

/// `max x` then `max y` subject to `0≤x,y≤10 ∧ x+y≤12`: x pins to 10, then y≤2.
#[test]
fn lexicographic_max_then_max() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let [xl, xh] = bound_0_10(&mut arena, x);
    let [yl, yh] = bound_0_10(&mut arena, y);
    let sum = arena.int_add(x, y).unwrap();
    let twelve = arena.int_const(12);
    let cap = arena.int_le(sum, twelve).unwrap();
    let asserts = [xl, xh, yl, yh, cap];
    let objs = [
        LexObjective {
            objective: x,
            maximize: true,
        },
        LexObjective {
            objective: y,
            maximize: true,
        },
    ];
    assert_eq!(
        optimize_lia_lexicographic(&mut arena, &asserts, &objs).unwrap(),
        LexOutcome::Optimal(vec![10, 2])
    );
}

/// Order matters: `max y` then `max x` on the same problem gives y=10, x=2.
#[test]
fn lexicographic_order_matters() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let [xl, xh] = bound_0_10(&mut arena, x);
    let [yl, yh] = bound_0_10(&mut arena, y);
    let sum = arena.int_add(x, y).unwrap();
    let twelve = arena.int_const(12);
    let cap = arena.int_le(sum, twelve).unwrap();
    let asserts = [xl, xh, yl, yh, cap];
    let objs = [
        LexObjective {
            objective: y,
            maximize: true,
        },
        LexObjective {
            objective: x,
            maximize: true,
        },
    ];
    assert_eq!(
        optimize_lia_lexicographic(&mut arena, &asserts, &objs).unwrap(),
        LexOutcome::Optimal(vec![10, 2]) // y=10 first, then x=2
    );
}

/// Mixed direction: `max x` then `min y` → x=10, y=0 (min y under x+y≤12, y≥0).
#[test]
fn lexicographic_max_then_min() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let [xl, xh] = bound_0_10(&mut arena, x);
    let [yl, yh] = bound_0_10(&mut arena, y);
    let sum = arena.int_add(x, y).unwrap();
    let twelve = arena.int_const(12);
    let cap = arena.int_le(sum, twelve).unwrap();
    let asserts = [xl, xh, yl, yh, cap];
    let objs = [
        LexObjective {
            objective: x,
            maximize: true,
        },
        LexObjective {
            objective: y,
            maximize: false,
        },
    ];
    assert_eq!(
        optimize_lia_lexicographic(&mut arena, &asserts, &objs).unwrap(),
        LexOutcome::Optimal(vec![10, 0])
    );
}

/// A lexicographic chain stops at the first non-finite objective: maximizing an
/// upward-unbounded `x` (only `x ≥ 0`) stops at index 0 with no prefix.
#[test]
fn lexicographic_stops_on_unbounded() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let zero = arena.int_const(0);
    let xl = arena.int_ge(x, zero).unwrap(); // x ≥ 0, no upper bound
    let objs = [
        LexObjective {
            objective: x,
            maximize: true,
        },
        LexObjective {
            objective: y,
            maximize: true,
        },
    ];
    match optimize_lia_lexicographic(&mut arena, &[xl], &objs).unwrap() {
        LexOutcome::Stopped {
            index,
            prefix,
            outcome,
        } => {
            assert_eq!(index, 0);
            assert!(prefix.is_empty());
            assert_eq!(outcome, OptOutcome::Unbounded);
        }
        LexOutcome::Optimal(vals) => {
            panic!("expected Stopped at unbounded objective, got Optimal({vals:?})")
        }
    }
}

use axeyum_solver::{BvLexObjective, optimize_bv_lexicographic};

/// BV lexicographic (unsigned): `max x` then `max y` s.t. `x,y ≤u 10 ∧ x+y ≤u 12`
/// over BV8 → x=10, y=2.
#[test]
fn lexicographic_bv_unsigned() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let twelve = arena.bv_const(8, 12).unwrap();
    let xh = arena.bv_ule(x, ten).unwrap();
    let yh = arena.bv_ule(y, ten).unwrap();
    let sum = arena.bv_add(x, y).unwrap(); // no wrap: x,y ≤ 10 ⇒ sum ≤ 20 < 256
    let cap = arena.bv_ule(sum, twelve).unwrap();
    let objs = [
        BvLexObjective {
            objective: x,
            signed: false,
            maximize: true,
        },
        BvLexObjective {
            objective: y,
            signed: false,
            maximize: true,
        },
    ];
    assert_eq!(
        optimize_bv_lexicographic(&mut arena, &[xh, yh, cap], &objs).unwrap(),
        LexOutcome::Optimal(vec![10, 2])
    );
}

/// BV lexicographic (signed): `min x` then `max y` over BV8 s.t. `x ≥s -5 ∧ y ≤s 7`
/// → x=-5, y=7 (independent objectives, signed pinning).
#[test]
fn lexicographic_bv_signed() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let neg5 = arena.bv_const(8, 251).unwrap(); // -5 in two's complement (BV8)
    let seven = arena.bv_const(8, 7).unwrap();
    let xlo = arena.bv_sge(x, neg5).unwrap();
    let yhi = arena.bv_sle(y, seven).unwrap();
    let objs = [
        BvLexObjective {
            objective: x,
            signed: true,
            maximize: false,
        },
        BvLexObjective {
            objective: y,
            signed: true,
            maximize: true,
        },
    ];
    assert_eq!(
        optimize_bv_lexicographic(&mut arena, &[xlo, yhi], &objs).unwrap(),
        LexOutcome::Optimal(vec![-5, 7])
    );
}

use axeyum_solver::optimize_lia_box;

/// Box (independent) optimization differs from lexicographic: for
/// `0≤x,y≤10 ∧ x+y≤12`, box `max x`/`max y` each reach 10 independently ([10,10]),
/// whereas lex pins x first → [10,2].
#[test]
fn box_optimization_is_independent_unlike_lex() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let [xl, xh] = bound_0_10(&mut arena, x);
    let [yl, yh] = bound_0_10(&mut arena, y);
    let sum = arena.int_add(x, y).unwrap();
    let twelve = arena.int_const(12);
    let cap = arena.int_le(sum, twelve).unwrap();
    let asserts = [xl, xh, yl, yh, cap];
    let objs = [
        LexObjective {
            objective: x,
            maximize: true,
        },
        LexObjective {
            objective: y,
            maximize: true,
        },
    ];
    assert_eq!(
        optimize_lia_box(&mut arena, &asserts, &objs).unwrap(),
        vec![OptOutcome::Optimal(10), OptOutcome::Optimal(10)]
    );
    // Same problem, lexicographic: x pins to 10, then y ≤ 2.
    assert_eq!(
        optimize_lia_lexicographic(&mut arena, &asserts, &objs).unwrap(),
        LexOutcome::Optimal(vec![10, 2])
    );
}

use axeyum_solver::{ParetoOutcome, optimize_lia_pareto};

/// Pareto front of `max x, max y` s.t. `0≤x,y≤3 ∧ x+y≤4`: the non-dominated tuples
/// are exactly {(3,1),(2,2),(1,3)} (on the x+y=4 frontier within the box).
#[test]
fn pareto_front_two_objectives() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let y = int_var(&mut arena, "y");
    let zero = arena.int_const(0);
    let three = arena.int_const(3);
    let four = arena.int_const(4);
    let xl = arena.int_ge(x, zero).unwrap();
    let xh = arena.int_le(x, three).unwrap();
    let yl = arena.int_ge(y, zero).unwrap();
    let yh = arena.int_le(y, three).unwrap();
    let sum = arena.int_add(x, y).unwrap();
    let cap = arena.int_le(sum, four).unwrap();
    let asserts = [xl, xh, yl, yh, cap];
    let objs = [
        LexObjective {
            objective: x,
            maximize: true,
        },
        LexObjective {
            objective: y,
            maximize: true,
        },
    ];
    let ParetoOutcome::Complete(mut points) =
        optimize_lia_pareto(&mut arena, &asserts, &objs).unwrap()
    else {
        panic!("expected a complete Pareto front");
    };
    points.sort();
    assert_eq!(points, vec![vec![1, 3], vec![2, 2], vec![3, 1]]);
}

/// A single objective has a one-point Pareto front: just its optimum.
#[test]
fn pareto_single_objective_is_the_optimum() {
    let mut arena = TermArena::new();
    let x = int_var(&mut arena, "x");
    let [xl, xh] = bound_0_10(&mut arena, x);
    let objs = [LexObjective {
        objective: x,
        maximize: true,
    }];
    assert_eq!(
        optimize_lia_pareto(&mut arena, &[xl, xh], &objs).unwrap(),
        ParetoOutcome::Complete(vec![vec![10]])
    );
}
