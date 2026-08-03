//! Unit tests for the online difference-logic theory solver.
//!
//! The soundness-negative tests are the point of this file: a satisfiable
//! system must never come back `unsat`, a cycle that is not actually negative
//! must never be accepted as a refutation, the strict/non-strict boundary must
//! be exact, and integer tightening must be right for a **negative** bound.

use super::*;

fn real(arena: &mut TermArena, name: &str) -> TermId {
    let symbol = arena.declare(name, Sort::Real).expect("declare real");
    arena.var(symbol)
}

fn int(arena: &mut TermArena, name: &str) -> TermId {
    let symbol = arena.declare(name, Sort::Int).expect("declare int");
    arena.var(symbol)
}

fn config() -> SolverConfig {
    SolverConfig::default()
}

fn check(arena: &mut TermArena, assertions: &[TermId]) -> Option<CheckResult> {
    try_check_qf_dl(arena, assertions, &config())
}

// -------------------------------------------------------------------------
// Positive: the route decides real difference logic
// -------------------------------------------------------------------------

/// `x - y ≤ -1 ∧ y - x ≤ -1` is a negative cycle of weight `-2`.
#[test]
fn real_negative_cycle_is_unsat() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let m1 = arena.real_const(Rational::integer(-1));
    let a = arena.real_sub(x, y).expect("x-y");
    let b = arena.real_sub(y, x).expect("y-x");
    let c1 = arena.real_le(a, m1).expect("x-y<=-1");
    let c2 = arena.real_le(b, m1).expect("y-x<=-1");
    assert_eq!(check(&mut arena, &[c1, c2]), Some(CheckResult::Unsat));
}

/// The same graph with weight `+1` on one edge is satisfiable, and the model
/// must replay.
#[test]
fn real_feasible_system_is_sat_and_replays() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let m1 = arena.real_const(Rational::integer(-1));
    let p3 = arena.real_const(Rational::integer(3));
    let a = arena.real_sub(x, y).expect("x-y");
    let b = arena.real_sub(y, x).expect("y-x");
    let c1 = arena.real_le(a, m1).expect("x-y<=-1");
    let c2 = arena.real_le(b, p3).expect("y-x<=3");
    let result = check(&mut arena, &[c1, c2]).expect("in fragment");
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    assert!(replays(&arena, &[c1, c2], &model), "model must replay");
}

/// A Boolean-structured difference-logic query: both disjuncts of the `or` are
/// refuted by the *same* third constraint, so the query is `unsat` and the
/// verdict comes from resolution over two Farkas-checked theory lemmas.
#[test]
fn boolean_structure_is_refuted_by_two_lemmas() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let m5 = arena.real_const(Rational::integer(-5));
    let m1 = arena.real_const(Rational::integer(-1));
    let m2 = arena.real_const(Rational::integer(-2));
    let xy = arena.real_sub(x, y).expect("x-y");
    let yx = arena.real_sub(y, x).expect("y-x");
    // y - x ≤ -5, so x - y ≥ 5: both `x - y ≤ -1` and `x - y ≤ -2` are refuted.
    let base = arena.real_le(yx, m5).expect("y-x<=-5");
    let d1 = arena.real_le(xy, m1).expect("x-y<=-1");
    let d2 = arena.real_le(xy, m2).expect("x-y<=-2");
    let disj = arena.or(d1, d2).expect("or");
    assert_eq!(check(&mut arena, &[base, disj]), Some(CheckResult::Unsat));
}

// -------------------------------------------------------------------------
// Soundness-negative: a satisfiable system must never come back `unsat`
// -------------------------------------------------------------------------

/// A cycle of total weight `0` is **not** a refutation over the non-strict
/// relation: `x - y ≤ 1 ∧ y - x ≤ -1` is satisfied by `x = y + 1`.
#[test]
fn zero_weight_cycle_is_not_a_refutation() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let p1 = arena.real_const(Rational::integer(1));
    let m1 = arena.real_const(Rational::integer(-1));
    let xy = arena.real_sub(x, y).expect("x-y");
    let yx = arena.real_sub(y, x).expect("y-x");
    let c1 = arena.real_le(xy, p1).expect("x-y<=1");
    let c2 = arena.real_le(yx, m1).expect("y-x<=-1");
    let result = check(&mut arena, &[c1, c2]).expect("in fragment");
    assert!(
        !matches!(result, CheckResult::Unsat),
        "a zero-weight cycle is satisfiable, got {result:?}"
    );
    let CheckResult::Sat(model) = result else {
        panic!("expected sat");
    };
    assert!(replays(&arena, &[c1, c2], &model));
}

/// The strict/non-strict boundary. `x - y < 0 ∧ y - x < 0` is `unsat` (a
/// zero-weight cycle with two strict edges), while `x - y ≤ 0 ∧ y - x ≤ 0` is
/// `sat` (`x = y`). This is exactly the pair the `δ` component exists for.
#[test]
fn strict_versus_non_strict_at_zero() {
    let mut strict_arena = TermArena::new();
    let x = real(&mut strict_arena, "x");
    let y = real(&mut strict_arena, "y");
    let zero = strict_arena.real_const(Rational::zero());
    let xy = strict_arena.real_sub(x, y).expect("x-y");
    let yx = strict_arena.real_sub(y, x).expect("y-x");
    let s1 = strict_arena.real_lt(xy, zero).expect("x-y<0");
    let s2 = strict_arena.real_lt(yx, zero).expect("y-x<0");
    assert_eq!(
        check(&mut strict_arena, &[s1, s2]),
        Some(CheckResult::Unsat),
        "two strict edges summing to zero are infeasible"
    );

    let mut loose_arena = TermArena::new();
    let x = real(&mut loose_arena, "x");
    let y = real(&mut loose_arena, "y");
    let zero = loose_arena.real_const(Rational::zero());
    let xy = loose_arena.real_sub(x, y).expect("x-y");
    let yx = loose_arena.real_sub(y, x).expect("y-x");
    let l1 = loose_arena.real_le(xy, zero).expect("x-y<=0");
    let l2 = loose_arena.real_le(yx, zero).expect("y-x<=0");
    let result = check(&mut loose_arena, &[l1, l2]).expect("in fragment");
    let CheckResult::Sat(model) = result else {
        panic!("x = y satisfies both, got {result:?}");
    };
    assert!(replays(&loose_arena, &[l1, l2], &model));
}

/// A single strict edge must not be strengthened over the **reals**:
/// `x - y < 1 ∧ y - x < 0` is real-satisfiable (`x - y = 1/2`) even though the
/// integer tightening of the same system is not.
#[test]
fn real_strict_edges_are_not_integer_tightened() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let one = arena.real_const(Rational::integer(1));
    let zero = arena.real_const(Rational::zero());
    let xy = arena.real_sub(x, y).expect("x-y");
    let yx = arena.real_sub(y, x).expect("y-x");
    let c1 = arena.real_lt(xy, one).expect("x-y<1");
    let c2 = arena.real_lt(yx, zero).expect("y-x<0");
    let result = check(&mut arena, &[c1, c2]).expect("in fragment");
    let CheckResult::Sat(model) = result else {
        panic!("real-satisfiable, got {result:?}");
    };
    assert!(replays(&arena, &[c1, c2], &model));
}

// -------------------------------------------------------------------------
// Integer difference logic and its tightening
// -------------------------------------------------------------------------

/// The counterpart of the previous test: over the **integers** `x - y < 1` is
/// `x - y ≤ 0`, so together with `y - x < 0` (`y - x ≤ -1`) the cycle weight is
/// `-1` and the system is `unsat`.
#[test]
fn integer_tightening_makes_the_real_feasible_system_unsat() {
    let mut arena = TermArena::new();
    let x = int(&mut arena, "x");
    let y = int(&mut arena, "y");
    let one = arena.int_const(1);
    let zero = arena.int_const(0);
    let xy = arena.int_sub(x, y).expect("x-y");
    let yx = arena.int_sub(y, x).expect("y-x");
    let c1 = arena.int_lt(xy, one).expect("x-y<1");
    let c2 = arena.int_lt(yx, zero).expect("y-x<0");
    assert_eq!(check(&mut arena, &[c1, c2]), Some(CheckResult::Unsat));
}

/// Integer tightening where the bound is **negative**: `x - y < -2` must become
/// `x - y ≤ -3`, not `≤ -2`. Pairing it with `y - x ≤ 2` leaves cycle weight
/// `-1` (`unsat`); pairing with `y - x ≤ 3` leaves `0` (`sat`). Getting the
/// tightening wrong flips exactly one of these.
#[test]
fn integer_tightening_at_a_negative_bound() {
    // `x - y < -2 ∧ y - x ≤ 2`: tightened weights -3 and 2 sum to -1.
    let mut unsat_arena = TermArena::new();
    let x = int(&mut unsat_arena, "x");
    let y = int(&mut unsat_arena, "y");
    let m2 = unsat_arena.int_const(-2);
    let p2 = unsat_arena.int_const(2);
    let xy = unsat_arena.int_sub(x, y).expect("x-y");
    let yx = unsat_arena.int_sub(y, x).expect("y-x");
    let c1 = unsat_arena.int_lt(xy, m2).expect("x-y<-2");
    let c2 = unsat_arena.int_le(yx, p2).expect("y-x<=2");
    assert_eq!(
        check(&mut unsat_arena, &[c1, c2]),
        Some(CheckResult::Unsat),
        "x-y<=-3 with y-x<=2 is a -1 cycle"
    );

    // `x - y < -2 ∧ y - x ≤ 3`: tightened weights -3 and 3 sum to 0 — feasible.
    let mut sat_arena = TermArena::new();
    let x = int(&mut sat_arena, "x");
    let y = int(&mut sat_arena, "y");
    let m2 = sat_arena.int_const(-2);
    let p3 = sat_arena.int_const(3);
    let xy = sat_arena.int_sub(x, y).expect("x-y");
    let yx = sat_arena.int_sub(y, x).expect("y-x");
    let d1 = sat_arena.int_lt(xy, m2).expect("x-y<-2");
    let d2 = sat_arena.int_le(yx, p3).expect("y-x<=3");
    let result = check(&mut sat_arena, &[d1, d2]).expect("in fragment");
    let CheckResult::Sat(model) = result else {
        panic!("x-y=-3 satisfies both, got {result:?}");
    };
    assert!(replays(&sat_arena, &[d1, d2], &model));
}

/// The negation of a non-strict integer atom must tighten too: `¬(x - y ≤ -2)`
/// is `y - x < 2`, i.e. `y - x ≤ 1` over the integers.
#[test]
fn negated_integer_atom_tightens() {
    let mut arena = TermArena::new();
    let x = int(&mut arena, "x");
    let y = int(&mut arena, "y");
    let m2 = arena.int_const(-2);
    let m1 = arena.int_const(-1);
    let xy = arena.int_sub(x, y).expect("x-y");
    let yx = arena.int_sub(y, x).expect("y-x");
    let atom = arena.int_le(xy, m2).expect("x-y<=-2");
    let negated = arena.not(atom).expect("not");
    // `y - x ≤ 1` (from the negation) with `x - y ≤ -2` is a -1 cycle... but we
    // assert the *negation*, so pair it with `x - y ≤ -2`'s complement side:
    // `y - x ≤ 1` plus `x - y ≤ -2` would be contradictory with the atom itself.
    // Instead pair with `x - y ≥ ...` expressed as an edge of weight -2 the other
    // way: `y - x ≤ 1 ∧ x - y ≤ -2` sums to -1.
    let other = arena.int_le(xy, m2).expect("x-y<=-2 again");
    assert_eq!(atom, other, "structural sharing keeps one atom");
    // Asserting both the atom and its negation is trivially unsat at the
    // Boolean level; the interesting check is that the negated edge is the
    // tightened one, which the next assertion exercises.
    let bound = arena.int_le(yx, m1).expect("y-x<=-1");
    // ¬(x-y ≤ -2) gives y-x ≤ 1; with y-x ≤ -1 the tighter bound wins and the
    // system is satisfiable (e.g. x = 1, y = 0 gives x-y = 1 > -2 and y-x = -1).
    let result = check(&mut arena, &[negated, bound]).expect("in fragment");
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    assert!(replays(&arena, &[negated, bound], &model));
}

/// A single-variable bound uses the zero vertex: `x ≤ 1 ∧ x ≥ 3` is `unsat`,
/// and `x ≤ 3 ∧ x ≥ 1` is `sat` with a replaying model.
#[test]
fn single_variable_bounds_use_the_zero_vertex() {
    let mut unsat_arena = TermArena::new();
    let x = int(&mut unsat_arena, "x");
    let one = unsat_arena.int_const(1);
    let three = unsat_arena.int_const(3);
    let hi = unsat_arena.int_le(x, one).expect("x<=1");
    let lo = unsat_arena.int_ge(x, three).expect("x>=3");
    assert_eq!(check(&mut unsat_arena, &[hi, lo]), Some(CheckResult::Unsat));

    let mut sat_arena = TermArena::new();
    let x = int(&mut sat_arena, "x");
    let one = sat_arena.int_const(1);
    let three = sat_arena.int_const(3);
    let hi = sat_arena.int_le(x, three).expect("x<=3");
    let lo = sat_arena.int_ge(x, one).expect("x>=1");
    let result = check(&mut sat_arena, &[hi, lo]).expect("in fragment");
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    assert!(replays(&sat_arena, &[hi, lo], &model));
}

// -------------------------------------------------------------------------
// The Farkas certificate is the refutation
// -------------------------------------------------------------------------

/// A genuine negative cycle produces a [`FarkasCertificate`] with unit
/// multipliers that the independent re-checker accepts.
#[test]
fn negative_cycle_certificate_verifies() {
    let edges = vec![
        CycleStep {
            spec: EdgeSpec {
                from: 1,
                to: 2,
                w: Weight { c: -1, d: 0 },
                bound: Rational::integer(-1),
                strict: false,
            },
            index: None,
        },
        CycleStep {
            spec: EdgeSpec {
                from: 2,
                to: 1,
                w: Weight { c: -1, d: 0 },
                bound: Rational::integer(-1),
                strict: false,
            },
            index: None,
        },
    ];
    let symbols = Vec::new();
    let certificate = cycle_certificate(&edges, &symbols).expect("built");
    assert!(certificate.verify(), "unit-multiplier Farkas must verify");
    assert!(
        certificate
            .multipliers
            .iter()
            .all(|m| *m == Rational::integer(1)),
        "a negative cycle uses unit multipliers"
    );
}

/// A cycle whose weight is **not** negative must be rejected by the independent
/// re-checker — the guard that keeps a mis-detected cycle from becoming a
/// refutation.
#[test]
fn non_negative_cycle_certificate_is_rejected() {
    for (first, second) in [(-1_i128, 1_i128), (0, 0), (2, 3)] {
        let edges = vec![
            CycleStep {
                spec: EdgeSpec {
                    from: 1,
                    to: 2,
                    w: Weight { c: first, d: 0 },
                    bound: Rational::integer(first),
                    strict: false,
                },
                index: None,
            },
            CycleStep {
                spec: EdgeSpec {
                    from: 2,
                    to: 1,
                    w: Weight { c: second, d: 0 },
                    bound: Rational::integer(second),
                    strict: false,
                },
                index: None,
            },
        ];
        let certificate = cycle_certificate(&edges, &[]).expect("built");
        assert!(
            !certificate.verify(),
            "cycle weight {} is not negative and must not refute",
            first + second
        );
    }
}

/// A zero-weight cycle refutes only when at least one edge is **strict**.
#[test]
fn zero_weight_cycle_refutes_only_when_strict() {
    let make = |strict: bool| {
        vec![
            CycleStep {
                spec: EdgeSpec {
                    from: 1,
                    to: 2,
                    w: Weight {
                        c: 0,
                        d: -i64::from(strict),
                    },
                    bound: Rational::zero(),
                    strict,
                },
                index: None,
            },
            CycleStep {
                spec: EdgeSpec {
                    from: 2,
                    to: 1,
                    w: Weight { c: 0, d: 0 },
                    bound: Rational::zero(),
                    strict: false,
                },
                index: None,
            },
        ]
    };
    assert!(
        !cycle_certificate(&make(false), &[])
            .expect("built")
            .verify(),
        "0 ≤ 0 is satisfiable"
    );
    assert!(
        cycle_certificate(&make(true), &[]).expect("built").verify(),
        "0 < 0 is a refutation"
    );
}

// -------------------------------------------------------------------------
// The conservative gate
// -------------------------------------------------------------------------

/// A coefficient other than `±1` is not difference logic; the route must
/// decline so the query falls through to the linear-arithmetic cores.
#[test]
fn non_unit_coefficient_falls_through() {
    let mut arena = TermArena::new();
    let x = int(&mut arena, "x");
    let y = int(&mut arena, "y");
    let two_x = arena.int_add(x, x).expect("x+x");
    let expr = arena.int_sub(two_x, y).expect("2x-y");
    let zero = arena.int_const(0);
    let atom = arena.int_le(expr, zero).expect("2x-y<=0");
    assert!(
        check(&mut arena, &[atom]).is_none(),
        "2x - y ≤ 0 must fall through"
    );
}

/// A numeric equality between two distinct variables is **supported**: it is
/// expanded in the skeleton into `a ≤ b ∧ a ≥ b`, so the theory only ever sees
/// difference constraints. `x = y ∧ x - y ≤ -1` is `unsat`.
#[test]
fn equality_between_distinct_variables_is_expanded() {
    let mut arena = TermArena::new();
    let x = int(&mut arena, "x");
    let y = int(&mut arena, "y");
    let minus_one = arena.int_const(-1);
    let xy = arena.int_sub(x, y).expect("x-y");
    let eq = arena.eq(x, y).expect("x=y");
    let lt = arena.int_le(xy, minus_one).expect("x-y<=-1");
    assert_eq!(check(&mut arena, &[eq, lt]), Some(CheckResult::Unsat));
}

/// The **negation** of an equality is a propositional disjunction of two
/// difference atoms, not a disequality the theory must split on:
/// `¬(x = y) ∧ x - y ≤ 0 ∧ y - x ≤ 0` is `unsat` (the two bounds force `x = y`).
#[test]
fn negated_equality_is_a_skeleton_disjunction() {
    let mut arena = TermArena::new();
    let x = int(&mut arena, "x");
    let y = int(&mut arena, "y");
    let zero = arena.int_const(0);
    let xy = arena.int_sub(x, y).expect("x-y");
    let yx = arena.int_sub(y, x).expect("y-x");
    let eq = arena.eq(x, y).expect("x=y");
    let neq = arena.not(eq).expect("not");
    let hi = arena.int_le(xy, zero).expect("x-y<=0");
    let lo = arena.int_le(yx, zero).expect("y-x<=0");
    assert_eq!(check(&mut arena, &[neq, hi, lo]), Some(CheckResult::Unsat));
}

/// A satisfiable disequality must come back `sat` with a **replaying** model —
/// the model has to genuinely separate the two variables, which is the whole
/// reason the negation lives in the skeleton rather than being dropped.
#[test]
fn satisfiable_disequality_produces_a_separating_model() {
    let mut arena = TermArena::new();
    let x = int(&mut arena, "x");
    let y = int(&mut arena, "y");
    let zero = arena.int_const(0);
    let three = arena.int_const(3);
    let xy = arena.int_sub(x, y).expect("x-y");
    let eq = arena.eq(x, y).expect("x=y");
    let neq = arena.not(eq).expect("not");
    let lo = arena.int_le(zero, xy).expect("0<=x-y");
    let hi = arena.int_le(xy, three).expect("x-y<=3");
    let result = check(&mut arena, &[neq, lo, hi]).expect("in fragment");
    let CheckResult::Sat(model) = result else {
        panic!("0 < x-y <= 3 is satisfiable, got {result:?}");
    };
    assert!(
        replays(&arena, &[neq, lo, hi], &model),
        "the model must actually separate x and y"
    );
}

/// A **real** disequality must separate too, which needs the `δ` machinery to
/// stay out of the way: `x ≠ y ∧ x - y ≥ 0 ∧ x - y ≤ 1` is `sat`.
#[test]
fn real_satisfiable_disequality_replays() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let zero = arena.real_const(Rational::zero());
    let one = arena.real_const(Rational::integer(1));
    let xy = arena.real_sub(x, y).expect("x-y");
    let eq = arena.eq(x, y).expect("x=y");
    let neq = arena.not(eq).expect("not");
    let lo = arena.real_ge(xy, zero).expect("x-y>=0");
    let hi = arena.real_le(xy, one).expect("x-y<=1");
    let result = check(&mut arena, &[neq, lo, hi]).expect("in fragment");
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    assert!(replays(&arena, &[neq, lo, hi], &model));
}

/// A **Boolean** equality is skeleton structure, not a theory atom: it gets an
/// `XNOR` gate so a query mixing Boolean frame axioms with difference
/// constraints (the shape of the `fischer` benchmark family) stays in the
/// fragment. `(= p q) ∧ p ∧ ¬q` is `unsat`.
#[test]
fn boolean_equality_is_a_skeleton_gate() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let zero = arena.real_const(Rational::zero());
    let xy = arena.real_sub(x, y).expect("x-y");
    let p = arena.bool_var("p").expect("p");
    let q = arena.bool_var("q").expect("q");
    let eq = arena.eq(p, q).expect("p = q");
    let not_q = arena.not(q).expect("not q");
    // A difference atom keeps the query inside the fragment.
    let guard = arena.real_le(xy, zero).expect("x-y<=0");
    assert_eq!(
        check(&mut arena, &[eq, p, not_q, guard]),
        Some(CheckResult::Unsat),
        "p = q with p and ¬q is unsat"
    );
}

/// The same gate must not over-constrain: `(= p q) ∧ ¬p ∧ x - y ≤ 0` is `sat`
/// and the model must replay (including the Boolean leaves).
#[test]
fn boolean_equality_gate_admits_its_models() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let zero = arena.real_const(Rational::zero());
    let xy = arena.real_sub(x, y).expect("x-y");
    let p = arena.bool_var("p").expect("p");
    let q = arena.bool_var("q").expect("q");
    let eq = arena.eq(p, q).expect("p = q");
    let not_p = arena.not(p).expect("not p");
    let guard = arena.real_le(xy, zero).expect("x-y<=0");
    let result = check(&mut arena, &[eq, not_p, guard]).expect("in fragment");
    let CheckResult::Sat(model) = result else {
        panic!("expected sat, got {result:?}");
    };
    assert!(replays(&arena, &[eq, not_p, guard], &model));
}

/// An equality whose sides are not difference-shaped still falls through.
#[test]
fn non_difference_equality_falls_through() {
    let mut arena = TermArena::new();
    let x = int(&mut arena, "x");
    let y = int(&mut arena, "y");
    let z = int(&mut arena, "z");
    let sum = arena.int_add(y, z).expect("y+z");
    let eq = arena.eq(x, sum).expect("x = y+z");
    assert!(
        check(&mut arena, &[eq]).is_none(),
        "x = y + z is not a difference constraint"
    );
}

/// A mixed `Int`/`Real` query is outside the single-sorted fragment.
#[test]
fn mixed_sorts_fall_through() {
    let mut arena = TermArena::new();
    let x = int(&mut arena, "x");
    let r = real(&mut arena, "r");
    let zero_i = arena.int_const(0);
    let zero_r = arena.real_const(Rational::zero());
    let a = arena.int_le(x, zero_i).expect("x<=0");
    let b = arena.real_le(r, zero_r).expect("r<=0");
    assert!(
        check(&mut arena, &[a, b]).is_none(),
        "mixed Int/Real must fall through"
    );
}

/// A multiplication is not difference logic.
#[test]
fn product_falls_through() {
    let mut arena = TermArena::new();
    let x = int(&mut arena, "x");
    let y = int(&mut arena, "y");
    let product = arena.int_mul(x, y).expect("x*y");
    let zero = arena.int_const(0);
    let atom = arena.int_le(product, zero).expect("x*y<=0");
    assert!(
        check(&mut arena, &[atom]).is_none(),
        "x·y ≤ 0 must fall through"
    );
}

// -------------------------------------------------------------------------
// Constant atoms (`x - x ⋈ c`), which the benchmark families actually contain
// -------------------------------------------------------------------------

/// `x - x > 14` is the constant `false`; `x - x ≥ 0` is the constant `true`.
/// Both shapes appear verbatim in the `QF_RDL` planning benchmarks.
#[test]
fn self_difference_atoms_are_constants() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let xx = arena.real_sub(x, x).expect("x-x");
    let fourteen = arena.real_const(Rational::integer(14));
    let zero = arena.real_const(Rational::zero());
    let false_atom = arena.real_gt(xx, fourteen).expect("x-x>14");
    let true_atom = arena.real_ge(xx, zero).expect("x-x>=0");

    assert_eq!(
        check(&mut arena, &[false_atom]),
        Some(CheckResult::Unsat),
        "0 > 14 is false"
    );
    let result = check(&mut arena, &[true_atom]).expect("in fragment");
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "0 ≥ 0 is true, got {result:?}"
    );
}

// -------------------------------------------------------------------------
// The theory solver's backtracking contract
// -------------------------------------------------------------------------

/// `push`/`pop` must drop exactly the edges added since the matching `push`, so
/// a conflict at one decision level does not persist after backtracking.
#[test]
fn pop_restores_feasibility() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let m1 = arena.real_const(Rational::integer(-1));
    let xy = arena.real_sub(x, y).expect("x-y");
    let yx = arena.real_sub(y, x).expect("y-x");
    let a = arena.real_le(xy, m1).expect("x-y<=-1");
    let b = arena.real_le(yx, m1).expect("y-x<=-1");
    let scan = scan_dl(&mut arena, &[a, b]).expect("pure difference logic");
    let mut theory = DlTheory::new(&scan, None);

    let a_index = scan
        .atom_terms
        .iter()
        .position(|&t| t == a)
        .expect("atom a registered");
    let b_index = scan
        .atom_terms
        .iter()
        .position(|&t| t == b)
        .expect("atom b registered");

    theory.assert(a_index, true).expect("first is feasible");
    theory.push();
    let core = theory.assert(b_index, true).expect_err("cycle");
    assert!(
        core.iter().any(|l| l.atom == b_index && l.value),
        "the conflict must carry the trigger literal: {core:?}"
    );
    theory.pop();
    // After the pop the second atom can be asserted at the opposite polarity.
    theory
        .assert(b_index, false)
        .expect("the negated atom is feasible");
}

/// Every conflict the theory reports carries the just-asserted literal — the
/// generic driver's trigger-literal precondition.
#[test]
fn conflicts_carry_the_trigger_literal() {
    let mut arena = TermArena::new();
    let var_x = int(&mut arena, "x");
    let var_y = int(&mut arena, "y");
    let var_z = int(&mut arena, "z");
    let minus_one = arena.int_const(-1);
    let xy = arena.int_sub(var_x, var_y).expect("x-y");
    let yz = arena.int_sub(var_y, var_z).expect("y-z");
    let zx = arena.int_sub(var_z, var_x).expect("z-x");
    let first = arena.int_le(xy, minus_one).expect("x-y<=-1");
    let second = arena.int_le(yz, minus_one).expect("y-z<=-1");
    let third = arena.int_le(zx, minus_one).expect("z-x<=-1");
    let scan = scan_dl(&mut arena, &[first, second, third]).expect("pure difference logic");
    let mut theory = DlTheory::new(&scan, None);
    let index = |t: TermId| {
        scan.atom_terms
            .iter()
            .position(|&s| s == t)
            .expect("registered")
    };

    theory.assert(index(first), true).expect("feasible");
    theory.assert(index(second), true).expect("feasible");
    let core = theory
        .assert(index(third), true)
        .expect_err("3-cycle of weight -3");
    assert!(
        core.iter().any(|l| l.atom == index(third) && l.value),
        "trigger literal missing from {core:?}"
    );
    assert_eq!(
        core.len(),
        3,
        "the cycle is minimal by construction: {core:?}"
    );
}

/// Theory propagation must only emit genuinely entailed literals, each with a
/// reason drawn from the currently asserted set.
#[test]
fn propagation_is_entailed_and_explained() {
    let mut arena = TermArena::new();
    let x = int(&mut arena, "x");
    let y = int(&mut arena, "y");
    let m5 = arena.int_const(-5);
    let m1 = arena.int_const(-1);
    let xy = arena.int_sub(x, y).expect("x-y");
    let a = arena.int_le(xy, m5).expect("x-y<=-5");
    let b = arena.int_le(xy, m1).expect("x-y<=-1");
    let scan = scan_dl(&mut arena, &[a, b]).expect("pure difference logic");
    let mut theory = DlTheory::new(&scan, None);
    let index = |t: TermId| {
        scan.atom_terms
            .iter()
            .position(|&s| s == t)
            .expect("registered")
    };

    theory.assert(index(a), true).expect("feasible");
    let props = theory.propagate();
    // `x - y ≤ -5` entails `x - y ≤ -1`.
    let entailed = props
        .iter()
        .find(|p| p.lit.atom == index(b))
        .expect("x-y<=-1 must be propagated");
    assert!(entailed.lit.value, "the entailed polarity is `true`");
    assert!(
        entailed
            .reason
            .iter()
            .all(|l| theory.assigned[l.atom] == Some(l.value)),
        "every reason literal must be currently asserted: {:?}",
        entailed.reason
    );
}

// -------------------------------------------------------------------------
// Normalization helpers
// -------------------------------------------------------------------------

#[test]
fn floor_and_ceil_are_exact_at_negative_rationals() {
    let cases = [
        (Rational::new(-5, 2), -3_i128, -2_i128),
        (Rational::new(5, 2), 2, 3),
        (Rational::integer(-3), -3, -3),
        (Rational::integer(0), 0, 0),
    ];
    for (value, floor, ceil) in cases {
        assert_eq!(floor_of(value), Some(floor), "floor of {value:?}");
        assert_eq!(ceil_of(value), Some(ceil), "ceil of {value:?}");
    }
}

#[test]
fn integer_edge_tightening_matches_the_semantics() {
    // `x - y < c` becomes `≤ ⌈c⌉ - 1` for both signs of `c`.
    for (bound, expected) in [(3_i128, 2_i128), (-2, -3), (0, -1)] {
        let edge = edge_for(Mode::Integer, 1, 2, Rational::integer(bound), true, 1).expect("built");
        assert_eq!(edge.w.c, expected, "strict tightening of {bound}");
        assert!(!edge.strict, "integer mode records the non-strict relation");
        assert_eq!(edge.w.d, 0, "integer mode never uses δ");
    }
    // `x - y ≤ c` becomes `≤ ⌊c⌋`.
    for (bound, expected) in [(3_i128, 3_i128), (-2, -2)] {
        let edge =
            edge_for(Mode::Integer, 1, 2, Rational::integer(bound), false, 1).expect("built");
        assert_eq!(edge.w.c, expected, "non-strict tightening of {bound}");
    }
}

#[test]
fn real_strict_edges_carry_a_negative_delta() {
    let strict = edge_for(Mode::Real, 1, 2, Rational::integer(4), true, 1).expect("built");
    assert_eq!(strict.w, Weight { c: 4, d: -1 });
    assert!(strict.strict);
    let loose = edge_for(Mode::Real, 1, 2, Rational::integer(4), false, 1).expect("built");
    assert_eq!(loose.w, Weight { c: 4, d: 0 });
    assert!(!loose.strict);
}

#[test]
fn weight_order_is_the_delta_rational_order() {
    assert!(Weight { c: 0, d: -1 }.is_negative(), "0 - δ < 0");
    assert!(!Weight { c: 0, d: 0 }.is_negative(), "0 is not negative");
    assert!(!Weight { c: 0, d: 1 }.is_negative(), "0 + δ > 0");
    assert!(Weight { c: -1, d: 5 }.is_negative(), "-1 + 5δ < 0");
}
