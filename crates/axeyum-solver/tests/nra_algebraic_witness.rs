//! ADR-2134: a `sat` whose final coordinate is an ALGEBRAIC number, accepted
//! only after an exact replay of every ORIGINAL assertion at that exact point.
//!
//! # What this file is for
//!
//! The single-cell CAD route (ADR-2121) finds a cell in which every collected
//! atom holds and hands the cell's representative point back as a model. When
//! that point is an irrational root the route used to refuse
//! (`CadDecline::AlgebraicWitness`) — measured at **7 of the pinned 200 QF_NRA
//! files** on the shipped default, 6 of them `unknown`, which is the largest
//! named lever left in the division.
//!
//! The lever accepts such a point **only as the last coordinate** and **only if
//! the exact replay accepts**. Three fixtures hold that, and each is written to
//! fail in a specific way if the guarantee is weakened:
//!
//! 1. [`algebraic_only_solution_is_sat_with_an_irrational_coordinate`] — a
//!    system whose ONLY solutions are irrational is decided, the coordinate is
//!    genuinely algebraic, and it has an exact root object to print.
//! 2. [`a_rational_approximation_can_satisfy_what_the_exact_point_violates`] —
//!    the soundness-negative. A nearby rational satisfies every atom while the
//!    exact point violates one, so a route that rounded would answer `sat` to a
//!    query false at the point it names. The fixture first proves the
//!    approximation IS accepted, which is what makes the exactness load-bearing
//!    rather than decorative.
//! 3. [`a_sign_needing_deep_refinement_is_still_decided_exactly`] — the
//!    separation control. An atom whose sign at `α` needs the bracket narrowed
//!    past `1e-12` is still decided, so "exact" did not become "declines
//!    whenever it is hard".
//!
//! The printed `(root-obj p k)` form is pinned where the printer lives, by
//! `smtlib::tests::an_algebraic_model_value_prints_as_a_root_object`.
//!
//! # Why the entry points and not the environment
//!
//! `AXEYUM_NRA_CAD` is read once per process through a `OnceLock`, so a test
//! that set it would measure whichever test ran first. Every test here drives
//! `single_cell_decide_for_testing` (lever OFF) and
//! `algebraic_witness_decide_for_testing` (lever ON) directly. They differ in
//! exactly one flag, so running the same query through both attributes the
//! difference to the lever and to nothing else.

#![cfg(feature = "full")]

use axeyum_ir::{Assignment, Rational, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, algebraic_witness_decide_for_testing, single_cell_decide_for_testing,
    single_cell_decline_cause,
};

fn real(arena: &mut TermArena, name: &str) -> (SymbolId, TermId) {
    let s = arena.declare(name, Sort::Real).unwrap();
    let t = arena.var(s);
    (s, t)
}

fn rc(arena: &mut TermArena, n: i128) -> TermId {
    arena.real_const(Rational::integer(n))
}

/// Replay a returned model through the ground evaluator against the assertions
/// it is offered as a model of. This is an INDEPENDENT check: the route has its
/// own replay, and a test that trusted that one would only be asserting that
/// the producer agrees with itself.
fn replay_accepts(arena: &TermArena, assertions: &[TermId], model: &axeyum_solver::Model) -> bool {
    let mut asg = Assignment::new();
    for (sym, value) in model.iter() {
        asg.set(sym, value);
    }
    assertions
        .iter()
        .all(|&a| matches!(eval(arena, a, &asg), Ok(Value::Bool(true))))
}

/// How many coordinates of the model are irrational-algebraic.
fn algebraic_coordinates(model: &axeyum_solver::Model) -> usize {
    model
        .iter()
        .filter(|(_, v)| matches!(v, Value::RealAlgebraic(_)))
        .count()
}

#[test]
fn algebraic_only_solution_is_sat_with_an_irrational_coordinate() {
    // `x*x = 2 ∧ x > 0` — the smallest system whose only solution is irrational.
    let mut arena = TermArena::new();
    let (_, x) = real(&mut arena, "x");
    let xx = arena.real_mul(x, x).unwrap();
    let two = rc(&mut arena, 2);
    let eq = arena.eq(xx, two).unwrap();
    let zero = rc(&mut arena, 0);
    let pos = arena.real_gt(x, zero).unwrap();
    let assertions = vec![eq, pos];

    // Lever OFF: the route refuses, and it refuses for THIS reason. Asserting
    // the cause rather than merely `is_none()` is what makes this a control for
    // the lever instead of for any decline at all.
    let off = single_cell_decide_for_testing(&arena, &assertions);
    assert!(off.is_none(), "lever OFF must refuse, got {off:?}");
    assert_eq!(
        single_cell_decline_cause(),
        "algebraic-witness",
        "the OFF arm must refuse for exactly the reason this lever removes"
    );

    // Lever ON: decided, with a model.
    let on = algebraic_witness_decide_for_testing(&arena, &assertions);
    let Some(CheckResult::Sat(model)) = on else {
        panic!("lever ON must decide `x*x=2 ∧ x>0` as sat, got {on:?}");
    };

    // The coordinate is genuinely IRRATIONAL. Had it come back rational the
    // fixture would be exercising the old path and passing for the wrong reason.
    assert_eq!(
        algebraic_coordinates(&model),
        1,
        "the witness must be an algebraic value, not a rounded rational"
    );

    // The model satisfies the ORIGINAL assertions — checked here, not taken on
    // the route's word.
    assert!(
        replay_accepts(&arena, &assertions, &model),
        "the returned model must satisfy the original assertions exactly"
    );

    // And the value can be NAMED exactly, which is what lets `(get-model)`
    // print it instead of refusing or rounding.
    let alpha = model
        .iter()
        .find_map(|(_, v)| match v {
            Value::RealAlgebraic(a) => Some(a),
            _ => None,
        })
        .expect("an algebraic coordinate");
    let (poly, index) = alpha
        .root_object()
        .expect("the witness must have an exact root object");
    assert_eq!(
        index, 2,
        "+√2 is the SECOND real root of x² − 2 in ascending order"
    );
    assert_eq!(
        poly.len(),
        3,
        "the squarefree defining polynomial of √2 is quadratic, got {poly:?}"
    );
}

#[test]
fn a_rational_approximation_can_satisfy_what_the_exact_point_violates() {
    // THE SOUNDNESS-NEGATIVE.
    //
    // `x*x = 2 ∧ x > 0 ∧ 5*x < 7` — that is, `α = √2 ≈ 1.4142135…` under the
    // extra atom `x < 7/5 = 1.4`.
    //
    // `7/5` sits between the usual short approximation of √2 and √2 itself:
    //
    //   * the APPROXIMATION `1.39` satisfies `x > 0` and `5x < 7` (6.95 < 7);
    //   * the EXACT point `√2` violates it (5·1.41421… = 7.0710… > 7).
    //
    // A route that rounded the coordinate and replayed the rounded value would
    // answer `sat` to a system that is FALSE at the point it names. The exact
    // replay must refuse to call this `sat`.
    let mut arena = TermArena::new();
    let (xs, x) = real(&mut arena, "x");
    let xx = arena.real_mul(x, x).unwrap();
    let two = rc(&mut arena, 2);
    let eq = arena.eq(xx, two).unwrap();
    let zero = rc(&mut arena, 0);
    let pos = arena.real_gt(x, zero).unwrap();
    let five = rc(&mut arena, 5);
    let seven = rc(&mut arena, 7);
    let fivex = arena.real_mul(five, x).unwrap();
    let bounded = arena.real_lt(fivex, seven).unwrap();
    let assertions = vec![eq, pos, bounded];

    // First establish that the fixture IS the trap it claims to be. A
    // soundness-negative that is not actually near the boundary tests nothing.
    let mut approx = Assignment::new();
    approx.set(xs, Value::Real(Rational::new(139, 100)));
    assert!(
        matches!(eval(&arena, pos, &approx), Ok(Value::Bool(true))),
        "the approximation must satisfy x > 0"
    );
    assert!(
        matches!(eval(&arena, bounded, &approx), Ok(Value::Bool(true))),
        "the approximation must satisfy 5x < 7 -- this is what makes it a trap"
    );
    // ... and that the EXACT point does not. Checked in exact integer
    // arithmetic, independently of anything the solver does: 5√2 > 7 iff
    // 25·2 > 49.
    assert!(
        25 * 2 > 49,
        "5√2 > 7, so the exact point violates the bound"
    );

    // The route, with the lever ON, must not answer `sat`.
    let on = algebraic_witness_decide_for_testing(&arena, &assertions);
    assert!(
        !matches!(on, Some(CheckResult::Sat(_))),
        "the exact point violates 5x < 7; a `sat` here would be a wrong verdict \
         reached by rounding, got {on:?}"
    );
}

#[test]
fn a_sign_needing_deep_refinement_is_still_decided_exactly() {
    // THE SEPARATION CONTROL.
    //
    // `x*x = 2 ∧ x > 0 ∧ 1136689*x - 1607521 > 0`.
    //
    // `1607521/1136689` is a Pell convergent of √2: `a² − 2b² = −1`, the
    // smallest possible nonzero value, which is what makes the convergent close.
    // Being `−1` it sits just BELOW √2, so the atom holds at √2 — but the atom's
    // own root is only
    //
    //     1 / (b·(a + b√2)) ≈ 2.7e-13
    //
    // away from √2. Deciding the atom's sign there requires narrowing the
    // bracket around √2 to better than `2.7e-13`; two endpoint samples of any
    // wider bracket cannot separate the two numbers, and a route that stopped
    // refining at a fixed width would decline here.
    //
    // A Pell convergent rather than a decimal bound on purpose: an earlier draft
    // used `1000000000000*x > 1414213562373`, which has a comparable gap but a
    // coefficient above the route's declared `1 << 40` coefficient range, so it
    // declined at `coefficient-range` — a SLICE bound, which says nothing about
    // exactness. Both coefficients here are under `2^21`.
    let mut arena = TermArena::new();
    let (_, x) = real(&mut arena, "x");
    let xx = arena.real_mul(x, x).unwrap();
    let two = rc(&mut arena, 2);
    let eq = arena.eq(xx, two).unwrap();
    let zero = rc(&mut arena, 0);
    let pos = arena.real_gt(x, zero).unwrap();
    let den = rc(&mut arena, 1_136_689);
    let num = rc(&mut arena, 1_607_521);
    let denx = arena.real_mul(den, x).unwrap();
    let gap = arena.real_sub(denx, num).unwrap();
    let tight = arena.real_gt(gap, zero).unwrap();
    let assertions = vec![eq, pos, tight];

    // The fixture's arithmetic, exact and independent of anything the solver
    // does. Two claims, both in integers:
    let a = 1_607_521_i128;
    let b = 1_136_689_i128;

    //  (1) `a² − 2b² = −1` ⟹ `a/b < √2` ⟹ the atom `b·x − a` is POSITIVE at √2,
    //      so this fixture asserts a sat and not a decline-by-falsity.
    assert_eq!(
        a * a - 2 * b * b,
        -1,
        "a/b must be a Pell convergent lying just BELOW √2"
    );

    //  (2) the separation is finer than 1e-12. Exactly:
    //          √2 − a/b = (2b² − a²) / (b·(a + b√2)) = 1 / (b·(a + b√2))
    //      and `1393/985 < √2` (since 1393² = 1940449 < 1940450 = 2·985²), so
    //          b·(a + b√2) > b·(985a + 1393b)/985
    //      hence the gap is below `985 / (b·(985a + 1393b))`. Requiring that to
    //      be under 1e-12 is requiring `b·(985a + 1393b) > 985e12`.
    assert!(
        1393_i128 * 1393 < 2 * 985 * 985,
        "1393/985 must be a LOWER bound on √2 for the estimate below"
    );
    assert!(
        b * (985 * a + 1393 * b) > 985 * 1_000_000_000_000,
        "the separation must be finer than 1e-12"
    );

    let on = algebraic_witness_decide_for_testing(&arena, &assertions);
    let Some(CheckResult::Sat(model)) = on else {
        panic!(
            "an atom whose sign needs refinement past 2.7e-13 must still be \
             decided exactly, got {on:?} (cause: {})",
            single_cell_decline_cause()
        );
    };
    assert_eq!(
        algebraic_coordinates(&model),
        1,
        "the deep-refinement witness is still the algebraic point"
    );
    assert!(
        replay_accepts(&arena, &assertions, &model),
        "the deep-refinement model must satisfy the original assertions"
    );
}

#[test]
fn the_lever_is_strictly_additive_on_a_rational_witness() {
    // The arm's central claim: it changes nothing the shipped arm already
    // decides. A query with a RATIONAL model must come back identically from
    // both entry points.
    let mut arena = TermArena::new();
    let (_, x) = real(&mut arena, "x");
    let xx = arena.real_mul(x, x).unwrap();
    let four = rc(&mut arena, 4);
    let eq = arena.eq(xx, four).unwrap();
    let zero = rc(&mut arena, 0);
    let pos = arena.real_gt(x, zero).unwrap();
    let assertions = vec![eq, pos];

    let off = single_cell_decide_for_testing(&arena, &assertions);
    let on = algebraic_witness_decide_for_testing(&arena, &assertions);
    match (&off, &on) {
        (Some(CheckResult::Sat(a)), Some(CheckResult::Sat(b))) => {
            let av: Vec<_> = a.iter().map(|(s, v)| (s, format!("{v:?}"))).collect();
            let bv: Vec<_> = b.iter().map(|(s, v)| (s, format!("{v:?}"))).collect();
            assert_eq!(av, bv, "the lever must not change an existing model");
            assert_eq!(
                algebraic_coordinates(a),
                0,
                "x*x=4 ∧ x>0 has the RATIONAL model x=2; an algebraic \
                 coordinate here would mean the fixture lost its subject"
            );
        }
        other => panic!("both arms must decide `x*x=4 ∧ x>0` sat, and identically, got {other:?}"),
    }
}
