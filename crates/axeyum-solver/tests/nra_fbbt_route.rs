//! The FBBT refutation route, end to end through the front door.
//!
//! `crates/axeyum-solver/src/nra_fbbt.rs`'s own unit tests exercise the Farkas
//! checker guard by guard. These exercise the **route**: what a whole query is
//! answered with once the derived bounds reach the deciders.
//!
//! The route is refutation-only by construction (`nra_fbbt::Refutation` carries no
//! model and converts to exactly one verdict), so the failure mode these tests
//! have to hunt is a **wrong `unsat`** — a query the route refutes that is in fact
//! satisfiable. Every negative test below is therefore over a SATISFIABLE query
//! whose satisfiability depends on a bound being derived correctly: a too-tight
//! bound flips it, and nothing weaker would be visible.
//!
//! # Which of these actually reach the route, and how that is known
//!
//! A satisfiable query answered `sat` by a route UPSTREAM of this one passes every
//! assertion here while measuring nothing about the FBBT route — the vacuous
//! negative control. Asserting a verdict cannot tell the two apart, so each test
//! says below which it is, and the evidence is a **measured mutation**, not a
//! reading of the dispatch order:
//!
//! - `the_sqrt_1mcosq_shape_is_refuted_through_derived_bounds` and
//!   `a_satisfiable_query_with_a_three_variable_transitive_bound_is_not_refuted`
//!   are **proven to reach it**. Setting `FbbtPolicy::DERIVED_BOUNDS`'s
//!   `max_component_vars` to `0` — which turns the route off and changes nothing
//!   else — kills the first; deriving a bound 20x tighter than entailed with the
//!   checker's residual guard removed kills the second with `got Unsat` on a query
//!   satisfied by `x = 8, y = 5, z = 0`. Both are registered as the
//!   `nra-fbbt-route` suite in `scripts/tests/mutation_controls.py`.
//! - The remaining three are **front-door non-regression** checks: the shipped
//!   engine must not answer `unsat` on a satisfiable query, whichever route
//!   answers it. At least one is decided upstream by the two-variable non-strict
//!   CAD, so it says nothing about this route specifically, and it is labelled
//!   that way rather than counted as coverage of it.
#![cfg(feature = "full")]
// `x`, `y`, `z` and the arena `a` are the names these queries are DISCUSSED
// under, in the doc comments and in the assertion messages; renaming them to
// satisfy the lint would make the tests harder to read against their own
// explanation. `tests/nra.rs` carries the same allow for the same reason.
#![allow(clippy::many_single_char_names)]

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, check_with_nra};

fn real(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Real).unwrap();
    arena.var(s)
}

fn q(n: i128, d: i128) -> Rational {
    Rational::new(n, d)
}

/// `y²·(1/2 + y²·(−1/24 + y²/720))`, i.e. the degree-6 Taylor head of `1 − cos y`
/// that `sqrt-1mcosq-8-chunk-0014.smt2` asserts is `> 1`.
fn one_minus_cos_head(a: &mut TermArena, y: TermId) -> TermId {
    let y2 = a.real_mul(y, y).unwrap();
    let c720 = a.real_const(q(1, 720));
    let inner = a.real_mul(y2, c720).unwrap(); // y²/720
    let c24 = a.real_const(q(-1, 24));
    let inner = a.real_add(c24, inner).unwrap(); // −1/24 + y²/720
    let inner = a.real_mul(y2, inner).unwrap();
    let chalf = a.real_const(q(1, 2));
    let inner = a.real_add(chalf, inner).unwrap(); // 1/2 + y²(−1/24 + y²/720)
    a.real_mul(y2, inner).unwrap()
}

/// **The positive control, and the file this route exists for.**
///
/// `sqrt-1mcosq-8-chunk-0014.smt2` reduced to its atoms: one degree-6 nonlinear
/// atom in `skoY` alone, and four linear atoms in which `pi` and `skoX` occur.
/// `decompose_multivariate` unions all of them into one 3-variable component and
/// declines. Deriving `1/10 < skoY < 31415927/20000000 − 1/5` from the linear
/// atoms — both bounds TRANSITIVE, so `nra::extract_bounds` finds neither — leaves
/// a 1-variable system the sign-cell decider refutes at once.
///
/// The file's own `:status` is `unsat`, so this is a verdict an independent
/// authority has already recorded.
#[test]
fn the_sqrt_1mcosq_shape_is_refuted_through_derived_bounds() {
    let mut a = TermArena::new();
    let sko_y = real(&mut a, "skoY");
    let pi = a.declare("pi", Sort::Real).unwrap();
    let pi = a.var(pi);
    let sko_x = real(&mut a, "skoX");

    let head = one_minus_cos_head(&mut a, sko_y);
    let one = a.real_const(Rational::integer(1));
    let a1 = a.real_gt(head, one).unwrap(); // ¬(head ≤ 1)

    // skoY ≤ −1/5 + pi/2
    let half = a.real_const(q(1, 2));
    let half_pi = a.real_mul(pi, half).unwrap();
    let m_fifth = a.real_const(q(-1, 5));
    let rhs = a.real_add(m_fifth, half_pi).unwrap();
    let a2 = a.real_le(sko_y, rhs).unwrap();

    // 15707963/5000000 < pi < 31415927/10000000
    let lo = a.real_const(q(15_707_963, 5_000_000));
    let a3 = a.real_gt(pi, lo).unwrap();
    let hi = a.real_const(q(31_415_927, 10_000_000));
    let a4 = a.real_lt(pi, hi).unwrap();

    // 1/10 ≤ skoX < skoY
    let tenth = a.real_const(q(1, 10));
    let a5 = a.real_ge(sko_x, tenth).unwrap();
    let a6 = a.real_gt(sko_y, sko_x).unwrap();

    let r = check_with_nra(&mut a, &[a1, a2, a3, a4, a5, a6], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "the derived interval on skoY refutes the degree-6 atom; got {r:?}"
    );
}

/// **Front-door non-regression, NOT coverage of this route.**
///
/// `x² > 50 ∧ 0 ≤ x ≤ y + 10 ∧ 0 ≤ y ≤ 100` is satisfied by `x = 10, y = 0`, and
/// the shipped engine must not answer `unsat`. But it is a TWO-variable component,
/// so `decompose_multivariate`'s non-strict two-variable CAD decides it before the
/// FBBT route is consulted — confirmed by measurement, not by reading the
/// dispatch: a derivation 20x too tight with the residual guard removed flips the
/// three-variable test below and leaves this one green. Kept for what it is, and
/// labelled so nobody counts it as evidence about the derived bounds.
#[test]
fn a_two_variable_satisfiable_query_is_not_refuted() {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");

    let xx = a.real_mul(x, x).unwrap();
    let fifty = a.real_const(Rational::integer(50));
    let a1 = a.real_gt(xx, fifty).unwrap(); // x² > 50   (x > ~7.07)

    let zero = a.real_const(Rational::zero());
    let a2 = a.real_ge(x, zero).unwrap(); // x ≥ 0
    let ten = a.real_const(Rational::integer(10));
    let ypten = a.real_add(y, ten).unwrap();
    let a3 = a.real_le(x, ypten).unwrap(); // x ≤ y + 10
    let a4 = a.real_ge(y, zero).unwrap(); // y ≥ 0
    let hundred = a.real_const(Rational::integer(100));
    let a5 = a.real_le(y, hundred).unwrap(); // y ≤ 100

    let r = check_with_nra(&mut a, &[a1, a2, a3, a4, a5], &SolverConfig::default()).unwrap();
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x=10, y=0 satisfies this; a refutation here is a WRONG unsat, got {r:?}"
    );
}

/// **The adversarial test that is proven to reach the route.**
///
/// Three variables, so `decompose_multivariate` unions them into one 3-variable
/// component and declines — exactly the shape the FBBT route exists for, and why
/// this one is not decided upstream the way the two-variable case above is. The
/// bound on `x` arrives TRANSITIVELY, through `z` and then `y`: `x ≤ y + 3`,
/// `y ≤ z + 5`, `0 ≤ z ≤ 5` give `x ≤ 13`, and `x = 8, y = 5, z = 0` satisfies the
/// whole query.
///
/// A derivation 20x tighter than entailed, with the checker's residual guard
/// removed, makes this same query come back `Unsat` — measured, not argued. So the
/// test can fail, it fails on precisely the wrong-`unsat` failure mode, and it is
/// the one that says the route was exercised at all.
#[test]
fn a_satisfiable_query_with_a_three_variable_transitive_bound_is_not_refuted() {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let z = real(&mut a, "z");

    let xx = a.real_mul(x, x).unwrap();
    let fifty = a.real_const(Rational::integer(50));
    let a1 = a.real_gt(xx, fifty).unwrap(); // x² > 50

    let zero = a.real_const(Rational::zero());
    let a2 = a.real_ge(x, zero).unwrap();
    // x ≤ y + 3, y ≤ z + 5, 0 ≤ z ≤ 5  ⇒  x ≤ 13.
    let three = a.real_const(Rational::integer(3));
    let yp3 = a.real_add(y, three).unwrap();
    let a3 = a.real_le(x, yp3).unwrap();
    let five = a.real_const(Rational::integer(5));
    let zp5 = a.real_add(z, five).unwrap();
    let a4 = a.real_le(y, zp5).unwrap();
    let a5 = a.real_ge(z, zero).unwrap();
    let a6 = a.real_le(z, five).unwrap();

    let r = check_with_nra(&mut a, &[a1, a2, a3, a4, a5, a6], &SolverConfig::default()).unwrap();
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x=8, y=5, z=0 satisfies this; got {r:?}"
    );
}

/// A nonlinear atom whose variables are genuinely coupled beyond the policy's
/// `max_component_vars` is left alone: the route skips it rather than paying the
/// ≥3-variable CAD a second time. Satisfiable, so a refutation would be wrong.
#[test]
fn a_three_variable_nonlinear_component_is_left_to_the_existing_route() {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let z = real(&mut a, "z");

    let xy = a.real_mul(x, y).unwrap();
    let xyz = a.real_mul(xy, z).unwrap();
    let one = a.real_const(Rational::integer(1));
    let a1 = a.real_gt(xyz, one).unwrap(); // xyz > 1

    let zero = a.real_const(Rational::zero());
    let ten = a.real_const(Rational::integer(10));
    let mut bounds = vec![a1];
    for v in [x, y, z] {
        bounds.push(a.real_ge(v, zero).unwrap());
        bounds.push(a.real_le(v, ten).unwrap());
    }

    let r = check_with_nra(&mut a, &bounds, &SolverConfig::default()).unwrap();
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x=y=z=2 satisfies this; got {r:?}"
    );
}

/// An UNSAT query whose nonlinear atom needs a bound the linear atoms do **not**
/// give (the neighbour is unconstrained). The route must decline rather than
/// invent an extreme — declining leaves the verdict to the engines that already
/// handle it, and inventing one is the wrong-unsat shape.
///
/// Asserted as "not a refutation THROUGH this route" by construction: with the
/// neighbour free there is no constant bound to derive, so the only way to reach
/// `unsat` is a bound that is not entailed.
#[test]
fn an_unbounded_neighbour_produces_no_refutation() {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");

    let xx = a.real_mul(x, x).unwrap();
    let fifty = a.real_const(Rational::integer(50));
    let a1 = a.real_gt(xx, fifty).unwrap(); // x² > 50
    let a2 = a.real_le(x, y).unwrap(); // x ≤ y, y free

    let r = check_with_nra(&mut a, &[a1, a2], &SolverConfig::default()).unwrap();
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x=10, y=10 satisfies this; got {r:?}"
    );
}

/// **The coverage control for the differential fuzz's FBBT seed class.**
///
/// This is one instance of exactly the shape
/// `nra_differential_fuzz::Instance::generate_fbbt_bound_chain` emits, driven
/// through the same front door (`solve`) the fuzz uses, asserting that the
/// derived-bound route is actually **reached** — read from
/// `nra_derived_bound_coverage`, not inferred from the verdict.
///
/// It exists because the fuzz's own tally could not answer the question. With
/// the seed class in place and 2,000 instances swept, the tally was identical
/// with the route on and off (1,927 jointly decided, 1,927 agreements, 0
/// disagreements, both arms), which is equally consistent with "ran and changed
/// nothing" and "never ran". The counters said it was the second — 0 components
/// offered — and this is the fast reproduction of that question.
#[test]
fn the_fuzz_seed_class_shape_reaches_the_derived_bound_route() {
    let before = axeyum_solver::nra_derived_bound_coverage();

    let mut a = TermArena::new();
    let x0 = real(&mut a, "c0");
    let x1 = real(&mut a, "c1");
    let x2 = real(&mut a, "c2");

    // 2·x0⁴ + x0 − 3 > 0, nonlinear content in x0 alone.
    let mut p = a.real_const(Rational::integer(2));
    for _ in 0..4 {
        p = a.real_mul(p, x0).unwrap();
    }
    let p = a.real_add(p, x0).unwrap();
    let three = a.real_const(Rational::integer(-3));
    let p = a.real_add(p, three).unwrap();
    let zero = a.real_const(Rational::zero());
    let nl = a.real_gt(p, zero).unwrap();

    // The chain: −2 ≤ x2 ≤ 4, |x1 − x2| ≤ 3, |x0 − x1| ≤ 2  ⇒  −7 ≤ x0 ≤ 9.
    let mut asserts = vec![nl];
    let four = a.real_const(Rational::integer(4));
    let mtwo = a.real_const(Rational::integer(-2));
    asserts.push(a.real_le(x2, four).unwrap());
    asserts.push(a.real_ge(x2, mtwo).unwrap());
    for (lo, hi, gap) in [(x1, x2, 3i128), (x0, x1, 2)] {
        let g = a.real_const(Rational::integer(gap));
        let up = a.real_add(hi, g).unwrap();
        asserts.push(a.real_le(lo, up).unwrap());
        let gneg = a.real_const(Rational::integer(-gap));
        let dn = a.real_add(hi, gneg).unwrap();
        asserts.push(a.real_ge(lo, dn).unwrap());
    }

    let r = axeyum_solver::solve(&mut a, &asserts, &SolverConfig::default()).unwrap();
    assert!(
        !matches!(r, CheckResult::Unsat),
        "x0 = 2 satisfies this; got {r:?}"
    );

    let after = axeyum_solver::nra_derived_bound_coverage();
    assert!(
        after.components_offered > before.components_offered,
        "the fuzz's seed shape never reached the derived-bound route: {before:?} -> {after:?}"
    );
}
