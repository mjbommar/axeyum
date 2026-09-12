//! A refinement point lemma must be rewritten through the product abstraction
//! before it reaches the linear engine.
//!
//! # The defect this pins
//!
//! `solve_relaxation`'s incremental-linearization loop builds a point lemma
//! `(a = a0 and b = b0) implies r = a0*b0` from the **original** operand terms of
//! an abstracted product. It guards that with `products.contains(&pa)`, which
//! skips an operand that *is* a collected product — but **not** one that merely
//! *contains* one. `(+ c (* x (* x k)))` is a `RealAdd`, so it is not in
//! `products`, yet the lemma built from it carries a live `(* x …)` into the
//! linear relaxation. The linear engine cannot linearize a product of two
//! non-constants and returns `SolverError::Unsupported`, which
//! `check_with_nra_impl` propagates with `?`.
//!
//! Measured on the 2026-09-12 `QF_NRA` census
//! (`bench-results/qf-nra-route-20260912/`), that escaping error was the
//! **largest single cause** of the division's addressable gap — 20 of the 77
//! winnable files — surfacing at the front door as
//! `give-up kind=Error detail=unsupported by backend: QF_LRA: nonlinear real
//! multiplication`, whose text names the linear backend rather than the
//! nonlinear boundary that actually refused.
//!
//! # Why this calls `check_with_nra` and not the front door
//!
//! The dispatcher now also converts a pure-real `Unsupported` into an `unknown`
//! (`unknown` is a first-class result here and never an error). That conversion
//! is a **safety net for any future producer**, and it MASKS this defect: a
//! front-door test passes with the point-lemma rewrite deleted, because the
//! escaping error is caught one layer up. Measured — the first version of this
//! test went through `solve_smtlib` and the mutation control reported the guard
//! SURVIVED. So the assertion is made at `check_with_nra`, below the net, where
//! the leak is observable.
//!
//! # The fixture
//!
//! Reduced by hand from `meti-tarski/sin/problem/7/sin-problem-7-chunk-0124.smt2`
//! (the fastest of the 20 to reach the defect) to two variables and one coupling
//! atom, keeping the two properties that matter: **tight rational coefficients**
//! (so the exact real-root decider declines rather than certifying) and the
//! **Horner nesting** `(* y (* y (+ (* x k) …)))`, whose addition operand
//! contains a product.
//!
//! A tidier earlier fixture (`y*(1 + x*x) = 7` over a box) was also **rejected
//! by the mutation control**: `decide_real_poly_constraint` decides it outright,
//! so the relaxation never ran. Both rejections are recorded because "a
//! plausible fixture that never reaches the code" is exactly the vacuous-gate
//! shape this repository keeps paying for.
//!
//! # Why this assertion and not a verdict
//!
//! The fix makes the relaxation *able to continue*; it does not promise a
//! decision. So the assertion is exactly what the fix establishes — the route
//! returns a `CheckResult` rather than an `Unsupported` error — and nothing
//! stronger.

#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_solver::{SolverConfig, SolverError, check_with_nra};

fn real(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Real).unwrap();
    arena.var(s)
}

/// `y > 0 and x > 0 and y > x and not(L(x,y) <= R(x))`, where
///
/// ```text
/// L = y * (y * ((x * -1/6) + y * (y * (x * 1/120))))
/// R = x * (x * (x * (-1/6 + x * (x * 1/120))))
/// ```
///
/// `L`'s inner addition `((x * -1/6) + y * (y * (x * 1/120)))` is a `RealAdd`
/// that CONTAINS the collected product `y * (y * (x * 1/120))`, so it passes
/// `products.contains(&pb)` and is the operand whose point lemma leaks.
fn horner_coupling() -> (TermArena, Vec<TermId>) {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let zero = a.real_const(Rational::integer(0));
    let k6 = a.real_const(Rational::new(-1, 6));
    let k120 = a.real_const(Rational::new(1, 120));

    // L = y*(y*((x*k6) + y*(y*(x*k120))))
    let x_k120 = a.real_mul(x, k120).unwrap();
    let y_times_x_k120 = a.real_mul(y, x_k120).unwrap();
    let y_sq_x_k120 = a.real_mul(y, y_times_x_k120).unwrap();
    let x_k6 = a.real_mul(x, k6).unwrap();
    let inner = a.real_add(x_k6, y_sq_x_k120).unwrap();
    let y_inner = a.real_mul(y, inner).unwrap();
    let lhs = a.real_mul(y, y_inner).unwrap();

    // R = x*(x*(x*(k6 + x*(x*k120))))
    let rx_k120 = a.real_mul(x, k120).unwrap();
    let rxx_k120 = a.real_mul(x, rx_k120).unwrap();
    let rinner = a.real_add(k6, rxx_k120).unwrap();
    let rx1 = a.real_mul(x, rinner).unwrap();
    let rx2 = a.real_mul(x, rx1).unwrap();
    let rhs = a.real_mul(x, rx2).unwrap();

    let le = a.real_le(lhs, rhs).unwrap();
    let asserts = vec![
        a.real_gt(y, zero).unwrap(),
        a.real_gt(x, zero).unwrap(),
        a.real_gt(y, x).unwrap(),
        a.not(le).unwrap(),
    ];
    (a, asserts)
}

#[test]
fn a_point_lemma_over_a_nested_product_does_not_escape_as_unsupported() {
    let (mut arena, asserts) = horner_coupling();
    let config = SolverConfig {
        timeout: Some(Duration::from_secs(60)),
        ..SolverConfig::default()
    };
    match check_with_nra(&mut arena, &asserts, &config) {
        Ok(_) => {}
        Err(SolverError::Unsupported(message)) => panic!(
            "check_with_nra returned an Unsupported ERROR instead of a \
             CheckResult: {message}\nA refinement point lemma reached the linear \
             engine without being rewritten through the product abstraction."
        ),
        Err(other) => panic!("unexpected error from the nonlinear real route: {other:?}"),
    }
}
