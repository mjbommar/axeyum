//! `QF_NIA` single-variable polynomial equalities now carry a checkable
//! refutation, and the checker can reject one.
//!
//! Three arguments are certified here — a non-square discriminant, rational but
//! non-integral quadratic roots, and rational-root exhaustion at degree ≥ 3.
//! Each was previously decided exactly by `nia_square` and shipped as a bare
//! `Evidence::Unsat(None)`, which is why `QF_NIA` ranked *band 2 — model replay
//! only* in `scripts/check-capability-assurance.py`.
//!
//! # What these tests are actually for
//!
//! Producing a certificate proves nothing on its own: a checker that accepts
//! everything would make every test below pass. So each refutation is exercised
//! three ways —
//!
//! 1. it is produced, and marked `certified`;
//! 2. it survives re-validation against a **freshly built arena** for the same
//!    query, sharing no state with the producing run;
//! 3. a **tampered** certificate is REJECTED, and a certificate for a
//!    *different* query is REJECTED.
//!
//! (3) is the one that can fail for a real reason, and it is separately asserted
//! per argument rather than once for the set — six of seven guards in another
//! suite here were removable while everything stayed green, because they all
//! rejected through one shared path.

#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::certificates::arithmetic::{
    IntUnivariateRefutationReason, check_int_univariate_refutation, int_univariate_refutation,
};
use axeyum_solver::{CheckResult, Evidence, SolverConfig, produce_evidence, solve};

/// Build `p(x) ⋈ 0`-shaped assertions from LSB-first integer coefficients:
/// `coeffs[0] + coeffs[1]·x + coeffs[2]·x² + …  =  0`.
fn poly_eq_zero(arena: &mut TermArena, coeffs: &[i128]) -> TermId {
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let mut sum: Option<TermId> = None;
    for (power, &c) in coeffs.iter().enumerate() {
        if c == 0 {
            continue;
        }
        let mut term = arena.int_const(c);
        for _ in 0..power {
            term = arena.int_mul(term, xv).unwrap();
        }
        sum = Some(match sum {
            None => term,
            Some(acc) => arena.int_add(acc, term).unwrap(),
        });
    }
    let lhs = sum.unwrap_or_else(|| arena.int_const(0));
    let zero = arena.int_const(0);
    arena.eq(lhs, zero).unwrap()
}

/// `(x² + x − 1 = 0)`: `D = 1 + 4 = 5`, not a perfect square.
const NON_SQUARE_DISC: &[i128] = &[-1, 1, 1];
/// `(4x² − 1 = 0)`: `D = 16 = 4²`, roots `±1/2` — rational, not integral.
const NON_INTEGRAL_ROOTS: &[i128] = &[-1, 0, 4];
/// `(x³ + x + 1 = 0)`: `a₀ = 1`, and neither `p(1) = 3` nor `p(−1) = −1` is zero.
const RATIONAL_ROOT_EXHAUSTED: &[i128] = &[1, 1, 0, 1];

/// `(x² − 4 = 0)`: satisfiable at `x = 2`. The negative control for the
/// quadratic arguments.
const QUADRATIC_SAT: &[i128] = &[-4, 0, 1];
/// `(x³ − 1 = 0)`: satisfiable at `x = 1`. The negative control for the
/// rational-root argument — `1` is a divisor of `|a₀|` and IS a root, so an
/// enumeration bug that skipped it would report a wrong `unsat`.
const CUBIC_SAT: &[i128] = &[-1, 0, 0, 1];

fn produce(coeffs: &[i128]) -> (Evidence, TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let assertion = poly_eq_zero(&mut arena, coeffs);
    let assertions = vec![assertion];
    let report = produce_evidence(&mut arena, &assertions, &SolverConfig::default())
        .expect("evidence production must not error");
    (report.evidence, arena, assertions)
}

/// A second, independent arena for the same query — no shared `TermId`s.
fn fresh(coeffs: &[i128]) -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let assertion = poly_eq_zero(&mut arena, coeffs);
    (arena, vec![assertion])
}

fn reason_of(coeffs: &[i128]) -> IntUnivariateRefutationReason {
    let (arena, assertions) = fresh(coeffs);
    int_univariate_refutation(&arena, &assertions)
        .unwrap_or_else(|| panic!("expected a certificate for {coeffs:?}"))
        .reason()
}

// ---- the queries really are unsat, and really are certified ---------------

#[test]
fn each_argument_decides_unsat_and_carries_a_certificate() {
    for coeffs in [NON_SQUARE_DISC, NON_INTEGRAL_ROOTS, RATIONAL_ROOT_EXHAUSTED] {
        let mut arena = TermArena::new();
        let assertion = poly_eq_zero(&mut arena, coeffs);
        let result = solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve");
        assert!(
            matches!(result, CheckResult::Unsat),
            "{coeffs:?} must be unsat, got {result:?}"
        );

        let (evidence, _, _) = produce(coeffs);
        assert!(
            matches!(evidence, Evidence::UnsatIntUnivariatePoly(_)),
            "{coeffs:?} must carry the univariate certificate, got {}",
            evidence.kind_label()
        );
        assert!(
            evidence.is_certified(),
            "{coeffs:?} produced a certificate that does not claim certification"
        );
    }
}

#[test]
fn the_three_arguments_are_distinct_and_each_is_exercised() {
    // Without this, one argument could cover all three fixtures and two
    // branches of the checker would never run.
    let disc = reason_of(NON_SQUARE_DISC);
    let roots = reason_of(NON_INTEGRAL_ROOTS);
    let exhausted = reason_of(RATIONAL_ROOT_EXHAUSTED);
    assert!(
        matches!(
            disc,
            IntUnivariateRefutationReason::NonSquareDiscriminant {
                discriminant: 5,
                isqrt_floor: 2
            }
        ),
        "x²+x−1: {disc:?}"
    );
    assert!(
        matches!(
            roots,
            IntUnivariateRefutationReason::NonIntegralQuadraticRoots {
                discriminant: 16,
                root_sqrt: 4,
                two_a: 8
            }
        ),
        "4x²−1: {roots:?}"
    );
    assert!(
        matches!(
            exhausted,
            IntUnivariateRefutationReason::RationalRootExhausted {
                constant_term: 1,
                candidates_checked: 2
            }
        ),
        "x³+x+1: {exhausted:?}"
    );
}

// ---- re-validation against a fresh parse ---------------------------------

#[test]
fn every_certificate_survives_an_independent_rebuild() {
    for coeffs in [NON_SQUARE_DISC, NON_INTEGRAL_ROOTS, RATIONAL_ROOT_EXHAUSTED] {
        let (evidence, _producing_arena, _) = produce(coeffs);
        let (arena, assertions) = fresh(coeffs);
        let outcome = evidence
            .check_outcome(&arena, &assertions)
            .expect("the checker must not error");
        assert!(
            outcome.is_verified(),
            "{coeffs:?} failed re-validation on a fresh arena: {}",
            outcome.label()
        );
    }
}

// ---- non-vacuity: satisfiable queries must NOT be certified --------------

#[test]
fn satisfiable_polynomials_produce_no_certificate() {
    for coeffs in [QUADRATIC_SAT, CUBIC_SAT] {
        let (arena, assertions) = fresh(coeffs);
        assert!(
            int_univariate_refutation(&arena, &assertions).is_none(),
            "{coeffs:?} is satisfiable but a refutation was produced"
        );
        let mut arena = TermArena::new();
        let assertion = poly_eq_zero(&mut arena, coeffs);
        let result = solve(&mut arena, &[assertion], &SolverConfig::default()).expect("solve");
        assert!(
            matches!(result, CheckResult::Sat(_)),
            "{coeffs:?} must be sat, got {result:?}"
        );
    }
}

#[test]
fn the_negative_discriminant_shape_is_left_to_its_own_certificate() {
    // `x² + 1 = 0`: D = −4. Already covered by
    // `IntQuadraticNegativeDiscriminantCertificate`; two artifacts for one shape
    // would have to be kept in agreement forever.
    let (arena, assertions) = fresh(&[1, 0, 1]);
    assert!(int_univariate_refutation(&arena, &assertions).is_none());
    let (evidence, _, _) = produce(&[1, 0, 1]);
    assert!(
        matches!(evidence, Evidence::UnsatIntQuadraticNegativeDiscriminant(_)),
        "got {}",
        evidence.kind_label()
    );
}

// ---- source binding, from outside the crate -----------------------------

#[test]
fn a_certificate_from_another_query_is_rejected() {
    // The coefficients must be THIS query's. Tampering with the *reason* needs
    // field access and is unit-tested inside `nia_univariate_cert`; this is the
    // half that is visible from outside, and it is the one a caller could hit by
    // accident — reusing a cached certificate against the wrong file.
    for (a, b) in [
        (NON_SQUARE_DISC, NON_INTEGRAL_ROOTS),
        (NON_INTEGRAL_ROOTS, RATIONAL_ROOT_EXHAUSTED),
        (RATIONAL_ROOT_EXHAUSTED, NON_SQUARE_DISC),
    ] {
        let (arena_a, assertions_a) = fresh(a);
        let cert = int_univariate_refutation(&arena_a, &assertions_a).expect("certificate");
        let (arena_b, assertions_b) = fresh(b);
        assert!(
            !check_int_univariate_refutation(&arena_b, &assertions_b, &cert),
            "a certificate for {a:?} was accepted against {b:?}"
        );
    }
}
