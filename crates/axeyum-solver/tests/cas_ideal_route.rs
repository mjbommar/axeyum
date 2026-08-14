//! `cas-ideal-refuter`: multivariate nonlinear refutation by an explicit
//! Nullstellensatz / positivity combination, re-checked by an independent
//! expander.
//!
//! The route sits **behind** `nra-real-root` and the nonlinear-integer tail, not
//! on the fast path: it computes a Gröbner basis, and the first placement (beside
//! the two ADR-0386 routes) was measured taking over queries `nra-real-root`
//! already decided four times faster. So the end-to-end tests here are only the
//! cases that were `unknown` before the route existed; the rest assert the
//! *capability* through the route's own entry point, because pinning a deciding
//! route for a query another engine decides would pin a placement, not a
//! capability.
//!
//! Negative controls come first in this file, deliberately. A refuter that never
//! declines is worthless, and a refuter that refutes a satisfiable query is a P0.
//! Every control asserts on the route's own outcome (`NotRefuted`, never
//! `NoCandidate`) rather than on the end-to-end verdict — a control that only
//! asserts "the query stayed `sat`" passes vacuously whenever the admission gate
//! rejects the shape, which is exactly how a control tests nothing. Recorded
//! evidence that each one fires is in the campaign notes: with the checker
//! stubbed to accept, all 8 tamper tests fail; with the two sign guards mutated
//! off, all 4 behavioural controls fail; with the nonlinearity gate mutated off,
//! the linear-system control fails.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Rational, TermArena};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CasHypothesisKind, CasIdealCertificate, CasIdealEntry, CasOutcome, CheckResult, SolverConfig,
    cas_ideal_refutation, check_cas_ideal_certificate,
};

fn config() -> SolverConfig {
    SolverConfig::default().with_timeout(Duration::from_secs(10))
}

/// Solves `text` and returns `(verdict, deciding-route, full trace)`.
fn solve(text: &str) -> (CheckResult, String, String) {
    let mut script = parse_script(text).expect("parse");
    let assertions = script.assertions.clone();
    let (result, trace) =
        axeyum_solver::check_auto_explained(&mut script.arena, &assertions, &config())
            .expect("solve");
    let route = trace
        .last()
        .map(|attempt| attempt.route.to_owned())
        .unwrap_or_default();
    (result, route, trace.to_string())
}

/// End-to-end: the whole dispatch answers `unsat` **and** this route is the one
/// that did it. Reserved for the cases that were `unknown` before it existed;
/// the route deliberately sits behind `nra-real-root` and `int-real-relax`, so a
/// case those decide is asserted with [`assert_route_refutes`] instead.
fn assert_unsat_via_ideal(text: &str) {
    let (result, route, trace) = solve(text);
    assert_eq!(result, CheckResult::Unsat, "trace:\n{trace}");
    assert_eq!(route, "cas-ideal-refuter", "trace:\n{trace}");
}

/// The route's own outcome on `text`.
fn route_outcome(text: &str) -> CasOutcome<CasIdealCertificate> {
    let script = parse_script(text).expect("parse");
    cas_ideal_refutation(&script.arena, &script.assertions)
}

/// The route refutes `text` and the certificate re-checks. This is the
/// capability assertion, independent of where the route sits in the dispatch —
/// several of these shapes are (correctly) decided earlier and faster by
/// `nra-real-root` or `int-real-relax`, and pinning the deciding route for them
/// would pin a placement decision rather than a capability.
fn assert_route_refutes(text: &str) {
    let script = parse_script(text).expect("parse");
    let outcome = cas_ideal_refutation(&script.arena, &script.assertions);
    let CasOutcome::Refuted(cert) = outcome else {
        panic!("expected a refutation, got {outcome:?}\nfor:\n{text}");
    };
    assert!(
        check_cas_ideal_certificate(&script.arena, &script.assertions, &cert),
        "certificate failed its own re-check for:\n{text}"
    );
}

/// The negative-control assertion, in the non-vacuous form: the route itself
/// reached a candidate and **declined** (`NotRefuted`, never `NoCandidate`), and
/// the whole dispatch does not answer `unsat`.
///
/// Asserting only "the query stayed sat" would pass whenever the route's
/// admission gate happened to reject the shape — a control that tests nothing.
/// Asserting on the route outcome is what makes it fire: with the sign guards
/// mutated off, all four of these fail.
fn assert_sat_and_ideal_route_declined(text: &str) {
    let outcome = route_outcome(text);
    assert!(
        matches!(outcome, CasOutcome::NotRefuted(_)),
        "the control is vacuous or the route misfired: {outcome:?}\nfor:\n{text}"
    );
    let (result, _, trace) = solve(text);
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "expected sat, got {result:?}\ntrace:\n{trace}"
    );
}

// ---------------------------------------------------------------------------
// NEGATIVE CONTROLS
// ---------------------------------------------------------------------------

/// The near miss of the flagship case. `x + y = 3 ∧ x·y = 2` is satisfiable
/// (`x = 1, y = 2`); only the constant differs from the refuted `x·y = 5`.
/// Here `x² + y² ≡ 9 − 4 = 5 ≥ 0`, so the squares route finds no negative
/// congruence class and must decline.
#[test]
fn control_a_solvable_system_is_not_refuted() {
    assert_sat_and_ideal_route_declined(
        r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 3))
(assert (= (* x y) 2))
(check-sat)
",
    );
}

/// **The control that pins the fragment boundary.** `x + y = 3 ∧ x·y = 1` is
/// unsatisfiable over ℤ but *satisfiable* over ℝ, at `x, y = (3 ± √5)/2`. The
/// ideal argument is a statement about ℝ (indeed about ℂ), so it must decline
/// here. If it ever fired, the identical reasoning applied to the real-sorted
/// query below would be a wrong `unsat`.
#[test]
fn control_an_integer_only_unsat_is_not_refuted_by_the_ideal_argument() {
    let (result, _, trace) = solve(
        r"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (+ x y) 3.0))
(assert (= (* x y) 1.0))
(check-sat)
",
    );
    assert!(
        !matches!(result, CheckResult::Unsat),
        "a real-satisfiable system was refuted\ntrace:\n{trace}"
    );
    // And the same shape over Int: the route must not claim it, even though the
    // query really is unsat over ℤ — being right for a reason the certificate
    // does not establish is how a wrong `unsat` ships.
    let outcome = route_outcome(
        r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 3))
(assert (= (* x y) 1))
(check-sat)
",
    );
    assert!(
        matches!(outcome, CasOutcome::NotRefuted(_)),
        "expected a decline, got {outcome:?}"
    );
}

/// The sign direction. `x + y = 3 ∧ x·y = 2 ∧ x² + y² ≥ 4` has `x² + y² ≡ 5`,
/// so the inequality's normal form is the *positive* constant `1`. A positive
/// constant is consistent with `≥ 0` and must not refute. This is the off-by-one
/// that would turn the whole route into a wrong-`unsat` generator.
#[test]
fn control_a_positive_residue_does_not_refute_a_non_negativity() {
    assert_sat_and_ideal_route_declined(
        r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 3))
(assert (= (* x y) 2))
(assert (>= (+ (* x x) (* y y)) 4))
(check-sat)
",
    );
}

/// One off the limit. `x² + y² ≡ 5` and the asserted bound is `≥ 5`, so the
/// residue is exactly `0` — satisfied, not contradicted. `≥ 6` would refute.
/// This pins the `<` where an off-by-one produces a wrong `unsat`.
#[test]
fn control_a_residue_exactly_at_the_bound_does_not_refute() {
    assert_sat_and_ideal_route_declined(
        r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 3))
(assert (= (* x y) 2))
(assert (>= (+ (* x x) (* y y)) 5))
(check-sat)
",
    );
}

/// A purely linear system must not enter the route at all — `lia-simplex` and
/// friends decide it far faster, and paying for a Gröbner basis on every linear
/// query would be a fast-path regression. `NoCandidate` records nothing in the
/// trace, so this is asserted on the route outcome directly.
#[test]
fn control_a_linear_system_is_not_a_candidate() {
    let outcome = route_outcome(
        r"
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 3))
(assert (= (- x y) 1))
(check-sat)
",
    );
    assert!(
        matches!(outcome, CasOutcome::NoCandidate),
        "expected no candidate, got {outcome:?}"
    );
}

// ---------------------------------------------------------------------------
// TAMPER TESTS — the checker must reject a certificate it did not derive
// ---------------------------------------------------------------------------

/// Builds the arena and assertions for `x + y = 3 ∧ x·y = 5` over Int, plus the
/// certificate the route produces for it.
fn flagship_certificate() -> (TermArena, Vec<axeyum_ir::TermId>, CasIdealCertificate) {
    let text = r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 3))
(assert (= (* x y) 5))
(check-sat)
";
    let script = parse_script(text).expect("parse");
    let assertions = script.assertions.clone();
    let CasOutcome::Refuted(cert) = cas_ideal_refutation(&script.arena, &assertions) else {
        panic!("the flagship case must be refuted");
    };
    assert!(
        check_cas_ideal_certificate(&script.arena, &assertions, &cert),
        "the untampered certificate must check"
    );
    (script.arena, assertions, cert)
}

/// An inflated multiplier breaks the identity, so the re-derived constant no
/// longer matches and the checker rejects.
#[test]
fn tamper_an_inflated_equality_multiplier_is_rejected() {
    let (arena, assertions, mut cert) = flagship_certificate();
    let mut changed = false;
    for entry in &mut cert.entries {
        if let CasIdealEntry::Asserted { multiplier, .. } = entry
            && let Some((_, coefficient)) = multiplier.first_mut()
        {
            *coefficient = coefficient.checked_mul(Rational::integer(2)).unwrap();
            changed = true;
            break;
        }
    }
    assert!(changed, "the certificate must carry an equality multiplier");
    assert!(!check_cas_ideal_certificate(&arena, &assertions, &cert));
}

/// A relabelled constant is rejected even though the combination itself is
/// unchanged: the checker compares its own re-derivation against the stored
/// value, so a printed certificate cannot lie about what it computes.
#[test]
fn tamper_a_relabelled_constant_is_rejected() {
    let (arena, assertions, mut cert) = flagship_certificate();
    cert.constant = cert.constant.checked_sub(Rational::integer(1)).unwrap();
    assert!(!check_cas_ideal_certificate(&arena, &assertions, &cert));
}

/// **The soundness-critical tamper.** An *odd* exponent is not a square: `x³`
/// takes negative values, so admitting it as a non-negative term would let the
/// checker conclude `unsat` from a combination that is not bounded below. The
/// exponent parity check must catch it.
#[test]
fn tamper_an_odd_power_is_not_accepted_as_non_negative() {
    let (arena, assertions, mut cert) = flagship_certificate();
    let mut changed = false;
    for entry in &mut cert.entries {
        if let CasIdealEntry::EvenMonomial { monomial, .. } = entry
            && let Some((_, exponent)) = monomial.first_mut()
        {
            *exponent = 3;
            changed = true;
        }
    }
    assert!(changed, "the flagship certificate must carry squares");
    assert!(
        !check_cas_ideal_certificate(&arena, &assertions, &cert),
        "an odd power was accepted as non-negative"
    );
}

/// A negative coefficient on a square term is not a non-negative contribution.
#[test]
fn tamper_a_negative_square_coefficient_is_rejected() {
    let (arena, assertions, mut cert) = flagship_certificate();
    let mut changed = false;
    for entry in &mut cert.entries {
        if let CasIdealEntry::EvenMonomial { coefficient, .. } = entry {
            *coefficient = coefficient.checked_neg().unwrap();
            changed = true;
        }
    }
    assert!(changed);
    assert!(!check_cas_ideal_certificate(&arena, &assertions, &cert));
}

/// Dropping a term from the combination breaks the identity: the remaining sum is
/// no longer a constant, so there is nothing to read a sign off.
#[test]
fn tamper_a_truncated_combination_is_rejected() {
    let (arena, assertions, mut cert) = flagship_certificate();
    assert!(cert.entries.len() >= 2);
    cert.entries.pop();
    assert!(!check_cas_ideal_certificate(&arena, &assertions, &cert));
}

/// A conjunct that is not in the assertion list cannot be cited, even if the
/// arithmetic would work out.
#[test]
fn tamper_a_foreign_conjunct_is_rejected() {
    let (mut arena, assertions, mut cert) = flagship_certificate();
    let a = arena.int_var("a").unwrap();
    let b = arena.int_var("b").unwrap();
    let foreign = arena.eq(a, b).unwrap();
    for entry in &mut cert.entries {
        if let CasIdealEntry::Asserted { conjunct, .. } = entry {
            *conjunct = foreign;
            break;
        }
    }
    assert!(!check_cas_ideal_certificate(&arena, &assertions, &cert));
}

/// Relabelling an equality as a non-negativity is rejected: the checker re-reads
/// the comparison head off the conjunct rather than believing the label.
#[test]
fn tamper_a_relabelled_hypothesis_kind_is_rejected() {
    let (arena, assertions, mut cert) = flagship_certificate();
    for entry in &mut cert.entries {
        if let CasIdealEntry::Asserted { kind, .. } = entry {
            *kind = CasHypothesisKind::NonNegative;
            break;
        }
    }
    assert!(!check_cas_ideal_certificate(&arena, &assertions, &cert));
}

/// An empty certificate proves nothing.
#[test]
fn tamper_an_empty_combination_is_rejected() {
    let (arena, assertions, mut cert) = flagship_certificate();
    cert.entries.clear();
    assert!(!check_cas_ideal_certificate(&arena, &assertions, &cert));
}

// ---------------------------------------------------------------------------
// POSITIVE CASES
// ---------------------------------------------------------------------------

/// The flagship. `x + y = 3 ∧ x·y = 5` has no real solution — the discriminant
/// `9 − 20` is negative — and the certificate says so exactly: `x² + y²` is
/// congruent to `9 − 10 = −1` modulo the ideal, and a sum of squares is never
/// negative.
///
/// Nothing in the query mentions `x² + y²`. That is the point: the refutation
/// needs a fact nobody asserted, which is why no rewriting or bit-blasting route
/// finds it. Measured before this route: `unknown` at a 10 s budget.
#[test]
fn sum_of_two_squares_refutes_an_impossible_symmetric_system() {
    assert_route_refutes(
        r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 3))
(assert (= (* x y) 5))
(check-sat)
",
    );
}

/// The same system over ℝ. The argument is a real one, so the real-sorted query
/// is refuted by the identical certificate — which is what makes the integer case
/// sound rather than lucky.
#[test]
fn the_same_system_is_refuted_over_the_reals() {
    assert_route_refutes(
        r"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (+ x y) 3.0))
(assert (= (* x y) 5.0))
(check-sat)
",
    );
}

/// The weak Nullstellensatz proper: three equations with no common zero over ℂ,
/// so `1` lies in the ideal they generate and the certificate is `Σ cᵢ·gᵢ = 1`.
/// `x + y = 3` and `x·y = 5` force `x² + y² = −1`, contradicting the third
/// equation.
#[test]
fn the_unit_ideal_refutes_an_inconsistent_equation_system() {
    assert_route_refutes(
        r"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (+ x y) 3.0))
(assert (= (* x y) 5.0))
(assert (= (+ (* x x) (* y y)) 1.0))
(check-sat)
",
    );
}

/// Three variables, degree 3 — the shape the Rado symbolic-parameter work
/// stalled on. `x + y + z = 0`, `xy + yz + zx = 0` and `xyz = 1` are the
/// elementary symmetric functions of the roots of `t³ − 1`, whose power sum
/// `x³ + y³ + z³` is `3`; asserting `4` is inconsistent, and the certificate is
/// an explicit cofactor combination.
#[test]
fn a_three_variable_cubic_system_is_refuted() {
    assert_route_refutes(
        r"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (= (+ x y z) 0.0))
(assert (= (+ (* x y) (* y z) (* z x)) 0.0))
(assert (= (* x (* y z)) 1.0))
(assert (= (+ (* x (* x x)) (* y (* y y)) (* z (* z z))) 4.0))
(check-sat)
",
    );
}

/// An asserted inequality whose normal form modulo the equations is a constant of
/// the wrong sign. `x + y = 3 ∧ x·y = 2` forces `x² + y² = 5`, so `≥ 6` is
/// refuted — by the equations, not by any bound on `x` or `y` individually.
#[test]
fn an_asserted_inequality_is_refuted_modulo_the_ideal() {
    assert_route_refutes(
        r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 3))
(assert (= (* x y) 2))
(assert (>= (+ (* x x) (* y y)) 6))
(check-sat)
",
    );
}

/// Opaque atoms: the same impossible system stated over two *uninterpreted*
/// integer quantities. `f(a)` and `g(b)` are abstracted to atoms, and the
/// refutation holds whatever they denote — the "generalising the lemma made it
/// harder" shape from the Rado campaign, handled by construction.
#[test]
fn the_refutation_reaches_through_uninterpreted_atoms() {
    assert_route_refutes(
        r"
(set-logic QF_UFNIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= (+ (f a) (g b)) 3))
(assert (= (* (f a) (g b)) 5))
(check-sat)
",
    );
}

/// Underspecified `div` subterms are atoms too, and the refutation is valid for
/// whatever value SMT-LIB's totality assigns them. This is the shape that made
/// the Route B divisibility lemmas time out.
#[test]
fn the_refutation_reaches_through_underspecified_division() {
    assert_unsat_via_ideal(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= (+ (div a b) (div b a)) 3))
(assert (= (* (div a b) (div b a)) 5))
(check-sat)
",
    );
}

/// Every returned refutation carries a certificate that re-checks. This test is
/// the standing guard that the route never returns a verdict its checker did not
/// confirm — `finish` is the only path to `Refuted`, and this pins it.
#[test]
fn every_refutation_carries_a_certificate_that_rechecks() {
    for text in [
        r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 3))
(assert (= (* x y) 5))
(check-sat)
",
        r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 3))
(assert (= (* x y) 2))
(assert (>= (+ (* x x) (* y y)) 6))
(check-sat)
",
    ] {
        let script = parse_script(text).expect("parse");
        let CasOutcome::Refuted(cert) = cas_ideal_refutation(&script.arena, &script.assertions)
        else {
            panic!("expected a refutation for:\n{text}");
        };
        assert!(
            check_cas_ideal_certificate(&script.arena, &script.assertions, &cert),
            "certificate failed its own re-check for:\n{text}"
        );
        assert!(!cert.entries.is_empty());
    }
}

/// Real-sorted division atoms. `nra-real-root` declines on a non-polynomial
/// operator and the linear-abstraction relaxation declines with "3
/// cross-products exceed the deterministic admission bound of 2 ... this needs a
/// nlsat/CAD engine". Measured before this route: `unknown` after 282 ms.
#[test]
fn real_division_atoms_are_refuted_end_to_end() {
    assert_unsat_via_ideal(
        r"
(set-logic QF_NRA)
(declare-fun p () Real)
(declare-fun q () Real)
(assert (= (+ (/ p q) (/ q p)) 3.0))
(assert (= (* (/ p q) (/ q p)) 5.0))
(check-sat)
",
    );
}

/// Three coupled real variables with a non-strict conjunct. The exact real-root
/// decider reports "2-variable resultant elimination could not certify
/// (algebraic-x lift or inequality region)" and that `unknown` is terminal for
/// the real branch. The ideal combination closes it: `x² + y² + z²` is congruent
/// to `1 − 2 = −1` modulo the ideal.
#[test]
fn a_three_variable_real_system_past_the_cad_caps_is_refuted_end_to_end() {
    assert_unsat_via_ideal(
        r"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (= (+ x y z) 1.0))
(assert (= (+ (* x y) (* y z) (* z x)) 1.0))
(assert (= (* x (* y z)) 1.0))
(assert (>= (+ (* x x) (* y y) (* z z)) 0.0))
(check-sat)
",
    );
}

/// Integer `mod` atoms. Measured before this route: `unknown` after 801 ms via
/// `int-blast-ladder` ("no model within the bounded integer width 32").
#[test]
fn integer_mod_atoms_are_refuted_end_to_end() {
    assert_unsat_via_ideal(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= (+ (mod a b) (mod b a)) 3))
(assert (= (* (mod a b) (mod b a)) 5))
(check-sat)
",
    );
}

/// An asserted inequality refuted modulo an ideal over `div` atoms — the
/// inequality shape and the opaque-atom shape at once. Measured before this
/// route: `unknown` after 1.73 s.
#[test]
fn an_inequality_over_division_atoms_is_refuted_end_to_end() {
    assert_unsat_via_ideal(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= (+ (div a b) (div b a)) 3))
(assert (= (* (div a b) (div b a)) 2))
(assert (>= (+ (* (div a b) (div a b)) (* (div b a) (div b a))) 6))
(check-sat)
",
    );
}
