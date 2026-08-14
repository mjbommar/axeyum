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

// ---------------------------------------------------------------------------
// The positivity combination: products of asserted non-negativities
// ---------------------------------------------------------------------------

/// **The Rado shape.** `M ≥ 1 ∧ w ≥ 1 ⊢ M·w ≥ M` is the campaign's micro-lemma
/// `M6`, which its degree-3 lemma `L3` was hand-split into after `L3` timed out
/// at 60 s. Its refutation is
///
/// ```text
/// (M − M·w)  +  (M−1)(w−1)  +  (w−1)  =  0
/// ```
///
/// and the middle term is the **product of two asserted bounds** — a degree-2
/// certificate that no rational multiplier can express.
///
/// Stated over `div` atoms with three quantities, so `int-real-relax` (which
/// aborts on `div`) and `nia-linearize` both decline. Measured before this
/// search: `unknown` after a **20 s timeout** via `int-blast-ladder`.
#[test]
fn the_product_of_two_bounds_refutes_the_rado_monotonicity_shape() {
    assert_unsat_via_ideal(
        r"
(set-logic QF_NIA)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun r () Int)
(assert (>= (div p q) 1))
(assert (>= (div r q) (div q r)))
(assert (< (* (div p q) (div r q)) (* (div q r) (div p q))))
(check-sat)
",
    );
}

/// The same argument over real division atoms. `nra-real-root` declines on the
/// non-polynomial operator; the linear-abstraction relaxation decided it before,
/// in 60.6 ms, and this closes it exactly in 1.2 ms.
#[test]
fn the_product_argument_works_over_real_division_atoms() {
    assert_route_refutes(
        r"
(set-logic QF_NRA)
(declare-fun p () Real)
(declare-fun q () Real)
(assert (>= (/ p q) 1.0))
(assert (>= (/ q p) 1.0))
(assert (< (* (/ p q) (/ q p)) (/ p q)))
(check-sat)
",
    );
}

/// NEGATIVE CONTROL for the product shape. `M ≥ 1 ∧ w ≥ 2 ∧ M·w < 3M` is
/// satisfiable (`M = 1, w = 2`), and no product of the asserted bounds closes it.
#[test]
fn control_a_satisfiable_product_shape_is_not_refuted() {
    assert_sat_and_ideal_route_declined(
        r"
(set-logic QF_NIA)
(declare-fun m () Int)
(declare-fun w () Int)
(assert (>= m 1))
(assert (>= w 2))
(assert (< (* m w) (* 3 m)))
(check-sat)
",
    );
}

/// NEGATIVE CONTROL: drop one bound and the argument collapses. Without `b ≥ 1`
/// the product `(b−1)(t−a)` is no longer available and the query is genuinely
/// satisfiable (`b = −1, a = 0, t = 1`).
#[test]
fn control_dropping_a_bound_makes_the_product_argument_unavailable() {
    assert_sat_and_ideal_route_declined(
        r"
(set-logic QF_NIA)
(declare-fun m () Int)
(declare-fun w () Int)
(assert (>= w 1))
(assert (< (* m w) m))
(check-sat)
",
    );
}

/// Pins that the product search really emits an [`CasIdealEntry::AssertedProduct`],
/// rather than a combination that happens to close without one. Without this the
/// product shape could silently regress to the earlier search and nothing would
/// notice, because the end-to-end verdict would be unchanged.
#[test]
fn the_product_search_emits_a_product_entry() {
    let text = r"
(set-logic QF_NIA)
(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun r () Int)
(assert (>= (div p q) 1))
(assert (>= (div r q) (div q r)))
(assert (< (* (div p q) (div r q)) (* (div q r) (div p q))))
(check-sat)
";
    let script = parse_script(text).expect("parse");
    let assertions = script.assertions.clone();
    let CasOutcome::Refuted(cert) = cas_ideal_refutation(&script.arena, &assertions) else {
        panic!("the product case must be refuted");
    };
    assert!(
        cert.entries
            .iter()
            .any(|entry| matches!(entry, CasIdealEntry::AssertedProduct { .. })),
        "the certificate must actually use a product: {cert:?}"
    );
    assert!(check_cas_ideal_certificate(
        &script.arena,
        &assertions,
        &cert
    ));
}

// ---------------------------------------------------------------------------
// GUARD-ISOLATING FORGERIES
//
// The tamper tests above mutate a real certificate. Measured by targeted
// mutation, most of them reject through the *identity* check — change any
// number and the combination stops being a constant — which means they do not
// actually exercise the guard they are named after. Deleting the guard leaves
// them green.
//
// The tests below are different in kind: each is a **hand-built certificate for
// a satisfiable query** whose combination really is a constant of the refuting
// sign, and which exactly one guard stands between and a wrong `unsat`. Each was
// verified to fail when its guard is deleted.
// ---------------------------------------------------------------------------

/// The constant-`1` multiplier every forgery below uses.
fn one() -> axeyum_solver::AtomPoly {
    vec![(Vec::new(), Rational::integer(1))]
}

/// **Parity.** `x³ = −1` is satisfiable (`x = −1`). This forgery presents `x³` as
/// a non-negative term and cancels it against the equation, giving the constant
/// `−1`, which refutes. Only the even-exponent check stands between it and a
/// wrong `unsat` — `x³` is negative exactly where the model is.
#[test]
fn forgery_an_odd_power_presented_as_non_negative_is_rejected() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let square = arena.int_mul(x, x).unwrap();
    let cube = arena.int_mul(x, square).unwrap();
    let minus_one = arena.int_const(-1);
    let equation = arena.eq(cube, minus_one).unwrap();
    let assertions = vec![equation];

    // x³ + (−1)·(x³ + 1) = −1
    let negative_one = vec![(Vec::new(), Rational::integer(-1))];
    let cert = CasIdealCertificate {
        entries: vec![
            CasIdealEntry::EvenMonomial {
                monomial: vec![(x, 3)],
                coefficient: Rational::integer(1),
            },
            CasIdealEntry::Asserted {
                conjunct: equation,
                kind: CasHypothesisKind::Equality,
                multiplier: negative_one,
            },
        ],
        constant: Rational::integer(-1),
    };
    assert!(
        !check_cas_ideal_certificate(&arena, &assertions, &cert),
        "an odd power was accepted as a non-negative term"
    );
}

/// **Square coefficient sign.** `x² = 1` is satisfiable (`x = 1`). Presenting
/// `−x²` as a non-negative term and cancelling against the equation gives `−1`.
#[test]
fn forgery_a_negative_square_coefficient_is_rejected() {
    let mut arena = TermArena::new();
    let x = arena.int_var("x").unwrap();
    let square = arena.int_mul(x, x).unwrap();
    let one_const = arena.int_const(1);
    let equation = arena.eq(square, one_const).unwrap();
    let assertions = vec![equation];

    // (−1)·x² + 1·(x² − 1) = −1
    let cert = CasIdealCertificate {
        entries: vec![
            CasIdealEntry::EvenMonomial {
                monomial: vec![(x, 2)],
                coefficient: Rational::integer(-1),
            },
            CasIdealEntry::Asserted {
                conjunct: equation,
                kind: CasHypothesisKind::Equality,
                multiplier: one(),
            },
        ],
        constant: Rational::integer(-1),
    };
    assert!(!check_cas_ideal_certificate(&arena, &assertions, &cert));
}

/// **The kind label.** `x > 0` over `Real` is satisfiable. Labelling that strict
/// inequality as an *equality* unlocks an arbitrary — here negative — multiplier,
/// and `(−1)·x + 1·x = 0` then reads as `0 = 0` with a strict entry present,
/// which the checker treats as a contradiction. The label must never be trusted:
/// the fact is re-read off the comparison head.
#[test]
fn forgery_a_strict_inequality_relabelled_as_an_equality_is_rejected() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::zero());
    let positive = arena.real_gt(x, zero).unwrap();
    let assertions = vec![positive];

    let negative_one = vec![(Vec::new(), Rational::integer(-1))];
    let cert = CasIdealCertificate {
        entries: vec![
            CasIdealEntry::Asserted {
                conjunct: positive,
                kind: CasHypothesisKind::Equality,
                multiplier: negative_one,
            },
            CasIdealEntry::Asserted {
                conjunct: positive,
                kind: CasHypothesisKind::Positive,
                multiplier: one(),
            },
        ],
        constant: Rational::zero(),
    };
    assert!(
        !check_cas_ideal_certificate(&arena, &assertions, &cert),
        "a strict inequality was accepted under an equality label"
    );
}

/// **Citation.** `x > 0` over `Real` is satisfiable. The forgery cites a
/// perfectly well-formed `x ≤ 0` that is **built but never asserted**; the two
/// cancel to `0`, which with a strict entry present reads as a contradiction.
#[test]
fn forgery_an_uncited_conjunct_is_rejected() {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::zero());
    let positive = arena.real_gt(x, zero).unwrap();
    let unasserted = arena.real_le(x, zero).unwrap();
    let assertions = vec![positive];

    let cert = CasIdealCertificate {
        entries: vec![
            CasIdealEntry::Asserted {
                conjunct: positive,
                kind: CasHypothesisKind::Positive,
                multiplier: one(),
            },
            CasIdealEntry::Asserted {
                conjunct: unasserted,
                kind: CasHypothesisKind::NonNegative,
                multiplier: one(),
            },
        ],
        constant: Rational::zero(),
    };
    assert!(
        !check_cas_ideal_certificate(&arena, &assertions, &cert),
        "a conjunct that was never asserted was accepted as a hypothesis"
    );
}

/// Builds `x ≥ 2 ∧ x ≥ 0 ∧ x² = 2x + 1` over `Real`, which is satisfiable at
/// `x = 1 + √2 ≈ 2.414`. Both product forgeries below are built on it.
fn product_forgery_setup() -> (TermArena, Vec<axeyum_ir::TermId>) {
    let mut arena = TermArena::new();
    let x = arena.real_var("x").unwrap();
    let two = arena.real_const(Rational::integer(2));
    let zero = arena.real_const(Rational::zero());
    let one_const = arena.real_const(Rational::integer(1));
    let at_least_two = arena.real_ge(x, two).unwrap();
    let non_negative = arena.real_ge(x, zero).unwrap();
    let square = arena.real_mul(x, x).unwrap();
    let doubled = arena.real_mul(two, x).unwrap();
    let rhs = arena.real_add(doubled, one_const).unwrap();
    let equation = arena.eq(square, rhs).unwrap();
    (arena, vec![at_least_two, non_negative, equation])
}

/// **Product multiplier sign.** `−(x−2)·x + (x² − 2x − 1) = −1` is a genuine
/// constant of the refuting sign, and the query is satisfiable. Only the
/// requirement that a product multiplier be strictly positive stops it.
#[test]
fn forgery_a_negative_product_multiplier_is_rejected() {
    let (arena, assertions) = product_forgery_setup();
    let negative_one = vec![(Vec::new(), Rational::integer(-1))];
    let cert = CasIdealCertificate {
        entries: vec![
            CasIdealEntry::AssertedProduct {
                first: assertions[0],
                second: assertions[1],
                multiplier: negative_one,
            },
            CasIdealEntry::Asserted {
                conjunct: assertions[2],
                kind: CasHypothesisKind::Equality,
                multiplier: one(),
            },
        ],
        constant: Rational::integer(-1),
    };
    assert!(
        !check_cas_ideal_certificate(&arena, &assertions, &cert),
        "a negative product multiplier was accepted"
    );
}

/// **Product citation.** The same combination, this time with a positive
/// multiplier but one factor an unasserted `x ≤ 0`, whose polynomial `−x` makes
/// the product `−(x−2)·x` non-negative-looking. `x ≤ 0` is false in every model
/// of the query, which is exactly why it must not be citable.
#[test]
fn forgery_an_uncited_product_factor_is_rejected() {
    let (mut arena, assertions) = product_forgery_setup();
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::zero());
    let unasserted = arena.real_le(x, zero).unwrap();
    let cert = CasIdealCertificate {
        entries: vec![
            CasIdealEntry::AssertedProduct {
                first: assertions[0],
                second: unasserted,
                multiplier: one(),
            },
            CasIdealEntry::Asserted {
                conjunct: assertions[2],
                kind: CasHypothesisKind::Equality,
                multiplier: one(),
            },
        ],
        constant: Rational::integer(-1),
    };
    assert!(
        !check_cas_ideal_certificate(&arena, &assertions, &cert),
        "an unasserted product factor was accepted"
    );
}
