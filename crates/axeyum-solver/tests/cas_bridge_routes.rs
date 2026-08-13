//! The two CAS bridge routes (ADR-0386): `cas-identity-refuter` and
//! `cas-int-units`.
//!
//! Both routes turn `unknown` into `unsat` on shapes the integer bit-blast width
//! ladder structurally cannot close, so every test here is paired: a positive
//! case pinning the new decision, and a **negative control** pinning that the
//! route declines rather than refuting a satisfiable query. A refuter that never
//! declines is worthless; a refuter that refutes a `sat` query is a P0.
//!
//! The `route` assertions matter as much as the verdicts. `cas-*` routes sit on
//! the fast path ahead of every theory engine, so a silent misfire would show up
//! as a wrong verdict somewhere far away; pinning the deciding route keeps the
//! measurement honest about *which* code closed the query.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CasIntUnitsKind, CasOutcome, CheckResult, RouteOutcome, SolverConfig, Verdict,
    cas_identity_refutation, cas_int_units_refutation, check_cas_identity_certificate,
    check_cas_int_units_certificate,
};

/// A generous budget: every case here is meant to decide in microseconds, so a
/// case that needs the budget is a case that regressed off the CAS route.
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

fn assert_unsat_via(text: &str, expected_route: &str) {
    let (result, route, trace) = solve(text);
    assert_eq!(result, CheckResult::Unsat, "trace:\n{trace}");
    assert_eq!(route, expected_route, "trace:\n{trace}");
}

fn assert_sat_not_via_cas(text: &str) {
    let (result, _, trace) = solve(text);
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "expected sat, got {result:?}\ntrace:\n{trace}"
    );
    // Belt and braces: the query is satisfiable, so no `cas-*` route may have
    // decided it. `check_auto` returning `sat` already proves that, but pinning
    // the trace catches a future reordering that lets a CAS route answer first.
    for line in trace.lines() {
        assert!(
            !(line.starts_with("cas-") && line.contains("decided")),
            "a cas route decided a satisfiable query\ntrace:\n{trace}"
        );
    }
}

// ---------------------------------------------------------------------------
// Route 1: cas-identity-refuter
// ---------------------------------------------------------------------------

/// The identity refuter's reach beyond `int-real-relax`: the same polynomial
/// identity, in a query whose *other* conjunct carries an underspecified `div`.
/// Measured before this route existed: `unknown(Timeout)` after 15 s, declining
/// through `int-blast-ladder`. Now `unsat` in microseconds.
#[test]
fn identity_refuted_beside_an_unspecified_div() {
    assert_unsat_via(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun k () Int)
(assert (>= k 1))
(assert (= (div k 3) 2))
(assert (not (= (* (+ a b) (+ a b)) (+ (* a a) (* 2 (* a b)) (* b b)))))
(check-sat)
",
        "cas-identity-refuter",
    );
}

/// Rational coefficients: `(a + b/2)² = a² + ab + b²/4`. The real routes
/// declined on the literal division (`nra-real-root: not-applicable`) and the
/// lazy NRA engine burned the whole budget; exact ℚ normalization closes it.
#[test]
fn identity_refuted_with_rational_coefficients() {
    assert_unsat_via(
        r"
(set-logic QF_NRA)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (not (= (* (+ a (/ b 2.0)) (+ a (/ b 2.0)))
                (+ (* a a) (* a b) (/ (* b b) 4.0)))))
(check-sat)
",
        "cas-identity-refuter",
    );
}

/// Opaque atoms: `f(x)` and `g(y)` are uninterpreted applications, abstracted to
/// atoms. The identity holds whatever they denote — this is the "generalising a
/// lemma made it harder" shape, which a CAS handles by construction.
#[test]
fn identity_refuted_over_uninterpreted_atoms() {
    assert_unsat_via(
        r"
(set-logic QF_UFNIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (not (= (* (+ (f x) (g y)) (+ (f x) (g y)))
                (+ (* (f x) (f x)) (* 2 (* (f x) (g y))) (* (g y) (g y))))))
(check-sat)
",
        "cas-identity-refuter",
    );
}

/// Degree 9 in three variables: `((a+b+c)³)³ = (a+b+c)⁹`. Exercised because a
/// normal-form refuter should be insensitive to degree where a search is not.
#[test]
fn identity_refuted_at_degree_nine() {
    assert_unsat_via(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (not (= (* (* (+ a b c) (* (+ a b c) (+ a b c)))
                   (* (* (+ a b c) (* (+ a b c) (+ a b c)))
                      (* (+ a b c) (* (+ a b c) (+ a b c)))))
                (* (+ a b c) (* (+ a b c) (* (+ a b c) (* (+ a b c)
                   (* (+ a b c) (* (+ a b c) (* (+ a b c) (* (+ a b c) (+ a b c))))))))))))
(check-sat)
",
        "cas-identity-refuter",
    );
}

/// NEGATIVE CONTROL — a near miss. One coefficient differs (`3ab`, not `2ab`),
/// so the difference is `ab`, not zero, and the query is genuinely satisfiable
/// (`a = b = 1` gives `4 ≠ 5`). The route must decline.
#[test]
fn near_miss_identity_is_not_refuted() {
    assert_sat_not_via_cas(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (not (= (* (+ a b) (+ a b)) (+ (* a a) (* 3 (* a b)) (* b b)))))
(check-sat)
",
    );
}

/// NEGATIVE CONTROL — two *different* `div` terms. Abstracting both to atoms
/// must keep them distinct: `div x y` and `div y x` differ (x=1, y=2 gives 0 and
/// 2), so the disequality is satisfiable. Collapsing distinct subterms onto one
/// atom is the single unsound direction of the abstraction; this pins it.
#[test]
fn distinct_div_terms_are_distinct_atoms() {
    assert_sat_not_via_cas(
        r"
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (not (= (div x y) (div y x))))
(check-sat)
",
    );
}

/// NEGATIVE CONTROL — division by a *variable* is not polynomial. `(a/b)·b = a`
/// fails at `b = 0` under SMT-LIB's underspecified `/`, so the disequality is
/// satisfiable and the route must not fold the division away.
#[test]
fn real_division_by_a_variable_is_not_folded() {
    assert_sat_not_via_cas(
        r"
(set-logic QF_NRA)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= b 0.0))
(assert (= a 1.0))
(assert (not (= (* (/ a b) b) a)))
(check-sat)
",
    );
}

/// NEGATIVE CONTROL — a non-arithmetic disequality. Bit-vector sides are outside
/// the polynomial fragment, so the route must not even claim a candidate.
#[test]
fn bitvector_disequality_is_not_a_candidate() {
    let mut script = parse_script(
        r"
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (not (= x x)))
(check-sat)
",
    )
    .expect("parse");
    let assertions = script.assertions.clone();
    assert_eq!(
        cas_identity_refutation(&script.arena, &assertions),
        CasOutcome::NoCandidate
    );
    // The narrow `term-identity-refuter` still closes it — the CAS route
    // declining does not cost the verdict.
    let (result, trace) =
        axeyum_solver::check_auto_explained(&mut script.arena, &assertions, &config())
            .expect("solve");
    assert_eq!(result, CheckResult::Unsat, "trace:\n{trace}");
}

// ---------------------------------------------------------------------------
// Route 2: cas-int-units
// ---------------------------------------------------------------------------

/// The headline case. `∃a,p. a ≥ 2 ∧ a·p = 1` — no integer unit is ≥ 2.
/// Measured before this route: `unknown(Timeout)` at 20 s and 60 s, with
/// `int-blast-ladder` reporting "no model within the bounded integer width 32".
#[test]
fn units_a_times_p_equals_one_is_refuted() {
    assert_unsat_via(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun p () Int)
(assert (>= a 2))
(assert (= (* a p) 1))
(check-sat)
",
        "cas-int-units",
    );
}

/// The negative branch: `a ≤ −2` is equally outside the units.
#[test]
fn units_with_a_negative_bound_is_refuted() {
    assert_unsat_via(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun p () Int)
(assert (<= a (- 2)))
(assert (= (* a p) 1))
(check-sat)
",
        "cas-int-units",
    );
}

/// Three factors and a cubed factor — the divisor bound is about the monomial,
/// not about a two-way product.
#[test]
fn units_with_three_factors_is_refuted() {
    assert_unsat_via(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun q () Int)
(assert (>= a 2))
(assert (>= b 2))
(assert (= (* a (* b q)) 1))
(check-sat)
",
        "cas-int-units",
    );
}

/// `a ∤ j` in the refutation direction: `a·s = 12` with `a ≥ 13` has no
/// solution, because every factor of 12 has absolute value at most 12.
#[test]
fn divisibility_bound_above_the_dividend_is_refuted() {
    assert_unsat_via(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun s () Int)
(assert (>= a 13))
(assert (= (* a s) 12))
(check-sat)
",
        "cas-int-units",
    );
}

/// A cubed symbolic divisor: `a³·s = 1` with `a ≥ 2`. Also measured as a 20 s
/// `unknown` before this route.
#[test]
fn cubed_symbolic_divisor_is_refuted() {
    assert_unsat_via(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun s () Int)
(assert (>= a 2))
(assert (= (* a (* a (* a s))) 1))
(check-sat)
",
        "cas-int-units",
    );
}

/// `2·a·b = 3` needs no bounds at all: the left side is even.
#[test]
fn even_product_equal_to_an_odd_constant_is_refuted() {
    assert_unsat_via(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= (* 2 (* a b)) 3))
(check-sat)
",
        "cas-int-units",
    );
}

/// A zero product whose every factor is bounded away from zero.
#[test]
fn zero_product_with_nonzero_factors_is_refuted() {
    assert_unsat_via(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (>= a 1))
(assert (<= b (- 1)))
(assert (= (* a b) 0))
(check-sat)
",
        "cas-int-units",
    );
}

/// NEGATIVE CONTROL — `a ≥ 1 ∧ a·p = 1` is satisfiable at `a = p = 1`: the
/// bound is exactly at the divisor limit, not past it.
#[test]
fn units_at_the_bound_are_not_refuted() {
    assert_sat_not_via_cas(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun p () Int)
(assert (>= a 1))
(assert (= (* a p) 1))
(check-sat)
",
    );
}

/// NEGATIVE CONTROL — one off the limit. `a·s = 12` with `a ≥ 12` is satisfiable
/// (`a = 12`, `s = 1`); only `a ≥ 13` refutes. This pins the `>` in the divisor
/// comparison, the exact place an off-by-one would produce a wrong `unsat`.
#[test]
fn divisibility_bound_at_the_dividend_is_not_refuted() {
    assert_sat_not_via_cas(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun s () Int)
(assert (>= a 12))
(assert (= (* a s) 12))
(check-sat)
",
    );
}

/// NEGATIVE CONTROL — `2·a·b = 4` *is* solvable (`a = 1`, `b = 2`), so the
/// even/odd argument must not fire when the coefficient does divide.
#[test]
fn even_product_equal_to_an_even_constant_is_not_refuted() {
    assert_sat_not_via_cas(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= (* 2 (* a b)) 4))
(check-sat)
",
    );
}

/// NEGATIVE CONTROL — a zero product whose factor *may* be zero.
#[test]
fn zero_product_with_a_possibly_zero_factor_is_not_refuted() {
    assert_sat_not_via_cas(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (>= a 0))
(assert (>= b 1))
(assert (= (* a b) 0))
(check-sat)
",
    );
}

/// NEGATIVE CONTROL — a bound on a *different* symbol must not be read as a
/// bound on a factor. `b ≥ 2` says nothing about `a` or `p`.
#[test]
fn a_bound_on_an_unrelated_symbol_is_not_used() {
    assert_sat_not_via_cas(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun p () Int)
(declare-fun b () Int)
(assert (>= b 2))
(assert (= (* a p) 1))
(check-sat)
",
    );
}

// ---------------------------------------------------------------------------
// Certificates: the independent checker is what makes the routes trustworthy
// ---------------------------------------------------------------------------

/// The identity certificate re-checks against the original assertions, and the
/// re-check is what the route's `unsat` rests on.
#[test]
fn identity_certificate_recheck_is_independent() {
    let script = parse_script(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (not (= (* (+ a b) (+ a b)) (+ (* a a) (* 2 (* a b)) (* b b)))))
(check-sat)
",
    )
    .expect("parse");
    let assertions = script.assertions.clone();
    let CasOutcome::Refuted(cert) = cas_identity_refutation(&script.arena, &assertions) else {
        panic!("expected a refutation");
    };
    assert!(check_cas_identity_certificate(
        &script.arena,
        &assertions,
        &cert
    ));
    // `(a+b)² = a² + 2ab + b²` has three monomials over two atoms.
    assert_eq!(cert.normal_form.len(), 3, "{:?}", cert.normal_form);

    // A tampered certificate must be rejected: swapping in a normal form that
    // is not the one the terms expand to breaks the audit trail even though the
    // underlying terms are still equal.
    let mut tampered = cert.clone();
    tampered.normal_form.pop();
    assert!(!check_cas_identity_certificate(
        &script.arena,
        &assertions,
        &tampered
    ));

    // A certificate citing an assertion that is not in the list is rejected.
    let mut foreign = cert.clone();
    foreign.assertion = cert.lhs;
    assert!(!check_cas_identity_certificate(
        &script.arena,
        &assertions,
        &foreign
    ));
}

/// The units certificate names the equation, the monomial, `k`, `c`, and the
/// bound conjunct — and every one of those is re-derived by the checker.
#[test]
fn units_certificate_recheck_is_independent() {
    let script = parse_script(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun p () Int)
(assert (>= a 2))
(assert (= (* a p) 1))
(check-sat)
",
    )
    .expect("parse");
    let assertions = script.assertions.clone();
    let CasOutcome::Refuted(cert) = cas_int_units_refutation(&script.arena, &assertions) else {
        panic!("expected a refutation");
    };
    assert_eq!(cert.kind, CasIntUnitsKind::DivisorBound);
    assert_eq!((cert.coefficient, cert.constant), (1, 1));
    assert_eq!(cert.monomial.len(), 2, "a·p is a two-factor monomial");
    assert!(check_cas_int_units_certificate(
        &script.arena,
        &assertions,
        &cert
    ));

    // Inflating the claimed bound past what the cited conjunct asserts must be
    // rejected: `a ≥ 2` does not entail `a ≥ 99`.
    let mut inflated = cert.clone();
    inflated.bounds[0].lower = Some(99);
    assert!(!check_cas_int_units_certificate(
        &script.arena,
        &assertions,
        &inflated
    ));

    // Claiming a bound on a factor from a conjunct that does not bound it.
    let mut misattributed = cert.clone();
    misattributed.bounds[0].source = cert.equation;
    assert!(!check_cas_int_units_certificate(
        &script.arena,
        &assertions,
        &misattributed
    ));

    // Re-labelling the refutation kind does not make a different argument valid:
    // `c = 1 ≠ 0`, so the zero-product rule cannot apply.
    let mut relabelled = cert.clone();
    relabelled.kind = CasIntUnitsKind::ZeroProduct;
    assert!(!check_cas_int_units_certificate(
        &script.arena,
        &assertions,
        &relabelled
    ));
}

/// The declines are recorded, not silent. A `QF_NIA` query the units route looks
/// at but cannot close must leave a `cas-int-units` decline in the trace —
/// the diagnosability rule the NIA routes had to learn the hard way.
#[test]
fn declines_are_recorded_in_the_route_trace() {
    let (_, _, trace) = solve(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun p () Int)
(assert (>= a 1))
(assert (= (* a p) 1))
(check-sat)
",
    );
    assert!(trace.contains("cas-int-units: declined"), "trace:\n{trace}");
}

/// A query with no arithmetic disequality and no integer equation leaves *no*
/// `cas-*` entry at all: declines are recorded where there was something to
/// decide, not appended to every trace in the system.
#[test]
fn no_candidate_leaves_no_trace_entry() {
    let (result, _, trace) = solve(
        r"
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 3))
(assert (< x 2))
(check-sat)
",
    );
    assert_eq!(result, CheckResult::Unsat, "trace:\n{trace}");
    assert!(!trace.contains("cas-"), "trace:\n{trace}");
}

/// Trace hygiene: a decided `cas-*` route is the terminal entry and is recorded
/// as a decision, so `check_auto_explained`'s structural invariant (an `Unknown`
/// ends in a decline) is untouched.
#[test]
fn a_deciding_cas_route_is_the_terminal_trace_entry() {
    let mut script = parse_script(
        r"
(set-logic QF_NIA)
(declare-fun a () Int)
(declare-fun p () Int)
(assert (>= a 2))
(assert (= (* a p) 1))
(check-sat)
",
    )
    .expect("parse");
    let assertions = script.assertions.clone();
    let (result, trace) =
        axeyum_solver::check_auto_explained(&mut script.arena, &assertions, &config())
            .expect("solve");
    assert_eq!(result, CheckResult::Unsat);
    let last = trace.last().expect("non-empty trace");
    assert_eq!(last.route, "cas-int-units", "trace:\n{trace}");
    assert!(matches!(
        last.outcome,
        RouteOutcome::Decided(Verdict::Unsat)
    ));
}
