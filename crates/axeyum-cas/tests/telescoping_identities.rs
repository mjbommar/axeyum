//! Classical binomial identities, proved end to end by creative telescoping and
//! re-checked by the independent certificate checker.
//!
//! Each test does the same four things, in the same order:
//!
//! 1. state the summand as a [`HyperTerm`] specification;
//! 2. run [`zeilberger`] — an untrusted search — to obtain a certificate;
//! 3. hand the certificate to [`check_certificate`], which shares no code with
//!    the search and re-derives everything from the specification, including a
//!    cross-check against exact factorials;
//! 4. where a closed form is claimed, run [`check_closed_form`] to turn the
//!    verified recurrence into the identity.
//!
//! The tamper tests at the end are the point of the exercise: they perturb a
//! verified certificate and confirm the checker **rejects** it. A checker that
//! accepts everything is the failure mode that matters.

use std::collections::BTreeMap;

use axeyum_cas::mvpoly::MvPoly;
use axeyum_cas::telescoping::{
    Factor, HyperTerm, Limits, LinearForm, TelescopingCertificate, TelescopingOutcome,
    binomial_factors, zeilberger,
};
use axeyum_cas::telescoping_check::{
    CheckOptions, check_certificate, check_closed_form, check_closed_form_symbolic,
    evaluate_term_symbolic, symbolic_window_sum,
};
use axeyum_ir::Rational;

fn form(terms: &[(&str, i64)], constant: i64) -> LinearForm {
    LinearForm::new(terms, constant)
}

/// `Σ coefficient·variable + constant` as a polynomial, for stating an expected
/// recurrence coefficient.
fn linear_poly(terms: &[(&str, i128)], constant: i128) -> MvPoly {
    let mut poly = MvPoly::constant(Rational::integer(constant));
    for (name, coefficient) in terms {
        poly = poly
            .add(
                &MvPoly::var(name)
                    .mul(&MvPoly::constant(Rational::integer(*coefficient)))
                    .unwrap(),
            )
            .unwrap();
    }
    poly
}

/// Assert the discovered recurrence is exactly the expected one.
fn assert_recurrence(certificate: &TelescopingCertificate, expected: &[MvPoly]) {
    assert_eq!(
        certificate.recurrence.as_slice(),
        expected,
        "the discovered recurrence is not the classical one"
    );
}

/// `C(n,k)^power`.
fn binomial_n_k(power: i32) -> Vec<Factor> {
    binomial_factors(&form(&[("n", 1)], 0), &form(&[("k", 1)], 0), power)
}

/// Search for a certificate and verify it independently, returning it.
fn proved(
    term: &HyperTerm,
    shift_var: &str,
    sum_var: &str,
    options: &CheckOptions,
) -> TelescopingCertificate {
    proved_within(term, shift_var, sum_var, options, &Limits::classical())
}

/// [`proved`] with an explicit search budget.
fn proved_within(
    term: &HyperTerm,
    shift_var: &str,
    sum_var: &str,
    options: &CheckOptions,
    limits: &Limits,
) -> TelescopingCertificate {
    let TelescopingOutcome::Found(certificate) = zeilberger(term, shift_var, sum_var, limits)
    else {
        panic!("creative telescoping declined");
    };
    let verdict = check_certificate(&certificate, options);
    assert!(
        verdict.is_verified(),
        "the independent checker rejected a certificate: {verdict:?}"
    );
    *certificate
}

/// The row sum `∑_k C(n,k) = 2ⁿ`.
#[test]
fn binomial_row_sum_is_a_power_of_two() {
    let term = HyperTerm::new(binomial_n_k(1));
    let options = CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6, 7], (-2, 14));
    let certificate = proved(&term, "n", "k", &options);

    // The recurrence is S(n+1) = 2·S(n), up to the overall sign the search
    // normalizes to: a_0 = −2·a_1 with a_1 a nonzero constant.
    assert_eq!(certificate.order(), 1);
    let leading = certificate.recurrence[1].clone();
    assert_eq!(leading.total_degree(), 0, "a_1 must be constant");
    assert!(!leading.is_zero());
    assert_eq!(
        certificate.recurrence[0],
        leading
            .mul(&MvPoly::constant(Rational::integer(-2)))
            .unwrap()
    );

    // 2ⁿ satisfies the same recurrence and agrees at n = 0.
    let closed = HyperTerm::new(vec![Factor::Power {
        base: Rational::integer(2),
        form: form(&[("n", 1)], 0),
    }]);
    let report = check_closed_form(&certificate, &closed, 0, &options)
        .expect("2^n must satisfy the certified recurrence");
    assert_eq!(report.base_cases, 1);
    assert!(report.leading_zeros.is_empty());
}

/// The alternating row sum `∑_k (−1)^k C(n,k) = 0` for `n ≥ 1`.
#[test]
fn alternating_binomial_row_sum_vanishes() {
    let mut factors = vec![Factor::Power {
        base: Rational::integer(-1),
        form: form(&[("k", 1)], 0),
    }];
    factors.extend(binomial_n_k(1));
    let term = HyperTerm::new(factors);
    let options = CheckOptions::over("n", &[1, 2, 3, 4, 5, 6, 7], (-2, 14));
    let certificate = proved(&term, "n", "k", &options);

    // Order ZERO: the summand itself telescopes in k, and the recurrence is the
    // bare `n·S(n) = 0`. The leading coefficient `n` is exactly the reason the
    // identity is stated for n ≥ 1 — it vanishes at n = 0, where S(0) = 1.
    assert_recurrence(&certificate, &[linear_poly(&[("n", 1)], 0)]);
    assert_eq!(certificate.order(), 0);
    let mut point: BTreeMap<String, i64> = BTreeMap::new();
    for n in 1..=9 {
        point.insert("n".to_owned(), n);
        let mut total = num_rational::BigRational::from_integer(num_bigint::BigInt::from(0));
        for k in -2..=14 {
            point.insert("k".to_owned(), k);
            total += axeyum_cas::telescoping_check::evaluate_term(&term, &point)
                .expect("the term is exactly evaluable");
        }
        assert!(
            num_traits::Zero::is_zero(&total),
            "the alternating row sum must vanish at n = {n}"
        );
    }
}

/// `∑_k C(n,k)² = C(2n,n)`.
#[test]
fn sum_of_squared_binomials_is_the_central_binomial() {
    let term = HyperTerm::new(binomial_n_k(2));
    let options = CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6], (-2, 12));
    let certificate = proved(&term, "n", "k", &options);
    // (4n+2)·S(n) − (n+1)·S(n+1) = 0, the classical central-binomial recurrence.
    assert_recurrence(
        &certificate,
        &[linear_poly(&[("n", 4)], 2), linear_poly(&[("n", -1)], -1)],
    );

    let closed = HyperTerm::new(binomial_factors(
        &form(&[("n", 2)], 0),
        &form(&[("n", 1)], 0),
        1,
    ));
    let report = check_closed_form(&certificate, &closed, 0, &options)
        .expect("C(2n,n) must satisfy the certified recurrence");
    assert_eq!(report.base_cases, 1);
    assert!(report.leading_zeros.is_empty());
}

/// `∑_k k·C(n,k) = n·2^{n−1}`.
#[test]
fn weighted_binomial_row_sum_is_n_times_a_power_of_two() {
    let mut factors = vec![Factor::Poly {
        poly: MvPoly::var("k"),
        exponent: 1,
    }];
    factors.extend(binomial_n_k(1));
    let term = HyperTerm::new(factors);
    let options = CheckOptions::over("n", &[1, 2, 3, 4, 5, 6, 7], (-2, 14));
    let certificate = proved(&term, "n", "k", &options);
    // (2n+2)·S(n) − n·S(n+1) = 0.
    assert_recurrence(
        &certificate,
        &[linear_poly(&[("n", 2)], 2), linear_poly(&[("n", -1)], 0)],
    );

    // n·2^{n−1} = (1/2)·n·2ⁿ.
    let closed = HyperTerm::new(vec![
        Factor::Poly {
            poly: MvPoly::var("n"),
            exponent: 1,
        },
        Factor::Power {
            base: Rational::new(1, 2),
            form: form(&[], 1),
        },
        Factor::Power {
            base: Rational::integer(2),
            form: form(&[("n", 1)], 0),
        },
    ]);
    let report = check_closed_form(&certificate, &closed, 1, &options)
        .expect("n·2^(n−1) must satisfy the certified recurrence");
    assert!(report.base_cases >= 1);
    assert!(report.leading_zeros.is_empty());
}

/// Chu–Vandermonde: `∑_k C(m,k)·C(n,p−k) = C(m+n,p)`, with the recurrence taken
/// in `p` while `m` and `n` stay symbolic.
#[test]
fn chu_vandermonde_convolution() {
    let mut factors = binomial_factors(&form(&[("m", 1)], 0), &form(&[("k", 1)], 0), 1);
    factors.extend(binomial_factors(
        &form(&[("n", 1)], 0),
        &form(&[("p", 1), ("k", -1)], 0),
        1,
    ));
    let term = HyperTerm::new(factors);
    let options = CheckOptions::over("p", &[0, 1, 2, 3, 4], (-2, 12))
        .with("m", &[3, 5])
        .with("n", &[4, 6]);
    // Default limits. Four variables used to make the ansatz sweep unaffordable
    // (~18 s in release, ~250 s in debug); with the certificate denominator and
    // degree derived from the Gosper–Petkovšek normal form there is nothing left
    // to sweep, so no hand-tightened budget is needed.
    let certificate = proved(&term, "p", "k", &options);
    // (m+n−p)·S(p) − (p+1)·S(p+1) = 0, valid for symbolic m and n. Combined with
    // S(0) = 1 this is Chu–Vandermonde; only the recurrence is certified here.
    assert_recurrence(
        &certificate,
        &[
            linear_poly(&[("m", 1), ("n", 1), ("p", -1)], 0),
            linear_poly(&[("p", -1)], -1),
        ],
    );

    // The closed form, at symbolic m and n. The base case S(0) = 1 is decided,
    // not sampled: at p = 0 the parameter-free Γ factors Γ(k+1)⁻¹ and Γ(−k+1)⁻¹
    // force the support to {0}, and the surviving term's Γ powers cancel.
    let closed = HyperTerm::new(binomial_factors(
        &form(&[("m", 1), ("n", 1)], 0),
        &form(&[("p", 1)], 0),
        1,
    ));
    let report = check_closed_form_symbolic(&certificate, &closed, 0, &options)
        .expect("C(m+n,p) must be forced by the recurrence and the symbolic base case");
    assert_eq!(report.base_cases, 1);
    assert_eq!(report.forced_support, (0, 0));
    assert!(report.leading_zeros.is_empty());
    assert!(report.confirmed_zero_points >= 12);
}

/// `∑_k C(m,k)·C(n,k) = C(m+n,n)`, with the recurrence in `n` and `m` symbolic
/// throughout — closed form and all.
#[test]
fn cross_binomial_sum_is_a_central_binomial() {
    let mut factors = binomial_factors(&form(&[("m", 1)], 0), &form(&[("k", 1)], 0), 1);
    factors.extend(binomial_factors(
        &form(&[("n", 1)], 0),
        &form(&[("k", 1)], 0),
        1,
    ));
    let term = HyperTerm::new(factors);
    let options = CheckOptions::over("n", &[0, 1, 2, 3, 4], (-2, 12)).with("m", &[3, 5, 7]);
    let certificate = proved(&term, "n", "k", &options);
    assert_eq!(certificate.order(), 1);

    let closed = HyperTerm::new(binomial_factors(
        &form(&[("m", 1), ("n", 1)], 0),
        &form(&[("n", 1)], 0),
        1,
    ));
    let report = check_closed_form_symbolic(&certificate, &closed, 0, &options)
        .expect("C(m+n,n) must be forced by the certified recurrence and the symbolic base case");
    assert_eq!(report.base_cases, 1);
    assert!(report.leading_zeros.is_empty());
    // The base case is a genuine collapse: at n = 0 the parameter-free Γ factors
    // pin k to a single point, and every other window point is *checked* zero.
    assert_eq!(report.forced_support, (0, 0));
    assert!(report.confirmed_zero_points >= 12);
}

/// The Franel numbers `∑_k C(n,k)³`: a **second-order** recurrence, which is the
/// class the sweep-based search could not afford at all.
///
/// There is no hypergeometric closed form, so none is claimed. The recurrence is
/// the result, and it is the classical one.
#[test]
fn franel_numbers_get_an_order_two_recurrence() {
    let term = HyperTerm::new(binomial_n_k(3));
    let options = CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6], (-2, 14));
    let certificate = proved(&term, "n", "k", &options);
    assert_eq!(certificate.order(), 2);
    // 8(n+1)²·S(n) + (7n²+21n+16)·S(n+1) − (n+2)²·S(n+2) = 0.
    let square = |terms: &[(&str, i128)], constant: i128, scale: i128| {
        linear_poly(terms, constant)
            .pow(2)
            .unwrap()
            .mul(&MvPoly::constant(Rational::integer(scale)))
            .unwrap()
    };
    let middle = MvPoly::var("n")
        .pow(2)
        .unwrap()
        .mul(&MvPoly::constant(Rational::integer(7)))
        .unwrap()
        .add(&linear_poly(&[("n", 21)], 16))
        .unwrap();
    assert_recurrence(
        &certificate,
        &[
            square(&[("n", 1)], 1, 8),
            middle,
            square(&[("n", 1)], 2, -1),
        ],
    );

    // Independent sanity: the Franel numbers themselves satisfy it.
    let franel = [1i64, 2, 10, 56, 346, 2252, 15184];
    for index in 0..franel.len() - 2 {
        let n = i128::try_from(index).unwrap();
        assert_eq!(
            8 * (n + 1) * (n + 1) * i128::from(franel[index])
                + (7 * n * n + 21 * n + 16) * i128::from(franel[index + 1]),
            (n + 2) * (n + 2) * i128::from(franel[index + 2]),
            "the certified recurrence must hold on the Franel numbers"
        );
    }
}

// ---------------------------------------------------------------------------
// Tamper control: the symbolic base-case route must reject too.
// ---------------------------------------------------------------------------

/// Build the Chu–Vandermonde certificate once, for the symbolic tamper tests.
fn chu_vandermonde() -> (TelescopingCertificate, CheckOptions) {
    let mut factors = binomial_factors(&form(&[("m", 1)], 0), &form(&[("k", 1)], 0), 1);
    factors.extend(binomial_factors(
        &form(&[("n", 1)], 0),
        &form(&[("p", 1), ("k", -1)], 0),
        1,
    ));
    let options = CheckOptions::over("p", &[0, 1, 2, 3, 4], (-2, 12))
        .with("m", &[3, 5])
        .with("n", &[4, 6]);
    let certificate = proved(&HyperTerm::new(factors), "p", "k", &options);
    (certificate, options)
}

#[test]
fn a_symbolic_closed_form_with_the_wrong_base_is_rejected() {
    let (certificate, options) = chu_vandermonde();
    // 2·C(m+n,p) satisfies the same recurrence — the recurrence is homogeneous —
    // and fails only at the base case, which is now checked at symbolic m and n.
    let mut doubled = vec![Factor::Poly {
        poly: MvPoly::constant(Rational::integer(2)),
        exponent: 1,
    }];
    doubled.extend(binomial_factors(
        &form(&[("m", 1), ("n", 1)], 0),
        &form(&[("p", 1)], 0),
        1,
    ));
    let reasons = check_closed_form_symbolic(&certificate, &HyperTerm::new(doubled), 0, &options)
        .expect_err("2·C(m+n,p) must fail the symbolic base case");
    assert!(
        reasons.iter().any(|reason| reason.contains("base case")),
        "the rejection must name the base case: {reasons:?}"
    );
}

#[test]
fn a_symbolic_closed_form_with_the_wrong_ratio_is_rejected() {
    let (certificate, options) = chu_vandermonde();
    // C(m+n,p+1) has base value 1 at p = 0 too, so only the annihilation check
    // can catch it.
    let wrong = HyperTerm::new(binomial_factors(
        &form(&[("m", 1), ("n", 1)], 0),
        &form(&[("p", 1)], 1),
        1,
    ));
    let reasons = check_closed_form_symbolic(&certificate, &wrong, 0, &options)
        .expect_err("C(m+n,p+1) must fail the annihilation check");
    assert!(
        reasons.iter().any(|reason| reason.contains("annihilate")),
        "the rejection must name the annihilation check: {reasons:?}"
    );
}

#[test]
fn a_symbolic_closed_form_with_an_uncancelled_gamma_is_rejected() {
    let (certificate, options) = chu_vandermonde();
    // C(m+n,p)·Γ(m+1) has the right ratio in p, and its base value is Γ(m+1) —
    // not a rational. The checker must say so rather than compare coefficients.
    let mut dressed = binomial_factors(&form(&[("m", 1), ("n", 1)], 0), &form(&[("p", 1)], 0), 1);
    dressed.push(Factor::Gamma {
        form: form(&[("m", 1)], 1),
        exponent: 1,
    });
    let reasons = check_closed_form_symbolic(&certificate, &HyperTerm::new(dressed), 0, &options)
        .expect_err("an uncancelled Γ must not be compared as a rational");
    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("uncancelled Γ power")),
        "the rejection must name the uncancelled Γ: {reasons:?}"
    );
}

#[test]
fn a_symbolic_window_that_clips_the_forced_support_is_rejected() {
    let (certificate, _) = chu_vandermonde();
    let closed = HyperTerm::new(binomial_factors(
        &form(&[("m", 1), ("n", 1)], 0),
        &form(&[("p", 1)], 0),
        1,
    ));
    // The forced support at p = 0 is {0}; a window starting at 0 does not
    // strictly contain it, so the vanishing outside is not established.
    let clipped = CheckOptions::over("p", &[0, 1, 2], (0, 6))
        .with("m", &[3])
        .with("n", &[4]);
    let reasons = check_closed_form_symbolic(&certificate, &closed, 0, &clipped)
        .expect_err("a window that does not strictly contain the forced support must be rejected");
    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("does not strictly contain")),
        "the rejection must name the window: {reasons:?}"
    );
}

/// A summand whose support is not pinned by parameter-free `Γ` factors must make
/// the symbolic route **decline**, not guess a truncation.
#[test]
fn an_unbounded_symbolic_support_declines() {
    // 1/k! is nonzero for every k ≥ 0: bounded below, unbounded above.
    let term = HyperTerm::new(vec![Factor::Gamma {
        form: form(&[("k", 1)], 1),
        exponent: -1,
    }]);
    let reason = symbolic_window_sum(&term, &BTreeMap::new(), "k", (-4, 12))
        .expect_err("an unbounded support must not be summed");
    assert!(
        reason.contains("not forced finite"),
        "the refusal must name the support: {reason}"
    );
}

/// The symbolic evaluator must agree with the concrete one wherever both apply —
/// the two are separate code paths and this is what keeps them honest.
#[test]
fn symbolic_and_concrete_evaluation_agree_on_bound_points() {
    let term = HyperTerm::new(binomial_n_k(2));
    let mut point: BTreeMap<String, i64> = BTreeMap::new();
    let mut compared = 0usize;
    for n in 0..=6i64 {
        for k in -2..=8i64 {
            point.insert("n".to_owned(), n);
            point.insert("k".to_owned(), k);
            let concrete = axeyum_cas::telescoping_check::evaluate_term(&term, &point)
                .expect("C(n,k)² is exactly evaluable");
            let symbolic = evaluate_term_symbolic(&term, &point)
                .expect("with every variable bound the symbolic route is total");
            assert!(symbolic.is_rational());
            assert_eq!(symbolic.coefficient(), &concrete, "at n={n}, k={k}");
            compared += 1;
        }
    }
    assert_eq!(compared, 7 * 11);
}

// ---------------------------------------------------------------------------
// Tamper control: the checker must reject perturbed certificates.
// ---------------------------------------------------------------------------

fn tampered(certificate: &TelescopingCertificate, options: &CheckOptions, label: &str) {
    let verdict = check_certificate(certificate, options);
    assert!(
        !verdict.is_verified(),
        "the checker ACCEPTED a tampered certificate ({label}): {verdict:?}"
    );
}

#[test]
fn a_perturbed_certificate_numerator_is_rejected() {
    let term = HyperTerm::new(binomial_n_k(1));
    let options = CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6, 7], (-2, 14));
    let good = proved(&term, "n", "k", &options);

    // Add 1 to P. R changes, so the telescoping identity no longer holds.
    let mut bad = good.clone();
    bad.certificate_numerator = bad
        .certificate_numerator
        .add(&MvPoly::constant(Rational::integer(1)))
        .unwrap();
    tampered(&bad, &options, "P + 1");

    // Scale P by 2.
    let mut bad = good.clone();
    bad.certificate_numerator = bad
        .certificate_numerator
        .mul(&MvPoly::constant(Rational::integer(2)))
        .unwrap();
    tampered(&bad, &options, "2·P");

    // Perturb the certificate denominator.
    let mut bad = good.clone();
    bad.certificate_denominator = bad.certificate_denominator.add(&MvPoly::var("k")).unwrap();
    tampered(&bad, &options, "Q + k");

    // Perturb the recurrence: S(n+1) − 3·S(n) = 0 is false.
    let mut bad = good.clone();
    bad.recurrence[0] = MvPoly::constant(Rational::integer(-3));
    tampered(&bad, &options, "wrong recurrence constant");

    // A degree bump in a recurrence coefficient.
    let mut bad = good.clone();
    bad.recurrence[1] = bad.recurrence[1].add(&MvPoly::var("n")).unwrap();
    tampered(&bad, &options, "a_1 + n");

    // Zeroing the recurrence leaves nothing asserted.
    let mut bad = good.clone();
    bad.recurrence = vec![MvPoly::zero(), MvPoly::zero()];
    tampered(&bad, &options, "zero recurrence");
}

#[test]
fn a_certificate_for_the_wrong_term_is_rejected() {
    let squares = HyperTerm::new(binomial_n_k(2));
    let options = CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6], (-2, 12));
    let good = proved(&squares, "n", "k", &options);

    // The same certificate, re-pointed at ∑_k C(n,k): the recurrence and the
    // rational identity are both wrong for it.
    let mut bad = good.clone();
    bad.term = HyperTerm::new(binomial_n_k(1));
    tampered(&bad, &options, "certificate re-pointed at another term");
}

#[test]
fn a_wrong_closed_form_is_rejected() {
    let term = HyperTerm::new(binomial_n_k(1));
    let options = CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6, 7], (-2, 14));
    let certificate = proved(&term, "n", "k", &options);

    // 3ⁿ satisfies S(n+1) = 3·S(n), not the certified S(n+1) = 2·S(n).
    let wrong_ratio = HyperTerm::new(vec![Factor::Power {
        base: Rational::integer(3),
        form: form(&[("n", 1)], 0),
    }]);
    assert!(
        check_closed_form(&certificate, &wrong_ratio, 0, &options).is_err(),
        "3^n must not pass the annihilation check"
    );

    // 3·2ⁿ satisfies the recurrence but fails the base case.
    let wrong_base = HyperTerm::new(vec![
        Factor::Poly {
            poly: MvPoly::constant(Rational::integer(3)),
            exponent: 1,
        },
        Factor::Power {
            base: Rational::integer(2),
            form: form(&[("n", 1)], 0),
        },
    ]);
    assert!(
        check_closed_form(&certificate, &wrong_base, 0, &options).is_err(),
        "3·2^n must fail the base case"
    );
}

/// A window that does not contain the support must be rejected, not silently
/// truncated: the telescoped sum would otherwise be compared against a boundary
/// term that is not zero.
#[test]
fn a_window_that_clips_the_support_is_rejected() {
    let term = HyperTerm::new(binomial_n_k(1));
    let honest = CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6, 7], (-2, 14));
    let certificate = proved(&term, "n", "k", &honest);
    let clipped = CheckOptions::over("n", &[6, 7], (0, 4));
    let verdict = check_certificate(&certificate, &clipped);
    assert!(
        !verdict.is_verified(),
        "a window narrower than the support must be rejected: {verdict:?}"
    );
}
