//! CAS `SymPy` parity corpus harness (math-department file 13, item 10,
//! second half — `docs/plan/cas-parity-corpus-2026-09-05/README.md`).
//!
//! For every entry in `corpus.json`, this file's `entries()` reconstructs the
//! same query directly against `axeyum-cas`, independent of whatever
//! `corpus.json`'s `expected` field says (that field was independently
//! established by `../ground_truth.py`, never read by this program). Each
//! entry reports:
//!
//! - **verdict**: `agree` (axeyum's answer matches the independently
//!   established expected value), `disagree` (a wrong answer — a real
//!   finding), or `decline` (axeyum could not decide; honest, never scored
//!   as wrong).
//! - **trust**: `certified` (the decision carries a re-checkable certificate
//!   — a native one from the function under test, such as
//!   `CertifiedIntegral::is_certified`, `Enclosure::verify`,
//!   `HomologyCertificate::verify`, or a `ZeroTest::Certified` from this
//!   entry's own `equal`-based correctness check when the function under
//!   test returns a plain, uncertified value), `uncertified` (a decided
//!   answer with no such witness), or `unknown` (declined).
//! - **wall time** for the call under test.
//!
//! Run: `cargo run -p axeyum-cas --example parity_corpus --release`
//! (or `scripts/cargo-serialized.sh run -p axeyum-cas --example
//! parity_corpus --release` per this repo's multi-agent discipline).
//!
//! Exit status is nonzero iff any entry's verdict is `disagree`. A `decline`
//! is never a failure — some entries are *tiered* `decline_expected` and are
//! declining on purpose (an open problem, a documented capability gap, a
//! cited non-elementary/undecidable case); see `corpus.json`'s
//! `justification` field per entry, and the README's design-decision note on
//! why trust is derived per-entry rather than from one verdict type.
#![allow(clippy::too_many_lines)] // one flat entry table in main; length is inherent (cf. cas_tour.rs)

use std::time::Instant;

use axeyum_cas::enclosure::enclose_constant;
use axeyum_cas::geometry::Point;
use axeyum_cas::geometry_beyond::{self, Conic, Isometry};
use axeyum_cas::homology::{self, SimplicialComplex};
use axeyum_cas::numberfield::{self, QuadraticField, TwoSquaresCertificate};
use axeyum_cas::permgroup::PermutationGroup;
use axeyum_cas::permutation::Permutation;
use axeyum_cas::probability::{self, Discrete};
use axeyum_cas::qe::{self, Atom, ExistsFormula, ForallFormula, Relation};
use axeyum_cas::{
    CasExpr, LimitPoint, Matrix, ZeroTest, definite_integrate, dsolve_homogeneous,
    dsolve_inhomogeneous, eigenvectors, equal, factor, factor_expr, fps, gosper_sum, integrate,
    laplace_transform, limit, minimal_polynomial, ntheory, ntheory_advanced, series, solve,
    sum_polynomial, z_transform,
};
use axeyum_ir::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

// ============================================================================
// Framework
// ============================================================================

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Trust {
    Certified,
    Uncertified,
    Unknown,
}

impl Trust {
    fn label(self) -> &'static str {
        match self {
            Trust::Certified => "certified",
            Trust::Uncertified => "uncertified",
            Trust::Unknown => "unknown",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Agree,
    Disagree,
    Decline,
}

impl Verdict {
    fn label(self) -> &'static str {
        match self {
            Verdict::Agree => "agree",
            Verdict::Disagree => "disagree",
            Verdict::Decline => "decline",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tier {
    /// Deciding correctly is the point; a decline is an honest capability
    /// gap (not scored as a failure) but not the anticipated outcome.
    Core,
    /// This entry is expected to decline, or (for a `two_squares`-style
    /// classification entry) expected to land on a specific side — see
    /// `justification` in `corpus.json`. A decline here is the anticipated,
    /// correct behavior.
    DeclineExpected,
    /// A CONFIRMED, tracked wrong answer (not a decline) with an owning fix
    /// in flight elsewhere (see the entry's `tracked_by`). Excluded from the
    /// `agree`/`disagree`/`decline` tally and counted separately so this
    /// corpus's exit status does not redden every session's aggregate gate
    /// while the fix lands. The harness asserts the disagreement PERSISTS:
    /// if the entry starts agreeing, that is a HARD FAILURE (exit nonzero)
    /// demanding the entry be reclassified to `core` — a known defect can
    /// never be quietly forgotten, only fixed-and-promoted or left failing.
    KnownDefect,
}

impl Tier {
    fn label(self) -> &'static str {
        match self {
            Tier::Core => "core",
            Tier::DeclineExpected => "decline_expected",
            Tier::KnownDefect => "known_defect",
        }
    }
}

struct Outcome {
    verdict: Verdict,
    trust: Trust,
    expected: String,
    actual: String,
}

struct Entry {
    id: &'static str,
    area: Option<&'static str>,
    module: Option<&'static str>,
    tier: Tier,
    /// Who owns the fix for a `Tier::KnownDefect` entry (`None` for every
    /// other tier). Matches `corpus.json`'s `tracked_by` field.
    tracked_by: Option<&'static str>,
    run: fn() -> Outcome,
}

/// The decisive check for most "plain value" `axeyum-cas` functions
/// (`differentiate`, `limit`, `series`, `sum_polynomial`, `solve`, `factor`,
/// ...): does axeyum's computed expression equal an independently-built
/// expected expression? The `ZeroTest` this produces — `Certified` or
/// `Unknown` — is the entry's trust, exactly as `CertifiedIntegral`'s own
/// certificate *is* an `equal` call under the hood.
fn eq_check(
    actual: &CasExpr,
    expected: &CasExpr,
    expect_equal: bool,
    actual_label: &str,
) -> Outcome {
    match equal(actual, expected) {
        ZeroTest::Certified { equal: decided, .. } => Outcome {
            verdict: if decided == expect_equal {
                Verdict::Agree
            } else {
                Verdict::Disagree
            },
            trust: Trust::Certified,
            expected: format!("equal(_, {expected}) == {expect_equal}"),
            actual: format!("{actual_label}; equal(_, {expected}) == {decided}"),
        },
        ZeroTest::Unknown => Outcome {
            verdict: Verdict::Decline,
            trust: Trust::Unknown,
            expected: format!("equal(_, {expected}) == {expect_equal}"),
            actual: format!("{actual_label}; equal-check declined (Unknown)"),
        },
    }
}

/// A plain `axeyum-cas` function declined outright (`None`) before any
/// `equal`-based check was even possible.
fn declined(what: &str) -> Outcome {
    Outcome {
        verdict: Verdict::Decline,
        trust: Trust::Unknown,
        expected: "-".to_string(),
        actual: format!("{what} declined (None)"),
    }
}

fn bool_check(actual: bool, expected: bool, label_actual: &str) -> Outcome {
    Outcome {
        verdict: if actual == expected {
            Verdict::Agree
        } else {
            Verdict::Disagree
        },
        trust: Trust::Uncertified,
        expected: format!("{expected}"),
        actual: label_actual.to_string(),
    }
}

fn x() -> CasExpr {
    CasExpr::var("x")
}
fn i(n: i128) -> CasExpr {
    CasExpr::int(n)
}
fn r(num: i128, den: i128) -> CasExpr {
    CasExpr::rat(num, den)
}

// ============================================================================
// Entries: differentiate
// ============================================================================

fn d1_cubic() -> Outcome {
    let f = x().pow(3) - i(2) * x() + i(1);
    let d = f.differentiate("x");
    let expected = i(3) * x().pow(2) - i(2);
    eq_check(&d, &expected, true, &format!("d/dx = {d}"))
}
fn d1_cubic_ctrl() -> Outcome {
    let f = x().pow(3) - i(2) * x() + i(1);
    let d = f.differentiate("x");
    let wrong = i(3) * x().pow(2) - i(2) + i(1);
    eq_check(&d, &wrong, false, &format!("d/dx = {d}"))
}
fn d2_product() -> Outcome {
    let f = x() * x().sin();
    let d = f.differentiate("x");
    let expected = x().sin() + x() * x().cos();
    eq_check(&d, &expected, true, &format!("d/dx = {d}"))
}
fn d2_product_ctrl() -> Outcome {
    let f = x() * x().sin();
    let d = f.differentiate("x");
    let wrong = x().sin() - x() * x().cos();
    eq_check(&d, &wrong, false, &format!("d/dx = {d}"))
}
fn d3_chain() -> Outcome {
    let f = x().pow(2).sin();
    let d = f.differentiate("x");
    let expected = i(2) * x() * x().pow(2).cos();
    eq_check(&d, &expected, true, &format!("d/dx = {d}"))
}
fn d3_chain_ctrl() -> Outcome {
    let f = x().pow(2).sin();
    let d = f.differentiate("x");
    let wrong = i(2) * x().pow(2).cos();
    eq_check(&d, &wrong, false, &format!("d/dx = {d}"))
}

// ============================================================================
// Entries: integrate
// ============================================================================

fn i1_def_poly() -> Outcome {
    let integrand = i(3) * x().pow(2) + i(2) * x();
    match definite_integrate(&integrand, "x", &i(0), &i(1)) {
        Some(result) => eq_check(
            &result.value,
            &i(2),
            true,
            &format!("value={}", result.value),
        ),
        None => declined("definite_integrate(3x^2+2x, x, 0, 1)"),
    }
}
fn i2_def_log() -> Outcome {
    let e = i(1).exp();
    match definite_integrate(&(i(1) / x()), "x", &i(1), &e) {
        Some(result) => eq_check(
            &result.value,
            &i(1),
            true,
            &format!("value={}", result.value),
        ),
        None => declined("definite_integrate(1/x, x, 1, e)"),
    }
}
fn i3_indef_trig() -> Outcome {
    let f = x() * x().sin();
    match integrate(&f, "x") {
        Some(result) => {
            let expected = x().sin() - x() * x().cos();
            eq_check(
                &result.antiderivative,
                &expected,
                true,
                &format!("F={}", result.antiderivative),
            )
        }
        None => declined("integrate(x*sin(x))"),
    }
}
fn i3_indef_trig_ctrl() -> Outcome {
    let f = x() * x().sin();
    match integrate(&f, "x") {
        Some(result) => {
            let wrong = x() * x().cos() + x().sin();
            eq_check(
                &result.antiderivative,
                &wrong,
                false,
                &format!("F={}", result.antiderivative),
            )
        }
        None => declined("integrate(x*sin(x))"),
    }
}
/// `integrate(e^{-x^2}, x)` has no antiderivative in CLOSED ELEMENTARY form
/// (Liouville's theorem: the standard elementary functions cannot express
/// it) — but `erf` is exactly the special function defined to fill this gap
/// (`erf(x) = (2/sqrt(pi)) integral_0^x e^{-t^2} dt`), and this was FOUND
/// EMPIRICALLY: `axeyum-cas`'s `integrate` has a dedicated Gaussian-integral
/// route that returns `(sqrt(pi)/2) erf(x)` here, which is correct — its
/// derivative is exactly `e^{-x^2}` (checked below via the same
/// differentiate-and-`equal` route `CertifiedIntegral`'s own certificate
/// uses). This corrects an initial assumption (based on the module's plain
/// polynomial/`1/x`/`x^k e^{ax}` fast paths) that this would decline; the
/// real capability is broader. `is_certified()` on the returned
/// `CertifiedIntegral` should be true.
fn i4_gaussian_erf() -> Outcome {
    let f = (-x().pow(2)).exp();
    match integrate(&f, "x") {
        Some(result) => {
            let expected = r(1, 2) * CasExpr::var("pi").sqrt() * x().erf();
            eq_check(
                &result.antiderivative,
                &expected,
                true,
                &format!(
                    "F={} (is_certified={})",
                    result.antiderivative,
                    result.is_certified()
                ),
            )
        }
        None => declined("integrate(e^(-x^2), x)"),
    }
}

// ============================================================================
// Entries: limit
// ============================================================================

fn l1_removable() -> Outcome {
    let expr = (x().pow(2) - i(4)) / (x() - i(2));
    match limit(&expr, "x", LimitPoint::Finite(Rational::integer(2))) {
        Some(actual) => eq_check(&actual, &i(4), true, &format!("limit={actual}")),
        None => declined("limit((x^2-4)/(x-2), x->2)"),
    }
}
/// `limit`'s dispatcher (read in `crates/axeyum-cas/src/lib.rs`) handles: a
/// rational-function fragment, `abs` composed with a rational inner limit,
/// globally-continuous heads composed with a rational inner limit, additive
/// linearity, a sum-of-logarithms cancellation and a log-dominance rule at
/// `+-infinity`, algebraic (polynomial +- sqrt(polynomial)) limits at
/// `+infinity`, `exp`-of-a-finite-inner-limit (the `1^infinity` route), Bessel
/// composed with a rational inner limit, and exponential dominance at
/// `+-infinity`. None of those cover `sin(x)/x` — a `Div` whose numerator is a
/// bare transcendental head, not a rational-function ratio and not a
/// continuous-head composition — so this is expected to decline.
fn l2_sinc() -> Outcome {
    let expr = x().sin() / x();
    match limit(&expr, "x", LimitPoint::Finite(Rational::zero())) {
        None => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Unknown,
            expected: "1 (classical, but declining is the documented behavior)".to_string(),
            actual: "declined".to_string(),
        },
        Some(actual) => eq_check(&actual, &i(1), true, &format!("limit={actual}")),
    }
}
/// Same reasoning as `l2_sinc`: `(1 - cos x)/x^2` is a `Div` of transcendental
/// heads, outside every rule `limit` implements.
fn l3_cos_quad() -> Outcome {
    let expr = (i(1) - x().cos()) / x().pow(2);
    match limit(&expr, "x", LimitPoint::Finite(Rational::zero())) {
        None => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Unknown,
            expected: "1/2 (classical, but declining is the documented behavior)".to_string(),
            actual: "declined".to_string(),
        },
        Some(actual) => eq_check(&actual, &r(1, 2), true, &format!("limit={actual}")),
    }
}
/// `(1+1/x)^x` cannot be written with `CasExpr::Pow` (integer exponents only)
/// — it must be written as `exp(x ln(1+1/x))`, exactly the form the `exp`
/// dispatcher's own comment names as its example. `limit` composes `exp` with
/// a finite inner limit (`lim x ln(1+1/x) = 1` by the algebraic-at-infinity
/// route), giving `e`.
fn l4_e_definition() -> Outcome {
    let inner = x() * (i(1) + i(1) / x()).ln();
    let expr = inner.exp();
    match limit(&expr, "x", LimitPoint::PosInfinity) {
        Some(actual) => eq_check(&actual, &i(1).exp(), true, &format!("limit={actual}")),
        None => declined("limit((1+1/x)^x, x->+inf) [as exp(x ln(1+1/x))]"),
    }
}

// ============================================================================
// Entries: series
// ============================================================================

fn s1_exp() -> Outcome {
    match series(&x().exp(), "x", 4) {
        Some(actual) => {
            let expected =
                i(1) + x() + r(1, 2) * x().pow(2) + r(1, 6) * x().pow(3) + r(1, 24) * x().pow(4);
            eq_check(&actual, &expected, true, &format!("series={actual}"))
        }
        None => declined("series(exp(x), x, 4)"),
    }
}
fn s2_sin() -> Outcome {
    match series(&x().sin(), "x", 5) {
        Some(actual) => {
            let expected = x() - r(1, 6) * x().pow(3) + r(1, 120) * x().pow(5);
            eq_check(&actual, &expected, true, &format!("series={actual}"))
        }
        None => declined("series(sin(x), x, 5)"),
    }
}
fn s3_ln() -> Outcome {
    match series(&(i(1) + x()).ln(), "x", 4) {
        Some(actual) => {
            let expected = x() - r(1, 2) * x().pow(2) + r(1, 3) * x().pow(3) - r(1, 4) * x().pow(4);
            eq_check(&actual, &expected, true, &format!("series={actual}"))
        }
        None => declined("series(ln(1+x), x, 4)"),
    }
}
/// `sqrt(x)` is not analytic at `x=0` (a branch point: no Taylor series
/// exists there, classical fact of complex analysis), so a Taylor-series
/// producer that only ever returns a genuine power series must decline here.
fn s4_sqrt_branch() -> Outcome {
    match series(&x().sqrt(), "x", 4) {
        None => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Unknown,
            expected: "None (sqrt(x) is not analytic at 0)".to_string(),
            actual: "declined".to_string(),
        },
        Some(actual) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Uncertified,
            expected: "None (sqrt(x) is not analytic at 0)".to_string(),
            actual: format!("decided: {actual}"),
        },
    }
}

// ============================================================================
// Entries: sum
// ============================================================================

fn sum1_linear() -> Outcome {
    // sum_polynomial's own convention (its rustdoc): the summand `f` is
    // written using the SAME symbol as the desired upper-limit variable, i.e.
    // `sum_polynomial(f(n), "n")` computes `S(n) = sum_{k=0}^{n-1} f(k)` with
    // the result expressed in `n`. `f = n` (the identity) is `sum_{k=0}^{n-1}
    // k = n(n-1)/2`.
    let n = CasExpr::var("n");
    match sum_polynomial(&n, "n") {
        Some(actual) => {
            let expected = (n.clone().pow(2) - n) / i(2);
            eq_check(&actual, &expected, true, &format!("S(n)={actual}"))
        }
        None => declined("sum_polynomial(n, n)"),
    }
}
fn sum2_quadratic() -> Outcome {
    let n = CasExpr::var("n");
    match sum_polynomial(&n.clone().pow(2), "n") {
        Some(actual) => {
            let expected = (i(2) * n.clone().pow(3) - i(3) * n.clone().pow(2) + n) / i(6);
            eq_check(&actual, &expected, true, &format!("S(n)={actual}"))
        }
        None => declined("sum_polynomial(n^2, n)"),
    }
}
/// `gosper_sum(term, k)` returns the antidifference `S` with `S(k+1) - S(k) =
/// term`. For `term = 1/(k(k+1))`, `S(k) = -1/k` works: `S(k+1) - S(k) =
/// -1/(k+1) + 1/k = 1/(k(k+1))` (verified by clearing denominators:
/// `-k + (k+1) = 1`).
fn sum3_gosper() -> Outcome {
    let k = CasExpr::var("k");
    let term = i(1) / (k.clone() * (k.clone() + i(1)));
    match gosper_sum(&term, "k") {
        Some(actual) => {
            let expected = -(i(1) / k);
            eq_check(&actual, &expected, true, &format!("S(k)={actual}"))
        }
        None => declined("gosper_sum(1/(k(k+1)), k)"),
    }
}

// ============================================================================
// Entries: solve
// ============================================================================

/// Whether `roots` contains an entry `equal`-confirmed equal to `target`.
fn contains_root(roots: &[CasExpr], target: &CasExpr) -> bool {
    roots
        .iter()
        .any(|root| matches!(equal(root, target), ZeroTest::Certified { equal: true, .. }))
}

fn solve1_rational_roots() -> Outcome {
    let p = x().pow(2) - i(3) * x() + i(2);
    match solve(&p, "x") {
        Some(roots) => {
            let has1 = contains_root(&roots, &i(1));
            let has2 = contains_root(&roots, &i(2));
            let agree = has1 && has2 && roots.len() == 2;
            Outcome {
                verdict: if agree {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: Trust::Uncertified,
                expected: "{1, 2}".to_string(),
                actual: format!("{roots:?} (has 1: {has1}, has 2: {has2})"),
            }
        }
        None => declined("solve(x^2-3x+2, x)"),
    }
}
fn solve2_irrational_roots() -> Outcome {
    let p = x().pow(2) - i(2);
    match solve(&p, "x") {
        Some(roots) => {
            let sqrt2 = i(2).sqrt();
            let has_pos = contains_root(&roots, &sqrt2);
            let has_neg = contains_root(&roots, &(-sqrt2.clone()));
            let agree = has_pos && has_neg && roots.len() == 2;
            Outcome {
                verdict: if agree {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: Trust::Uncertified,
                expected: "{-sqrt(2), sqrt(2)}".to_string(),
                actual: format!("{roots:?} (has +sqrt2: {has_pos}, has -sqrt2: {has_neg})"),
            }
        }
        None => declined("solve(x^2-2, x)"),
    }
}
/// `x^5 - x - 1` is irreducible over Q with Galois group `S_5`, which is not
/// solvable — Abel-Ruffini says there is no radical formula for its roots.
/// `solve`'s own rustdoc documents that "complex roots and irreducible
/// cubics+" are OMITTED from its returned list (not claimed root-free) — so
/// this is expected to return `Some(vec![])` (an honestly incomplete, not a
/// wrong, list), not `None`. FOUND EMPIRICALLY: this is exactly what
/// happens, which corrects an initial assumption that `solve` would return
/// `None` outright; the real contract is "omit what I can't handle",
/// distinguishable from "claim no roots" only by reading the doc.
fn solve3_quintic() -> Outcome {
    let p = x().pow(5) - x() - i(1);
    match solve(&p, "x") {
        Some(roots) if roots.is_empty() => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Uncertified,
            expected: "Some([]) (irreducible S5-quintic factor omitted, per solve's own \
                       documented contract; Abel-Ruffini says no radical roots exist to find)"
                .to_string(),
            actual: "Some([]) (empty, as documented)".to_string(),
        },
        Some(roots) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Uncertified,
            expected: "Some([]) (irreducible S5-quintic factor omitted)".to_string(),
            actual: format!("decided: {roots:?}"),
        },
        None => Outcome {
            verdict: Verdict::Decline,
            trust: Trust::Unknown,
            expected: "Some([]) (irreducible S5-quintic factor omitted)".to_string(),
            actual: "declined (None) -- also honest, but not what solve's own doc predicts"
                .to_string(),
        },
    }
}

// ============================================================================
// Entries: factor
// ============================================================================

fn f1_quadratic() -> Outcome {
    match factor(&(x().pow(2) - i(3) * x() + i(2)), "x") {
        Some(factored) => {
            let expected = (x() - i(1)) * (x() - i(2));
            eq_check(&factored, &expected, true, &format!("factor={factored}"))
        }
        None => declined("factor(x^2-3x+2, x)"),
    }
}
fn f1_quadratic_ctrl() -> Outcome {
    match factor(&(x().pow(2) - i(3) * x() + i(2)), "x") {
        Some(factored) => {
            let wrong = (x() - i(1)) * (x() - i(3));
            eq_check(&factored, &wrong, false, &format!("factor={factored}"))
        }
        None => declined("factor(x^2-3x+2, x)"),
    }
}
fn f2_quartic() -> Outcome {
    match factor_expr(&(x().pow(4) - i(1)), "x") {
        Some(factored) => {
            let expected = (x() - i(1)) * (x() + i(1)) * (x().pow(2) + i(1));
            eq_check(
                &factored,
                &expected,
                true,
                &format!("factor_expr={factored}"),
            )
        }
        None => declined("factor_expr(x^4-1, x)"),
    }
}
fn f2_quartic_ctrl() -> Outcome {
    match factor_expr(&(x().pow(4) - i(1)), "x") {
        Some(factored) => {
            let wrong = (x() - i(1)) * (x() + i(1)) * (x().pow(2) - i(1));
            eq_check(&factored, &wrong, false, &format!("factor_expr={factored}"))
        }
        None => declined("factor_expr(x^4-1, x)"),
    }
}
/// `x*y^2 + x^2*y - x - y = (x+y)(xy-1)`, a genuinely two-variable
/// factorization. `factor`'s own dispatch (read in
/// `crates/axeyum-cas/src/lib.rs`) is univariate in the named variable plus
/// two special bivariate forms (a bivariate quadratic in one variable, and
/// sums/differences of like powers) — a general bivariate cubic like this
/// one is outside both, so `None` is expected (chair 04:
/// "factorization univariate plus two bivariate special forms").
fn f3_multivariate() -> Outcome {
    let y = CasExpr::var("y");
    let poly = x() * y.clone().pow(2) + x().pow(2) * y.clone() - x() - y;
    match factor(&poly, "x") {
        None => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Unknown,
            expected: "None ((x+y)(xy-1), outside factor's univariate+2-special-form fragment)"
                .to_string(),
            actual: "declined".to_string(),
        },
        Some(factored) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Uncertified,
            expected: "None ((x+y)(xy-1), outside factor's univariate+2-special-form fragment)"
                .to_string(),
            actual: format!("decided: {factored}"),
        },
    }
}

// ============================================================================
// Entries: simplify / equal
// ============================================================================

fn e1_radical() -> Outcome {
    let lhs = i(2).sqrt() * i(2).sqrt();
    eq_check(&lhs, &i(2), true, &format!("lhs={lhs}"))
}
/// `sqrt(2)*sqrt(3)` and `sqrt(6)` are mathematically equal (as real
/// numbers), but `equal`'s zero-test does not know that: it treats
/// `sqrt(2)`, `sqrt(3)`, and `sqrt(6)` as three unrelated atomic constants
/// with no multiplicative relation between them (there is no
/// `sqrt(a)*sqrt(b) = sqrt(a*b)` rewrite rule in the zero-test's atom
/// algebra — confirmed by printing the witness with `{:?}`: it is the
/// nonzero free-algebra polynomial `1*(sqrt:2)*(sqrt:3) - 1*(sqrt:6)`).
///
/// **THE FINDING**: this is not an honest decline. `equal` returns
/// `ZeroTest::Certified { equal: false, .. }` — a CONFIDENT, LABELED-CERTIFIED
/// claim that these two equal real numbers are different. The certificate is
/// internally consistent (the witness polynomial genuinely is nonzero *in the
/// free algebra over these three atoms*, and re-deriving it reproduces the
/// same witness), so it is not a forged or malformed certificate; but the
/// atom algebra it certifies over is coarser than real-number equality, and
/// nothing downstream is told that. This is exactly the shape CLAUDE.md's
/// evidence-and-checker-discipline warns about: a certificate whose scope is
/// narrower than the claim its label suggests. A caller reading only
/// `ZeroTest::Certified { equal: false }` has no way to see this gap.
///
/// **`tier: KnownDefect`, `tracked_by` "file 13, item 1 wave two, lane
/// cas-witness"**: the fix is owned elsewhere and in flight, so this entry
/// is excluded from the `agree`/`disagree`/`decline` tally that drives most
/// of this harness's exit status — but `main`'s loop still asserts the
/// disagreement PERSISTS (`outcome.verdict == Verdict::Disagree`), and exits
/// nonzero with a reclassify-to-`core` message the moment it does not.
fn e1_radical_cross_base() -> Outcome {
    let lhs = i(2).sqrt() * i(3).sqrt();
    let rhs = i(6).sqrt();
    match equal(&lhs, &rhs) {
        ZeroTest::Unknown => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Unknown,
            expected: "Unknown (sqrt(2)*sqrt(3) = sqrt(6) is true, but not in the atom algebra)"
                .to_string(),
            actual: "declined".to_string(),
        },
        ZeroTest::Certified { equal: decided, .. } => Outcome {
            verdict: if decided {
                Verdict::Agree
            } else {
                Verdict::Disagree
            },
            trust: Trust::Certified,
            expected: "true (sqrt(2)*sqrt(3) = sqrt(6) as real numbers)".to_string(),
            actual: format!(
                "Certified{{equal={decided}}} -- a confidently WRONG, certified false; \
                 see this function's doc comment"
            ),
        },
    }
}
fn e2_poly_identity() -> Outcome {
    let lhs = (x() + i(1)).pow(2);
    let rhs = x().pow(2) + i(2) * x() + i(1);
    eq_check(&lhs, &rhs, true, &format!("lhs={lhs}"))
}
fn e2_poly_identity_ctrl() -> Outcome {
    let lhs = (x() + i(1)).pow(2);
    let rhs = x().pow(2) + i(2) * x() + i(2);
    eq_check(&lhs, &rhs, false, &format!("lhs={lhs}"))
}
/// The Pythagorean identity is transcendentally true but is not a polynomial
/// identity over the atoms `sin(x)`, `cos(x)` unless the zero-test's atom
/// algebra specifically knows `sin^2 + cos^2 = 1`. Recorded as
/// `decline_expected`; if this actually certifies, that is a genuine, welcome
/// capability finding (see the harness's printed `actual` and the README).
fn e3_trig_pythagorean() -> Outcome {
    let lhs = x().sin().pow(2) + x().cos().pow(2);
    match equal(&lhs, &i(1)) {
        ZeroTest::Unknown => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Unknown,
            expected: "Unknown expected (true identity, but see justification)".to_string(),
            actual: "declined".to_string(),
        },
        ZeroTest::Certified { equal: decided, .. } => Outcome {
            verdict: if decided {
                Verdict::Agree
            } else {
                Verdict::Disagree
            },
            trust: Trust::Certified,
            expected: "true".to_string(),
            actual: format!("decided equal={decided}"),
        },
    }
}

// ============================================================================
// Entries: linear algebra
// ============================================================================

fn la1_det() -> Outcome {
    let Some(m) = Matrix::from_rows(vec![vec![i(2), i(0)], vec![i(0), i(3)]]) else {
        return declined("Matrix::from_rows([[2,0],[0,3]])");
    };
    match m.determinant() {
        Some(actual) => eq_check(&actual, &i(6), true, &format!("det={actual}")),
        None => declined("det([[2,0],[0,3]])"),
    }
}
fn la2_eigen() -> Outcome {
    let Some(m) = Matrix::from_rows(vec![vec![i(2), i(0)], vec![i(0), i(3)]]) else {
        return declined("Matrix::from_rows([[2,0],[0,3]])");
    };
    match eigenvectors(&m, "L") {
        Some(pairs) => {
            let has_2 = pairs.iter().any(|(lambda, _)| {
                matches!(
                    equal(lambda, &i(2)),
                    ZeroTest::Certified { equal: true, .. }
                )
            });
            let has_3 = pairs.iter().any(|(lambda, _)| {
                matches!(
                    equal(lambda, &i(3)),
                    ZeroTest::Certified { equal: true, .. }
                )
            });
            let agree = has_2 && has_3 && pairs.len() == 2;
            Outcome {
                verdict: if agree {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: Trust::Uncertified,
                expected: "eigenvalues {2, 3}".to_string(),
                actual: format!(
                    "{} eigenvalue(s) (has 2: {has_2}, has 3: {has_3})",
                    pairs.len()
                ),
            }
        }
        None => declined("eigenvectors([[2,0],[0,3]])"),
    }
}
/// `[[2,1],[0,2]]` is a single 2x2 Jordan block at eigenvalue 2: it is NOT
/// diagonalizable, so its minimal polynomial is `(L-2)^2`, not the
/// characteristic-polynomial-degree-1 guess `(L-2)`. Classical linear
/// algebra fact (a diagonalizable matrix's minimal polynomial has only
/// simple roots; this one, tested directly, does not: `(A-2I) != 0` but
/// `(A-2I)^2 = 0`).
fn la3_minpoly_jordan() -> Outcome {
    let Some(m) = Matrix::from_rows(vec![vec![i(2), i(1)], vec![i(0), i(2)]]) else {
        return declined("Matrix::from_rows([[2,1],[0,2]])");
    };
    match minimal_polynomial(&m, "L") {
        Some(actual) => {
            let l = CasExpr::var("L");
            let expected = (l - i(2)).pow(2);
            eq_check(&actual, &expected, true, &format!("minpoly={actual}"))
        }
        None => declined("minimal_polynomial([[2,1],[0,2]])"),
    }
}
fn la3_minpoly_jordan_ctrl() -> Outcome {
    let Some(m) = Matrix::from_rows(vec![vec![i(2), i(1)], vec![i(0), i(2)]]) else {
        return declined("Matrix::from_rows([[2,1],[0,2]])");
    };
    match minimal_polynomial(&m, "L") {
        Some(actual) => {
            let l = CasExpr::var("L");
            let wrong = l - i(2);
            eq_check(&actual, &wrong, false, &format!("minpoly={actual}"))
        }
        None => declined("minimal_polynomial([[2,1],[0,2]])"),
    }
}

// ============================================================================
// Entries: number theory
// ============================================================================

fn nt1_mersenne_prime() -> Outcome {
    bool_check(
        ntheory::is_prime(2_147_483_647),
        true,
        "is_prime(2^31-1)=true",
    )
}
fn nt1_mersenne_prime_ctrl() -> Outcome {
    // 2^31 - 3 = 2147483645 = 5 * 429496729 (composite; verified in
    // ground_truth.py by trial division, independent of this crate).
    bool_check(
        ntheory::is_prime(2_147_483_645),
        false,
        "is_prime(2^31-3)=false",
    )
}
fn nt2_factorize() -> Outcome {
    let mut actual = ntheory::factorize(360);
    actual.sort_unstable();
    let mut expected = vec![(2i128, 3u32), (3, 2), (5, 1)];
    expected.sort_unstable();
    Outcome {
        verdict: if actual == expected {
            Verdict::Agree
        } else {
            Verdict::Disagree
        },
        trust: Trust::Uncertified,
        expected: format!("{expected:?}"),
        actual: format!("{actual:?}"),
    }
}
fn nt3_legendre() -> Outcome {
    let actual = ntheory_advanced::legendre_symbol(3, 7);
    Outcome {
        verdict: if actual == -1 {
            Verdict::Agree
        } else {
            Verdict::Disagree
        },
        trust: Trust::Uncertified,
        expected: "-1".to_string(),
        actual: format!("{actual}"),
    }
}
/// The Pell equation `x^2 - 61 y^2 = 1`'s fundamental solution,
/// `(1766319049, 226153980)` — famously the smallest-discriminant Pell
/// equation whose fundamental solution is nonetheless enormous (cited in
/// Weil's "Number Theory: An Approach Through History", used as the classic
/// example that a naive search is infeasible).
fn nt4_pell() -> Outcome {
    match ntheory_advanced::pell_fundamental_solution(61) {
        Some((actual_x, actual_y)) => Outcome {
            verdict: if actual_x == 1_766_319_049 && actual_y == 226_153_980 {
                Verdict::Agree
            } else {
                Verdict::Disagree
            },
            trust: Trust::Uncertified,
            expected: "(1766319049, 226153980)".to_string(),
            actual: format!("({actual_x}, {actual_y})"),
        },
        None => declined("pell_fundamental_solution(61)"),
    }
}

// ============================================================================
// Entries: ODE
// ============================================================================

fn ode1_homog() -> Outcome {
    // y'' + y = 0, char_coeffs = [c0, c1, c2] for c0*y + c1*y' + c2*y'' = 0.
    match dsolve_homogeneous(
        &[Rational::integer(1), Rational::zero(), Rational::integer(1)],
        "x",
    ) {
        Some(sol) => {
            let second_deriv = sol.differentiate("x").differentiate("x");
            let residual = second_deriv + sol.clone();
            eq_check(
                &residual,
                &CasExpr::zero(),
                true,
                &format!("y={sol}; y''+y"),
            )
        }
        None => declined("dsolve_homogeneous([1,0,1], x) [y''+y=0]"),
    }
}
fn ode2_inhomog() -> Outcome {
    // y' + y = x, char_coeffs = [c0, c1] for c0*y + c1*y' = forcing.
    match dsolve_inhomogeneous(&[Rational::integer(1), Rational::integer(1)], &x(), "x") {
        Some(sol) => {
            let first_deriv = sol.differentiate("x");
            let residual = first_deriv + sol.clone() - x();
            eq_check(
                &residual,
                &CasExpr::zero(),
                true,
                &format!("y={sol}; y'+y-x"),
            )
        }
        None => declined("dsolve_inhomogeneous([1,1], x, x) [y'+y=x]"),
    }
}
/// `y' + y = tan(x)`: the non-polynomial first-order route uses the
/// certified integrating-factor method, which needs `integrate(e^x tan(x),
/// x)`. That integral has no elementary closed form (it is not a
/// polynomial/exponential/trig product `integrate` covers), so the whole
/// ODE solve is expected to decline.
fn ode3_tan_forcing() -> Outcome {
    let forcing = x().sin() / x().cos();
    match dsolve_inhomogeneous(&[Rational::integer(1), Rational::integer(1)], &forcing, "x") {
        None => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Unknown,
            expected: "None (integrate(e^x tan(x), x) is not elementary)".to_string(),
            actual: "declined".to_string(),
        },
        Some(sol) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Uncertified,
            expected: "None (integrate(e^x tan(x), x) is not elementary)".to_string(),
            actual: format!("decided: y={sol}"),
        },
    }
}

// ============================================================================
// Entries: transforms
// ============================================================================

fn tr1_laplace_t() -> Outcome {
    let t = CasExpr::var("t");
    match laplace_transform(&t, "t", "s") {
        Some(actual) => {
            let expected = i(1) / CasExpr::var("s").pow(2);
            eq_check(&actual, &expected, true, &format!("L{{t}}={actual}"))
        }
        None => declined("laplace_transform(t, t, s)"),
    }
}
fn tr2_z_geometric() -> Outcome {
    // signal = 2^n, written as exp(n*ln 2) per z_transform's own documented
    // convention for a^n.
    let n = CasExpr::var("n");
    let signal = (n * i(2).ln()).exp();
    match z_transform(&signal, "n", "z") {
        Some(actual) => {
            let z = CasExpr::var("z");
            let expected = z.clone() / (z - i(2));
            eq_check(&actual, &expected, true, &format!("Z{{2^n}}={actual}"))
        }
        None => declined("z_transform(2^n, n, z)"),
    }
}
/// `laplace_transform`'s own fragment (its rustdoc) is linear combinations of
/// `t^k e^{at}`, `t^k sin(bt)`, `t^k cos(bt)`, `t^k` Bessel `J`/`I`, and plain
/// polynomials. `tan(t)` (written as `sin(t)/cos(t)`, since there is no
/// `.tan()` constructor) is none of those — a ratio, not a product with a
/// polynomial factor — so `None` is expected. There is also no Fourier
/// transform in this crate at all (chair 03: "no Fourier transform"), which
/// is why this entry substitutes a documented-fragment boundary on the
/// transform that does exist rather than calling a function that does not.
fn tr3_laplace_decline() -> Outcome {
    let t = CasExpr::var("t");
    let tan_t = t.clone().sin() / t.cos();
    match laplace_transform(&tan_t, "t", "s") {
        None => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Unknown,
            expected:
                "None (tan(t) is outside laplace_transform's product-with-polynomial fragment)"
                    .to_string(),
            actual: "declined".to_string(),
        },
        Some(actual) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Uncertified,
            expected:
                "None (tan(t) is outside laplace_transform's product-with-polynomial fragment)"
                    .to_string(),
            actual: format!("decided: {actual}"),
        },
    }
}

// ============================================================================
// Entries: first-pass modules — fps
// ============================================================================

fn fps1_fibonacci() -> Outcome {
    let terms: Vec<BigRational> = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
        .iter()
        .map(|&n| BigRational::from_integer(BigInt::from(n)))
        .collect();
    match fps::guess_linear_recurrence(&terms) {
        Some(cert) => {
            let verified = cert.verify().is_ok();
            let order_ok = cert.order == 2;
            let coeffs_ok = cert.coefficients == vec![BigRational::one(), BigRational::one()];
            let agree = verified && order_ok && coeffs_ok;
            Outcome {
                verdict: if agree {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "order=2, coefficients=[1,1] (Fibonacci: a_n=a_{n-1}+a_{n-2})"
                    .to_string(),
                actual: format!(
                    "order={}, coefficients={:?}, verify_ok={verified}",
                    cert.order, cert.coefficients
                ),
            }
        }
        None => declined("guess_linear_recurrence(Fibonacci terms)"),
    }
}
/// The primes have no constant-coefficient linear recurrence of any bounded
/// order (classical: they are not eventually periodic nor polynomially
/// recursive) — `docs/math-department/13-computer-algebra.md`'s progress log
/// for `fps` records this directly: "recovers Fibonacci, Lucas, Padovan;
/// declines on the primes". Uses the same 13 terms as this crate's own
/// `fps.rs` regression test
/// (`berlekamp_massey_declines_on_the_primes_which_satisfy_no_short_recurrence`):
/// with only 10 terms an order-5 fit is a trivial, uninformative overfit
/// (Berlekamp-Massey can always fit `floor(len/2)` unknowns to `len` data
/// points), which this entry's first draft used and got a spurious
/// `Some(order=5)` — an artifact of too little data, not a genuine
/// recurrence, and fixed here to the crate's own better-chosen sample size.
fn fps2_primes_decline() -> Outcome {
    let terms: Vec<BigRational> = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
        .iter()
        .map(|&n| BigRational::from_integer(BigInt::from(n)))
        .collect();
    match fps::guess_linear_recurrence(&terms) {
        None => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Unknown,
            expected: "None (the primes have no linear recurrence)".to_string(),
            actual: "declined".to_string(),
        },
        Some(cert) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Uncertified,
            expected: "None (the primes have no linear recurrence)".to_string(),
            actual: format!("decided: order={}", cert.order),
        },
    }
}

// ============================================================================
// Entries: first-pass modules — enclosure
// ============================================================================

fn enc1_pi() -> Outcome {
    match enclose_constant("pi", 64) {
        Some(enc) => {
            let verified = enc.verify(&CasExpr::var("pi"), &[]).is_ok();
            let decimal = enc.interval.decimal(6);
            // OEIS A000796: pi = 3.14159265358979323846...
            let matches_digits = decimal.starts_with("[3.141592");
            let agree = verified && matches_digits;
            Outcome {
                verdict: if agree {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "[3.141592... (OEIS A000796), verify Ok".to_string(),
                actual: format!("{decimal}, verify_ok={verified}"),
            }
        }
        None => declined("enclose_constant(\"pi\", 64)"),
    }
}
/// `enclose_constant`'s own match recognizes only `"pi"`, `"e"`, `"ln2"`
/// (`"ln 2"`), and `"sqrt2"` (`"sqrt 2"`) — everything else, including the
/// Euler-Mascheroni constant, falls to its `_ => None` arm. Chair 02's
/// complaint ("gamma, Bessel, erf ... still decline", 2026-09-05 progress
/// log) is still current for gamma specifically.
fn enc2_gamma_decline() -> Outcome {
    match enclose_constant("gamma", 40) {
        None => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Unknown,
            expected: "None (only pi, e, ln2, sqrt2 are recognized names)".to_string(),
            actual: "declined".to_string(),
        },
        Some(_) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Uncertified,
            expected: "None (only pi, e, ln2, sqrt2 are recognized names)".to_string(),
            actual: "decided".to_string(),
        },
    }
}

// ============================================================================
// Entries: first-pass modules — qe
// ============================================================================

/// `Atom::new` takes `BigRational` coefficients (widened from `i128`-backed
/// `Rational` by the "wave two" fix to item 7's Cauchy-bound overflow, merged
/// after this corpus's first draft, `docs/math-department/13-computer-algebra.md`).
fn bigrat(n: i128) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn qe1_exists_sqrt2() -> Outcome {
    // exists x. x^2 - 2 = 0 -- true, witnessed by sqrt(2).
    let atom = Atom::new(vec![bigrat(-2), bigrat(0), bigrat(1)], Relation::Eq);
    let formula = ExistsFormula::new(vec![atom]);
    match qe::eliminate(&formula) {
        Some(true) => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Certified,
            expected: "true".to_string(),
            actual: "true (self-verified by eliminate)".to_string(),
        },
        Some(false) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Certified,
            expected: "true".to_string(),
            actual: "false (self-verified by eliminate)".to_string(),
        },
        None => declined("eliminate(exists x. x^2-2=0)"),
    }
}
fn qe2_forall_positive() -> Outcome {
    // forall x. x^2 + 1 > 0 -- true (no real root).
    let atom = Atom::new(vec![bigrat(1), bigrat(0), bigrat(1)], Relation::Gt);
    let formula = ForallFormula { atoms: vec![atom] };
    match qe::eliminate_forall(&formula) {
        Some(true) => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Certified,
            expected: "true".to_string(),
            actual: "true (self-verified by eliminate_forall)".to_string(),
        },
        Some(false) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Certified,
            expected: "true".to_string(),
            actual: "false (self-verified by eliminate_forall)".to_string(),
        },
        None => declined("eliminate_forall(forall x. x^2+1>0)"),
    }
}
/// `exists x. x^2 - 10^30 = 0` is true (witnessed by `10^15`). A first draft
/// of this entry, and the 2026-09-05 progress log for item 7's first slice,
/// recorded this exact example declining: "x² − 10³⁰ returns Unknown because
/// the reused root isolation is still i128". **This corpus's own local
/// `main` merge picked up item 7's "wave two" fix** (`Atom`'s coefficients
/// widened from `i128`-backed `Rational` to `BigRational`, per
/// `docs/math-department/13-computer-algebra.md`'s "wave two" log entries)
/// mid-development, which FIXED exactly this overflow — re-running this
/// corpus after that merge found `qe1`/`qe2` still passed unchanged (their
/// coefficients were always small) but this entry flipped from a documented
/// decline to a correct, certified decision. Reclassified `core`: this is a
/// genuine capability gain the corpus caught happening in real time, not a
/// corpus bug.
fn qe3_large_coefficient() -> Outcome {
    let ten_to_30: i128 = 1_000_000_000_000_000_000_000_000_000_000; // 10^30
    let atom = Atom::new(vec![bigrat(-ten_to_30), bigrat(0), bigrat(1)], Relation::Eq);
    let formula = ExistsFormula::new(vec![atom]);
    match qe::eliminate(&formula) {
        Some(true) => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Certified,
            expected: "true (witnessed by 10^15; also now decides, past the former i128 Cauchy-bound overflow)"
                .to_string(),
            actual: "true (self-verified by eliminate)".to_string(),
        },
        Some(false) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Certified,
            expected: "true".to_string(),
            actual: "false (self-verified by eliminate)".to_string(),
        },
        None => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Unknown,
            expected: "true (decides, per the wave-two BigRational fix)".to_string(),
            actual: "declined".to_string(),
        },
    }
}

// ============================================================================
// Entries: first-pass modules — numberfield
// ============================================================================

/// 41 is prime and `41 = 1 (mod 4)`; by Fermat's two-squares theorem it is a
/// sum of two squares: `41 = 4^2 + 5^2`.
fn nf1_two_squares_41() -> Outcome {
    match numberfield::two_squares(&BigInt::from(41)) {
        Some(cert) => {
            let verified = cert.verify().is_ok();
            let is_represented = matches!(cert, TwoSquaresCertificate::Represented { .. });
            Outcome {
                verdict: if verified && is_represented {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "Represented: 41 = 4^2 + 5^2 (Fermat's two-squares theorem)".to_string(),
                actual: format!("{cert:?}, verify_ok={verified}"),
            }
        }
        None => declined("two_squares(41)"),
    }
}
/// 43 is prime and `43 = 3 (mod 4)` to the first (odd) power, so by the same
/// theorem it is NOT a sum of two squares. Minimally different from
/// `nf1_two_squares_41` (the adjacent prime) to give the classification
/// entry its flip-side control.
fn nf2_two_squares_43_refuted() -> Outcome {
    match numberfield::two_squares(&BigInt::from(43)) {
        Some(cert) => {
            let verified = cert.verify().is_ok();
            let is_refuted = matches!(cert, TwoSquaresCertificate::Refuted { .. });
            Outcome {
                verdict: if verified && is_refuted {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "Refuted: 43 is prime, 43 mod 4 = 3 to an odd power".to_string(),
                actual: format!("{cert:?}, verify_ok={verified}"),
            }
        }
        None => declined("two_squares(43)"),
    }
}
/// The fundamental unit of `Z[sqrt(61)]` is `29718 + 3805*sqrt(61)` — per
/// this crate's own `numberfield` progress log (2026-09-05), which corrected
/// an initial brief's confusion of this with the (much larger) Pell
/// solution `1766319049 + 226153980*sqrt(61)`, the fundamental unit's
/// square.
fn nf3_fundamental_unit_61() -> Outcome {
    let field = match QuadraticField::new(&BigInt::from(61)) {
        Ok(field) => field,
        Err(err) => return declined(&format!("QuadraticField::new(61): {err:?}")),
    };
    match field.fundamental_unit() {
        Ok(cert) => {
            let verified = cert.verify().is_ok();
            let matches_expected =
                cert.a == BigInt::from(29718i64) && cert.b == BigInt::from(3805i64);
            Outcome {
                verdict: if verified && matches_expected {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "a=29718, b=3805".to_string(),
                actual: format!("a={}, b={}, verify_ok={verified}", cert.a, cert.b),
            }
        }
        Err(reason) => declined(&format!("fundamental_unit(61): {reason:?}")),
    }
}

// ============================================================================
// Entries: first-pass modules — permgroup
// ============================================================================

/// `S3`, generated by a 3-cycle and a transposition: classical order 6.
fn pg1_s3_order() -> Outcome {
    let Some(g1) = Permutation::from_cycles(&[vec![0, 1, 2]], 3) else {
        return declined("Permutation::from_cycles([[0,1,2]], 3)");
    };
    let Some(g2) = Permutation::from_cycles(&[vec![0, 1]], 3) else {
        return declined("Permutation::from_cycles([[0,1]], 3)");
    };
    match PermutationGroup::from_generators(vec![g1, g2], 3) {
        Some(group) => {
            let order = group.order();
            let verified = group.order_certificate().verify().is_ok();
            Outcome {
                verdict: if order == 6 {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "6 (|S3| = 3!)".to_string(),
                actual: format!("{order}, verify_ok={verified}"),
            }
        }
        None => declined("PermutationGroup::from_generators(S3 gens, 3)"),
    }
}
/// `C4`, generated by a single 4-cycle: classical order 4.
fn pg2_c4_order() -> Outcome {
    let Some(g1) = Permutation::from_cycles(&[vec![0, 1, 2, 3]], 4) else {
        return declined("Permutation::from_cycles([[0,1,2,3]], 4)");
    };
    match PermutationGroup::from_generators(vec![g1], 4) {
        Some(group) => {
            let order = group.order();
            let verified = group.order_certificate().verify().is_ok();
            Outcome {
                verdict: if order == 4 {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "4 (a single 4-cycle generates C4)".to_string(),
                actual: format!("{order}, verify_ok={verified}"),
            }
        }
        None => declined("PermutationGroup::from_generators(C4 gen, 4)"),
    }
}

// ============================================================================
// Entries: first-pass modules — homology
// ============================================================================

/// Three edges forming a triangle's *boundary*, with no filled 2-face: this
/// is (homotopy equivalent to) a circle S^1. Classical Betti numbers: b0=1
/// (connected), b1=1 (one independent loop).
fn hom1_circle_betti() -> Outcome {
    let Some(complex) =
        SimplicialComplex::from_maximal_simplices(&[vec![0, 1], vec![1, 2], vec![0, 2]])
    else {
        return declined("SimplicialComplex::from_maximal_simplices (hollow triangle)");
    };
    match homology::homology(&complex) {
        Some(cert) => {
            let verified = cert.verify(&complex).is_ok();
            let b0 = cert.betti.get(&0).copied().unwrap_or(usize::MAX);
            let b1 = cert.betti.get(&1).copied().unwrap_or(usize::MAX);
            let agree = verified && b0 == 1 && b1 == 1;
            Outcome {
                verdict: if agree {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "b0=1, b1=1 (circle S^1)".to_string(),
                actual: format!("betti={:?}, verify_ok={verified}", cert.betti),
            }
        }
        None => declined("homology(hollow triangle)"),
    }
}
/// A single filled 2-simplex (a solid triangle) is contractible: b0=1, b1=0.
fn hom2_disk_betti() -> Outcome {
    let Some(complex) = SimplicialComplex::from_maximal_simplices(&[vec![0, 1, 2]]) else {
        return declined("SimplicialComplex::from_maximal_simplices (filled triangle)");
    };
    match homology::homology(&complex) {
        Some(cert) => {
            let verified = cert.verify(&complex).is_ok();
            let b0 = cert.betti.get(&0).copied().unwrap_or(usize::MAX);
            let b1 = cert.betti.get(&1).copied().unwrap_or(usize::MAX);
            let agree = verified && b0 == 1 && b1 == 0;
            Outcome {
                verdict: if agree {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "b0=1, b1=0 (a filled 2-simplex is contractible)".to_string(),
                actual: format!("betti={:?}, verify_ok={verified}", cert.betti),
            }
        }
        None => declined("homology(filled triangle)"),
    }
}

// ============================================================================
// Entries: first-pass modules — probability
// ============================================================================

/// The sum of two independent Poisson variables is Poisson with the summed
/// rate — a classical convolution theorem. Per the module's own doc,
/// `convolve_poisson` certifies this for all `k` at once via
/// `prove_wz_sum`, a strictly stronger route than `Poisson`'s own
/// (uncertified) total mass.
fn prob1_poisson_convolution() -> Outcome {
    let x_d = Discrete::Poisson(i(2));
    let y_d = Discrete::Poisson(i(3));
    match probability::convolve_poisson(&x_d, &y_d) {
        Some(cert) => {
            let certified = cert.is_certified();
            Outcome {
                verdict: if certified {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if certified {
                    Trust::Certified
                } else {
                    Trust::Uncertified
                },
                expected: "certified (Poisson(2)+Poisson(3) ~ Poisson(5), classical convolution)"
                    .to_string(),
                actual: format!("certified={certified}, claim={}", cert.claim),
            }
        }
        None => declined("convolve_poisson(Poisson(2), Poisson(3))"),
    }
}
/// Per the module's own doc and progress log: `Poisson`'s own total mass
/// (`sum_k e^{-lam} lam^k/k! = 1`) is TRUE but declines — `lam^k/k!` is not
/// Gosper-summable, so `infinite_sum` cannot certify it, even though the
/// stronger WZ route certifies the Poisson+Poisson convolution identity
/// above. Expected: `Trust::Uncertified`, not `Trust::Certified`.
fn prob2_poisson_totalmass_decline() -> Outcome {
    let d = Discrete::Poisson(i(3));
    let cert = d.total_mass();
    let certified = cert.is_certified();
    Outcome {
        verdict: if certified {
            Verdict::Disagree
        } else {
            Verdict::Agree
        },
        trust: if certified {
            Trust::Certified
        } else {
            Trust::Uncertified
        },
        expected: "uncertified (true, but lam^k/k! is not Gosper-summable)".to_string(),
        actual: format!("certified={certified}, claim={}", cert.claim),
    }
}
/// `E[Binomial(n,p)] = n*p`: with `n` concrete, the finite support is
/// enumerable, so this is expected to certify even with symbolic `p`.
fn prob3_binomial_mean() -> Outcome {
    let d = Discrete::Binomial {
        n: 4,
        p: CasExpr::var("p"),
    };
    let cert = d.mean();
    let certified = cert.is_certified();
    let expected_claim = i(4) * CasExpr::var("p");
    let matches_expected = matches!(
        equal(&cert.claim, &expected_claim),
        ZeroTest::Certified { equal: true, .. }
    );
    Outcome {
        verdict: if certified && matches_expected {
            Verdict::Agree
        } else {
            Verdict::Disagree
        },
        trust: if certified {
            Trust::Certified
        } else {
            Trust::Uncertified
        },
        expected: "certified: E[Binomial(4,p)] = 4p".to_string(),
        actual: format!("certified={certified}, claim={}", cert.claim),
    }
}

// ============================================================================
// Entries: first-pass modules — geometry_beyond
// ============================================================================

/// Five points on the unit circle determine it uniquely as a conic; a sixth
/// unit-circle point not among the five should also lie on the recovered
/// conic (an independent re-check beyond the certificate's own
/// re-derivation, since 5 points determine a unique conic and a circle
/// through 5 of its own points IS that circle).
fn gb1_conic_unit_circle() -> Outcome {
    let points = [
        Point::new(Rational::integer(1), Rational::zero()),
        Point::new(Rational::zero(), Rational::integer(1)),
        Point::new(Rational::integer(-1), Rational::zero()),
        Point::new(Rational::zero(), Rational::integer(-1)),
        Point::new(Rational::new(3, 5), Rational::new(4, 5)),
    ];
    let sixth = Point::new(Rational::new(4, 5), Rational::new(-3, 5));
    match Conic::through_five_points(&points) {
        Ok((conic, cert)) => {
            let verified = cert.verify();
            let on_sixth = conic.on_conic(&sixth);
            let agree = verified && on_sixth;
            Outcome {
                verdict: if agree {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "verify Ok and a 6th unit-circle point also on the conic".to_string(),
                actual: format!("verify={verified}, on 6th point={on_sixth}"),
            }
        }
        Err(refusal) => declined(&format!("through_five_points (unit circle): {refusal:?}")),
    }
}
/// Minimally different from `gb1_conic_unit_circle`: one point moved off the
/// circle (`(3/5,9/5)` instead of `(3/5,4/5)`). The five points are still in
/// general position (a different, genuine conic exists), but that conic is
/// no longer the unit circle, so the held-out 6th unit-circle point should
/// NOT lie on it.
fn gb1_conic_unit_circle_ctrl() -> Outcome {
    let points = [
        Point::new(Rational::integer(1), Rational::zero()),
        Point::new(Rational::zero(), Rational::integer(1)),
        Point::new(Rational::integer(-1), Rational::zero()),
        Point::new(Rational::zero(), Rational::integer(-1)),
        Point::new(Rational::new(3, 5), Rational::new(9, 5)),
    ];
    let sixth = Point::new(Rational::new(4, 5), Rational::new(-3, 5));
    match Conic::through_five_points(&points) {
        Ok((conic, cert)) => {
            let verified = cert.verify();
            let on_sixth = conic.on_conic(&sixth);
            let agree = verified && !on_sixth;
            Outcome {
                verdict: if agree {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "verify Ok and the held-out unit-circle point NOT on this conic"
                    .to_string(),
                actual: format!("verify={verified}, on 6th point={on_sixth}"),
            }
        }
        Err(refusal) => declined(&format!("through_five_points (perturbed): {refusal:?}")),
    }
}
/// A 90-degree rotation about the origin is a valid isometry and, by
/// definition (orthogonality IS the distance-preservation condition),
/// always preserves distance.
fn gb2_isometry_rotation() -> Outcome {
    match Isometry::new(
        Rational::zero(),
        Rational::integer(-1),
        Rational::integer(1),
        Rational::zero(),
        Rational::zero(),
        Rational::zero(),
    ) {
        Ok(iso) => {
            let cert = geometry_beyond::certify_preserves_distance(&iso);
            let verified = cert.verify();
            Outcome {
                verdict: if verified {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Unknown
                },
                expected: "true (a rotation preserves distance)".to_string(),
                actual: format!("verify={verified}"),
            }
        }
        Err(refusal) => declined(&format!("Isometry::new(90-degree rotation): {refusal:?}")),
    }
}
/// A shear (`[[1,1],[0,1]]`) is not orthogonal (its second column has norm
/// `sqrt(2)`, not 1), so `Isometry::new` must reject it before any distance
/// certificate is even attempted.
fn gb2_isometry_shear_rejected() -> Outcome {
    match Isometry::new(
        Rational::integer(1),
        Rational::integer(1),
        Rational::zero(),
        Rational::integer(1),
        Rational::zero(),
        Rational::zero(),
    ) {
        Ok(_) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Uncertified,
            expected: "Err(NotOrthogonal) (a shear is not an isometry)".to_string(),
            actual: "accepted (wrongly)".to_string(),
        },
        Err(refusal) => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Uncertified,
            expected: "Err(NotOrthogonal)".to_string(),
            actual: format!("{refusal:?}"),
        },
    }
}

macro_rules! e {
    ($id:literal, $area:expr, $module:expr, $tier:expr, $f:expr) => {
        Entry {
            id: $id,
            area: $area,
            module: $module,
            tier: $tier,
            tracked_by: None,
            run: $f,
        }
    };
}

fn main() {
    use Tier::{Core, DeclineExpected, KnownDefect};
    let entries: Vec<Entry> = vec![
        // differentiate
        e!("d1-cubic", Some("differentiate"), None, Core, d1_cubic),
        e!(
            "d1-cubic-ctrl",
            Some("differentiate"),
            None,
            Core,
            d1_cubic_ctrl
        ),
        e!("d2-product", Some("differentiate"), None, Core, d2_product),
        e!(
            "d2-product-ctrl",
            Some("differentiate"),
            None,
            Core,
            d2_product_ctrl
        ),
        e!("d3-chain", Some("differentiate"), None, Core, d3_chain),
        e!(
            "d3-chain-ctrl",
            Some("differentiate"),
            None,
            Core,
            d3_chain_ctrl
        ),
        // integrate
        e!("i1-def-poly", Some("integrate"), None, Core, i1_def_poly),
        e!("i2-def-log", Some("integrate"), None, Core, i2_def_log),
        e!(
            "i3-indef-trig",
            Some("integrate"),
            None,
            Core,
            i3_indef_trig
        ),
        e!(
            "i3-indef-trig-ctrl",
            Some("integrate"),
            None,
            Core,
            i3_indef_trig_ctrl
        ),
        e!(
            "i4-gaussian-erf",
            Some("integrate"),
            None,
            Core,
            i4_gaussian_erf
        ),
        // limit
        e!("l1-removable", Some("limit"), None, Core, l1_removable),
        e!("l2-sinc", Some("limit"), None, DeclineExpected, l2_sinc),
        e!(
            "l3-cos-quad",
            Some("limit"),
            None,
            DeclineExpected,
            l3_cos_quad
        ),
        e!(
            "l4-e-definition",
            Some("limit"),
            None,
            Core,
            l4_e_definition
        ),
        // series
        e!("s1-exp", Some("series"), None, Core, s1_exp),
        e!("s2-sin", Some("series"), None, Core, s2_sin),
        e!("s3-ln", Some("series"), None, Core, s3_ln),
        e!(
            "s4-sqrt-branch",
            Some("series"),
            None,
            DeclineExpected,
            s4_sqrt_branch
        ),
        // sum
        e!("sum1-linear", Some("sum"), None, Core, sum1_linear),
        e!("sum2-quadratic", Some("sum"), None, Core, sum2_quadratic),
        e!("sum3-gosper", Some("sum"), None, Core, sum3_gosper),
        // solve
        e!(
            "solve1-rational-roots",
            Some("solve"),
            None,
            Core,
            solve1_rational_roots
        ),
        e!(
            "solve2-irrational-roots",
            Some("solve"),
            None,
            Core,
            solve2_irrational_roots
        ),
        e!(
            "solve3-quintic",
            Some("solve"),
            None,
            DeclineExpected,
            solve3_quintic
        ),
        // factor
        e!("f1-quadratic", Some("factor"), None, Core, f1_quadratic),
        e!(
            "f1-quadratic-ctrl",
            Some("factor"),
            None,
            Core,
            f1_quadratic_ctrl
        ),
        e!("f2-quartic", Some("factor"), None, Core, f2_quartic),
        e!(
            "f2-quartic-ctrl",
            Some("factor"),
            None,
            Core,
            f2_quartic_ctrl
        ),
        e!(
            "f3-multivariate",
            Some("factor"),
            None,
            DeclineExpected,
            f3_multivariate
        ),
        // simplify / equal
        e!("e1-radical", Some("simplify/equal"), None, Core, e1_radical),
        Entry {
            id: "e1-radical-cross-base",
            area: Some("simplify/equal"),
            module: None,
            tier: KnownDefect,
            tracked_by: Some("file 13, item 1 wave two, lane cas-witness"),
            run: e1_radical_cross_base,
        },
        e!(
            "e2-poly-identity",
            Some("simplify/equal"),
            None,
            Core,
            e2_poly_identity
        ),
        e!(
            "e2-poly-identity-ctrl",
            Some("simplify/equal"),
            None,
            Core,
            e2_poly_identity_ctrl
        ),
        e!(
            "e3-trig-pythagorean",
            Some("simplify/equal"),
            None,
            DeclineExpected,
            e3_trig_pythagorean
        ),
        // linear algebra
        e!("la1-det", Some("linear algebra"), None, Core, la1_det),
        e!("la2-eigen", Some("linear algebra"), None, Core, la2_eigen),
        e!(
            "la3-minpoly-jordan",
            Some("linear algebra"),
            None,
            Core,
            la3_minpoly_jordan
        ),
        e!(
            "la3-minpoly-jordan-ctrl",
            Some("linear algebra"),
            None,
            Core,
            la3_minpoly_jordan_ctrl
        ),
        // number theory
        e!(
            "nt1-mersenne-prime",
            Some("number theory"),
            None,
            Core,
            nt1_mersenne_prime
        ),
        e!(
            "nt1-mersenne-prime-ctrl",
            Some("number theory"),
            None,
            Core,
            nt1_mersenne_prime_ctrl
        ),
        e!(
            "nt2-factorize",
            Some("number theory"),
            None,
            Core,
            nt2_factorize
        ),
        e!(
            "nt3-legendre",
            Some("number theory"),
            None,
            Core,
            nt3_legendre
        ),
        e!("nt4-pell", Some("number theory"), None, Core, nt4_pell),
        // ODE
        e!("ode1-homog", Some("ODE"), None, Core, ode1_homog),
        e!("ode2-inhomog", Some("ODE"), None, Core, ode2_inhomog),
        e!(
            "ode3-tan-forcing",
            Some("ODE"),
            None,
            DeclineExpected,
            ode3_tan_forcing
        ),
        // transforms
        e!(
            "tr1-laplace-t",
            Some("transforms"),
            None,
            Core,
            tr1_laplace_t
        ),
        e!(
            "tr2-z-geometric",
            Some("transforms"),
            None,
            Core,
            tr2_z_geometric
        ),
        e!(
            "tr3-laplace-decline",
            Some("transforms"),
            None,
            DeclineExpected,
            tr3_laplace_decline
        ),
        // first-pass modules: fps
        e!(
            "fps1-fibonacci",
            Some("series"),
            Some("fps"),
            Core,
            fps1_fibonacci
        ),
        e!(
            "fps2-primes-decline",
            Some("series"),
            Some("fps"),
            DeclineExpected,
            fps2_primes_decline
        ),
        // first-pass modules: enclosure
        e!("enc1-pi", None, Some("enclosure"), Core, enc1_pi),
        e!(
            "enc2-gamma-decline",
            None,
            Some("enclosure"),
            DeclineExpected,
            enc2_gamma_decline
        ),
        // first-pass modules: qe
        e!("qe1-exists-sqrt2", None, Some("qe"), Core, qe1_exists_sqrt2),
        e!(
            "qe2-forall-positive",
            None,
            Some("qe"),
            Core,
            qe2_forall_positive
        ),
        e!(
            "qe3-large-coefficient",
            None,
            Some("qe"),
            Core,
            qe3_large_coefficient
        ),
        // first-pass modules: numberfield
        e!(
            "nf1-two-squares-41",
            Some("number theory"),
            Some("numberfield"),
            Core,
            nf1_two_squares_41
        ),
        e!(
            "nf2-two-squares-43-refuted",
            Some("number theory"),
            Some("numberfield"),
            Core,
            nf2_two_squares_43_refuted
        ),
        e!(
            "nf3-fundamental-unit-61",
            Some("number theory"),
            Some("numberfield"),
            Core,
            nf3_fundamental_unit_61
        ),
        // first-pass modules: permgroup
        e!("pg1-s3-order", None, Some("permgroup"), Core, pg1_s3_order),
        e!("pg2-c4-order", None, Some("permgroup"), Core, pg2_c4_order),
        // first-pass modules: homology
        e!(
            "hom1-circle-betti",
            None,
            Some("homology"),
            Core,
            hom1_circle_betti
        ),
        e!(
            "hom2-disk-betti",
            None,
            Some("homology"),
            Core,
            hom2_disk_betti
        ),
        // first-pass modules: probability
        e!(
            "prob1-poisson-convolution",
            None,
            Some("probability"),
            Core,
            prob1_poisson_convolution
        ),
        e!(
            "prob2-poisson-totalmass-decline",
            None,
            Some("probability"),
            DeclineExpected,
            prob2_poisson_totalmass_decline
        ),
        e!(
            "prob3-binomial-mean",
            None,
            Some("probability"),
            Core,
            prob3_binomial_mean
        ),
        // first-pass modules: geometry_beyond
        e!(
            "gb1-conic-unit-circle",
            None,
            Some("geometry_beyond"),
            Core,
            gb1_conic_unit_circle
        ),
        e!(
            "gb1-conic-unit-circle-ctrl",
            None,
            Some("geometry_beyond"),
            Core,
            gb1_conic_unit_circle_ctrl
        ),
        e!(
            "gb2-isometry-rotation",
            None,
            Some("geometry_beyond"),
            Core,
            gb2_isometry_rotation
        ),
        e!(
            "gb2-isometry-shear-rejected",
            None,
            Some("geometry_beyond"),
            Core,
            gb2_isometry_shear_rejected
        ),
    ];

    let total_start = Instant::now();
    let mut any_disagree = false;
    let mut agree = 0u32;
    let mut disagree = 0u32;
    let mut decline = 0u32;
    let mut known_defect = 0u32;
    let mut certified = 0u32;
    let mut uncertified = 0u32;
    let mut unknown = 0u32;
    let mut area_counts: std::collections::BTreeMap<&str, u32> = std::collections::BTreeMap::new();
    let mut module_counts: std::collections::BTreeMap<&str, u32> =
        std::collections::BTreeMap::new();
    let mut disagreements: Vec<(&str, String, String)> = Vec::new();
    let mut known_defect_alerts: Vec<String> = Vec::new();

    for entry in &entries {
        let start = Instant::now();
        let outcome = (entry.run)();
        let wall = start.elapsed();
        if matches!(entry.tier, Tier::KnownDefect) {
            // A known_defect entry is excluded from the agree/disagree/decline
            // tally: it is a TRACKED, owned finding, not this session's
            // failure to fix. But the disagreement must PERSIST -- if the
            // underlying bug is fixed, `equal` (or whatever this entry
            // checks) starts agreeing with the independently-established
            // truth, and that is exactly the signal that this entry must be
            // reclassified to `core` before anyone trusts it as still-open.
            known_defect += 1;
            if outcome.verdict == Verdict::Agree {
                any_disagree = true;
                let alert = format!(
                    "known defect {} now agrees: reclassify it to core",
                    entry.id
                );
                println!("FATAL: {alert}");
                known_defect_alerts.push(alert);
            }
        } else {
            match outcome.verdict {
                Verdict::Agree => agree += 1,
                Verdict::Disagree => {
                    disagree += 1;
                    any_disagree = true;
                    disagreements.push((
                        entry.id,
                        outcome.expected.clone(),
                        outcome.actual.clone(),
                    ));
                }
                Verdict::Decline => decline += 1,
            }
        }
        match outcome.trust {
            Trust::Certified => certified += 1,
            Trust::Uncertified => uncertified += 1,
            Trust::Unknown => unknown += 1,
        }
        if let Some(area) = entry.area {
            *area_counts.entry(area).or_insert(0) += 1;
        }
        if let Some(module) = entry.module {
            *module_counts.entry(module).or_insert(0) += 1;
        }
        println!(
            "{:<32} area={:<16} module={:<14} tier={:<16} verdict={:<8} trust={:<11} wall={:>10.3?} expected={} actual={}{}",
            entry.id,
            entry.area.unwrap_or("-"),
            entry.module.unwrap_or("-"),
            entry.tier.label(),
            outcome.verdict.label(),
            outcome.trust.label(),
            wall,
            outcome.expected,
            outcome.actual,
            entry
                .tracked_by
                .map(|t| format!(" tracked_by={t}"))
                .unwrap_or_default(),
        );
    }

    let total_wall = total_start.elapsed();
    println!("\n=== summary ===");
    println!("entries: {}", entries.len());
    println!(
        "verdict: agree={agree} disagree={disagree} decline={decline} known_defect={known_defect}"
    );
    println!("trust:   certified={certified} uncertified={uncertified} unknown={unknown}");
    println!("by area:");
    for (area, count) in &area_counts {
        println!("  {area:<16} {count}");
    }
    println!("by module:");
    for (module, count) in &module_counts {
        println!("  {module:<16} {count}");
    }
    println!("total wall time: {total_wall:.3?}");
    if !disagreements.is_empty() {
        println!("\n=== DISAGREEMENTS (findings) ===");
        for (id, expected, actual) in &disagreements {
            println!("  {id}: expected={expected} actual={actual}");
        }
    }
    if !known_defect_alerts.is_empty() {
        println!("\n=== KNOWN-DEFECT ALERTS (a tracked defect stopped reproducing) ===");
        for alert in &known_defect_alerts {
            println!("  {alert}");
        }
    }

    std::process::exit(i32::from(any_disagree));
}
