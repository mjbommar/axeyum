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

use std::collections::BTreeMap;
use std::time::Instant;

use axeyum_cas::enclosure::{BigInterval, EULER_GAMMA_NAME, enclose, enclose_constant};
use axeyum_cas::enclosure_special::{MultiPoly, PolySystem, enclose_system};
use axeyum_cas::fps_analytic::{
    RadiusOfConvergence, coefficient_asymptotics, radius_of_convergence,
};
use axeyum_cas::geometry::Point;
use axeyum_cas::geometry_beyond::{self, Conic, Isometry};
use axeyum_cas::homology::{
    self, SimplicialComplex, coefficients, cohomology, induced, persistent,
};
use axeyum_cas::numberfield::{self, QuadraticField, TwoSquaresCertificate};
use axeyum_cas::numberfield_ideals::{
    OrderElement, QuadraticOrder, SplittingType, class_number as ideal_class_number,
};
use axeyum_cas::permgroup::{NormalityCertificate, PermutationGroup};
use axeyum_cas::permutation::Permutation;
use axeyum_cas::probability::{self, Discrete};
use axeyum_cas::qe::bivariate::{BiAtom, ExistsYFormula, eliminate_y};
use axeyum_cas::qe::dnf::{Dnf, eliminate_dnf};
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
    #[expect(
        dead_code,
        reason = "the only tracked defect, `e1-radical-cross-base`, was fixed by lane \
                  cas-witness and reclassified to `Core`. The tier and its \
                  reclassify-when-it-stops-reproducing alert are kept for the next one; \
                  the summary line prints `known_defect=0` so an empty tier is visible \
                  rather than implied. Delete this attribute when an entry uses it again."
    )]
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
        ZeroTest::Certified { equal: decided, .. }
        | ZeroTest::CertifiedBig { equal: decided, .. } => Outcome {
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
/// `sqrt(2)*sqrt(3)` vs `sqrt(6)` — **fixed**, was the harness's one tracked
/// wrong-refuted.
///
/// The zero-test atomized each radical spelling into its own independent
/// variable, so `sqrt(2)*sqrt(3) - sqrt(6)` was a nonzero polynomial in three
/// unrelated atoms and came back `Certified { equal: false }` — a certificate
/// whose scope was narrower than the claim its label made, and the exact shape
/// CLAUDE.md's evidence-and-checker-discipline warns about.
///
/// Lane `cas-witness` repaired the class (ADR-1670 wave two): constant radicals
/// are canonicalized by their squarefree part at intake, the radicals inside one
/// monomial are multiplied together and re-extracted, and a refutation whose
/// difference still multiplies two radical atoms is declined rather than
/// asserted. Seven sibling identities were wrong-refuted on the same build and
/// are covered by the `radical_atom_products` tests in `axeyum-cas`.
///
/// Now `tier: Core`: it must certify TRUE, and a regression is an ordinary
/// disagreement rather than a tracked one.
fn e1_radical_cross_base() -> Outcome {
    let lhs = i(2).sqrt() * i(3).sqrt();
    let rhs = i(6).sqrt();
    eq_check(&lhs, &rhs, true, &format!("lhs={lhs}"))
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
        ZeroTest::Certified { equal: decided, .. }
        | ZeroTest::CertifiedBig { equal: decided, .. } => Outcome {
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
/// Euler's constant. Reclassified from `decline_expected` on 2026-09-06: the
/// enclosure lane's third wave (item 2) added `euler_gamma` with `"gamma"` as
/// an alias, so `enclose_constant("gamma", 40)` now decides. The corpus follows
/// the machinery: the entry asserts the enclosure verifies and contains the
/// thirty cited digits of gamma (OEIS A001620).
fn enc2_gamma_euler() -> Outcome {
    let expected = "certified enclosure containing 0.577215664901532860606512090082".to_string();
    match enclose_constant("gamma", 40) {
        None => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Unknown,
            expected,
            actual: "declined".to_string(),
        },
        Some(enc) => {
            // Thirty cited digits as an exact rational; the enclosure's width
            // is about 2^-40, so a sound enclosure of gamma contains this point.
            let digits: BigInt = "577215664901532860606512090082".parse().expect("digits");
            let scale: BigInt = "1000000000000000000000000000000".parse().expect("scale");
            let gamma = BigRational::new(digits, scale);
            let contains = enc.interval.contains(&gamma);
            let verified = enc.verify(&CasExpr::var(EULER_GAMMA_NAME), &[]).is_ok();
            Outcome {
                verdict: if contains && verified {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: if verified {
                    Trust::Certified
                } else {
                    Trust::Uncertified
                },
                expected,
                actual: format!("contains_digits={contains}, verified={verified}"),
            }
        }
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
fn prob2_poisson_totalmass() -> Outcome {
    // Reclassified from `decline_expected` on 2026-09-05: the summation lane
    // (cas-sum-gaps) taught `infinite_sum` the exponential series, so
    // `sum_{k>=0} 3^k/k! e^{-3} = 1` now certifies. The corpus is judged by
    // the harness, not the other way round, so the entry follows the machinery.
    let d = Discrete::Poisson(i(3));
    let cert = d.total_mass();
    let certified = cert.is_certified();
    let matches_expected = matches!(
        equal(&cert.claim, &i(1)),
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
        expected: "certified total mass 1 (exponential series route)".to_string(),
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

/// `M(t) = λ/(λ−t)` for `Exponential(λ)` at a symbolic `λ` **and** a symbolic
/// `t`, decided under `λ − t > 0` (i.e. `t < λ`, the interval on which the mgf
/// exists at all). Added 2026-09-05 by lane cas-symbolic-mgf.
///
/// The entry agrees only when the condition is recorded **exactly**: if the
/// hypothesis ever silently disappears, the claim `λ/(λ−t)` becomes an
/// unconditional falsehood and this entry disagrees, reddening the harness.
fn prob4_exponential_symbolic_mgf() -> Outcome {
    let lambda = CasExpr::var("lam");
    let d = probability::Continuous::Exponential(lambda.clone());
    let cert = d.mgf("t");
    let conditions = cert.hypotheses_display();
    let matches_claim = matches!(
        equal(
            &cert.claim,
            &(lambda.clone() / (lambda - CasExpr::var("t")))
        ),
        ZeroTest::Certified { equal: true, .. }
    );
    let good = cert.is_decided() && conditions == "lam - t > 0" && matches_claim;
    Outcome {
        verdict: if good {
            Verdict::Agree
        } else {
            Verdict::Disagree
        },
        trust: if cert.is_decided() {
            Trust::Certified
        } else {
            Trust::Uncertified
        },
        expected: "decided lam/(lam - t) under exactly `lam - t > 0`".to_string(),
        actual: format!(
            "decided={}, unconditional={}, claim={}, under=[{conditions}]",
            cert.is_decided(),
            cert.is_certified(),
            cert.claim
        ),
    }
}

/// `M(t) = e^{μt + σ²t²/2}` for `Normal(μ, 4)` at a symbolic `μ` and symbolic
/// `t`, certified **unconditionally** — `σ²` is concrete, so its sign is decided
/// rather than recorded. Reached by completing the square, not by integrating
/// `e^{tx}φ(x)` (which declines). Added 2026-09-05 by lane cas-symbolic-mgf.
fn prob5_normal_symbolic_mgf() -> Outcome {
    let mu = CasExpr::var("mu");
    let t = CasExpr::var("t");
    let d = probability::Continuous::Normal {
        mu: mu.clone(),
        variance: CasExpr::Const(Rational::integer(4)),
    };
    let cert = d.mgf("t");
    let expected_claim = (t.clone() * mu + i(4) * t.pow(2) / i(2)).exp();
    let matches_claim = matches!(
        equal(&cert.claim, &expected_claim),
        ZeroTest::Certified { equal: true, .. }
    );
    let good = cert.is_certified() && cert.hypotheses().is_empty() && matches_claim;
    Outcome {
        verdict: if good {
            Verdict::Agree
        } else {
            Verdict::Disagree
        },
        trust: if cert.is_certified() {
            Trust::Certified
        } else {
            Trust::Uncertified
        },
        expected: "certified exp(mu*t + 4*t^2/2), unconditionally".to_string(),
        actual: format!(
            "certified={}, claim={}, under=[{}]",
            cert.is_certified(),
            cert.claim,
            cert.hypotheses_display()
        ),
    }
}

/// `Normal` with a **negative** variance must decline its mgf: the square
/// completes, but the shifted Gaussian points the wrong way and has no erf
/// antiderivative. The control that the completing-the-square reduction did not
/// become a formula-printer. Added 2026-09-05 by lane cas-symbolic-mgf.
fn prob6_normal_negative_variance_declines() -> Outcome {
    let d = probability::Continuous::Normal {
        mu: CasExpr::var("mu"),
        variance: CasExpr::Const(Rational::integer(-1)),
    };
    let cert = d.mgf("t");
    Outcome {
        verdict: if cert.is_decided() {
            Verdict::Disagree
        } else {
            Verdict::Decline
        },
        trust: Trust::Uncertified,
        expected: "declines: a negative variance is not a Gaussian this route integrates"
            .to_string(),
        actual: format!("decided={}, claim={}", cert.is_decided(), cert.claim),
    }
}

/// `E[Geometric(p)] = 1/p` at a **symbolic** `p`, decided under exactly
/// `0 < p < 1`. Was `decline_expected` until 2026-09-06: `gosper_sum` still has
/// no antidifference for a symbolic ratio, but `infinite_sum_conditional`'s
/// geometric series reaches the same summand with `|1−p| < 1` recorded.
/// Reclassified by lane `cas-sum-gaps-2` after the harness flagged the
/// disagreement — the direction the corpus is meant to move.
///
/// The entry DISAGREES if the conditions ever silently disappear: `1/p` is not
/// the mean of anything at `p ≤ 0` or `p ≥ 1`, where the series does not
/// converge to it.
fn prob7_geometric_symbolic_p_mean() -> Outcome {
    let p = CasExpr::var("p");
    let d = Discrete::Geometric(p.clone());
    let cert = d.mean();
    let conditions = cert.hypotheses_display();
    let matches_claim = matches!(
        equal(&cert.claim, &(CasExpr::one() / p)),
        ZeroTest::Certified { equal: true, .. }
    );
    let good = cert.is_decided() && conditions == "p > 0 and 1 - p > 0" && matches_claim;
    Outcome {
        verdict: if good {
            Verdict::Agree
        } else {
            Verdict::Disagree
        },
        trust: if cert.is_decided() {
            Trust::Certified
        } else {
            Trust::Uncertified
        },
        expected: "decided 1/p under exactly `p > 0 and 1 - p > 0`".to_string(),
        actual: format!(
            "decided={}, unconditional={}, claim={}, under=[{conditions}]",
            cert.is_decided(),
            cert.is_certified(),
            cert.claim
        ),
    }
}

/// `Geometric(p)`'s mgf at a symbolic `p` **and** symbolic `t`, decided under
/// `0 < p < 1` together with `t < −ln(1−p)`. The third condition is the one the
/// mgf genuinely needs and the moments do not: `(1−p)eᵗ` leaves the unit disc as
/// `t` grows, and `pe^t/(1−(1−p)e^t)` is negative there rather than an mgf.
fn prob8_geometric_symbolic_mgf() -> Outcome {
    let p = CasExpr::var("p");
    let d = Discrete::Geometric(p.clone());
    let cert = d.mgf("t");
    let conditions = cert.hypotheses_display();
    let e = CasExpr::var("t").exp();
    let expected_claim = (p.clone() * e.clone()) / (CasExpr::one() - (CasExpr::one() - p) * e);
    let matches_claim = matches!(
        equal(&cert.claim, &expected_claim),
        ZeroTest::Certified { equal: true, .. }
    );
    let good = cert.is_decided()
        && conditions == "p > 0 and 1 - p > 0 and -ln(1 - p) - t > 0"
        && matches_claim;
    Outcome {
        verdict: if good {
            Verdict::Agree
        } else {
            Verdict::Disagree
        },
        trust: if cert.is_decided() {
            Trust::Certified
        } else {
            Trust::Uncertified
        },
        expected: "decided p*e^t/(1-(1-p)*e^t) under exactly `0 < p < 1` and `t < -ln(1-p)`"
            .to_string(),
        actual: format!(
            "decided={}, unconditional={}, claim={}, under=[{conditions}]",
            cert.is_decided(),
            cert.is_certified(),
            cert.claim
        ),
    }
}

/// `Normal(μ, σ²)` at a **symbolic** variance: mass `1`, mean `μ`, variance `σ²`
/// and mgf `e^{μt+σ²t²/2}`, each decided under exactly `σ² > 0`. Added
/// 2026-09-06 by lane `cas-sum-gaps-2`; before it, a symbolic variance was not
/// even representable (the field was a concrete rational).
///
/// All four are checked in one entry because the failure mode being guarded is
/// shared: if the `σ² > 0` condition ever disappears, every one of them becomes
/// a claim about an "upward Gaussian" that has no finite integral at all.
fn prob9_normal_symbolic_variance() -> Outcome {
    let mu = CasExpr::var("mu");
    let s = CasExpr::var("s");
    let t = CasExpr::var("t");
    let d = probability::Continuous::Normal {
        mu: mu.clone(),
        variance: s.clone(),
    };
    let mgf_target = (t.clone() * mu.clone() + s.clone() * t.pow(2) / i(2)).exp();
    let quantities = [
        (d.total_mass(), CasExpr::one()),
        (d.mean(), mu),
        (d.variance(), s),
        (d.mgf("t"), mgf_target),
    ];
    let mut good = true;
    let mut report = Vec::new();
    for (cert, expected_claim) in &quantities {
        let conditions = cert.hypotheses_display();
        let matches_claim = matches!(
            equal(&cert.claim, expected_claim),
            ZeroTest::Certified { equal: true, .. }
        );
        good &= cert.is_decided() && conditions == "s > 0" && matches_claim;
        report.push(format!(
            "{}|decided={}|under=[{conditions}]",
            cert.claim,
            cert.is_decided()
        ));
    }
    Outcome {
        verdict: if good {
            Verdict::Agree
        } else {
            Verdict::Disagree
        },
        trust: if good {
            Trust::Certified
        } else {
            Trust::Uncertified
        },
        expected:
            "mass 1, mean mu, variance s, mgf exp(mu*t + s*t^2/2), each under exactly `s > 0`"
                .to_string(),
        actual: report.join(" ; "),
    }
}

/// **Control** for `prob7`/`prob8`: a `Geometric` whose ratio leaves the unit
/// disc must decline, not print the analytic continuation. `Geometric(2)` has
/// `q = 1 − 2 = −1`, so `Σ qʲ` oscillates and has no value; the closed form
/// `1/(1−q) = 1/2` is spellable and wrong.
fn prob10_geometric_divergent_ratio_declines() -> Outcome {
    let d = Discrete::Geometric(i(2));
    let cert = d.mean();
    Outcome {
        verdict: if cert.is_decided() {
            Verdict::Disagree
        } else {
            Verdict::Decline
        },
        trust: Trust::Uncertified,
        expected: "declines: |1-p| = 1, so the geometric series does not converge".to_string(),
        actual: format!("decided={}, claim={}", cert.is_decided(), cert.claim),
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

// ============================================================================
// Entries: second-pass modules — enclosure_special
// ============================================================================

/// Gamma(6) = 5! = 120, exactly (no remainder -- `Gamma` at a positive
/// integer argument is the module's one exact case).
fn es1_gamma_integer() -> Outcome {
    match enclose(&i(6).gamma(), &[], 64) {
        Some(enc) => {
            let verified = enc.verify(&i(6).gamma(), &[]).is_ok();
            let contains = enc
                .interval
                .contains(&BigRational::from_integer(BigInt::from(120)));
            let agree = verified && contains;
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
                expected: "120 (Gamma(6) = 5! = 120, exact)".to_string(),
                actual: format!("{}, verify_ok={verified}", enc.interval.decimal(6)),
            }
        }
        None => declined("enclose(Gamma(6), [], 64)"),
    }
}

/// `erf(1) = 0.84270079294971486934...` -- confirmed independently by
/// `SymPy`'s `N(erf(1), 20)` in `ground_truth.py`.
fn es2_erf_one() -> Outcome {
    match enclose(&i(1).erf(), &[], 64) {
        Some(enc) => {
            let verified = enc.verify(&i(1).erf(), &[]).is_ok();
            let decimal = enc.interval.decimal(8);
            let matches_digits = decimal.starts_with("[0.84270079");
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
                expected: "[0.84270079... (erf(1), independently confirmed by SymPy)".to_string(),
                actual: format!("{decimal}, verify_ok={verified}"),
            }
        }
        None => declined("enclose(erf(1), [], 64)"),
    }
}
/// Near-miss control on the SAME enclosure: `erf(1)` is nowhere near `0.9`
/// -- the certificate's own interval must exclude it, not just report a
/// leading-digit match that could be a coincidence.
fn es2_erf_one_ctrl() -> Outcome {
    match enclose(&i(1).erf(), &[], 64) {
        Some(enc) => {
            let excludes_wrong = !enc
                .interval
                .contains(&BigRational::new(BigInt::from(9), BigInt::from(10)));
            Outcome {
                verdict: if excludes_wrong {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: Trust::Certified,
                expected: "the erf(1) enclosure does NOT contain 0.9".to_string(),
                actual: format!("excludes_0.9={excludes_wrong}"),
            }
        }
        None => declined("enclose(erf(1), [], 64)"),
    }
}

/// `J_0(0) = 1` exactly: the Bessel series at `x = 0` has only its `k = 0`
/// term survive.
fn es3_besselj0_zero() -> Outcome {
    match enclose(&i(0).bessel_j(0), &[], 64) {
        Some(enc) => {
            let verified = enc.verify(&i(0).bessel_j(0), &[]).is_ok();
            let contains = enc.interval.contains(&BigRational::one());
            let agree = verified && contains;
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
                expected: "1 (J_0(0) = 1, exact)".to_string(),
                actual: format!("{}, verify_ok={verified}", enc.interval.decimal(6)),
            }
        }
        None => declined("enclose(BesselJ_0(0), [], 64)"),
    }
}

/// The multivariate Krawczyk root enclosure: the unit circle `x^2+y^2-1=0`
/// meets the diagonal `y-x=0` at `(1/sqrt(2), 1/sqrt(2))` -- the exact
/// system and starting box this crate's own `enclosure_special` test suite
/// uses (`circle_and_line`/`near_the_root`), independently justified by
/// elementary substitution: `x=y` turns the circle into `2x^2=1`.
fn es4_krawczyk_circle_line() -> Outcome {
    let circle = (|| {
        MultiPoly::zero(2)
            .with_term(Rational::integer(1), &[2, 0])?
            .with_term(Rational::integer(1), &[0, 2])?
            .with_term(Rational::integer(-1), &[0, 0])
    })();
    let line = (|| {
        MultiPoly::zero(2)
            .with_term(Rational::integer(1), &[0, 1])?
            .with_term(Rational::integer(-1), &[1, 0])
    })();
    let (Some(circle), Some(line)) = (circle, line) else {
        return declined("MultiPoly::with_term (circle/line)");
    };
    let Some(system) = PolySystem::new(vec![circle, line]) else {
        return declined("PolySystem::new(circle, line)");
    };
    let q = |n: i128, d: i128| BigRational::new(BigInt::from(n), BigInt::from(d));
    let start = (|| {
        Some(vec![
            BigInterval::new(q(7, 10), q(18, 25))?,
            BigInterval::new(q(7, 10), q(18, 25))?,
        ])
    })();
    let Some(start) = start else {
        return declined("BigInterval::new (start box)");
    };
    match enclose_system(&system, &start, 60) {
        Some(enc) => {
            let verified = enc.verify(&system, &start).is_ok();
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
                expected: "a certified enclosure of (1/sqrt(2), 1/sqrt(2)), verify Ok".to_string(),
                actual: format!("verify_ok={verified}"),
            }
        }
        None => declined("enclose_system(circle & line, start, 60)"),
    }
}

// ============================================================================
// Entries: second-pass modules — fps_analytic
// ============================================================================

/// `1/(1-2x)`'s radius of convergence is exactly `1/2` (geometric series,
/// classical).
fn fa1_radius_exact_geometric() -> Outcome {
    let numerator = vec![bigrat(1)];
    let denominator = vec![bigrat(1), bigrat(-2)];
    match radius_of_convergence(&numerator, &denominator) {
        Ok(cert) => {
            let verified = cert.verify().is_ok();
            let half = BigRational::new(BigInt::from(1), BigInt::from(2));
            let exact_half = matches!(&cert.radius, RadiusOfConvergence::Exact(r) if *r == half);
            let agree = verified && exact_half;
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
                expected: "Exact(1/2) (1/(1-2x), geometric series)".to_string(),
                actual: format!("{:?}, verify_ok={verified}", cert.radius),
            }
        }
        Err(reason) => declined(&format!("radius_of_convergence(1/(1-2x)): {reason:?}")),
    }
}
/// Near-miss control: `1/(1-3x)` has a DIFFERENT exact radius, `1/3` -- the
/// tool must not report the same answer regardless of the denominator.
fn fa1_radius_exact_geometric_ctrl() -> Outcome {
    let numerator = vec![bigrat(1)];
    let denominator = vec![bigrat(1), bigrat(-3)];
    match radius_of_convergence(&numerator, &denominator) {
        Ok(cert) => {
            let verified = cert.verify().is_ok();
            let third = BigRational::new(BigInt::from(1), BigInt::from(3));
            let half = BigRational::new(BigInt::from(1), BigInt::from(2));
            let exact_third = matches!(&cert.radius, RadiusOfConvergence::Exact(r) if *r == third);
            let not_half = !matches!(&cert.radius, RadiusOfConvergence::Exact(r) if *r == half);
            let agree = verified && exact_third && not_half;
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
                expected: "Exact(1/3), and NOT 1/2 (1/(1-3x), distinguishing the two denominators)"
                    .to_string(),
                actual: format!("{:?}, verify_ok={verified}", cert.radius),
            }
        }
        Err(reason) => declined(&format!("radius_of_convergence(1/(1-3x)): {reason:?}")),
    }
}

/// The Fibonacci generating function `x/(1-x-x^2)` has radius `1/phi =
/// (sqrt(5)-1)/2 ~= 0.6180339887498948` -- the smaller-modulus root of
/// `1-x-x^2` (confirmed independently by `SymPy` in `ground_truth.py`). The
/// bracket check uses a loose +/-0.01 margin since the module refines to 96
/// bits, far tighter than any literal digit string is worth pinning.
fn fa2_radius_algebraic_fibonacci() -> Outcome {
    let numerator = vec![bigrat(0), bigrat(1)];
    let denominator = vec![bigrat(1), bigrat(-1), bigrat(-1)];
    match radius_of_convergence(&numerator, &denominator) {
        Ok(cert) => {
            let verified = cert.verify().is_ok();
            let is_algebraic = matches!(&cert.radius, RadiusOfConvergence::Algebraic(_));
            let lower_margin = BigRational::new(BigInt::from(608), BigInt::from(1000));
            let upper_margin = BigRational::new(BigInt::from(628), BigInt::from(1000));
            let bracket_ok = cert
                .radius
                .bracket()
                .is_some_and(|(lo, hi)| lower_margin <= lo && hi <= upper_margin);
            let agree = verified && is_algebraic && bracket_ok;
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
                expected: "an algebraic radius bracketed within [0.608, 0.628] (1/phi ~= 0.618)"
                    .to_string(),
                actual: format!("{:?}, verify_ok={verified}", cert.radius),
            }
        }
        Err(reason) => declined(&format!("radius_of_convergence(x/(1-x-x^2)): {reason:?}")),
    }
}

/// `1/(1-2x)`'s coefficients are exactly `2^n`; sampled at `n=4,8,16` this is
/// `16, 256, 65536`.
fn fa3_coefficient_asymptotics_geometric() -> Outcome {
    let numerator = vec![bigrat(1)];
    let denominator = vec![bigrat(1), bigrat(-2)];
    match coefficient_asymptotics(&numerator, &denominator, 4) {
        Ok(cert) => {
            let verified = cert.verify().is_ok();
            let expected_coeffs = vec![bigrat(16), bigrat(256), bigrat(65536)];
            let matches_expected = cert.coefficients == expected_coeffs;
            let agree = verified && matches_expected;
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
                expected: "coefficients [16, 256, 65536] at n=[4,8,16] (2^n)".to_string(),
                actual: format!("{:?}, verify_ok={verified}", cert.coefficients),
            }
        }
        Err(reason) => declined(&format!(
            "coefficient_asymptotics(1/(1-2x), base=4): {reason:?}"
        )),
    }
}

// ============================================================================
// Entries: second-pass modules — numberfield_ideals
// ============================================================================

/// `N((2+sqrt(-5))) = 2^2 + 5*1^2 = 9` in `Z[sqrt(-5)]` (`d=-5`): the norm
/// of a principal ideal is the absolute value of the element norm, a
/// classical fact about principal ideals.
fn nfi1_ideal_norm_principal() -> Outcome {
    let order = match QuadraticOrder::new(&BigInt::from(-5)) {
        Ok(order) => order,
        Err(err) => return declined(&format!("QuadraticOrder::new(-5): {err:?}")),
    };
    let element = OrderElement::from_i64(2, 1); // 2 + 1*sqrt(-5)
    match order.principal_ideal(&element) {
        Ok(ideal) => {
            let norm = ideal.norm();
            let agree = norm == BigInt::from(9);
            Outcome {
                verdict: if agree {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: Trust::Uncertified,
                expected: "9 (N(2+sqrt(-5)) = 4+5 = 9)".to_string(),
                actual: format!("norm={norm}"),
            }
        }
        Err(reason) => declined(&format!("principal_ideal(2+sqrt(-5)): {reason:?}")),
    }
}

/// `3` splits in `Q(sqrt(-5))` (discriminant `-20`): `(-20/3) = 1` (a
/// quadratic residue), confirmed independently by `SymPy`'s Jacobi symbol in
/// `ground_truth.py`.
fn nfi2_prime_splitting_3_splits() -> Outcome {
    let order = match QuadraticOrder::new(&BigInt::from(-5)) {
        Ok(order) => order,
        Err(err) => return declined(&format!("QuadraticOrder::new(-5): {err:?}")),
    };
    match order.split_prime(&BigInt::from(3)) {
        Ok((_factors, cert)) => {
            let verified = cert.verify().is_ok();
            let is_split = matches!(cert.splitting, SplittingType::Split);
            let agree = verified && is_split;
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
                expected: "Split ((-20/3) = 1)".to_string(),
                actual: format!("{:?}, verify_ok={verified}", cert.splitting),
            }
        }
        Err(reason) => declined(&format!("split_prime(3) in Q(sqrt(-5)): {reason:?}")),
    }
}
/// Near-miss control: `2` RAMIFIES in the same field (`2` divides the
/// discriminant `-20`), the flip-side classification at a different prime.
fn nfi2_prime_splitting_2_ramifies_ctrl() -> Outcome {
    let order = match QuadraticOrder::new(&BigInt::from(-5)) {
        Ok(order) => order,
        Err(err) => return declined(&format!("QuadraticOrder::new(-5): {err:?}")),
    };
    match order.split_prime(&BigInt::from(2)) {
        Ok((_factors, cert)) => {
            let verified = cert.verify().is_ok();
            let is_ramified = matches!(cert.splitting, SplittingType::Ramified);
            let agree = verified && is_ramified;
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
                expected: "Ramified (2 divides the discriminant -20)".to_string(),
                actual: format!("{:?}, verify_ok={verified}", cert.splitting),
            }
        }
        Err(reason) => declined(&format!("split_prime(2) in Q(sqrt(-5)): {reason:?}")),
    }
}

/// The class number of `Q(sqrt(-5))` (discriminant `-20`) is 2 -- the
/// textbook example of a non-UFD ring of integers (`6 = 2*3 =
/// (1+sqrt(-5))(1-sqrt(-5))`), independently confirmed by hand-enumerating
/// reduced binary quadratic forms in `ground_truth.py`.
fn nfi3_class_number_20() -> Outcome {
    match ideal_class_number(&BigInt::from(-20)) {
        Ok((h, cert)) => {
            let verified = cert.verify().is_ok();
            let agree = verified && h == 2;
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
                expected: "2 (h(-20) = 2, the classical Z[sqrt(-5)] non-UFD example)".to_string(),
                actual: format!("h={h}, verify_ok={verified}"),
            }
        }
        Err(reason) => declined(&format!("class_number(-20): {reason:?}")),
    }
}

// ============================================================================
// Entries: second-pass modules — permgroup_sylow
// ============================================================================

fn s4_group() -> Option<PermutationGroup> {
    let gens: Vec<Permutation> = (0..3)
        .map(|i| Permutation::from_cycles(&[vec![i, i + 1]], 4))
        .collect::<Option<Vec<_>>>()?;
    PermutationGroup::from_generators(gens, 4)
}
fn a4_group() -> Option<PermutationGroup> {
    let gens: Vec<Permutation> = (2..4)
        .map(|k| Permutation::from_cycles(&[vec![0, 1, k]], 4))
        .collect::<Option<Vec<_>>>()?;
    PermutationGroup::from_generators(gens, 4)
}

/// `S4`'s Sylow-2 subgroup has order `2^3 = 8` (`|S4|=24=2^3*3`), and there
/// are `n_2=3` of them -- the standard textbook fact (e.g. Dummit & Foote,
/// worked as the dihedral-of-the-square example).
fn sy1_s4_sylow2_order() -> Outcome {
    let Some(s4) = s4_group() else {
        return declined("S4 construction");
    };
    match s4.sylow_subgroup(2) {
        Ok((sylow2, cert)) => {
            let verified = cert.verify().is_ok();
            let order_ok = sylow2.order() == 8;
            match s4.sylow_count(&sylow2, 2) {
                Ok(count_cert) => {
                    let count_verified = count_cert.verify().is_ok();
                    let count_ok = count_cert.n_p == 3;
                    let agree = verified && order_ok && count_verified && count_ok;
                    Outcome {
                        verdict: if agree {
                            Verdict::Agree
                        } else {
                            Verdict::Disagree
                        },
                        trust: if verified && count_verified {
                            Trust::Certified
                        } else {
                            Trust::Unknown
                        },
                        expected: "order 8, n_2=3".to_string(),
                        actual: format!(
                            "order={}, n_2={}, verify_ok={verified}, count_verify_ok={count_verified}",
                            sylow2.order(),
                            count_cert.n_p
                        ),
                    }
                }
                Err(reason) => declined(&format!("sylow_count(sylow2, 2): {reason:?}")),
            }
        }
        Err(reason) => declined(&format!("sylow_subgroup(2) of S4: {reason:?}")),
    }
}

/// `S4`'s Sylow-3 subgroup has order 3, and there are `n_3=4` of them.
fn sy2_s4_sylow3_count() -> Outcome {
    let Some(s4) = s4_group() else {
        return declined("S4 construction");
    };
    match s4.sylow_subgroup(3) {
        Ok((sylow3, cert)) => {
            let verified = cert.verify().is_ok();
            let order_ok = sylow3.order() == 3;
            match s4.sylow_count(&sylow3, 3) {
                Ok(count_cert) => {
                    let count_verified = count_cert.verify().is_ok();
                    let count_ok = count_cert.n_p == 4;
                    let agree = verified && order_ok && count_verified && count_ok;
                    Outcome {
                        verdict: if agree {
                            Verdict::Agree
                        } else {
                            Verdict::Disagree
                        },
                        trust: if verified && count_verified {
                            Trust::Certified
                        } else {
                            Trust::Unknown
                        },
                        expected: "order 3, n_3=4".to_string(),
                        actual: format!(
                            "order={}, n_3={}, verify_ok={verified}, count_verify_ok={count_verified}",
                            sylow3.order(),
                            count_cert.n_p
                        ),
                    }
                }
                Err(reason) => declined(&format!("sylow_count(sylow3, 3): {reason:?}")),
            }
        }
        Err(reason) => declined(&format!("sylow_subgroup(3) of S4: {reason:?}")),
    }
}

/// `A4` (index 2 in `S4`) is normal -- every index-2 subgroup is,
/// classically.
fn sy3_a4_normal_in_s4() -> Outcome {
    let (Some(s4), Some(a4)) = (s4_group(), a4_group()) else {
        return declined("S4/A4 construction");
    };
    match s4.is_normal(&a4) {
        Ok(cert) => {
            let verified = cert.verify().is_ok();
            let is_normal = matches!(cert, NormalityCertificate::Normal { .. });
            let agree = verified && is_normal;
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
                expected: "Normal (A4 has index 2 in S4)".to_string(),
                actual: format!("{cert:?}, verify_ok={verified}"),
            }
        }
        Err(reason) => declined(&format!("is_normal(S4, A4): {reason:?}")),
    }
}
/// Near-miss control: a Sylow-3 subgroup of `S4` (order 3, `n_3=4>1`) is NOT
/// normal -- the flip side of `sy3-a4-normal-in-s4`, by the standard fact
/// that a Sylow subgroup is normal iff it is the only one.
fn sy3_a4_normal_in_s4_ctrl() -> Outcome {
    let Some(s4) = s4_group() else {
        return declined("S4 construction");
    };
    match s4.sylow_subgroup(3) {
        Ok((sylow3, _)) => match s4.is_normal(&sylow3) {
            Ok(cert) => {
                let verified = cert.verify().is_ok();
                let not_normal = matches!(cert, NormalityCertificate::NotNormal { .. });
                let agree = verified && not_normal;
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
                    expected: "NotNormal (n_3=4 > 1, so no Sylow-3 subgroup is normal)".to_string(),
                    actual: format!("{cert:?}, verify_ok={verified}"),
                }
            }
            Err(reason) => declined(&format!("is_normal(S4, sylow3): {reason:?}")),
        },
        Err(reason) => declined(&format!("sylow_subgroup(3) of S4: {reason:?}")),
    }
}

// ============================================================================
// Entries: second-pass modules — homology_coefficients / homology_cohomology
// ============================================================================

/// The standard 6-vertex triangulation of the real projective plane RP^2
/// (`b=(1,0,0)` over Z with torsion Z/2 at `H_1` -- a classical fact, any
/// algebraic topology text, e.g. Hatcher).
fn rp2_6v() -> Option<SimplicialComplex> {
    SimplicialComplex::from_maximal_simplices(&[
        vec![0, 1, 2],
        vec![0, 1, 4],
        vec![0, 2, 3],
        vec![0, 3, 5],
        vec![0, 4, 5],
        vec![1, 2, 5],
        vec![1, 3, 4],
        vec![1, 3, 5],
        vec![2, 3, 4],
        vec![2, 4, 5],
    ])
}

/// Over `F_2` the torsion becomes a free rank-1 contribution:
/// `b_1(F2) = b_1(Z) + t_1 + t_0 = 0+1+0 = 1` (universal coefficient
/// theorem).
fn hc1_rp2_torsion_f2() -> Outcome {
    let Some(complex) = rp2_6v() else {
        return declined("SimplicialComplex::from_maximal_simplices (RP^2)");
    };
    match coefficients::homology_with_coefficients(&complex) {
        Some(cert) => {
            let verified = cert.verify(&complex).is_ok();
            let b1_f2 = cert.betti_f2.get(&1).copied();
            let agree = verified && b1_f2 == Some(1);
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
                expected: "b1(F2)=1 (UCT: b1(Z)=0 plus the even Z/2 torsion of H_1)".to_string(),
                actual: format!("betti_f2={:?}, verify_ok={verified}", cert.betti_f2),
            }
        }
        None => declined("homology_with_coefficients(RP^2)"),
    }
}
/// Near-miss control on the SAME complex: over `Q`, torsion vanishes and
/// `b1(Q)=b1(Z)=0` -- DIFFERENT from `b1(F2)=1` above, demonstrating the
/// coefficient ring genuinely changes the answer.
fn hc1_rp2_torsion_q_ctrl() -> Outcome {
    let Some(complex) = rp2_6v() else {
        return declined("SimplicialComplex::from_maximal_simplices (RP^2)");
    };
    match coefficients::homology_with_coefficients(&complex) {
        Some(cert) => {
            let verified = cert.verify(&complex).is_ok();
            let b1_q = cert.betti_q.get(&1).copied();
            let b1_f2 = cert.betti_f2.get(&1).copied();
            let agree = verified && b1_q == Some(0) && b1_q != b1_f2;
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
                expected: "b1(Q)=0, DIFFERENT from b1(F2)=1 (coefficients matter)".to_string(),
                actual: format!(
                    "betti_q={:?}, betti_f2={:?}, verify_ok={verified}",
                    cert.betti_q, cert.betti_f2
                ),
            }
        }
        None => declined("homology_with_coefficients(RP^2)"),
    }
}

fn hollow_triangle() -> Option<SimplicialComplex> {
    SimplicialComplex::from_maximal_simplices(&[vec![0, 1], vec![1, 2], vec![0, 2]])
}
fn tetrahedron_boundary() -> Option<SimplicialComplex> {
    SimplicialComplex::from_maximal_simplices(&[
        vec![0, 1, 2],
        vec![0, 1, 3],
        vec![0, 2, 3],
        vec![1, 2, 3],
    ])
}

/// A hollow triangle (circle S^1, torsion-free): all three coefficient
/// rings agree, `b=(1,1)`.
fn hc2_circle_agrees_across_rings() -> Outcome {
    let Some(complex) = hollow_triangle() else {
        return declined("SimplicialComplex::from_maximal_simplices (hollow triangle)");
    };
    match coefficients::homology_with_coefficients(&complex) {
        Some(cert) => {
            let verified = cert.verify(&complex).is_ok();
            let expected: BTreeMap<usize, usize> = [(0, 1), (1, 1)].into_iter().collect();
            let agree = verified && cert.betti_f2 == expected && cert.betti_q == expected;
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
                expected: "b=(1,1) over F2 and Q alike (torsion-free)".to_string(),
                actual: format!(
                    "betti_f2={:?}, betti_q={:?}, verify_ok={verified}",
                    cert.betti_f2, cert.betti_q
                ),
            }
        }
        None => declined("homology_with_coefficients(circle)"),
    }
}

/// The boundary of a tetrahedron (four triangular faces on 4 vertices, no
/// interior) is homotopy equivalent to `S^2`: `b=(1,0,1)`, torsion-free, so
/// again agrees across `Z`/`F2`/`Q` (Euler characteristic `4-6+4=2=1-0+1`).
fn hc3_sphere_boundary_tetrahedron() -> Outcome {
    let Some(complex) = tetrahedron_boundary() else {
        return declined("SimplicialComplex::from_maximal_simplices (tetrahedron boundary)");
    };
    match coefficients::homology_with_coefficients(&complex) {
        Some(cert) => {
            let verified = cert.verify(&complex).is_ok();
            let expected: BTreeMap<usize, usize> = [(0, 1), (1, 0), (2, 1)].into_iter().collect();
            let agree = verified && cert.betti_f2 == expected && cert.betti_q == expected;
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
                expected: "b=(1,0,1) over F2 and Q alike (S^2, torsion-free)".to_string(),
                actual: format!(
                    "betti_f2={:?}, betti_q={:?}, verify_ok={verified}",
                    cert.betti_f2, cert.betti_q
                ),
            }
        }
        None => declined("homology_with_coefficients(tetrahedron boundary)"),
    }
}

/// RP^2's cohomology has its torsion SHIFTED UP one degree from homology:
/// `H_1(RP^2;Z)=Z/2` but `H^1(RP^2;Z)` is torsion-free (free rank 0, since
/// `b_1=0`) while `H^2(RP^2;Z)` carries the torsion -- the classical
/// universal coefficient theorem for cohomology (Ext shifts torsion up one
/// degree; any algebraic topology text).
fn co1_rp2_cohomology_torsion_shift() -> Outcome {
    let Some(complex) = rp2_6v() else {
        return declined("SimplicialComplex::from_maximal_simplices (RP^2)");
    };
    match cohomology::cohomology(&complex) {
        Some(cert) => {
            let verified = cert.verify(&complex).is_ok();
            let h2_torsion = cert.torsion.get(&2).cloned().unwrap_or_default();
            let agree = verified && h2_torsion == vec![2];
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
                expected: "H^2 torsion = [2] (the Z/2 shifted up from H_1)".to_string(),
                actual: format!("torsion={:?}, verify_ok={verified}", cert.torsion),
            }
        }
        None => declined("cohomology(RP^2)"),
    }
}
/// Near-miss control on the SAME complex: `H^1` carries NO torsion (the
/// shift moves it to `H^2`, not `H^1`) -- the precise degree matters.
fn co1_rp2_cohomology_torsion_not_at_h1_ctrl() -> Outcome {
    let Some(complex) = rp2_6v() else {
        return declined("SimplicialComplex::from_maximal_simplices (RP^2)");
    };
    match cohomology::cohomology(&complex) {
        Some(cert) => {
            let verified = cert.verify(&complex).is_ok();
            let h1_torsion = cert.torsion.get(&1).cloned().unwrap_or_default();
            let agree = verified && h1_torsion.is_empty();
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
                expected: "H^1 torsion = [] (NOT where the torsion lands)".to_string(),
                actual: format!("torsion={:?}, verify_ok={verified}", cert.torsion),
            }
        }
        None => declined("cohomology(RP^2)"),
    }
}

/// The hollow triangle (circle): free ranks `(1,1)`, no torsion anywhere --
/// cohomology agrees with homology exactly in the torsion-free case.
fn co2_circle_cohomology() -> Outcome {
    let Some(complex) = hollow_triangle() else {
        return declined("SimplicialComplex::from_maximal_simplices (hollow triangle)");
    };
    match cohomology::cohomology(&complex) {
        Some(cert) => {
            let verified = cert.verify(&complex).is_ok();
            let expected: BTreeMap<usize, usize> = [(0, 1), (1, 1)].into_iter().collect();
            let no_torsion = cert.torsion.values().all(Vec::is_empty);
            let agree = verified && cert.free_rank == expected && no_torsion;
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
                expected: "free_rank=(1,1), no torsion".to_string(),
                actual: format!(
                    "free_rank={:?}, torsion={:?}, verify_ok={verified}",
                    cert.free_rank, cert.torsion
                ),
            }
        }
        None => declined("cohomology(circle)"),
    }
}

/// The boundary of a tetrahedron (`S^2`): free ranks `(1,0,1)`, no torsion.
fn co3_sphere_cohomology() -> Outcome {
    let Some(complex) = tetrahedron_boundary() else {
        return declined("SimplicialComplex::from_maximal_simplices (tetrahedron boundary)");
    };
    match cohomology::cohomology(&complex) {
        Some(cert) => {
            let verified = cert.verify(&complex).is_ok();
            let expected: BTreeMap<usize, usize> = [(0, 1), (1, 0), (2, 1)].into_iter().collect();
            let no_torsion = cert.torsion.values().all(Vec::is_empty);
            let agree = verified && cert.free_rank == expected && no_torsion;
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
                expected: "free_rank=(1,0,1), no torsion".to_string(),
                actual: format!(
                    "free_rank={:?}, torsion={:?}, verify_ok={verified}",
                    cert.free_rank, cert.torsion
                ),
            }
        }
        None => declined("cohomology(tetrahedron boundary)"),
    }
}

// ============================================================================
// Entries: second-pass modules — homology_induced
// ============================================================================

/// The identity map on the hollow triangle (circle) induces an isomorphism
/// on both `H_0` and `H_1`: rank 1 each.
fn ind1_circle_identity_isomorphism() -> Outcome {
    let Some(circle) = hollow_triangle() else {
        return declined("SimplicialComplex::from_maximal_simplices (circle)");
    };
    let vertex_map: BTreeMap<usize, usize> = [(0, 0), (1, 1), (2, 2)].into_iter().collect();
    match induced::induced_homology(&vertex_map, &circle, &circle) {
        Some(cert) => {
            let verified = cert.verify(&circle, &circle).is_ok();
            let expected: BTreeMap<usize, usize> = [(0, 1), (1, 1)].into_iter().collect();
            let agree = verified && cert.induced_rank == expected;
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
                expected: "induced_rank=(1,1) (identity is an isomorphism on H_*)".to_string(),
                actual: format!("induced_rank={:?}, verify_ok={verified}", cert.induced_rank),
            }
        }
        None => declined("induced_homology(identity on circle)"),
    }
}

/// Near-miss counterpoint to `ind1`: the SAME circle collapsed onto a single
/// edge (vertex 2 identified with vertex 0) forces `H_1`'s induced map to
/// have rank 0 (the target `H_1(edge)=0` has no room for anything nonzero),
/// while `H_0` still maps isomorphically (both are connected).
fn ind2_circle_collapse_to_edge() -> Outcome {
    let Some(circle) = hollow_triangle() else {
        return declined("SimplicialComplex::from_maximal_simplices (circle)");
    };
    let Some(edge) = SimplicialComplex::from_maximal_simplices(&[vec![0, 1]]) else {
        return declined("SimplicialComplex::from_maximal_simplices (single edge)");
    };
    let vertex_map: BTreeMap<usize, usize> = [(0, 0), (1, 1), (2, 0)].into_iter().collect();
    match induced::induced_homology(&vertex_map, &circle, &edge) {
        Some(cert) => {
            let verified = cert.verify(&circle, &edge).is_ok();
            let expected: BTreeMap<usize, usize> = [(0, 1), (1, 0)].into_iter().collect();
            let agree = verified && cert.induced_rank == expected;
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
                expected: "induced_rank=(1,0) (H_1 of the target is 0, forcing rank 0)".to_string(),
                actual: format!("induced_rank={:?}, verify_ok={verified}", cert.induced_rank),
            }
        }
        None => declined("induced_homology(circle collapsed to an edge)"),
    }
}

/// `is_simplicial` correctly REJECTS a vertex map whose image is not a face
/// of the codomain: the circle's edge `{0,1}` would map to `{0,1}`, which
/// is not a face of a codomain with only two ISOLATED points (no edge
/// between them).
fn ind3_is_simplicial_rejects_missing_face() -> Outcome {
    let Some(circle) = hollow_triangle() else {
        return declined("SimplicialComplex::from_maximal_simplices (circle)");
    };
    let Some(two_points) = SimplicialComplex::from_maximal_simplices(&[vec![0], vec![1]]) else {
        return declined("SimplicialComplex::from_maximal_simplices (two isolated points)");
    };
    let vertex_map: BTreeMap<usize, usize> = [(0, 0), (1, 1), (2, 0)].into_iter().collect();
    let is_simplicial = induced::is_simplicial(&vertex_map, &circle, &two_points);
    Outcome {
        verdict: if is_simplicial {
            Verdict::Disagree
        } else {
            Verdict::Agree
        },
        trust: Trust::Uncertified,
        expected: "false (the image edge {0,1} is not a face of two isolated points)".to_string(),
        actual: format!("is_simplicial={is_simplicial}"),
    }
}

// ============================================================================
// Entries: second-pass modules — homology_persistent
// ============================================================================

/// The standard "circle then fill" persistence example: 3 vertices, then 3
/// edges (closing the triangle's boundary at index 5), then the 2-face
/// (index 6). The `H_1` loop is born at the closing edge and dies when the
/// triangle is filled -- the textbook persistent-homology example.
fn circle_then_fill() -> Vec<Vec<usize>> {
    vec![
        vec![0],
        vec![1],
        vec![2],
        vec![0, 1],
        vec![1, 2],
        vec![0, 2],
        vec![0, 1, 2],
    ]
}

fn per1_circle_then_fill_h1_bar() -> Outcome {
    let filtration = circle_then_fill();
    match persistent::persistent_homology(&filtration) {
        Some(cert) => {
            let verified = cert.verify().is_ok();
            let h1_bars: Vec<_> = cert.pairs.iter().filter(|&&(dim, _, _)| dim == 1).collect();
            let agree = verified && h1_bars.len() == 1 && *h1_bars[0] == (1, 5, 6);
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
                expected:
                    "exactly one H_1 bar, (1, 5, 6): born at the closing edge, dies when filled"
                        .to_string(),
                actual: format!("h1_bars={h1_bars:?}, verify_ok={verified}"),
            }
        }
        None => declined("persistent_homology(circle_then_fill)"),
    }
}

fn per2_circle_then_fill_h0_essential() -> Outcome {
    let filtration = circle_then_fill();
    match persistent::persistent_homology(&filtration) {
        Some(cert) => {
            let verified = cert.verify().is_ok();
            let h0_essential = cert.essential.iter().filter(|&&(dim, _)| dim == 0).count();
            let h0_pairs = cert.pairs.iter().filter(|&&(dim, _, _)| dim == 0).count();
            let agree = verified && h0_essential == 1 && h0_pairs == 2;
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
                expected: "1 essential H_0 bar (final component), 2 finite H_0 bars (two merges)"
                    .to_string(),
                actual: format!(
                    "h0_essential={h0_essential}, h0_pairs={h0_pairs}, verify_ok={verified}"
                ),
            }
        }
        None => declined("persistent_homology(circle_then_fill)"),
    }
}

/// Before the closing edge is added (`m=5`, the first 5 entries), the
/// prefix complex is a graph with no 2-simplex -- it cannot yet contain the
/// filled triangle.
fn per3_prefix_before_fill_lacks_triangle() -> Outcome {
    let filtration = circle_then_fill();
    match persistent::prefix_complex(&filtration, 5) {
        Some(complex) => {
            let has_triangle = complex.contains_face(&[0, 1, 2]);
            Outcome {
                verdict: if has_triangle {
                    Verdict::Disagree
                } else {
                    Verdict::Agree
                },
                trust: Trust::Uncertified,
                expected: "false (the triangle has not been added yet at m=5)".to_string(),
                actual: format!("contains_face([0,1,2])={has_triangle}"),
            }
        }
        None => declined("prefix_complex(circle_then_fill, 5)"),
    }
}
/// Near-miss control: at `m=7` (the full filtration), the prefix complex
/// DOES contain the triangle.
fn per3_prefix_after_fill_has_triangle_ctrl() -> Outcome {
    let filtration = circle_then_fill();
    match persistent::prefix_complex(&filtration, 7) {
        Some(complex) => {
            let has_triangle = complex.contains_face(&[0, 1, 2]);
            Outcome {
                verdict: if has_triangle {
                    Verdict::Agree
                } else {
                    Verdict::Disagree
                },
                trust: Trust::Uncertified,
                expected: "true (the full filtration includes the triangle)".to_string(),
                actual: format!("contains_face([0,1,2])={has_triangle}"),
            }
        }
        None => declined("prefix_complex(circle_then_fill, 7)"),
    }
}

// ============================================================================
// Entries: second-pass modules — qe_big (the private BigRational engine,
// exercised indirectly through the public qe::eliminate/eliminate_forall
// front door -- qe_big itself declares no public items)
// ============================================================================

fn huge(pow: u32) -> BigRational {
    BigRational::from_integer(BigInt::from(10u32).pow(pow))
}

/// `exists x. x^2 - 10^50 = 0` -- true, witnessed by `10^25`, at a magnitude
/// that overflows `i128` (max ~1.7e38) even before any Cauchy-bound
/// squaring.
fn qeb1_huge_coefficient_exists() -> Outcome {
    let atom = Atom::new(vec![-huge(50), bigrat(0), bigrat(1)], Relation::Eq);
    let formula = ExistsFormula::new(vec![atom]);
    match qe::eliminate(&formula) {
        Some(true) => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Certified,
            expected: "true (witnessed by 10^25)".to_string(),
            actual: "true (self-verified by eliminate)".to_string(),
        },
        Some(false) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Certified,
            expected: "true".to_string(),
            actual: "false (self-verified by eliminate)".to_string(),
        },
        None => declined("eliminate(exists x. x^2-10^50=0)"),
    }
}
/// Near-miss control: `exists x. x^2 + 10^50 = 0` -- false (`x^2 >= 0`
/// always, so the sum with a huge POSITIVE constant is never zero).
fn qeb1_huge_coefficient_exists_ctrl() -> Outcome {
    let atom = Atom::new(vec![huge(50), bigrat(0), bigrat(1)], Relation::Eq);
    let formula = ExistsFormula::new(vec![atom]);
    match qe::eliminate(&formula) {
        Some(false) => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Certified,
            expected: "false (x^2 >= 0 always, so x^2+10^50 never 0)".to_string(),
            actual: "false (self-verified by eliminate)".to_string(),
        },
        Some(true) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Certified,
            expected: "false".to_string(),
            actual: "true (self-verified by eliminate)".to_string(),
        },
        None => declined("eliminate(exists x. x^2+10^50=0)"),
    }
}

/// `forall x. x^2 + 10^50 > 0` -- true (always, same reasoning as the
/// control above but universally quantified).
fn qeb2_huge_coefficient_forall() -> Outcome {
    let atom = Atom::new(vec![huge(50), bigrat(0), bigrat(1)], Relation::Gt);
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
        None => declined("eliminate_forall(forall x. x^2+10^50>0)"),
    }
}

/// `exists x. x - 10^50 > 0` -- true, witnessed by any `x > 10^50` (a huge
/// LINEAR coefficient, exercising a different atom shape than the
/// quadratic cases above).
fn qeb3_huge_coefficient_inequality() -> Outcome {
    let atom = Atom::new(vec![-huge(50), bigrat(1)], Relation::Gt);
    let formula = ExistsFormula::new(vec![atom]);
    match qe::eliminate(&formula) {
        Some(true) => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Certified,
            expected: "true (witnessed by any x > 10^50)".to_string(),
            actual: "true (self-verified by eliminate)".to_string(),
        },
        Some(false) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Certified,
            expected: "true".to_string(),
            actual: "false (self-verified by eliminate)".to_string(),
        },
        None => declined("eliminate(exists x. x-10^50>0)"),
    }
}

// ============================================================================
// Entries: second-pass modules — qe_dnf
// ============================================================================

/// `exists x. (x-2=0) OR (x+2=0)` -- true (witnessed by the first disjunct
/// at x=2).
fn dnf1_true_via_first_disjunct() -> Outcome {
    let disjuncts = vec![
        vec![Atom::new(qe::integer_poly(&[-2, 1]), Relation::Eq)],
        vec![Atom::new(qe::integer_poly(&[2, 1]), Relation::Eq)],
    ];
    let formula = Dnf::new(disjuncts);
    match eliminate_dnf(&formula) {
        Some(true) => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Certified,
            expected: "true (x=2 satisfies the first disjunct)".to_string(),
            actual: "true (self-verified by eliminate_dnf)".to_string(),
        },
        Some(false) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Certified,
            expected: "true".to_string(),
            actual: "false (self-verified by eliminate_dnf)".to_string(),
        },
        None => declined("eliminate_dnf((x-2=0) OR (x+2=0))"),
    }
}

/// `exists x. x^2+1=0` (a single, unsatisfiable disjunct) -- false, no real
/// root.
fn dnf2_false_no_real_root() -> Outcome {
    let disjuncts = vec![vec![Atom::new(qe::integer_poly(&[1, 0, 1]), Relation::Eq)]];
    let formula = Dnf::new(disjuncts);
    match eliminate_dnf(&formula) {
        Some(false) => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Certified,
            expected: "false (x^2+1=0 has no real root)".to_string(),
            actual: "false (self-verified by eliminate_dnf)".to_string(),
        },
        Some(true) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Certified,
            expected: "false".to_string(),
            actual: "true (self-verified by eliminate_dnf)".to_string(),
        },
        None => declined("eliminate_dnf(x^2+1=0)"),
    }
}

/// `exists x. x>0 AND x<0` (a conjunction WITHIN one disjunct) -- false, the
/// empty intersection.
fn dnf3_conjunction_unsat() -> Outcome {
    let disjuncts = vec![vec![
        Atom::new(qe::integer_poly(&[0, 1]), Relation::Gt),
        Atom::new(qe::integer_poly(&[0, 1]), Relation::Lt),
    ]];
    let formula = Dnf::new(disjuncts);
    match eliminate_dnf(&formula) {
        Some(false) => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Certified,
            expected: "false (x>0 and x<0 cannot both hold)".to_string(),
            actual: "false (self-verified by eliminate_dnf)".to_string(),
        },
        Some(true) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Certified,
            expected: "false".to_string(),
            actual: "true (self-verified by eliminate_dnf)".to_string(),
        },
        None => declined("eliminate_dnf(x>0 AND x<0)"),
    }
}
/// Near-miss control: `exists x. x>0 AND x<5` -- true (e.g. x=1), the same
/// conjunction SHAPE as `dnf3` but satisfiable.
fn dnf3_conjunction_sat_ctrl() -> Outcome {
    let disjuncts = vec![vec![
        Atom::new(qe::integer_poly(&[0, 1]), Relation::Gt),
        Atom::new(qe::integer_poly(&[-5, 1]), Relation::Lt),
    ]];
    let formula = Dnf::new(disjuncts);
    match eliminate_dnf(&formula) {
        Some(true) => Outcome {
            verdict: Verdict::Agree,
            trust: Trust::Certified,
            expected: "true (e.g. x=1 satisfies 0<x<5)".to_string(),
            actual: "true (self-verified by eliminate_dnf)".to_string(),
        },
        Some(false) => Outcome {
            verdict: Verdict::Disagree,
            trust: Trust::Certified,
            expected: "true".to_string(),
            actual: "false (self-verified by eliminate_dnf)".to_string(),
        },
        None => declined("eliminate_dnf(x>0 AND x<5)"),
    }
}

// ============================================================================
// Entries: second-pass modules — qe_bivariate
// ============================================================================

fn bipoly(rows: &[&[i128]]) -> Vec<Vec<Rational>> {
    rows.iter()
        .map(|row| row.iter().map(|&c| Rational::integer(c)).collect())
        .collect()
}

/// The unit circle's boundary `y^2+x^2-1=0`: `exists y` holds exactly on
/// the CLOSED interval `x in [-1,1]`.
fn bv1_circle_boundary_closed() -> Outcome {
    let atom = BiAtom::new(bipoly(&[&[-1, 0, 1], &[0], &[1]]), Relation::Eq);
    match eliminate_y(&ExistsYFormula::new(vec![atom])) {
        Ok(cert) => {
            let verified = cert.verify().is_ok();
            let description = cert.describe();
            let agree = verified && description == "x ∈ [-1, 1]";
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
                expected: "x ∈ [-1, 1] (the unit circle's boundary)".to_string(),
                actual: format!("{description}, verify_ok={verified}"),
            }
        }
        Err(fault) => declined(&format!("eliminate_y(y^2+x^2-1=0): {fault:?}")),
    }
}
/// Near-miss control: the SAME polynomial but `>` instead of `=` -- `exists
/// y. y^2+x^2-1>0` is a TAUTOLOGY (`y` unbounded, so `y^2` can always
/// exceed `1-x^2`), the whole line rather than a bounded interval.
fn bv1_exterior_tautology_ctrl() -> Outcome {
    let atom = BiAtom::new(bipoly(&[&[-1, 0, 1], &[0], &[1]]), Relation::Gt);
    match eliminate_y(&ExistsYFormula::new(vec![atom])) {
        Ok(cert) => {
            let verified = cert.verify().is_ok();
            let description = cert.describe();
            let agree = verified && description == "x ∈ (-∞, ∞)";
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
                expected: "x ∈ (-∞, ∞) (y is unbounded, so this always holds)".to_string(),
                actual: format!("{description}, verify_ok={verified}"),
            }
        }
        Err(fault) => declined(&format!("eliminate_y(y^2+x^2-1>0): {fault:?}")),
    }
}

/// The open unit disk `y^2+x^2-1<0`: `exists y` holds on the OPEN interval
/// `x in (-1,1)` -- this crate's own doctest example for `eliminate_y`.
fn bv2_disk_interior_open() -> Outcome {
    let atom = BiAtom::new(bipoly(&[&[-1, 0, 1], &[0], &[1]]), Relation::Lt);
    match eliminate_y(&ExistsYFormula::new(vec![atom])) {
        Ok(cert) => {
            let verified = cert.verify().is_ok();
            let description = cert.describe();
            let agree = verified && description == "x ∈ (-1, 1)";
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
                expected: "x ∈ (-1, 1) (the open unit disk)".to_string(),
                actual: format!("{description}, verify_ok={verified}"),
            }
        }
        Err(fault) => declined(&format!("eliminate_y(y^2+x^2-1<0): {fault:?}")),
    }
}

/// The parabola `y^2-x=0`: `exists y` holds exactly on `x >= 0`.
fn bv3_parabola_halfline() -> Outcome {
    let atom = BiAtom::new(bipoly(&[&[0, -1], &[0], &[1]]), Relation::Eq);
    match eliminate_y(&ExistsYFormula::new(vec![atom])) {
        Ok(cert) => {
            let verified = cert.verify().is_ok();
            let description = cert.describe();
            let agree = verified && description == "x ∈ [0, ∞)";
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
                expected: "x ∈ [0, ∞) (y=sqrt(x) real iff x>=0)".to_string(),
                actual: format!("{description}, verify_ok={verified}"),
            }
        }
        Err(fault) => declined(&format!("eliminate_y(y^2-x=0): {fault:?}")),
    }
}

// ============================================================================
// Entries: second-pass — symbolic-lambda Poisson (probability, item 9 wave
// two)
// ============================================================================

/// `Poisson(lambda)` with SYMBOLIC lambda: total mass certifies to exactly
/// 1 (the exponential-series machinery this crate's `infinite_sum` gained,
/// per file 13's item 9 wave-two log).
fn prob4_poisson_symbolic_totalmass() -> Outcome {
    let d = Discrete::Poisson(CasExpr::var("lam"));
    let cert = d.total_mass();
    let certified = cert.is_certified();
    let matches_expected = matches!(
        equal(&cert.claim, &i(1)),
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
        expected: "certified total mass 1, with SYMBOLIC lambda".to_string(),
        actual: format!("certified={certified}, claim={}", cert.claim),
    }
}

/// `E[Poisson(lambda)] = lambda`, symbolic.
fn prob5_poisson_symbolic_mean() -> Outcome {
    let d = Discrete::Poisson(CasExpr::var("lam"));
    let cert = d.mean();
    let certified = cert.is_certified();
    let matches_expected = matches!(
        equal(&cert.claim, &CasExpr::var("lam")),
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
        expected: "certified: E[Poisson(lambda)] = lambda, symbolic".to_string(),
        actual: format!("certified={certified}, claim={}", cert.claim),
    }
}

/// `Var[Poisson(lambda)] = lambda`, symbolic (the Poisson's mean and
/// variance always coincide).
fn prob6_poisson_symbolic_variance() -> Outcome {
    let d = Discrete::Poisson(CasExpr::var("lam"));
    let cert = d.variance();
    let certified = cert.is_certified();
    let matches_expected = matches!(
        equal(&cert.claim, &CasExpr::var("lam")),
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
        expected: "certified: Var[Poisson(lambda)] = lambda, symbolic".to_string(),
        actual: format!("certified={certified}, claim={}", cert.claim),
    }
}
/// Near-miss control: the variance certificate's claim is NOT `2*lambda` --
/// a plausible-looking wrong answer (mean+variance summed, or a doubled
/// variance) that the certificate must not agree with.
fn prob6_poisson_symbolic_variance_ctrl() -> Outcome {
    let d = Discrete::Poisson(CasExpr::var("lam"));
    let cert = d.variance();
    let wrong_claim = i(2) * CasExpr::var("lam");
    let equals_wrong = matches!(
        equal(&cert.claim, &wrong_claim),
        ZeroTest::Certified { equal: true, .. }
    );
    Outcome {
        verdict: if equals_wrong {
            Verdict::Disagree
        } else {
            Verdict::Agree
        },
        trust: Trust::Certified,
        expected: "the variance claim is NOT 2*lambda".to_string(),
        actual: format!("claim={}, equals_2lambda={equals_wrong}", cert.claim),
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
    use Tier::{Core, DeclineExpected};
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
        e!(
            "e1-radical-cross-base",
            Some("simplify/equal"),
            None,
            Core,
            e1_radical_cross_base
        ),
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
            "enc2-gamma-euler",
            None,
            Some("enclosure"),
            Core,
            enc2_gamma_euler
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
            "prob2-poisson-totalmass",
            None,
            Some("probability"),
            Core,
            prob2_poisson_totalmass
        ),
        e!(
            "prob3-binomial-mean",
            None,
            Some("probability"),
            Core,
            prob3_binomial_mean
        ),
        e!(
            "prob4-exponential-symbolic-mgf",
            None,
            Some("probability"),
            Core,
            prob4_exponential_symbolic_mgf
        ),
        e!(
            "prob5-normal-symbolic-mgf",
            None,
            Some("probability"),
            Core,
            prob5_normal_symbolic_mgf
        ),
        e!(
            "prob6-normal-negative-variance",
            None,
            Some("probability"),
            DeclineExpected,
            prob6_normal_negative_variance_declines
        ),
        e!(
            "prob7-geometric-symbolic-p",
            None,
            Some("probability"),
            Core,
            prob7_geometric_symbolic_p_mean
        ),
        e!(
            "prob8-geometric-symbolic-mgf",
            None,
            Some("probability"),
            Core,
            prob8_geometric_symbolic_mgf
        ),
        e!(
            "prob9-normal-symbolic-variance",
            None,
            Some("probability"),
            Core,
            prob9_normal_symbolic_variance
        ),
        e!(
            "prob10-geometric-divergent-ratio",
            None,
            Some("probability"),
            DeclineExpected,
            prob10_geometric_divergent_ratio_declines
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
        // second-pass modules: enclosure_special
        e!(
            "es1-gamma-integer",
            None,
            Some("enclosure_special"),
            Core,
            es1_gamma_integer
        ),
        e!(
            "es2-erf-one",
            None,
            Some("enclosure_special"),
            Core,
            es2_erf_one
        ),
        e!(
            "es2-erf-one-ctrl",
            None,
            Some("enclosure_special"),
            Core,
            es2_erf_one_ctrl
        ),
        e!(
            "es3-besselj0-zero",
            None,
            Some("enclosure_special"),
            Core,
            es3_besselj0_zero
        ),
        e!(
            "es4-krawczyk-circle-line",
            None,
            Some("enclosure_special"),
            Core,
            es4_krawczyk_circle_line
        ),
        // second-pass modules: fps_analytic
        e!(
            "fa1-radius-exact-geometric",
            Some("series"),
            Some("fps_analytic"),
            Core,
            fa1_radius_exact_geometric
        ),
        e!(
            "fa1-radius-exact-geometric-ctrl",
            Some("series"),
            Some("fps_analytic"),
            Core,
            fa1_radius_exact_geometric_ctrl
        ),
        e!(
            "fa2-radius-algebraic-fibonacci",
            Some("series"),
            Some("fps_analytic"),
            Core,
            fa2_radius_algebraic_fibonacci
        ),
        e!(
            "fa3-coefficient-asymptotics-geometric",
            Some("series"),
            Some("fps_analytic"),
            Core,
            fa3_coefficient_asymptotics_geometric
        ),
        // second-pass modules: numberfield_ideals
        e!(
            "nfi1-ideal-norm-principal",
            Some("number theory"),
            Some("numberfield_ideals"),
            Core,
            nfi1_ideal_norm_principal
        ),
        e!(
            "nfi2-prime-splitting-3-splits",
            Some("number theory"),
            Some("numberfield_ideals"),
            Core,
            nfi2_prime_splitting_3_splits
        ),
        e!(
            "nfi2-prime-splitting-2-ramifies-ctrl",
            Some("number theory"),
            Some("numberfield_ideals"),
            Core,
            nfi2_prime_splitting_2_ramifies_ctrl
        ),
        e!(
            "nfi3-class-number-20",
            Some("number theory"),
            Some("numberfield_ideals"),
            Core,
            nfi3_class_number_20
        ),
        // second-pass modules: permgroup_sylow
        e!(
            "sy1-s4-sylow2-order",
            None,
            Some("permgroup_sylow"),
            Core,
            sy1_s4_sylow2_order
        ),
        e!(
            "sy2-s4-sylow3-count",
            None,
            Some("permgroup_sylow"),
            Core,
            sy2_s4_sylow3_count
        ),
        e!(
            "sy3-a4-normal-in-s4",
            None,
            Some("permgroup_sylow"),
            Core,
            sy3_a4_normal_in_s4
        ),
        e!(
            "sy3-a4-normal-in-s4-ctrl",
            None,
            Some("permgroup_sylow"),
            Core,
            sy3_a4_normal_in_s4_ctrl
        ),
        // second-pass modules: homology_coefficients
        e!(
            "hc1-rp2-torsion-f2",
            None,
            Some("homology_coefficients"),
            Core,
            hc1_rp2_torsion_f2
        ),
        e!(
            "hc1-rp2-torsion-q-ctrl",
            None,
            Some("homology_coefficients"),
            Core,
            hc1_rp2_torsion_q_ctrl
        ),
        e!(
            "hc2-circle-agrees-across-rings",
            None,
            Some("homology_coefficients"),
            Core,
            hc2_circle_agrees_across_rings
        ),
        e!(
            "hc3-sphere-boundary-tetrahedron",
            None,
            Some("homology_coefficients"),
            Core,
            hc3_sphere_boundary_tetrahedron
        ),
        // second-pass modules: homology_cohomology
        e!(
            "co1-rp2-cohomology-torsion-shift",
            None,
            Some("homology_cohomology"),
            Core,
            co1_rp2_cohomology_torsion_shift
        ),
        e!(
            "co1-rp2-cohomology-torsion-not-at-h1-ctrl",
            None,
            Some("homology_cohomology"),
            Core,
            co1_rp2_cohomology_torsion_not_at_h1_ctrl
        ),
        e!(
            "co2-circle-cohomology",
            None,
            Some("homology_cohomology"),
            Core,
            co2_circle_cohomology
        ),
        e!(
            "co3-sphere-cohomology",
            None,
            Some("homology_cohomology"),
            Core,
            co3_sphere_cohomology
        ),
        // second-pass modules: homology_induced
        e!(
            "ind1-circle-identity-isomorphism",
            None,
            Some("homology_induced"),
            Core,
            ind1_circle_identity_isomorphism
        ),
        e!(
            "ind2-circle-collapse-to-edge",
            None,
            Some("homology_induced"),
            Core,
            ind2_circle_collapse_to_edge
        ),
        e!(
            "ind3-is-simplicial-rejects-missing-face",
            None,
            Some("homology_induced"),
            Core,
            ind3_is_simplicial_rejects_missing_face
        ),
        // second-pass modules: homology_persistent
        e!(
            "per1-circle-then-fill-h1-bar",
            None,
            Some("homology_persistent"),
            Core,
            per1_circle_then_fill_h1_bar
        ),
        e!(
            "per2-circle-then-fill-h0-essential",
            None,
            Some("homology_persistent"),
            Core,
            per2_circle_then_fill_h0_essential
        ),
        e!(
            "per3-prefix-before-fill-lacks-triangle",
            None,
            Some("homology_persistent"),
            Core,
            per3_prefix_before_fill_lacks_triangle
        ),
        e!(
            "per3-prefix-after-fill-has-triangle-ctrl",
            None,
            Some("homology_persistent"),
            Core,
            per3_prefix_after_fill_has_triangle_ctrl
        ),
        // second-pass modules: qe_big (indirect, through qe::eliminate/eliminate_forall)
        e!(
            "qeb1-huge-coefficient-exists",
            None,
            Some("qe_big"),
            Core,
            qeb1_huge_coefficient_exists
        ),
        e!(
            "qeb1-huge-coefficient-exists-ctrl",
            None,
            Some("qe_big"),
            Core,
            qeb1_huge_coefficient_exists_ctrl
        ),
        e!(
            "qeb2-huge-coefficient-forall",
            None,
            Some("qe_big"),
            Core,
            qeb2_huge_coefficient_forall
        ),
        e!(
            "qeb3-huge-coefficient-inequality",
            None,
            Some("qe_big"),
            Core,
            qeb3_huge_coefficient_inequality
        ),
        // second-pass modules: qe_dnf
        e!(
            "dnf1-true-via-first-disjunct",
            None,
            Some("qe_dnf"),
            Core,
            dnf1_true_via_first_disjunct
        ),
        e!(
            "dnf2-false-no-real-root",
            None,
            Some("qe_dnf"),
            Core,
            dnf2_false_no_real_root
        ),
        e!(
            "dnf3-conjunction-unsat",
            None,
            Some("qe_dnf"),
            Core,
            dnf3_conjunction_unsat
        ),
        e!(
            "dnf3-conjunction-sat-ctrl",
            None,
            Some("qe_dnf"),
            Core,
            dnf3_conjunction_sat_ctrl
        ),
        // second-pass modules: qe_bivariate
        e!(
            "bv1-circle-boundary-closed",
            None,
            Some("qe_bivariate"),
            Core,
            bv1_circle_boundary_closed
        ),
        e!(
            "bv1-exterior-tautology-ctrl",
            None,
            Some("qe_bivariate"),
            Core,
            bv1_exterior_tautology_ctrl
        ),
        e!(
            "bv2-disk-interior-open",
            None,
            Some("qe_bivariate"),
            Core,
            bv2_disk_interior_open
        ),
        e!(
            "bv3-parabola-halfline",
            None,
            Some("qe_bivariate"),
            Core,
            bv3_parabola_halfline
        ),
        // second-pass — symbolic-lambda Poisson (probability, item 9 wave two)
        e!(
            "prob4-poisson-symbolic-totalmass",
            None,
            Some("probability"),
            Core,
            prob4_poisson_symbolic_totalmass
        ),
        e!(
            "prob5-poisson-symbolic-mean",
            None,
            Some("probability"),
            Core,
            prob5_poisson_symbolic_mean
        ),
        e!(
            "prob6-poisson-symbolic-variance",
            None,
            Some("probability"),
            Core,
            prob6_poisson_symbolic_variance
        ),
        e!(
            "prob6-poisson-symbolic-variance-ctrl",
            None,
            Some("probability"),
            Core,
            prob6_poisson_symbolic_variance_ctrl
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
