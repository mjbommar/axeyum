//! Source-bound refutation certificates for single-variable integer polynomial
//! **equalities** — the `QF_NIA` `unsat` results `nia_square` decides exactly but
//! could not hand to anyone else.
//!
//! # Why this exists
//!
//! `check-capability-assurance.py` ranks `QF_NIA` in *band 2 — model replay only,
//! needs an UNSAT proof format first*, and the proof-gap matrix shows where that
//! costs: of 327 baseline UNSAT instances, **267 are marked certified**. The
//! 60-instance drop is the largest single loss in the pipeline — Lean
//! reconstruction, the stage usually blamed, costs 7 more. A logic whose `unsat`
//! carries no artifact cannot be checked by a third party at all.
//!
//! `nia_square` already decides this fragment *exactly* (not by bounded search),
//! and its arguments are small integer facts. So the artifact was available; it
//! was simply never emitted. One narrow case — degree 2, equality, negative
//! discriminant — was certified in
//! [`crate::nia_square::IntQuadraticNegativeDiscriminantCertificate`]. That
//! certificate is left exactly as it is: an autogenesis operation
//! (`smt-int-quadratic-negative-discriminant-v1`) is registered against it, and
//! redefining a shape another lane has pinned is not an upgrade. This module
//! covers the **three remaining equality refutations**, each of which was
//! previously a bare `unsat`.
//!
//! # The three arguments, and why each is checkable
//!
//! Normalize the assertion to `p(x) = 0` over one `Int` variable, with a
//! positive leading coefficient (negating both sides preserves the root set).
//!
//! 1. **`NonSquareDiscriminant`** (degree 2). `D = b² − 4ac ≥ 0`, but `D` is not
//!    a perfect square, so both roots `(−b ± √D)/2a` are irrational and no
//!    *integer* root exists.
//! 2. **`NonIntegralQuadraticRoots`** (degree 2). `D = s²` is a perfect square,
//!    so the roots are rational — but neither `(−b + s)` nor `(−b − s)` is
//!    divisible by `2a`, so neither root is an integer.
//! 3. **`RationalRootExhausted`** (degree ≥ 3). By the rational root theorem
//!    specialized to `q = 1`, every integer root of `aₙxⁿ + … + a₀` divides
//!    `a₀`. With `a₀ ≠ 0`, evaluating `p` at every divisor of `|a₀|` (both signs)
//!    and finding no zero refutes the equality outright.
//!
//! Each is a finite computation over the coefficients. Nothing about the solver
//! run needs to be trusted, and nothing from the producing arena is carried —
//! the certificate holds integers only, so it means the same thing to a reader
//! who has never seen this process.
//!
//! # The checker does not call the producer
//!
//! This matters more than the certificate's contents. The established in-tree
//! convention is `fresh == *cert`: re-run the matcher on the original assertions
//! and compare. That binds the certificate to the source — genuinely valuable,
//! and this module does it too, as step one — but a *re-execution* cannot
//! discover that the producer's reasoning is wrong, because it is the same
//! reasoning. Both would be wrong together.
//!
//! So [`check_int_univariate_refutation`] has two independent stages:
//!
//! 1. **Bind.** Re-collect the polynomial from the untouched original assertion
//!    and require the certificate's coefficients to match exactly. Guards against
//!    a certificate about a different query.
//! 2. **Re-derive.** Establish the refutation *from the coefficients alone*,
//!    by an argument written here and not shared with the producer.
//!
//! The difference is load-bearing in case 3, which is the one with somewhere for
//! a bug to hide. The producer enumerates divisors by trial division to `√|a₀|`,
//! taking each `d` **and its cofactor** `|a₀|/d` — and a completeness bug in
//! cofactor handling would silently skip candidate roots, turning a `sat` into a
//! wrong `unsat`. The checker instead scans `1..=|a₀|` directly. Slower, utterly
//! naive, and *does not share the step that could be wrong*. A missing cofactor
//! shows up as a checker rejection rather than as agreement.
//!
//! That naive scan is why `CHECKER_SCAN_BOUND` exists, and why it is a
//! deliberate narrowing rather than an oversight — see its docs.

use axeyum_ir::{TermArena, TermId};

use crate::nia_square::{Cmp, MAX_ABS_COEFF, MAX_DEGREE, Poly, match_poly_constraint};

/// Largest `|a₀|` for which a `RationalRootExhausted` certificate is issued.
///
/// The checker proves divisor-set completeness by scanning `1..=|a₀|`, so this
/// bounds *the checker's* work, not the solver's. `nia_square` still decides
/// `unsat` for `|a₀|` up to `MAX_ABS_COEFF` (`2^40`); above this bound the
/// result is simply **decided but not certified**, which is the honest state and
/// exactly the distinction the capability ledger exists to record. Trading that
/// admission for a checker that re-used the producer's `√` enumeration would
/// make the number look better and mean less.
///
/// `2^20` keeps the worst-case scan near a million `i128` remainders — under a
/// millisecond — so re-validation stays cheap enough to run on every result.
pub(crate) const CHECKER_SCAN_BOUND: i128 = 1i128 << 20;

/// Which exact argument refutes the equality. Each variant carries only what a
/// reader needs to redo the arithmetic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntUnivariateRefutationReason {
    /// Degree 2: `D = b² − 4ac ≥ 0` is not a perfect square, so both roots are
    /// irrational. `isqrt_floor` is `⌊√D⌋`, and the checker confirms
    /// `isqrt_floor² < D < (isqrt_floor + 1)²` — which *proves* no integer
    /// squares to `D`, rather than trusting any square-root routine.
    NonSquareDiscriminant {
        /// `b² − 4ac`.
        discriminant: i128,
        /// `⌊√D⌋`, bracketed by the checker.
        isqrt_floor: i128,
    },
    /// Degree 2: `D = root_sqrt²` exactly, so the roots are rational, but
    /// neither `−b + root_sqrt` nor `−b − root_sqrt` is divisible by `2a`.
    NonIntegralQuadraticRoots {
        /// `b² − 4ac`, a perfect square.
        discriminant: i128,
        /// The exact `s` with `s² = D`, `s ≥ 0`.
        root_sqrt: i128,
        /// `2a`, the denominator neither numerator divides.
        two_a: i128,
    },
    /// Degree ≥ 3: `a₀ ≠ 0` and no divisor of `|a₀|` is a root of `p`.
    RationalRootExhausted {
        /// `a₀`, whose divisors bound the integer roots.
        constant_term: i128,
        /// How many distinct integers (both signs) the checker evaluated. Not
        /// trusted — recomputed — but it makes a vacuous certificate visible.
        candidates_checked: u32,
    },
}

/// A refutation of one single-variable integer polynomial equality.
///
/// Carries integers only: no `TermId`, no `SymbolId`, nothing arena-local. A
/// certificate that named terms from the producing run would be meaningless
/// against a fresh parse of the same file — the failure
/// `crates/axeyum-solver/tests/certified_implies_revalidatable.rs` was written
/// to catch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntUnivariateRefutationCertificate {
    /// `p`'s coefficients LSB-first (`a₀, a₁, …, aₙ`), normalized to a positive
    /// leading coefficient and with trailing zeros trimmed.
    coefficients: Vec<i128>,
    /// The argument that refutes `p(x) = 0`.
    reason: IntUnivariateRefutationReason,
}

impl IntUnivariateRefutationCertificate {
    /// `p`'s coefficients, LSB-first.
    #[must_use]
    pub fn coefficients(&self) -> &[i128] {
        &self.coefficients
    }

    /// The refuting argument.
    #[must_use]
    pub const fn reason(&self) -> IntUnivariateRefutationReason {
        self.reason
    }

    /// Degree of the refuted polynomial.
    #[must_use]
    pub fn degree(&self) -> usize {
        self.coefficients.len().saturating_sub(1)
    }
}

/// Normalize a single-assertion query to `p(x) = 0` with a positive leading
/// coefficient, or decline.
fn normalized_equality(arena: &TermArena, assertions: &[TermId]) -> Option<Poly> {
    let [assertion] = assertions else {
        return None;
    };
    let (_var, Cmp::Eq, poly) = match_poly_constraint(arena, *assertion)? else {
        return None;
    };
    let degree = poly.degree();
    if degree == 0 || degree > MAX_DEGREE || !poly.coeffs_in_guard() {
        return None;
    }
    // A positive leading coefficient is a normal form, not a restriction:
    // `p(x) = 0` and `−p(x) = 0` have identical root sets.
    let poly = if poly.coeff(degree) < 0 {
        poly.neg()?
    } else {
        poly
    };
    (poly.coeff(degree) > 0).then_some(poly)
}

/// Derive a certificate for the exact source query, or decline.
///
/// Declines — soundly, always — on anything this module cannot make airtight:
/// a non-equality, more than one assertion, degree 0, a coefficient outside the
/// magnitude guard, an overflow, a constant term past `CHECKER_SCAN_BOUND`,
/// and any query that is in fact *satisfiable*.
#[must_use]
pub fn int_univariate_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<IntUnivariateRefutationCertificate> {
    let poly = normalized_equality(arena, assertions)?;
    let reason = match poly.degree() {
        2 => quadratic_reason(&poly)?,
        d if d >= 3 => rational_root_reason(&poly)?,
        // Degree 1 is exact linear arithmetic; it belongs to the LIA routes and
        // certifying it here would tread on `UnsatDiophantine`.
        _ => return None,
    };
    Some(IntUnivariateRefutationCertificate {
        coefficients: poly.coeffs.clone(),
        reason,
    })
}

/// The degree-2 argument, when one applies.
fn quadratic_reason(poly: &Poly) -> Option<IntUnivariateRefutationReason> {
    let (a, b, c) = (poly.coeff(2), poly.coeff(1), poly.coeff(0));
    debug_assert!(a > 0, "normalized to a positive leading coefficient");
    let discriminant = b
        .checked_mul(b)?
        .checked_sub(4i128.checked_mul(a)?.checked_mul(c)?)?;
    if discriminant < 0 {
        // Already certified by `IntQuadraticNegativeDiscriminantCertificate`.
        // Declining keeps one shape to one certificate rather than emitting two
        // artifacts that would have to be kept in agreement forever.
        return None;
    }
    let isqrt_floor = integer_sqrt_floor(discriminant)?;
    if isqrt_floor.checked_mul(isqrt_floor)? != discriminant {
        return Some(IntUnivariateRefutationReason::NonSquareDiscriminant {
            discriminant,
            isqrt_floor,
        });
    }
    let two_a = 2i128.checked_mul(a)?;
    let plus = (-b).checked_add(isqrt_floor)?;
    let minus = (-b).checked_sub(isqrt_floor)?;
    if plus % two_a == 0 || minus % two_a == 0 {
        return None; // an integer root exists: satisfiable, not our business
    }
    Some(IntUnivariateRefutationReason::NonIntegralQuadraticRoots {
        discriminant,
        root_sqrt: isqrt_floor,
        two_a,
    })
}

/// The degree-≥3 argument, when one applies.
fn rational_root_reason(poly: &Poly) -> Option<IntUnivariateRefutationReason> {
    let a0 = poly.coeff(0);
    if a0 == 0 {
        return None; // x = 0 is a root: satisfiable
    }
    let a0_abs = a0.checked_abs()?;
    if a0_abs >= MAX_ABS_COEFF || a0_abs > CHECKER_SCAN_BOUND {
        // Decided by `nia_square`, deliberately not certified here. See
        // `CHECKER_SCAN_BOUND`.
        return None;
    }
    let candidates = evaluate_all_divisors(poly, a0_abs)?;
    Some(IntUnivariateRefutationReason::RationalRootExhausted {
        constant_term: a0,
        candidates_checked: candidates,
    })
}

/// Evaluate `p` at every `±d` with `d | |a₀|`, `1 ≤ d ≤ |a₀|`.
///
/// Returns how many integers were evaluated, or `None` if any is a root (so the
/// query is satisfiable) or any evaluation overflows.
///
/// The scan is `1..=a0_abs` on purpose. `nia_square` reaches the same divisor
/// set in `O(√|a₀|)` by pairing each `d` with its cofactor; this repeats none of
/// that, so a cofactor-pairing bug cannot be agreed with. See the module docs.
fn evaluate_all_divisors(poly: &Poly, a0_abs: i128) -> Option<u32> {
    let mut checked: u32 = 0;
    let mut d = 1i128;
    while d <= a0_abs {
        if a0_abs % d == 0 {
            for candidate in [d, -d] {
                if poly.eval_at(candidate)? == 0 {
                    return None; // a root exists
                }
                checked = checked.checked_add(1)?;
            }
        }
        d = d.checked_add(1)?;
    }
    Some(checked)
}

/// `⌊√n⌋` for `n ≥ 0` by Newton's method, with no floating point.
///
/// Written here rather than reused from `nia_square` so that stage 2 of the
/// check shares no arithmetic with the producer.
fn integer_sqrt_floor(n: i128) -> Option<i128> {
    if n < 0 {
        return None;
    }
    if n < 2 {
        return Some(n);
    }
    let mut x = n;
    let mut y = x.checked_add(1)? / 2;
    while y < x {
        x = y;
        y = (x.checked_add(n.checked_div(x)?)?) / 2;
    }
    Some(x)
}

/// Independently re-validate a certificate against the **original** assertions.
///
/// Two stages, both required, neither delegating to the producer:
///
/// 1. the certificate's coefficients are exactly the polynomial this query
///    normalizes to;
/// 2. the carried reason genuinely refutes that polynomial, re-derived here.
#[must_use]
pub fn check_int_univariate_refutation(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &IntUnivariateRefutationCertificate,
) -> bool {
    let Some(poly) = normalized_equality(arena, assertions) else {
        return false;
    };
    if poly.coeffs != certificate.coefficients {
        return false;
    }
    reason_refutes(&poly, certificate.reason)
}

/// Stage 2: does this reason actually refute this polynomial?
fn reason_refutes(poly: &Poly, reason: IntUnivariateRefutationReason) -> bool {
    match reason {
        IntUnivariateRefutationReason::NonSquareDiscriminant {
            discriminant,
            isqrt_floor,
        } => {
            if poly.degree() != 2 {
                return false;
            }
            let Some(actual) = discriminant_of(poly) else {
                return false;
            };
            if actual != discriminant || discriminant < 0 || isqrt_floor < 0 {
                return false;
            }
            // Bracket rather than trust: `f² < D < (f+1)²` leaves no integer
            // whose square is D, which is the whole claim.
            let (Some(low), Some(high)) = (
                isqrt_floor.checked_mul(isqrt_floor),
                isqrt_floor.checked_add(1).and_then(|n| n.checked_mul(n)),
            ) else {
                return false;
            };
            low < discriminant && discriminant < high
        }
        IntUnivariateRefutationReason::NonIntegralQuadraticRoots {
            discriminant,
            root_sqrt,
            two_a,
        } => {
            if poly.degree() != 2 || root_sqrt < 0 {
                return false;
            }
            let Some(actual) = discriminant_of(poly) else {
                return false;
            };
            if actual != discriminant {
                return false;
            }
            if root_sqrt.checked_mul(root_sqrt) != Some(discriminant) {
                return false;
            }
            if 2i128.checked_mul(poly.coeff(2)) != Some(two_a) || two_a == 0 {
                return false;
            }
            let b = poly.coeff(1);
            let (Some(plus), Some(minus)) =
                ((-b).checked_add(root_sqrt), (-b).checked_sub(root_sqrt))
            else {
                return false;
            };
            // Both rational roots must fail to be integers.
            plus % two_a != 0 && minus % two_a != 0
        }
        IntUnivariateRefutationReason::RationalRootExhausted {
            constant_term,
            candidates_checked,
        } => {
            if poly.degree() < 3 || constant_term == 0 {
                return false;
            }
            if poly.coeff(0) != constant_term {
                return false;
            }
            let Some(a0_abs) = constant_term.checked_abs() else {
                return false;
            };
            if a0_abs > CHECKER_SCAN_BOUND {
                return false;
            }
            // The independent enumeration. Also re-derives the count, so a
            // certificate claiming a scan it did not do is rejected.
            evaluate_all_divisors(poly, a0_abs) == Some(candidates_checked)
        }
    }
}

fn discriminant_of(poly: &Poly) -> Option<i128> {
    let (a, b, c) = (poly.coeff(2), poly.coeff(1), poly.coeff(0));
    b.checked_mul(b)?
        .checked_sub(4i128.checked_mul(a)?.checked_mul(c)?)
}

#[cfg(test)]
mod tests {
    //! White-box adversarial tests: **the checker must reject a forged reason.**
    //!
    //! These live here rather than in `tests/` because forging a certificate
    //! needs field access, and exposing a public constructor purely so an
    //! integration test could build a wrong certificate would put a
    //! footgun in the API to test a guard. The black-box half — production,
    //! re-validation on a fresh arena, non-vacuity, and source binding — is
    //! `crates/axeyum-solver/tests/nia_univariate_cert.rs`.
    //!
    //! Each guard is asserted separately. A single "some tampering is rejected"
    //! test would pass while all but one guard were deleted.

    use super::*;
    use axeyum_ir::Sort;

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

    /// `(arena, assertions, honest certificate)` for `p(x) = 0`.
    fn setup(coeffs: &[i128]) -> (TermArena, Vec<TermId>, IntUnivariateRefutationCertificate) {
        let mut arena = TermArena::new();
        let assertion = poly_eq_zero(&mut arena, coeffs);
        let assertions = vec![assertion];
        let cert = int_univariate_refutation(&arena, &assertions)
            .unwrap_or_else(|| panic!("expected a certificate for {coeffs:?}"));
        assert!(
            check_int_univariate_refutation(&arena, &assertions, &cert),
            "the honest certificate for {coeffs:?} must verify"
        );
        (arena, assertions, cert)
    }

    /// Swap the reason, keep the coefficients: isolates stage 2 of the check.
    fn with_reason(
        cert: &IntUnivariateRefutationCertificate,
        reason: IntUnivariateRefutationReason,
    ) -> IntUnivariateRefutationCertificate {
        IntUnivariateRefutationCertificate {
            coefficients: cert.coefficients.clone(),
            reason,
        }
    }

    // `x² + x − 1 = 0`, D = 5.
    const NON_SQUARE: &[i128] = &[-1, 1, 1];
    // `4x² − 1 = 0`, D = 16, roots ±1/2.
    const NON_INTEGRAL: &[i128] = &[-1, 0, 4];
    // `x³ + x + 1 = 0`, a₀ = 1.
    const EXHAUSTED: &[i128] = &[1, 1, 0, 1];

    #[test]
    fn a_discriminant_that_is_not_b2_minus_4ac_is_rejected() {
        let (arena, assertions, cert) = setup(NON_SQUARE);
        let forged = with_reason(
            &cert,
            IntUnivariateRefutationReason::NonSquareDiscriminant {
                discriminant: 4,
                isqrt_floor: 2,
            },
        );
        assert!(!check_int_univariate_refutation(
            &arena,
            &assertions,
            &forged
        ));
    }

    #[test]
    fn a_bracket_that_does_not_exclude_an_integer_square_root_is_rejected() {
        // D = 5 with ⌊√D⌋ claimed as 1: the upper bound 1 < 5 < 4 is false, so
        // the certificate does not establish that 5 is a non-square. This is the
        // guard that makes `isqrt_floor` proof rather than decoration.
        let (arena, assertions, cert) = setup(NON_SQUARE);
        for bad in [0i128, 1, 3] {
            let forged = with_reason(
                &cert,
                IntUnivariateRefutationReason::NonSquareDiscriminant {
                    discriminant: 5,
                    isqrt_floor: bad,
                },
            );
            assert!(
                !check_int_univariate_refutation(&arena, &assertions, &forged),
                "isqrt_floor = {bad} was accepted for D = 5"
            );
        }
    }

    #[test]
    fn a_root_sqrt_that_does_not_square_to_the_discriminant_is_rejected() {
        let (arena, assertions, cert) = setup(NON_INTEGRAL);
        let forged = with_reason(
            &cert,
            IntUnivariateRefutationReason::NonIntegralQuadraticRoots {
                discriminant: 16,
                root_sqrt: 3,
                two_a: 8,
            },
        );
        assert!(!check_int_univariate_refutation(
            &arena,
            &assertions,
            &forged
        ));
    }

    #[test]
    fn a_denominator_that_is_not_twice_the_leading_coefficient_is_rejected() {
        // With two_a = 2 the numerator −b + s = 4 IS divisible, so accepting
        // this would mean accepting a refutation of a root that exists.
        let (arena, assertions, cert) = setup(NON_INTEGRAL);
        for bad in [2i128, 4, -8, 0] {
            let forged = with_reason(
                &cert,
                IntUnivariateRefutationReason::NonIntegralQuadraticRoots {
                    discriminant: 16,
                    root_sqrt: 4,
                    two_a: bad,
                },
            );
            assert!(
                !check_int_univariate_refutation(&arena, &assertions, &forged),
                "two_a = {bad} was accepted where 2a = 8"
            );
        }
    }

    #[test]
    fn a_constant_term_that_is_not_a0_is_rejected() {
        let (arena, assertions, cert) = setup(EXHAUSTED);
        let forged = with_reason(
            &cert,
            IntUnivariateRefutationReason::RationalRootExhausted {
                constant_term: 7,
                candidates_checked: 2,
            },
        );
        assert!(!check_int_univariate_refutation(
            &arena,
            &assertions,
            &forged
        ));
    }

    #[test]
    fn a_candidate_count_the_divisor_set_does_not_support_is_rejected() {
        // The checker re-derives the count from its own enumeration, so a
        // certificate claiming a scan it did not do is rejected in both
        // directions — inflated (looks thorough) and deflated (skipped work).
        let (arena, assertions, cert) = setup(EXHAUSTED);
        for bad in [0u32, 1, 3, 99] {
            let forged = with_reason(
                &cert,
                IntUnivariateRefutationReason::RationalRootExhausted {
                    constant_term: 1,
                    candidates_checked: bad,
                },
            );
            assert!(
                !check_int_univariate_refutation(&arena, &assertions, &forged),
                "candidates_checked = {bad} was accepted where the divisor set gives 2"
            );
        }
    }

    #[test]
    fn a_reason_borrowed_from_the_wrong_degree_is_rejected() {
        // A cubic's first three coefficients form a well-typed discriminant that
        // means nothing. Without the per-branch degree guard this would be
        // arithmetic that checks out and proves the wrong thing.
        let (arena, assertions, cert) = setup(EXHAUSTED);
        let quadratic_on_a_cubic = with_reason(
            &cert,
            IntUnivariateRefutationReason::NonSquareDiscriminant {
                discriminant: 1,
                isqrt_floor: 1,
            },
        );
        assert!(!check_int_univariate_refutation(
            &arena,
            &assertions,
            &quadratic_on_a_cubic
        ));

        let (q_arena, q_assertions, q_cert) = setup(NON_SQUARE);
        let cubic_on_a_quadratic = with_reason(
            &q_cert,
            IntUnivariateRefutationReason::RationalRootExhausted {
                constant_term: -1,
                candidates_checked: 2,
            },
        );
        assert!(!check_int_univariate_refutation(
            &q_arena,
            &q_assertions,
            &cubic_on_a_quadratic
        ));
    }

    /// Build a certificate from nothing. Needed for the four guards below,
    /// each of which can only be isolated by a certificate the producer would
    /// never emit — for a *satisfiable* query, or with reason data that every
    /// other guard happens to accept.
    fn forge(
        coeffs: &[i128],
        reason: IntUnivariateRefutationReason,
    ) -> IntUnivariateRefutationCertificate {
        IntUnivariateRefutationCertificate {
            coefficients: coeffs.to_vec(),
            reason,
        }
    }

    fn query(coeffs: &[i128]) -> (TermArena, Vec<TermId>) {
        let mut arena = TermArena::new();
        let assertion = poly_eq_zero(&mut arena, coeffs);
        (arena, vec![assertion])
    }

    // ---- the four guards that overlapping tests could not isolate ---------
    //
    // Mutation testing found these: deleting each of the four killed NOTHING,
    // because another guard rejected the same forgery first. That is the
    // "six of seven guards were removable while green" failure, and the fix is
    // a certificate crafted so exactly one guard stands between it and
    // acceptance.

    #[test]
    fn accepting_a_non_integral_claim_over_an_actual_root_is_rejected() {
        // `x² − 4 = 0` is SATISFIABLE at x = 2. D = 16 = 4², 2a = 2 — so the
        // discriminant, the square root and the denominator all check out, and
        // only the divisibility test stands between this forgery and a wrong
        // `unsat`: −b + s = 4 IS divisible by 2.
        let (arena, assertions) = query(&[-4, 0, 1]);
        let forged = forge(
            &[-4, 0, 1],
            IntUnivariateRefutationReason::NonIntegralQuadraticRoots {
                discriminant: 16,
                root_sqrt: 4,
                two_a: 2,
            },
        );
        assert!(
            !check_int_univariate_refutation(&arena, &assertions, &forged),
            "a refutation was accepted for a polynomial with the integer root 2"
        );
    }

    #[test]
    fn a_constant_term_of_the_right_magnitude_but_the_wrong_sign_is_rejected() {
        // `x³ + x + 1 = 0` has a₀ = 1. Claiming a₀ = −1 keeps |a₀| = 1, so the
        // divisor set and the recomputed candidate count are IDENTICAL and the
        // count guard passes. Only the equality against the real a₀ catches it.
        let (arena, assertions) = query(&[1, 1, 0, 1]);
        let forged = forge(
            &[1, 1, 0, 1],
            IntUnivariateRefutationReason::RationalRootExhausted {
                constant_term: -1,
                candidates_checked: 2,
            },
        );
        assert!(
            !check_int_univariate_refutation(&arena, &assertions, &forged),
            "a constant term with the right magnitude and the wrong sign was accepted"
        );
    }

    #[test]
    fn a_certificate_for_a_different_polynomial_with_the_same_reason_is_rejected() {
        // `x³ + x + 1` and `x³ + x² + 1` are both unsat with IDENTICAL reason
        // data (a₀ = 1, two candidates checked). Every stage-2 guard therefore
        // accepts the other's certificate, and only the stage-1 coefficient
        // binding distinguishes them. Swapping certificates between two queries
        // with different reasons proves nothing about the binding.
        let a = [1i128, 1, 0, 1];
        let b = [1i128, 0, 1, 1];
        let (arena_a, assertions_a) = query(&a);
        let (arena_b, assertions_b) = query(&b);
        let cert_a = int_univariate_refutation(&arena_a, &assertions_a).expect("a is unsat");
        let cert_b = int_univariate_refutation(&arena_b, &assertions_b).expect("b is unsat");
        assert_eq!(
            cert_a.reason, cert_b.reason,
            "the fixtures must share a reason or this test does not isolate the binding"
        );
        assert_ne!(cert_a.coefficients, cert_b.coefficients);
        assert!(
            !check_int_univariate_refutation(&arena_b, &assertions_b, &cert_a),
            "a certificate for x^3+x+1 was accepted against x^3+x^2+1"
        );
        assert!(
            !check_int_univariate_refutation(&arena_a, &assertions_a, &cert_b),
            "a certificate for x^3+x^2+1 was accepted against x^3+x+1"
        );
    }

    #[test]
    fn a_quadratic_argument_over_a_satisfiable_cubic_is_rejected() {
        // `x³ + x² + x − 3 = 0` is SATISFIABLE at x = 1. Reading its first three
        // coefficients as a quadratic gives b² − 4ac = 1 + 12 = 13, a genuine
        // non-square with ⌊√13⌋ = 3 and 9 < 13 < 16 — so the discriminant, the
        // bracket and every other stage-2 guard PASS. Only the degree guard
        // prevents this from certifying a satisfiable query as unsat.
        let (arena, assertions) = query(&[-3, 1, 1, 1]);
        let forged = forge(
            &[-3, 1, 1, 1],
            IntUnivariateRefutationReason::NonSquareDiscriminant {
                discriminant: 13,
                isqrt_floor: 3,
            },
        );
        assert!(
            !check_int_univariate_refutation(&arena, &assertions, &forged),
            "a degree-2 argument certified a satisfiable cubic as unsat"
        );
    }

    #[test]
    fn the_independent_scan_finds_a_root_the_producer_would_have_to_find() {
        // `x³ − 1 = 0` has the root 1, a divisor of |a₀|. The checker's own
        // enumeration must see it, so no certificate exists. This is the control
        // for `evaluate_all_divisors`: if it silently skipped candidates it
        // would happily certify a satisfiable query.
        let mut arena = TermArena::new();
        let assertion = poly_eq_zero(&mut arena, &[-1, 0, 0, 1]);
        assert!(int_univariate_refutation(&arena, &[assertion]).is_none());
    }

    #[test]
    fn integer_sqrt_floor_is_exact_across_the_boundaries() {
        // The bracket argument is only as good as this function at n = k² and
        // n = k² − 1, where an off-by-one turns a non-square into a square.
        for k in 0i128..200 {
            let square = k * k;
            assert_eq!(integer_sqrt_floor(square), Some(k), "n = {square}");
            if k > 0 {
                assert_eq!(
                    integer_sqrt_floor(square - 1),
                    Some(k - 1),
                    "n = {}",
                    square - 1
                );
                assert_eq!(
                    integer_sqrt_floor(square + 1),
                    Some(k),
                    "n = {}",
                    square + 1
                );
            }
        }
        assert_eq!(integer_sqrt_floor(-1), None);
    }
}
