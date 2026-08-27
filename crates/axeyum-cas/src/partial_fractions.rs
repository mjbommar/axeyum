//! Certified PARTIAL-FRACTION DECOMPOSITION (Spivak ch. 19): the algebraic
//! engine behind rational-function integration (`∫ dx/(x²−1)` is elementary
//! precisely because `1/(x²−1)` splits into `(1/2)/(x−1) − (1/2)/(x+1)`).
//!
//! Unlike [`crate::mvt`], [`crate::taylor`], and [`crate::extremum`], this
//! fragment carries **no analytic content at all** — no Rolle's theorem, no
//! completeness, nothing Richardson's theorem could make undecidable. Given
//! `p(x)/q(x)` and a factorization of `q` into irreducibles over ℚ, the
//! decomposition is a single **linear** algebraic identity: match
//! coefficients, solve one square system of exact-rational equations. Every
//! step here is decidable and exact; the only limits are the same
//! computational bounds the reused machinery already carries (see "Scope and
//! bounds" below).
//!
//! ## What already existed and is reused here, unchanged
//!
//! - [`crate::factor_univariate_over_q`] — full Berlekamp–Zassenhaus
//!   factorization over ℚ into irreducibles **with multiplicities**. This is
//!   the piece that turns what could have been "rungs 1–2 landed, 3–4
//!   characterised" into all four rungs landed directly: distinct linear
//!   factors, repeated linear factors, irreducible quadratics (and higher),
//!   and the fully general case are all one code path, because the
//!   factorizer does not stop at square-free decomposition — it goes all the
//!   way to irreducibles.
//! - `crate::ratint::solve_linear` — the exact-rational Gauss–Jordan solver
//!   [`crate::ratint::horowitz`] already uses for its own undetermined-
//!   coefficients system (rational integration's `B`/`C` unknowns). The
//!   column-per-unknown, row-per-coefficient construction here is the same
//!   shape, applied to the classical partial-fraction unknowns instead.
//! - `crate::ratint::divrem` — exact polynomial division with remainder, used
//!   once, up front, to split off a polynomial part when `deg p ≥ deg q`
//!   (Spivak's `p/q` is stated for a proper fraction; this module accepts an
//!   improper one too and reduces it to the proper case before doing
//!   anything else).
//!
//! Nothing above was copied; both are reached via `crate::ratint::{..}`
//! (`pub(crate)`, visible crate-wide from the module they are declared in —
//! see the multi-agent hygiene notes on `pub(crate)` reach) and
//! [`crate::factor_univariate_over_q`] via its existing `pub use` re-export.
//!
//! ## The construction
//!
//! 1. `(whole, r) = divrem(p, q)`, so `p = whole·q + r` with `deg r < deg q`.
//! 2. `factors = factor_univariate_over_q(q)`: pairs `(fᵢ, eᵢ)`, irreducible
//!    `fᵢ` (primitive, positive leading coefficient) with multiplicity `eᵢ`.
//! 3. Recover the scalar `leading` with `q = leading · ∏ᵢ fᵢ^eᵢ` by comparing
//!    leading coefficients (the factorizer's own documented contract), then
//!    confirm the product **exactly** reproduces `q` — a defensive re-check
//!    the producer performs on itself, mirroring [`crate::factor_int`]'s own
//!    "the answer is cheaply certified by re-multiplying" stance.
//! 4. For every `(fᵢ, eᵢ)` and every power `j = 1, …, eᵢ`, an unknown
//!    numerator `Nᵢⱼ` of degree `< deg fᵢ` contributes
//!    `Nᵢⱼ(x) · ∏_{k≠i} fₖ^{eₖ} · fᵢ^{eᵢ−j}` to `leading⁻¹ · r` once cleared of
//!    denominators — exactly `leading · Nᵢⱼ(x) · (that cofactor)` contributing
//!    to `r`. The total number of unknown coefficients is `Σᵢ eᵢ·deg(fᵢ) =
//!    deg(q)`, matching the number of coefficient-matching equations exactly
//!    (this is the textbook uniqueness argument for partial fractions,
//!    surfacing here as "the linear system is square"), so
//!    `crate::ratint::solve_linear` either returns the unique solution or the
//!    system is genuinely singular (which should not happen for a correct
//!    factorization, and is reported as an honest decline, never a wrong
//!    answer).
//! 5. The certificate carries only `p`, `q`, `whole`, `leading`, and the
//!    resulting `(factor, power, numerator)` terms — not the intermediate
//!    cofactor polynomials or the linear system itself, which are producer-
//!    side search machinery [`verify_partial_fraction_certificate`] never
//!    needs (same "certificate is data, not a trace of the search" split as
//!    every sibling module in this ladder).
//!
//! ## What the checker independently re-derives
//!
//! [`verify_partial_fraction_certificate`] never calls
//! [`crate::factor_univariate_over_q`] or `crate::ratint::solve_linear` — it
//! re-derives everything from the certificate's own data:
//!
//! 1. Non-constant `q` (`deg q ≥ 1`), `leading` nonzero, `terms` nonempty.
//! 2. **Structural well-formedness**: every group's `factor` is non-constant
//!    (`deg ≥ 1`), and grouping `terms` by their stated `factor`, the
//!    `power`s present in each group must be **exactly** `{1, …, m}` for that
//!    group's size `m` — no gaps, no duplicates. The power-set half is the
//!    guard that makes a mislabeled multiplicity a structural rejection
//!    rather than a numeric coincidence (see
//!    `wrong_multiplicity_is_vacuous_without_the_power_set_guard`, below,
//!    which is deliberately built so the value identity alone — checks 4 and
//!    5 — passes anyway); the non-constant half catches a spurious constant
//!    "factor" with a zero numerator, smuggled in to absorb into `leading`
//!    (`spurious_constant_factor_with_zero_numerator_is_rejected`).
//! 3. **Degree bound**: every numerator's degree is strictly below its
//!    factor's — without this, a decomposition is not unique (`N/(x−1) ==
//!    (N + k·(x−1))/(x−1) − k` for any `k`, absorbed into `whole`), so a
//!    dedicated fixture bumps one numerator's degree and compensates exactly
//!    in `whole` (`over_degree_numerator_compensated_by_whole_is_rejected`).
//! 4. **Pairwise coprimality** of distinct factor groups (`gcd` has degree
//!    0). This is the cheap, standard necessary condition for a genuine
//!    irreducible-factor decomposition, and it is what catches a repeated
//!    root disguised as two separate proportional "factors" —
//!    `disguised_repeated_root_via_proportional_factors_is_rejected`, below.
//! 5. **Reconstruct `q`** as `leading · ∏ factorᵢ^{mᵢ}` (`mᵢ` = that group's
//!    size) and compare **exactly** to the stored `q`
//!    (`mismatched_q_is_rejected`).
//! 6. **Reconstruct `p`** as `whole·q + leading·Σ` (numerator × cofactor) and
//!    compare **exactly** to the stored `p`
//!    (`perturbed_coefficient_is_rejected`).
//!
//! `Some(true)` only if every one of these holds; `Some(false)` the moment
//! any one fails; `None` only on arithmetic overflow — never a false accept.
//!
//! **Mutation testing** (deleting each guard in turn and confirming exactly
//! which test dies) found that check 1's three individual guards (`deg q ≥
//! 1`, `leading` nonzero, `terms` nonempty) are **structurally subsumed** by
//! check 5 given check 2's non-constant-factor half: with `terms` nonempty
//! and every factor non-constant, the reconstructed `∏ factorᵢ^{mᵢ}` always
//! has degree `≥ 1`, so a constant or zero `q`, or a `leading` of zero, can
//! never reconstruct a genuinely non-constant `q` regardless of what those
//! three guards do. No fixture kills any of the three in isolation — this
//! was verified, not assumed, and is recorded here rather than left as
//! silent decoration. They are kept anyway (cheap, and a clearer failure
//! shape than a coincidental reconstruction mismatch would be), but the
//! checker's soundness does not rest on them.
//!
//! ## Scope and bounds — and the one thing NOT independently re-derived
//!
//! This fragment has no Richardson-theorem-shaped boundary; everything is
//! finite exact arithmetic. The bounds that exist are inherited wholesale
//! from the machinery being reused, not new to this module:
//!
//! - **Degree**: [`crate::factor_univariate_over_q`] declines above degree 32
//!   (worst-case-exponential recombination search), so `partial_fractions`
//!   inherits the same cap.
//! - **Linear-system size**: `crate::ratint::solve_linear` tries a fast
//!   `i128` path first and falls back to exact big-rational Gauss–Jordan only
//!   up to dimension 16; a `deg(q)` between 17 and 32 that overflows `i128`
//!   partway through the fast path can decline even though the degree cap
//!   above would otherwise allow it. Still never a wrong answer — an honest
//!   `None`.
//!
//! One thing is genuinely **not** independently re-derived, by deliberate
//! choice matching an existing precedent in this crate:
//! **[`verify_partial_fraction_certificate`] does not reprove that each
//! stated factor is irreducible over ℚ.** It confirms the factors are
//! pairwise coprime (item 3 above) and that they reconstruct `q` and `p`
//! exactly, but a certificate whose "factors" are, say, one non-coprime
//! *reducible* factor could in principle be built by hand (not by
//! [`partial_fractions`], which only ever emits factors from
//! [`crate::factor_univariate_over_q`]) and would still be **accepted** if
//! its coprimality and reconstruction hold. This mirrors
//! [`crate::factor_int::factor_expr`]'s own documented certification scope:
//! that function also certifies its factorization only by re-multiplying and
//! checking equality, never by independently reproving irreducibility of
//! each factor. Re-proving irreducibility from nothing would mean
//! re-implementing (or re-deriving a certificate format for) the
//! Berlekamp–Zassenhaus recombination step itself — a second, independent
//! irreducibility-testing algorithm, which is out of scope here. What *is*
//! certified is strictly stronger than a bare identity check (coprimality
//! rules out the most obvious way to cheat: splitting one repeated
//! irreducible factor into several proportional copies of itself, or into
//! two coprime-looking-but-not pieces of one real factor).

use axeyum_ir::{Rational, poly};

use crate::factor_univariate_over_q;
use crate::ratint::{divrem, solve_linear};

/// One term `numerator(x) / factor(x)^power` of a partial-fraction
/// decomposition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialFractionTerm {
    /// The irreducible (over ℚ) factor `factor` of `q`, LSB-first, of degree
    /// at least one. Several terms in one certificate may share the same
    /// `factor` (one per power, for a repeated factor).
    pub factor: Vec<Rational>,
    /// The power `j` of `factor` this term's denominator is `factor^j`.
    /// `1`-indexed: for a factor with multiplicity `e`, exactly the powers
    /// `1, …, e` must appear, each exactly once.
    pub power: u32,
    /// The numerator `N(x)`, with `deg(N) < deg(factor)`, LSB-first.
    pub numerator: Vec<Rational>,
}

/// A checkable certificate for the partial-fraction decomposition of
/// `p(x)/q(x)`: `p = whole·q + leading·Σ (numerator × cofactor)` over
/// `terms`, checked exactly by [`verify_partial_fraction_certificate`]. See
/// the module doc for the full construction and what the checker
/// independently re-derives.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialFractionCertificate {
    /// The original numerator, LSB-first, trimmed.
    pub p: Vec<Rational>,
    /// The original denominator, LSB-first, trimmed, degree ≥ 1.
    pub q: Vec<Rational>,
    /// The polynomial part of `p/q` (`q(x)·whole(x)` is `p`'s non-proper
    /// part); empty (the zero polynomial) when `deg p < deg q` already.
    pub whole: Vec<Rational>,
    /// The scalar with `q = leading · ∏ᵢ factorᵢ^{multiplicityᵢ}`.
    pub leading: Rational,
    /// The decomposition's terms, one per `(factor, power)` pair.
    pub terms: Vec<PartialFractionTerm>,
}

/// `x^k` as a dense LSB-first polynomial of length `k + 1`.
fn monomial(k: usize) -> Vec<Rational> {
    let mut v = vec![Rational::zero(); k + 1];
    v[k] = Rational::integer(1);
    v
}

/// `base^exp` by repeated polynomial multiplication (`exp` is always small
/// here — a factor multiplicity). `exp == 0` gives the constant `1`. `None`
/// on overflow.
fn poly_pow(base: &[Rational], exp: u32) -> Option<Vec<Rational>> {
    let mut acc = vec![Rational::integer(1)];
    for _ in 0..exp {
        acc = poly::ratpoly_mul(&acc, base)?;
    }
    Some(acc)
}

/// Multiply every coefficient of `p` by `scalar`. `None` on overflow.
fn scale_poly(p: &[Rational], scalar: Rational) -> Option<Vec<Rational>> {
    p.iter().map(|&c| c.checked_mul(scalar)).collect()
}

/// `∏ᵢ factorsᵢ.0 ^ factorsᵢ.1`, skipping index `skip` (pass `factors.len()`
/// to skip nothing, i.e. the full product). `None` on overflow.
fn product_excluding(factors: &[(Vec<Rational>, u32)], skip: usize) -> Option<Vec<Rational>> {
    let mut acc = vec![Rational::integer(1)];
    for (idx, (factor, mult)) in factors.iter().enumerate() {
        if idx == skip {
            continue;
        }
        acc = poly::ratpoly_mul(&acc, &poly_pow(factor, *mult)?)?;
    }
    Some(acc)
}

/// Produce a certified partial-fraction decomposition of `p(x)/q(x)`.
///
/// `q` must be non-constant (`deg q ≥ 1`); it is fully factored over the
/// rationals into irreducibles via [`crate::factor_univariate_over_q`]
/// (Berlekamp–Zassenhaus), so distinct linear factors, repeated linear
/// factors, irreducible quadratics, and the fully general case are all the
/// same code path. `p` may have any degree — if `deg p ≥ deg q` the
/// polynomial quotient is split off first (`crate::ratint::divrem`) so the
/// fractional part handed to the linear system is always proper.
///
/// Returns `None` if `q` is the zero or a constant polynomial, if the
/// factorization declines (see the module doc's "Scope and bounds"), or if
/// the resulting linear system is singular or overflows — never a wrong
/// decomposition.
#[must_use]
pub fn partial_fractions(p: &[Rational], q: &[Rational]) -> Option<PartialFractionCertificate> {
    let p = poly::rat_trim(p.to_vec());
    let q = poly::rat_trim(q.to_vec());
    let deg_q = poly::rat_degree(&q)?; // None for the zero polynomial
    if deg_q == 0 {
        return None; // constant denominator: nothing to decompose
    }

    let (whole, remainder) = divrem(&p, &q)?;

    let mut factors = factor_univariate_over_q(&q)?;
    if factors.is_empty() {
        return None; // unreachable for deg_q >= 1, but decline rather than assume
    }
    // Deterministic order, mirroring factor_univariate_over_q's own sort.
    factors.sort_by(|left, right| {
        left.0
            .len()
            .cmp(&right.0.len())
            .then_with(|| left.0.cmp(&right.0))
    });

    let reconstructed = product_excluding(&factors, factors.len())?;
    let lead_q = *q.last()?;
    let lead_reconstructed = *reconstructed.last()?;
    if lead_reconstructed.is_zero() {
        return None;
    }
    let leading = lead_q.checked_div(lead_reconstructed)?;
    let scaled = poly::rat_trim(scale_poly(&reconstructed, leading)?);
    if scaled != q {
        return None; // defensive: the factorization must reproduce q exactly
    }

    let mut cols: Vec<Vec<Rational>> = Vec::with_capacity(deg_q);
    for (i, (factor, mult)) in factors.iter().enumerate() {
        let deg_f = poly::rat_degree(factor)?;
        let cofactor = product_excluding(&factors, i)?;
        for power in 1..=*mult {
            let remaining = poly_pow(factor, mult - power)?;
            let complement = scale_poly(&poly::ratpoly_mul(&cofactor, &remaining)?, leading)?;
            for m in 0..deg_f {
                cols.push(poly::ratpoly_mul(&monomial(m), &complement)?);
            }
        }
    }
    if cols.len() != deg_q {
        return None; // should be impossible: Sigma mult*deg(factor) == deg(q)
    }

    let mut rhs = remainder;
    rhs.resize(deg_q, Rational::zero());
    let solution = solve_linear(&cols, &rhs)?;

    let mut terms = Vec::with_capacity(deg_q);
    let mut idx = 0usize;
    for (factor, mult) in &factors {
        let deg_f = poly::rat_degree(factor)?;
        for power in 1..=*mult {
            let coeffs = solution.get(idx..idx + deg_f)?.to_vec();
            idx += deg_f;
            terms.push(PartialFractionTerm {
                factor: factor.clone(),
                power,
                numerator: poly::rat_trim(coeffs),
            });
        }
    }

    Some(PartialFractionCertificate {
        p,
        q,
        whole,
        leading,
        terms,
    })
}

/// Independently re-derive and check a [`PartialFractionCertificate`]. See
/// the module doc's "What the checker independently re-derives" for the full
/// list of five checks; `Some(true)` only if every one holds, `Some(false)`
/// the moment any one fails, `None` only on arithmetic overflow.
#[must_use]
pub fn verify_partial_fraction_certificate(cert: &PartialFractionCertificate) -> Option<bool> {
    let PartialFractionCertificate {
        p,
        q,
        whole,
        leading,
        terms,
    } = cert;

    let q = poly::rat_trim(q.clone());
    let p = poly::rat_trim(p.clone());
    match poly::rat_degree(&q) {
        Some(d) if d >= 1 => {}
        _ => return Some(false),
    }
    if leading.is_zero() {
        return Some(false);
    }
    if terms.is_empty() {
        return Some(false);
    }

    // Group terms by their stated factor, preserving first-seen order.
    let mut groups: Vec<(Vec<Rational>, Vec<u32>)> = Vec::new();
    for term in terms {
        if poly::rat_trim(term.factor.clone()) != term.factor {
            return Some(false); // factor must already be given trimmed
        }
        match groups.iter_mut().find(|(f, _)| *f == term.factor) {
            Some((_, powers)) => powers.push(term.power),
            None => groups.push((term.factor.clone(), vec![term.power])),
        }
    }

    // Guard: every group's factor is non-constant, and its powers are
    // EXACTLY {1, ..., group size} -- no gap, no duplicate.
    for (factor, powers) in &groups {
        let Some(deg_f) = poly::rat_degree(factor) else {
            return Some(false);
        };
        if deg_f == 0 {
            return Some(false);
        }
        let mut sorted_powers = powers.clone();
        sorted_powers.sort_unstable();
        let Ok(group_len) = u32::try_from(powers.len()) else {
            return Some(false);
        };
        let expected: Vec<u32> = (1..=group_len).collect();
        if sorted_powers != expected {
            return Some(false);
        }
    }

    // Guard: every numerator's degree is strictly below its factor's.
    for term in terms {
        let Some(deg_f) = poly::rat_degree(&term.factor) else {
            return Some(false);
        };
        let numerator = poly::rat_trim(term.numerator.clone());
        if numerator.len() > deg_f {
            return Some(false);
        }
    }

    // Guard: distinct factor groups are pairwise coprime.
    let gcd_bound = q.len().saturating_add(4);
    for i in 0..groups.len() {
        for j in (i + 1)..groups.len() {
            let gcd = poly::rat_gcd(&groups[i].0, &groups[j].0, gcd_bound)?;
            if poly::rat_degree(&gcd) != Some(0) {
                return Some(false);
            }
        }
    }

    // Reconstruct q from the grouped factors and compare exactly.
    let factors_with_mult: Vec<(Vec<Rational>, u32)> = groups
        .iter()
        .map(|(f, powers)| {
            u32::try_from(powers.len())
                .ok()
                .map(|m| (f.clone(), m))
                .unwrap_or((f.clone(), 0))
        })
        .collect();
    let product = product_excluding(&factors_with_mult, factors_with_mult.len())?;
    let scaled_product = poly::rat_trim(scale_poly(&product, *leading)?);
    if scaled_product != q {
        return Some(false);
    }

    // Reconstruct p = whole*q + leading * Sigma(numerator * cofactor) exactly.
    let whole_times_q = poly::ratpoly_mul(whole, &q)?;
    let mut cleared_sum = Vec::new();
    for (i, (factor, mult)) in factors_with_mult.iter().enumerate() {
        let cofactor = product_excluding(&factors_with_mult, i)?;
        for term in terms.iter().filter(|t| t.factor == *factor) {
            let remaining_power = mult.checked_sub(term.power)?;
            let remaining = poly_pow(factor, remaining_power)?;
            let complement = poly::ratpoly_mul(&cofactor, &remaining)?;
            let contribution = poly::ratpoly_mul(&term.numerator, &complement)?;
            cleared_sum = poly::ratpoly_add(&cleared_sum, &contribution)?;
        }
    }
    let scaled_sum = scale_poly(&cleared_sum, *leading)?;
    let reconstructed_p = poly::rat_trim(poly::ratpoly_add(&whole_times_q, &scaled_sum)?);
    if reconstructed_p != p {
        return Some(false);
    }

    Some(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn poly_from(coeffs: &[i128]) -> Vec<Rational> {
        coeffs.iter().map(|&c| Rational::integer(c)).collect()
    }

    fn rat(num: i128, den: i128) -> Rational {
        Rational::checked_new(num, den).unwrap()
    }

    /// The sum, over every term, of `numerator(x)/factor(x)^power` cleared of
    /// denominators against a fresh cofactor computation -- an independent
    /// evaluation-based cross-check used only inside tests (never inside the
    /// checker itself), by evaluating both sides of `p(x)/q(x) == Sigma` at a
    /// handful of rational points not roots of `q`.
    fn eval_ratio(poly: &[Rational], x: Rational) -> Rational {
        poly::eval_rat_poly(poly, x).unwrap()
    }

    fn decomposition_value_at(cert: &PartialFractionCertificate, x: Rational) -> Rational {
        // p/q = whole + Sigma(N_i/f_i^power_i), with NO further `leading`
        // factor: `leading` only relates q to the unscaled product
        // F = prod(factor_i^mult_i) (q = leading*F), and that `leading`
        // cancels exactly against the `leading` the checker/producer apply
        // when clearing denominators against q rather than F.
        let whole_val = eval_ratio(&cert.whole, x);
        let mut sum = Rational::zero();
        for term in &cert.terms {
            let fx = eval_ratio(&term.factor, x);
            let mut denom = Rational::integer(1);
            for _ in 0..term.power {
                denom = denom.checked_mul(fx).unwrap();
            }
            let nx = eval_ratio(&term.numerator, x);
            sum = sum.checked_add(nx.checked_div(denom).unwrap()).unwrap();
        }
        whole_val.checked_add(sum).unwrap()
    }

    // ---- rung 1: distinct linear factors ----

    #[test]
    fn distinct_linear_factors() {
        // 1 / ((x-1)(x+1)) = (1/2)/(x-1) - (1/2)/(x+1).
        let p = poly_from(&[1]);
        let q = poly_from(&[-1, 0, 1]); // x^2 - 1
        let cert = partial_fractions(&p, &q).expect("must not decline");
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(true));
        assert_eq!(cert.terms.len(), 2);
        assert!(cert.terms.iter().all(|t| t.power == 1));

        // Cross-check by evaluation at a non-root point.
        let x = Rational::integer(3);
        let lhs = eval_ratio(&p, x).checked_div(eval_ratio(&q, x)).unwrap();
        let rhs = decomposition_value_at(&cert, x);
        assert_eq!(lhs, rhs);
    }

    /// A NON-monic denominator, so `leading != 1` -- every other producer
    /// test above uses a monic `q`, which would leave a `leading`-handling
    /// bug in `partial_fractions` invisible (multiplying by 1 hides an
    /// error). `q = 2x^2 - 2 = 2(x-1)(x+1)`.
    #[test]
    fn non_monic_denominator() {
        let p = poly_from(&[1]);
        let q = poly_from(&[-2, 0, 2]); // 2x^2 - 2
        let cert = partial_fractions(&p, &q).expect("must not decline");
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(true));
        assert_eq!(cert.leading, Rational::integer(2));

        let x = Rational::integer(5);
        let lhs = eval_ratio(&p, x).checked_div(eval_ratio(&q, x)).unwrap();
        assert_eq!(lhs, decomposition_value_at(&cert, x));
    }

    // ---- rung 2: repeated linear factor ----

    #[test]
    fn repeated_linear_factor() {
        // x / ((x-1)^2 (x-2)), q = (x-1)^2(x-2) = x^3 -4x^2 +5x -2.
        let p = poly_from(&[0, 1]);
        let q = poly_from(&[-2, 5, -4, 1]);
        let cert = partial_fractions(&p, &q).expect("must not decline");
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(true));
        assert_eq!(cert.terms.len(), 3);
        let group_for_x_minus_1 = cert
            .terms
            .iter()
            .filter(|t| t.factor == poly_from(&[-1, 1]))
            .count();
        assert_eq!(group_for_x_minus_1, 2, "the repeated factor gets 2 terms");

        let x = Rational::integer(5);
        let lhs = eval_ratio(&p, x).checked_div(eval_ratio(&q, x)).unwrap();
        assert_eq!(lhs, decomposition_value_at(&cert, x));
    }

    // ---- rung 3: irreducible quadratic factor ----

    #[test]
    fn irreducible_quadratic_factor() {
        // 1 / ((x-1)(x^2+1)), q = (x-1)(x^2+1) = x^3 - x^2 + x - 1.
        let p = poly_from(&[1]);
        let q = poly_from(&[-1, 1, -1, 1]);
        let cert = partial_fractions(&p, &q).expect("must not decline");
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(true));
        assert_eq!(cert.terms.len(), 2);
        let quadratic_term = cert
            .terms
            .iter()
            .find(|t| t.factor.len() == 3)
            .expect("an irreducible quadratic factor must appear");
        assert!(quadratic_term.numerator.len() <= 2, "Ax+B, degree < 2");

        let x = Rational::integer(4);
        let lhs = eval_ratio(&p, x).checked_div(eval_ratio(&q, x)).unwrap();
        assert_eq!(lhs, decomposition_value_at(&cert, x));
    }

    // ---- rung 4: fully general (mixed linear + repeated + quadratic) ----

    #[test]
    fn mixed_general_case() {
        // q = (x-1)^2 (x^2+1), a mix of a repeated linear factor and an
        // irreducible quadratic in one denominator.
        let p = poly_from(&[1, 1]); // x + 1
        let q_lin_sq = poly_from(&[1, -2, 1]); // (x-1)^2
        let q_quad = poly_from(&[1, 0, 1]); // x^2+1
        let q = poly::ratpoly_mul(&q_lin_sq, &q_quad).unwrap();
        let cert = partial_fractions(&p, &q).expect("must not decline");
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(true));
        assert_eq!(cert.terms.len(), 3); // (x-1)^1, (x-1)^2, quadratic^1

        let x = Rational::integer(7);
        let lhs = eval_ratio(&p, x).checked_div(eval_ratio(&q, x)).unwrap();
        assert_eq!(lhs, decomposition_value_at(&cert, x));
    }

    // ---- improper fraction: deg(p) >= deg(q) ----

    #[test]
    fn improper_fraction_splits_off_a_polynomial_part() {
        // p = x^3, q = x^2 - 1: p/q = x + x/(x^2-1) = x + (1/2)/(x-1) + (1/2)/(x+1).
        let p = poly_from(&[0, 0, 0, 1]);
        let q = poly_from(&[-1, 0, 1]);
        let cert = partial_fractions(&p, &q).expect("must not decline");
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(true));
        assert_eq!(cert.whole, poly_from(&[0, 1]), "whole part is x");

        let x = Rational::integer(5);
        let lhs = eval_ratio(&p, x).checked_div(eval_ratio(&q, x)).unwrap();
        assert_eq!(lhs, decomposition_value_at(&cert, x));
    }

    #[test]
    fn declines_on_constant_denominator() {
        let p = poly_from(&[1]);
        let q = poly_from(&[3]);
        assert_eq!(partial_fractions(&p, &q), None);
    }

    // ---- adversarial fixtures: the checker's return value must depend on
    // what it found ----

    #[test]
    fn perturbed_coefficient_is_rejected() {
        let p = poly_from(&[1]);
        let q = poly_from(&[-1, 0, 1]); // (x-1)(x+1)
        let mut cert = partial_fractions(&p, &q).expect("must not decline");
        // Perturb one numerator coefficient by +1.
        let term = &mut cert.terms[0];
        let bumped = term.numerator.first().copied().unwrap_or(Rational::zero());
        term.numerator = vec![bumped.checked_add(Rational::integer(1)).unwrap()];
        assert_eq!(
            verify_partial_fraction_certificate(&cert),
            Some(false),
            "a perturbed coefficient must be rejected"
        );
    }

    /// The flagship fixture for the power-set guard: relabel a repeated
    /// factor's SECOND term (power 2, numerator identically zero) down to
    /// power 1 (duplicating the first term's power). Because the demoted
    /// term's numerator is zero, BOTH the q-reconstruction check and the
    /// p-reconstruction check pass unchanged -- q's reconstruction only
    /// depends on the GROUP SIZE (still 2), and the demoted term still
    /// contributes exactly zero to the p-reconstruction sum, same as before.
    /// Only the "powers are exactly {1, .., group size}" guard tells the two
    /// apart. This is this module's analogue of taylor.rs's flagship fixture
    /// (an exterior root satisfying the same value equation): a genuinely
    /// wrong certificate whose non-structural checks are, by construction,
    /// vacuously satisfied.
    #[test]
    fn wrong_multiplicity_is_vacuous_without_the_power_set_guard() {
        // 1/(x-1) has decomposition: power-1 numerator 1, power-2 numerator 0
        // (a valid, if wasteful, way to write it against denominator (x-1)^2
        // -- scaled by leading so p = q_actual/(x-1); pick p, q directly).
        let factor = poly_from(&[-1, 1]); // x - 1
        let q = poly::ratpoly_mul(&factor, &factor).unwrap(); // (x-1)^2
        let p = factor.clone(); // p/q = (x-1)/(x-1)^2 = 1/(x-1)

        let cert = partial_fractions(&p, &q).expect("must not decline");
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(true));
        assert_eq!(cert.terms.len(), 2);
        let power2_numerator_is_zero = cert
            .terms
            .iter()
            .find(|t| t.power == 2)
            .is_some_and(|t| t.numerator.is_empty());
        assert!(
            power2_numerator_is_zero,
            "this fixture requires the power-2 term to carry a zero numerator"
        );

        // Mutate: relabel the power-2 (zero-numerator) term down to power 1,
        // producing powers {1, 1} instead of {1, 2} for one factor group.
        let mut mutant = cert.clone();
        for term in &mut mutant.terms {
            if term.power == 2 {
                term.power = 1;
            }
        }
        assert_eq!(
            verify_partial_fraction_certificate(&mutant),
            Some(false),
            "duplicate power labels for one factor group must be rejected, \
             even though q- and p-reconstruction both still hold"
        );
    }

    /// A repeated root disguised as two separate, non-coprime "irreducible"
    /// factors: (x-1) and (2x-2) = 2*(x-1), each claimed with multiplicity 1.
    /// Chosen so BOTH the q-reconstruction (leading * (x-1) * (2x-2) = q) and
    /// the p-reconstruction (for this specific p, divisible by (x-1)) still
    /// hold exactly -- only the pairwise-coprimality guard rejects it.
    #[test]
    fn disguised_repeated_root_via_proportional_factors_is_rejected() {
        let q = poly_from(&[2, -4, 2]); // 2x^2 - 4x + 2 = (x-1)*(2x-2)
        let p = poly_from(&[-1, 1]); // x - 1

        let cert = PartialFractionCertificate {
            p: p.clone(),
            q: q.clone(),
            whole: Vec::new(),
            leading: Rational::integer(1),
            terms: vec![
                PartialFractionTerm {
                    factor: poly_from(&[-1, 1]), // x - 1
                    power: 1,
                    numerator: Vec::new(), // 0
                },
                PartialFractionTerm {
                    factor: poly_from(&[-2, 2]), // 2x - 2
                    power: 1,
                    numerator: poly_from(&[1]), // 1
                },
            ],
        };

        // Confirm the fixture really does clear denominators correctly
        // before trusting the guard rejects it for the right reason.
        let x = Rational::integer(4);
        let lhs = eval_ratio(&p, x).checked_div(eval_ratio(&q, x)).unwrap();
        assert_eq!(
            lhs,
            decomposition_value_at(&cert, x),
            "fixture must be a genuine identity"
        );

        assert_eq!(
            verify_partial_fraction_certificate(&cert),
            Some(false),
            "two proportional (non-coprime) factors must be rejected even \
             though they reconstruct p and q exactly"
        );
    }

    /// A spurious CONSTANT "factor" group, with a zero numerator so it
    /// contributes nothing to the p-reconstruction sum, and `leading` scaled
    /// to compensate exactly in the q-reconstruction. This slips past every
    /// guard except the "every group's factor is non-constant" one:
    /// coprimality is vacuous against a constant (its gcd with anything is a
    /// unit), the numerator-degree bound is vacuous for a zero numerator
    /// against `deg_f == 0`, and both reconstructions are exact by
    /// construction. Only rejecting non-constant-factor groups catches it.
    #[test]
    fn spurious_constant_factor_with_zero_numerator_is_rejected() {
        let factor = poly_from(&[-1, 1]); // x - 1
        let q = factor.clone();
        let p = poly_from(&[1]); // p/q = 1/(x-1)

        let cert = PartialFractionCertificate {
            p: p.clone(),
            q: q.clone(),
            whole: Vec::new(),
            leading: rat(1, 2),
            terms: vec![
                PartialFractionTerm {
                    factor: factor.clone(),
                    power: 1,
                    numerator: poly_from(&[1]),
                },
                PartialFractionTerm {
                    factor: poly_from(&[2]), // constant "factor"
                    power: 1,
                    numerator: Vec::new(), // 0
                },
            ],
        };

        // Confirm it is a genuine identity before trusting the guard.
        let x = Rational::integer(9);
        let lhs = eval_ratio(&p, x).checked_div(eval_ratio(&q, x)).unwrap();
        assert_eq!(
            lhs,
            decomposition_value_at(&cert, x),
            "fixture must be a genuine identity"
        );

        assert_eq!(
            verify_partial_fraction_certificate(&cert),
            Some(false),
            "a spurious constant factor group must be rejected even though \
             both reconstructions and coprimality hold"
        );
    }

    #[test]
    fn empty_terms_is_rejected() {
        let cert = PartialFractionCertificate {
            p: poly_from(&[1]),
            q: poly_from(&[-1, 0, 1]),
            whole: Vec::new(),
            leading: Rational::integer(1),
            terms: Vec::new(),
        };
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(false));
    }

    #[test]
    fn constant_denominator_certificate_is_rejected() {
        let cert = PartialFractionCertificate {
            p: poly_from(&[1]),
            q: poly_from(&[3]),
            whole: Vec::new(),
            leading: Rational::integer(1),
            terms: vec![PartialFractionTerm {
                factor: poly_from(&[3]),
                power: 1,
                numerator: poly_from(&[1]),
            }],
        };
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(false));
    }

    #[test]
    fn zero_leading_scalar_is_rejected() {
        let p = poly_from(&[1]);
        let q = poly_from(&[-1, 0, 1]);
        let mut cert = partial_fractions(&p, &q).unwrap();
        cert.leading = Rational::zero();
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(false));
    }

    /// Isolates the q-reconstruction guard: keep a genuinely correct
    /// certificate for `1/((x-1)(x+1))` (`whole` is empty, so `q` never
    /// enters the p-reconstruction sum at all -- `whole*q` is zero
    /// regardless of `q`'s value) but swap the stored `q` for an unrelated
    /// non-constant polynomial. Every other guard is blind to this: the
    /// terms/factors/powers/coprimality checks never look at `q` itself, and
    /// p-reconstruction is unaffected because `whole` is empty.
    #[test]
    fn mismatched_q_is_rejected() {
        let p = poly_from(&[1]);
        let q = poly_from(&[-1, 0, 1]); // (x-1)(x+1)
        let mut cert = partial_fractions(&p, &q).expect("must not decline");
        assert_eq!(
            cert.whole,
            Vec::<Rational>::new(),
            "fixture needs whole == 0"
        );
        cert.q = poly_from(&[-4, 0, 1]); // x^2 - 4, unrelated to the factors
        assert_eq!(
            verify_partial_fraction_certificate(&cert),
            Some(false),
            "a q that the stated factors do not reconstruct must be rejected"
        );
    }

    #[test]
    fn numerator_degree_too_high_is_rejected() {
        let p = poly_from(&[1]);
        let q = poly_from(&[-1, 0, 1]); // two degree-1 factors
        let mut cert = partial_fractions(&p, &q).unwrap();
        cert.terms[0].numerator = poly_from(&[1, 1]); // degree 1, factor degree 1
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(false));
    }

    /// `numerator_degree_too_high_is_rejected` above is ALSO caught by the
    /// p-reconstruction guard (bumping one numerator's degree without
    /// compensating breaks the identity). This fixture isolates the degree
    /// bound itself: without it, a partial-fraction "decomposition" is not
    /// unique -- `N/(x-1) == (N + k*(x-1))/(x-1) - k` for ANY polynomial `k`,
    /// shifted into `whole`. Bump the single numerator's degree by exactly
    /// one factor's worth and compensate in `whole`, so p- and
    /// q-reconstruction, coprimality, and the power-set guard all still hold
    /// exactly; only the degree bound rejects it.
    #[test]
    fn over_degree_numerator_compensated_by_whole_is_rejected() {
        let factor = poly_from(&[-1, 1]); // x - 1
        let q = factor.clone();
        let p = poly_from(&[2]); // p/q = 2/(x-1): whole=0, N=2

        let baseline = partial_fractions(&p, &q).expect("must not decline");
        assert_eq!(verify_partial_fraction_certificate(&baseline), Some(true));
        assert_eq!(baseline.whole, Vec::<Rational>::new());
        assert_eq!(baseline.terms[0].numerator, poly_from(&[2]));

        // N' = N + 1*(x-1) = 1 + x; whole' = whole - 1 = -1. Since q = x-1
        // exactly, whole'*q + N' = -(x-1) + (1+x) = 2 = p, unchanged.
        let mut mutant = baseline.clone();
        mutant.whole = poly_from(&[-1]);
        mutant.terms[0].numerator = poly_from(&[1, 1]);

        let x = Rational::integer(5);
        let lhs = eval_ratio(&p, x).checked_div(eval_ratio(&q, x)).unwrap();
        assert_eq!(
            lhs,
            decomposition_value_at(&mutant, x),
            "fixture must be a genuine identity"
        );

        assert_eq!(
            verify_partial_fraction_certificate(&mutant),
            Some(false),
            "an over-degree numerator must be rejected even when compensated \
             exactly by the whole part"
        );
    }
}
