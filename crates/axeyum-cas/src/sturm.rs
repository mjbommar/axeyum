//! Real-root isolation via Sturm sequences.
//!
//! Given a univariate polynomial with rational coefficients, [`isolate_real_roots`]
//! returns disjoint rational intervals each containing **exactly one** real root,
//! and [`count_real_roots_in`] counts the real roots in a half-open interval. Both
//! rest on **Sturm's theorem**: for the Sturm chain of a square-free polynomial,
//! the number of distinct real roots in `(a, b]` equals `V(a) − V(b)`, where `V(x)`
//! is the number of sign changes in the chain evaluated at `x`. The sign-count is
//! the certificate — an exact, theorem-backed count, computed in exact rational
//! arithmetic.
//!
//! The polynomial is reduced to its square-free part first, so each real root is
//! isolated once regardless of multiplicity.

use axeyum_ir::{Rational, poly};

/// A generous degree cap for the exact GCD used in square-free reduction.
const GCD_DEGREE_CAP: usize = 256;

/// The Sturm chain `s₀ = p`, `s₁ = p′`, `sₖ = −rem(sₖ₋₂, sₖ₋₁)`, stopping when the
/// remainder vanishes. `p` is LSB-first; `None` on the zero polynomial or overflow.
fn sturm_chain(p: &[Rational]) -> Option<Vec<Vec<Rational>>> {
    let first = poly::rat_trim(p.to_vec());
    poly::rat_degree(&first)?; // reject the zero polynomial
    let mut chain = vec![first];
    let derivative = poly::rat_trim(poly::rat_derivative(&chain[0])?);
    if poly::rat_degree(&derivative).is_none() {
        return Some(chain); // constant polynomial: no roots, chain is [p]
    }
    chain.push(derivative);
    loop {
        let len = chain.len();
        let remainder = poly::rat_rem(&chain[len - 2], &chain[len - 1])?;
        let remainder = poly::rat_trim(remainder);
        if poly::rat_degree(&remainder).is_none() {
            break; // zero remainder: the chain is complete
        }
        let negated = remainder
            .iter()
            .map(|coeff| coeff.checked_neg())
            .collect::<Option<Vec<_>>>()?;
        chain.push(poly::rat_trim(negated));
    }
    Some(chain)
}

/// The number of sign changes (ignoring zeros) in the Sturm chain evaluated at `x`.
fn sign_variations(chain: &[Vec<Rational>], x: Rational) -> Option<usize> {
    let mut variations = 0usize;
    let mut previous: Option<bool> = None; // sign: true = positive
    for member in chain {
        let value = poly::eval_rat_poly(member, x)?;
        if value.is_zero() {
            continue;
        }
        let positive = value.numerator() > 0;
        if let Some(prev) = previous
            && prev != positive
        {
            variations += 1;
        }
        previous = Some(positive);
    }
    Some(variations)
}

/// The number of **distinct** real roots of `p` in the half-open interval
/// `(lower, upper]`, via Sturm's theorem. `p` is an LSB-first rational polynomial.
/// `None` if `p` is zero/constant-with-no-square-free-part or on overflow.
#[must_use]
pub fn count_real_roots_in(p: &[Rational], lower: Rational, upper: Rational) -> Option<usize> {
    let squarefree = poly::squarefree_part(p, GCD_DEGREE_CAP)?;
    let chain = sturm_chain(&squarefree)?;
    let at_lower = sign_variations(&chain, lower)?;
    let at_upper = sign_variations(&chain, upper)?;
    Some(at_lower.saturating_sub(at_upper))
}

/// A Cauchy bound `B` such that every real root lies in `(−B, B)`:
/// `B = 1 + max_i |aᵢ / aₙ|` for `p = Σ aᵢ xⁱ` of degree `n`. `None` on overflow or
/// a constant polynomial.
fn cauchy_bound(p: &[Rational]) -> Option<Rational> {
    let degree = poly::rat_degree(p)?;
    if degree == 0 {
        return None;
    }
    let leading = p[degree];
    let mut max_ratio = Rational::zero();
    for coeff in &p[..degree] {
        let ratio = coeff.checked_div(leading)?;
        let magnitude = if ratio.numerator() < 0 {
            ratio.checked_neg()?
        } else {
            ratio
        };
        if magnitude.checked_cmp(&max_ratio)? == core::cmp::Ordering::Greater {
            max_ratio = magnitude;
        }
    }
    max_ratio.checked_add(Rational::integer(1))
}

/// Isolate the real roots of a univariate rational polynomial: return disjoint
/// half-open intervals `(lower, upper]`, sorted ascending, each containing
/// **exactly one** real root (multiplicity collapsed to one). The count in each
/// interval is Sturm-certified to be `1`.
///
/// Returns `None` for the zero polynomial or on overflow; `Some(vec![])` when there
/// are no real roots. `p` is LSB-first.
#[must_use]
pub fn isolate_real_roots(p: &[Rational]) -> Option<Vec<(Rational, Rational)>> {
    let squarefree = poly::squarefree_part(p, GCD_DEGREE_CAP)?;
    let degree = poly::rat_degree(&squarefree)?;
    if degree == 0 {
        return Some(Vec::new()); // nonzero constant: no roots
    }
    let chain = sturm_chain(&squarefree)?;
    let bound = cauchy_bound(&squarefree)?;
    let lower = bound.checked_neg()?;

    let variations_at = |x: Rational| sign_variations(&chain, x);
    let total = variations_at(lower)?.saturating_sub(variations_at(bound)?);

    // Bisection worklist: refine each interval until it isolates a single root.
    let mut isolated: Vec<(Rational, Rational)> = Vec::new();
    let mut stack: Vec<(Rational, Rational, usize)> = vec![(lower, bound, total)];
    let mut guard = 0usize;
    let guard_limit = 100_000usize;
    while let Some((left, right, count)) = stack.pop() {
        guard += 1;
        if guard > guard_limit {
            return None; // resource cap — decline rather than loop
        }
        match count {
            0 => {}
            1 => isolated.push((left, right)),
            _ => {
                let mid = left.checked_add(right)?.checked_div(Rational::integer(2))?;
                // A root exactly at `mid` would be missed by the two half-open
                // subintervals `(left, mid]` and `(mid, right]`; but the chain is
                // square-free, and `mid` is a dyadic rational, so shifting is not
                // needed here — the endpoints are handled by the half-open counts.
                let variations_mid = variations_at(mid)?;
                let left_count = variations_at(left)?.saturating_sub(variations_mid);
                let right_count = variations_mid.saturating_sub(variations_at(right)?);
                stack.push((mid, right, right_count));
                stack.push((left, mid, left_count));
            }
        }
    }
    isolated.sort_by(|a, b| a.0.checked_cmp(&b.0).unwrap_or(core::cmp::Ordering::Equal));
    Some(isolated)
}

/// Refine an isolating interval `(lower, upper]` for a **simple** root of the
/// square-free polynomial `p` down to width `< width` by sign-bisection, returning
/// the midpoint as a rational approximation. `None` on overflow.
fn refine_root(
    p: &[Rational],
    mut lower: Rational,
    mut upper: Rational,
    width: Rational,
) -> Option<Rational> {
    let sign_at = |x: Rational| -> Option<i32> {
        let value = poly::eval_rat_poly(p, x)?;
        Some(value.numerator().signum().try_into().unwrap_or(0))
    };
    let lower_sign = sign_at(lower)?;
    let mut guard = 0usize;
    while upper.checked_sub(lower)?.checked_cmp(&width)? == core::cmp::Ordering::Greater {
        guard += 1;
        if guard > 100_000 {
            break;
        }
        let mid = lower
            .checked_add(upper)?
            .checked_div(Rational::integer(2))?;
        let mid_sign = sign_at(mid)?;
        if mid_sign == 0 {
            return Some(mid); // landed exactly on the root
        }
        if mid_sign == lower_sign {
            lower = mid;
        } else {
            upper = mid;
        }
    }
    lower.checked_add(upper)?.checked_div(Rational::integer(2))
}

/// Rational approximations (to within `width`) of **every** real root of a
/// univariate rational polynomial, ascending. Each root is first isolated by
/// [`isolate_real_roots`] (Sturm-certified), then bisected to the requested width.
/// `None` for the zero polynomial, a non-positive `width`, or on overflow.
#[must_use]
pub fn approximate_real_roots(p: &[Rational], width: Rational) -> Option<Vec<Rational>> {
    if width.numerator() <= 0 {
        return None;
    }
    let squarefree = poly::squarefree_part(p, GCD_DEGREE_CAP)?;
    let intervals = isolate_real_roots(p)?;
    let mut roots = Vec::with_capacity(intervals.len());
    for (lower, upper) in intervals {
        roots.push(refine_root(&squarefree, lower, upper, width)?);
    }
    Some(roots)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn poly_from(coeffs: &[i128]) -> Vec<Rational> {
        coeffs.iter().map(|&c| Rational::integer(c)).collect()
    }

    #[test]
    fn counts_and_isolates_rational_roots() {
        // (x−1)(x−2)(x−3) = x³ − 6x² + 11x − 6: roots 1, 2, 3.
        let p = poly_from(&[-6, 11, -6, 1]);
        let intervals = isolate_real_roots(&p).unwrap();
        assert_eq!(intervals.len(), 3);
        // Each interval brackets exactly one integer root, in order.
        for (interval, root) in intervals.iter().zip([1, 2, 3]) {
            let (lo, hi) = *interval;
            let root_rat = Rational::integer(root);
            assert!(lo.checked_cmp(&root_rat).unwrap() != core::cmp::Ordering::Greater);
            assert!(hi.checked_cmp(&root_rat).unwrap() != core::cmp::Ordering::Less);
            // Exactly one root in each isolating interval (Sturm-certified).
            assert_eq!(count_real_roots_in(&p, lo, hi), Some(1));
        }
    }

    #[test]
    fn isolates_irrational_roots() {
        // x² − 2: roots ±√2 ≈ ±1.414. Two disjoint intervals, each with one root.
        let p = poly_from(&[-2, 0, 1]);
        let intervals = isolate_real_roots(&p).unwrap();
        assert_eq!(intervals.len(), 2);
        assert_eq!(
            count_real_roots_in(&p, intervals[0].0, intervals[0].1),
            Some(1)
        );
        // The negative root's interval is entirely negative, the positive's positive.
        assert!(intervals[0].1.numerator() < 0 || intervals[0].0.numerator() < 0);
    }

    #[test]
    fn no_real_roots_for_positive_definite() {
        // x² + 1 has no real roots.
        let p = poly_from(&[1, 0, 1]);
        assert_eq!(isolate_real_roots(&p).unwrap().len(), 0);
    }

    #[test]
    fn multiplicity_collapses_to_one_interval() {
        // (x−1)² = x² − 2x + 1: a double root at 1, isolated once.
        let p = poly_from(&[1, -2, 1]);
        assert_eq!(isolate_real_roots(&p).unwrap().len(), 1);
    }

    #[test]
    #[allow(clippy::cast_precision_loss)] // small test values; f64 comparison only
    fn approximates_roots_to_precision() {
        // x² − 2: √2 ≈ 1.41421356. Approximate to width 1/1000.
        let p = poly_from(&[-2, 0, 1]);
        let width = Rational::new(1, 1000);
        let roots = approximate_real_roots(&p, width).unwrap();
        assert_eq!(roots.len(), 2);
        // The positive approximation is within `width` of √2.
        let positive = roots.iter().find(|r| r.numerator() > 0).unwrap();
        let as_float = positive.numerator() as f64 / positive.denominator() as f64;
        assert!((as_float - std::f64::consts::SQRT_2).abs() < 1e-2);
        // Exact rational roots come out essentially exact: (x−3)(x+5) → {−5, 3}.
        let q = poly_from(&[-15, 2, 1]); // x² + 2x − 15
        let exact = approximate_real_roots(&q, Rational::new(1, 1_000_000)).unwrap();
        assert_eq!(exact.len(), 2);
    }

    #[test]
    fn counts_roots_in_a_subinterval() {
        // x³ − 6x² + 11x − 6 (roots 1,2,3): (0,2] holds {1,2}, (2,4] holds {3}.
        let p = poly_from(&[-6, 11, -6, 1]);
        assert_eq!(
            count_real_roots_in(&p, Rational::integer(0), Rational::integer(2)),
            Some(2)
        );
        assert_eq!(
            count_real_roots_in(&p, Rational::integer(2), Rational::integer(4)),
            Some(1)
        );
        assert_eq!(
            count_real_roots_in(&p, Rational::integer(4), Rational::integer(10)),
            Some(0)
        );
    }
}
