//! Real algebraic numbers as (minimal polynomial + isolating interval).
//!
//! An [`AlgebraicReal`] represents a single real root of an irreducible rational
//! polynomial, pinned down by a rational isolating interval `(lower, upper]` known
//! (by Sturm's theorem) to contain exactly that one root. This is the axeyum-cas
//! realization of a `RootOf` value: every real root of any univariate rational
//! polynomial — rational, quadratic-surd, or of degree ≥ 5 beyond closed-form
//! radicals — is representable exactly and can be refined to arbitrary precision.
//!
//! The defining polynomial is an **irreducible factor over ℚ** (from
//! [`factor_univariate_over_q`]), so it is the
//! genuine minimal polynomial and `degree()` is the algebraic degree.

use axeyum_ir::{Rational, poly};

use crate::{factor_univariate_over_q, sturm};

/// A real algebraic number: the unique real root of `minimal_poly` lying in the
/// half-open interval `(lower, upper]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlgebraicReal {
    /// The minimal polynomial (an irreducible factor over ℚ), LSB-first.
    minimal_poly: Vec<Rational>,
    /// Lower interval endpoint (exclusive).
    lower: Rational,
    /// Upper interval endpoint (inclusive).
    upper: Rational,
}

impl AlgebraicReal {
    /// The minimal polynomial (LSB-first irreducible factor over ℚ) this root
    /// satisfies.
    #[must_use]
    pub fn minimal_polynomial(&self) -> &[Rational] {
        &self.minimal_poly
    }

    /// The algebraic degree — the degree of the minimal polynomial (`1` for a
    /// rational number).
    #[must_use]
    pub fn degree(&self) -> usize {
        poly::rat_degree(&self.minimal_poly).unwrap_or(0)
    }

    /// The current isolating interval `(lower, upper]`.
    #[must_use]
    pub fn isolating_interval(&self) -> (Rational, Rational) {
        (self.lower, self.upper)
    }

    /// Whether this is a rational number (degree-1 minimal polynomial); if so, its
    /// exact rational value.
    #[must_use]
    pub fn rational_value(&self) -> Option<Rational> {
        if self.degree() == 1 {
            // minimal_poly = a·x + b (LSB [b, a]); root = −b/a.
            let b = self.minimal_poly.first().copied()?;
            let a = self.minimal_poly.get(1).copied()?;
            b.checked_neg()?.checked_div(a)
        } else {
            None
        }
    }

    /// Refine the isolating interval by sign-bisection until its width is below
    /// `width`, returning the tightened [`AlgebraicReal`] (same root). `None` on a
    /// non-positive `width` or overflow.
    #[must_use]
    pub fn refine(&self, width: Rational) -> Option<AlgebraicReal> {
        if width.numerator() <= 0 {
            return None;
        }
        let sign_at = |x: Rational| -> Option<i128> {
            Some(
                poly::eval_rat_poly(&self.minimal_poly, x)?
                    .numerator()
                    .signum(),
            )
        };
        let lower_sign = sign_at(self.lower)?;
        let (mut lower, mut upper) = (self.lower, self.upper);
        let mut guard = 0usize;
        while upper.checked_sub(lower)?.checked_cmp(&width)? == core::cmp::Ordering::Greater {
            guard += 1;
            if guard > 100_000 {
                break;
            }
            let mid = lower
                .checked_add(upper)?
                .checked_div(Rational::integer(2))?;
            match sign_at(mid)? {
                0 => {
                    // Exact rational root at the midpoint.
                    lower = mid;
                    upper = mid;
                    break;
                }
                s if s == lower_sign => lower = mid,
                _ => upper = mid,
            }
        }
        Some(AlgebraicReal {
            minimal_poly: self.minimal_poly.clone(),
            lower,
            upper,
        })
    }

    /// A floating-point approximation of the root, obtained by bisecting the
    /// isolating interval in `f64` (the minimal polynomial's sign decides each step).
    /// Bisecting in `f64` rather than exact rationals avoids the `i128` overflow of
    /// evaluating a high-degree polynomial at a fine rational, and reaches full
    /// double precision regardless of algebraic degree.
    #[must_use]
    #[allow(clippy::cast_precision_loss)] // f64 approximation by definition
    pub fn to_f64(&self) -> f64 {
        let coeffs: Vec<f64> = self
            .minimal_poly
            .iter()
            .map(|c| c.numerator() as f64 / c.denominator() as f64)
            .collect();
        // Horner evaluation of the (MSB-last) coefficient vector.
        let eval = |x: f64| coeffs.iter().rev().fold(0.0, |acc, &c| acc * x + c);

        let mut lower = self.lower.numerator() as f64 / self.lower.denominator() as f64;
        let mut upper = self.upper.numerator() as f64 / self.upper.denominator() as f64;
        let lower_positive = eval(lower) > 0.0;
        for _ in 0..200 {
            let mid = 0.5 * (lower + upper);
            if mid <= lower || mid >= upper {
                break; // converged to the f64 ulp
            }
            if (eval(mid) > 0.0) == lower_positive {
                lower = mid;
            } else {
                upper = mid;
            }
        }
        0.5 * (lower + upper)
    }
}

/// All **real** roots of a univariate rational polynomial, each as an exact
/// [`AlgebraicReal`] (with its irreducible minimal polynomial), sorted ascending.
///
/// The polynomial is factored over ℚ; each irreducible factor's real roots are
/// Sturm-isolated. This yields every real root — rational, surd, or higher-degree —
/// with an exact defining polynomial and a certified isolating interval. `None` for
/// the zero polynomial or on overflow; `Some(vec![])` when there are no real roots.
///
/// ```
/// use axeyum_cas::algebraic::real_roots;
/// use axeyum_ir::Rational;
/// // x³ − 2 has one real root, the cube root of 2 (degree 3, ≈ 1.2599).
/// let coeffs = [Rational::integer(-2), Rational::zero(), Rational::zero(), Rational::integer(1)];
/// let roots = real_roots(&coeffs).unwrap();
/// assert_eq!(roots.len(), 1);
/// assert_eq!(roots[0].degree(), 3);
/// assert!((roots[0].to_f64() - 2f64.cbrt()).abs() < 1e-9);
/// ```
#[must_use]
pub fn real_roots(coeffs: &[Rational]) -> Option<Vec<AlgebraicReal>> {
    let factors = factor_univariate_over_q(coeffs)?;
    let mut roots: Vec<AlgebraicReal> = Vec::new();
    for (factor, _multiplicity) in factors {
        if poly::rat_degree(&factor).unwrap_or(0) == 0 {
            continue; // a constant factor has no roots
        }
        for (lower, upper) in sturm::isolate_real_roots(&factor)? {
            roots.push(AlgebraicReal {
                minimal_poly: factor.clone(),
                lower,
                upper,
            });
        }
    }
    roots.sort_by(|a, b| {
        a.to_f64()
            .partial_cmp(&b.to_f64())
            .unwrap_or(core::cmp::Ordering::Equal)
    });
    Some(roots)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn poly_from(coeffs: &[i128]) -> Vec<Rational> {
        coeffs.iter().map(|&c| Rational::integer(c)).collect()
    }

    #[test]
    fn cube_root_of_two_is_degree_three() {
        // x³ − 2: one real root ∛2 ≈ 1.2599, degree 3, irrational.
        let roots = real_roots(&poly_from(&[-2, 0, 0, 1])).unwrap();
        assert_eq!(roots.len(), 1);
        assert_eq!(roots[0].degree(), 3);
        assert!(roots[0].rational_value().is_none());
        assert!((roots[0].to_f64() - 2f64.cbrt()).abs() < 1e-9);
    }

    #[test]
    fn mixed_rational_and_irrational_roots() {
        // (x − 3)(x² − 2) = x³ − 3x² − 2x + 6: roots −√2, √2, 3.
        let roots = real_roots(&poly_from(&[6, -2, -3, 1])).unwrap();
        assert_eq!(roots.len(), 3);
        // Ascending: −√2 ≈ −1.414 (deg 2), √2 ≈ 1.414 (deg 2), 3 (deg 1, rational).
        assert!((roots[0].to_f64() + std::f64::consts::SQRT_2).abs() < 1e-9);
        assert_eq!(roots[0].degree(), 2);
        assert!((roots[1].to_f64() - std::f64::consts::SQRT_2).abs() < 1e-9);
        assert_eq!(roots[2].degree(), 1);
        assert_eq!(roots[2].rational_value(), Some(Rational::integer(3)));
    }

    #[test]
    fn quintic_beyond_radicals_is_isolated() {
        // x⁵ − x − 1 (the classic non-solvable-by-radicals quintic) has one real
        // root ≈ 1.1673, isolated exactly with degree 5.
        let roots = real_roots(&poly_from(&[-1, -1, 0, 0, 0, 1])).unwrap();
        assert_eq!(roots.len(), 1);
        assert_eq!(roots[0].degree(), 5);
        assert!((roots[0].to_f64() - 1.167_303_978).abs() < 1e-6);
    }

    #[test]
    fn no_real_roots() {
        // x² + 1 has no real roots.
        assert!(real_roots(&poly_from(&[1, 0, 1])).unwrap().is_empty());
    }

    #[test]
    fn refine_narrows_the_interval() {
        let roots = real_roots(&poly_from(&[-2, 0, 0, 1])).unwrap(); // ∛2
        let refined = roots[0].refine(Rational::new(1, 1_000_000)).unwrap();
        let (lower, upper) = refined.isolating_interval();
        assert_ne!(
            upper
                .checked_sub(lower)
                .unwrap()
                .checked_cmp(&Rational::new(1, 1_000_000))
                .unwrap(),
            core::cmp::Ordering::Greater
        );
    }
}
