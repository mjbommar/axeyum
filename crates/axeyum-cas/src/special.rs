//! Closed-form special-function values at rational arguments.
//!
//! The Gamma function has elementary closed forms at integer and half-integer
//! arguments; this module returns those exactly (integers as rationals, half-integers
//! with a `√π` factor). The Beta function follows from `B(x,y) = Γ(x)Γ(y)/Γ(x+y)`.
//! General (non-rational-shifted) arguments have no elementary closed form and return
//! `None`.

use axeyum_ir::Rational;

use crate::{CasExpr, ntheory};

/// `√π` as a `CasExpr` (the reserved constant `pi` under a square root).
fn sqrt_pi() -> CasExpr {
    CasExpr::var("pi").sqrt()
}

/// The **Gamma function** `Γ(x)` at a rational `x`, when it has an elementary closed
/// form: a positive integer `n` gives `(n−1)!`; a positive half-integer `n + 1/2`
/// (`n ≥ 0`) gives `(2n)!/(4ⁿ·n!)·√π`. Returned as an exact [`CasExpr`]. `None` for
/// non-positive integers (poles), other rationals, or overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, special::gamma};
/// use axeyum_ir::Rational;
/// // Γ(5) = 4! = 24.
/// assert_eq!(gamma(Rational::integer(5)), Some(CasExpr::int(24)));
/// ```
#[must_use]
pub fn gamma(x: Rational) -> Option<CasExpr> {
    let (num, den) = (x.numerator(), x.denominator());
    if den == 1 {
        // Integer: Γ(n) = (n−1)! for n ≥ 1; pole for n ≤ 0.
        if num < 1 {
            return None;
        }
        let factorial = ntheory::factorial(num - 1)?;
        return Some(CasExpr::Const(Rational::integer(factorial)));
    }
    if den == 2 {
        // Reduced half-integer x = num/2 (num odd). Γ has a closed form for the
        // positive half-integers n + 1/2 = (2n+1)/2, i.e. num ≥ 1.
        if num < 1 {
            return None;
        }
        let n = (num - 1) / 2; // n ≥ 0
        // Γ(n+1/2) = (2n)! / (4ⁿ · n!) · √π.
        let two_n_fact = ntheory::factorial(2 * n)?;
        let n_fact = ntheory::factorial(n)?;
        let four_pow_n = 4i128.checked_pow(u32::try_from(n).ok()?)?;
        let coefficient = Rational::checked_new(two_n_fact, four_pow_n.checked_mul(n_fact)?)?;
        return Some(CasExpr::Const(coefficient) * sqrt_pi());
    }
    None
}

/// The **Beta function** `B(x, y) = Γ(x)·Γ(y)/Γ(x+y)` at rational arguments, when all
/// three Gamma values have closed forms. Returned as an exact [`CasExpr`], simplified.
/// `None` otherwise.
#[must_use]
pub fn beta(x: Rational, y: Rational) -> Option<CasExpr> {
    let gx = gamma(x)?;
    let gy = gamma(y)?;
    let gxy = gamma(x.checked_add(y)?)?;
    // Return the raw quotient (the zero-test reduces the rational part); do not
    // `simplify`, which would atomize any `√π` factor and lose structure.
    Some(gx * gy / gxy)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ZeroTest, equal};

    fn assert_equal(a: &CasExpr, b: &CasExpr) {
        assert!(matches!(
            equal(a, b),
            ZeroTest::Certified { equal: true, .. }
        ));
    }

    #[test]
    fn gamma_at_integers() {
        assert_eq!(gamma(Rational::integer(1)), Some(CasExpr::int(1))); // Γ(1)=0!=1
        assert_eq!(gamma(Rational::integer(4)), Some(CasExpr::int(6))); // Γ(4)=3!=6
        assert_eq!(gamma(Rational::integer(6)), Some(CasExpr::int(120)));
        assert!(gamma(Rational::integer(0)).is_none()); // pole
        assert!(gamma(Rational::integer(-2)).is_none());
    }

    #[test]
    fn gamma_at_half_integers() {
        // Γ(1/2) = √π.
        assert_equal(&gamma(Rational::new(1, 2)).unwrap(), &sqrt_pi());
        // Γ(3/2) = (1/2)√π.
        assert_equal(&gamma(Rational::new(3, 2)).unwrap(), &(CasExpr::rat(1, 2) * sqrt_pi()));
        // Γ(5/2) = (3/4)√π.
        assert_equal(&gamma(Rational::new(5, 2)).unwrap(), &(CasExpr::rat(3, 4) * sqrt_pi()));
    }

    #[test]
    fn beta_values() {
        // B(2,3) = Γ(2)Γ(3)/Γ(5) = 1·2/24 = 1/12 (rational — reduces via the zero-test).
        assert_equal(&beta(Rational::integer(2), Rational::integer(3)).unwrap(), &CasExpr::rat(1, 12));
        // B(3,4) = 2·6/720 = 1/60.
        assert_equal(&beta(Rational::integer(3), Rational::integer(4)).unwrap(), &CasExpr::rat(1, 60));
        // B(1/2, 1/2) = Γ(1/2)²/Γ(1) = √π·√π (which equals π for π>0; the zero-test
        // keeps it as √π·√π since `pi` is a symbol, not a non-negative constant).
        assert_equal(
            &beta(Rational::new(1, 2), Rational::new(1, 2)).unwrap(),
            &(sqrt_pi() * sqrt_pi()),
        );
    }
}
