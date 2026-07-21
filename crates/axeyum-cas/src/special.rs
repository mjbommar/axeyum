//! Closed-form special-function values at rational arguments.
//!
//! The Gamma function has elementary closed forms at integer and half-integer
//! arguments; this module returns those exactly (integers as rationals, half-integers
//! with a `√π` factor). The Beta function follows from `B(x,y) = Γ(x)Γ(y)/Γ(x+y)`.
//! General (non-rational-shifted) arguments have no elementary closed form and return
//! `None`.

use axeyum_ir::Rational;

use crate::{CasExpr, combinatorics, ntheory};

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

/// The **Riemann zeta function** `ζ(s)` at an integer `s`, wherever it has an
/// elementary closed form:
///
/// - **positive even** `s = 2k`: `ζ(2k) = (−1)^{k+1}·B_{2k}·(2π)^{2k}/(2·(2k)!)`,
///   a rational multiple of `π^{2k}` (`ζ(2) = π²/6`, `ζ(4) = π⁴/90`, …), returned
///   as `CasExpr::Const(c)·pi^{2k}`;
/// - `s = 0`: `ζ(0) = −1/2`;
/// - **negative integers** `s = −m` (`m ≥ 1`): `ζ(−m) = −B_{m+1}/(m+1)`
///   (`ζ(−1) = −1/12`; `ζ(−2k) = 0` at the trivial zeros).
///
/// Returns `None` for the pole at `s = 1`, for **positive odd** `s ≥ 3` (`ζ(3)`,
/// … have no known elementary closed form — honestly declined, not approximated),
/// and on `i128` overflow (large `s`, where the factorial or `2^{2k}` exceeds the
/// exact range).
///
/// ```
/// use axeyum_cas::{CasExpr, special::zeta, equal, ZeroTest};
/// // ζ(2) = π²/6.
/// let z2 = zeta(2).unwrap();
/// let expected = CasExpr::rat(1, 6) * CasExpr::var("pi").pow(2);
/// assert!(matches!(equal(&z2, &expected), ZeroTest::Certified { equal: true, .. }));
/// // ζ(−1) = −1/12.
/// assert_eq!(zeta(-1), Some(CasExpr::rat(-1, 12)));
/// ```
#[must_use]
pub fn zeta(s: i64) -> Option<CasExpr> {
    if s == 1 {
        return None; // simple pole
    }
    if s == 0 {
        return Some(CasExpr::rat(-1, 2));
    }
    if s < 0 {
        // ζ(−m) = −B_{m+1}/(m+1).
        let m = u32::try_from(-s).ok()?;
        let order = m.checked_add(1)?;
        let bernoulli = combinatorics::bernoulli(order)?;
        let value = bernoulli
            .checked_div(Rational::integer(i128::from(order)))?
            .checked_neg()?;
        return Some(CasExpr::Const(value));
    }
    // s ≥ 2.
    let n = u32::try_from(s).ok()?;
    if n % 2 == 1 {
        return None; // positive odd ≥ 3: no elementary closed form
    }
    let k = n / 2;
    // ζ(2k) = (−1)^{k+1}·B_{2k}·(2π)^{2k}/(2·(2k)!) = c·π^{2k} with
    // c = (−1)^{k+1}·B_{2k}·2^{2k}/(2·(2k)!).
    let bernoulli = combinatorics::bernoulli(n)?; // B_{2k}
    let factorial = ntheory::factorial(i128::from(n))?; // (2k)!
    let two_pow = 2i128.checked_pow(n)?; // 2^{2k}
    let denom = Rational::integer(2i128.checked_mul(factorial)?);
    let mut coeff = bernoulli
        .checked_mul(Rational::integer(two_pow))?
        .checked_div(denom)?;
    if k % 2 == 0 {
        // (−1)^{k+1} = −1 when k is even.
        coeff = coeff.checked_neg()?;
    }
    Some(CasExpr::Const(coeff) * CasExpr::var("pi").pow(n))
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
        assert_equal(
            &gamma(Rational::new(3, 2)).unwrap(),
            &(CasExpr::rat(1, 2) * sqrt_pi()),
        );
        // Γ(5/2) = (3/4)√π.
        assert_equal(
            &gamma(Rational::new(5, 2)).unwrap(),
            &(CasExpr::rat(3, 4) * sqrt_pi()),
        );
    }

    #[test]
    fn beta_values() {
        // B(2,3) = Γ(2)Γ(3)/Γ(5) = 1·2/24 = 1/12 (rational — reduces via the zero-test).
        assert_equal(
            &beta(Rational::integer(2), Rational::integer(3)).unwrap(),
            &CasExpr::rat(1, 12),
        );
        // B(3,4) = 2·6/720 = 1/60.
        assert_equal(
            &beta(Rational::integer(3), Rational::integer(4)).unwrap(),
            &CasExpr::rat(1, 60),
        );
        // B(1/2, 1/2) = Γ(1/2)²/Γ(1) = √π·√π (which equals π for π>0; the zero-test
        // keeps it as √π·√π since `pi` is a symbol, not a non-negative constant).
        assert_equal(
            &beta(Rational::new(1, 2), Rational::new(1, 2)).unwrap(),
            &(sqrt_pi() * sqrt_pi()),
        );
    }

    #[test]
    fn zeta_closed_forms() {
        let pi = || CasExpr::var("pi");
        // Positive even: ζ(2)=π²/6, ζ(4)=π⁴/90, ζ(6)=π⁶/945.
        assert_equal(&zeta(2).unwrap(), &(CasExpr::rat(1, 6) * pi().pow(2)));
        assert_equal(&zeta(4).unwrap(), &(CasExpr::rat(1, 90) * pi().pow(4)));
        assert_equal(&zeta(6).unwrap(), &(CasExpr::rat(1, 945) * pi().pow(6)));
        // Zero, and negative integers (with trivial zeros at negative evens).
        assert_eq!(zeta(0), Some(CasExpr::rat(-1, 2)));
        assert_eq!(zeta(-1), Some(CasExpr::rat(-1, 12)));
        assert_eq!(zeta(-3), Some(CasExpr::rat(1, 120)));
        assert_eq!(zeta(-2), Some(CasExpr::int(0)));
        assert_eq!(zeta(-4), Some(CasExpr::int(0)));
        // Pole at 1, and no elementary closed form at positive odd ≥ 3.
        assert!(zeta(1).is_none());
        assert!(zeta(3).is_none());
        assert!(zeta(5).is_none());
    }
}
