//! Hyperbolic and inverse-hyperbolic functions, built from `exp`/`ln`/`sqrt`.
//!
//! Each function is defined by its closed exponential (or logarithmic) form
//! rather than a fresh transcendental head, so the results land squarely inside
//! the exp-tower fragment that [`crate::equal`] decides. Because `exp(A+B) =
//! exp(A)·exp(B)`, `exp(2x) = exp(x)²`, `exp(−A) = 1/exp(A)`, and `exp(0) = 1`
//! all fold during normalization, the fundamental hyperbolic identities
//! (`cosh² − sinh² = 1`, the double-angle and addition laws, `eᵘ = cosh u +
//! sinh u`) **certify** through the zero-test rather than merely holding
//! numerically.
//!
//! The inverse functions are the standard logarithmic forms; they are opaque
//! `ln`/`sqrt` atoms to the certifier, so the identities that certify for them
//! are their defining equations.

use crate::CasExpr;

/// Hyperbolic sine `sinh(u) = (eᵘ − e⁻ᵘ)/2`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::hyperbolic::sinh;
/// use axeyum_cas::{CasExpr, equal, ZeroTest};
///
/// let u = CasExpr::var("u");
/// // sinh is odd: sinh(−u) = −sinh(u).
/// let lhs = sinh(&(-u.clone()));
/// let rhs = -sinh(&u);
/// assert!(matches!(equal(&lhs, &rhs), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn sinh(u: &CasExpr) -> CasExpr {
    (u.clone().exp() - (-u.clone()).exp()) / CasExpr::int(2)
}

/// Hyperbolic cosine `cosh(u) = (eᵘ + e⁻ᵘ)/2`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::hyperbolic::cosh;
/// use axeyum_cas::{CasExpr, equal, ZeroTest};
///
/// let u = CasExpr::var("u");
/// // cosh is even: cosh(−u) = cosh(u).
/// let lhs = cosh(&(-u.clone()));
/// let rhs = cosh(&u);
/// assert!(matches!(equal(&lhs, &rhs), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn cosh(u: &CasExpr) -> CasExpr {
    (u.clone().exp() + (-u.clone()).exp()) / CasExpr::int(2)
}

/// Hyperbolic tangent `tanh(u) = sinh(u)/cosh(u)`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::hyperbolic::{cosh, sinh, tanh};
/// use axeyum_cas::{CasExpr, equal, ZeroTest};
///
/// let u = CasExpr::var("u");
/// // tanh(u)·cosh(u) = sinh(u).
/// let lhs = tanh(&u) * cosh(&u);
/// let rhs = sinh(&u);
/// assert!(matches!(equal(&lhs, &rhs), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn tanh(u: &CasExpr) -> CasExpr {
    sinh(u) / cosh(u)
}

/// Hyperbolic cotangent `coth(u) = cosh(u)/sinh(u)` (valid away from `u = 0`).
///
/// # Examples
///
/// ```
/// use axeyum_cas::hyperbolic::{cosh, coth, sinh};
/// use axeyum_cas::{CasExpr, equal, ZeroTest};
///
/// let u = CasExpr::var("u");
/// // coth(u)·sinh(u) = cosh(u).
/// let lhs = coth(&u) * sinh(&u);
/// let rhs = cosh(&u);
/// assert!(matches!(equal(&lhs, &rhs), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn coth(u: &CasExpr) -> CasExpr {
    cosh(u) / sinh(u)
}

/// Hyperbolic secant `sech(u) = 1/cosh(u)`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::hyperbolic::{cosh, sech};
/// use axeyum_cas::{CasExpr, equal, ZeroTest};
///
/// let u = CasExpr::var("u");
/// // sech(u)·cosh(u) = 1.
/// let lhs = sech(&u) * cosh(&u);
/// let rhs = CasExpr::int(1);
/// assert!(matches!(equal(&lhs, &rhs), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn sech(u: &CasExpr) -> CasExpr {
    CasExpr::int(1) / cosh(u)
}

/// Hyperbolic cosecant `csch(u) = 1/sinh(u)` (valid away from `u = 0`).
///
/// # Examples
///
/// ```
/// use axeyum_cas::hyperbolic::{csch, sinh};
/// use axeyum_cas::{CasExpr, equal, ZeroTest};
///
/// let u = CasExpr::var("u");
/// // csch(u)·sinh(u) = 1.
/// let lhs = csch(&u) * sinh(&u);
/// let rhs = CasExpr::int(1);
/// assert!(matches!(equal(&lhs, &rhs), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn csch(u: &CasExpr) -> CasExpr {
    CasExpr::int(1) / sinh(u)
}

/// Inverse hyperbolic sine `asinh(u) = ln(u + √(u² + 1))`.
///
/// # Examples
///
/// ```
/// use axeyum_cas::hyperbolic::asinh;
/// use axeyum_cas::{CasExpr, equal, ZeroTest};
///
/// let u = CasExpr::var("u");
/// // asinh's defining logarithmic form certifies.
/// let lhs = asinh(&u);
/// let rhs = (u.clone() + (u.clone().pow(2) + CasExpr::int(1)).sqrt()).ln();
/// assert!(matches!(equal(&lhs, &rhs), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn asinh(u: &CasExpr) -> CasExpr {
    (u.clone() + (u.clone().pow(2) + CasExpr::int(1)).sqrt()).ln()
}

/// Inverse hyperbolic cosine `acosh(u) = ln(u + √(u² − 1))` (for `u ≥ 1`).
///
/// # Examples
///
/// ```
/// use axeyum_cas::hyperbolic::acosh;
/// use axeyum_cas::{CasExpr, equal, ZeroTest};
///
/// let u = CasExpr::var("u");
/// // acosh's defining logarithmic form certifies.
/// let lhs = acosh(&u);
/// let rhs = (u.clone() + (u.clone().pow(2) - CasExpr::int(1)).sqrt()).ln();
/// assert!(matches!(equal(&lhs, &rhs), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn acosh(u: &CasExpr) -> CasExpr {
    (u.clone() + (u.clone().pow(2) - CasExpr::int(1)).sqrt()).ln()
}

/// Inverse hyperbolic tangent `atanh(u) = ½·ln((1 + u)/(1 − u))` (for `|u| < 1`).
///
/// # Examples
///
/// ```
/// use axeyum_cas::hyperbolic::atanh;
/// use axeyum_cas::{CasExpr, equal, ZeroTest};
///
/// let u = CasExpr::var("u");
/// // 2·atanh(u) = ln((1 + u)/(1 − u)).
/// let lhs = CasExpr::int(2) * atanh(&u);
/// let rhs = ((CasExpr::int(1) + u.clone()) / (CasExpr::int(1) - u.clone())).ln();
/// assert!(matches!(equal(&lhs, &rhs), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn atanh(u: &CasExpr) -> CasExpr {
    CasExpr::rat(1, 2) * ((CasExpr::int(1) + u.clone()) / (CasExpr::int(1) - u.clone())).ln()
}

#[cfg(test)]
mod tests {
    use super::{acosh, asinh, atanh, cosh, coth, csch, sech, sinh, tanh};
    use crate::{CasExpr, ZeroTest, equal};

    /// Whether `a` and `b` are proven equal by the certified zero-test.
    fn certifies(a: &CasExpr, b: &CasExpr) -> bool {
        matches!(equal(a, b), ZeroTest::Certified { equal: true, .. })
    }

    #[test]
    fn hyperbolic_pythagorean_identity() {
        let u = CasExpr::var("u");
        // cosh²u − sinh²u = 1.
        let lhs = cosh(&u).pow(2) - sinh(&u).pow(2);
        assert!(certifies(&lhs, &CasExpr::int(1)));
    }

    #[test]
    fn sinh_double_angle() {
        let u = CasExpr::var("u");
        // sinh(2u) = 2·sinh u·cosh u.
        let lhs = sinh(&(CasExpr::int(2) * u.clone()));
        let rhs = CasExpr::int(2) * sinh(&u) * cosh(&u);
        assert!(certifies(&lhs, &rhs));
    }

    #[test]
    fn cosh_double_angle() {
        let u = CasExpr::var("u");
        let lhs = cosh(&(CasExpr::int(2) * u.clone()));
        // cosh(2u) = cosh²u + sinh²u.
        let rhs_sum = cosh(&u).pow(2) + sinh(&u).pow(2);
        assert!(certifies(&lhs, &rhs_sum));
        // cosh(2u) = 2·cosh²u − 1.
        let rhs_alt = CasExpr::int(2) * cosh(&u).pow(2) - CasExpr::int(1);
        assert!(certifies(&lhs, &rhs_alt));
    }

    #[test]
    fn sinh_addition_law() {
        let a = CasExpr::var("a");
        let b = CasExpr::var("b");
        // sinh(a+b) = sinh a cosh b + cosh a sinh b.
        let lhs = sinh(&(a.clone() + b.clone()));
        let rhs = sinh(&a) * cosh(&b) + cosh(&a) * sinh(&b);
        assert!(certifies(&lhs, &rhs));
    }

    #[test]
    fn cosh_addition_law() {
        let a = CasExpr::var("a");
        let b = CasExpr::var("b");
        // cosh(a+b) = cosh a cosh b + sinh a sinh b.
        let lhs = cosh(&(a.clone() + b.clone()));
        let rhs = cosh(&a) * cosh(&b) + sinh(&a) * sinh(&b);
        assert!(certifies(&lhs, &rhs));
    }

    #[test]
    fn tanh_coth_reciprocal() {
        let u = CasExpr::var("u");
        // tanh(u)·coth(u) = 1 (away from u = 0).
        let lhs = tanh(&u) * coth(&u);
        assert!(certifies(&lhs, &CasExpr::int(1)));
    }

    #[test]
    fn exp_as_cosh_plus_sinh() {
        let u = CasExpr::var("u");
        // eᵘ = cosh u + sinh u.
        let lhs = u.clone().exp();
        let rhs = cosh(&u) + sinh(&u);
        assert!(certifies(&lhs, &rhs));
    }

    #[test]
    fn sech_csch_reciprocals() {
        let u = CasExpr::var("u");
        // sech(u)·cosh(u) = 1 and csch(u)·sinh(u) = 1.
        assert!(certifies(&(sech(&u) * cosh(&u)), &CasExpr::int(1)));
        assert!(certifies(&(csch(&u) * sinh(&u)), &CasExpr::int(1)));
    }

    #[test]
    fn inverse_hyperbolic_definitions() {
        let u = CasExpr::var("u");
        // Defining logarithmic forms certify (opaque ln/sqrt atoms match).
        let asinh_form = (u.clone() + (u.clone().pow(2) + CasExpr::int(1)).sqrt()).ln();
        assert!(certifies(&asinh(&u), &asinh_form));

        let acosh_form = (u.clone() + (u.clone().pow(2) - CasExpr::int(1)).sqrt()).ln();
        assert!(certifies(&acosh(&u), &acosh_form));

        // 2·atanh(u) = ln((1+u)/(1−u)).
        let atanh_form = ((CasExpr::int(1) + u.clone()) / (CasExpr::int(1) - u.clone())).ln();
        assert!(certifies(&(CasExpr::int(2) * atanh(&u)), &atanh_form));
    }

    #[test]
    fn non_identity_must_not_falsely_certify() {
        let u = CasExpr::var("u");
        // cosh(2u) ≠ 2·sinh²u — must NOT certify as equal.
        let lhs = cosh(&(CasExpr::int(2) * u.clone()));
        let rhs = CasExpr::int(2) * sinh(&u).pow(2);
        assert!(!certifies(&lhs, &rhs));
    }
}
