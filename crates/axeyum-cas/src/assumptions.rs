//! A lightweight assumptions system — sign/domain facts about variables that gate
//! otherwise-unsound rewrites.
//!
//! [`Assumptions`] records per-variable properties (positive, negative, nonzero,
//! …); [`Assumptions::sign_of`] then decides the sign of a compound expression by
//! structural rules (`exp > 0`, `even power ≥ 0`, product-of-signs, …). This is what
//! lets `√(x²) → x` (rather than `|x|`) become *sound* under `x ≥ 0`.

use std::collections::BTreeSet;

use crate::{CasExpr, UnaryFunc};

/// The sign of a real quantity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sign {
    /// Strictly positive (`> 0`).
    Positive,
    /// Strictly negative (`< 0`).
    Negative,
    /// Exactly zero.
    Zero,
    /// `≥ 0` (positive or zero, not further resolved).
    Nonnegative,
    /// `≤ 0` (negative or zero, not further resolved).
    Nonpositive,
    /// Sign not determined.
    Unknown,
}

impl Sign {
    /// Whether this sign guarantees `≥ 0`.
    #[must_use]
    pub fn is_nonnegative(self) -> bool {
        matches!(self, Sign::Positive | Sign::Zero | Sign::Nonnegative)
    }

    /// Whether this sign guarantees `≠ 0`.
    #[must_use]
    pub fn is_nonzero(self) -> bool {
        matches!(self, Sign::Positive | Sign::Negative)
    }

    /// The sign of a product `a·b`.
    fn times(self, other: Sign) -> Sign {
        use Sign::{Negative, Nonnegative, Nonpositive, Positive, Unknown, Zero};
        match (self, other) {
            (Zero, _) | (_, Zero) => Zero,
            (Unknown, _) | (_, Unknown) => Unknown,
            (Positive, x) | (x, Positive) => x,
            (Negative, Negative) => Positive,
            (Negative | Nonpositive, Nonpositive)
            | (Nonpositive, Negative)
            | (Nonnegative, Nonnegative) => Nonnegative,
            (Negative | Nonpositive, Nonnegative) | (Nonnegative, Negative | Nonpositive) => {
                Nonpositive
            }
        }
    }

    /// The additive combination of two summands' signs (conservative).
    fn plus(self, other: Sign) -> Sign {
        use Sign::{Negative, Nonnegative, Nonpositive, Positive, Unknown, Zero};
        match (self, other) {
            (Zero, x) | (x, Zero) => x,
            (Positive, Positive) => Positive,
            (Negative, Negative) => Negative,
            (Positive | Nonnegative, Positive | Nonnegative) => {
                if self == Positive || other == Positive {
                    Positive
                } else {
                    Nonnegative
                }
            }
            (Negative | Nonpositive, Negative | Nonpositive) => {
                if self == Negative || other == Negative {
                    Negative
                } else {
                    Nonpositive
                }
            }
            _ => Unknown,
        }
    }

    /// The sign of `−self`.
    fn negate(self) -> Sign {
        match self {
            Sign::Positive => Sign::Negative,
            Sign::Negative => Sign::Positive,
            Sign::Nonnegative => Sign::Nonpositive,
            Sign::Nonpositive => Sign::Nonnegative,
            other => other,
        }
    }
}

/// Sign/domain assumptions about variables. Built fluently, e.g.
/// `Assumptions::new().positive("x").nonzero("y")`.
#[derive(Debug, Clone, Default)]
pub struct Assumptions {
    positive: BTreeSet<String>,
    negative: BTreeSet<String>,
    nonnegative: BTreeSet<String>,
    nonzero: BTreeSet<String>,
}

impl Assumptions {
    /// An empty assumption set.
    #[must_use]
    pub fn new() -> Assumptions {
        Assumptions::default()
    }

    /// Assume `var > 0`.
    #[must_use]
    pub fn positive(mut self, var: &str) -> Assumptions {
        self.positive.insert(var.to_owned());
        self
    }

    /// Assume `var < 0`.
    #[must_use]
    pub fn negative(mut self, var: &str) -> Assumptions {
        self.negative.insert(var.to_owned());
        self
    }

    /// Assume `var ≥ 0`.
    #[must_use]
    pub fn nonnegative(mut self, var: &str) -> Assumptions {
        self.nonnegative.insert(var.to_owned());
        self
    }

    /// Assume `var ≠ 0`.
    #[must_use]
    pub fn nonzero(mut self, var: &str) -> Assumptions {
        self.nonzero.insert(var.to_owned());
        self
    }

    /// The sign of a variable under these assumptions.
    fn variable_sign(&self, name: &str) -> Sign {
        if self.positive.contains(name) {
            Sign::Positive
        } else if self.negative.contains(name) {
            Sign::Negative
        } else if self.nonnegative.contains(name) {
            Sign::Nonnegative
        } else {
            // `nonzero` alone gives no sign (it only rules out zero elsewhere).
            Sign::Unknown
        }
    }

    /// Whether `name` is known to be nonzero.
    fn variable_nonzero(&self, name: &str) -> bool {
        self.positive.contains(name) || self.negative.contains(name) || self.nonzero.contains(name)
    }

    /// The [`Sign`] of an expression under these assumptions, by structural rules
    /// (`exp > 0`, an even power is `≥ 0`, `|·| ≥ 0`, product/sum of signs, …).
    #[must_use]
    pub fn sign_of(&self, expr: &CasExpr) -> Sign {
        match expr {
            CasExpr::Const(c) => {
                if c.is_zero() {
                    Sign::Zero
                } else if c.numerator() > 0 {
                    Sign::Positive
                } else {
                    Sign::Negative
                }
            }
            CasExpr::Var(name) => self.variable_sign(name),
            CasExpr::Neg(inner) => self.sign_of(inner).negate(),
            CasExpr::Add(terms) => terms
                .iter()
                .map(|t| self.sign_of(t))
                .reduce(Sign::plus)
                .unwrap_or(Sign::Zero),
            CasExpr::Mul(factors) => factors
                .iter()
                .map(|f| self.sign_of(f))
                .reduce(Sign::times)
                .unwrap_or(Sign::Positive),
            CasExpr::Div(a, b) => self.sign_of(a).times(self.sign_of(b)),
            CasExpr::Pow(base, exponent) => {
                let base_sign = self.sign_of(base);
                if exponent % 2 == 0 {
                    // Even power: ≥ 0, and > 0 when the base is nonzero.
                    if self.is_nonzero(base) {
                        Sign::Positive
                    } else {
                        Sign::Nonnegative
                    }
                } else {
                    base_sign
                }
            }
            CasExpr::Unary(UnaryFunc::Exp, _) => Sign::Positive, // exp(x) > 0 always
            CasExpr::Unary(UnaryFunc::Abs, arg) => {
                if self.is_nonzero(arg) {
                    Sign::Positive
                } else {
                    Sign::Nonnegative
                }
            }
            CasExpr::Unary(UnaryFunc::Sqrt, arg) => {
                if self.is_nonzero(arg) && self.sign_of(arg).is_nonnegative() {
                    Sign::Positive
                } else {
                    Sign::Nonnegative // principal root is ≥ 0
                }
            }
            CasExpr::Unary(..) => Sign::Unknown,
        }
    }

    /// Whether `expr` is (provably) strictly positive.
    #[must_use]
    pub fn is_positive(&self, expr: &CasExpr) -> bool {
        self.sign_of(expr) == Sign::Positive
    }

    /// Whether `expr` is (provably) `≥ 0`.
    #[must_use]
    pub fn is_nonnegative(&self, expr: &CasExpr) -> bool {
        self.sign_of(expr).is_nonnegative()
    }

    /// Whether `expr` is (provably) nonzero.
    #[must_use]
    pub fn is_nonzero(&self, expr: &CasExpr) -> bool {
        match expr {
            CasExpr::Const(c) => !c.is_zero(),
            CasExpr::Var(name) => self.variable_nonzero(name),
            CasExpr::Neg(inner) => self.is_nonzero(inner),
            CasExpr::Mul(factors) => factors.iter().all(|f| self.is_nonzero(f)),
            CasExpr::Div(a, b) => self.is_nonzero(a) && self.is_nonzero(b),
            CasExpr::Pow(base, _) => self.is_nonzero(base),
            CasExpr::Unary(UnaryFunc::Exp, _) => true,
            _ => self.sign_of(expr).is_nonzero(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x() -> CasExpr {
        CasExpr::var("x")
    }

    #[test]
    fn constant_and_variable_signs() {
        let a = Assumptions::new().positive("x").negative("y");
        assert_eq!(a.sign_of(&CasExpr::int(3)), Sign::Positive);
        assert_eq!(a.sign_of(&CasExpr::int(-2)), Sign::Negative);
        assert_eq!(a.sign_of(&CasExpr::zero()), Sign::Zero);
        assert_eq!(a.sign_of(&x()), Sign::Positive);
        assert_eq!(a.sign_of(&CasExpr::var("y")), Sign::Negative);
        assert_eq!(a.sign_of(&CasExpr::var("z")), Sign::Unknown);
    }

    #[test]
    fn structural_sign_rules() {
        let a = Assumptions::new().positive("x");
        // exp(x) > 0 regardless.
        assert_eq!(
            Assumptions::new().sign_of(&CasExpr::var("t").exp()),
            Sign::Positive
        );
        // x² ≥ 0, and > 0 when x is nonzero.
        assert_eq!(Assumptions::new().sign_of(&x().pow(2)), Sign::Nonnegative);
        assert_eq!(a.sign_of(&x().pow(2)), Sign::Positive);
        // |x| ≥ 0.
        assert_eq!(Assumptions::new().sign_of(&x().abs()), Sign::Nonnegative);
        // Product of positives is positive; positive·negative is negative.
        assert_eq!(
            a.clone().positive("y").sign_of(&(x() * CasExpr::var("y"))),
            Sign::Positive
        );
        assert_eq!(
            a.negative("z").sign_of(&(x() * CasExpr::var("z"))),
            Sign::Negative
        );
    }

    #[test]
    fn sum_and_nonzero() {
        let a = Assumptions::new().positive("x").positive("y");
        // Sum of positives is positive; x² + 1 > 0.
        assert_eq!(a.sign_of(&(x() + CasExpr::var("y"))), Sign::Positive);
        assert_eq!(
            Assumptions::new().sign_of(&(x().pow(2) + CasExpr::int(1))),
            Sign::Positive
        );
        // Mixed-sign sum is Unknown.
        assert_eq!(
            Assumptions::new()
                .positive("x")
                .negative("y")
                .sign_of(&(x() + CasExpr::var("y"))),
            Sign::Unknown
        );
        // Nonzero propagation.
        assert!(a.is_nonzero(&(x() * CasExpr::var("y"))));
        assert!(!Assumptions::new().is_nonzero(&x()));
        assert!(Assumptions::new().nonzero("x").is_nonzero(&x()));
    }
}
