//! Proof-carrying computer algebra — Phase C0: the certified polynomial kernel.
//!
//! This crate is the first slice of the [CAS
//! initiative](../../../docs/research/10-cas/README.md), built under
//! [ADR-0301](../../../docs/research/09-decisions/adr-0301-cas-layer-reduce-to-decide.md):
//! a **broad symbolic algebra layer whose results are certified by lowering to
//! the decidable core**. Here the layer is the polynomial fragment and the
//! certifier is exact rational arithmetic — no solver dependency, oracle-free.
//!
//! The three operations of the kernel, over the polynomial fragment (variables,
//! exact `Rational` constants, `+`, `-`, `*`, and non-negative integer powers):
//!
//! - [`CasExpr::differentiate`] — mechanical sum/product/power differentiation on
//!   the expression tree (returns a new, un-simplified expression);
//! - [`normalize`] — expand an expression to its **canonical multivariate
//!   polynomial** [`MultiPoly`] (a map monomial → nonzero coefficient). The
//!   canonical form is exact and unique, so it *is* a certificate;
//! - [`equal`] — a **decidable zero-test**: normalize `a − b` and check the
//!   result is the zero polynomial. Returns a trust-tagged [`ZeroTest`] whose
//!   `witness` is the difference in canonical form, re-checkable independently.
//!
//! Example — the motivating exemplar `D[x² + c] = 2x`:
//!
//! ```
//! use axeyum_cas::{CasExpr, equal, ZeroTest};
//!
//! let x = CasExpr::var("x");
//! let c = CasExpr::var("c");
//! // x^2 + c
//! let f = CasExpr::pow(x.clone(), 2) + c;
//! // d/dx (x^2 + c)
//! let df = f.differentiate("x");
//! // 2*x
//! let claimed = CasExpr::int(2) * x;
//! match equal(&df, &claimed) {
//!     ZeroTest::Certified { equal, .. } => assert!(equal),
//!     ZeroTest::Unknown => panic!("should be decidable"),
//! }
//! ```
//!
//! Differentiation of the polynomial fragment is decidable and complete, and the
//! zero-test is decidable and exact, so every answer here is `certified` in the
//! sense of
//! [decidability-map.md](../../../docs/research/10-cas/decidability-map.md):
//! `equal` returns a re-checkable polynomial witness. Overflow of the underlying
//! `i128` rational arithmetic is reported as an honest [`ZeroTest::Unknown`],
//! never a wrong answer.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Rational, poly};

pub mod algebraic;
pub mod approx;
pub mod assumptions;
pub mod boolean;
pub mod combinatorics;
mod factor_int;
pub mod geometry;
pub mod gfp;
mod gosper;
pub mod groebner;
pub mod hyperbolic;
pub mod interval_arith;
mod matrix;
pub mod mvpoly;
mod normalforms;
pub mod ntheory;
pub mod ntheory_advanced;
pub mod ntheory_more;
pub mod orthopoly;
pub mod permutation;
mod ratint;
mod series;
pub mod sets;
pub mod special;
pub mod stats;
pub mod sturm;

pub use algebraic::AlgebraicReal;
pub use approx::{lagrange_interpolation, newton_divided_differences, pade, pade_fraction};
pub use assumptions::{Assumptions, Sign};
pub use boolean::BoolExpr;
pub use factor_int::{factor_expr, factor_univariate_over_q};
pub use geometry::{Circle, Line, Point};
pub use gosper::{geometric_power, gosper_sum};
pub use groebner::{groebner_basis, ideal_contains, reduce};
pub use matrix::Matrix;
pub use mvpoly::MvPoly;
pub use normalforms::{hermite_normal_form, smith_normal_form};
pub use orthopoly::{chebyshev_t, chebyshev_u, hermite, laguerre, legendre};
pub use permutation::Permutation;
pub use series::{series, series_at};
pub use sets::{RealSet, finite_set};

/// A symbolic expression over the polynomial fragment (Phase C0).
///
/// This is intentionally minimal: it is the decidable, fully-certifiable core on
/// which later CAS breadth (rational functions, transcendental heads) will build.
/// The tree is not kept in any normal form — [`normalize`] is responsible for the
/// canonical form used to decide equality.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CasExpr {
    /// An exact rational constant.
    Const(Rational),
    /// A named variable or parameter symbol.
    Var(String),
    /// A sum of subexpressions (empty sum denotes `0`).
    Add(Vec<CasExpr>),
    /// A product of subexpressions (empty product denotes `1`).
    Mul(Vec<CasExpr>),
    /// Arithmetic negation.
    Neg(Box<CasExpr>),
    /// A quotient `numerator / denominator` (rational-function fragment). The
    /// denominator must not be identically zero; that is enforced at
    /// normalization time, where a zero denominator yields an honest unknown.
    Div(Box<CasExpr>, Box<CasExpr>),
    /// A non-negative integer power `base^exp`.
    Pow(Box<CasExpr>, u32),
    /// A unary transcendental function applied to an argument, e.g. `ln(u)`,
    /// `exp(u)`, `sin(u)`. Outside the polynomial/rational fragment, but every
    /// such head has a mechanical chain-rule derivative, so expressions built
    /// from them are still differentiable and (where the derivative reduces to a
    /// decidable identity) certifiable.
    Unary(UnaryFunc, Box<CasExpr>),
}

/// A unary transcendental function head (see [`CasExpr::Unary`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryFunc {
    /// Natural logarithm `ln`.
    Ln,
    /// Exponential `exp`.
    Exp,
    /// Sine `sin`.
    Sin,
    /// Cosine `cos`.
    Cos,
    /// Tangent `tan`.
    Tan,
    /// Arctangent `atan`.
    Atan,
    /// Principal square root `sqrt`.
    Sqrt,
    /// Absolute value `abs`.
    Abs,
}

impl UnaryFunc {
    /// The function's display name.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            UnaryFunc::Ln => "ln",
            UnaryFunc::Exp => "exp",
            UnaryFunc::Sin => "sin",
            UnaryFunc::Cos => "cos",
            UnaryFunc::Tan => "tan",
            UnaryFunc::Atan => "atan",
            UnaryFunc::Sqrt => "sqrt",
            UnaryFunc::Abs => "abs",
        }
    }

    /// The chain-rule derivative `d/dx f(u) = f'(u) · du_dx`, given the argument
    /// `arg` (= `u`) and its derivative `arg_deriv` (= `du/dx`).
    fn differentiate(self, arg: &CasExpr, arg_deriv: CasExpr) -> CasExpr {
        let u = || arg.clone();
        // f'(u) as a CasExpr.
        let outer = match self {
            // d/du ln u = 1/u
            UnaryFunc::Ln => CasExpr::int(1) / u(),
            // d/du exp u = exp u
            UnaryFunc::Exp => CasExpr::Unary(UnaryFunc::Exp, Box::new(u())),
            // d/du sin u = cos u
            UnaryFunc::Sin => CasExpr::Unary(UnaryFunc::Cos, Box::new(u())),
            // d/du cos u = -sin u
            UnaryFunc::Cos => -CasExpr::Unary(UnaryFunc::Sin, Box::new(u())),
            // d/du tan u = 1 + tan² u
            UnaryFunc::Tan => {
                CasExpr::int(1) + CasExpr::Unary(UnaryFunc::Tan, Box::new(u())).pow(2)
            }
            // d/du atan u = 1/(1+u²)
            UnaryFunc::Atan => CasExpr::int(1) / (CasExpr::int(1) + u().pow(2)),
            // d/du sqrt u = 1/(2·sqrt u)
            UnaryFunc::Sqrt => {
                CasExpr::int(1) / (CasExpr::int(2) * CasExpr::Unary(UnaryFunc::Sqrt, Box::new(u())))
            }
            // d/du |u| = u/|u| (the sign of u; valid away from u = 0)
            UnaryFunc::Abs => u() / CasExpr::Unary(UnaryFunc::Abs, Box::new(u())),
        };
        CasExpr::Mul(vec![outer, arg_deriv])
    }
}

impl CasExpr {
    /// The integer constant `n`.
    #[must_use]
    pub fn int(n: i128) -> Self {
        CasExpr::Const(Rational::integer(n))
    }

    /// The exact rational constant `num/den`.
    ///
    /// # Panics
    ///
    /// Panics if `den` is zero (a denominator-zero rational is a usage error).
    #[must_use]
    pub fn rat(num: i128, den: i128) -> Self {
        CasExpr::Const(Rational::new(num, den))
    }

    /// The variable named `name`.
    #[must_use]
    pub fn var(name: &str) -> Self {
        CasExpr::Var(name.to_owned())
    }

    /// The constant `0`.
    #[must_use]
    pub fn zero() -> Self {
        CasExpr::Const(Rational::zero())
    }

    /// The constant `1`.
    #[must_use]
    pub fn one() -> Self {
        CasExpr::Const(Rational::integer(1))
    }

    /// `self` raised to a non-negative integer power.
    #[must_use]
    pub fn pow(self, exp: u32) -> Self {
        CasExpr::Pow(Box::new(self), exp)
    }

    /// The natural logarithm of `self`.
    #[must_use]
    pub fn ln(self) -> Self {
        CasExpr::Unary(UnaryFunc::Ln, Box::new(self))
    }

    /// The exponential `exp(self)`.
    #[must_use]
    pub fn exp(self) -> Self {
        CasExpr::Unary(UnaryFunc::Exp, Box::new(self))
    }

    /// The sine of `self`.
    #[must_use]
    pub fn sin(self) -> Self {
        CasExpr::Unary(UnaryFunc::Sin, Box::new(self))
    }

    /// The cosine of `self`.
    #[must_use]
    pub fn cos(self) -> Self {
        CasExpr::Unary(UnaryFunc::Cos, Box::new(self))
    }

    /// The tangent of `self`.
    #[must_use]
    pub fn tan(self) -> Self {
        CasExpr::Unary(UnaryFunc::Tan, Box::new(self))
    }

    /// The arctangent of `self`.
    #[must_use]
    pub fn atan(self) -> Self {
        CasExpr::Unary(UnaryFunc::Atan, Box::new(self))
    }

    /// The principal square root of `self`.
    #[must_use]
    pub fn sqrt(self) -> Self {
        CasExpr::Unary(UnaryFunc::Sqrt, Box::new(self))
    }

    /// The absolute value `|self|`. A constant argument folds to its magnitude
    /// immediately (`|−3| = 3`); otherwise it is the symbolic `abs` head.
    #[must_use]
    pub fn abs(self) -> Self {
        if let CasExpr::Const(value) = self {
            // Denominators are normalized positive, so the sign is the numerator's.
            if value.numerator() >= 0 {
                return CasExpr::Const(value);
            }
            if let Some(magnitude) = value.checked_neg() {
                return CasExpr::Const(magnitude);
            }
        }
        CasExpr::Unary(UnaryFunc::Abs, Box::new(self))
    }

    /// The imaginary unit `I`. It is a reserved symbol: the zero-test ([`equal`])
    /// knows `I² = −1`, so complex-number identities are decidable and certified.
    #[must_use]
    pub fn imaginary_unit() -> Self {
        CasExpr::var("I")
    }

    /// The symbolic derivative of this expression with respect to `var`.
    ///
    /// Applies the mechanical rules — constant, variable, sum, product, and power
    /// — returning a new (un-simplified) expression. Differentiation over the
    /// polynomial fragment is decidable and complete; the result is made
    /// canonical by [`normalize`] and checked by [`equal`].
    #[must_use]
    pub fn differentiate(&self, var: &str) -> CasExpr {
        match self {
            CasExpr::Const(_) => CasExpr::zero(),
            CasExpr::Var(v) => {
                if v == var {
                    CasExpr::one()
                } else {
                    CasExpr::zero()
                }
            }
            CasExpr::Add(terms) => {
                CasExpr::Add(terms.iter().map(|t| t.differentiate(var)).collect())
            }
            CasExpr::Neg(inner) => CasExpr::Neg(Box::new(inner.differentiate(var))),
            CasExpr::Mul(factors) => {
                // Product rule: d(∏ fᵢ) = Σᵢ fᵢ′ · ∏_{j≠i} fⱼ.
                let mut sum_terms = Vec::with_capacity(factors.len());
                for i in 0..factors.len() {
                    let product: Vec<CasExpr> = factors
                        .iter()
                        .enumerate()
                        .map(|(j, f)| {
                            if i == j {
                                f.differentiate(var)
                            } else {
                                f.clone()
                            }
                        })
                        .collect();
                    sum_terms.push(CasExpr::Mul(product));
                }
                CasExpr::Add(sum_terms)
            }
            CasExpr::Div(u, w) => {
                // Quotient rule: d(u/w) = (u′·w − u·w′) / w².
                let numerator = CasExpr::Mul(vec![u.differentiate(var), (**w).clone()])
                    - CasExpr::Mul(vec![(**u).clone(), w.differentiate(var)]);
                CasExpr::Div(Box::new(numerator), Box::new(CasExpr::Pow(w.clone(), 2)))
            }
            CasExpr::Pow(base, exp) => {
                // d(bⁿ) = n · bⁿ⁻¹ · b′ ; d(b⁰) = 0.
                if *exp == 0 {
                    return CasExpr::zero();
                }
                let n = *exp;
                CasExpr::Mul(vec![
                    CasExpr::Const(Rational::integer(i128::from(n))),
                    CasExpr::Pow(base.clone(), n - 1),
                    base.differentiate(var),
                ])
            }
            CasExpr::Unary(func, arg) => func.differentiate(arg, arg.differentiate(var)),
        }
    }

    /// The `n`-th derivative with respect to `var` (`differentiate` applied `n`
    /// times; `n = 0` returns a clone).
    #[must_use]
    pub fn differentiate_n(&self, var: &str, n: usize) -> CasExpr {
        let mut result = self.clone();
        for _ in 0..n {
            // Fold the trivial `0·x`/`1·x`/`x+0` noise the product/chain rules emit
            // between iterations, so repeated differentiation cannot blow up (and
            // `dⁿ/dxⁿ sin x` stays a clean `±sin`/`±cos`). Structure-preserving —
            // no atomization — so radical/trig heads survive.
            result = fold_trivial(&result.differentiate(var));
        }
        result
    }

    /// Substitute every occurrence of `var` with `replacement` (a `subs`-style
    /// substitution).
    ///
    /// Purely structural, and denotation-preserving under the substitution:
    /// `self.substitute(v, r).eval(env) == self.eval(env with v := r.eval(env))`.
    /// The building block for composition, solution-checking, and change of
    /// variables.
    #[must_use]
    pub fn substitute(&self, var: &str, replacement: &CasExpr) -> CasExpr {
        match self {
            CasExpr::Const(_) => self.clone(),
            CasExpr::Var(v) => {
                if v == var {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            CasExpr::Add(terms) => CasExpr::Add(
                terms
                    .iter()
                    .map(|t| t.substitute(var, replacement))
                    .collect(),
            ),
            CasExpr::Mul(factors) => CasExpr::Mul(
                factors
                    .iter()
                    .map(|t| t.substitute(var, replacement))
                    .collect(),
            ),
            CasExpr::Neg(inner) => CasExpr::Neg(Box::new(inner.substitute(var, replacement))),
            CasExpr::Div(u, w) => CasExpr::Div(
                Box::new(u.substitute(var, replacement)),
                Box::new(w.substitute(var, replacement)),
            ),
            CasExpr::Pow(base, exp) => {
                CasExpr::Pow(Box::new(base.substitute(var, replacement)), *exp)
            }
            CasExpr::Unary(func, arg) => {
                CasExpr::Unary(*func, Box::new(arg.substitute(var, replacement)))
            }
        }
    }

    /// Exact evaluation at a rational point assigning every free variable.
    ///
    /// Returns `None` if a variable is unassigned or `i128` rational arithmetic
    /// overflows. Used as an independent, trusted checker in tests (mirroring the
    /// `axeyum-scenarios` self-check philosophy: correctness is confirmed by a
    /// small trusted evaluator, never by a search).
    #[must_use]
    pub fn eval(&self, env: &BTreeMap<String, Rational>) -> Option<Rational> {
        match self {
            CasExpr::Const(r) => Some(*r),
            CasExpr::Var(v) => env.get(v).copied(),
            CasExpr::Add(terms) => terms
                .iter()
                .try_fold(Rational::zero(), |acc, t| acc.checked_add(t.eval(env)?)),
            CasExpr::Mul(factors) => factors
                .iter()
                .try_fold(Rational::integer(1), |acc, f| acc.checked_mul(f.eval(env)?)),
            CasExpr::Neg(inner) => inner.eval(env)?.checked_neg(),
            CasExpr::Div(u, w) => {
                let denom = w.eval(env)?;
                if denom.is_zero() {
                    return None;
                }
                u.eval(env)?.checked_div(denom)
            }
            CasExpr::Pow(base, exp) => {
                let b = base.eval(env)?;
                let mut acc = Rational::integer(1);
                for _ in 0..*exp {
                    acc = acc.checked_mul(b)?;
                }
                Some(acc)
            }
            // Transcendental: no exact rational value.
            CasExpr::Unary(_, _) => None,
        }
    }
}

impl std::ops::Add for CasExpr {
    type Output = CasExpr;
    fn add(self, rhs: CasExpr) -> CasExpr {
        CasExpr::Add(vec![self, rhs])
    }
}

impl std::ops::Sub for CasExpr {
    type Output = CasExpr;
    fn sub(self, rhs: CasExpr) -> CasExpr {
        CasExpr::Add(vec![self, CasExpr::Neg(Box::new(rhs))])
    }
}

impl std::ops::Mul for CasExpr {
    type Output = CasExpr;
    fn mul(self, rhs: CasExpr) -> CasExpr {
        CasExpr::Mul(vec![self, rhs])
    }
}

impl std::ops::Neg for CasExpr {
    type Output = CasExpr;
    fn neg(self) -> CasExpr {
        CasExpr::Neg(Box::new(self))
    }
}

impl std::ops::Div for CasExpr {
    type Output = CasExpr;
    fn div(self, rhs: CasExpr) -> CasExpr {
        CasExpr::Div(Box::new(self), Box::new(rhs))
    }
}

impl std::fmt::Display for CasExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.render(0))
    }
}

impl CasExpr {
    /// Render to a human-readable infix string, parenthesizing where the operator
    /// precedence `min_prec` of the enclosing context requires it. Precedence:
    /// `Add` = 1, `Mul`/`Div`/`Neg` = 2, `Pow` = 3, atoms = 4 (negative/fractional
    /// constants use 2 so they parenthesize inside products/powers).
    fn render(&self, min_prec: u8) -> String {
        let (prec, s): (u8, String) = match self {
            CasExpr::Const(r) => {
                let text = if r.denominator() == 1 {
                    format!("{}", r.numerator())
                } else {
                    format!("{}/{}", r.numerator(), r.denominator())
                };
                let prec = if r.numerator() < 0 || r.denominator() != 1 {
                    2
                } else {
                    4
                };
                (prec, text)
            }
            CasExpr::Var(v) => (4, v.clone()),
            CasExpr::Pow(base, exp) => (3, format!("{}^{exp}", base.render(4))),
            CasExpr::Neg(inner) => (2, format!("-{}", inner.render(3))),
            CasExpr::Mul(factors) => {
                // Pull a leading negative constant sign out front for readability
                // (`-2*I` rather than `(-2)*I`, `-x*y` rather than `(-1)*x*y`).
                let (sign, rendered): (&str, Vec<String>) = match factors.first() {
                    Some(CasExpr::Const(k)) if k.numerator() < 0 => {
                        let mut parts: Vec<String> = Vec::with_capacity(factors.len());
                        if *k != Rational::integer(-1) {
                            parts.push(CasExpr::Const(k.checked_neg().unwrap_or(*k)).render(3));
                        }
                        for factor in &factors[1..] {
                            parts.push(factor.render(3));
                        }
                        if parts.is_empty() {
                            parts.push("1".to_owned());
                        }
                        ("-", parts)
                    }
                    _ => ("", factors.iter().map(|x| x.render(3)).collect()),
                };
                (2, format!("{sign}{}", rendered.join("*")))
            }
            CasExpr::Div(u, w) => (2, format!("{}/{}", u.render(3), w.render(3))),
            CasExpr::Unary(func, arg) => (4, format!("{}({})", func.name(), arg.render(0))),
            CasExpr::Add(terms) => {
                let mut out = String::new();
                for (i, t) in terms.iter().enumerate() {
                    let r = t.render(2);
                    if i == 0 {
                        out.push_str(&r);
                    } else if let Some(rest) = r.strip_prefix('-') {
                        out.push_str(" - ");
                        out.push_str(rest);
                    } else {
                        out.push_str(" + ");
                        out.push_str(&r);
                    }
                }
                (1, out)
            }
        };
        if prec < min_prec { format!("({s})") } else { s }
    }
}

/// A monomial: a product of variable powers, e.g. `x²·y`. Canonical: exponents
/// are all `> 0` and variables are ordered, so structural equality is value
/// equality. The empty monomial is the constant term `1`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
struct Monomial {
    powers: BTreeMap<String, u32>,
}

impl Monomial {
    /// The constant monomial `1`.
    fn one() -> Self {
        Monomial {
            powers: BTreeMap::new(),
        }
    }

    /// The degree-1 monomial in a single variable.
    fn var(name: &str) -> Self {
        let mut powers = BTreeMap::new();
        powers.insert(name.to_owned(), 1);
        Monomial { powers }
    }

    /// The monomial `name^exp` (`exp` assumed ≥ 1).
    fn var_pow(name: &str, exp: u32) -> Self {
        let mut powers = BTreeMap::new();
        powers.insert(name.to_owned(), exp);
        Monomial { powers }
    }

    /// The total degree (sum of exponents); the constant monomial has degree 0.
    fn total_degree(&self) -> u64 {
        self.powers.values().map(|&e| u64::from(e)).sum()
    }

    /// The product of two monomials (add exponents), or `None` on `u32` exponent
    /// overflow.
    fn mul(&self, other: &Monomial) -> Option<Monomial> {
        let mut powers = self.powers.clone();
        for (v, e) in &other.powers {
            let slot = powers.entry(v.clone()).or_insert(0);
            *slot = slot.checked_add(*e)?;
        }
        Some(Monomial { powers })
    }
}

/// A multivariate polynomial with exact rational coefficients, in **canonical
/// form**: a map from monomial to a nonzero coefficient, with zero-coefficient
/// terms removed. Because the form is canonical, equality of two polynomials is
/// structural equality and [`MultiPoly::is_zero`] is exact — this is what makes
/// it a certificate for the zero-test.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MultiPoly {
    terms: BTreeMap<Monomial, Rational>,
}

impl MultiPoly {
    /// The zero polynomial.
    #[must_use]
    pub fn zero() -> Self {
        MultiPoly {
            terms: BTreeMap::new(),
        }
    }

    /// A constant polynomial (empty for `0`).
    #[must_use]
    fn constant(r: Rational) -> Self {
        let mut terms = BTreeMap::new();
        if !r.is_zero() {
            terms.insert(Monomial::one(), r);
        }
        MultiPoly { terms }
    }

    /// The degree-1 polynomial in a single variable.
    #[must_use]
    fn single_var(name: &str) -> Self {
        let mut terms = BTreeMap::new();
        terms.insert(Monomial::var(name), Rational::integer(1));
        MultiPoly { terms }
    }

    /// Returns `true` if this is the zero polynomial.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Reduce powers of the reserved imaginary-unit variable `I` using `I² = −1`,
    /// giving an equivalent polynomial with `I`-degree ≤ 1. Applied by the
    /// zero-test so complex identities decide correctly. `None` on overflow.
    fn fold_imaginary(&self) -> Option<MultiPoly> {
        const IMAG: &str = "I";
        // Fast path: no imaginary unit present.
        if !self.terms.keys().any(|m| m.powers.contains_key(IMAG)) {
            return Some(self.clone());
        }
        let mut out = MultiPoly::zero();
        for (mono, coeff) in &self.terms {
            let exp = mono.powers.get(IMAG).copied().unwrap_or(0);
            // I^exp = (−1)^(exp/2) · I^(exp mod 2).
            let sign = if (exp / 2) % 2 == 0 {
                Rational::integer(1)
            } else {
                Rational::integer(-1)
            };
            let new_coeff = coeff.checked_mul(sign)?;
            let mut powers = mono.powers.clone();
            if exp % 2 == 0 {
                powers.remove(IMAG);
            } else {
                powers.insert(IMAG.to_owned(), 1);
            }
            let mono = Monomial { powers };
            let combined = match out.terms.get(&mono).copied() {
                Some(existing) => existing.checked_add(new_coeff)?,
                None => new_coeff,
            };
            if combined.is_zero() {
                out.terms.remove(&mono);
            } else {
                out.terms.insert(mono, combined);
            }
        }
        Some(out)
    }

    /// Reduce `cos²(u) → 1 − sin²(u)` for every argument `u`, so the zero-test
    /// knows the Pythagorean identity `sin²+cos² = 1`. Sound (reduction modulo the
    /// true relation) and complete for that single relation; other trig identities
    /// (double-angle, sum) are not captured and conservatively fail. `None` on
    /// overflow.
    fn fold_pythagorean(&self) -> Option<MultiPoly> {
        // Fast path: no cosine atom raised to a power ≥ 2.
        let has_cos_sq = self.terms.keys().any(|m| {
            m.powers
                .iter()
                .any(|(var, &e)| e >= 2 && var.starts_with("\0cos:"))
        });
        if !has_cos_sq {
            return Some(self.clone());
        }
        let mut out = MultiPoly::zero();
        for (mono, coeff) in &self.terms {
            // Rebuild the term as a product of per-variable factors, replacing
            // cos(u)^e with cos(u)^(e mod 2)·(1 − sin(u)²)^(e/2).
            let mut term = MultiPoly::constant(*coeff);
            for (var, &exp) in &mono.powers {
                let factor = if let Some(arg) = var.strip_prefix("\0cos:") {
                    let sin_var = format!("\0sin:{arg}");
                    let cos_pow = MultiPoly::single_var_pow(var, exp % 2);
                    let mut one_minus_sin_sq = MultiPoly::constant(Rational::integer(1));
                    let mut sin_sq = MultiPoly::zero();
                    sin_sq
                        .terms
                        .insert(Monomial::var_pow(&sin_var, 2), Rational::integer(-1));
                    one_minus_sin_sq = one_minus_sin_sq.add(&sin_sq)?;
                    cos_pow.mul(&one_minus_sin_sq.pow(exp / 2)?)?
                } else {
                    MultiPoly::single_var_pow(var, exp)
                };
                term = term.mul(&factor)?;
            }
            out = out.add(&term)?;
        }
        Some(out)
    }

    /// The mirror of [`fold_pythagorean`]: reduce `sin(u)^e → sin(u)^(e mod 2)·
    /// (1 − cos(u)²)^(e/2)`, eliminating every squared sine in favour of cosine.
    /// Sound (`sin²u = 1 − cos²u`); used by [`trigsimp`] as the other reduction
    /// direction so the structurally smaller of the two forms can be chosen.
    fn fold_pythagorean_to_cos(&self) -> Option<MultiPoly> {
        let has_sin_sq = self.terms.keys().any(|m| {
            m.powers
                .iter()
                .any(|(var, &e)| e >= 2 && var.starts_with("\0sin:"))
        });
        if !has_sin_sq {
            return Some(self.clone());
        }
        let mut out = MultiPoly::zero();
        for (mono, coeff) in &self.terms {
            let mut term = MultiPoly::constant(*coeff);
            for (var, &exp) in &mono.powers {
                let factor = if let Some(arg) = var.strip_prefix("\0sin:") {
                    let cos_var = format!("\0cos:{arg}");
                    let sin_pow = MultiPoly::single_var_pow(var, exp % 2);
                    let mut one_minus_cos_sq = MultiPoly::constant(Rational::integer(1));
                    let mut cos_sq = MultiPoly::zero();
                    cos_sq
                        .terms
                        .insert(Monomial::var_pow(&cos_var, 2), Rational::integer(-1));
                    one_minus_cos_sq = one_minus_cos_sq.add(&cos_sq)?;
                    sin_pow.mul(&one_minus_cos_sq.pow(exp / 2)?)?
                } else {
                    MultiPoly::single_var_pow(var, exp)
                };
                term = term.mul(&factor)?;
            }
            out = out.add(&term)?;
        }
        Some(out)
    }

    /// Reduce `sqrt(c)² → c` for every square-root atom whose radicand is a
    /// non-negative rational constant, so the zero-test knows exact radical
    /// arithmetic (`√2·√2 = 2`, `(√8/2)² = 2`). Sound: for `c ≥ 0`, `sqrt(c)` is a
    /// real number whose square is exactly `c`. Atoms whose radicand is not a
    /// parseable non-negative rational (e.g. `sqrt(x)`, `sqrt(−3)`) are left
    /// untouched — conservative, never a false reduction. `None` on overflow.
    fn fold_radical(&self) -> Option<MultiPoly> {
        const SQRT: &str = "\0sqrt:";
        let has_sqrt_sq = self.terms.keys().any(|m| {
            m.powers
                .iter()
                .any(|(var, &e)| e >= 2 && var.starts_with(SQRT))
        });
        if !has_sqrt_sq {
            return Some(self.clone());
        }
        let mut out = MultiPoly::zero();
        for (mono, coeff) in &self.terms {
            let mut term = MultiPoly::constant(*coeff);
            for (var, &exp) in &mono.powers {
                let radicand = var
                    .strip_prefix(SQRT)
                    .and_then(parse_rational_render)
                    .filter(|value| value.numerator() >= 0);
                let factor = if let Some(radicand) = radicand {
                    // sqrt(c)^exp = c^(exp/2) · sqrt(c)^(exp mod 2).
                    let mut power = Rational::integer(1);
                    for _ in 0..(exp / 2) {
                        power = power.checked_mul(radicand)?;
                    }
                    MultiPoly::constant(power).mul(&MultiPoly::single_var_pow(var, exp % 2))?
                } else {
                    MultiPoly::single_var_pow(var, exp)
                };
                term = term.mul(&factor)?;
            }
            out = out.add(&term)?;
        }
        Some(out)
    }

    /// The monomial `var^exp` as a one-term polynomial (or the constant `1` when
    /// `exp == 0`).
    fn single_var_pow(var: &str, exp: u32) -> MultiPoly {
        if exp == 0 {
            return MultiPoly::constant(Rational::integer(1));
        }
        let mut terms = BTreeMap::new();
        terms.insert(Monomial::var_pow(var, exp), Rational::integer(1));
        MultiPoly { terms }
    }

    /// Exact polynomial addition, or `None` on `i128` coefficient overflow.
    #[must_use]
    fn add(&self, other: &MultiPoly) -> Option<MultiPoly> {
        let mut out = self.clone();
        for (mono, coeff) in &other.terms {
            let combined = match out.terms.get(mono).copied() {
                Some(existing) => existing.checked_add(*coeff)?,
                None => *coeff,
            };
            if combined.is_zero() {
                out.terms.remove(mono);
            } else {
                out.terms.insert(mono.clone(), combined);
            }
        }
        Some(out)
    }

    /// Exact polynomial negation, or `None` on `i128` overflow.
    #[must_use]
    fn neg(&self) -> Option<MultiPoly> {
        let mut out = MultiPoly::zero();
        for (mono, coeff) in &self.terms {
            out.terms.insert(mono.clone(), coeff.checked_neg()?);
        }
        Some(out)
    }

    /// Exact polynomial multiplication, or `None` on `i128`/`u32` overflow.
    #[must_use]
    fn mul(&self, other: &MultiPoly) -> Option<MultiPoly> {
        let mut out = MultiPoly::zero();
        for (m1, c1) in &self.terms {
            for (m2, c2) in &other.terms {
                let mono = m1.mul(m2)?;
                let coeff = c1.checked_mul(*c2)?;
                let combined = match out.terms.get(&mono).copied() {
                    Some(existing) => existing.checked_add(coeff)?,
                    None => coeff,
                };
                if combined.is_zero() {
                    out.terms.remove(&mono);
                } else {
                    out.terms.insert(mono, combined);
                }
            }
        }
        Some(out)
    }

    /// `self` raised to a non-negative integer power, or `None` on overflow.
    #[must_use]
    fn pow(&self, exp: u32) -> Option<MultiPoly> {
        let mut acc = MultiPoly::constant(Rational::integer(1));
        for _ in 0..exp {
            acc = acc.mul(self)?;
        }
        Some(acc)
    }

    /// If this polynomial involves at most the single variable `var`, returns its
    /// dense coefficient vector (LSB-first: index `i` is the coefficient of
    /// `var^i`), matching the convention of [`axeyum_ir::poly`]. Returns `None`
    /// if any other variable appears, so the caller can fall back.
    #[must_use]
    pub fn to_univariate(&self, var: &str) -> Option<Vec<Rational>> {
        let mut coeffs: Vec<Rational> = Vec::new();
        for (mono, coeff) in &self.terms {
            // A monomial is univariate in `var` iff every variable it mentions is
            // `var`; its exponent there is the term's degree (0 for the constant).
            let mut exp = 0usize;
            for (name, e) in &mono.powers {
                if name != var {
                    return None;
                }
                exp = *e as usize;
            }
            if exp >= coeffs.len() {
                coeffs.resize(exp + 1, Rational::zero());
            }
            coeffs[exp] = *coeff;
        }
        Some(coeffs)
    }

    /// Reconstruct a canonical [`CasExpr`] (expanded sum-of-monomials form) that
    /// denotes this polynomial. The result is value-equal to any expression that
    /// normalizes to `self` — verified by [`equal`] round-tripping to zero.
    #[must_use]
    pub fn to_expr(&self) -> CasExpr {
        if self.terms.is_empty() {
            return CasExpr::zero();
        }
        // Present terms in descending total degree (canonical, SymPy-like), with
        // the monomial order as a stable tiebreak.
        let mut ordered: Vec<(&Monomial, &Rational)> = self.terms.iter().collect();
        ordered.sort_by(|a, b| {
            b.0.total_degree()
                .cmp(&a.0.total_degree())
                .then_with(|| a.0.cmp(b.0))
        });
        let mut sum: Vec<CasExpr> = Vec::with_capacity(ordered.len());
        for (mono, coeff) in ordered {
            let mut factors: Vec<CasExpr> = Vec::new();
            // Emit the coefficient unless it is a bare `1` multiplying a monomial.
            if *coeff != Rational::integer(1) || mono.powers.is_empty() {
                factors.push(CasExpr::Const(*coeff));
            }
            for (var, exp) in &mono.powers {
                let base = CasExpr::Var(var.clone());
                factors.push(if *exp == 1 { base } else { base.pow(*exp) });
            }
            let term = match factors.len() {
                1 => factors.into_iter().next().unwrap_or_else(CasExpr::zero),
                _ => CasExpr::Mul(factors),
            };
            sum.push(term);
        }
        match sum.len() {
            1 => sum.into_iter().next().unwrap_or_else(CasExpr::zero),
            _ => CasExpr::Add(sum),
        }
    }

    /// The set of variables that occur in this polynomial.
    #[must_use]
    fn variables(&self) -> BTreeSet<&str> {
        let mut vars = BTreeSet::new();
        for mono in self.terms.keys() {
            for v in mono.powers.keys() {
                vars.insert(v.as_str());
            }
        }
        vars
    }

    /// Build a polynomial from a dense univariate coefficient vector (LSB-first)
    /// in `var`, matching [`axeyum_ir::poly`] conventions.
    #[must_use]
    fn from_univariate(var: &str, coeffs: &[Rational]) -> MultiPoly {
        let mut terms = BTreeMap::new();
        for (i, coeff) in coeffs.iter().enumerate() {
            if coeff.is_zero() {
                continue;
            }
            let mut powers = BTreeMap::new();
            if i > 0 {
                powers.insert(
                    var.to_owned(),
                    u32::try_from(i).expect("degree fits in u32"),
                );
            }
            terms.insert(Monomial { powers }, *coeff);
        }
        MultiPoly { terms }
    }

    /// The formal antiderivative of this polynomial with respect to `var`:
    /// `∫ (Σ cₘ·mₘ) dvar`, integrating each monomial (`∫ c·varᵏ·… dvar =
    /// c/(k+1)·varᵏ⁺¹·…`). Exact; `None` on overflow. The `+C` constant is
    /// dropped (indefinite integral up to a constant).
    #[must_use]
    fn integrate_in(&self, var: &str) -> Option<MultiPoly> {
        let mut terms = BTreeMap::new();
        for (mono, coeff) in &self.terms {
            let cur = mono.powers.get(var).copied().unwrap_or(0);
            let new_exp = cur.checked_add(1)?;
            let new_coeff = coeff.checked_div(Rational::integer(i128::from(new_exp)))?;
            let mut powers = mono.powers.clone();
            powers.insert(var.to_owned(), new_exp);
            // Distinct input monomials map to distinct output monomials (the var
            // exponent shifts uniformly), so there are no collisions.
            terms.insert(Monomial { powers }, new_coeff);
        }
        Some(MultiPoly { terms })
    }

    /// Exact evaluation at a rational point (trusted checker for tests). `None`
    /// on a missing assignment or `i128` overflow.
    #[must_use]
    pub fn eval(&self, env: &BTreeMap<String, Rational>) -> Option<Rational> {
        let mut total = Rational::zero();
        for (mono, coeff) in &self.terms {
            let mut term = *coeff;
            for (v, e) in &mono.powers {
                let base = *env.get(v)?;
                for _ in 0..*e {
                    term = term.checked_mul(base)?;
                }
            }
            total = total.checked_add(term)?;
        }
        Some(total)
    }
}

/// Expand a [`CasExpr`] to its canonical [`MultiPoly`], or `None` if exact
/// `i128` rational (or `u32` exponent) arithmetic overflows during expansion.
#[must_use]
pub fn normalize(expr: &CasExpr) -> Option<MultiPoly> {
    match expr {
        CasExpr::Const(r) => Some(MultiPoly::constant(*r)),
        CasExpr::Var(v) => Some(MultiPoly::single_var(v)),
        CasExpr::Add(terms) => terms
            .iter()
            .try_fold(MultiPoly::zero(), |acc, t| acc.add(&normalize(t)?)),
        CasExpr::Mul(factors) => factors
            .iter()
            .try_fold(MultiPoly::constant(Rational::integer(1)), |acc, f| {
                acc.mul(&normalize(f)?)
            }),
        CasExpr::Neg(inner) => normalize(inner)?.neg(),
        CasExpr::Pow(base, exp) => normalize(base)?.pow(*exp),
        // A quotient (use [`normalize_rational`]) or a transcendental head is not
        // a polynomial: the polynomial normal form declines.
        CasExpr::Div(..) | CasExpr::Unary(..) => None,
    }
}

/// A rational function in the fragment: a `num / den` pair of canonical
/// polynomials with `den` not identically zero. It is **not** reduced to lowest
/// terms (GCD reduction is a later phase); equality is still decided exactly by
/// cross-multiplication, which does not require a reduced form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RatFunc {
    /// The numerator polynomial.
    num: MultiPoly,
    /// The denominator polynomial (never identically zero).
    den: MultiPoly,
}

impl RatFunc {
    /// The polynomial `p` as `p / 1`.
    fn from_poly(num: MultiPoly) -> Self {
        RatFunc {
            num,
            den: MultiPoly::constant(Rational::integer(1)),
        }
    }

    /// `self + other = (a·d + c·b) / (b·d)`, or `None` on overflow.
    fn add(&self, other: &RatFunc) -> Option<RatFunc> {
        let ad = self.num.mul(&other.den)?;
        let cb = other.num.mul(&self.den)?;
        Some(RatFunc {
            num: ad.add(&cb)?,
            den: self.den.mul(&other.den)?,
        })
    }

    /// `self · other = (a·c) / (b·d)`, or `None` on overflow.
    fn mul(&self, other: &RatFunc) -> Option<RatFunc> {
        Some(RatFunc {
            num: self.num.mul(&other.num)?,
            den: self.den.mul(&other.den)?,
        })
    }

    /// `-self = (-a) / b`, or `None` on overflow.
    fn neg(&self) -> Option<RatFunc> {
        Some(RatFunc {
            num: self.num.neg()?,
            den: self.den.clone(),
        })
    }

    /// `self^exp`, or `None` on overflow.
    fn pow(&self, exp: u32) -> Option<RatFunc> {
        Some(RatFunc {
            num: self.num.pow(exp)?,
            den: self.den.pow(exp)?,
        })
    }

    /// `self / other = (a·d) / (b·c)`. Returns `None` on overflow or if
    /// `other`'s numerator is identically zero (division by zero).
    fn div(&self, other: &RatFunc) -> Option<RatFunc> {
        if other.num.is_zero() {
            return None; // division by the zero function
        }
        Some(RatFunc {
            num: self.num.mul(&other.den)?,
            den: self.den.mul(&other.num)?,
        })
    }

    /// Reduce to lowest terms when the function is univariate (or constant),
    /// using the exact polynomial GCD (`poly::rat_gcd`) and exact division. The
    /// denominator's leading coefficient is normalized positive. Multivariate
    /// functions are returned unchanged (still value-equal; multivariate GCD is a
    /// later phase). `None` on overflow or an exact-division failure.
    fn reduced(&self) -> Option<RatFunc> {
        if self.num.is_zero() {
            return Some(RatFunc::from_poly(MultiPoly::zero()));
        }
        let mut vars = self.num.variables();
        vars.extend(self.den.variables());
        match vars.len() {
            0 => {
                // Both constant: collapse num/den to one rational constant.
                let empty = BTreeMap::new();
                let val = self.num.eval(&empty)?.checked_div(self.den.eval(&empty)?)?;
                Some(RatFunc::from_poly(MultiPoly::constant(val)))
            }
            1 => {
                let var = *vars.iter().next()?;
                let nv = self.num.to_univariate(var)?;
                let dv = self.den.to_univariate(var)?;
                let bound = nv.len() + dv.len() + 4;
                let g = poly::rat_gcd(&nv, &dv, bound)?;
                let mut num = poly::rat_exact_div(&nv, &g)?;
                let mut den = poly::rat_exact_div(&dv, &g)?;
                // Canonicalize the sign: make the denominator's leading coeff > 0.
                if den.last().is_some_and(|l| l.numerator() < 0) {
                    let negate = |v: &[Rational]| -> Option<Vec<Rational>> {
                        v.iter().map(|c| c.checked_neg()).collect()
                    };
                    num = negate(&num)?;
                    den = negate(&den)?;
                }
                Some(RatFunc {
                    num: MultiPoly::from_univariate(var, &num),
                    den: MultiPoly::from_univariate(var, &den),
                })
            }
            _ => {
                // Multivariate: reduce via the multivariate GCD (mvpoly). If any
                // step declines, fall back to the unreduced (still value-equal)
                // fraction rather than failing.
                self.reduced_multivariate().or_else(|| Some(self.clone()))
            }
        }
    }

    /// Reduce a multivariate rational function to lowest terms via the
    /// multivariate GCD ([`mvpoly::MvPoly`]). `None` if any conversion or exact
    /// division declines (the caller then keeps the unreduced form).
    fn reduced_multivariate(&self) -> Option<RatFunc> {
        let num_mv = mvpoly::MvPoly::from_cas_expr(&self.num.to_expr())?;
        let den_mv = mvpoly::MvPoly::from_cas_expr(&self.den.to_expr())?;
        let gcd = num_mv.gcd(&den_mv)?;
        let num_reduced = num_mv.exact_div(&gcd)?;
        let den_reduced = den_mv.exact_div(&gcd)?;
        Some(RatFunc {
            num: normalize(&num_reduced.to_cas_expr())?,
            den: normalize(&den_reduced.to_cas_expr())?,
        })
    }
}

/// Expand a [`CasExpr`] (rational-function fragment) to a [`RatFunc`], or `None`
/// on overflow or a division by an identically-zero denominator.
fn normalize_rational(expr: &CasExpr) -> Option<RatFunc> {
    match expr {
        CasExpr::Const(r) => Some(RatFunc::from_poly(MultiPoly::constant(*r))),
        CasExpr::Var(v) => Some(RatFunc::from_poly(MultiPoly::single_var(v))),
        CasExpr::Add(terms) => {
            let mut acc = RatFunc::from_poly(MultiPoly::zero());
            for t in terms {
                acc = acc.add(&normalize_rational(t)?)?;
            }
            Some(acc)
        }
        CasExpr::Mul(factors) => {
            let mut acc = RatFunc::from_poly(MultiPoly::constant(Rational::integer(1)));
            for f in factors {
                acc = acc.mul(&normalize_rational(f)?)?;
            }
            Some(acc)
        }
        CasExpr::Neg(inner) => normalize_rational(inner)?.neg(),
        CasExpr::Div(u, w) => normalize_rational(u)?.div(&normalize_rational(w)?),
        CasExpr::Pow(base, exp) => normalize_rational(base)?.pow(*exp),
        // Treat `ln(v)` as an opaque atom (a fresh variable keyed by `v`'s
        // canonical rendering). This makes the zero-test **sound**: a zero normal
        // form proves equality (the atoms are independent), while genuine log
        // identities conservatively fail to reduce (→ not certified, never a false
        // certification). It is exactly what lets `d/dx (c·ln v) = c'·ln v + c·v'/v`
        // certify — the spurious `c'·ln v` term drops when `c` is constant.
        CasExpr::Unary(UnaryFunc::Exp, arg) => normalize_exp(arg),
        CasExpr::Unary(func, arg) => Some(RatFunc::from_poly(MultiPoly::single_var(&atom_name(
            func.name(),
            arg,
        )))),
    }
}

/// Normalize `exp(arg)` so the exponent law `exp(A+B) = exp(A)·exp(B)` becomes
/// decidable: the argument is expanded to a polynomial `Σ termᵢ` and `exp` is
/// distributed over the sum into a **product of primitive per-term factors**
/// `∏ exp(termᵢ)`, each keyed on its sign-canonicalized term (a negative term
/// contributing `1/exp(−termᵢ)`). Two spellings of the same exponential — `exp(x+y)`
/// and `exp(x)·exp(y)`, or `exp(−P)·exp(P)` — then reach the same normal form, so
/// the addition/cancellation identities certify (this is what makes
/// integrating-factor ODE solutions self-check). `exp(0) = 1`.
///
/// Sound: `exp` is a homomorphism of `+` into `×`, so the decomposition is exact.
/// Falls back to a single opaque atom when `arg` is outside the polynomial-over-atoms
/// fragment. The *scaling* law `exp(2x) = exp(x)²` is **not** captured (per-term
/// keys keep the coefficient), which is the remaining
/// [exp-tower](../../../docs/research/10-cas/exp-tower.md) work.
/// The value `vᵏ` when a single exp-argument term `coeff · monomial` is exactly
/// `k · ln(v)` for a **positive rational** `v` and integer `k = coeff` — i.e. the
/// exp/ln inverse `exp(k·ln v) = vᵏ`. `None` when the term is not of that shape
/// (sound only for `v > 0`, where `ln v` is real). Debug-logs nothing; pure.
fn exp_ln_inverse(monomial: &Monomial, coeff: Rational) -> Option<Rational> {
    if coeff.denominator() != 1 || monomial.powers.len() != 1 {
        return None;
    }
    let (atom, &power) = monomial.powers.iter().next()?;
    if power != 1 {
        return None;
    }
    let base = atom.strip_prefix("\0ln:").and_then(parse_rational_render)?;
    if base.numerator() <= 0 {
        return None;
    }
    let exponent = coeff.numerator();
    let unit = if exponent < 0 {
        Rational::integer(1).checked_div(base)?
    } else {
        base
    };
    let mut value = Rational::integer(1);
    for _ in 0..exponent.unsigned_abs() {
        value = value.checked_mul(unit)?;
    }
    Some(value)
}

fn normalize_exp(arg: &CasExpr) -> Option<RatFunc> {
    let opaque = || {
        Some(RatFunc::from_poly(MultiPoly::single_var(&atom_name(
            "exp", arg,
        ))))
    };
    // Use the rational-function normal form so transcendental atoms (e.g. `ln`) in the
    // argument are handled; the argument must reduce to a polynomial (denominator 1)
    // to decompose it term-by-term — a genuine fraction like `exp(1/x)` stays opaque.
    let Some(ratio) = normalize_rational(arg) else {
        return opaque();
    };
    if ratio.den != MultiPoly::constant(Rational::integer(1)) {
        return opaque();
    }
    let arg_poly = ratio.num;
    if arg_poly.is_zero() {
        return Some(RatFunc::from_poly(MultiPoly::constant(Rational::integer(
            1,
        )))); // exp(0) = 1
    }
    let one = || RatFunc::from_poly(MultiPoly::constant(Rational::integer(1)));
    let mut result = one();
    for (monomial, coeff) in &arg_poly.terms {
        // exp/ln inverse: exp(k·ln v) = vᵏ for a positive rational v and integer k.
        if let Some(value) = exp_ln_inverse(monomial, *coeff) {
            result = result.mul(&RatFunc::from_poly(MultiPoly::constant(value)))?;
            continue;
        }
        let negative = coeff.numerator() < 0;
        // The primitive atom and the power to raise it to. When the coefficient is a
        // (nonzero) **integer** `c`, key on `exp(monomial)` and use `exp(c·m) =
        // exp(m)^c` — so `exp(2x) = exp(x)²` and `exp(x)·exp(2x) = exp(3x)` decide.
        // Otherwise key on the whole `|coeff|·monomial` term (power 1).
        let (primitive_coeff, power) = if coeff.denominator() == 1 {
            (
                Rational::integer(1),
                u32::try_from(coeff.numerator().unsigned_abs()).ok()?,
            )
        } else {
            let magnitude = if negative {
                coeff.checked_neg()?
            } else {
                *coeff
            };
            (magnitude, 1)
        };
        let mut single = BTreeMap::new();
        single.insert(monomial.clone(), primitive_coeff);
        let atom = MultiPoly::single_var(&atom_name("exp", &MultiPoly { terms: single }.to_expr()));
        let base = if negative {
            // exp(negative term) = 1 / exp(positive term).
            one().div(&RatFunc::from_poly(atom))?
        } else {
            RatFunc::from_poly(atom)
        };
        result = result.mul(&base.pow(power)?)?;
    }
    Some(result)
}

/// A collision-resistant variable name standing for a transcendental atom
/// `head(arg)`, keyed by `arg`'s canonical rendering. The `\0` prefix cannot occur
/// in a user variable name.
fn atom_name(head: &str, arg: &CasExpr) -> String {
    format!("\0{head}:{}", arg.render(0))
}

/// Collect a decoding dictionary `atom_name → Unary(head, arg)` from every
/// transcendental subexpression of `source`. Normalization ([`normalize_rational`])
/// encodes each `Unary` head as an opaque `\0head:render` atom *variable*; this
/// records the original head so [`deatomize`] can rebuild a clean, user-facing
/// form after a `to_expr()` round-trip (which otherwise leaks the raw atom key).
///
/// For `exp`, [`normalize_exp`] additionally splits `exp(Σ termᵢ)` into per-term
/// factors `∏ exp(termᵢ)` (sign-canonicalized), so each additive term of an
/// `exp` argument — and its negation — is registered too.
fn collect_atom_dictionary(source: &CasExpr, dict: &mut BTreeMap<String, CasExpr>) {
    match source {
        CasExpr::Const(_) | CasExpr::Var(_) => {}
        CasExpr::Add(items) | CasExpr::Mul(items) => {
            for item in items {
                collect_atom_dictionary(item, dict);
            }
        }
        CasExpr::Neg(a) | CasExpr::Pow(a, _) => collect_atom_dictionary(a, dict),
        CasExpr::Div(a, b) => {
            collect_atom_dictionary(a, dict);
            collect_atom_dictionary(b, dict);
        }
        CasExpr::Unary(func, arg) => {
            dict.insert(
                atom_name(func.name(), arg),
                CasExpr::Unary(*func, arg.clone()),
            );
            // A Pythagorean reduction (see `trigsimp`) rewrites `cos²u` in terms
            // of `sin u` and vice versa, introducing the *conjugate* trig head on
            // the same argument. Register it so those forms decode cleanly.
            if let Some(conjugate) = match func {
                UnaryFunc::Sin => Some(UnaryFunc::Cos),
                UnaryFunc::Cos => Some(UnaryFunc::Sin),
                _ => None,
            } {
                dict.insert(
                    atom_name(conjugate.name(), arg),
                    CasExpr::Unary(conjugate, arg.clone()),
                );
            }
            if *func == UnaryFunc::Exp
                && let Some(poly) = normalize(arg)
            {
                // `normalize_exp` splits `exp(Σ termᵢ)` into per-term factors,
                // sign-canonicalizing each (a term with negative coefficient is
                // stored as `1/exp(−term)`) and applying the integer-scaling law
                // `exp(c·m) = exp(m)^c` (so `exp(2x)` keys on the primitive
                // `exp(x)`, not `exp(2x)`). Register, for each term, both
                // coefficient signs of the full term *and* of its coefficient-1
                // monomial base, so every canonical key decodes. Negating the
                // *coefficient* reproduces the same `to_expr` rendering used for keys.
                let one = Rational::integer(1);
                for (mono, coeff) in &poly.terms {
                    for base_coeff in [*coeff, one] {
                        for signed in [Some(base_coeff), base_coeff.checked_neg()] {
                            let Some(signed) = signed else { continue };
                            let term = MultiPoly {
                                terms: [(mono.clone(), signed)].into_iter().collect(),
                            }
                            .to_expr();
                            dict.insert(
                                atom_name("exp", &term),
                                CasExpr::Unary(UnaryFunc::Exp, Box::new(term)),
                            );
                        }
                    }
                }
            }
            collect_atom_dictionary(arg, dict);
        }
    }
}

/// Rebuild the transcendental heads that normalization encoded as opaque
/// `\0head:…` atom variables, using `dict` (see [`collect_atom_dictionary`]) as
/// the decoder. An atom absent from `dict` (should not occur for well-formed
/// input) is left as-is rather than guessed at.
fn deatomize(expr: &CasExpr, dict: &BTreeMap<String, CasExpr>) -> CasExpr {
    match expr {
        CasExpr::Var(name) if name.starts_with('\0') => {
            dict.get(name).cloned().unwrap_or_else(|| expr.clone())
        }
        CasExpr::Const(_) | CasExpr::Var(_) => expr.clone(),
        CasExpr::Add(items) => CasExpr::Add(items.iter().map(|e| deatomize(e, dict)).collect()),
        CasExpr::Mul(items) => CasExpr::Mul(items.iter().map(|e| deatomize(e, dict)).collect()),
        CasExpr::Neg(a) => CasExpr::Neg(Box::new(deatomize(a, dict))),
        CasExpr::Pow(a, n) => CasExpr::Pow(Box::new(deatomize(a, dict)), *n),
        CasExpr::Div(a, b) => CasExpr::Div(
            Box::new(deatomize(a, dict)),
            Box::new(deatomize(b, dict)),
        ),
        CasExpr::Unary(func, a) => CasExpr::Unary(*func, Box::new(deatomize(a, dict))),
    }
}

/// Apply [`deatomize`] using a dictionary freshly collected from `source` — the
/// standard post-pass for the user-facing [`expand`]/[`cancel`] transforms so no
/// internal `\0head:…` atom key ever reaches the caller.
fn deatomize_from(result: &CasExpr, source: &CasExpr) -> CasExpr {
    let mut dict = BTreeMap::new();
    collect_atom_dictionary(source, &mut dict);
    deatomize(result, &dict)
}

/// Parse a rational from the canonical rendering of a [`CasExpr::Const`] — an
/// integer `"n"` or a fraction `"n/d"` — or `None` if `text` is not such a literal.
/// Used to recover the radicand of a `sqrt` atom for [`MultiPoly::fold_radical`].
fn parse_rational_render(text: &str) -> Option<Rational> {
    if let Some((numerator, denominator)) = text.split_once('/') {
        Rational::checked_new(numerator.parse().ok()?, denominator.parse().ok()?)
    } else {
        Some(Rational::integer(text.parse().ok()?))
    }
}

/// The trust tag attached to a CAS answer
/// ([decidability-map.md](../../../docs/research/10-cas/decidability-map.md)).
///
/// Phase C0 only ever produces [`Certainty::Certified`] (a witness is attached)
/// or an honest unknown; the other tags exist for later phases.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Certainty {
    /// A checkable witness is attached; the answer re-checks independently.
    Certified,
    /// A complete algorithm produced the answer but no witness is emitted.
    DecidableUncertified,
    /// May fail to find a true answer; never asserts a false one.
    Heuristic,
}

/// The result of a decidable equality / zero-test.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ZeroTest {
    /// Decided exactly: `a − b` expanded to the canonical polynomial `witness`,
    /// and `equal == witness.is_zero()`. The `witness` is a re-checkable
    /// certificate: recompute the normal form and confirm.
    Certified {
        /// Whether the two expressions are equal (the difference is zero).
        equal: bool,
        /// The difference `a − b` in canonical form (the certificate).
        witness: MultiPoly,
    },
    /// Could not decide within exact `i128` rational arithmetic (overflow).
    /// Honest unknown — never a wrong answer.
    Unknown,
}

impl ZeroTest {
    /// The trust tag for this result.
    #[must_use]
    pub fn certainty(&self) -> Certainty {
        match self {
            ZeroTest::Certified { .. } => Certainty::Certified,
            // An overflow-limited zero-test is not heuristic in nature; it is a
            // resource limit. We surface it as `Heuristic` here only to mean
            // "no certificate produced"; callers should branch on the variant.
            ZeroTest::Unknown => Certainty::Heuristic,
        }
    }
}

/// Decide whether two rational-function-fragment expressions are equal.
///
/// The two sides are normalized to `a/b` and `c/d` and compared by
/// **cross-multiplication**: `a/b = c/d` iff `a·d − c·b ≡ 0` as a polynomial
/// (the denominators are non-zero by construction, so no reduced form is
/// required). Over the fragment this is a **complete decision procedure**; the
/// `witness` is the cross-multiplied numerator `a·d − c·b` in canonical form,
/// which is re-checkable independently. Overflow of exact `i128` rational
/// arithmetic yields [`ZeroTest::Unknown`], never a wrong answer.
///
/// # Trigonometric soundness (Euler fallback)
///
/// The core test treats each transcendental head (`sin x`, `cos x`, `tan x`,
/// `cos 2x`, …) as an **independent** atom. That is sound for *asserting
/// equality* (a zero witness means the identity holds for any values of the
/// atoms), but it would be **unsound for asserting inequality** when the atoms
/// are secretly related — `tan x = sin x / cos x`, `cos 2x = 2cos²x − 1`, etc.
/// A naïve nonzero witness in those atoms does not prove `≠`.
///
/// So a *non-equal* core result is only trusted after re-checking on the
/// [`rewrite_exp`] (Euler) canonical form, where every `sin/cos/tan` becomes a
/// complex exponential and the exp-tower reduces distinct atoms to genuinely
/// independent ones (ℚ-linearly-independent exponents ⇒ algebraically
/// independent). `rewrite_exp` is denotation-preserving and the identity on
/// trig-free input, so trig-free results are unchanged. If the Euler re-check
/// cannot decide, a bare (possibly relation-blind) inequality is downgraded to
/// [`ZeroTest::Unknown`] rather than reported as a false certificate.
#[must_use]
pub fn equal(a: &CasExpr, b: &CasExpr) -> ZeroTest {
    let direct = equal_core(a, b);
    // A certified equality is already sound (zero witness ⇒ identity holds).
    if matches!(direct, ZeroTest::Certified { equal: true, .. }) {
        return direct;
    }
    // Otherwise re-check on the Euler canonical form so hidden trig relations
    // are resolved before we would assert `≠`.
    match equal_core(&rewrite_exp(a), &rewrite_exp(b)) {
        certified @ ZeroTest::Certified { .. } => certified,
        // The Euler form could not decide. Never surface a relation-blind
        // inequality: downgrade a core `≠` to `Unknown`, else keep `Unknown`.
        ZeroTest::Unknown => match direct {
            ZeroTest::Certified { equal: false, .. } => ZeroTest::Unknown,
            other => other,
        },
    }
}

/// The core cross-multiplication zero-test (no Euler canonicalization). Treats
/// transcendental heads as independent atoms; see [`equal`] for why the public
/// entry point re-checks a non-equal result on the [`rewrite_exp`] form.
fn equal_core(a: &CasExpr, b: &CasExpr) -> ZeroTest {
    let (Some(ra), Some(rb)) = (normalize_rational(a), normalize_rational(b)) else {
        return ZeroTest::Unknown;
    };
    // a·d − c·b
    let (Some(ad), Some(cb)) = (ra.num.mul(&rb.den), rb.num.mul(&ra.den)) else {
        return ZeroTest::Unknown;
    };
    let Some(neg_cb) = cb.neg() else {
        return ZeroTest::Unknown;
    };
    match ad
        .add(&neg_cb)
        .and_then(|w| w.fold_imaginary())
        .and_then(|w| w.fold_pythagorean())
        .and_then(|w| w.fold_radical())
    {
        Some(witness) => ZeroTest::Certified {
            equal: witness.is_zero(),
            witness,
        },
        None => ZeroTest::Unknown,
    }
}

/// The degree of a univariate polynomial in `var`, or `None` if `expr` is not a
/// univariate polynomial in `var` (the zero polynomial also returns `None`).
#[must_use]
pub fn degree(expr: &CasExpr, var: &str) -> Option<usize> {
    poly::rat_degree(&normalize(expr)?.to_univariate(var)?)
}

/// The coefficient of `var^n` in a univariate polynomial `expr`, as a constant
/// `CasExpr`. `None` if `expr` is not a univariate polynomial in `var`.
#[must_use]
pub fn coeff(expr: &CasExpr, var: &str, n: usize) -> Option<CasExpr> {
    let coeffs = normalize(expr)?.to_univariate(var)?;
    Some(CasExpr::Const(
        coeffs.get(n).copied().unwrap_or_else(Rational::zero),
    ))
}

/// The leading coefficient (of the highest power of `var`) of a univariate
/// polynomial. `None` if `expr` is not a univariate polynomial in `var` or is zero.
#[must_use]
pub fn leading_coeff(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let coeffs = normalize(expr)?.to_univariate(var)?;
    let d = poly::rat_degree(&coeffs)?;
    Some(CasExpr::Const(coeffs[d]))
}

/// The monic greatest common divisor of two univariate polynomials over ℚ.
/// `None` if either argument is not a univariate polynomial in `var` (or on
/// overflow). `gcd(x²−1, x²−2x+1) = x−1`.
#[must_use]
pub fn poly_gcd(a: &CasExpr, b: &CasExpr, var: &str) -> Option<CasExpr> {
    let ca = normalize(a)?.to_univariate(var)?;
    let cb = normalize(b)?.to_univariate(var)?;
    let bound = ca.len() + cb.len() + 4;
    let g = poly::rat_gcd(&ca, &cb, bound)?;
    Some(MultiPoly::from_univariate(var, &g).to_expr())
}

/// The monic least common multiple `lcm(a, b) = a·b / gcd(a, b)` of two univariate
/// polynomials in `var`. `None` if either is not a univariate polynomial, either is
/// zero, or on overflow.
#[must_use]
pub fn poly_lcm(a: &CasExpr, b: &CasExpr, var: &str) -> Option<CasExpr> {
    let ca = normalize(a)?.to_univariate(var)?;
    let cb = normalize(b)?.to_univariate(var)?;
    if ratint::is_zero(&ca) || ratint::is_zero(&cb) {
        return None;
    }
    let bound = ca.len() + cb.len() + 4;
    let gcd = poly::rat_gcd(&ca, &cb, bound)?;
    let product = poly::ratpoly_mul(&ca, &cb)?;
    let lcm = poly::rat_exact_div(&product, &gcd)?;
    // Make monic.
    let degree = poly::rat_degree(&lcm)?;
    let leading = lcm[degree];
    let monic: Vec<Rational> = lcm
        .iter()
        .map(|c| c.checked_div(leading))
        .collect::<Option<_>>()?;
    Some(MultiPoly::from_univariate(var, &monic).to_expr())
}

/// The **content** of a univariate polynomial in `var` — the GCD of its
/// coefficients, made positive (with the sign of the leading coefficient factored
/// into the primitive part). Returns the content as a rational constant `CasExpr`.
/// `None` if `expr` is not a univariate polynomial or is zero.
#[must_use]
pub fn content(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let coeffs = univariate_coeffs(expr, var)?;
    poly::rat_degree(&coeffs)?; // reject zero
    // Content = GCD of numerators / LCM of denominators, sign from leading coeff.
    let mut num_gcd = 0i128;
    let mut den_lcm = 1i128;
    for c in &coeffs {
        if c.is_zero() {
            continue;
        }
        num_gcd = ntheory::gcd(num_gcd, c.numerator());
        den_lcm = poly::lcm_i128(den_lcm, c.denominator())?;
    }
    let value = Rational::checked_new(num_gcd, den_lcm)?;
    Some(CasExpr::Const(value))
}

/// The **primitive part** of a univariate polynomial in `var` — the polynomial
/// divided by its [`content`], made to have a positive leading coefficient. `None`
/// if `expr` is not a univariate polynomial or is zero.
#[must_use]
pub fn primitive_part(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let coeffs = univariate_coeffs(expr, var)?;
    let degree = poly::rat_degree(&coeffs)?;
    let CasExpr::Const(cont) = content(expr, var)? else {
        return None;
    };
    // Divide by the content; flip sign so the leading coefficient is positive.
    let sign = if coeffs[degree].numerator() < 0 {
        Rational::integer(-1)
    } else {
        Rational::integer(1)
    };
    let divisor = cont.checked_mul(sign)?;
    let primitive: Vec<Rational> = coeffs
        .iter()
        .map(|c| c.checked_div(divisor))
        .collect::<Option<_>>()?;
    Some(MultiPoly::from_univariate(var, &primitive).to_expr())
}

/// Whether a univariate polynomial `expr` in `var` is **irreducible over ℚ** (degree
/// ≥ 1 and not a product of two non-constant rational polynomials). `None` if `expr`
/// is not a univariate polynomial in `var` or on overflow.
#[must_use]
pub fn is_irreducible(expr: &CasExpr, var: &str) -> Option<bool> {
    let coeffs = univariate_coeffs(expr, var)?;
    let degree = poly::rat_degree(&coeffs)?;
    if degree == 0 {
        return Some(false); // a nonzero constant is a unit, not irreducible
    }
    // Irreducible iff its factorization over ℚ is a single degree-`degree` factor.
    let factors = factor_univariate_over_q(&coeffs)?;
    let total_multiplicity: u32 = factors
        .iter()
        .filter(|(f, _)| poly::rat_degree(f).unwrap_or(0) >= 1)
        .map(|(_, m)| *m)
        .sum();
    Some(total_multiplicity == 1)
}

/// Polynomial division of univariate polynomials: returns `(quotient, remainder)`
/// with `a = quotient·b + remainder` and `deg remainder < deg b`. `None` if either
/// side is not a univariate polynomial in `var`, `b = 0`, or on overflow.
#[must_use]
pub fn poly_div(a: &CasExpr, b: &CasExpr, var: &str) -> Option<(CasExpr, CasExpr)> {
    let ca = normalize(a)?.to_univariate(var)?;
    let cb = normalize(b)?.to_univariate(var)?;
    if ratint::is_zero(&cb) {
        return None;
    }
    let (quotient, remainder) = ratint::divrem(&ca, &cb)?;
    Some((
        MultiPoly::from_univariate(var, &quotient).to_expr(),
        MultiPoly::from_univariate(var, &remainder).to_expr(),
    ))
}

/// Factor a univariate polynomial over ℚ into its rational linear factors times a
/// remaining (rational-root-free) polynomial — e.g. `x² − 3x + 2 → (x−1)·(x−2)`,
/// `2x² − 6x + 4 → 2·(x−1)·(x−2)`. The result is **certified** equal to the input
/// (re-multiplication zero-test). Returns `None` if `expr` is not a univariate
/// polynomial or on overflow. (Irreducible factors of degree ≥ 2 are left intact;
/// full factorization over ℚ is a later slice.)
#[must_use]
pub fn factor(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let coeffs = poly::rat_trim(normalize(expr)?.to_univariate(var)?);
    if ratint::is_zero(&coeffs) {
        return Some(CasExpr::zero());
    }
    let mut remaining = coeffs;
    let mut factors: Vec<CasExpr> = Vec::new();
    // Peel each rational-root linear factor with its multiplicity: (x − r)^m.
    while poly::rat_degree(&remaining).unwrap_or(0) >= 1 {
        let Some(&root) = ratint::rational_roots(&remaining)?.first() else {
            break;
        };
        let divisor = [root.checked_neg()?, Rational::integer(1)]; // x − root
        let mut multiplicity = 0u32;
        while poly::rat_degree(&remaining).unwrap_or(0) >= 1
            && poly::eval_rat_poly(&remaining, root)?.is_zero()
        {
            remaining = poly::rat_exact_div(&remaining, &divisor)?;
            multiplicity += 1;
        }
        let linear = CasExpr::var(var) - CasExpr::Const(root);
        factors.push(if multiplicity == 1 {
            linear
        } else {
            linear.pow(multiplicity)
        });
    }
    // A non-unit remaining factor (leading constant or an irreducible ≥2).
    if remaining != vec![Rational::integer(1)] {
        factors.push(MultiPoly::from_univariate(var, &remaining).to_expr());
    }
    let factored = match factors.len() {
        0 => return Some(CasExpr::one()),
        1 => factors.into_iter().next()?,
        _ => CasExpr::Mul(factors),
    };
    match equal(&factored, expr) {
        ZeroTest::Certified { equal: true, .. } => Some(factored),
        _ => None,
    }
}

/// Solve a **square system of linear equations** `equationsᵢ = 0` (each linear in
/// `vars`) for the variables `vars`, by exact Gaussian elimination on the coefficient
/// matrix `A·x = b` (`Aᵢⱼ = ∂eqᵢ/∂varⱼ`, `bᵢ = −eqᵢ(0)`). Returns the assignment
/// `(name, value)` per variable. Requires `equations.len() == vars.len()`, all
/// equations affine in `vars` with rational-constant coefficients, and a unique
/// solution; `None` otherwise.
///
/// ```
/// use axeyum_cas::{CasExpr, solve_linear_system};
/// let x = CasExpr::var("x");
/// let y = CasExpr::var("y");
/// // x + y = 3, x − y = 1  ⇒  x = 2, y = 1.
/// let sol = solve_linear_system(
///     &[x.clone() + y.clone() - CasExpr::int(3), x - y - CasExpr::int(1)],
///     &["x", "y"],
/// )
/// .unwrap();
/// assert_eq!(sol, vec![("x".to_string(), CasExpr::int(2)), ("y".to_string(), CasExpr::int(1))]);
/// ```
#[must_use]
pub fn solve_linear_system(equations: &[CasExpr], vars: &[&str]) -> Option<Vec<(String, CasExpr)>> {
    let n = vars.len();
    if n == 0 || equations.len() != n {
        return None;
    }
    let mut a_rows: Vec<Vec<CasExpr>> = Vec::with_capacity(n);
    let mut b_rows: Vec<Vec<CasExpr>> = Vec::with_capacity(n);
    for equation in equations {
        // Coefficient of each variable = ∂/∂var (constant iff the equation is affine).
        let mut row = Vec::with_capacity(n);
        for var in vars {
            let coeff = equation.differentiate(var);
            row.push(expand(&coeff)?);
        }
        a_rows.push(row);
        // Constant term = the equation with every variable set to 0; b = −constant.
        let mut constant = equation.clone();
        for var in vars {
            constant = constant.substitute(var, &CasExpr::zero());
        }
        let negated = expand(&(-constant))?;
        b_rows.push(vec![negated]);
    }
    let solution = Matrix::from_rows(a_rows)?.solve(&Matrix::from_rows(b_rows)?)?;
    let mut result = Vec::with_capacity(n);
    for (i, var) in vars.iter().enumerate() {
        result.push(((*var).to_owned(), solution.get(i, 0)?.clone()));
    }
    Some(result)
}

/// Match a term `A·f(a·var + b)` where `f ∈ {exp, ln}`, `A` is a rational-constant
/// coefficient and the argument is linear in `var` (`a ≠ 0`). Returns
/// `(f, A, a, b)`. `None` for any other shape (no such head, non-linear argument,
/// non-constant coefficient).
fn match_scaled_unary(term: &CasExpr, var: &str) -> Option<(UnaryFunc, Rational, Rational, Rational)> {
    let mut coeff = Rational::integer(1);
    let mut head: Option<(UnaryFunc, Rational, Rational)> = None;
    for factor in flatten_mul(term) {
        match factor {
            CasExpr::Const(c) => coeff = coeff.checked_mul(c)?,
            CasExpr::Unary(func @ (UnaryFunc::Exp | UnaryFunc::Ln), arg) if head.is_none() => {
                let arg_poly = normalize(&arg)?.to_univariate(var)?;
                if poly::rat_degree(&arg_poly)? != 1 {
                    return None;
                }
                let a = arg_poly[1];
                let b = arg_poly.first().copied().unwrap_or_else(Rational::zero);
                head = Some((func, a, b));
            }
            _ => return None, // a second head, or a non-constant/non-linear factor
        }
    }
    let (func, a, b) = head?;
    Some((func, coeff, a, b))
}

/// The exact rational value of a **variable-free constant** expression (`5`,
/// `−8`, `3/2`, `2·3`), or `None` if it contains any variable or is outside the
/// rational fragment.
fn constant_term(expr: &CasExpr) -> Option<Rational> {
    let poly = normalize(expr)?;
    if poly.terms.keys().any(|m| !m.powers.is_empty()) {
        return None; // contains a variable
    }
    Some(
        poly.terms
            .iter()
            .find(|(m, _)| m.powers.is_empty())
            .map_or_else(Rational::zero, |(_, c)| *c),
    )
}

/// Solve an elementary transcendental equation `A·f(a·var+b) + C = 0` for a single
/// `exp`/`ln` head (`f`), rational constants `A, C`, and a linear inner argument.
/// `exp`: `var = (ln(−C/A) − b)/a` (real when `−C/A > 0`); `ln`: `var =
/// (e^{−C/A} − b)/a`. Certified by substituting the root back (`equal`, using the
/// exp-tower `e^{ln v}=v`). `None` if `expr` is not of this shape (e.g. a
/// polynomial, so the caller proceeds to the polynomial solver) or has no real root.
fn solve_transcendental(expr: &CasExpr, var: &str) -> Option<Vec<CasExpr>> {
    let terms = match expr {
        CasExpr::Add(terms) => terms.clone(),
        other => vec![other.clone()],
    };
    let mut head: Option<(UnaryFunc, Rational, Rational, Rational)> = None;
    let mut constant = Rational::zero();
    for term in &terms {
        if let Some(matched) = match_scaled_unary(term, var) {
            if head.is_some() {
                return None; // more than one transcendental term — unsupported
            }
            head = Some(matched);
        } else {
            // Otherwise a var-free constant term (`5`, `−8`, `3/2`, …); a
            // var-dependent non-transcendental term declines the whole match.
            constant = constant.checked_add(constant_term(term)?)?;
        }
    }
    let (func, big_a, a, b) = head?;
    // f(u) = −C/A.
    let target = constant.checked_neg()?.checked_div(big_a)?;
    let inner = match func {
        UnaryFunc::Exp => {
            if target.numerator() <= 0 {
                return None; // exp is strictly positive — no real solution
            }
            CasExpr::Const(target).ln() // u = ln(target)
        }
        UnaryFunc::Ln => CasExpr::Const(target).exp(), // u = exp(target)
        _ => return None,
    };
    // a·var + b = inner  ⇒  var = (inner − b)/a.
    let shifted = if b.is_zero() {
        inner.clone()
    } else {
        inner.clone() - CasExpr::Const(b)
    };
    let root = if a == Rational::integer(1) {
        shifted
    } else {
        fold_trivial(&(shifted / CasExpr::Const(a)))
    };
    // Two-part certificate (avoids the rational-argument `exp(3·(ln4/3))` that the
    // exp-tower would not reduce after a naïve substitute-back):
    //   (1) the head reduces exactly — `f(inner) = target` — and
    //   (2) the root links back — `a·root + b = inner` (an exact rational identity).
    // Together with `target = −C/A` these give `A·f(a·root+b)+C = A·target+C = 0`.
    // The exp-tower reduces `exp(ln target)=target`; the inverse `ln(exp target)`
    // is not reduced, so `ln` roots honestly fail here and are declined.
    let head_reduces = matches!(
        equal(
            &CasExpr::Unary(func, Box::new(inner.clone())),
            &CasExpr::Const(target)
        ),
        ZeroTest::Certified { equal: true, .. }
    );
    let recovered = fold_trivial(&(CasExpr::Const(a) * root.clone() + CasExpr::Const(b)));
    let links_back = matches!(
        equal(&recovered, &inner),
        ZeroTest::Certified { equal: true, .. }
    );
    if head_reduces && links_back {
        Some(vec![fold_trivial(&fold_elementary_constants(&root))])
    } else {
        None
    }
}

/// The coefficient of `yⁱ` in a polynomial `f`, as a [`CasExpr`] in the remaining
/// variables: `[∂ⁱ_y f / i!]|_{y=0}`. (Uses the differentiate/substitute kernels,
/// so it is exact for polynomial `f`.)
fn coefficient_in(f: &CasExpr, y: &str, i: u32) -> Option<CasExpr> {
    let derivative = f.differentiate_n(y, usize::try_from(i).ok()?);
    let at_zero = derivative.substitute(y, &CasExpr::zero());
    let factorial = ntheory::factorial(i128::from(i))?;
    Some(simplify(&(at_zero / CasExpr::Const(Rational::integer(factorial)))))
}

/// Solve a **system of two polynomial equations** `f(x,y)=0`, `g(x,y)=0` for the
/// variables `xvar, yvar`, by **resultant elimination**: the Sylvester resultant
/// `R(x) = Res_y(f, g)` (a determinant of `CasExpr` coefficient entries, so it
/// carries the `x`-polynomial coefficients exactly) vanishes at every common root's
/// `x`-coordinate. Each rational/quadratic `x`-root is back-substituted and the
/// resulting univariate equation solved for `y`; only pairs that satisfy **both**
/// equations — certified by the zero-test — are returned (distinct, sorted by the
/// order found). `None` if either input is not a polynomial in these two variables,
/// if elimination degenerates (a shared factor makes `R ≡ 0`), or on overflow.
///
/// Solutions with **irrational coordinates** are dropped (honest under-
/// approximation): once an irrational `x` is back-substituted, the univariate
/// equation in `y` has surd coefficients that fall outside the rational [`solve`].
/// Systems whose solutions are rational (or whose `x`-coordinates are rational)
/// are returned in full and certified.
///
/// ```
/// use axeyum_cas::{CasExpr, solve_polynomial_system, equal, ZeroTest};
/// let x = CasExpr::var("x");
/// let y = CasExpr::var("y");
/// // Circle ∩ hyperbola: x²+y²=25, x²−y²=7  ⇒  (±4, ±3).
/// let sols = solve_polynomial_system(
///     &(x.clone().pow(2) + y.clone().pow(2) - CasExpr::int(25)),
///     &(x.clone().pow(2) - y.clone().pow(2) - CasExpr::int(7)),
///     "x",
///     "y",
/// ).unwrap();
/// assert_eq!(sols.len(), 4);
/// ```
#[must_use]
pub fn solve_polynomial_system(
    f: &CasExpr,
    g: &CasExpr,
    xvar: &str,
    yvar: &str,
) -> Option<Vec<(CasExpr, CasExpr)>> {
    // Both must be bivariate polynomials in {xvar, yvar}.
    let f_mv = mvpoly::MvPoly::from_cas_expr(f)?;
    let g_mv = mvpoly::MvPoly::from_cas_expr(g)?;
    let allowed = [xvar.to_owned(), yvar.to_owned()].into_iter().collect();
    if !f_mv.variables().is_subset(&allowed) || !g_mv.variables().is_subset(&allowed) {
        return None;
    }
    let deg_f = f_mv.degree_in(yvar);
    let deg_g = g_mv.degree_in(yvar);
    if deg_f == 0 || deg_g == 0 {
        return None; // need genuine y-dependence in both to eliminate y
    }
    // Sylvester matrix of f, g as polynomials in y (coefficients are CasExpr in x).
    let f_coeffs = collect_y_coefficients(f, yvar, deg_f)?; // LSB-first
    let g_coeffs = collect_y_coefficients(g, yvar, deg_g)?;
    let resultant = sylvester_determinant_expr(&f_coeffs, &g_coeffs)?;
    // R(x) = 0 at every common root's x-coordinate.
    let x_roots = solve(&simplify(&resultant), xvar)?;
    let mut solutions: Vec<(CasExpr, CasExpr)> = Vec::new();
    for x_root in x_roots {
        // Only x-roots we can substitute exactly (rational or exact surd) are useful;
        // substitute and solve the (now univariate) equation in y.
        let f_at = simplify(&f.substitute(xvar, &x_root));
        let Some(y_candidates) = solve(&f_at, yvar) else {
            continue;
        };
        for y_root in y_candidates {
            // Certify the pair against BOTH equations.
            let f_val = f.substitute(xvar, &x_root).substitute(yvar, &y_root);
            let g_val = g.substitute(xvar, &x_root).substitute(yvar, &y_root);
            let both_zero = matches!(
                equal(&f_val, &CasExpr::zero()),
                ZeroTest::Certified { equal: true, .. }
            ) && matches!(
                equal(&g_val, &CasExpr::zero()),
                ZeroTest::Certified { equal: true, .. }
            );
            if both_zero {
                let pair = (x_root.clone(), y_root);
                if !solutions.contains(&pair) {
                    solutions.push(pair);
                }
            }
        }
    }
    Some(solutions)
}

/// The `y`-coefficient vector (LSB-first, length `degree+1`) of a bivariate
/// polynomial `f`, each entry a [`CasExpr`] in the other variable.
fn collect_y_coefficients(f: &CasExpr, yvar: &str, degree: u32) -> Option<Vec<CasExpr>> {
    (0..=degree).map(|i| coefficient_in(f, yvar, i)).collect()
}

/// The Sylvester resultant of two polynomials given by their (LSB-first)
/// [`CasExpr`] coefficient vectors, as the determinant of the `(m+n)×(m+n)`
/// Sylvester matrix — computed symbolically so polynomial coefficients are
/// retained. `None` if either polynomial is constant or on a determinant failure.
fn sylvester_determinant_expr(a: &[CasExpr], b: &[CasExpr]) -> Option<CasExpr> {
    let m = a.len().checked_sub(1)?; // deg a
    let n = b.len().checked_sub(1)?; // deg b
    if m == 0 || n == 0 {
        return None;
    }
    let size = m + n;
    // Rows: n shifted copies of a (MSB-first), then m shifted copies of b.
    let mut rows: Vec<Vec<CasExpr>> = Vec::with_capacity(size);
    let msb = |coeffs: &[CasExpr]| -> Vec<CasExpr> { coeffs.iter().rev().cloned().collect() };
    let a_msb = msb(a);
    let b_msb = msb(b);
    for shift in 0..n {
        let mut row = vec![CasExpr::zero(); size];
        for (j, coeff) in a_msb.iter().enumerate() {
            row[shift + j] = coeff.clone();
        }
        rows.push(row);
    }
    for shift in 0..m {
        let mut row = vec![CasExpr::zero(); size];
        for (j, coeff) in b_msb.iter().enumerate() {
            row[shift + j] = coeff.clone();
        }
        rows.push(row);
    }
    Matrix::from_rows(rows)?.determinant()
}

/// Solve a **trigonometric equation** `A·f(var) + C = 0` for a single `sin`/`cos`/
/// `tan` head with a bare `var` argument and rational constants `A, C`: returns the
/// **principal solutions in `[0, 2π)`** — the special angles `k·π/12` whose
/// `f`-value equals `−C/A` — each certified by substitution + [`evaluate_trig`].
/// `None` if `expr` is not of this shape or the target value is not attained at a
/// tabulated angle. The full solution family is these values plus the head's period.
fn solve_trigonometric(expr: &CasExpr, var: &str) -> Option<Vec<CasExpr>> {
    // Match A·f(var) + C with exactly one trig head on a bare `var`.
    let terms = match expr {
        CasExpr::Add(terms) => terms.clone(),
        other => vec![other.clone()],
    };
    let mut func: Option<UnaryFunc> = None;
    let mut coeff = Rational::integer(1);
    let mut constant = Rational::zero();
    for term in &terms {
        // A variable-free constant term (`5`, `−1`, `3/2`, …) goes to the constant.
        if let Some(c) = constant_term(term) {
            constant = constant.checked_add(c)?;
            continue;
        }
        // Otherwise the term must be `A·f(var)` with a single trig head.
        let mut trig_here: Option<UnaryFunc> = None;
        let mut term_coeff = Rational::integer(1);
        for factor in flatten_mul(term) {
            match factor {
                CasExpr::Const(c) => term_coeff = term_coeff.checked_mul(c)?,
                CasExpr::Unary(f @ (UnaryFunc::Sin | UnaryFunc::Cos | UnaryFunc::Tan), arg)
                    if trig_here.is_none() && matches!(&*arg, CasExpr::Var(v) if v == var) =>
                {
                    trig_here = Some(f);
                }
                _ => return None, // non-constant/non-trig factor, or a second head
            }
        }
        if func.is_some() {
            return None; // more than one trig term
        }
        func = Some(trig_here?);
        coeff = term_coeff;
    }
    let func = func?;
    let target = constant.checked_neg()?.checked_div(coeff)?; // f(var) = −C/A
    let pi = CasExpr::var("pi");
    let mut roots: Vec<CasExpr> = Vec::new();
    // Scan the tabulated angles k·π/12 in [0, 2π): k = 0..24.
    for k in 0..24u32 {
        let angle = fold_trivial(&(CasExpr::Const(Rational::new(i128::from(k), 12)) * pi.clone()));
        let value = evaluate_trig(&CasExpr::Unary(func, Box::new(angle.clone())));
        // Skip `tan` poles (value stays an unevaluated `tan(...)`) and non-matches.
        if matches!(value, CasExpr::Unary(_, _)) {
            continue;
        }
        if matches!(
            equal(&value, &CasExpr::Const(target)),
            ZeroTest::Certified { equal: true, .. }
        ) {
            // Certify against the original equation.
            let residual = expr.substitute(var, &angle);
            if matches!(
                equal(&evaluate_trig(&residual), &CasExpr::zero()),
                ZeroTest::Certified { equal: true, .. }
            ) && !roots.contains(&angle)
            {
                roots.push(angle);
            }
        }
    }
    if roots.is_empty() { None } else { Some(roots) }
}

/// Solve `expr = 0` for `var`. Over a univariate polynomial: returns the distinct
/// real roots (rational roots exact; a leftover real quadratic via the quadratic
/// formula, rational or symbolic `sqrt`; complex roots and irreducible cubics+
/// omitted). Also solves elementary transcendental equations `A·exp(ax+b)+C=0`
/// and `A·ln(ax+b)+C=0` (e.g. `eˣ−5 ⇒ ln 5`). `None` if `expr` is outside both.
#[must_use]
pub fn solve(expr: &CasExpr, var: &str) -> Option<Vec<CasExpr>> {
    // Elementary transcendental equations `A·exp(ax+b)+C=0`, `A·ln(ax+b)+C=0`
    // fall outside the polynomial fragment; try them first.
    if let Some(roots) = solve_transcendental(expr, var) {
        return Some(roots);
    }
    // Trigonometric equations `A·f(var)+C=0` (f ∈ {sin,cos,tan}) — principal
    // solutions in [0, 2π) from the special-angle table.
    if let Some(roots) = solve_trigonometric(expr, var) {
        return Some(roots);
    }
    let mut remaining = poly::rat_trim(normalize(expr)?.to_univariate(var)?);
    poly::rat_degree(&remaining)?; // reject the zero polynomial (every x is a root)
    let mut roots: Vec<CasExpr> = Vec::new();
    let mut seen: Vec<Rational> = Vec::new();
    let push_rational = |r: Rational, roots: &mut Vec<CasExpr>, seen: &mut Vec<Rational>| {
        if !seen.contains(&r) {
            seen.push(r);
            roots.push(CasExpr::Const(r));
        }
    };
    while poly::rat_degree(&remaining).unwrap_or(0) >= 1 {
        let Some(&root) = ratint::rational_roots(&remaining)?.first() else {
            break;
        };
        remaining = poly::rat_exact_div(&remaining, &[root.checked_neg()?, Rational::integer(1)])?;
        push_rational(root, &mut roots, &mut seen);
    }
    // Leftover of degree ≥ 2 (no rational roots left). Degree 2 is solved directly;
    // higher degree is factored over ℚ and each quadratic factor solved — so
    // products of irreducible quadratics (e.g. `(x²+1)(x²+2)`) are fully solved.
    let push_root = |root: CasExpr, roots: &mut Vec<CasExpr>| {
        if !roots.contains(&root) {
            roots.push(root);
        }
    };
    match poly::rat_degree(&remaining) {
        Some(2) => {
            for root in quadratic_roots(remaining[2], remaining[1], remaining[0])? {
                push_root(root, &mut roots);
            }
        }
        Some(degree) if degree >= 3 => {
            for (factor, _multiplicity) in factor_univariate_over_q(&remaining)? {
                match poly::rat_degree(&factor) {
                    Some(1) => {
                        let root = factor[0].checked_neg()?.checked_div(factor[1])?;
                        push_root(CasExpr::Const(root), &mut roots);
                    }
                    Some(2) => {
                        for root in quadratic_roots(factor[2], factor[1], factor[0])? {
                            push_root(root, &mut roots);
                        }
                    }
                    // Irreducible cubic or higher: no general radical solution here.
                    _ => {}
                }
            }
        }
        _ => {}
    }
    Some(roots)
}

/// A comparison operator for polynomial inequality solving.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InequalityOp {
    /// `> 0`
    Greater,
    /// `≥ 0`
    GreaterEqual,
    /// `< 0`
    Less,
    /// `≤ 0`
    LessEqual,
}

/// A real interval with rational (or infinite) endpoints and open/closed bounds,
/// as returned by [`solve_polynomial_inequality`]. `None` endpoints are `∓∞`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RealInterval {
    /// Lower endpoint (`None` = `−∞`).
    pub lower: Option<Rational>,
    /// Whether the lower endpoint is included.
    pub lower_closed: bool,
    /// Upper endpoint (`None` = `+∞`).
    pub upper: Option<Rational>,
    /// Whether the upper endpoint is included.
    pub upper_closed: bool,
}

/// Solve a polynomial inequality `p(var) ⋈ 0` (with `⋈` from [`InequalityOp`]) over
/// the reals, returning the solution as a union of disjoint [`RealInterval`]s
/// (ascending). Implemented by a **sign chart**: the real roots partition ℝ into
/// regions of constant sign, each tested at an interior sample point.
///
/// Requires all real roots to be **rational** (so the interval endpoints are exact
/// rationals — the common textbook case); returns `None` if any real root is
/// irrational (endpoints would not be exactly representable), if `p` is not a
/// univariate polynomial in `var`, or on overflow. An empty vector means no real
/// number satisfies the inequality.
///
/// ```
/// use axeyum_cas::{CasExpr, solve_polynomial_inequality, InequalityOp};
/// let x = CasExpr::var("x");
/// // x² − 5x + 6 > 0  ⇒  (−∞, 2) ∪ (3, ∞).
/// let p = x.clone().pow(2) - CasExpr::int(5) * x + CasExpr::int(6);
/// let solution = solve_polynomial_inequality(&p, "x", InequalityOp::Greater).unwrap();
/// assert_eq!(solution.len(), 2);
/// ```
#[must_use]
pub fn solve_polynomial_inequality(
    expr: &CasExpr,
    var: &str,
    op: InequalityOp,
) -> Option<Vec<RealInterval>> {
    let coeffs = univariate_coeffs(expr, var)?;
    poly::rat_degree(&coeffs)?; // reject the zero polynomial
    // Distinct rational roots, sorted. If the polynomial has any irrational real
    // root, its rational-endpoint interval form is not exact → decline.
    let mut roots: Vec<Rational> = Vec::new();
    for root in solve(expr, var)? {
        if let CasExpr::Const(value) = root
            && !roots.contains(&value)
        {
            roots.push(value);
        }
    }
    roots.sort_unstable();
    // Every rational root must be accounted for: if the count of real roots
    // (Sturm) exceeds the rational roots found, an irrational real root exists.
    let total_real = sturm::count_real_roots_in(
        &coeffs,
        roots
            .first()
            .copied()
            .unwrap_or(Rational::zero())
            .checked_sub(root_span(&coeffs)?)?,
        roots
            .last()
            .copied()
            .unwrap_or(Rational::zero())
            .checked_add(root_span(&coeffs)?)?,
    )?;
    if total_real != roots.len() {
        return None; // an irrational real root is present
    }
    let strict = matches!(op, InequalityOp::Greater | InequalityOp::Less);
    let want_positive = matches!(op, InequalityOp::Greater | InequalityOp::GreaterEqual);

    // Sample the sign in each region delimited by the sorted roots.
    let sign_at = |x: Rational| -> Option<i32> {
        Some(
            poly::eval_rat_poly(&coeffs, x)?
                .numerator()
                .signum()
                .try_into()
                .unwrap_or(0),
        )
    };
    let want_sign = if want_positive { 1 } else { -1 };
    let step = Rational::integer(1);

    // Region sample points: below the first root, between consecutive roots, above
    // the last. With no roots, one sample at 0 decides all of ℝ.
    let mut selected: Vec<RealInterval> = Vec::new();
    if roots.is_empty() {
        if sign_at(Rational::zero())? == want_sign {
            selected.push(RealInterval {
                lower: None,
                lower_closed: false,
                upper: None,
                upper_closed: false,
            });
        }
        return Some(selected);
    }
    for index in 0..=roots.len() {
        let sample = if index == 0 {
            roots[0].checked_sub(step)?
        } else if index == roots.len() {
            roots[roots.len() - 1].checked_add(step)?
        } else {
            roots[index - 1]
                .checked_add(roots[index])?
                .checked_div(Rational::integer(2))?
        };
        if sign_at(sample)? == want_sign {
            let lower = if index == 0 {
                None
            } else {
                Some(roots[index - 1])
            };
            let upper = if index == roots.len() {
                None
            } else {
                Some(roots[index])
            };
            selected.push(RealInterval {
                lower,
                lower_closed: false,
                upper,
                upper_closed: false,
            });
        }
    }
    // For non-strict operators the roots themselves satisfy `p = 0`; include them
    // (closing adjacent interval endpoints and adding isolated points), then merge.
    if strict {
        Some(selected)
    } else {
        // Non-strict: the roots satisfy `p = 0`, so include them and merge.
        Some(merge_with_roots(selected, &roots))
    }
}

/// A span wide enough to bracket all real roots (twice the Cauchy-style bound),
/// used to frame the Sturm real-root count.
fn root_span(coeffs: &[Rational]) -> Option<Rational> {
    let degree = poly::rat_degree(coeffs)?;
    let leading = coeffs[degree];
    let mut bound = Rational::integer(1);
    for coeff in &coeffs[..degree] {
        let ratio = coeff.checked_div(leading)?;
        let magnitude = if ratio.numerator() < 0 {
            ratio.checked_neg()?
        } else {
            ratio
        };
        bound = bound.checked_add(magnitude)?;
    }
    bound.checked_add(Rational::integer(1))
}

/// Close endpoints at the roots (which satisfy `p = 0` for non-strict operators),
/// add isolated root points, and merge intervals that now touch at an included root.
fn merge_with_roots(strict_intervals: Vec<RealInterval>, roots: &[Rational]) -> Vec<RealInterval> {
    let mut intervals = strict_intervals;
    // Close any endpoint that coincides with a root.
    for interval in &mut intervals {
        if interval.lower.is_some() {
            interval.lower_closed = true;
        }
        if interval.upper.is_some() {
            interval.upper_closed = true;
        }
    }
    // Add each root not already covered as an isolated closed point.
    for &root in roots {
        let covered = intervals.iter().any(|i| {
            (i.lower == Some(root) && i.lower_closed) || (i.upper == Some(root) && i.upper_closed)
        });
        if !covered {
            intervals.push(RealInterval {
                lower: Some(root),
                lower_closed: true,
                upper: Some(root),
                upper_closed: true,
            });
        }
    }
    // Sort by lower endpoint (−∞ first) and merge touching/overlapping intervals.
    intervals.sort_by(|a, b| match (a.lower, b.lower) {
        (None, None) => core::cmp::Ordering::Equal,
        (None, _) => core::cmp::Ordering::Less,
        (_, None) => core::cmp::Ordering::Greater,
        (Some(x), Some(y)) => x.checked_cmp(&y).unwrap_or(core::cmp::Ordering::Equal),
    });
    let mut merged: Vec<RealInterval> = Vec::new();
    for interval in intervals {
        match merged.last_mut() {
            Some(last)
                if last.upper.is_some()
                    && last.upper == interval.lower
                    && (last.upper_closed || interval.lower_closed) =>
            {
                // They meet at a shared, included endpoint → merge.
                last.upper = interval.upper;
                last.upper_closed = interval.upper_closed;
            }
            _ => merged.push(interval),
        }
    }
    merged
}

/// Isolate the real roots of a univariate polynomial `expr` in `var`: disjoint
/// half-open intervals (ascending), each **Sturm-certified** to contain exactly one
/// real root (multiplicity collapsed). `Some(vec![])` if there are no real roots;
/// `None` if `expr` is not a univariate polynomial in `var` or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, real_root_intervals};
/// let x = CasExpr::var("x");
/// // x² − 2 has two real roots (±√2) → two disjoint isolating intervals.
/// let intervals = real_root_intervals(&(x.pow(2) - CasExpr::int(2)), "x").unwrap();
/// assert_eq!(intervals.len(), 2);
/// ```
#[must_use]
pub fn real_root_intervals(expr: &CasExpr, var: &str) -> Option<Vec<(Rational, Rational)>> {
    sturm::isolate_real_roots(&univariate_coeffs(expr, var)?)
}

/// The number of **distinct** real roots of a univariate polynomial `expr` in the
/// half-open interval `(lower, upper]`, via Sturm's theorem (an exact,
/// theorem-certified count). `None` if `expr` is not a univariate polynomial in
/// `var` or on overflow.
#[must_use]
pub fn count_real_roots(
    expr: &CasExpr,
    var: &str,
    lower: Rational,
    upper: Rational,
) -> Option<usize> {
    sturm::count_real_roots_in(&univariate_coeffs(expr, var)?, lower, upper)
}

/// Rational approximations (to within `width`) of **every** real root of a
/// univariate polynomial `expr` in `var`, ascending — each root Sturm-isolated then
/// bisected to precision. This gives decimal(-izable) roots for polynomials whose
/// roots are irrational or of degree ≥ 5 (beyond closed-form radicals). `None` if
/// `expr` is not a univariate polynomial, `width ≤ 0`, or on overflow.
#[must_use]
pub fn approximate_real_roots(expr: &CasExpr, var: &str, width: Rational) -> Option<Vec<Rational>> {
    sturm::approximate_real_roots(&univariate_coeffs(expr, var)?, width)
}

/// Every **real** root of a univariate polynomial `expr` in `var` as an exact
/// [`AlgebraicReal`] (`RootOf`) — the minimal polynomial (irreducible factor over
/// ℚ) plus a certified isolating interval — sorted ascending. Unlike [`solve`], this
/// represents roots of *any* degree exactly (cube roots, non-solvable quintics, …),
/// each refinable to arbitrary precision. `None` if `expr` is not a univariate
/// polynomial in `var` or on overflow.
#[must_use]
pub fn real_roots(expr: &CasExpr, var: &str) -> Option<Vec<AlgebraicReal>> {
    algebraic::real_roots(&univariate_coeffs(expr, var)?)
}

/// The (up to two) roots of `a·x² + b·x + c` as [`CasExpr`] values: rational when
/// the discriminant is a perfect square, a symbolic real `√` when the discriminant
/// is positive non-square, and a complex-conjugate pair (via `I`) when it is
/// negative. A zero discriminant yields the single (double) root. `None` if `a` is
/// zero or on overflow.
fn quadratic_roots(a: Rational, b: Rational, c: Rational) -> Option<Vec<CasExpr>> {
    if a.is_zero() {
        return None;
    }
    let two_a = Rational::integer(2).checked_mul(a)?;
    let disc = b
        .checked_mul(b)?
        .checked_sub(Rational::integer(4).checked_mul(a)?.checked_mul(c)?)?;
    let neg_b_over = b.checked_neg()?.checked_div(two_a)?;
    let mut out = Vec::new();
    if disc.is_zero() {
        out.push(CasExpr::Const(neg_b_over)); // repeated root
    } else if disc.numerator() >= 0 {
        // √disc = coeff·√radicand (radicand square-free). Real roots
        // neg_b_over ± (coeff/2a)·√radicand.
        let (coeff, radicand) = simplify_surd(disc)?;
        let amplitude = coeff.checked_div(two_a)?;
        for sign in [Rational::integer(1), Rational::integer(-1)] {
            let signed = sign.checked_mul(amplitude)?;
            let root = if radicand == Rational::integer(1) {
                CasExpr::Const(neg_b_over.checked_add(signed)?)
            } else {
                let surd = scaled_term(signed, CasExpr::Const(radicand).sqrt());
                fold_trivial(&(CasExpr::Const(neg_b_over) + surd))
            };
            out.push(root);
        }
    } else {
        // Complex conjugate roots: neg_b_over ± (coeff/2a)·√radicand·I.
        let neg_disc = Rational::zero().checked_sub(disc)?;
        let (coeff, radicand) = simplify_surd(neg_disc)?;
        let amplitude = coeff.checked_div(two_a)?;
        let imag_unit = CasExpr::var("I");
        for sign in [Rational::integer(1), Rational::integer(-1)] {
            let signed = sign.checked_mul(amplitude)?;
            let imaginary = if radicand == Rational::integer(1) {
                scaled_term(signed, imag_unit.clone())
            } else {
                CasExpr::Mul(vec![
                    CasExpr::Const(signed),
                    CasExpr::Const(radicand).sqrt(),
                    imag_unit.clone(),
                ])
            };
            let root = if neg_b_over.is_zero() {
                imaginary
            } else {
                CasExpr::Const(neg_b_over) + imaginary
            };
            out.push(fold_trivial(&root));
        }
    }
    Some(out)
}

/// Solve a **constant-coefficient linear homogeneous ODE**
/// `Σₖ cₖ·y⁽ᵏ⁾ = 0` given the coefficients `char_coeffs = [c₀, c₁, …, cₙ]` (which
/// are exactly the characteristic polynomial `Σ cₖ rᵏ`). Returns the general
/// solution with symbolic constants `C0, C1, …`, built from the characteristic
/// roots: real rational root `r` (multiplicity `m`) → `Cᵢ·xᵏ·e^(rx)` for
/// `k < m`; a complex pair `α ± βi` (rational `β`) → `e^(αx)(Cᵢ·cos βx + Cⱼ·sin βx)`.
/// **Certified** by applying the ODE operator to the solution and zero-testing.
/// `None` if a root is real-irrational or the remainder is unhandled.
#[must_use]
pub fn dsolve_homogeneous(char_coeffs: &[Rational], var: &str) -> Option<CasExpr> {
    let mut remaining = poly::rat_trim(char_coeffs.to_vec());
    poly::rat_degree(&remaining)?; // reject the zero polynomial
    let x = || CasExpr::var(var);
    let mut terms: Vec<CasExpr> = Vec::new();
    let mut c_index = 0usize;
    // Real rational roots, with multiplicity.
    while poly::rat_degree(&remaining).unwrap_or(0) >= 1 {
        let Some(&root) = ratint::rational_roots(&remaining)?.first() else {
            break;
        };
        let divisor = [root.checked_neg()?, Rational::integer(1)];
        let mut multiplicity = 0u32;
        while poly::rat_degree(&remaining).unwrap_or(0) >= 1
            && poly::eval_rat_poly(&remaining, root)?.is_zero()
        {
            remaining = poly::rat_exact_div(&remaining, &divisor)?;
            multiplicity += 1;
        }
        for k in 0..multiplicity {
            let mut factors = vec![CasExpr::var(&format!("C{c_index}"))];
            c_index += 1;
            if k >= 1 {
                factors.push(x().pow(k));
            }
            factors.push(scaled_term(root, x()).exp()); // e^(root·x)
            terms.push(CasExpr::Mul(factors));
        }
    }
    // A leftover irreducible quadratic → a complex-conjugate pair α ± βi.
    match poly::rat_degree(&remaining) {
        Some(0) => {}
        Some(2) => {
            let (a, b, c) = (remaining[2], remaining[1], remaining[0]);
            let two_a = Rational::integer(2).checked_mul(a)?;
            let alpha = b.checked_neg()?.checked_div(two_a)?;
            let disc = b
                .checked_mul(b)?
                .checked_sub(Rational::integer(4).checked_mul(a)?.checked_mul(c)?)?;
            if disc.numerator() >= 0 {
                return None; // real irrational roots — not handled here
            }
            let beta_sq = Rational::zero()
                .checked_sub(disc)?
                .checked_div(two_a.checked_mul(two_a)?)?;
            let beta = rational_sqrt(beta_sq)?;
            let cos_c = CasExpr::var(&format!("C{c_index}"));
            let sin_c = CasExpr::var(&format!("C{}", c_index + 1));
            let bx = scaled_term(beta, x());
            let inner = cos_c * bx.clone().cos() + sin_c * bx.sin();
            // e^(αx)·(…); drop the exponential when α = 0 (e.g. a harmonic oscillator).
            terms.push(if alpha.is_zero() {
                inner
            } else {
                CasExpr::Mul(vec![scaled_term(alpha, x()).exp(), inner])
            });
        }
        _ => return None, // higher-degree irreducible / irrational — not handled
    }
    if terms.is_empty() {
        return None;
    }
    let solution = match terms.len() {
        1 => terms.into_iter().next()?,
        _ => CasExpr::Add(terms),
    };
    // Certify: Σₖ cₖ·y⁽ᵏ⁾ ≡ 0.
    let mut operator = CasExpr::zero();
    let mut derivative = solution.clone();
    for coeff in char_coeffs {
        operator = operator + CasExpr::Const(*coeff) * derivative.clone();
        derivative = derivative.differentiate(var);
    }
    match equal(&operator, &CasExpr::zero()) {
        ZeroTest::Certified { equal: true, .. } => Some(solution),
        _ => None,
    }
}

/// Apply the constant-coefficient linear operator `L = Σₖ cₖ·Dᵏ` to the monomial
/// `xᵖ`, returning the resulting polynomial as an LSB-first coefficient vector.
/// `L[xᵖ] = Σₖ cₖ · p·(p−1)···(p−k+1) · x^{p−k}`. `None` on overflow.
fn operator_on_monomial(char_coeffs: &[Rational], power: usize) -> Option<Vec<Rational>> {
    let mut result = vec![Rational::zero(); power + 1];
    for (order, &coeff) in char_coeffs.iter().enumerate() {
        if order > power {
            break; // the k-th derivative of xᵖ vanishes once k > p
        }
        if coeff.is_zero() {
            continue;
        }
        // Falling factorial p·(p−1)···(p−order+1).
        let mut falling = Rational::integer(1);
        for step in 0..order {
            falling = falling.checked_mul(Rational::integer(i128::try_from(power - step).ok()?))?;
        }
        let term = coeff.checked_mul(falling)?;
        result[power - order] = result[power - order].checked_add(term)?;
    }
    Some(result)
}

/// Solve a **constant-coefficient linear ODE with polynomial forcing**
/// `Σₖ cₖ·y⁽ᵏ⁾ = f(x)`, where `char_coeffs = [c₀, …, cₙ]` and `forcing` is a
/// polynomial in `var`. Returns the general solution — a particular polynomial
/// solution (found by **undetermined coefficients**, including the `xˢ` factor for
/// resonance with the root `0`) plus the homogeneous solution (symbolic constants
/// `C0, C1, …`).
///
/// **Certified** by applying the ODE operator to the returned solution and
/// zero-testing the residual against `forcing` (the same differentiate-and-check
/// that certifies [`dsolve_homogeneous`]) — the polynomial particular part and the
/// single-exponential homogeneous atoms both lie in the decidable fragment.
///
/// Returns `None` if `forcing` is not a polynomial in `var`, if the homogeneous
/// part is outside [`dsolve_homogeneous`]'s domain (irrational characteristic
/// roots), or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, dsolve_inhomogeneous};
/// use axeyum_ir::Rational;
/// // y' + y = x  ⇒  particular x − 1, general x − 1 + C0·e^(−x).
/// let sol = dsolve_inhomogeneous(
///     &[Rational::integer(1), Rational::integer(1)],
///     &CasExpr::var("x"),
///     "x",
/// )
/// .unwrap();
/// // Substituting back, y' + y reduces to x — certified inside the call.
/// let _ = sol;
/// ```
#[must_use]
pub fn dsolve_inhomogeneous(
    char_coeffs: &[Rational],
    forcing: &CasExpr,
    var: &str,
) -> Option<CasExpr> {
    let trimmed = poly::rat_trim(char_coeffs.to_vec());
    poly::rat_degree(&trimmed)?; // reject the zero operator
    let forcing_coeffs = poly::rat_trim(univariate_coeffs(forcing, var)?);

    // Zero forcing → the pure homogeneous problem.
    let Some(forcing_degree) = poly::rat_degree(&forcing_coeffs) else {
        return dsolve_homogeneous(char_coeffs, var);
    };

    // Multiplicity `s` of the root 0 = number of leading zero coefficients.
    let resonance = char_coeffs.iter().take_while(|c| c.is_zero()).count();

    // Undetermined coefficients: y_p = Σⱼ bⱼ·x^{j+s}, j = 0..=forcing_degree.
    let unknowns = forcing_degree + 1;
    let equation_len = forcing_degree + resonance + 1;
    let pad = |mut v: Vec<Rational>| -> Vec<Rational> {
        v.resize(equation_len, Rational::zero());
        v
    };
    let mut columns: Vec<Vec<Rational>> = Vec::with_capacity(unknowns);
    for j in 0..unknowns {
        columns.push(pad(operator_on_monomial(char_coeffs, j + resonance)?));
    }
    let target = pad(forcing_coeffs);
    let Dependency::Combination(coefficients) = linear_dependency(&columns, &target)? else {
        return None; // no polynomial particular solution of this shape
    };

    // Build the particular solution y_p = Σⱼ bⱼ·x^{j+s}.
    let x = CasExpr::var(var);
    let mut particular = CasExpr::zero();
    for (j, &b) in coefficients.iter().enumerate() {
        if b.is_zero() {
            continue;
        }
        let power = u32::try_from(j + resonance).ok()?;
        let monomial = if power == 0 {
            CasExpr::Const(b)
        } else {
            CasExpr::Const(b) * x.clone().pow(power)
        };
        particular = particular + monomial;
    }
    let particular = expand(&particular).unwrap_or(particular);
    let homogeneous = dsolve_homogeneous(char_coeffs, var)?;
    let solution = particular + homogeneous;

    // Certify: L[solution] ≡ forcing.
    let mut operator = CasExpr::zero();
    let mut derivative = solution.clone();
    for coeff in char_coeffs {
        operator = operator + CasExpr::Const(*coeff) * derivative.clone();
        derivative = derivative.differentiate(var);
    }
    match equal(&operator, forcing) {
        ZeroTest::Certified { equal: true, .. } => Some(solution),
        _ => None,
    }
}

/// Solve a **first-order linear ODE** `y′ + p(x)·y = q(x)` by the integrating-factor
/// method: with `P = ∫p dx` and `μ = e^P`, the general solution is
/// `y = e^{−P}·(∫ μ·q dx + C₀)`.
///
/// **Certified** by substituting the solution into `y′ + p·y − q` and zero-testing
/// the residual — which now decides because the exp tower reduces the
/// `e^{−P}·e^P = 1` cancellation. Returns `None` unless both integrals `∫p` and
/// `∫μq` are found and certified by [`integrate`] (e.g. constant `p` with polynomial
/// forcing), or on overflow — an honest decline outside that fragment.
///
/// ```
/// use axeyum_cas::{CasExpr, dsolve_first_order_linear};
/// let x = CasExpr::var("x");
/// // y′ + y = x  ⇒  y = (x − 1) + C₀·e^{−x}.
/// let solution = dsolve_first_order_linear(&CasExpr::int(1), &x, "x").unwrap();
/// let _ = solution; // certified inside the call
/// ```
#[must_use]
pub fn dsolve_first_order_linear(p: &CasExpr, q: &CasExpr, var: &str) -> Option<CasExpr> {
    // P = ∫ p dx (certified antiderivative).
    let big_p = integrate(p, var)?;
    if !big_p.is_certified() {
        return None;
    }
    let antiderivative_p = big_p.antiderivative;

    // Integrating factor μ = exp(P); inner integrand μ·q.
    let mu = antiderivative_p.clone().exp();
    let inner = integrate(&(mu * q.clone()), var)?;
    if !inner.is_certified() {
        return None;
    }

    // y = exp(−P)·(R + C₀).
    let neg_p = CasExpr::Neg(Box::new(antiderivative_p)).exp();
    let solution = neg_p * (inner.antiderivative + CasExpr::var("C0"));

    // Certify: y′ + p·y − q ≡ 0.
    let residual = solution.differentiate(var) + p.clone() * solution.clone() - q.clone();
    match equal(&residual, &CasExpr::zero()) {
        ZeroTest::Certified { equal: true, .. } => Some(solution),
        _ => None,
    }
}

/// Solve a **separable first-order ODE** `dy/dx = f(x)·g(y)` by separation of
/// variables, returning the **implicit** general solution `G(y) − F(x) − C0 = 0`
/// (`= 0`), where `F = ∫ f dx` and `G = ∫ dy/g(y)`.
///
/// `f` is a function of `xvar` and `g` a function of `yvar`; `C0` is the reserved
/// integration constant. **Certified** in the sense that both antiderivatives are
/// differentiate-and-check certified (so `F′ = f` and `G′ = 1/g`), whence
/// `d/dx[G(y)−F(x)] = (1/g)·y′ − f = 0` exactly along `y′ = f·g`. E.g. `y′ = y`
/// gives `ln y − x − C0`; `y′ = x/y` gives `y²/2 − x²/2 − C0`. `None` if either
/// integral is not found/certified or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, dsolve_separable};
/// // y′ = y  ⇒  ln y − x − C0 = 0.
/// let sol = dsolve_separable(&CasExpr::int(1), &CasExpr::var("y"), "x", "y").unwrap();
/// // dsolve is implicit; check dependence on both variables is present.
/// assert!(sol.to_string().contains("ln(y)"));
/// ```
#[must_use]
pub fn dsolve_separable(f: &CasExpr, g: &CasExpr, xvar: &str, yvar: &str) -> Option<CasExpr> {
    // F = ∫ f dx (certified).
    let big_f = integrate(f, xvar)?;
    if !big_f.is_certified() {
        return None;
    }
    // G = ∫ 1/g dy (certified).
    let reciprocal = CasExpr::int(1) / g.clone();
    let big_g = integrate(&reciprocal, yvar)?;
    if !big_g.is_certified() {
        return None;
    }
    // Implicit general solution G(y) − F(x) − C0 = 0.
    Some(big_g.antiderivative - big_f.antiderivative - CasExpr::var("C0"))
}

/// Solve a **constant-coefficient linear recurrence** `aₙ = c₁·aₙ₋₁ + … + c_d·aₙ₋d`
/// with the given `coefficients = [c₁, …, c_d]` and `initial = [a₀, …, a_{d−1}]`,
/// returning a closed form `a(var)` for the general term.
///
/// The characteristic polynomial `xᵈ − c₁xᵈ⁻¹ − … − c_d` drives the closed form
/// `Σ Aᵢ·rᵢ^var`, with `rᵢ^var = exp(var·ln rᵢ)` for `rᵢ > 0` and
/// `cos(π·var)·exp(var·ln|rᵢ|)` for `rᵢ < 0`, and the amplitudes `Aᵢ` fixed by the
/// initial conditions. Two fragments are supported:
/// - **distinct positive rational** roots (any order `d`) — Vandermonde solve over
///   ℚ, certified by substituting the closed form into the recurrence;
/// - **order-2 real quadratic-irrational** roots `(c₁ ± √D)/2` — solved over ℚ(√D)
///   and certified by a roots-and-initials argument, so e.g. **Fibonacci** yields
///   Binet's formula `(φⁿ − ψⁿ)/√5`.
///
/// Returns `None` for higher-order irrational/complex spectra, repeated roots, if
/// the input shapes disagree, or on overflow.
///
/// ```
/// use axeyum_cas::solve_recurrence;
/// use axeyum_ir::Rational;
/// // aₙ = 5aₙ₋₁ − 6aₙ₋₂, a₀ = 0, a₁ = 1  ⇒  aₙ = 3ⁿ − 2ⁿ.
/// let closed = solve_recurrence(
///     &[Rational::integer(5), Rational::integer(-6)],
///     &[Rational::integer(0), Rational::integer(1)],
///     "n",
/// );
/// assert!(closed.is_some()); // certified inside the call
/// ```
#[must_use]
pub fn solve_recurrence(
    coefficients: &[Rational],
    initial: &[Rational],
    var: &str,
) -> Option<CasExpr> {
    let order = coefficients.len();
    if order == 0 || initial.len() != order {
        return None;
    }
    // Characteristic polynomial (LSB-first): xᵈ − Σ cₖ xᵈ⁻ᵏ.
    let mut char_poly = vec![Rational::zero(); order + 1];
    char_poly[order] = Rational::integer(1);
    for (k, coeff) in coefficients.iter().enumerate() {
        char_poly[order - (k + 1)] = coeff.checked_neg()?;
    }

    // Distinct positive rational roots, exactly `order` of them.
    let mut roots: Vec<Rational> = Vec::new();
    for root in ratint::rational_roots(&char_poly)? {
        if root.numerator() > 0 && !roots.contains(&root) {
            roots.push(root);
        }
    }
    if roots.len() == order {
        // Vandermonde solve: Σᵢ Aᵢ·rᵢʲ = aⱼ for j = 0..order−1.
        let mut columns: Vec<Vec<Rational>> = Vec::with_capacity(order);
        for &root in &roots {
            let mut column = Vec::with_capacity(order);
            let mut power = Rational::integer(1);
            for _ in 0..order {
                column.push(power);
                power = power.checked_mul(root)?;
            }
            columns.push(column);
        }
        let amplitudes = ratint::solve_linear(&columns, initial)?;

        // Closed form Σᵢ Aᵢ · exp(var·ln rᵢ).
        let index = CasExpr::var(var);
        let mut closed = CasExpr::zero();
        for (amplitude, &root) in amplitudes.iter().zip(&roots) {
            if amplitude.is_zero() {
                continue;
            }
            let power = (index.clone() * CasExpr::Const(root).ln()).exp(); // rᵢ^var
            closed = closed + CasExpr::Const(*amplitude) * power;
        }

        // Certify: a(n) − Σₖ cₖ·a(n−k) ≡ 0.
        let mut residual = closed.clone();
        for (k, coeff) in coefficients.iter().enumerate() {
            let shift = i128::try_from(k + 1).ok()?;
            let shifted = closed.substitute(var, &(index.clone() - CasExpr::int(shift)));
            residual = residual - CasExpr::Const(*coeff) * shifted;
        }
        return match equal(&residual, &CasExpr::zero()) {
            ZeroTest::Certified { equal: true, .. } => Some(closed),
            _ => None,
        };
    }

    // Fallback: an order-2 recurrence with a conjugate pair of **positive**
    // quadratic-irrational roots (the golden-ratio family — e.g. `aₙ = 3aₙ₋₁ − aₙ₋₂`,
    // roots `(3 ± √5)/2 = φ², ψ²`). Handled over ℚ(√D) with a roots-and-initials
    // certificate that avoids evaluating `rⁿ`.
    if order == 2 {
        return solve_recurrence_quadratic_irrational(coefficients, initial, var);
    }
    None
}

/// Whether `equal(expr, 0)` is decided `true` — a small helper for algebraic-identity
/// certificates.
fn is_certified_zero(expr: &CasExpr) -> bool {
    matches!(
        equal(expr, &CasExpr::zero()),
        ZeroTest::Certified { equal: true, .. }
    )
}

/// Structurally fold the trivial identities `0·x → 0`, `1·x → x`, `x + 0 → x`,
/// `−0 → 0`, `−(−x) → x`, `x¹ → x`, `x⁰ → 1`, flattening nested products and
/// combining constant factors — recursing through the tree **without** normalizing,
/// so `sqrt`/`exp`/trig structure is preserved (unlike [`simplify`], which turns
/// radicals into opaque atoms that no longer render or `evalf`). Value-preserving.
fn fold_trivial(expr: &CasExpr) -> CasExpr {
    let is_zero = |e: &CasExpr| matches!(e, CasExpr::Const(c) if c.is_zero());
    match expr {
        CasExpr::Add(terms) => {
            let kept: Vec<CasExpr> = terms
                .iter()
                .map(fold_trivial)
                .filter(|t| !is_zero(t))
                .collect();
            match kept.len() {
                0 => CasExpr::zero(),
                1 => kept.into_iter().next().unwrap_or_else(CasExpr::zero),
                _ => CasExpr::Add(kept),
            }
        }
        CasExpr::Mul(factors) => {
            // Fold factors, flattening nested products so constants across levels
            // can combine (e.g. `3·(2·x) → 6·x`).
            let mut constant = Rational::integer(1);
            let mut others: Vec<CasExpr> = Vec::new();
            let mut stack: Vec<CasExpr> = factors.iter().rev().map(fold_trivial).collect();
            while let Some(f) = stack.pop() {
                match f {
                    CasExpr::Const(c) if c.is_zero() => return CasExpr::zero(),
                    CasExpr::Const(c) => {
                        let Some(product) = constant.checked_mul(c) else {
                            others.push(CasExpr::Const(c));
                            continue;
                        };
                        constant = product;
                    }
                    CasExpr::Mul(inner) => stack.extend(inner.into_iter().rev()),
                    other => others.push(other),
                }
            }
            if !constant.is_zero() && constant != Rational::integer(1) {
                others.insert(0, CasExpr::Const(constant));
            }
            match others.len() {
                0 => CasExpr::Const(constant),
                1 => others.into_iter().next().unwrap_or_else(CasExpr::one),
                _ => CasExpr::Mul(others),
            }
        }
        CasExpr::Neg(inner) => {
            let folded = fold_trivial(inner);
            match folded {
                CasExpr::Const(c) => c.checked_neg().map_or_else(
                    || CasExpr::Neg(Box::new(CasExpr::Const(c))),
                    CasExpr::Const,
                ), // −c → (−c), incl. −0 → 0
                CasExpr::Neg(inner) => *inner, // −(−x) → x
                other => CasExpr::Neg(Box::new(other)),
            }
        }
        CasExpr::Div(numerator, denominator) => CasExpr::Div(
            Box::new(fold_trivial(numerator)),
            Box::new(fold_trivial(denominator)),
        ),
        CasExpr::Pow(base, exponent) => {
            let folded = fold_trivial(base);
            match exponent {
                0 => CasExpr::one(),
                1 => folded,
                _ => CasExpr::Pow(Box::new(folded), *exponent),
            }
        }
        CasExpr::Unary(func, arg) => CasExpr::Unary(*func, Box::new(fold_trivial(arg))),
        CasExpr::Const(_) | CasExpr::Var(_) => expr.clone(),
    }
}

/// The symbolic power `rⁿ` for a real algebraic base `root` (a `CasExpr`) and index
/// `n = index`, in a form that is real and `evalf`-able for integer `n`:
/// `exp(n·ln r)` when `root > 0`, and `cos(π·n)·exp(n·ln|r|)` when `root < 0` (since
/// `(−1)ⁿ = cos(πn)` for integer `n`). This is a **display/evaluation** form only —
/// the recurrence certificate never substitutes it, so its opacity to the zero-test
/// is harmless.
fn algebraic_power(root: &CasExpr, positive: bool, index: &CasExpr) -> CasExpr {
    if positive {
        (index.clone() * root.clone().ln()).exp()
    } else {
        // rⁿ = (−1)ⁿ·|r|ⁿ = cos(π·n)·exp(n·ln(−r)),  with −r = |r| > 0.
        let magnitude = fold_trivial(&CasExpr::Neg(Box::new(root.clone())));
        let alternating = (CasExpr::var("pi") * index.clone()).cos();
        alternating * (index.clone() * magnitude.ln()).exp()
    }
}

/// Closed form of an order-2 recurrence `aₙ = c₁aₙ₋₁ + c₂aₙ₋₂` whose characteristic
/// roots are a conjugate pair of **real irrational** algebraic numbers `(c₁ ± √D)/2`
/// (`D = c₁² + 4c₂ > 0` non-square, `c₂ ≠ 0`). Amplitudes are solved over ℚ(√D); the
/// result is **certified** by verifying each root satisfies the characteristic
/// equation and the amplitudes reproduce `a₀, a₁` — which, for distinct roots,
/// implies the closed form solves the recurrence for all `n` (no `rⁿ` substitution).
///
/// Negative roots are represented via `cos(π·n)·exp(n·ln|r|)`, so **Fibonacci**
/// (`aₙ=aₙ₋₁+aₙ₋₂`, roots `φ=(1+√5)/2 > 0`, `ψ=(1−√5)/2 < 0`) yields Binet's formula.
/// `None` for rational/perfect-square `D`, `c₂ = 0`, or on overflow.
fn solve_recurrence_quadratic_irrational(
    coefficients: &[Rational],
    initial: &[Rational],
    var: &str,
) -> Option<CasExpr> {
    let (c1, c2) = (coefficients[0], coefficients[1]);
    let discriminant = c1
        .checked_mul(c1)?
        .checked_add(Rational::integer(4).checked_mul(c2)?)?;
    // Distinct real irrational roots: D > 0 non-square, and c₂ ≠ 0 (roots nonzero).
    if discriminant.numerator() <= 0 || rational_sqrt(discriminant).is_some() || c2.is_zero() {
        return None;
    }
    let sqrt_d = simplify_radicals(&CasExpr::Const(discriminant).sqrt());
    let half = || CasExpr::rat(1, 2);
    let root1 = fold_trivial(&(half() * (CasExpr::Const(c1) + sqrt_d.clone()))); // (c₁ + √D)/2
    let root2 = fold_trivial(&(half() * (CasExpr::Const(c1) - sqrt_d.clone()))); // (c₁ − √D)/2

    // Exact signs (no floats): `(c₁+√D)/2 > 0 ⟺ c₁ ≥ 0 ∨ D > c₁²`;
    // `(c₁−√D)/2 > 0 ⟺ c₁ > 0 ∧ c₁² > D`.
    let c1_squared = c1.checked_mul(c1)?;
    let root1_positive = c1.numerator() >= 0 || discriminant > c1_squared;
    let root2_positive = c1.numerator() > 0 && c1_squared > discriminant;

    // Amplitudes: A = (a₁ − a₀·r₂)/(r₁ − r₂) with r₁ − r₂ = √D; B = a₀ − A.
    let (a0, a1) = (CasExpr::Const(initial[0]), CasExpr::Const(initial[1]));
    let amp_a = fold_trivial(&((a1.clone() - a0.clone() * root2.clone()) / sqrt_d));
    let amp_b = fold_trivial(&(a0.clone() - amp_a.clone()));

    let index = CasExpr::var(var);
    let closed = fold_trivial(
        &(amp_a.clone() * algebraic_power(&root1, root1_positive, &index)
            + amp_b.clone() * algebraic_power(&root2, root2_positive, &index)),
    );

    // Certificate: each root solves x² − c₁x − c₂ = 0, and the amplitudes reproduce
    // the two initial terms (r⁰ = 1, r¹ = r — no `rⁿ` evaluation needed).
    let char_at =
        |r: &CasExpr| r.clone().pow(2) - CasExpr::Const(c1) * r.clone() - CasExpr::Const(c2);
    let initial0 = amp_a.clone() + amp_b.clone() - a0;
    let initial1 = amp_a * root1.clone() + amp_b * root2.clone() - a1;
    if is_certified_zero(&char_at(&root1))
        && is_certified_zero(&char_at(&root2))
        && is_certified_zero(&initial0)
        && is_certified_zero(&initial1)
    {
        Some(closed)
    } else {
        None
    }
}

/// The binomial coefficient `C(n, k)` as an exact rational, or `None` on overflow.
fn binomial_rat(n: usize, k: usize) -> Option<Rational> {
    if k > n {
        return Some(Rational::zero());
    }
    let mut result = Rational::integer(1);
    for i in 0..k {
        let numer = Rational::integer(i128::try_from(n - i).ok()?);
        let denom = Rational::integer(i128::try_from(i + 1).ok()?);
        result = result.checked_mul(numer)?.checked_div(denom)?;
    }
    Some(result)
}

/// The **definite sum** `Σ_{var=lower}^{upper} f(var)` of a polynomial summand `f`,
/// as a closed-form [`CasExpr`] in the (possibly symbolic) bounds. Computed from the
/// discrete antiderivative `S` (with `S(n) = Σ_{k=0}^{n−1} f(k)`, see
/// [`sum_polynomial`]) as `S(upper+1) − S(lower)`. **Certified** through
/// `sum_polynomial`'s telescoping certificate. `None` if `f` is not a univariate
/// polynomial in `var` or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, definite_sum, equal, ZeroTest};
/// let k = CasExpr::var("k");
/// let n = CasExpr::var("n");
/// // Σ_{k=1}^{n} k = n(n+1)/2.
/// let s = definite_sum(&k, "k", &CasExpr::int(1), &n).unwrap();
/// let expected = CasExpr::rat(1, 2) * n.clone() * (n + CasExpr::int(1));
/// assert!(matches!(equal(&s, &expected), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn definite_sum(f: &CasExpr, var: &str, lower: &CasExpr, upper: &CasExpr) -> Option<CasExpr> {
    let antidifference = sum_polynomial(f, var)?; // S(n) = Σ_{k=0}^{n-1} f(k)
    let at_upper = antidifference.substitute(var, &(upper.clone() + CasExpr::int(1)));
    let at_lower = antidifference.substitute(var, lower);
    let result = at_upper - at_lower;
    Some(expand(&result).unwrap_or(result))
}

/// The **finite product** `∏_{var=lower}^{upper} f(var)` over **concrete integer**
/// bounds — the multiplicative analogue of [`definite_sum`]. Each factor `f(k)` is
/// obtained by substitution and the exact product is simplified. An empty range
/// (`upper < lower`) is the empty product `1`. Handles any `f` (`∏ k = k!`,
/// `∏ (x+k)` a rising-factorial polynomial, `∏ 2 = 2^{count}`); the closed form
/// for a *symbolic* upper bound (Pochhammer/Γ) is out of the exact fragment and
/// not attempted here. `None` if the bounds are not integer constants or on
/// overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, finite_product, equal, ZeroTest};
/// // ∏_{k=1}^{5} k = 120.
/// let p = finite_product(&CasExpr::var("k"), "k", &CasExpr::int(1), &CasExpr::int(5)).unwrap();
/// assert!(matches!(equal(&p, &CasExpr::int(120)), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn finite_product(
    f: &CasExpr,
    var: &str,
    lower: &CasExpr,
    upper: &CasExpr,
) -> Option<CasExpr> {
    let a = integer_constant(lower)?;
    let b = integer_constant(upper)?;
    if b < a {
        return Some(CasExpr::one()); // empty product
    }
    let mut product = CasExpr::one();
    for k in a..=b {
        let term = f.substitute(var, &CasExpr::int(k));
        product = product * term;
    }
    Some(simplify(&product))
}

/// The exact integer value of `expr` if it is an integer [`CasExpr::Const`], else
/// `None` (a fraction or non-constant).
fn integer_constant(expr: &CasExpr) -> Option<i128> {
    match expr {
        CasExpr::Const(c) if c.denominator() == 1 => Some(c.numerator()),
        _ => None,
    }
}

/// The closed form of `∑_{k=0}^{var−1} f(k)` for a polynomial summand `f` — the
/// **discrete antiderivative** `S` with `S(var+1) − S(var) = f(var)` and `S(0)=0`.
/// Solved as one exact linear system; **certified** by the telescoping zero-test
/// `S(var+1) − S(var) − f ≡ 0`. E.g. `∑ k = (n²−n)/2`. `None` if `f` is not a
/// univariate polynomial or on overflow.
#[must_use]
pub fn sum_polynomial(f: &CasExpr, var: &str) -> Option<CasExpr> {
    let f_coeffs = normalize(f)?.to_univariate(var)?;
    if ratint::is_zero(&f_coeffs) {
        return Some(CasExpr::zero());
    }
    let degree = poly::rat_degree(&f_coeffs)?;
    let unknowns = degree + 2; // S has degree ≤ degree+1
    // Column j is the contribution of unknown sⱼ to the equations
    // [ΔS coefficients k⁰..k^degree ; boundary S(0)=0].
    let mut cols: Vec<Vec<Rational>> = Vec::with_capacity(unknowns);
    for j in 0..unknowns {
        let mut col = vec![Rational::zero(); degree + 1];
        // (k+1)^j − k^j = Σ_{i=0}^{j−1} C(j,i) k^i.
        for (i, entry) in col.iter_mut().enumerate().take(j) {
            *entry = binomial_rat(j, i)?;
        }
        col.push(if j == 0 {
            Rational::integer(1)
        } else {
            Rational::zero()
        });
        cols.push(col);
    }
    let mut rhs = f_coeffs;
    rhs.resize(degree + 1, Rational::zero());
    rhs.push(Rational::zero()); // boundary S(0) = 0
    let s_coeffs = ratint::solve_linear(&cols, &rhs)?;
    let closed_form = MultiPoly::from_univariate(var, &s_coeffs).to_expr();
    // Certify the telescoping identity S(var+1) − S(var) = f.
    let shifted = closed_form.substitute(var, &(CasExpr::var(var) + CasExpr::int(1)));
    match equal(&(shifted - closed_form.clone()), f) {
        ZeroTest::Certified { equal: true, .. } => Some(closed_form),
        _ => None,
    }
}

/// The distinct rational roots of `den` with their multiplicities, or `None` if
/// `den` does not split completely into rational **linear** factors (an irreducible
/// quadratic-or-higher factor remains).
/// Full partial-fraction decomposition of a univariate rational function over ℚ:
/// `p/q = (polynomial part) + Σ_f Σ_{j=1}^{k_f} N_{f,j}(x) / f(x)ʲ`, where `f` ranges
/// over the **irreducible factors** of the denominator (linear, irreducible
/// quadratic, or higher) with multiplicity `k_f`, and each numerator `N_{f,j}` has
/// degree `< deg f`. The numerators are found by undetermined coefficients (one
/// exact linear solve). Returns the decomposition **certified** equal to the input
/// (the re-combination zero-test), or `None` if `expr` is not a univariate rational
/// function or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, apart, equal, ZeroTest};
/// let x = CasExpr::var("x");
/// // x/((x−1)(x²+1)) splits with an irreducible-quadratic factor.
/// let f = x.clone() / ((x.clone() - CasExpr::int(1)) * (x.pow(2) + CasExpr::int(1)));
/// let decomposed = apart(&f, "x").unwrap();
/// assert!(matches!(equal(&decomposed, &f), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn apart(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let rf = normalize_rational(expr)?;
    let num = rf.num.to_univariate(var)?;
    let den = rf.den.to_univariate(var)?;
    let deg_den = poly::rat_degree(&den)?;
    if deg_den == 0 {
        return expand(expr); // no denominator — just the polynomial
    }
    let (quotient, remainder) = ratint::divrem(&num, &den)?;
    let factors = factor_univariate_over_q(&den)?;

    // Undetermined coefficients: for each irreducible factor `f` (degree `d`) with
    // multiplicity `k`, and each power `j = 1..k`, the numerator `N_{f,j}` (degree
    // `< d`) contributes `d` unknowns; the basis for its `xˡ` coefficient is
    // `xˡ·(den / fʲ)`. The system `Σ (unknown)·basis = remainder` is square
    // (`Σ d·k = deg den`).
    let mut columns: Vec<Vec<Rational>> = Vec::new();
    let mut meta: Vec<(usize, u32, usize)> = Vec::new(); // (factor index, power j, coeff l)
    let mut factor_polys: Vec<Vec<Rational>> = Vec::new();
    for (factor, multiplicity) in &factors {
        let degree = poly::rat_degree(factor).unwrap_or(0);
        if degree == 0 {
            continue; // a constant (content) factor contributes no partial fraction
        }
        factor_polys.push(factor.clone());
        let factor_index = factor_polys.len() - 1;
        let mut factor_power = vec![Rational::integer(1)];
        for power in 1..=*multiplicity {
            factor_power = poly::ratpoly_mul(&factor_power, factor)?; // fʲ
            let basis = poly::rat_exact_div(&den, &factor_power)?; // den / fʲ
            for shift in 0..degree {
                let mut column = vec![Rational::zero(); shift]; // xˢʰⁱᶠᵗ · basis
                column.extend_from_slice(&basis);
                column.resize(deg_den, Rational::zero());
                columns.push(column);
                meta.push((factor_index, power, shift));
            }
        }
    }
    let mut rhs = remainder;
    rhs.resize(deg_den, Rational::zero());
    if columns.len() != rhs.len() {
        return None; // shape guard (should hold: Σ d·k = deg den)
    }
    let coefficients = ratint::solve_linear(&columns, &rhs)?;

    // Group the solved coefficients into a numerator polynomial per (factor, power).
    let mut numerators: BTreeMap<(usize, u32), Vec<Rational>> = BTreeMap::new();
    for (coeff, &(factor_index, power, shift)) in coefficients.iter().zip(&meta) {
        let degree = poly::rat_degree(&factor_polys[factor_index]).unwrap_or(0);
        let numerator = numerators
            .entry((factor_index, power))
            .or_insert_with(|| vec![Rational::zero(); degree]);
        numerator[shift] = *coeff;
    }

    let mut parts: Vec<CasExpr> = Vec::new();
    if !ratint::is_zero(&quotient) {
        parts.push(MultiPoly::from_univariate(var, &quotient).to_expr());
    }
    for ((factor_index, power), numerator) in &numerators {
        if numerator.iter().all(|c| c.is_zero()) {
            continue;
        }
        let numerator_expr = MultiPoly::from_univariate(var, numerator).to_expr();
        let factor_expr = MultiPoly::from_univariate(var, &factor_polys[*factor_index]).to_expr();
        parts.push(numerator_expr / factor_expr.pow(*power));
    }
    let result = match parts.len() {
        0 => CasExpr::zero(),
        1 => parts.into_iter().next()?,
        _ => CasExpr::Add(parts),
    };
    // Fold `factor^1 → factor` (a simple pole) and other trivial noise for a clean
    // partial-fraction form; value-preserving, so the certificate still holds.
    let result = fold_trivial(&result);
    match equal(&result, expr) {
        ZeroTest::Certified { equal: true, .. } => Some(result),
        _ => None,
    }
}

/// The **residue** of a rational function `expr` at the rational point `point` — the
/// coefficient of `(var − point)⁻¹` in its Laurent expansion there. For a pole of
/// order `m`, `Res = (1/(m−1)!)·[d^{m−1}/dvar^{m−1}((var−point)ᵐ·expr)]|_{var=point}`;
/// a non-pole gives `0`. Exact over the rational-function fragment.
///
/// Returns `None` if `expr` is not a univariate rational function in `var` or on
/// overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, residue};
/// use axeyum_ir::Rational;
/// let x = CasExpr::var("x");
/// // Res_{x=1} 1/((x−1)(x−2)) = 1/(1−2) = −1.
/// let f = CasExpr::int(1) / ((x.clone() - CasExpr::int(1)) * (x - CasExpr::int(2)));
/// assert_eq!(residue(&f, "x", Rational::integer(1)).unwrap(), CasExpr::int(-1));
/// ```
#[must_use]
pub fn residue(expr: &CasExpr, var: &str, point: Rational) -> Option<CasExpr> {
    // Reduce to lowest terms so cancellable factors do not inflate the pole order.
    let reduced = cancel(expr)?;
    let ratio = normalize_rational(&reduced)?;
    let numerator = ratio.num.to_univariate(var)?;
    let mut denominator = ratio.den.to_univariate(var)?;

    // Peel the (var − point) factor to find the pole order `m` and the residual
    // denominator `r` with `denominator = (var − point)ᵐ · r`.
    let factor = [point.checked_neg()?, Rational::integer(1)];
    let mut order = 0u32;
    while poly::rat_degree(&denominator).unwrap_or(0) >= 1
        && poly::eval_rat_poly(&denominator, point)?.is_zero()
    {
        denominator = poly::rat_exact_div(&denominator, &factor)?;
        order += 1;
    }
    if order == 0 {
        return Some(CasExpr::zero()); // not a pole
    }

    // g(var) = (var − point)ᵐ · expr = numerator / r, finite at `point`.
    let g = MultiPoly::from_univariate(var, &numerator).to_expr()
        / MultiPoly::from_univariate(var, &denominator).to_expr();
    let derivative = g.differentiate_n(var, (order - 1) as usize);
    let value = limit(&derivative, var, LimitPoint::Finite(point))?;

    // Divide by (m − 1)!.
    let mut factorial = Rational::integer(1);
    for k in 1..order {
        factorial = factorial.checked_mul(Rational::integer(i128::from(k)))?;
    }
    Some(simplify(&(value / CasExpr::Const(factorial))))
}

/// The number of nodes in an expression tree (a size metric for [`simplify`]).
fn node_count(expr: &CasExpr) -> usize {
    1 + match expr {
        CasExpr::Const(_) | CasExpr::Var(_) => 0,
        CasExpr::Add(items) | CasExpr::Mul(items) => items.iter().map(node_count).sum(),
        CasExpr::Neg(a) | CasExpr::Pow(a, _) | CasExpr::Unary(_, a) => node_count(a),
        CasExpr::Div(a, b) => node_count(a) + node_count(b),
    }
}

/// Heuristically simplify by choosing the structurally smallest form among the
/// input, its [`expand`]ed, and its [`cancel`]led (lowest-terms) versions — all of
/// which are value-equal by construction. Always returns a value-equal expression
/// (the input itself in the worst case).
#[must_use]
pub fn simplify(expr: &CasExpr) -> CasExpr {
    let mut best = expr.clone();
    let mut best_size = node_count(&best);
    // `trigsimp` is included so the common entry point also collapses
    // `sin²+cos²`; it returns an equality-gated (hence value-equal) form.
    for candidate in [cancel(expr), expand(expr), Some(trigsimp(expr))]
        .into_iter()
        .flatten()
    {
        let size = node_count(&candidate);
        if size < best_size {
            best = candidate;
            best_size = size;
        }
    }
    best
}

/// Simplify trigonometric expressions using the Pythagorean identity
/// `sin²u + cos²u = 1`, returning the structurally smallest **value-equal** form.
///
/// The expression is normalized to a rational function over `sin`/`cos` atoms and
/// reduced in both directions — eliminating `cos²` in favour of `sin²` and vice
/// versa (see [`MultiPoly::fold_pythagorean`] and its mirror) — and the smallest
/// candidate that [`equal`] certifies value-equal to the input is chosen (the
/// input itself in the worst case). So `sin²x + cos²x → 1`, `1 − cos²x → sin²x`,
/// `2sin²x + 2cos²x → 2`, while an already-minimal form is returned unchanged.
///
/// Every returned form is guaranteed value-equal: candidates are gated on a
/// [`ZeroTest::Certified`] equality, so a mis-reduction can never escape.
#[must_use]
pub fn trigsimp(expr: &CasExpr) -> CasExpr {
    let mut best = expr.clone();
    let mut best_size = node_count(&best);
    for candidate in [pyth_reduce(expr, true), pyth_reduce(expr, false)]
        .into_iter()
        .flatten()
    {
        let size = node_count(&candidate);
        if size < best_size
            && matches!(equal(&candidate, expr), ZeroTest::Certified { equal: true, .. })
        {
            best = candidate;
            best_size = size;
        }
    }
    best
}

/// Reduce an expression by the Pythagorean identity, eliminating squared cosines
/// in favour of sines when `to_sin` (else squared sines in favour of cosines),
/// applied to both the numerator and denominator of its rational-function normal
/// form. Returns the reconstructed, de-atomized [`CasExpr`], or `None` if the
/// expression is outside the normalizable fragment or on overflow.
fn pyth_reduce(expr: &CasExpr, to_sin: bool) -> Option<CasExpr> {
    let rf = normalize_rational(expr)?;
    let fold = |p: &MultiPoly| {
        if to_sin {
            p.fold_pythagorean()
        } else {
            p.fold_pythagorean_to_cos()
        }
    };
    let num = fold(&rf.num)?;
    let den = fold(&rf.den)?;
    let result = if den == MultiPoly::constant(Rational::integer(1)) {
        num.to_expr()
    } else {
        CasExpr::Div(Box::new(num.to_expr()), Box::new(den.to_expr()))
    };
    Some(deatomize_from(&result, expr))
}

/// The rank of a rational-constant matrix (number of nonzero rows of its reduced
/// row echelon form). `None` if the matrix has non-constant entries or on overflow.
#[must_use]
pub fn matrix_rank(matrix: &Matrix) -> Option<usize> {
    let echelon = matrix.rref()?;
    let mut rank = 0;
    for i in 0..echelon.rows() {
        let nonzero_row = (0..echelon.cols())
            .any(|j| matches!(echelon.get(i, j), Some(CasExpr::Const(c)) if !c.is_zero()));
        if nonzero_row {
            rank += 1;
        }
    }
    Some(rank)
}

/// The trace of a square matrix (sum of the diagonal entries), expanded to
/// canonical form. `None` if the matrix is not square.
#[must_use]
pub fn trace(matrix: &Matrix) -> Option<CasExpr> {
    let n = matrix.rows();
    if n != matrix.cols() {
        return None;
    }
    let mut sum = CasExpr::zero();
    for i in 0..n {
        sum = sum + matrix.get(i, i)?.clone();
    }
    Some(expand(&sum).unwrap_or(sum))
}

/// The characteristic polynomial `det(A − λ·I)` of a square matrix, as an
/// (expanded) polynomial in `var` (= λ). `None` if the matrix is not square or on
/// overflow.
#[must_use]
pub fn characteristic_polynomial(matrix: &Matrix, var: &str) -> Option<CasExpr> {
    let n = matrix.rows();
    if n != matrix.cols() {
        return None;
    }
    let lambda = CasExpr::var(var);
    let mut rows: Vec<Vec<CasExpr>> = Vec::with_capacity(n);
    for i in 0..n {
        let mut row = Vec::with_capacity(n);
        for j in 0..n {
            let entry = matrix.get(i, j)?.clone();
            row.push(if i == j {
                entry - lambda.clone()
            } else {
                entry
            });
        }
        rows.push(row);
    }
    let determinant = Matrix::from_rows(rows)?.determinant()?;
    Some(expand(&determinant).unwrap_or(determinant))
}

/// The eigenvalues of a square matrix: the roots of its characteristic
/// polynomial (rational + real-quadratic + complex), via [`solve`].
#[must_use]
pub fn eigenvalues(matrix: &Matrix, var: &str) -> Option<Vec<CasExpr>> {
    solve(&characteristic_polynomial(matrix, var)?, var)
}

/// A basis for the (right) null space `{x : A·x = 0}` of a rational-constant
/// matrix, each vector an `n × 1` column [`Matrix`]. An empty result means the
/// null space is trivial. Every returned `v` satisfies `A·v = 0` exactly (the
/// certificate is the matrix product). `None` on a non-constant entry or overflow.
#[must_use]
pub fn null_space(matrix: &Matrix) -> Option<Vec<Matrix>> {
    matrix.null_space()
}

/// The eigenvectors of a square rational-constant matrix, grouped by eigenvalue.
///
/// For each **rational** eigenvalue `λ` (the fragment in which `A − λI` stays a
/// rational-constant matrix), returns `(λ, basis)` where `basis` spans the
/// eigenspace `ker(A − λI)` — i.e. every returned vector `v` satisfies `A·v = λ·v`
/// exactly, which is the eigenvector certificate. Eigenvalues that are irrational
/// or complex (so `A − λI` leaves the rational-constant fragment) are skipped
/// rather than mislabelled; the returned list covers exactly the rational spectrum.
///
/// `None` if the matrix is not square, is non-constant, or on overflow.
#[must_use]
pub fn eigenvectors(matrix: &Matrix, var: &str) -> Option<Vec<(CasExpr, Vec<Matrix>)>> {
    let n = matrix.rows();
    if n != matrix.cols() {
        return None;
    }
    let mut result: Vec<(CasExpr, Vec<Matrix>)> = Vec::new();
    let mut seen: Vec<Rational> = Vec::new();
    for eigenvalue in eigenvalues(matrix, var)? {
        // Only rational eigenvalues keep `A − λI` inside the rational-constant
        // fragment that `null_space` can decide; skip the rest honestly.
        let CasExpr::Const(lambda) = eigenvalue else {
            continue;
        };
        if seen.contains(&lambda) {
            continue;
        }
        seen.push(lambda);
        // Build `A − λI` directly over rationals so entries stay bare constants.
        let mut rows: Vec<Vec<CasExpr>> = Vec::with_capacity(n);
        for i in 0..n {
            let mut row = Vec::with_capacity(n);
            for j in 0..n {
                let CasExpr::Const(entry) = matrix.get(i, j)? else {
                    return None;
                };
                let value = if i == j {
                    entry.checked_sub(lambda)?
                } else {
                    *entry
                };
                row.push(CasExpr::Const(value));
            }
            rows.push(row);
        }
        let basis = Matrix::from_rows(rows)?.null_space()?;
        result.push((CasExpr::Const(lambda), basis));
    }
    Some(result)
}

/// **Diagonalize** a square rational-constant matrix `A` (with a full set of
/// rational eigenvectors): return `(P, D)` with `A = P·D·P⁻¹`, i.e. `A·P = P·D`,
/// where `D` is the diagonal matrix of eigenvalues and `P` has the corresponding
/// eigenvectors as columns. **Certified** by the identity `A·P = P·D` (re-multiply
/// and zero-test). Returns `None` if `A` is not square/constant, or is **not
/// diagonalizable over ℚ** (fewer than `n` independent rational eigenvectors — e.g.
/// a defective matrix or irrational/complex eigenvalues).
#[must_use]
pub fn diagonalize(matrix: &Matrix, var: &str) -> Option<(Matrix, Matrix)> {
    let n = matrix.rows();
    if n == 0 || n != matrix.cols() {
        return None;
    }
    // Collect (eigenvalue, eigenvector) pairs across all rational eigenspaces.
    let mut eigenvalues: Vec<CasExpr> = Vec::new();
    let mut columns: Vec<Vec<CasExpr>> = Vec::new();
    for (lambda, basis) in eigenvectors(matrix, var)? {
        for vector in basis {
            let column: Vec<CasExpr> = (0..n)
                .map(|i| vector.get(i, 0).cloned())
                .collect::<Option<_>>()?;
            columns.push(column);
            eigenvalues.push(lambda.clone());
        }
    }
    if columns.len() != n {
        return None; // not enough independent eigenvectors → not diagonalizable over ℚ
    }
    // P has the eigenvectors as columns; D is diag(eigenvalues).
    let p_rows: Vec<Vec<CasExpr>> = (0..n)
        .map(|i| columns.iter().map(|col| col[i].clone()).collect())
        .collect();
    let p = Matrix::from_rows(p_rows)?;
    let d_rows: Vec<Vec<CasExpr>> = (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    if i == j {
                        eigenvalues[i].clone()
                    } else {
                        CasExpr::zero()
                    }
                })
                .collect()
        })
        .collect();
    let d = Matrix::from_rows(d_rows)?;

    // Certificate: A·P = P·D.
    let left = matrix.mul(&p)?;
    let right = p.mul(&d)?;
    for i in 0..n {
        for j in 0..n {
            if !matches!(
                equal(left.get(i, j)?, right.get(i, j)?),
                ZeroTest::Certified { equal: true, .. }
            ) {
                return None;
            }
        }
    }
    Some((p, d))
}

/// The **matrix exponential** `exp(A·t)` of a square rational matrix `A` with a
/// **rational spectrum** (all eigenvalues rational, defective or not), as a matrix
/// of [`CasExpr`] in the symbol `t`.
///
/// With the Jordan decomposition `A = P·J·P⁻¹` (see [`jordan_form`]),
/// `exp(A·t) = P·exp(J·t)·P⁻¹`, where each Jordan block `λI + N` (size `s`)
/// contributes `exp(J·t) = e^{λt}·Σ (N t)^k/k!` — an upper-triangular block whose
/// `j`-th super-diagonal is `e^{λt}·t^j/j!`. This covers **defective** matrices
/// (a plain diagonalizable `A` is the all-size-1-blocks case, giving `diag(e^{dᵢt})`).
///
/// **Certified** by the defining initial-value problem: every entry of
/// `d/dt M(t) − A·M(t)` is proven zero by [`equal`] and `M(0) = I`, which uniquely
/// characterizes `exp(A·t)`. Returns `None` if `A` is not square, has an
/// irrational/complex eigenvalue, or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, Matrix, matrix_exp, equal, ZeroTest};
/// // exp(diag(1,2)·t) = diag(e^t, e^{2t}).
/// let a = Matrix::from_rows(vec![
///     vec![CasExpr::int(1), CasExpr::zero()],
///     vec![CasExpr::zero(), CasExpr::int(2)],
/// ]).unwrap();
/// let m = matrix_exp(&a, "t").unwrap();
/// let t = CasExpr::var("t");
/// assert!(matches!(equal(m.get(0, 0).unwrap(), &t.clone().exp()), ZeroTest::Certified { equal: true, .. }));
/// assert!(matches!(equal(m.get(1, 1).unwrap(), &(CasExpr::int(2) * t).exp()), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn matrix_exp(matrix: &Matrix, t: &str) -> Option<Matrix> {
    let n = matrix.rows();
    if n == 0 || n != matrix.cols() {
        return None;
    }
    // A = P·J·P⁻¹ (Jordan). Reserved spectral variable can't collide with `t`.
    let (p, _j, blocks) = jordan_decomposition(matrix, "\0mexp:lambda")?;
    let p_inv = p.solve(&Matrix::identity(n))?;
    // exp(J·t): per block (λ, size s) at `offset`, entry [offset+i][offset+i+d]
    // is e^{λt}·t^d/d! for the d-th super-diagonal (0 ≤ i+d < s).
    let t_expr = CasExpr::var(t);
    let mut exp_j = vec![vec![CasExpr::zero(); n]; n];
    let mut offset = 0;
    for &(lambda, size) in &blocks {
        let e_lambda_t = (CasExpr::Const(lambda) * t_expr.clone()).exp();
        let mut factorial = Rational::integer(1);
        for d in 0..size {
            if d > 0 {
                factorial = factorial.checked_mul(Rational::integer(i128::try_from(d).ok()?))?;
            }
            // t^d / d! · e^{λt} placed on the d-th super-diagonal of this block.
            let power = match u32::try_from(d).ok()? {
                0 => CasExpr::int(1),
                p => t_expr.clone().pow(p),
            };
            let entry = CasExpr::Const(Rational::integer(1).checked_div(factorial)?)
                * power
                * e_lambda_t.clone();
            for i in 0..(size - d) {
                exp_j[offset + i][offset + i + d] = entry.clone();
            }
        }
        offset += size;
    }
    let exp_d = Matrix::from_rows(exp_j)?;
    let product = p.mul(&exp_d)?.mul(&p_inv)?;
    // Simplify entries for a clean, readable result.
    let mut simplified_rows = Vec::with_capacity(n);
    for i in 0..n {
        let mut row = Vec::with_capacity(n);
        for j in 0..n {
            row.push(simplify(product.get(i, j)?));
        }
        simplified_rows.push(row);
    }
    let result = Matrix::from_rows(simplified_rows)?;

    // Certificate: M(0) = I and d/dt M(t) = A·M(t) entrywise.
    let a_times_m = matrix.mul(&result)?;
    for i in 0..n {
        for j in 0..n {
            let entry = result.get(i, j)?;
            // M(0) = I.
            let at_zero = entry.substitute(t, &CasExpr::zero());
            let expected0 = if i == j { CasExpr::one() } else { CasExpr::zero() };
            if !matches!(
                equal(&at_zero, &expected0),
                ZeroTest::Certified { equal: true, .. }
            ) {
                return None;
            }
            // d/dt M = A·M.
            if !matches!(
                equal(&entry.differentiate(t), a_times_m.get(i, j)?),
                ZeroTest::Certified { equal: true, .. }
            ) {
                return None;
            }
        }
    }
    Some(result)
}

/// Solve the **linear ODE system** `x′(t) = A·x(t)` with initial condition
/// `x(0) = x0`, for a rational matrix `A` with a rational spectrum (defective or
/// not). The unique solution is `x(t) = e^{A·t}·x0` (see [`matrix_exp`]); returned
/// as the solution vector (an `n × 1` [`Matrix`] of [`CasExpr`] in `t`), simplified.
///
/// **Certified**: `matrix_exp` proves `d/dt e^{At} = A·e^{At}` and `e^{A·0}=I`, so
/// `x′ = A·x` and `x(0) = x0` hold by construction. Returns `None` if `A` is not
/// square / has an irrational eigenvalue, `x0` is not an `n × 1` matrix, or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, Matrix, linear_ode_system, equal, ZeroTest};
/// // x′ = [[1,0],[0,2]]·x, x(0) = (1,1)  ⇒  x(t) = (e^t, e^{2t}).
/// let a = Matrix::from_rows(vec![
///     vec![CasExpr::int(1), CasExpr::zero()],
///     vec![CasExpr::zero(), CasExpr::int(2)],
/// ]).unwrap();
/// let x0 = Matrix::from_rows(vec![vec![CasExpr::int(1)], vec![CasExpr::int(1)]]).unwrap();
/// let x = linear_ode_system(&a, &x0, "t").unwrap();
/// let t = CasExpr::var("t");
/// assert!(matches!(equal(x.get(0, 0).unwrap(), &t.clone().exp()), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn linear_ode_system(matrix: &Matrix, initial: &Matrix, t: &str) -> Option<Matrix> {
    let n = matrix.rows();
    if initial.rows() != n || initial.cols() != 1 {
        return None;
    }
    let fundamental = matrix_exp(matrix, t)?;
    let solution = fundamental.mul(initial)?;
    // Simplify each solution component for a clean result.
    let rows: Vec<Vec<CasExpr>> = (0..n)
        .map(|i| Some(vec![simplify(solution.get(i, 0)?)]))
        .collect::<Option<_>>()?;
    Matrix::from_rows(rows)
}

/// The **Jordan canonical form** of a square rational matrix all of whose
/// eigenvalues are rational: returns `(P, J)` with `J` block-diagonal in Jordan
/// blocks (eigenvalue on the diagonal, `1`s on the super-diagonal) and `A = P·J·P⁻¹`.
///
/// **Certified** by re-multiplication: every entry of `A·P − P·J` is proven zero
/// by the zero-test. Handles **defective** matrices (fewer eigenvectors than the
/// algebraic multiplicity) via generalized-eigenvector chains built from the
/// nullities of `(A−λI)^k`. Returns `None` if `A` is not square, has any
/// irrational/complex eigenvalue (Jordan over ℚ requires a fully rational
/// spectrum), or on overflow — never an uncertified result.
///
/// ```
/// use axeyum_cas::{CasExpr, Matrix, jordan_form, equal, ZeroTest};
/// // A defective shear [[3,1],[0,3]] is its own Jordan form (one 2×2 block).
/// let a = Matrix::from_rows(vec![
///     vec![CasExpr::int(3), CasExpr::int(1)],
///     vec![CasExpr::zero(), CasExpr::int(3)],
/// ]).unwrap();
/// let (_p, j) = jordan_form(&a, "L").unwrap();
/// // J[0][1] = 1 (the super-diagonal of the single Jordan block).
/// assert!(matches!(equal(j.get(0, 1).unwrap(), &CasExpr::int(1)), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn jordan_form(matrix: &Matrix, var: &str) -> Option<(Matrix, Matrix)> {
    let (p, j, _blocks) = jordan_decomposition(matrix, var)?;
    Some((p, j))
}

/// The transform `P`, the Jordan matrix `J`, and the ordered `(eigenvalue, block
/// size)` list of a certified Jordan decomposition (see [`jordan_decomposition`]).
type JordanDecomposition = (Matrix, Matrix, Vec<(Rational, usize)>);

/// The certified Jordan decomposition `(P, J, blocks)` — like [`jordan_form`] but
/// also returning the ordered `(eigenvalue, block size)` list (the block structure
/// [`matrix_exp`] needs to build `exp(J·t)`).
fn jordan_decomposition(matrix: &Matrix, var: &str) -> Option<JordanDecomposition> {
    let n = matrix.rows();
    if n == 0 || n != matrix.cols() {
        return None;
    }
    let eigenvalues = rational_eigenvalues_with_multiplicity(matrix, var)?;
    let total: usize = eigenvalues.iter().map(|(_, m)| *m).sum();
    if total != n {
        return None; // some eigenvalue is irrational/complex — no ℚ Jordan form
    }
    let mut columns: Vec<Matrix> = Vec::new(); // P columns, eigenvector-first per block
    let mut blocks: Vec<(Rational, usize)> = Vec::new(); // (eigenvalue, block size)
    for (lambda, alg_mult) in eigenvalues {
        let shift = scalar_matrix(lambda, n)?; // λ·I
        let bmat = matrix.sub(&shift)?; // B = A − λI
        // Null-space bases `nulls[k]` = ker(B^k), until nullity reaches alg_mult.
        let mut nulls: Vec<Vec<Matrix>> = vec![Vec::new()]; // ker(B^0) = {0}
        let mut power = 1u32;
        loop {
            let basis = bmat.pow(power)?.null_space()?;
            let nullity = basis.len();
            nulls.push(basis);
            if nullity >= alg_mult {
                break;
            }
            power += 1;
            if power as usize > n {
                return None; // safety: nullity failed to reach the algebraic multiplicity
            }
        }
        let top_level = nulls.len() - 1; // largest null level
        let mut chains: Vec<Vec<Matrix>> = Vec::new(); // each chain: [top, B·top, …, eigenvector]
        for ell in (1..=top_level).rev() {
            // Spanning set S = ker(B^{ℓ−1}) ∪ {descending images of longer chains at
            // null-level ℓ}. New chain tops are the ker(B^ℓ) vectors independent of S.
            let mut spanning: Vec<Matrix> = nulls[ell - 1].clone();
            for chain in &chains {
                if chain.len() > ell {
                    spanning.push(chain[chain.len() - ell].clone()); // B^{L−ℓ}·top, null-level ℓ
                }
            }
            for candidate in &nulls[ell] {
                if columns_independent(&spanning, candidate)? {
                    // Build the chain top → eigenvector: [v, Bv, …, B^{ℓ−1}v].
                    let mut chain = Vec::with_capacity(ell);
                    let mut current = candidate.clone();
                    for _ in 0..ell {
                        chain.push(current.clone());
                        current = bmat.mul(&current)?;
                    }
                    spanning.push(candidate.clone());
                    chains.push(chain);
                }
            }
        }
        for chain in chains {
            let size = chain.len();
            for vector in chain.iter().rev() {
                columns.push(vector.clone());
            }
            blocks.push((lambda, size));
        }
    }
    if columns.len() != n {
        return None;
    }
    let p = matrix_from_columns(&columns)?;
    let j = jordan_block_matrix(&blocks, n)?;
    // Certificate: A·P = P·J.
    let left = matrix.mul(&p)?;
    let right = p.mul(&j)?;
    for i in 0..n {
        for col in 0..n {
            if !matches!(
                equal(left.get(i, col)?, right.get(i, col)?),
                ZeroTest::Certified { equal: true, .. }
            ) {
                return None;
            }
        }
    }
    Some((p, j, blocks))
}

/// The rational eigenvalues of a square rational matrix, each with its algebraic
/// multiplicity (its multiplicity as a root of the characteristic polynomial),
/// found by peeling rational linear factors. `None` if the characteristic
/// polynomial is unavailable or on overflow.
fn rational_eigenvalues_with_multiplicity(
    matrix: &Matrix,
    var: &str,
) -> Option<Vec<(Rational, usize)>> {
    let char_poly = characteristic_polynomial(matrix, var)?;
    let mut remaining = poly::rat_trim(normalize(&char_poly)?.to_univariate(var)?);
    let mut out: Vec<(Rational, usize)> = Vec::new();
    while poly::rat_degree(&remaining).unwrap_or(0) >= 1 {
        let Some(&root) = ratint::rational_roots(&remaining)?.first() else {
            break; // remaining factor has no rational root
        };
        let divisor = [root.checked_neg()?, Rational::integer(1)]; // x − root
        let mut multiplicity = 0usize;
        while poly::rat_degree(&remaining).unwrap_or(0) >= 1
            && poly::eval_rat_poly(&remaining, root)?.is_zero()
        {
            remaining = poly::rat_exact_div(&remaining, &divisor)?;
            multiplicity += 1;
        }
        out.push((root, multiplicity));
    }
    Some(out)
}

/// The scalar matrix `c·Iₙ` as a rational-constant [`Matrix`].
fn scalar_matrix(c: Rational, n: usize) -> Option<Matrix> {
    let rows: Vec<Vec<CasExpr>> = (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    if i == j {
                        CasExpr::Const(c)
                    } else {
                        CasExpr::zero()
                    }
                })
                .collect()
        })
        .collect();
    Matrix::from_rows(rows)
}

/// Assemble a matrix from its column vectors (each a `dim × 1` [`Matrix`]). The
/// row dimension is the vectors' length, **not** the number of columns.
fn matrix_from_columns(columns: &[Matrix]) -> Option<Matrix> {
    let dim = columns.first()?.rows();
    let rows: Vec<Vec<CasExpr>> = (0..dim)
        .map(|i| {
            columns
                .iter()
                .map(|col| col.get(i, 0).cloned())
                .collect::<Option<_>>()
        })
        .collect::<Option<_>>()?;
    Matrix::from_rows(rows)
}

/// The block-diagonal Jordan matrix from a list of `(eigenvalue, block size)`
/// blocks (in column order): each block has the eigenvalue on the diagonal and
/// `1`s on the super-diagonal.
fn jordan_block_matrix(blocks: &[(Rational, usize)], n: usize) -> Option<Matrix> {
    let mut data = vec![vec![CasExpr::zero(); n]; n];
    let mut offset = 0;
    for &(lambda, size) in blocks {
        for i in 0..size {
            data[offset + i][offset + i] = CasExpr::Const(lambda);
            if i + 1 < size {
                data[offset + i][offset + i + 1] = CasExpr::one();
            }
        }
        offset += size;
    }
    if offset != n {
        return None;
    }
    Matrix::from_rows(data)
}

/// Whether the column vector `candidate` is linearly independent of the columns in
/// `spanning` (all `n × 1` rational-constant [`Matrix`] vectors): true iff adding
/// it raises the rank. `None` on a non-constant entry or overflow.
fn columns_independent(spanning: &[Matrix], candidate: &Matrix) -> Option<bool> {
    let n = candidate.rows();
    let with: Vec<Matrix> = spanning
        .iter()
        .cloned()
        .chain(std::iter::once(candidate.clone()))
        .collect();
    let rank_without = if spanning.is_empty() {
        0
    } else {
        matrix_rank(&matrix_from_columns(spanning)?)?
    };
    let _ = n;
    let rank_with = matrix_rank(&matrix_from_columns(&with)?)?;
    Some(rank_with > rank_without)
}

/// A square rational-constant matrix as an exact rational grid, or `None` if any
/// entry is not a bare [`CasExpr::Const`].
fn matrix_to_rationals(matrix: &Matrix) -> Option<Vec<Vec<Rational>>> {
    let mut grid = Vec::with_capacity(matrix.rows());
    for i in 0..matrix.rows() {
        let mut row = Vec::with_capacity(matrix.cols());
        for j in 0..matrix.cols() {
            match matrix.get(i, j)? {
                CasExpr::Const(value) => row.push(*value),
                _ => return None,
            }
        }
        grid.push(row);
    }
    Some(grid)
}

/// The outcome of testing whether a `target` vector lies in the span of a `basis`.
enum Dependency {
    /// `target` is not in the span of the basis vectors.
    Independent,
    /// `target = Σ coeffs[j] · basis[j]` exactly.
    Combination(Vec<Rational>),
}

/// Decide whether `target` is an exact rational linear combination of the columns
/// in `basis` (all vectors of equal length), returning the coefficients if so.
/// `None` only on exact-arithmetic overflow. Solved by Gauss–Jordan on the
/// augmented system `[basis | target]`.
fn linear_dependency(basis: &[Vec<Rational>], target: &[Rational]) -> Option<Dependency> {
    let width = basis.len();
    if width == 0 {
        return Some(if target.iter().all(|value| value.is_zero()) {
            Dependency::Combination(Vec::new())
        } else {
            Dependency::Independent
        });
    }
    // Augmented matrix rows: [basis[0][r], …, basis[w-1][r] | target[r]].
    let rows: Vec<Vec<CasExpr>> = (0..target.len())
        .map(|r| {
            let mut row: Vec<CasExpr> = basis.iter().map(|col| CasExpr::Const(col[r])).collect();
            row.push(CasExpr::Const(target[r]));
            row
        })
        .collect();
    let reduced = matrix_to_rationals(&Matrix::from_rows(rows)?.rref()?)?;

    let mut coeffs = vec![Rational::zero(); width];
    let mut determined = vec![false; width];
    for row in &reduced {
        match (0..width).find(|&c| !row[c].is_zero()) {
            Some(pivot) => {
                coeffs[pivot] = row[width];
                determined[pivot] = true;
            }
            None => {
                // No pivot among the unknowns: an all-zero-lhs row with a nonzero
                // rhs is inconsistent, so `target` is not in the span.
                if !row[width].is_zero() {
                    return Some(Dependency::Independent);
                }
            }
        }
    }
    if determined.iter().all(|&d| d) {
        Some(Dependency::Combination(coeffs))
    } else {
        // A free basis column means no unique reading; treat as independent for
        // the minimal-polynomial search (which only feeds independent bases here).
        Some(Dependency::Independent)
    }
}

/// The minimal polynomial of a square rational-constant matrix `A`: the unique
/// monic polynomial `m` of least degree with `m(A) = 0` (the zero matrix).
///
/// Found by the standard power-dependence search — the least `k` for which `Aᵏ`
/// is a rational linear combination of `I, A, …, A^{k−1}` gives
/// `m(x) = xᵏ − Σ cⱼ xʲ`, with the `cⱼ` from that exact combination. Because the
/// combination is found by exact rational elimination, `m(A) = 0` holds exactly:
/// the answer is certified by construction (it is the very identity the solve
/// established). By Cayley–Hamilton the search terminates by `k = n`.
///
/// Returns `None` if the matrix is not square, is non-constant, or on overflow.
#[must_use]
pub fn minimal_polynomial(matrix: &Matrix, var: &str) -> Option<CasExpr> {
    let n = matrix.rows();
    if n == 0 || n != matrix.cols() {
        return None;
    }
    // Guard the constant-entry precondition up front.
    matrix_to_rationals(matrix)?;

    let mut powers: Vec<Vec<Rational>> = Vec::new();
    let mut current = Matrix::identity(n); // A⁰ = I
    for _ in 0..=n {
        let flat: Vec<Rational> = matrix_to_rationals(&current)?
            .into_iter()
            .flatten()
            .collect();
        match linear_dependency(&powers, &flat)? {
            Dependency::Combination(coeffs) => {
                return Some(minimal_polynomial_expr(&coeffs, var));
            }
            Dependency::Independent => {
                powers.push(flat);
                current = current.mul(matrix)?;
            }
        }
    }
    None
}

/// Build `xᵏ − Σ coeffs[j] · xʲ` (with `k = coeffs.len()`) as a canonical
/// [`CasExpr`] — the minimal polynomial from its lower-degree coefficients.
fn minimal_polynomial_expr(coeffs: &[Rational], var: &str) -> CasExpr {
    let degree = u32::try_from(coeffs.len()).unwrap_or(u32::MAX);
    let mut expr = CasExpr::var(var).pow(degree);
    for (power, coeff) in coeffs.iter().enumerate() {
        if coeff.is_zero() {
            continue;
        }
        let monomial = if power == 0 {
            CasExpr::Const(*coeff)
        } else {
            CasExpr::Const(*coeff) * CasExpr::var(var).pow(u32::try_from(power).unwrap_or(u32::MAX))
        };
        expr = expr - monomial;
    }
    expand(&expr).unwrap_or(expr)
}

/// The gradient `∇f = (∂f/∂x₁, …, ∂f/∂xₙ)` of a scalar field, one partial
/// derivative per variable in `vars`. Each component is a certified partial
/// derivative (via [`CasExpr::differentiate`], exact on the algebraic fragment).
#[must_use]
pub fn gradient(expr: &CasExpr, vars: &[&str]) -> Vec<CasExpr> {
    vars.iter()
        .map(|var| {
            let partial = expr.differentiate(var);
            expand(&partial).unwrap_or(partial)
        })
        .collect()
}

/// The Jacobian matrix `J[i][j] = ∂fᵢ/∂xⱼ` of a vector of scalar fields `exprs`
/// with respect to `vars` (rows indexed by `exprs`, columns by `vars`). Each entry
/// is a certified partial derivative. `None` only if the shape is degenerate for
/// [`Matrix::from_rows`] (e.g. `exprs` empty).
#[must_use]
pub fn jacobian(exprs: &[CasExpr], vars: &[&str]) -> Option<Matrix> {
    let rows: Vec<Vec<CasExpr>> = exprs
        .iter()
        .map(|f| {
            vars.iter()
                .map(|var| {
                    let partial = f.differentiate(var);
                    expand(&partial).unwrap_or(partial)
                })
                .collect()
        })
        .collect();
    Matrix::from_rows(rows)
}

/// The divergence `∇·F = Σ ∂Fᵢ/∂xᵢ` of a vector field `field` over coordinates
/// `vars`. Requires `field.len() == vars.len()` and a non-empty field; returns
/// `None` otherwise. The result is expanded to canonical form.
#[must_use]
pub fn divergence(field: &[CasExpr], vars: &[&str]) -> Option<CasExpr> {
    if field.is_empty() || field.len() != vars.len() {
        return None;
    }
    let mut sum = CasExpr::zero();
    for (component, var) in field.iter().zip(vars) {
        sum = sum + component.differentiate(var);
    }
    Some(expand(&sum).unwrap_or(sum))
}

/// The curl `∇×F` of a three-dimensional vector field, returned as its three
/// components. `field` and `vars` must each have length 3 (Cartesian `x, y, z`);
/// returns `None` otherwise. Each component is a difference of certified partial
/// derivatives, expanded to canonical form.
#[must_use]
pub fn curl(field: &[CasExpr], vars: &[&str]) -> Option<[CasExpr; 3]> {
    if field.len() != 3 || vars.len() != 3 {
        return None;
    }
    let (fx, fy, fz) = (&field[0], &field[1], &field[2]);
    let (x, y, z) = (vars[0], vars[1], vars[2]);
    let component = |expr: CasExpr| expand(&expr).unwrap_or(expr);
    Some([
        component(fz.differentiate(y) - fy.differentiate(z)),
        component(fx.differentiate(z) - fz.differentiate(x)),
        component(fy.differentiate(x) - fx.differentiate(y)),
    ])
}

/// The **falling factorial** `base^{(n)} = base·(base−1)···(base−n+1)` (`n` factors;
/// `1` when `n = 0`), expanded to canonical form. Its forward difference obeys the
/// finite-calculus power rule `Δ[x^{(n)}] = n·x^{(n−1)}`.
#[must_use]
pub fn falling_factorial(base: &CasExpr, n: u32) -> CasExpr {
    let factors: Vec<CasExpr> = (0..n)
        .map(|i| base.clone() - CasExpr::int(i128::from(i)))
        .collect();
    let product = match factors.len() {
        0 => return CasExpr::one(),
        1 => factors.into_iter().next().unwrap_or_else(CasExpr::one),
        _ => CasExpr::Mul(factors),
    };
    expand(&product).unwrap_or(product)
}

/// The **rising factorial** (Pochhammer symbol) `base^{(n)↑} =
/// base·(base+1)···(base+n−1)` (`n` factors; `1` when `n = 0`), expanded to
/// canonical form.
#[must_use]
pub fn rising_factorial(base: &CasExpr, n: u32) -> CasExpr {
    let factors: Vec<CasExpr> = (0..n)
        .map(|i| base.clone() + CasExpr::int(i128::from(i)))
        .collect();
    let product = match factors.len() {
        0 => return CasExpr::one(),
        1 => factors.into_iter().next().unwrap_or_else(CasExpr::one),
        _ => CasExpr::Mul(factors),
    };
    expand(&product).unwrap_or(product)
}

/// The **forward difference** `Δf = f(var+1) − f(var)`, expanded to canonical form —
/// the discrete analogue of the derivative.
#[must_use]
pub fn forward_difference(f: &CasExpr, var: &str) -> CasExpr {
    let shifted = f.substitute(var, &(CasExpr::var(var) + CasExpr::int(1)));
    let difference = shifted - f.clone();
    expand(&difference).unwrap_or(difference)
}

/// The **backward difference** `∇f = f(var) − f(var−1)`, expanded to canonical form.
#[must_use]
pub fn backward_difference(f: &CasExpr, var: &str) -> CasExpr {
    let shifted = f.substitute(var, &(CasExpr::var(var) - CasExpr::int(1)));
    let difference = f.clone() - shifted;
    expand(&difference).unwrap_or(difference)
}

/// The **least-squares** best-fit polynomial of the given `degree` through the data
/// `points` `(xᵢ, yᵢ)`, computed exactly by solving the normal equations
/// `AᵀA·c = Aᵀy` over ℚ (where `A` is the `[1, x, …, x^degree]` design matrix).
/// Returns the fit polynomial in `var`. With `degree ≥ points.len() − 1` this
/// reproduces the interpolant exactly; with fewer degrees of freedom it is the exact
/// rational least-squares fit. `None` if there are too few points, the normal matrix
/// is singular, or on overflow.
#[must_use]
pub fn least_squares_polynomial(
    points: &[(Rational, Rational)],
    degree: usize,
    var: &str,
) -> Option<CasExpr> {
    if points.len() < degree + 1 {
        return None;
    }
    let width = degree + 1;
    // Powers x^0..x^{2·degree} summed over the data drive the normal matrix.
    let power_sum = |exp: usize| -> Option<Rational> {
        let mut total = Rational::zero();
        for (x, _) in points {
            let mut term = Rational::integer(1);
            for _ in 0..exp {
                term = term.checked_mul(*x)?;
            }
            total = total.checked_add(term)?;
        }
        Some(total)
    };
    // Normal matrix M[j][k] = Σ xᵢ^{j+k}; RHS b[j] = Σ yᵢ·xᵢ^j.
    let mut normal_rows: Vec<Vec<CasExpr>> = Vec::with_capacity(width);
    let mut rhs_rows: Vec<Vec<CasExpr>> = Vec::with_capacity(width);
    for j in 0..width {
        let mut row = Vec::with_capacity(width);
        for k in 0..width {
            row.push(CasExpr::Const(power_sum(j + k)?));
        }
        normal_rows.push(row);
        let mut b = Rational::zero();
        for (x, y) in points {
            let mut term = *y;
            for _ in 0..j {
                term = term.checked_mul(*x)?;
            }
            b = b.checked_add(term)?;
        }
        rhs_rows.push(vec![CasExpr::Const(b)]);
    }
    let solution = Matrix::from_rows(normal_rows)?.solve(&Matrix::from_rows(rhs_rows)?)?;
    let coeffs: Vec<Rational> = (0..width)
        .map(|j| match solution.get(j, 0)? {
            CasExpr::Const(c) => Some(*c),
            _ => None,
        })
        .collect::<Option<_>>()?;
    Some(MultiPoly::from_univariate(var, &coeffs).to_expr())
}

/// The Hessian matrix `H[i][j] = ∂²f/∂xᵢ∂xⱼ` of a scalar field `f` over `vars` — the
/// symmetric matrix of second partial derivatives, each entry expanded to canonical
/// form and certified (a second partial of the certified `differentiate`). `None`
/// if `vars` is empty.
#[must_use]
pub fn hessian(f: &CasExpr, vars: &[&str]) -> Option<Matrix> {
    let rows: Vec<Vec<CasExpr>> = vars
        .iter()
        .map(|outer| {
            let first = f.differentiate(outer);
            vars.iter()
                .map(|inner| {
                    let second = first.differentiate(inner);
                    expand(&second).unwrap_or(second)
                })
                .collect()
        })
        .collect();
    Matrix::from_rows(rows)
}

/// The Laplacian `∇²f = Σ ∂²f/∂xᵢ²` of a scalar field `f` over `vars`, expanded to
/// canonical form. Certified (a sum of certified second partials).
#[must_use]
pub fn laplacian(f: &CasExpr, vars: &[&str]) -> CasExpr {
    let mut sum = CasExpr::zero();
    for var in vars {
        sum = sum + f.differentiate(var).differentiate(var);
    }
    expand(&sum).unwrap_or(sum)
}

/// The Wronskian `W(f₁, …, fₙ)` of a list of functions in `var` — the determinant of
/// the matrix whose row `j` holds the `j`-th derivatives `fᵢ⁽ʲ⁾`. It vanishes
/// identically iff the functions are linearly dependent (over the fragment the
/// zero-test decides), and appears in variation-of-parameters ODE solutions.
/// Expanded to canonical form. `None` on an empty list or a degenerate matrix shape.
///
/// ```
/// use axeyum_cas::{CasExpr, wronskian, equal, ZeroTest};
/// let x = CasExpr::var("x");
/// // W(x, x²) = det[[x, x²],[1, 2x]] = x².
/// let w = wronskian(&[x.clone(), x.clone().pow(2)], "x").unwrap();
/// assert!(matches!(equal(&w, &x.pow(2)), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn wronskian(functions: &[CasExpr], var: &str) -> Option<CasExpr> {
    let n = functions.len();
    if n == 0 {
        return None;
    }
    let rows: Vec<Vec<CasExpr>> = (0..n)
        .map(|order| {
            functions
                .iter()
                .map(|f| f.differentiate_n(var, order))
                .collect()
        })
        .collect();
    let determinant = Matrix::from_rows(rows)?.determinant()?;
    Some(expand(&determinant).unwrap_or(determinant))
}

/// The LSB-first rational coefficient vector of a univariate polynomial `expr` in
/// `var`, or `None` if `expr` is not a univariate polynomial in `var`.
fn univariate_coeffs(expr: &CasExpr, var: &str) -> Option<Vec<Rational>> {
    normalize(expr)?.to_univariate(var)
}

/// The resultant `Resᵥₐᵣ(a, b)` of two univariate polynomials, as a rational
/// constant. It vanishes **exactly** when `a` and `b` share a root (over an
/// algebraic closure) or a common factor — the classic common-root / elimination
/// test — and is computed as the determinant of the Sylvester matrix.
///
/// Returns `None` if either argument is not a univariate polynomial in `var`, if
/// either has degree 0 (a bare constant), or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, resultant};
/// let x = CasExpr::var("x");
/// // x²−1 and x−1 share the root 1 → resultant 0.
/// let r = resultant(&(x.clone().pow(2) - CasExpr::int(1)), &(x - CasExpr::int(1)), "x").unwrap();
/// assert_eq!(r, CasExpr::int(0));
/// ```
#[must_use]
pub fn resultant(a: &CasExpr, b: &CasExpr, var: &str) -> Option<CasExpr> {
    let coeffs_a = univariate_coeffs(a, var)?;
    let coeffs_b = univariate_coeffs(b, var)?;
    resultant_of_coeffs(&coeffs_a, &coeffs_b).map(CasExpr::Const)
}

/// The Sylvester resultant of two LSB-first rational coefficient vectors, or `None`
/// if either is constant / zero or on overflow.
fn resultant_of_coeffs(a: &[Rational], b: &[Rational]) -> Option<Rational> {
    let deg_a = poly::rat_degree(a)?;
    let deg_b = poly::rat_degree(b)?;
    if deg_a == 0 || deg_b == 0 {
        return None;
    }
    // Each scalar coefficient becomes a constant "polynomial in the surviving
    // variable" so the shared bivariate Sylvester routine applies.
    let p_coeffs: Vec<Vec<Rational>> = a[..=deg_a].iter().map(|c| vec![*c]).collect();
    let q_coeffs: Vec<Vec<Rational>> = b[..=deg_b].iter().map(|c| vec![*c]).collect();
    let matrix = poly::sylvester_matrix(&p_coeffs, &q_coeffs)?;
    // The determinant is a constant polynomial; an empty (trimmed) result is the
    // zero polynomial — i.e. a vanishing resultant (common root/factor).
    let determinant = poly::sylvester_determinant(&matrix)?;
    Some(determinant.first().copied().unwrap_or_else(Rational::zero))
}

/// The discriminant `discᵥₐᵣ(p)` of a univariate polynomial — a rational constant
/// that vanishes **exactly** when `p` has a repeated root. Computed from the
/// resultant of `p` and its derivative:
/// `disc(p) = (−1)^{n(n−1)/2} · Res(p, p′) / lc(p)` with `n = deg p`. A degree-`< 2`
/// polynomial has no repeated root, so its discriminant is `1` by convention.
///
/// For example `disc(x² + b·x + c) = b² − 4c`. Returns `None` if `p` is not a
/// univariate polynomial in `var`, is constant, or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, discriminant};
/// let x = CasExpr::var("x");
/// // disc(x² − 5x + 6) = 25 − 24 = 1 (distinct roots 2, 3).
/// let d = discriminant(&(x.clone().pow(2) - CasExpr::int(5) * x + CasExpr::int(6)), "x").unwrap();
/// assert_eq!(d, CasExpr::int(1));
/// ```
#[must_use]
pub fn discriminant(p: &CasExpr, var: &str) -> Option<CasExpr> {
    let coeffs = univariate_coeffs(p, var)?;
    let degree = poly::rat_degree(&coeffs)?;
    if degree == 0 {
        return None;
    }
    if degree == 1 {
        return Some(CasExpr::one());
    }
    let derivative = univariate_coeffs(&p.differentiate(var), var)?;
    let resultant = resultant_of_coeffs(&coeffs, &derivative)?;
    let leading = coeffs[degree];
    let signed = if (degree * (degree - 1) / 2) % 2 == 0 {
        resultant
    } else {
        resultant.checked_neg()?
    };
    signed.checked_div(leading).map(CasExpr::Const)
}

/// The dot product `a · b = Σ aᵢ·bᵢ` of two equal-length vectors, expanded to
/// canonical form. `None` if the lengths differ or on overflow.
#[must_use]
pub fn dot(a: &[CasExpr], b: &[CasExpr]) -> Option<CasExpr> {
    if a.len() != b.len() {
        return None;
    }
    let mut sum = CasExpr::zero();
    for (left, right) in a.iter().zip(b) {
        sum = sum + left.clone() * right.clone();
    }
    Some(expand(&sum).unwrap_or(sum))
}

/// The cross product `a × b` of two three-dimensional vectors, each component
/// expanded to canonical form. `None` unless both have length 3.
#[must_use]
pub fn cross(a: &[CasExpr], b: &[CasExpr]) -> Option<[CasExpr; 3]> {
    if a.len() != 3 || b.len() != 3 {
        return None;
    }
    let component = |expr: CasExpr| expand(&expr).unwrap_or(expr);
    Some([
        component(a[1].clone() * b[2].clone() - a[2].clone() * b[1].clone()),
        component(a[2].clone() * b[0].clone() - a[0].clone() * b[2].clone()),
        component(a[0].clone() * b[1].clone() - a[1].clone() * b[0].clone()),
    ])
}

/// **Gram–Schmidt orthogonalization** of a list of vectors (each a `Vec<CasExpr>` of
/// the same length): returns a mutually **orthogonal** set spanning the same space,
/// with `uᵢ = vᵢ − Σ_{j<i} (vᵢ·uⱼ / uⱼ·uⱼ) uⱼ`. Linearly dependent inputs contribute
/// a zero vector, which is dropped. Over rational vectors the output stays rational
/// (no normalization/`√`), and every returned pair is certifiably orthogonal
/// (`uᵢ·uⱼ = 0` decides via the zero-test). `None` on empty/mismatched shapes or
/// overflow.
#[must_use]
pub fn gram_schmidt(vectors: &[Vec<CasExpr>]) -> Option<Vec<Vec<CasExpr>>> {
    if vectors.is_empty() {
        return None;
    }
    let dimension = vectors[0].len();
    let mut basis: Vec<Vec<CasExpr>> = Vec::new();
    for vector in vectors {
        if vector.len() != dimension {
            return None;
        }
        // Subtract the projection onto each existing orthogonal vector.
        let mut residual = vector.clone();
        for previous in &basis {
            let numerator = dot(vector, previous)?;
            let denominator = dot(previous, previous)?;
            // coefficient = (vᵢ·uⱼ)/(uⱼ·uⱼ)
            let coefficient = numerator / denominator;
            for (component, prev_component) in residual.iter_mut().zip(previous) {
                let updated = component.clone() - coefficient.clone() * prev_component.clone();
                *component = simplify(&updated);
            }
        }
        // Drop a vector that collapsed to zero (linearly dependent).
        if residual.iter().all(|c| {
            matches!(
                equal(c, &CasExpr::zero()),
                ZeroTest::Certified { equal: true, .. }
            )
        }) {
            continue;
        }
        basis.push(residual);
    }
    Some(basis)
}

/// The Euclidean norm `‖v‖ = √(v · v)` of a vector, as an exact [`CasExpr`] with any
/// surd simplified to lowest terms (`‖(3,4)‖ = 5`, `‖(1,1)‖ = √2`). `None` on
/// overflow. For a constant vector the value is exact and certifiable via the
/// `sqrt(c)²→c` fold.
#[must_use]
pub fn norm(v: &[CasExpr]) -> Option<CasExpr> {
    let square = dot(v, v)?;
    Some(simplify_radicals(&square.sqrt()))
}

/// The LSB-first rational coefficient vector of the `n`-th cyclotomic polynomial
/// `Φₙ`, computed from the defining product `∏_{d∣n} Φ_d(x) = xⁿ − 1` by dividing
/// `xⁿ − 1` by every `Φ_d` with `d ∣ n`, `d < n` (recursively). `None` for `n = 0`
/// or on overflow.
fn cyclotomic_coeffs(n: u64) -> Option<Vec<Rational>> {
    if n == 0 {
        return None;
    }
    let size = usize::try_from(n).ok()?;
    // Start from xⁿ − 1.
    let mut quotient = vec![Rational::zero(); size + 1];
    quotient[0] = Rational::integer(-1);
    quotient[size] = Rational::integer(1);
    // Divide out Φ_d for every proper divisor d of n.
    for divisor in ntheory::divisors(i128::from(n)) {
        let divisor = u64::try_from(divisor).ok()?;
        if divisor < n {
            let phi_d = cyclotomic_coeffs(divisor)?;
            quotient = poly::rat_exact_div(&quotient, &phi_d)?;
        }
    }
    Some(poly::rat_trim(quotient))
}

/// The `n`-th cyclotomic polynomial `Φₙ(var)` — the minimal polynomial over ℚ of a
/// primitive `n`-th root of unity — as an (expanded) [`CasExpr`]. For example
/// `Φ₁ = x−1`, `Φ₂ = x+1`, `Φ₄ = x²+1`, `Φ₆ = x²−x+1`.
///
/// Built from the identity `∏_{d∣n} Φ_d(x) = xⁿ − 1`, which is also its
/// certificate (the product of `Φ_d` over all divisors re-multiplies to `xⁿ − 1`,
/// checkable by [`equal`]). Returns `None` for `n = 0` or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, cyclotomic_polynomial, equal, ZeroTest};
/// let x = CasExpr::var("x");
/// // Φ₆(x) = x² − x + 1.
/// let phi6 = cyclotomic_polynomial(6, "x").unwrap();
/// let expected = x.clone().pow(2) - x + CasExpr::int(1);
/// assert!(matches!(equal(&phi6, &expected), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn cyclotomic_polynomial(n: u64, var: &str) -> Option<CasExpr> {
    let coeffs = cyclotomic_coeffs(n)?;
    Some(MultiPoly::from_univariate(var, &coeffs).to_expr())
}

/// Factor a non-negative integer `n` as `s²·m` with `m` square-free, returning
/// `(s, m)` — the data needed to pull the largest perfect square out of a radical.
/// `None` on overflow.
fn largest_square_factor(n: i128) -> Option<(i128, i128)> {
    let mut square_root = 1i128;
    let mut squarefree = 1i128;
    for (prime, exponent) in ntheory::factorize(n) {
        for _ in 0..(exponent / 2) {
            square_root = square_root.checked_mul(prime)?;
        }
        if exponent % 2 == 1 {
            squarefree = squarefree.checked_mul(prime)?;
        }
    }
    Some((square_root, squarefree))
}

/// Simplify `√c` for a non-negative rational constant `c` into `k·√m` with `m`
/// square-free (and to a bare rational when `m = 1`), rationalizing any
/// denominator. Returns `None` for a negative radicand (left symbolic) or on
/// overflow. The rewrite is exact by construction: `k²·m = c`, an integer identity.
fn simplify_sqrt_const(value: Rational) -> Option<CasExpr> {
    let numerator = value.numerator();
    let denominator = value.denominator(); // normalized positive
    if numerator < 0 {
        return None; // negative radicand — not a real simplification here
    }
    if numerator == 0 {
        return Some(CasExpr::zero());
    }
    // √(a/b) = √(a·b)/b; pull the square part out of the integer a·b.
    let radicand = numerator.checked_mul(denominator)?;
    let (square_root, squarefree) = largest_square_factor(radicand)?;
    let coefficient = Rational::checked_new(square_root, denominator)?;
    if squarefree == 1 {
        return Some(CasExpr::Const(coefficient));
    }
    let radical = CasExpr::Const(Rational::integer(squarefree)).sqrt();
    if coefficient == Rational::integer(1) {
        Some(radical)
    } else {
        Some(CasExpr::Const(coefficient) * radical)
    }
}

/// Simplify an expression **under sign assumptions**, applying rewrites that are
/// only sound given the assumed signs: `|u| → u` when `u ≥ 0` (or `−u` when `u ≤ 0`),
/// and `√(b²ᵏ) → bᵏ` (rather than `|bᵏ|`) when `b ≥ 0`. Recurses structurally; parts
/// whose sign is unknown are left as-is. This is the sound counterpart to
/// [`simplify_radicals`]' unconditional `√(x²) → |x|`.
///
/// ```
/// use axeyum_cas::{CasExpr, Assumptions, simplify_under_assumptions, equal, ZeroTest};
/// let x = CasExpr::var("x");
/// // Under x ≥ 0, √(x²) = x (not |x|).
/// let simplified = simplify_under_assumptions(&x.clone().pow(2).sqrt(), &Assumptions::new().nonnegative("x"));
/// assert!(matches!(equal(&simplified, &x), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn simplify_under_assumptions(expr: &CasExpr, assumptions: &Assumptions) -> CasExpr {
    match expr {
        CasExpr::Unary(UnaryFunc::Abs, arg) => {
            let inner = simplify_under_assumptions(arg, assumptions);
            let sign = assumptions.sign_of(&inner);
            if sign.is_nonnegative() {
                inner
            } else if matches!(sign, Sign::Negative | Sign::Nonpositive | Sign::Zero) {
                simplify(&CasExpr::Neg(Box::new(inner)))
            } else {
                inner.abs()
            }
        }
        CasExpr::Unary(UnaryFunc::Sqrt, arg) => {
            let inner = simplify_under_assumptions(arg, assumptions);
            // √(b^{2k}) = bᵏ when b ≥ 0.
            if let CasExpr::Pow(base, exponent) = &inner
                && exponent % 2 == 0
                && assumptions.is_nonnegative(base)
            {
                let half = exponent / 2;
                return if half == 1 {
                    (**base).clone()
                } else {
                    CasExpr::Pow(base.clone(), half)
                };
            }
            simplify_radicals(&inner.sqrt())
        }
        CasExpr::Unary(func, arg) => CasExpr::Unary(
            *func,
            Box::new(simplify_under_assumptions(arg, assumptions)),
        ),
        CasExpr::Add(terms) => CasExpr::Add(
            terms
                .iter()
                .map(|t| simplify_under_assumptions(t, assumptions))
                .collect(),
        ),
        CasExpr::Mul(factors) => CasExpr::Mul(
            factors
                .iter()
                .map(|f| simplify_under_assumptions(f, assumptions))
                .collect(),
        ),
        CasExpr::Neg(inner) => {
            CasExpr::Neg(Box::new(simplify_under_assumptions(inner, assumptions)))
        }
        CasExpr::Div(a, b) => CasExpr::Div(
            Box::new(simplify_under_assumptions(a, assumptions)),
            Box::new(simplify_under_assumptions(b, assumptions)),
        ),
        CasExpr::Pow(base, exp) => CasExpr::Pow(
            Box::new(simplify_under_assumptions(base, assumptions)),
            *exp,
        ),
        CasExpr::Const(_) | CasExpr::Var(_) => expr.clone(),
    }
}

/// Simplify surds throughout an expression: rewrite every `√c` on a non-negative
/// rational constant `c` into `k·√m` with `m` square-free (extracting perfect
/// squares and rationalizing denominators, e.g. `√12 → 2·√3`, `√(1/2) → (1/2)·√2`).
/// Other subexpressions are recursed into structurally and left otherwise
/// unchanged. Each rewrite is exact (`k²·m = c`), so the result is value-equal to
/// the input by construction.
#[must_use]
pub fn simplify_radicals(expr: &CasExpr) -> CasExpr {
    match expr {
        CasExpr::Unary(UnaryFunc::Sqrt, arg) => {
            let inner = simplify_radicals(arg);
            if let CasExpr::Const(value) = inner
                && let Some(simplified) = simplify_sqrt_const(value)
            {
                return simplified;
            }
            // √(b^{2k}) = |b^k| (always non-negative), a sound identity.
            if let CasExpr::Pow(base, exponent) = &inner
                && exponent % 2 == 0
            {
                let half = exponent / 2;
                let root = if half == 1 {
                    (**base).clone()
                } else {
                    CasExpr::Pow(base.clone(), half)
                };
                return root.abs();
            }
            inner.sqrt()
        }
        CasExpr::Unary(func, arg) => CasExpr::Unary(*func, Box::new(simplify_radicals(arg))),
        CasExpr::Add(terms) => CasExpr::Add(terms.iter().map(simplify_radicals).collect()),
        CasExpr::Mul(factors) => {
            fold_trivial(&CasExpr::Mul(factors.iter().map(simplify_radicals).collect()))
        }
        CasExpr::Neg(inner) => CasExpr::Neg(Box::new(simplify_radicals(inner))),
        CasExpr::Div(numerator, denominator) => {
            let num = simplify_radicals(numerator);
            let den = simplify_radicals(denominator);
            // A constant denominator folds into the numerator's rational content
            // (`(2√2)/2 → √2`): fold_trivial combines the constants after flattening.
            if let CasExpr::Const(d) = den
                && !d.is_zero()
                && let Some(inv) = Rational::integer(1).checked_div(d)
            {
                fold_trivial(&CasExpr::Mul(vec![CasExpr::Const(inv), num]))
            } else {
                CasExpr::Div(Box::new(num), Box::new(den))
            }
        }
        CasExpr::Pow(base, exponent) => CasExpr::Pow(Box::new(simplify_radicals(base)), *exponent),
        CasExpr::Const(_) | CasExpr::Var(_) => expr.clone(),
    }
}

/// The **population** standard deviation `√variance` of rational data, returned as
/// an exact [`CasExpr`] with any surd simplified to lowest terms. `None` if `data`
/// is empty or on overflow.
#[must_use]
pub fn standard_deviation(data: &[Rational]) -> Option<CasExpr> {
    let variance = stats::variance(data)?;
    Some(simplify_radicals(&CasExpr::Const(variance).sqrt()))
}

/// The **Pearson correlation coefficient** `ρ = cov(x,y) / (σₓ·σᵧ)` of two data
/// sets, as an exact [`CasExpr`] with surds simplified (`ρ = ±1` for perfectly
/// linearly related data). `None` if the lengths differ, either has zero variance,
/// or on overflow.
#[must_use]
pub fn correlation(xs: &[Rational], ys: &[Rational]) -> Option<CasExpr> {
    let cov = stats::covariance(xs, ys)?;
    let var_x = stats::variance(xs)?;
    let var_y = stats::variance(ys)?;
    if var_x.is_zero() || var_y.is_zero() {
        return None;
    }
    // ρ = cov / √(var_x · var_y).
    let denom = simplify_radicals(&CasExpr::Const(var_x.checked_mul(var_y)?).sqrt());
    Some(simplify(&(CasExpr::Const(cov) / denom)))
}

/// The **sample** standard deviation `√(sample variance)` of rational data (with
/// Bessel's `n − 1` correction), as an exact [`CasExpr`] with any surd simplified.
/// `None` if `data` has fewer than two points or on overflow.
#[must_use]
pub fn sample_standard_deviation(data: &[Rational]) -> Option<CasExpr> {
    let variance = stats::sample_variance(data)?;
    Some(simplify_radicals(&CasExpr::Const(variance).sqrt()))
}

/// The constant value of a [`MultiPoly`] (the empty polynomial is `0`), or `None`
/// if it is not constant.
fn multipoly_as_constant(poly: &MultiPoly) -> Option<Rational> {
    if poly.terms.is_empty() {
        return Some(Rational::zero());
    }
    if poly.terms.len() == 1 {
        let (monomial, coeff) = poly.terms.iter().next()?;
        if monomial.powers.is_empty() {
            return Some(*coeff);
        }
    }
    None
}

/// If `arg` is a rational multiple of the reserved constant `pi` (the variable
/// named `"pi"`), return that rational coefficient `c` (so `arg = c·π`); `Some(0)`
/// for the constant `0`. Handles a constant denominator (e.g. `π/6`). `None` for
/// any other shape.
fn pi_coefficient(arg: &CasExpr) -> Option<Rational> {
    let ratio = normalize_rational(arg)?;
    let denominator = multipoly_as_constant(&ratio.den)?;
    if ratio.num.terms.is_empty() {
        return Some(Rational::zero());
    }
    if ratio.num.terms.len() != 1 {
        return None;
    }
    let (monomial, coeff) = ratio.num.terms.iter().next()?;
    if monomial.powers.len() == 1 && monomial.powers.get("pi") == Some(&1) {
        coeff.checked_div(denominator)
    } else {
        None
    }
}

/// The exact value of `sin(k · 15°)` = `sin(k·π/12)` for `k` reduced mod 24 — the
/// unit-circle table at every multiple of `π/12`, with surds in lowest terms.
fn sine_at_twelfth(k: usize) -> CasExpr {
    let half = || CasExpr::rat(1, 2);
    let root = |n| CasExpr::int(n).sqrt();
    let root2_2 = || CasExpr::rat(1, 2) * root(2); // √2/2
    let root3_2 = || CasExpr::rat(1, 2) * root(3); // √3/2
    let s15 = || CasExpr::rat(1, 4) * root(6) - CasExpr::rat(1, 4) * root(2); // (√6−√2)/4
    let s75 = || CasExpr::rat(1, 4) * root(6) + CasExpr::rat(1, 4) * root(2); // (√6+√2)/4
    match k % 24 {
        1 | 11 => s15(),
        2 | 10 => half(),
        3 | 9 => root2_2(),
        4 | 8 => root3_2(),
        5 | 7 => s75(),
        6 => CasExpr::one(),
        13 | 23 => -s15(),
        14 | 22 => -half(),
        15 | 21 => -root2_2(),
        16 | 20 => -root3_2(),
        17 | 19 => -s75(),
        18 => CasExpr::int(-1),
        _ => CasExpr::zero(), // 0 and 12 (and, unreachably, anything ≥ 24)
    }
}

/// The exact value of a trig head at a rational multiple of `π`, or `None` if the
/// argument is not `c·π` with `12c` an integer (a multiple of `π/12`), or if the
/// value is a pole (`tan` at `π/2 + kπ`).
fn trig_special_value(func: UnaryFunc, arg: &CasExpr) -> Option<CasExpr> {
    let coeff = pi_coefficient(arg)?;
    // Index in twelfths of a half-turn: k = 12·c, reduced mod 24.
    let scaled = coeff.checked_mul(Rational::integer(12))?;
    if scaled.denominator() != 1 {
        return None;
    }
    let k = usize::try_from(scaled.numerator().rem_euclid(24)).ok()?;
    match func {
        UnaryFunc::Sin => Some(sine_at_twelfth(k)),
        UnaryFunc::Cos => Some(sine_at_twelfth(k + 6)), // cos θ = sin(θ + π/2)
        UnaryFunc::Tan => {
            let cosine = sine_at_twelfth(k + 6);
            if matches!(
                equal(&cosine, &CasExpr::zero()),
                ZeroTest::Certified { equal: true, .. }
            ) {
                None // pole at π/2 + kπ
            } else {
                let value = simplify(&(sine_at_twelfth(k) / cosine));
                Some(simplify_radicals(&value))
            }
        }
        _ => None,
    }
}

/// Evaluate the trigonometric heads `sin`, `cos`, `tan` at rational multiples of
/// the reserved constant `pi` to their **exact** values (`sin(π/6) = 1/2`,
/// `cos(π/4) = √2/2`, `tan(π/3) = √3`), throughout an expression. Every multiple of
/// `π/12` is tabulated (with surds in lowest terms); `tan` poles and non-special
/// angles are left unevaluated. Other subexpressions are recursed into
/// structurally.
///
/// This is a **compute** operation — the returned values come from the exact
/// unit-circle table, definitionally, not from a zero-test certificate. The
/// constant `π` is the variable named `"pi"`.
///
/// ```
/// use axeyum_cas::{CasExpr, evaluate_trig, equal, ZeroTest};
/// let pi = CasExpr::var("pi");
/// // sin(π/6) = 1/2.
/// let value = evaluate_trig(&(pi / CasExpr::int(6)).sin());
/// assert!(matches!(equal(&value, &CasExpr::rat(1, 2)), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn evaluate_trig(expr: &CasExpr) -> CasExpr {
    match expr {
        CasExpr::Unary(func @ (UnaryFunc::Sin | UnaryFunc::Cos | UnaryFunc::Tan), arg) => {
            let inner = evaluate_trig(arg);
            trig_special_value(*func, &inner)
                .unwrap_or_else(|| CasExpr::Unary(*func, Box::new(inner)))
        }
        CasExpr::Unary(func, arg) => CasExpr::Unary(*func, Box::new(evaluate_trig(arg))),
        CasExpr::Add(terms) => CasExpr::Add(terms.iter().map(evaluate_trig).collect()),
        CasExpr::Mul(factors) => CasExpr::Mul(factors.iter().map(evaluate_trig).collect()),
        CasExpr::Neg(inner) => CasExpr::Neg(Box::new(evaluate_trig(inner))),
        CasExpr::Div(numerator, denominator) => CasExpr::Div(
            Box::new(evaluate_trig(numerator)),
            Box::new(evaluate_trig(denominator)),
        ),
        CasExpr::Pow(base, exponent) => CasExpr::Pow(Box::new(evaluate_trig(base)), *exponent),
        CasExpr::Const(_) | CasExpr::Var(_) => expr.clone(),
    }
}

/// The **Bernoulli polynomial** `Bₙ(x) = Σ_{k=0}^n C(n,k)·B_k·x^{n−k}` (with `B_k`
/// the Bernoulli numbers, `B₁ = −1/2`), as an exact [`CasExpr`] polynomial in `var`.
/// `B₀=1`, `B₁(x)=x−1/2`, `B₂(x)=x²−x+1/6`, `B₃(x)=x³−(3/2)x²+(1/2)x`. Satisfies
/// `Bₙ′(x)=n·Bₙ₋₁(x)` and `Bₙ(x+1)−Bₙ(x)=n·x^{n−1}`. `None` on `i128` overflow of a
/// Bernoulli numerator/denominator or a binomial coefficient (large `n`).
///
/// ```
/// use axeyum_cas::{CasExpr, bernoulli_polynomial, equal, ZeroTest};
/// // B₂(x) = x² − x + 1/6.
/// let b2 = bernoulli_polynomial(2, "x").unwrap();
/// let expected = CasExpr::var("x").pow(2) - CasExpr::var("x") + CasExpr::rat(1, 6);
/// assert!(matches!(equal(&b2, &expected), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn bernoulli_polynomial(n: u32, var: &str) -> Option<CasExpr> {
    let mut terms: Vec<CasExpr> = Vec::new();
    for k in 0..=n {
        let bernoulli = combinatorics::bernoulli(k)?;
        if bernoulli.is_zero() {
            continue;
        }
        let binomial = ntheory::binomial(i128::from(n), i128::from(k))?;
        let coeff = bernoulli.checked_mul(Rational::integer(binomial))?;
        let power = n - k;
        let monomial = match power {
            0 => CasExpr::Const(coeff),
            1 => scaled_term(coeff, CasExpr::var(var)),
            _ => scaled_term(coeff, CasExpr::var(var).pow(power)),
        };
        terms.push(monomial);
    }
    Some(match terms.len() {
        0 => CasExpr::zero(),
        1 => terms.into_iter().next().unwrap_or_else(CasExpr::zero),
        _ => CasExpr::Add(terms),
    })
}

/// The **Euler polynomial** `Eₙ(x)`, as an exact [`CasExpr`] polynomial in `var`,
/// via the Bernoulli relation `Eₙ(x) = (2^{n+1}/(n+1))·(B_{n+1}((x+1)/2) −
/// B_{n+1}(x/2))`. `E₀=1`, `E₁(x)=x−1/2`, `E₂(x)=x²−x`, `E₃(x)=x³−(3/2)x²+1/4`.
/// Satisfies `Eₙ′(x)=n·Eₙ₋₁(x)` and `Eₙ(x+1)+Eₙ(x)=2xⁿ`. `None` on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, euler_polynomial, equal, ZeroTest};
/// // E₂(x) = x² − x.
/// let e2 = euler_polynomial(2, "x").unwrap();
/// let expected = CasExpr::var("x").pow(2) - CasExpr::var("x");
/// assert!(matches!(equal(&e2, &expected), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn euler_polynomial(n: u32, var: &str) -> Option<CasExpr> {
    let bernoulli = bernoulli_polynomial(n.checked_add(1)?, var)?;
    let x = CasExpr::var(var);
    let upper = bernoulli.substitute(var, &((x.clone() + CasExpr::int(1)) / CasExpr::int(2)));
    let lower = bernoulli.substitute(var, &(x / CasExpr::int(2)));
    // scale = 2^{n+1} / (n+1).
    let two_pow = 2i128.checked_pow(n.checked_add(1)?)?;
    let scale = Rational::checked_new(two_pow, i128::from(n) + 1)?;
    let raw = CasExpr::Const(scale) * (upper - lower);
    // `raw` normalizes to `num / c` with a constant `c` (Eₙ is a polynomial);
    // distribute `1/c` across the numerator so the rational coefficients collapse
    // (`(64x − 32)/64 → x − 1/2`) rather than leaving an uncancelled unit denominator.
    let rf = normalize_rational(&raw)?;
    let CasExpr::Const(c) = rf.den.to_expr() else {
        return expand(&raw);
    };
    let inv = Rational::integer(1).checked_div(c)?;
    expand(&(CasExpr::Const(inv) * rf.num.to_expr()))
}

/// Fold every elementary head at an argument where it has an exact closed value:
/// the trigonometric special values of [`evaluate_trig`] (`sin`/`cos`/`tan` at
/// rational multiples of `π`) **plus** `exp(0)=1`, `ln(1)=0`, `sqrt(0)=0`,
/// `sqrt(1)=1`, `atan(0)=0`. Applied to a definite integral's `F(b) − F(a)` so
/// results like `∫₀^π sin x = cos 0 − cos π` collapse to `2` and `ln 1` vanishes.
/// Non-special arguments are left untouched; recurses structurally.
fn fold_elementary_constants(expr: &CasExpr) -> CasExpr {
    match expr {
        CasExpr::Unary(func, arg) => {
            let inner = fold_elementary_constants(arg);
            match (func, &inner) {
                (UnaryFunc::Sin | UnaryFunc::Cos | UnaryFunc::Tan, _) => {
                    trig_special_value(*func, &inner)
                        .unwrap_or_else(|| CasExpr::Unary(*func, Box::new(inner)))
                }
                (UnaryFunc::Exp, CasExpr::Const(c)) if c.is_zero() => CasExpr::one(),
                (UnaryFunc::Ln, CasExpr::Const(c)) if *c == Rational::integer(1) => {
                    CasExpr::zero()
                }
                (UnaryFunc::Atan, CasExpr::Const(c)) if c.is_zero() => CasExpr::zero(),
                (UnaryFunc::Sqrt, CasExpr::Const(c)) if c.is_zero() => CasExpr::zero(),
                (UnaryFunc::Sqrt, CasExpr::Const(c)) if *c == Rational::integer(1) => {
                    CasExpr::one()
                }
                _ => CasExpr::Unary(*func, Box::new(inner)),
            }
        }
        CasExpr::Add(terms) => {
            CasExpr::Add(terms.iter().map(fold_elementary_constants).collect())
        }
        CasExpr::Mul(factors) => {
            CasExpr::Mul(factors.iter().map(fold_elementary_constants).collect())
        }
        CasExpr::Neg(inner) => CasExpr::Neg(Box::new(fold_elementary_constants(inner))),
        CasExpr::Div(numerator, denominator) => CasExpr::Div(
            Box::new(fold_elementary_constants(numerator)),
            Box::new(fold_elementary_constants(denominator)),
        ),
        CasExpr::Pow(base, exponent) => {
            CasExpr::Pow(Box::new(fold_elementary_constants(base)), *exponent)
        }
        CasExpr::Const(_) | CasExpr::Var(_) => expr.clone(),
    }
}

/// Rewrite trigonometric heads via **Euler's formula** into complex exponentials:
/// `cos(u) → (e^{iu} + e^{−iu})/2`, `sin(u) → (e^{iu} − e^{−iu})/(2i)`,
/// `tan(u) → sin/cos`, throughout an expression (`i` is the reserved imaginary
/// unit). Combined with the exp tower and the `i² = −1` fold in the zero-test, this
/// turns **all polynomial trigonometric identities decidable**: comparing the
/// exponential rewrites of two sides via [`equal`] certifies double-angle,
/// sum/difference, product-to-sum, and power-reduction identities.
///
/// This is a sound, denotation-preserving rewrite (Euler's formula is an identity).
///
/// ```
/// use axeyum_cas::{CasExpr, rewrite_exp, equal, ZeroTest};
/// let x = CasExpr::var("x");
/// // cos(2x) = 2cos²x − 1, decided after the Euler rewrite.
/// let lhs = rewrite_exp(&(CasExpr::int(2) * x.clone()).cos());
/// let rhs = rewrite_exp(&(CasExpr::int(2) * x.clone().cos().pow(2) - CasExpr::int(1)));
/// assert!(matches!(equal(&lhs, &rhs), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn rewrite_exp(expr: &CasExpr) -> CasExpr {
    match expr {
        CasExpr::Unary(UnaryFunc::Cos, arg) => {
            let u = rewrite_exp(arg);
            let i = CasExpr::imaginary_unit();
            let plus = (i.clone() * u.clone()).exp();
            let minus = (-(i * u)).exp();
            (plus + minus) / CasExpr::int(2)
        }
        CasExpr::Unary(UnaryFunc::Sin, arg) => {
            let u = rewrite_exp(arg);
            let i = CasExpr::imaginary_unit();
            let plus = (i.clone() * u.clone()).exp();
            let minus = (-(i.clone() * u)).exp();
            (plus - minus) / (CasExpr::int(2) * i)
        }
        CasExpr::Unary(UnaryFunc::Tan, arg) => {
            let sin = rewrite_exp(&CasExpr::Unary(UnaryFunc::Sin, arg.clone()));
            let cos = rewrite_exp(&CasExpr::Unary(UnaryFunc::Cos, arg.clone()));
            sin / cos
        }
        CasExpr::Unary(func, arg) => CasExpr::Unary(*func, Box::new(rewrite_exp(arg))),
        CasExpr::Add(terms) => CasExpr::Add(terms.iter().map(rewrite_exp).collect()),
        CasExpr::Mul(factors) => CasExpr::Mul(factors.iter().map(rewrite_exp).collect()),
        CasExpr::Neg(inner) => CasExpr::Neg(Box::new(rewrite_exp(inner))),
        CasExpr::Div(numerator, denominator) => CasExpr::Div(
            Box::new(rewrite_exp(numerator)),
            Box::new(rewrite_exp(denominator)),
        ),
        CasExpr::Pow(base, exponent) => CasExpr::Pow(Box::new(rewrite_exp(base)), *exponent),
        CasExpr::Const(_) | CasExpr::Var(_) => expr.clone(),
    }
}

/// Expand logarithms by the product/quotient/power rules: `ln(a·b) → ln a + ln b`,
/// `ln(a/b) → ln a − ln b`, `ln(aⁿ) → n·ln a`, applied recursively throughout an
/// expression (and inside the arguments of other heads).
///
/// This is a **compute** operation labelled as such: the rules hold for positive
/// real arguments, which axeyum does not yet track (the assumptions engine is
/// future work), so `expand_log` is offered as an explicit transform rather than a
/// certified rewrite — mirroring the `force=True` mode of mainstream systems.
///
/// ```
/// use axeyum_cas::{CasExpr, expand_log, equal, ZeroTest};
/// let x = CasExpr::var("x");
/// let y = CasExpr::var("y");
/// // ln(x²·y) → 2·ln(x) + ln(y).
/// let expanded = expand_log(&(x.clone().pow(2) * y.clone()).ln());
/// let expected = CasExpr::int(2) * x.ln() + y.ln();
/// assert!(matches!(equal(&expanded, &expected), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn expand_log(expr: &CasExpr) -> CasExpr {
    match expr {
        CasExpr::Unary(UnaryFunc::Ln, arg) => expand_log_argument(&expand_log(arg)),
        CasExpr::Unary(func, arg) => CasExpr::Unary(*func, Box::new(expand_log(arg))),
        CasExpr::Add(terms) => CasExpr::Add(terms.iter().map(expand_log).collect()),
        CasExpr::Mul(factors) => CasExpr::Mul(factors.iter().map(expand_log).collect()),
        CasExpr::Neg(inner) => CasExpr::Neg(Box::new(expand_log(inner))),
        CasExpr::Div(numerator, denominator) => CasExpr::Div(
            Box::new(expand_log(numerator)),
            Box::new(expand_log(denominator)),
        ),
        CasExpr::Pow(base, exponent) => CasExpr::Pow(Box::new(expand_log(base)), *exponent),
        CasExpr::Const(_) | CasExpr::Var(_) => expr.clone(),
    }
}

/// Apply the log laws to `ln(arg)` for a single (already log-expanded) argument.
fn expand_log_argument(arg: &CasExpr) -> CasExpr {
    match arg {
        CasExpr::Mul(factors) => CasExpr::Add(factors.iter().map(expand_log_argument).collect()),
        CasExpr::Div(numerator, denominator) => {
            expand_log_argument(numerator) - expand_log_argument(denominator)
        }
        CasExpr::Pow(base, exponent) => {
            CasExpr::int(i128::from(*exponent)) * expand_log_argument(base)
        }
        other => other.clone().ln(),
    }
}

/// If `term` is `c·ln(u)` for an **integer** `c` (including `ln u` and `−ln u`),
/// return `(c, u)`; `None` otherwise.
fn as_log_term(term: &CasExpr) -> Option<(i128, CasExpr)> {
    match term {
        CasExpr::Unary(UnaryFunc::Ln, arg) => Some((1, (**arg).clone())),
        CasExpr::Neg(inner) => {
            let (c, u) = as_log_term(inner)?;
            Some((c.checked_neg()?, u))
        }
        CasExpr::Mul(factors) => {
            // Exactly one `ln` factor and the rest integer constants.
            let mut coeff = 1i128;
            let mut logarg: Option<CasExpr> = None;
            for factor in factors {
                match factor {
                    CasExpr::Const(c) if c.denominator() == 1 => {
                        coeff = coeff.checked_mul(c.numerator())?;
                    }
                    CasExpr::Unary(UnaryFunc::Ln, arg) if logarg.is_none() => {
                        logarg = Some((**arg).clone());
                    }
                    _ => return None,
                }
            }
            logarg.map(|u| (coeff, u))
        }
        _ => None,
    }
}

/// Combine logarithms — the inverse of [`expand_log`]: `ln a + ln b → ln(a·b)`,
/// `c·ln a → ln(aᶜ)` (integer `c`), `ln a − ln b → ln(a/b)`, collecting all
/// integer-coefficient `ln` terms of a sum into a single logarithm. Recurses into
/// subexpressions. A **compute** rewrite (sound for positive real arguments, which
/// axeyum does not yet track — like `expand_log`).
///
/// ```
/// use axeyum_cas::{CasExpr, logcombine, equal, ZeroTest};
/// let x = CasExpr::var("x");
/// let y = CasExpr::var("y");
/// // ln x + ln y → ln(x·y).
/// let combined = logcombine(&(x.clone().ln() + y.clone().ln()));
/// assert!(matches!(equal(&combined, &(x * y).ln()), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn logcombine(expr: &CasExpr) -> CasExpr {
    // `c·ln u → ln(uᶜ)` as a `CasExpr` for an integer coefficient.
    let as_ln_power = |coeff: i128, arg: &CasExpr| -> CasExpr {
        let power = u32::try_from(coeff.unsigned_abs()).unwrap_or(u32::MAX);
        if coeff >= 0 {
            arg.clone().pow(power)
        } else {
            CasExpr::int(1) / arg.clone().pow(power)
        }
    };
    match expr {
        CasExpr::Add(terms) => {
            let mut log_argument = CasExpr::int(1); // ∏ uᵢ^{cᵢ}
            let mut has_log = false;
            let mut others: Vec<CasExpr> = Vec::new();
            for term in terms {
                if let Some((coeff, arg)) = as_log_term(term) {
                    has_log = true;
                    log_argument = log_argument * as_ln_power(coeff, &arg);
                } else {
                    others.push(logcombine(term));
                }
            }
            if !has_log {
                return CasExpr::Add(others);
            }
            let mut result = simplify(&log_argument).ln();
            for other in others {
                result = result + other;
            }
            result
        }
        // A standalone `c·ln u` term also combines to `ln(uᶜ)`.
        _ if as_log_term(expr).is_some() => {
            let (coeff, arg) = as_log_term(expr).unwrap_or((1, expr.clone()));
            simplify(&as_ln_power(coeff, &arg)).ln()
        }
        CasExpr::Mul(factors) => CasExpr::Mul(factors.iter().map(logcombine).collect()),
        CasExpr::Neg(inner) => CasExpr::Neg(Box::new(logcombine(inner))),
        CasExpr::Div(a, b) => CasExpr::Div(Box::new(logcombine(a)), Box::new(logcombine(b))),
        CasExpr::Pow(base, exp) => CasExpr::Pow(Box::new(logcombine(base)), *exp),
        CasExpr::Unary(func, arg) => CasExpr::Unary(*func, Box::new(logcombine(arg))),
        CasExpr::Const(_) | CasExpr::Var(_) => expr.clone(),
    }
}

/// Recover the "nicest" exact rational approximating an `f64` `x` whose denominator
/// does not exceed `max_denominator`, via the continued-fraction convergents (each
/// convergent is the best rational approximation for its denominator size). For
/// example `rationalize(0.5, 100) = 1/2`, `rationalize(0.3333…, 100) = 1/3`, and
/// `rationalize(π, 1000) = 355/113`. `None` on overflow or a non-finite input.
#[must_use]
#[allow(clippy::cast_possible_truncation, clippy::cast_precision_loss)] // CF on f64
pub fn rationalize(x: f64, max_denominator: i128) -> Option<Rational> {
    if !x.is_finite() || max_denominator < 1 {
        return None;
    }
    let negative = x < 0.0;
    let mut value = x.abs();
    // Convergent recurrence hₙ = aₙhₙ₋₁ + hₙ₋₂, kₙ likewise.
    let (mut h_prev, mut h_curr) = (0i128, 1i128);
    let (mut k_prev, mut k_curr) = (1i128, 0i128);
    for _ in 0..64 {
        let a = value.floor() as i128;
        let h_next = a.checked_mul(h_curr)?.checked_add(h_prev)?;
        let k_next = a.checked_mul(k_curr)?.checked_add(k_prev)?;
        if k_next > max_denominator {
            break;
        }
        (h_prev, h_curr) = (h_curr, h_next);
        (k_prev, k_curr) = (k_curr, k_next);
        let fraction = value - a as f64;
        if fraction.abs() < 1e-12 {
            break;
        }
        value = 1.0 / fraction;
    }
    if k_curr == 0 {
        return None;
    }
    let numerator = if negative {
        h_curr.checked_neg()?
    } else {
        h_curr
    };
    Rational::checked_new(numerator, k_curr)
}

/// Numerically approximate an expression as an `f64`, given `bindings` for its free
/// variables. Rational constants are exact-to-`f64`; the transcendental heads map to
/// the corresponding `f64` functions; the reserved constant `pi` defaults to π. A
/// **compute** operation — the bridge from an exact symbolic result to a decimal
/// (`evalf(√2) ≈ 1.4142`). `None` for an unbound free variable (including `I`).
///
/// ```
/// use axeyum_cas::{CasExpr, evalf};
/// let two = evalf(&CasExpr::int(2).sqrt(), &[]).unwrap();
/// assert!((two - std::f64::consts::SQRT_2).abs() < 1e-12);
/// ```
#[must_use]
#[allow(clippy::cast_precision_loss)] // evalf is an approximation by definition
pub fn evalf(expr: &CasExpr, bindings: &[(&str, f64)]) -> Option<f64> {
    match expr {
        CasExpr::Const(value) => Some(value.numerator() as f64 / value.denominator() as f64),
        CasExpr::Var(name) => bindings
            .iter()
            .find(|(bound, _)| bound == name)
            .map(|&(_, value)| value)
            // The reserved constant `pi` defaults to π when not explicitly bound.
            .or_else(|| (name == "pi").then_some(core::f64::consts::PI)),
        CasExpr::Add(terms) => terms
            .iter()
            .try_fold(0.0, |acc, term| Some(acc + evalf(term, bindings)?)),
        CasExpr::Mul(factors) => factors
            .iter()
            .try_fold(1.0, |acc, factor| Some(acc * evalf(factor, bindings)?)),
        CasExpr::Neg(inner) => Some(-evalf(inner, bindings)?),
        CasExpr::Div(numerator, denominator) => {
            Some(evalf(numerator, bindings)? / evalf(denominator, bindings)?)
        }
        CasExpr::Pow(base, exponent) => {
            Some(evalf(base, bindings)?.powi(i32::try_from(*exponent).ok()?))
        }
        CasExpr::Unary(func, arg) => {
            let value = evalf(arg, bindings)?;
            Some(match func {
                UnaryFunc::Exp => value.exp(),
                UnaryFunc::Ln => value.ln(),
                UnaryFunc::Sin => value.sin(),
                UnaryFunc::Cos => value.cos(),
                UnaryFunc::Tan => value.tan(),
                UnaryFunc::Atan => value.atan(),
                UnaryFunc::Sqrt => value.sqrt(),
                UnaryFunc::Abs => value.abs(),
            })
        }
    }
}

/// The complex conjugate of an expression: replace the imaginary unit `I` with
/// `−I`. Purely structural.
#[must_use]
pub fn conjugate(expr: &CasExpr) -> CasExpr {
    expr.substitute("I", &CasExpr::Neg(Box::new(CasExpr::imaginary_unit())))
}

/// The real part of a polynomial expression in the imaginary unit `I` (and other
/// variables): the terms free of `I` after reducing `I² = −1`. `None` if `expr`
/// is not in the polynomial fragment or on overflow.
#[must_use]
pub fn real_part(expr: &CasExpr) -> Option<CasExpr> {
    let folded = normalize(expr)?.fold_imaginary()?;
    let mut re = MultiPoly::zero();
    for (mono, coeff) in &folded.terms {
        if !mono.powers.contains_key("I") {
            re.terms.insert(mono.clone(), *coeff);
        }
    }
    Some(re.to_expr())
}

/// The imaginary part of a polynomial expression in the imaginary unit `I`: the
/// coefficient of `I` after reducing `I² = −1`. `None` if `expr` is not in the
/// polynomial fragment or on overflow.
#[must_use]
pub fn imaginary_part(expr: &CasExpr) -> Option<CasExpr> {
    let folded = normalize(expr)?.fold_imaginary()?;
    let mut im = MultiPoly::zero();
    for (mono, coeff) in &folded.terms {
        if mono.powers.get("I") == Some(&1) {
            let mut powers = mono.powers.clone();
            powers.remove("I");
            im.terms.insert(Monomial { powers }, *coeff);
        }
    }
    Some(im.to_expr())
}

/// The **modulus** `|z| = √(Re(z)² + Im(z)²)` of a complex-polynomial expression in
/// the imaginary unit `I`, as an exact [`CasExpr`] with any surd simplified
/// (`|3+4i| = 5`, `|1+i| = √2`). `None` if `expr` is not in the polynomial fragment
/// or on overflow.
#[must_use]
pub fn modulus(expr: &CasExpr) -> Option<CasExpr> {
    let re = real_part(expr)?;
    let im = imaginary_part(expr)?;
    let square = expand(&(re.clone() * re + im.clone() * im))?;
    Some(simplify_radicals(&square.sqrt()))
}

/// The `n` complex **roots of unity** `e^{2πik/n} = cos(2πk/n) + i·sin(2πk/n)` for
/// `k = 0..n`, with the exact trigonometric values substituted where they are
/// tabulated (multiples of `π/12`). `None` for `n = 0`.
#[must_use]
pub fn roots_of_unity(n: u32) -> Option<Vec<CasExpr>> {
    if n == 0 {
        return None;
    }
    let pi = CasExpr::var("pi");
    let mut roots = Vec::with_capacity(n as usize);
    for k in 0..n {
        // angle = 2πk/n
        let angle = CasExpr::rat(2 * i128::from(k), i128::from(n)) * pi.clone();
        let real = evaluate_trig(&angle.clone().cos());
        let imaginary = evaluate_trig(&angle.sin());
        roots.push(real + imaginary * CasExpr::imaginary_unit());
    }
    Some(roots)
}

/// A point at which to take a [`limit`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LimitPoint {
    /// A finite rational point `x → a`.
    Finite(Rational),
    /// `x → +∞`.
    PosInfinity,
    /// `x → −∞`.
    NegInfinity,
}

/// The limit of a univariate rational-function `expr` as `var` approaches
/// `point`. Handles continuous evaluation, `0/0` indeterminate forms (by
/// cancelling common `(x−a)` factors), and limits at ±∞ (by comparing degrees).
/// Returns `None` for a pole (infinite limit), a non-rational/multivariate
/// expression, or on overflow. Exact by construction over the rational fragment.
#[must_use]
pub fn limit(expr: &CasExpr, var: &str, point: LimitPoint) -> Option<CasExpr> {
    if let Some(value) = limit_rational(expr, var, point) {
        return Some(value);
    }
    // At ±∞, an exponential dominates any rational factor: `R(x)·∏exp(cᵢx)^{±} → 0`
    // when the net exponential rate decays (e.g. `x²/eˣ → 0`).
    if matches!(point, LimitPoint::PosInfinity | LimitPoint::NegInfinity)
        && let Some(value) = limit_exp_dominated(expr, var, point)
    {
        return Some(value);
    }
    // Series fallback for transcendental `0/0` forms at a finite point
    // (`sin x/x → 1`, `(1−cos x)/x² → 1/2`, `(eˣ−1)/x → 1`).
    if let LimitPoint::Finite(a) = point {
        return limit_via_series(expr, var, a);
    }
    None
}

/// Limit at `±∞` of a product/quotient `R(x)·∏ exp(cᵢ·x)^{±}` where `R` is a
/// rational function of `var`: the **net exponential rate** decides. An
/// exponential beats any rational factor, so if the net rate is strictly negative
/// in the direction of the limit the value is `0`. A positive net rate diverges
/// (`None`); a zero net rate leaves it to the rational path. `None` if any factor
/// is outside `{rational function, exp(linear·var)}` or the expression has a
/// top-level sum (asymptotics of sums are not handled here).
fn limit_exp_dominated(expr: &CasExpr, var: &str, point: LimitPoint) -> Option<CasExpr> {
    let mut rate = Rational::zero();
    if !accumulate_exp_rate(expr, var, Rational::integer(1), &mut rate) {
        return None;
    }
    if rate.is_zero() {
        return None; // no net exponential — not this path
    }
    // Rate acts along +x; at −∞ the effective sign flips.
    let effective = match point {
        LimitPoint::NegInfinity => rate.checked_neg()?,
        _ => rate,
    };
    if effective.numerator() < 0 {
        Some(CasExpr::zero()) // decay beats the rational factor
    } else {
        None // growth → ±∞
    }
}

/// Walk a product/quotient, adding `sign·cᵢ` to `rate` for each `exp(cᵢ·var)`
/// factor and verifying every non-exponential factor is a rational function of
/// `var` (finite polynomial growth). Returns `false` if any factor is outside the
/// supported shape. `sign` carries the numerator/denominator and power multiplicity.
fn accumulate_exp_rate(expr: &CasExpr, var: &str, sign: Rational, rate: &mut Rational) -> bool {
    match expr {
        CasExpr::Mul(_) => flatten_mul(expr)
            .iter()
            .all(|f| accumulate_exp_rate(f, var, sign, rate)),
        CasExpr::Div(a, b) => {
            let Some(neg) = sign.checked_neg() else {
                return false;
            };
            accumulate_exp_rate(a, var, sign, rate) && accumulate_exp_rate(b, var, neg, rate)
        }
        CasExpr::Neg(inner) => accumulate_exp_rate(inner, var, sign, rate),
        CasExpr::Pow(base, exponent) => {
            // exp(c·x)^k contributes k·c; a rational-function base stays rational.
            if let CasExpr::Unary(UnaryFunc::Exp, _) = base.as_ref() {
                match sign.checked_mul(Rational::integer(i128::from(*exponent))) {
                    Some(scaled) => accumulate_exp_rate(base, var, scaled, rate),
                    None => false,
                }
            } else {
                is_rational_function(expr, var)
            }
        }
        CasExpr::Unary(UnaryFunc::Exp, arg) => {
            // Only exp(c·var) (linear, no constant that would just be a factor).
            match linear_var_coefficient(arg, var) {
                Some(coeff) => match sign.checked_mul(coeff) {
                    Some(contribution) => {
                        *rate = match rate.checked_add(contribution) {
                            Some(sum) => sum,
                            None => return false,
                        };
                        true
                    }
                    None => false,
                },
                None => false,
            }
        }
        // Anything else must be a plain rational function of `var` (bounded growth).
        _ => is_rational_function(expr, var),
    }
}

/// Whether `expr` is a univariate rational function of `var` (so it grows at most
/// polynomially, and an exponential factor dominates it at `±∞`).
fn is_rational_function(expr: &CasExpr, var: &str) -> bool {
    let Some(rf) = normalize_rational(expr) else {
        return false;
    };
    rf.num.to_univariate(var).is_some() && rf.den.to_univariate(var).is_some()
}

/// The limit over the **rational-function** fragment: continuous evaluation, `0/0`
/// by cancelling `(x−a)` factors, and `±∞` by degree comparison. `None` outside the
/// fragment or for an infinite limit.
fn limit_rational(expr: &CasExpr, var: &str, point: LimitPoint) -> Option<CasExpr> {
    let rf = normalize_rational(expr)?;
    let mut num = rf.num.to_univariate(var)?;
    let mut den = rf.den.to_univariate(var)?;
    match point {
        LimitPoint::Finite(a) => loop {
            let den_at = poly::eval_rat_poly(&den, a)?;
            if !den_at.is_zero() {
                let num_at = poly::eval_rat_poly(&num, a)?;
                return Some(CasExpr::Const(num_at.checked_div(den_at)?));
            }
            if poly::eval_rat_poly(&num, a)?.is_zero() {
                let factor = [a.checked_neg()?, Rational::integer(1)]; // x − a
                num = poly::rat_exact_div(&num, &factor)?;
                den = poly::rat_exact_div(&den, &factor)?;
            } else {
                return None; // pole — no finite limit
            }
        },
        LimitPoint::PosInfinity | LimitPoint::NegInfinity => {
            let deg_num = poly::rat_degree(&num)?;
            let deg_den = poly::rat_degree(&den)?;
            match deg_num.cmp(&deg_den) {
                core::cmp::Ordering::Less => Some(CasExpr::zero()),
                core::cmp::Ordering::Equal => {
                    Some(CasExpr::Const(num[deg_num].checked_div(den[deg_den])?))
                }
                core::cmp::Ordering::Greater => None,
            }
        }
    }
}

/// The coefficient `c` if `arg` is `c·var` (a rational multiple of a single
/// variable), `Some(0)` for the constant `0`; `None` otherwise.
fn linear_var_coefficient(arg: &CasExpr, var: &str) -> Option<Rational> {
    let poly = normalize(arg)?;
    if poly.terms.is_empty() {
        return Some(Rational::zero());
    }
    if poly.terms.len() != 1 {
        return None;
    }
    let (monomial, coeff) = poly.terms.iter().next()?;
    if monomial.powers.len() == 1 && monomial.powers.get(var) == Some(&1) {
        Some(*coeff)
    } else {
        None
    }
}

/// The Laplace transform `L{g}(s)` of a single elementary "base" `g` in `t`
/// (`1`, `e^{a·t}`, `sin(b·t)`, `cos(b·t)`), returned in the variable `s`. `None`
/// outside that table.
fn laplace_base(g: &CasExpr, t: &str, s: &str) -> Option<CasExpr> {
    let s_var = CasExpr::var(s);
    match g {
        CasExpr::Const(c) if *c == Rational::integer(1) => Some(CasExpr::int(1) / s_var), // L{1}=1/s
        CasExpr::Unary(UnaryFunc::Exp, arg) => {
            let a = linear_var_coefficient(arg, t)?; // e^{a·t} → 1/(s−a)
            Some(CasExpr::int(1) / (s_var - CasExpr::Const(a)))
        }
        CasExpr::Unary(UnaryFunc::Sin, arg) => {
            let b = linear_var_coefficient(arg, t)?; // sin(b·t) → b/(s²+b²)
            Some(CasExpr::Const(b) / (s_var.pow(2) + CasExpr::Const(b.checked_mul(b)?)))
        }
        CasExpr::Unary(UnaryFunc::Cos, arg) => {
            let b = linear_var_coefficient(arg, t)?; // cos(b·t) → s/(s²+b²)
            Some(s_var.clone() / (s_var.pow(2) + CasExpr::Const(b.checked_mul(b)?)))
        }
        _ => None,
    }
}

/// The Laplace transform `L{f}(s) = ∫₀^∞ f(t)·e^{−st} dt` of an elementary function
/// `f` in `t`, returned in the variable `s`. Handles linear combinations of
/// `tᵏ·e^{a·t}`, `tᵏ·sin(b·t)`, `tᵏ·cos(b·t)`, and polynomials (via `L{tᵏ·g} =
/// (−1)ᵏ dᵏ/dsᵏ L{g}` and the `1, e^{at}, sin, cos` table). `None` outside that
/// fragment or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, laplace_transform, equal, ZeroTest};
/// let t = CasExpr::var("t");
/// // L{t} = 1/s².
/// let f = laplace_transform(&t, "t", "s").unwrap();
/// let expected = CasExpr::int(1) / CasExpr::var("s").pow(2);
/// assert!(matches!(equal(&f, &expected), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn laplace_transform(f: &CasExpr, t: &str, s: &str) -> Option<CasExpr> {
    // Linearity: transform each additive term and sum.
    if let CasExpr::Add(terms) = f {
        let mut total = CasExpr::zero();
        for term in terms {
            total = total + laplace_transform(term, t, s)?;
        }
        return Some(expand(&total).unwrap_or(total));
    }

    // Decompose the term into constant `c`, power `t^power`, and a transcendental
    // base `g ∈ {1, e^{at}, sin, cos}`.
    let factors: Vec<CasExpr> = match f {
        CasExpr::Mul(factors) => factors.clone(),
        other => vec![other.clone()],
    };
    let mut coefficient = Rational::integer(1);
    let mut power = 0u32;
    let mut base = CasExpr::int(1);
    let mut base_seen = false;
    for factor in &factors {
        match factor {
            CasExpr::Const(c) => coefficient = coefficient.checked_mul(*c)?,
            CasExpr::Var(name) if name == t => power = power.checked_add(1)?,
            CasExpr::Pow(inner, exp) if matches!(&**inner, CasExpr::Var(n) if n == t) => {
                power = power.checked_add(*exp)?;
            }
            CasExpr::Unary(UnaryFunc::Exp | UnaryFunc::Sin | UnaryFunc::Cos, _) => {
                if base_seen {
                    return None; // more than one transcendental factor — unsupported
                }
                base = factor.clone();
                base_seen = true;
            }
            _ => return None, // outside the supported fragment
        }
    }

    // L{g}(s), then L{t^power · g} = (−1)^power d^power/ds^power L{g}.
    let mut transform = laplace_base(&base, t, s)?;
    transform = transform.differentiate_n(s, power as usize);
    let sign = if power.is_multiple_of(2) {
        coefficient
    } else {
        coefficient.checked_neg()?
    };
    let result = CasExpr::Const(sign) * transform;
    Some(simplify(&result))
}

/// The **Laurent series** of a univariate rational function `f` about `var = 0`, up
/// to and including degree `order` (which may include a finite principal part of
/// negative powers when `f` has a pole at `0`). Returns the truncated Laurent
/// polynomial as a [`CasExpr`] (e.g. `1/(x(1−x)) = x⁻¹ + 1 + x + x² + …`); the
/// coefficient of `x⁻¹` is the residue at `0`. `None` if `f` is not a univariate
/// rational function in `var`, is identically zero, or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, laurent_series, equal, ZeroTest};
/// let x = CasExpr::var("x");
/// // 1/(x(1−x)) = 1/x + 1 + x + x² (to order 2).
/// let f = CasExpr::int(1) / (x.clone() * (CasExpr::int(1) - x.clone()));
/// let laurent = laurent_series(&f, "x", 2).unwrap();
/// let expected = CasExpr::int(1) / x.clone() + CasExpr::int(1) + x.clone() + x.pow(2);
/// assert!(matches!(equal(&laurent, &expected), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn laurent_series(f: &CasExpr, var: &str, order: usize) -> Option<CasExpr> {
    let rf = normalize_rational(f)?;
    let num = rf.num.to_univariate(var)?;
    let den = rf.den.to_univariate(var)?;
    // Valuation (order of the lowest nonzero term) of numerator and denominator.
    let num_val = num.iter().position(|c| !c.is_zero())?; // None ⇒ f ≡ 0
    let den_val = den.iter().position(|c| !c.is_zero())?;
    // Strip the `x^val` factors so the reduced parts are nonzero at 0.
    let num_reduced = num[num_val..].to_vec();
    let den_reduced = den[den_val..].to_vec();
    let shift = isize::try_from(num_val).ok()? - isize::try_from(den_val).ok()?;

    // The reduced quotient is analytic at 0 (denominator constant term ≠ 0).
    let reduced = MultiPoly::from_univariate(var, &num_reduced).to_expr()
        / MultiPoly::from_univariate(var, &den_reduced).to_expr();
    let taylor_order = usize::try_from((isize::try_from(order).ok()? - shift).max(0)).ok()?;
    let taylor = series(&reduced, var, taylor_order)?;

    // Multiply by `x^shift` (a positive power, or a division for a pole).
    let x = CasExpr::var(var);
    let result = if shift >= 0 {
        let power = u32::try_from(shift).ok()?;
        taylor * x.pow(power)
    } else {
        let power = u32::try_from(-shift).ok()?;
        taylor / x.pow(power)
    };
    Some(result)
}

/// The **inverse Laplace transform** `L⁻¹{F}(t)` of a proper rational function `F(s)`
/// with **simple real rational poles**: `F = Σ Rᵢ/(s−aᵢ)` gives `Σ Rᵢ·e^{aᵢt}`,
/// where each residue `Rᵢ = Res_{s=aᵢ} F`. **Certified** by the round trip
/// `L{result} = F` (via [`laplace_transform`] and the zero-test). Returns `None` for
/// an improper `F`, or poles that are repeated, irrational, or complex (future work).
///
/// ```
/// use axeyum_cas::{CasExpr, inverse_laplace, equal, ZeroTest};
/// let s = CasExpr::var("s");
/// // L⁻¹{1/(s−2)} = e^{2t}.
/// let g = inverse_laplace(&(CasExpr::int(1) / (s - CasExpr::int(2))), "s", "t").unwrap();
/// let expected = (CasExpr::int(2) * CasExpr::var("t")).exp();
/// assert!(matches!(equal(&g, &expected), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn inverse_laplace(f: &CasExpr, s: &str, t: &str) -> Option<CasExpr> {
    let rf = normalize_rational(f)?;
    let num = rf.num.to_univariate(s)?;
    let den = rf.den.to_univariate(s)?;
    let deg_num = poly::rat_degree(&num).unwrap_or(0);
    let deg_den = poly::rat_degree(&den)?;
    if deg_num >= deg_den {
        return None; // improper — the polynomial (δ-function) part is unsupported
    }
    // Require `deg_den` distinct rational poles (⇒ all simple).
    let mut poles: Vec<Rational> = Vec::new();
    for root in ratint::rational_roots(&den)? {
        if !poles.contains(&root) {
            poles.push(root);
        }
    }
    if poles.len() != deg_den {
        return None;
    }
    let mut result = CasExpr::zero();
    for pole in poles {
        let res = residue(f, s, pole)?;
        result = result + res * (CasExpr::Const(pole) * CasExpr::var(t)).exp();
    }
    // Round-trip certificate: L{result} = F.
    match equal(&laplace_transform(&result, t, s)?, f) {
        ZeroTest::Certified { equal: true, .. } => Some(result),
        _ => None,
    }
}

/// The **(unilateral) Z-transform** `X(z) = Σ_{k≥0} x[k]·z^{−k}` of a discrete
/// signal `x[n]`, over the geometric fragment: linear combinations of the unit
/// step (`x[n]=1 → z/(z−1)`) and geometric sequences (`x[n]=aⁿ → z/(z−a)`, with
/// `aⁿ` written as `exp(n·ln a)` for rational `a > 0`, cf. [`geometric_power`]).
/// Returned as a rational function of `z`. `None` outside that fragment.
///
/// Discrete counterpart of [`laplace_transform`]; pairs with [`inverse_z_transform`],
/// which is round-trip-certified against this function.
#[must_use]
pub fn z_transform(signal: &CasExpr, n: &str, z: &str) -> Option<CasExpr> {
    let terms = match signal {
        CasExpr::Add(terms) => terms.clone(),
        other => vec![other.clone()],
    };
    let z_var = CasExpr::var(z);
    let mut total = CasExpr::zero();
    for term in &terms {
        let (coeff, base) = match_geometric_signal(term, n)?; // c·aⁿ (a = 1 for a step)
        // Z{c·aⁿ} = c·z/(z − a).
        let contribution =
            CasExpr::Const(coeff) * z_var.clone() / (z_var.clone() - CasExpr::Const(base));
        total = total + contribution;
    }
    cancel(&total)
}

/// Match a discrete term `c·aⁿ` (with `aⁿ` written as `exp(n·ln a)`, `a > 0`) or a
/// bare constant `c` (`a = 1`, the unit step), returning `(c, a)`. `None` otherwise.
fn match_geometric_signal(term: &CasExpr, n: &str) -> Option<(Rational, Rational)> {
    let mut coeff = Rational::integer(1);
    let mut base: Option<Rational> = None;
    for factor in flatten_mul(term) {
        match factor {
            CasExpr::Const(c) => coeff = coeff.checked_mul(c)?,
            CasExpr::Unary(UnaryFunc::Exp, arg) if base.is_none() => {
                base = Some(geometric_base(&arg, n)?);
            }
            _ => return None, // n-dependent non-geometric factor, or a second exp
        }
    }
    Some((coeff, base.unwrap_or_else(|| Rational::integer(1))))
}

/// The base `a` if `arg` is `n·ln(a)` for a **positive rational** `a` (so
/// `exp(arg) = aⁿ`); `None` otherwise.
fn geometric_base(arg: &CasExpr, n: &str) -> Option<Rational> {
    let mut has_n = false;
    let mut base: Option<Rational> = None;
    for factor in flatten_mul(arg) {
        match factor {
            CasExpr::Var(v) if v == n => has_n = true,
            CasExpr::Unary(UnaryFunc::Ln, inner) if base.is_none() => {
                let CasExpr::Const(a) = *inner else {
                    return None;
                };
                if a.numerator() <= 0 {
                    return None; // ln real only for a > 0
                }
                base = Some(a);
            }
            CasExpr::Const(c) if c == Rational::integer(1) => {}
            _ => return None,
        }
    }
    if has_n { base } else { None }
}

/// The **inverse Z-transform** `x[n] = Z⁻¹{X}` of a proper rational `X(z)` with
/// **simple rational poles**: from the partial fraction `X(z)/z = Σ Rⱼ/(z − aⱼ)`,
/// `x[n] = Σ Rⱼ·aⱼⁿ` (with `aⁿ = exp(n·ln a)`). **Certified** by the round trip
/// `Z{x[n]} = X(z)` (via [`z_transform`] and the zero-test). Returns `None` for an
/// improper `X`, repeated/irrational/non-positive poles, or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, inverse_z_transform, z_transform, equal, ZeroTest};
/// let z = CasExpr::var("z");
/// // Z⁻¹{z/(z−2)} = 2ⁿ; the round trip recovers z/(z−2).
/// let x = inverse_z_transform(&(z.clone() / (z.clone() - CasExpr::int(2))), "z", "n").unwrap();
/// let back = z_transform(&x, "n", "z").unwrap();
/// assert!(matches!(equal(&back, &(z.clone() / (z - CasExpr::int(2)))), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn inverse_z_transform(transformed: &CasExpr, z: &str, n: &str) -> Option<CasExpr> {
    // Work with X(z)/z so simple poles a give residues R with x[n] = Σ R·aⁿ.
    let z_var = CasExpr::var(z);
    let over_z = CasExpr::Div(Box::new(transformed.clone()), Box::new(z_var));
    // Reduce to lowest terms so the extra `z` in the denominator cancels rather
    // than leaving a spurious pole at `z = 0` (e.g. `z/(z²−2z)` → `1/(z−2)`).
    let rf = normalize_rational(&over_z)?.reduced()?;
    let num = rf.num.to_univariate(z)?;
    let den = rf.den.to_univariate(z)?;
    let deg_num = poly::rat_degree(&num).unwrap_or(0);
    let deg_den = poly::rat_degree(&den)?;
    if deg_num >= deg_den {
        return None; // X(z)/z must be strictly proper (X proper)
    }
    let mut poles: Vec<Rational> = Vec::new();
    for root in ratint::rational_roots(&den)? {
        if !poles.contains(&root) {
            poles.push(root);
        }
    }
    if poles.len() != deg_den {
        return None; // need `deg_den` distinct rational poles (⇒ all simple)
    }
    let mut terms: Vec<CasExpr> = Vec::new();
    for pole in poles {
        if pole.numerator() <= 0 {
            return None; // aⁿ = exp(n·ln a) needs a > 0
        }
        let res = residue(&over_z, z, pole)?;
        terms.push(res * geometric_power(pole, n));
    }
    // Build a *flat* sum (a nested `zero()+a+b` would defeat z_transform's Add match).
    let result = fold_trivial(&match terms.len() {
        0 => CasExpr::zero(),
        1 => terms.into_iter().next()?,
        _ => CasExpr::Add(terms),
    });
    // Round-trip certificate: Z{result} = X(z).
    match equal(&z_transform(&result, n, z)?, transformed) {
        ZeroTest::Certified { equal: true, .. } => Some(result),
        _ => None,
    }
}

/// The Maclaurin coefficients of `f` about `0` to `order`, or `None` outside the
/// series-expandable fragment.
fn series_coefficients(f: &CasExpr, var: &str, order: usize) -> Option<Vec<Rational>> {
    normalize(&series(f, var, order)?)?.to_univariate(var)
}

/// The product of two coefficient vectors, truncated at degree `order`.
fn truncated_series_mul(a: &[Rational], b: &[Rational], order: usize) -> Option<Vec<Rational>> {
    let mut result = vec![Rational::zero(); order + 1];
    for (i, &ai) in a.iter().enumerate() {
        if i > order || ai.is_zero() {
            continue;
        }
        for (j, &bj) in b.iter().enumerate() {
            if i + j > order {
                break;
            }
            result[i + j] = result[i + j].checked_add(ai.checked_mul(bj)?)?;
        }
    }
    Some(result)
}

/// Compose a polynomial `poly` (coefficient vector) with a series `g`, truncated at
/// degree `order` — the series of `poly(g(x))` — by Horner's method.
fn compose_poly_with_series(
    poly: &[Rational],
    g: &[Rational],
    order: usize,
) -> Option<Vec<Rational>> {
    let mut acc = vec![Rational::zero(); order + 1];
    for &coeff in poly.iter().rev() {
        acc = truncated_series_mul(&acc, g, order)?;
        acc[0] = acc[0].checked_add(coeff)?;
    }
    Some(acc)
}

/// **Series reversion** — the compositional inverse of a power series. Given `f` with
/// `f(0) = 0` and `f'(0) ≠ 0`, return the series `g` (to degree `order`) with
/// `f(g(x)) = x`. For example the reversion of the `sin` series is the `arcsin`
/// series, and of `eˣ − 1` is `ln(1+x)`. `None` if `f(0) ≠ 0`, `f'(0) = 0`, `f` is
/// outside the series fragment, or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, series_reversion, equal, ZeroTest};
/// let x = CasExpr::var("x");
/// // reversion(2x) = x/2 (since 2·(x/2) = x).
/// let g = series_reversion(&(CasExpr::int(2) * x.clone()), "x", 3).unwrap();
/// assert!(matches!(equal(&g, &(x / CasExpr::int(2))), ZeroTest::Certified { equal: true, .. }));
/// ```
#[must_use]
pub fn series_reversion(f: &CasExpr, var: &str, order: usize) -> Option<CasExpr> {
    let a = series_coefficients(f, var, order)?;
    if a.first().is_some_and(|c| !c.is_zero()) {
        return None; // f(0) ≠ 0
    }
    let a1 = *a.get(1)?;
    if a1.is_zero() {
        return None; // f'(0) = 0 — not invertible
    }
    let mut g = vec![Rational::zero(); order + 1];
    if order >= 1 {
        g[1] = Rational::integer(1).checked_div(a1)?;
    }
    // Solve b_n order by order: [xⁿ] f(g) with b_n = 0 gives E, then b_n = −E/a₁.
    for n in 2..=order {
        let fg = compose_poly_with_series(&a, &g, n)?;
        g[n] = fg[n].checked_neg()?.checked_div(a1)?;
    }
    Some(MultiPoly::from_univariate(var, &g).to_expr())
}

/// The (valuation, leading coefficient) of a coefficient vector — the lowest degree
/// with a nonzero coefficient. `None` if all coefficients (to the computed order)
/// are zero.
fn leading_term(coeffs: &[Rational]) -> Option<(usize, Rational)> {
    coeffs
        .iter()
        .enumerate()
        .find(|(_, c)| !c.is_zero())
        .map(|(i, c)| (i, *c))
}

/// The limit of `expr` as `var → a` via Maclaurin series (after shifting to the
/// origin). For an analytic point the value is the series' constant term; for a
/// `0/0` quotient it is the ratio of leading terms of the numerator and denominator
/// expansions. `None` for an infinite limit or outside the series fragment.
fn limit_via_series(expr: &CasExpr, var: &str, a: Rational) -> Option<CasExpr> {
    const ORDER: usize = 12;
    let shifted = expr.substitute(var, &(CasExpr::var(var) + CasExpr::Const(a)));

    if let CasExpr::Div(numerator, denominator) = &shifted {
        let num_coeffs = series_coefficients(numerator, var, ORDER)?;
        let den_coeffs = series_coefficients(denominator, var, ORDER)?;
        let Some((den_val, den_lead)) = leading_term(&den_coeffs) else {
            return None; // denominator ≡ 0 to this order — undefined
        };
        let Some((num_val, num_lead)) = leading_term(&num_coeffs) else {
            return Some(CasExpr::zero()); // numerator ≡ 0 (and denominator ≢ 0)
        };
        return match num_val.cmp(&den_val) {
            core::cmp::Ordering::Greater => Some(CasExpr::zero()),
            core::cmp::Ordering::Equal => Some(CasExpr::Const(num_lead.checked_div(den_lead)?)),
            core::cmp::Ordering::Less => None, // pole — infinite limit
        };
    }

    // Analytic (non-quotient): the constant term of the series is the value.
    let expansion = series(&shifted, var, ORDER)?;
    Some(simplify(&expansion.substitute(var, &CasExpr::zero())))
}

/// Expand an expression to canonical form and return it as a [`CasExpr`].
///
/// For the polynomial fragment this is the expanded sum-of-monomials form; for a
/// rational function it is `num/den` with each part expanded (not yet reduced to
/// lowest terms — GCD reduction is a later phase). The result is value-equal to
/// the input by construction ([`equal`] certifies the round-trip). Returns `None`
/// on overflow or division by an identically-zero denominator.
#[must_use]
pub fn expand(expr: &CasExpr) -> Option<CasExpr> {
    let rf = normalize_rational(expr)?;
    let num = rf.num.to_expr();
    let result = if rf.den == MultiPoly::constant(Rational::integer(1)) {
        num
    } else {
        CasExpr::Div(Box::new(num), Box::new(rf.den.to_expr()))
    };
    Some(deatomize_from(&result, expr))
}

/// Reduce an expression to lowest terms (the `cancel` transform): a canonical reduced
/// rational function, value-equal to the input. Univariate functions are fully
/// reduced via the exact polynomial GCD; multivariate functions are expanded but
/// not yet GCD-reduced (a later phase). Returns `None` on overflow or division by
/// an identically-zero denominator.
#[must_use]
pub fn cancel(expr: &CasExpr) -> Option<CasExpr> {
    let rf = normalize_rational(expr)?.reduced()?;
    let num = rf.num.to_expr();
    let result = if rf.den == MultiPoly::constant(Rational::integer(1)) {
        num
    } else {
        CasExpr::Div(Box::new(num), Box::new(rf.den.to_expr()))
    };
    Some(deatomize_from(&result, expr))
}

/// Certify that `d/dvar (expr) = claimed`, by differentiating and deciding
/// equality against `claimed`. A [`ZeroTest::Certified`] with `equal == true` is
/// a proof (over the polynomial fragment) that the claimed derivative is correct.
#[must_use]
pub fn prove_derivative(expr: &CasExpr, var: &str, claimed: &CasExpr) -> ZeroTest {
    equal(&expr.differentiate(var), claimed)
}

/// A computed antiderivative bundled with its **correctness certificate** — the
/// heart of the proof-carrying thesis: axeyum = (compute, like a CAS) + (certify,
/// like a proof/decision engine). The engine *finds* the antiderivative and then *proves* it
/// by differentiating back and zero-testing against the integrand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedIntegral {
    /// A computed antiderivative `F` with `dF/dvar = integrand` (up to `+C`).
    pub antiderivative: CasExpr,
    /// The certificate: `equal(d(antiderivative)/dvar, integrand)`. When this is
    /// [`ZeroTest::Certified`] with `equal == true`, the antiderivative is
    /// *proven* correct — the integration answer carries its own proof.
    pub certificate: ZeroTest,
}

impl CertifiedIntegral {
    /// Whether the antiderivative is certified correct (the certificate decided
    /// the differentiate-and-check obligation as an exact equality).
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self.certificate, ZeroTest::Certified { equal: true, .. })
    }
}

/// Indefinite integral over the polynomial fragment, **returned with a proof**.
///
/// Computes an antiderivative (dropping `+C`) and immediately certifies it by
/// differentiating the result and zero-testing against the integrand
/// ([`CertifiedIntegral`]). Over the polynomial fragment the answer is always
/// certifiable; a returned integral therefore carries a re-checkable proof of its
/// own correctness. Returns `None` for non-polynomial input (rational-function
/// integration is a later phase) or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, integrate};
/// let x = CasExpr::var("x");
/// // ∫ (3x² + 2x) dx = x³ + x², and the answer proves itself.
/// let integrand = CasExpr::int(3) * x.clone().pow(2) + CasExpr::int(2) * x;
/// let result = integrate(&integrand, "x").unwrap();
/// assert!(result.is_certified());
/// ```
#[must_use]
pub fn integrate(expr: &CasExpr, var: &str) -> Option<CertifiedIntegral> {
    // Polynomial fast path — always certifiable.
    if let Some(p) = normalize(expr) {
        let antiderivative = p.integrate_in(var)?.to_expr();
        let certificate = prove_derivative(&antiderivative, var, expr);
        return Some(CertifiedIntegral {
            antiderivative,
            certificate,
        });
    }
    // Try each finder (univariate rational via Horowitz; elementary-function
    // table). Every candidate is certified by differentiate-and-check, so a
    // finder shortfall or out-of-fragment case declines to `None` rather than
    // returning a wrong answer.
    for antiderivative in [
        integrate_rational(expr, var),
        integrate_elementary(expr, var),
        integrate_poly_times_exp(expr, var),
        integrate_poly_times_log(expr, var),
        integrate_poly_times_sinusoid(expr, var),
        integrate_exp_times_sinusoid(expr, var),
        integrate_trig_monomial(expr, var),
        integrate_trig_square(expr, var),
    ]
    .into_iter()
    .flatten()
    {
        let certificate = prove_derivative(&antiderivative, var, expr);
        if matches!(certificate, ZeroTest::Certified { equal: true, .. }) {
            return Some(CertifiedIntegral {
                antiderivative,
                certificate,
            });
        }
    }
    None
}

/// A definite integral `∫ₐᵇ f dx` evaluated by the fundamental theorem of
/// calculus from a **certified** antiderivative.
#[derive(Debug, Clone)]
pub struct DefiniteIntegral {
    /// The evaluated value `F(b) − F(a)`, simplified.
    pub value: CasExpr,
    /// The antiderivative `F` used (with `dF/dvar = integrand`).
    pub antiderivative: CasExpr,
    /// The certificate carried over from the indefinite integral. When this is
    /// [`ZeroTest::Certified`] with `equal == true`, the antiderivative is proven,
    /// so by the fundamental theorem of calculus the value is proven too.
    pub certificate: ZeroTest,
}

impl DefiniteIntegral {
    /// Whether the underlying antiderivative was certified (and hence, by the
    /// fundamental theorem of calculus, this definite value).
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self.certificate, ZeroTest::Certified { equal: true, .. })
    }
}

/// The definite integral of `expr` in `var` from `lower` to `upper`, via the
/// fundamental theorem of calculus: find a certified antiderivative `F` with
/// [`integrate`], then return `F(upper) − F(lower)`.
///
/// The bounds are arbitrary [`CasExpr`] values (numeric or symbolic). The result
/// inherits the antiderivative's certificate: over the polynomial / rational
/// fragment the value is exact and proven; when `F` contains transcendental terms
/// (`ln`, `atan`) the value is returned symbolically with the same backing. Any
/// bound landing on a singularity of `F` (e.g. a pole) is *not* detected here — the
/// caller is responsible for continuity of `f` on `[lower, upper]`, exactly as the
/// theorem requires. Returns `None` when no antiderivative is found or on overflow.
///
/// ```
/// use axeyum_cas::{CasExpr, definite_integrate};
/// let x = CasExpr::var("x");
/// // ∫₀¹ 3x² dx = 1.
/// let result = definite_integrate(
///     &(CasExpr::int(3) * x.pow(2)),
///     "x",
///     &CasExpr::int(0),
///     &CasExpr::int(1),
/// )
/// .unwrap();
/// assert!(result.is_certified());
/// assert_eq!(result.value, CasExpr::int(1));
/// ```
#[must_use]
pub fn definite_integrate(
    expr: &CasExpr,
    var: &str,
    lower: &CasExpr,
    upper: &CasExpr,
) -> Option<DefiniteIntegral> {
    let indefinite = integrate(expr, var)?;
    let at_upper = indefinite.antiderivative.substitute(var, upper);
    let at_lower = indefinite.antiderivative.substitute(var, lower);
    // Fold exact elementary constants (sin 0 = 0, cos π = −1, ln 1 = 0, …) before
    // the structural simplify, so numeric bounds collapse to closed values.
    let value = simplify(&fold_elementary_constants(&(at_upper - at_lower)));
    Some(DefiniteIntegral {
        value,
        antiderivative: indefinite.antiderivative,
        certificate: indefinite.certificate,
    })
}

/// An **improper integral** with one or both bounds at `±∞` (or a finite bound),
/// evaluated as `lim_{var→upper} F − lim_{var→lower} F` for a **certified**
/// antiderivative `F` (see [`integrate`]). A finite bound is substituted; an
/// infinite bound routes through [`limit`] (so exponential-decay integrands
/// converge — `∫₀^∞ e^{−x} = 1`, `∫₀^∞ x·e^{−x} = 1`). Returns `None` when no
/// antiderivative is found or a boundary limit **diverges** (the integral does not
/// converge) — an honest decline, never a wrong value. The caller is responsible
/// for continuity of the integrand on the (open) interval, as for [`definite_integrate`].
///
/// ```
/// use axeyum_cas::{CasExpr, LimitPoint, improper_integrate};
/// use axeyum_ir::Rational;
/// // ∫₀^∞ e^{−x} dx = 1.
/// let f = (CasExpr::int(-1) * CasExpr::var("x")).exp();
/// let r = improper_integrate(&f, "x", LimitPoint::Finite(Rational::zero()), LimitPoint::PosInfinity).unwrap();
/// assert_eq!(r.value, CasExpr::int(1));
/// ```
#[must_use]
pub fn improper_integrate(
    expr: &CasExpr,
    var: &str,
    lower: LimitPoint,
    upper: LimitPoint,
) -> Option<DefiniteIntegral> {
    let indefinite = integrate(expr, var)?;
    let antiderivative = &indefinite.antiderivative;
    let boundary = |point: LimitPoint| -> Option<CasExpr> {
        match point {
            LimitPoint::Finite(a) => Some(simplify(&fold_elementary_constants(
                &antiderivative.substitute(var, &CasExpr::Const(a)),
            ))),
            infinity => limit(antiderivative, var, infinity),
        }
    };
    let at_upper = boundary(upper)?;
    let at_lower = boundary(lower)?;
    let value = simplify(&fold_elementary_constants(&(at_upper - at_lower)));
    Some(DefiniteIntegral {
        value,
        antiderivative: indefinite.antiderivative,
        certificate: indefinite.certificate,
    })
}

/// Integrate `k·sin²(a·x+b)` or `k·cos²(a·x+b)` (linear argument): the
/// antiderivative is `k·(x/2 ∓ (1/2a)·sin(u)·cos(u))`, certifiable via the
/// Pythagorean identity in the zero-test. `None` outside this shape.
fn integrate_trig_square(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let (coeff, inner) = match expr {
        CasExpr::Pow(_, _) => (Rational::integer(1), expr),
        CasExpr::Neg(a) => (Rational::integer(-1), a.as_ref()),
        CasExpr::Mul(factors) if factors.len() == 2 => match (&factors[0], &factors[1]) {
            (CasExpr::Const(k), p @ CasExpr::Pow(_, _))
            | (p @ CasExpr::Pow(_, _), CasExpr::Const(k)) => (*k, p),
            _ => return None,
        },
        _ => return None,
    };
    let CasExpr::Pow(base, 2) = inner else {
        return None;
    };
    let CasExpr::Unary(func, arg) = base.as_ref() else {
        return None;
    };
    if !matches!(func, UnaryFunc::Sin | UnaryFunc::Cos) {
        return None;
    }
    let arg_poly = normalize(arg)?.to_univariate(var)?;
    if poly::rat_degree(&arg_poly)? != 1 {
        return None;
    }
    let a = arg_poly[1];
    let arg_expr = MultiPoly::from_univariate(var, &arg_poly).to_expr();
    let inv_2a = Rational::integer(1).checked_div(Rational::integer(2).checked_mul(a)?)?;
    let product = CasExpr::Mul(vec![arg_expr.clone().sin(), arg_expr.cos()]);
    // sin²: −(1/2a)·sin·cos ; cos²: +(1/2a)·sin·cos.
    let cross_coeff = if *func == UnaryFunc::Sin {
        inv_2a.checked_neg()?
    } else {
        inv_2a
    };
    let antiderivative =
        scaled_term(Rational::new(1, 2), CasExpr::var(var)) + scaled_term(cross_coeff, product);
    Some(scaled_term(coeff, antiderivative))
}

/// Integrate `p(x)·e^(a·x+b)` for a polynomial `p` and a linear exponent:
/// `∫ p·e^(ax+b) = Q·e^(ax+b)` where `Q` solves `Q′ + a·Q = p` (one exact linear
/// system). Covers `∫ x·eˣ = (x−1)eˣ`, `∫ x²·eˣ = (x²−2x+2)eˣ`, etc. `None`
/// outside this shape; certified downstream by differentiate-and-check.
/// `∫ p(x)·ln(x) dx` for a polynomial `p` — `Σ cₖ·[x^{k+1}/(k+1)·ln x −
/// x^{k+1}/(k+1)²]` by parts. Returns `None` unless `expr` is `p(var)·ln(var)`.
fn integrate_poly_times_log(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let CasExpr::Mul(factors) = expr else {
        return None;
    };
    let mut log_found = false;
    let mut rest: Vec<CasExpr> = Vec::new();
    for factor in factors {
        if let CasExpr::Unary(UnaryFunc::Ln, arg) = factor
            && !log_found
            && matches!(&**arg, CasExpr::Var(v) if v == var)
        {
            log_found = true;
            continue;
        }
        rest.push(factor.clone());
    }
    if !log_found {
        return None;
    }
    let p = normalize(&CasExpr::Mul(rest))?.to_univariate(var)?;
    let ln_x = CasExpr::var(var).ln();
    let mut result = CasExpr::zero();
    for (k, &c) in p.iter().enumerate() {
        if c.is_zero() {
            continue;
        }
        let kp1 = Rational::integer(i128::try_from(k + 1).ok()?);
        let base_coeff = c.checked_div(kp1)?; // cₖ/(k+1)
        let power = u32::try_from(k + 1).ok()?;
        let x_power = CasExpr::var(var).pow(power);
        let with_log = CasExpr::Const(base_coeff) * x_power.clone() * ln_x.clone();
        let correction = CasExpr::Const(base_coeff.checked_div(kp1)?) * x_power;
        result = result + with_log - correction;
    }
    Some(result)
}

fn integrate_poly_times_exp(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let CasExpr::Mul(factors) = expr else {
        return None;
    };
    let mut exp_arg: Option<CasExpr> = None;
    let mut rest: Vec<CasExpr> = Vec::new();
    for factor in factors {
        if let CasExpr::Unary(UnaryFunc::Exp, arg) = factor {
            if exp_arg.is_some() {
                return None; // more than one exponential factor
            }
            exp_arg = Some((**arg).clone());
        } else {
            rest.push(factor.clone());
        }
    }
    let arg_poly = normalize(&exp_arg?)?.to_univariate(var)?;
    if poly::rat_degree(&arg_poly)? != 1 {
        return None;
    }
    let a = arg_poly[1];
    let p = normalize(&CasExpr::Mul(rest))?.to_univariate(var)?;
    let degree = poly::rat_degree(&p)?;
    let size = degree + 1;
    // Column j: contribution of qⱼ to (Q′ + a·Q) = a at xʲ and j at xʲ⁻¹.
    let mut cols: Vec<Vec<Rational>> = Vec::with_capacity(size);
    for j in 0..size {
        let mut col = vec![Rational::zero(); size];
        col[j] = a;
        if j >= 1 {
            col[j - 1] = Rational::integer(i128::try_from(j).ok()?);
        }
        cols.push(col);
    }
    let mut rhs = p;
    rhs.resize(size, Rational::zero());
    let q_coeffs = ratint::solve_linear(&cols, &rhs)?;
    let q_expr = MultiPoly::from_univariate(var, &q_coeffs).to_expr();
    let arg_expr = MultiPoly::from_univariate(var, &arg_poly).to_expr();
    Some(CasExpr::Mul(vec![q_expr, arg_expr.exp()]))
}

/// Integrate `p(x)·sin(a·x+b)` or `p(x)·cos(a·x+b)` for a polynomial `p` and
/// linear argument: the antiderivative has the form `A(x)·cos + B(x)·sin`, whose
/// polynomial coefficients solve a coupled linear system (`A′+aB` and `B′−aA`
/// match the sin/cos parts). Covers `∫ x·sin x = sin x − x·cos x`,
/// `∫ x²·cos x = x²·sin x + 2x·cos x − 2·sin x`, etc. `None` outside this shape;
/// certified downstream.
fn integrate_poly_times_sinusoid(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let CasExpr::Mul(factors) = expr else {
        return None;
    };
    let mut trig: Option<(UnaryFunc, CasExpr)> = None;
    let mut rest: Vec<CasExpr> = Vec::new();
    for factor in factors {
        match factor {
            CasExpr::Unary(f @ (UnaryFunc::Sin | UnaryFunc::Cos), arg) if trig.is_none() => {
                trig = Some((*f, (**arg).clone()));
            }
            CasExpr::Unary(UnaryFunc::Sin | UnaryFunc::Cos, _) => return None, // two trig factors
            other => rest.push(other.clone()),
        }
    }
    let (which, arg) = trig?;
    let arg_poly = normalize(&arg)?.to_univariate(var)?;
    if poly::rat_degree(&arg_poly)? != 1 {
        return None;
    }
    let a = arg_poly[1];
    let p = normalize(&CasExpr::Mul(rest))?.to_univariate(var)?;
    let degree = poly::rat_degree(&p)?;
    let block = degree + 1; // coefficients per polynomial A, B
    let size = 2 * block;
    // Unknowns [A₀..A_d, B₀..B_d]; equations [(A′+aB) x⁰..x^d ; (B′−aA) x⁰..x^d].
    let mut cols: Vec<Vec<Rational>> = vec![vec![Rational::zero(); size]; size];
    for j in 0..block {
        let jr = Rational::integer(i128::try_from(j).ok()?);
        // A_j column (index j)
        if j >= 1 {
            cols[j][j - 1] = jr; // A′ in (A′+aB)
        }
        cols[j][block + j] = a.checked_neg()?; // −aA in (B′−aA)
        // B_j column (index block+j)
        cols[block + j][j] = a; // aB in (A′+aB)
        if j >= 1 {
            cols[block + j][block + j - 1] = jr; // B′ in (B′−aA)
        }
    }
    // rhs: sin(u) ⇒ (A′+aB)=0, (B′−aA)=p ; cos(u) ⇒ (A′+aB)=p, (B′−aA)=0.
    let mut rhs = vec![Rational::zero(); size];
    let target = match which {
        UnaryFunc::Sin => block, // p goes in the second block
        _ => 0,                  // Cos: p goes in the first block
    };
    for (i, coeff) in p.iter().enumerate() {
        rhs[target + i] = *coeff;
    }
    let solution = ratint::solve_linear(&cols, &rhs)?;
    let a_expr = MultiPoly::from_univariate(var, &solution[0..block]).to_expr();
    let b_expr = MultiPoly::from_univariate(var, &solution[block..size]).to_expr();
    let arg_expr = MultiPoly::from_univariate(var, &arg_poly).to_expr();
    Some(CasExpr::Add(vec![
        CasExpr::Mul(vec![a_expr, arg_expr.clone().cos()]),
        CasExpr::Mul(vec![b_expr, arg_expr.sin()]),
    ]))
}

/// Flatten a (possibly left-nested) product into its multiplicative factors.
/// The `*` operator builds binary `Mul` nodes, so `x·eˣ·sin x` parses as
/// `Mul([Mul([x, eˣ]), sin x])`; the finders below need the flat factor list
/// `[x, eˣ, sin x]`. A non-product expression yields a one-element vector.
fn flatten_mul(expr: &CasExpr) -> Vec<CasExpr> {
    match expr {
        CasExpr::Mul(factors) => factors.iter().flat_map(flatten_mul).collect(),
        other => vec![other.clone()],
    }
}

/// Integrate `p(x)·e^{a·x+c}·trig(b·x+d)` (`trig ∈ {sin, cos}`) for a polynomial
/// `p` and linear exponent/argument. The antiderivative has the form
/// `e^{ax+c}·(A(x)·cos(bx+d) + B(x)·sin(bx+d))`, whose polynomial coefficients
/// `A, B` solve one coupled exact-rational linear system (matching, after
/// differentiation, the `cos` and `sin` parts of the integrand). Covers
/// `∫ eˣ·sin x = ½eˣ(sin x − cos x)`, `∫ e^{2x}cos x`, `∫ x·eˣ·sin x`, etc.
/// `None` outside this shape; certified downstream by differentiate-and-check.
fn integrate_exp_times_sinusoid(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    if !matches!(expr, CasExpr::Mul(_)) {
        return None;
    }
    let factors = flatten_mul(expr);
    let mut exp_arg: Option<CasExpr> = None;
    let mut trig: Option<(UnaryFunc, CasExpr)> = None;
    let mut rest: Vec<CasExpr> = Vec::new();
    for factor in &factors {
        match factor {
            CasExpr::Unary(UnaryFunc::Exp, arg) if exp_arg.is_none() => {
                exp_arg = Some((**arg).clone());
            }
            CasExpr::Unary(f @ (UnaryFunc::Sin | UnaryFunc::Cos), arg) if trig.is_none() => {
                trig = Some((*f, (**arg).clone()));
            }
            CasExpr::Unary(UnaryFunc::Exp | UnaryFunc::Sin | UnaryFunc::Cos, _) => return None,
            other => rest.push(other.clone()),
        }
    }
    let exp_arg = exp_arg?;
    let (which, trig_arg) = trig?;
    // Both the exponent and the trig argument must be linear in `var`.
    let exp_poly = normalize(&exp_arg)?.to_univariate(var)?;
    let trig_poly = normalize(&trig_arg)?.to_univariate(var)?;
    if poly::rat_degree(&exp_poly)? != 1 || poly::rat_degree(&trig_poly)? != 1 {
        return None;
    }
    let a = exp_poly[1]; // exponential rate
    let b = trig_poly[1]; // angular frequency
    let p = normalize(&CasExpr::Mul(rest))?.to_univariate(var)?;
    let degree = poly::rat_degree(&p)?;
    let block = degree + 1; // coefficients per polynomial A, B
    let size = 2 * block;
    // Unknowns [A₀..A_d, B₀..B_d]. Differentiating F = e^{ax+c}(A cos + B sin)
    // gives e^{ax+c}[(aA + A′ + bB) cos + (aB + B′ − bA) sin]. Equation block 1
    // (rows 0..block) matches the cos coefficient, block 2 (rows block..size) the
    // sin coefficient. `cols[column][row]`.
    let mut cols: Vec<Vec<Rational>> = vec![vec![Rational::zero(); size]; size];
    for j in 0..block {
        let jr = Rational::integer(i128::try_from(j).ok()?);
        // A_j column (index j): aA (row j, block 1), A′ (row j−1, block 1),
        // −bA (row block+j, block 2).
        cols[j][j] = a;
        if j >= 1 {
            cols[j][j - 1] = jr;
        }
        cols[j][block + j] = b.checked_neg()?;
        // B_j column (index block+j): bB (row j, block 1), aB (row block+j,
        // block 2), B′ (row block+j−1, block 2).
        cols[block + j][j] = b;
        cols[block + j][block + j] = a;
        if j >= 1 {
            cols[block + j][block + j - 1] = jr;
        }
    }
    // rhs: cos integrand ⇒ p in block 1; sin integrand ⇒ p in block 2.
    let mut rhs = vec![Rational::zero(); size];
    let target = match which {
        UnaryFunc::Cos => 0,
        _ => block,
    };
    for (i, coeff) in p.iter().enumerate() {
        rhs[target + i] = *coeff;
    }
    let solution = ratint::solve_linear(&cols, &rhs)?;
    let a_expr = MultiPoly::from_univariate(var, &solution[0..block]).to_expr();
    let b_expr = MultiPoly::from_univariate(var, &solution[block..size]).to_expr();
    let exp_expr = MultiPoly::from_univariate(var, &exp_poly).to_expr().exp();
    let trig_expr = MultiPoly::from_univariate(var, &trig_poly).to_expr();
    Some(CasExpr::Mul(vec![
        exp_expr,
        CasExpr::Add(vec![
            CasExpr::Mul(vec![a_expr, trig_expr.clone().cos()]),
            CasExpr::Mul(vec![b_expr, trig_expr.sin()]),
        ]),
    ]))
}

/// Integrate a **trigonometric monomial** `k·sin(u)^m·cos(u)^n` with a common
/// linear argument `u = a·x + b`, when at least one of `m, n` is odd. The odd
/// factor supplies the differential for a substitution (`w = cos u` when `m` is
/// odd, `w = sin u` when `n` is odd), reducing the integral to that of a
/// polynomial in `w` via the Pythagorean identity. Covers `∫ sin x·cos x`,
/// `∫ sin³x`, `∫ sin²x·cos x`, etc. Returns `None` when both powers are even
/// (a later power-reduction slice) or outside this shape; certified downstream.
fn integrate_trig_monomial(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let factors: Vec<CasExpr> = match expr {
        CasExpr::Mul(_) => flatten_mul(expr),
        CasExpr::Neg(a) => vec![CasExpr::int(-1), (**a).clone()],
        other @ (CasExpr::Unary(UnaryFunc::Sin | UnaryFunc::Cos, _) | CasExpr::Pow(_, _)) => {
            vec![other.clone()]
        }
        _ => return None,
    };
    let mut coeff = Rational::integer(1);
    let mut sin_pow = 0u32;
    let mut cos_pow = 0u32;
    let mut arg: Option<CasExpr> = None;
    // Record and cross-check the shared trig argument.
    let mut set_arg = |a: &CasExpr| -> Option<()> {
        match &arg {
            Some(existing) if existing == a => Some(()),
            Some(_) => None, // differing arguments — unsupported
            None => {
                arg = Some(a.clone());
                Some(())
            }
        }
    };
    for factor in &factors {
        match factor {
            CasExpr::Const(c) => coeff = coeff.checked_mul(*c)?,
            CasExpr::Unary(UnaryFunc::Sin, a) => {
                set_arg(a)?;
                sin_pow = sin_pow.checked_add(1)?;
            }
            CasExpr::Unary(UnaryFunc::Cos, a) => {
                set_arg(a)?;
                cos_pow = cos_pow.checked_add(1)?;
            }
            CasExpr::Pow(base, exp) => match base.as_ref() {
                CasExpr::Unary(UnaryFunc::Sin, a) => {
                    set_arg(a)?;
                    sin_pow = sin_pow.checked_add(*exp)?;
                }
                CasExpr::Unary(UnaryFunc::Cos, a) => {
                    set_arg(a)?;
                    cos_pow = cos_pow.checked_add(*exp)?;
                }
                _ => return None,
            },
            _ => return None,
        }
    }
    let arg = arg?;
    let arg_poly = normalize(&arg)?.to_univariate(var)?;
    if poly::rat_degree(&arg_poly)? != 1 {
        return None;
    }
    let a = arg_poly[1];
    let arg_expr = MultiPoly::from_univariate(var, &arg_poly).to_expr();
    // Build the polynomial P(w) so that the integrand equals P(trig)·(d/dx of the
    // substituted variable)/const, then integrate P and substitute back.
    //   m odd: w = cos u, integrand = k·sin·(1−w²)^{(m−1)/2}·wⁿ, ∫ = −(k/a)·∫P(w)dw
    //   n odd: w = sin u, integrand = k·cos·(1−w²)^{(n−1)/2}·wᵐ, ∫ = +(k/a)·∫P(w)dw
    let (base_pow, other_half, sign, substituted) = if sin_pow % 2 == 1 {
        (cos_pow, (sin_pow - 1) / 2, Rational::integer(-1), arg_expr.cos())
    } else if cos_pow % 2 == 1 {
        (sin_pow, (cos_pow - 1) / 2, Rational::integer(1), arg_expr.sin())
    } else {
        return None; // both even — not handled here
    };
    // P(w) = w^{base_pow} · (1 − w²)^{other_half}, as a dense coefficient vector.
    let one_minus_w2 = vec![Rational::integer(1), Rational::zero(), Rational::integer(-1)];
    let mut poly_w = vec![Rational::integer(1)];
    for _ in 0..other_half {
        poly_w = poly::ratpoly_mul(&poly_w, &one_minus_w2)?;
    }
    // Multiply by w^{base_pow} (shift up by base_pow).
    let base_shift = usize::try_from(base_pow).ok()?;
    let mut shifted = vec![Rational::zero(); base_shift];
    shifted.extend_from_slice(&poly_w);
    // Integrate term-by-term: ∫ Σ cᵢ wⁱ dw = Σ cᵢ/(i+1) w^{i+1}.
    let integrated = poly_antiderivative(&shifted)?;
    // Evaluate the antiderivative polynomial at w = substituted trig expression.
    let poly_in_w = eval_poly_at(&integrated, &substituted);
    let scale = coeff.checked_mul(sign)?.checked_div(a)?;
    Some(scaled_term(scale, poly_in_w))
}

/// The antiderivative of a dense univariate polynomial (`∫ Σ cᵢ xⁱ = Σ
/// cᵢ/(i+1) x^{i+1}`), as coefficients least-significant-first. `None` on overflow.
fn poly_antiderivative(coeffs: &[Rational]) -> Option<Vec<Rational>> {
    let mut out = vec![Rational::zero(); coeffs.len() + 1];
    for (i, &c) in coeffs.iter().enumerate() {
        let denom = Rational::integer(i128::try_from(i + 1).ok()?);
        out[i + 1] = c.checked_div(denom)?;
    }
    Some(out)
}

/// Evaluate a dense polynomial (coefficients least-significant-first) at a
/// [`CasExpr`] point, emitting a clean sum `Σ cᵢ·pointⁱ` that skips zero
/// coefficients (so no `0·point` noise reaches the output).
fn eval_poly_at(coeffs: &[Rational], point: &CasExpr) -> CasExpr {
    let mut terms: Vec<CasExpr> = Vec::new();
    for (i, &c) in coeffs.iter().enumerate() {
        if c.is_zero() {
            continue;
        }
        let power = match u32::try_from(i) {
            Ok(0) => CasExpr::Const(c),
            Ok(1) => scaled_term(c, point.clone()),
            Ok(p) => scaled_term(c, point.clone().pow(p)),
            Err(_) => continue,
        };
        terms.push(power);
    }
    match terms.len() {
        0 => CasExpr::zero(),
        1 => terms.pop().unwrap_or_else(CasExpr::zero),
        _ => CasExpr::Add(terms),
    }
}

/// Elementary-function integration by table, for `k · f(a·x + b)` where `f` is a
/// standard elementary function and the argument is linear in `var`. Returns the
/// antiderivative or `None` outside the supported shapes; certified downstream.
fn integrate_elementary(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    // Peel an optional rational constant coefficient: k · f(..).
    let (coeff, inner) = match expr {
        CasExpr::Unary(_, _) => (Rational::integer(1), expr),
        CasExpr::Neg(a) => (Rational::integer(-1), a.as_ref()),
        CasExpr::Mul(factors) if factors.len() == 2 => match (&factors[0], &factors[1]) {
            (CasExpr::Const(k), u @ CasExpr::Unary(_, _))
            | (u @ CasExpr::Unary(_, _), CasExpr::Const(k)) => (*k, u),
            _ => return None,
        },
        _ => return None,
    };
    let CasExpr::Unary(func, arg) = inner else {
        return None;
    };
    // The argument must be linear in `var`: a·x + b (a ≠ 0).
    let arg_poly = normalize(arg)?.to_univariate(var)?;
    if poly::rat_degree(&arg_poly)? != 1 {
        return None;
    }
    let a = arg_poly[1];
    let arg_expr = MultiPoly::from_univariate(var, &arg_poly).to_expr();
    // ∫ k·f(a·x+b) dx for the closed-form cases.
    let build = |c: Rational, body: CasExpr| -> Option<CasExpr> {
        let k = coeff.checked_mul(c)?.checked_div(a)?;
        Some(scaled_term(k, body))
    };
    match func {
        // ∫ exp(u) = (1/a) exp(u)
        UnaryFunc::Exp => build(Rational::integer(1), arg_expr.exp()),
        // ∫ sin(u) = -(1/a) cos(u)
        UnaryFunc::Sin => build(Rational::integer(-1), arg_expr.cos()),
        // ∫ cos(u) = (1/a) sin(u)
        UnaryFunc::Cos => build(Rational::integer(1), arg_expr.sin()),
        // ∫ ln(u) = (u/a)(ln(u) − 1)  [by parts]
        UnaryFunc::Ln => {
            let k = coeff.checked_div(a)?;
            let body = CasExpr::Mul(vec![arg_expr.clone(), arg_expr.ln() - CasExpr::int(1)]);
            Some(scaled_term(k, body))
        }
        // ∫ atan(u) = (1/a)[u·atan(u) − ½·ln(1 + u²)]  [by parts]
        UnaryFunc::Atan => {
            let k = coeff.checked_div(a)?;
            let body = arg_expr.clone() * arg_expr.clone().atan()
                - CasExpr::rat(1, 2) * (CasExpr::int(1) + arg_expr.pow(2)).ln();
            Some(scaled_term(k, body))
        }
        // ∫ tan(u) = -(1/a) ln(cos u); certified via the Euler fallback in
        // `equal` (which folds `tan` into `sin/cos`). The CAS `ln` stands for
        // the real `ln|·|` on the integrand's domain.
        UnaryFunc::Tan => build(Rational::integer(-1), arg_expr.cos().ln()),
        // sqrt closed forms are a later slice.
        _ => None,
    }
}

/// The rational part of `∫ expr dx` for a univariate rational function, via
/// Horowitz reduction. Returns `None` if `expr` is not a univariate rational
/// function, requires a logarithmic part, or on overflow.
fn integrate_rational(expr: &CasExpr, var: &str) -> Option<CasExpr> {
    let rf = normalize_rational(expr)?;
    let num = rf.num.to_univariate(var)?;
    let den = rf.den.to_univariate(var)?;
    if ratint::is_zero(&den) {
        return None;
    }
    // Proper/improper split: num = quotient·den + proper, deg proper < deg den.
    let (quotient, proper) = ratint::divrem(&num, &den)?;
    let quotient_integral = integrate_univariate_poly(&quotient)?;

    // Rational + logarithmic parts (Horowitz split).
    let mut parts: Vec<CasExpr> = Vec::new();
    if !ratint::is_zero(&quotient_integral) {
        parts.push(MultiPoly::from_univariate(var, &quotient_integral).to_expr());
    }
    if !ratint::is_zero(&proper) {
        let bound = proper.len() + den.len() + 4;
        let common = poly::rat_gcd(&proper, &den, bound)?;
        let reduced_num = poly::rat_exact_div(&proper, &common)?;
        let reduced_den = poly::rat_exact_div(&den, &common)?;
        let (b_num, rat_den, c_num, log_den) = ratint::horowitz(&reduced_num, &reduced_den)?;
        if !ratint::is_zero(&b_num) {
            parts.push(ratfunc_to_expr(var, &b_num, &rat_den));
        }
        if !ratint::is_zero(&c_num) {
            // Logarithmic part ∫ C/D₁; declines (None) beyond the supported slice.
            parts.push(integrate_log_part(var, &c_num, &log_den)?);
        }
    }

    Some(match parts.len() {
        0 => CasExpr::zero(),
        1 => parts.into_iter().next().unwrap_or_else(CasExpr::zero),
        _ => CasExpr::Add(parts),
    })
}

/// The logarithmic part `∫ c/d dx` of a rational integral, where `d` is
/// squarefree and `deg c < deg d`. Currently handles a **linear** denominator
/// `d = a·x + b` → `(c/a)·ln(a·x + b)` (the `∫ 1/(ax+b)` family). A higher-degree
/// denominator needs the Rothstein–Trager resultant (a later slice) and declines
/// to `None` — the certificate then rejects, never a wrong answer.
fn integrate_log_part(var: &str, c: &[Rational], d: &[Rational]) -> Option<CasExpr> {
    // Reduce to gcd(c, d) = 1.
    let bound = c.len() + d.len() + 4;
    let common = poly::rat_gcd(c, d, bound)?;
    let cc = poly::rat_exact_div(c, &common)?;
    let dd = poly::rat_exact_div(d, &common)?;
    if poly::rat_degree(&dd)? == 1 {
        // Linear denominator a·x+b: ∫ c0/(a·x+b) = (c0/a)·ln(a·x+b).
        let lead = dd[1];
        let c0 = cc.first().copied().unwrap_or_else(Rational::zero);
        let coeff = c0.checked_div(lead)?;
        let ln = CasExpr::Unary(
            UnaryFunc::Ln,
            Box::new(MultiPoly::from_univariate(var, &dd).to_expr()),
        );
        return Some(scaled_term(coeff, ln));
    }
    // Degree ≥ 2: Rothstein–Trager. ∫ C/D₁ = Σ cᵢ·ln(vᵢ), cᵢ the rational roots
    // of Res_t, vᵢ = gcd(C − cᵢ·D₁', D₁).
    if let Some(terms) = ratint::log_terms(&cc, &dd) {
        let mut sum: Vec<CasExpr> = Vec::with_capacity(terms.len());
        for (coeff, v_poly) in terms {
            let ln = CasExpr::Unary(
                UnaryFunc::Ln,
                Box::new(MultiPoly::from_univariate(var, &v_poly).to_expr()),
            );
            sum.push(scaled_term(coeff, ln));
        }
        return match sum.len() {
            0 => None,
            1 => sum.into_iter().next(),
            _ => Some(CasExpr::Add(sum)),
        };
    }
    // No rational roots: an irreducible **quadratic** denominator has a real
    // closed form in ln + atan (∫ 1/(x²+1) = atan x). Higher-degree irreducible
    // denominators need algebraic-number roots (a later slice) → None.
    if poly::rat_degree(&dd)? == 2 {
        return integrate_irreducible_quadratic(var, &cc, &dd);
    }
    None
}

/// `∫ (c₁·x + c₀)/(a·x² + b·x + d) dx` for an **irreducible** quadratic
/// (discriminant `b² − 4ad < 0`) whose `√(4ad − b²)` is rational:
/// `(c₁/2a)·ln(a·x²+b·x+d) + ((2a·c₀ − b·c₁)/(a·s))·atan((2a·x + b)/s)`,
/// `s = √(4ad − b²)`. Declines (`None`) when the root is irrational (needs
/// algebraic numbers). Certified downstream by differentiate-and-check.
fn integrate_irreducible_quadratic(var: &str, cc: &[Rational], dd: &[Rational]) -> Option<CasExpr> {
    let a = dd[2];
    let b = dd.get(1).copied().unwrap_or_else(Rational::zero);
    let d = dd.first().copied().unwrap_or_else(Rational::zero);
    let c1 = cc.get(1).copied().unwrap_or_else(Rational::zero);
    let c0 = cc.first().copied().unwrap_or_else(Rational::zero);
    // 4ad − b² must be positive (irreducible) and a perfect rational square.
    let four_ad = Rational::integer(4).checked_mul(a)?.checked_mul(d)?;
    let neg_disc = four_ad.checked_sub(b.checked_mul(b)?)?;
    if neg_disc.numerator() <= 0 {
        return None; // real roots — handled by the rational-root path, not here
    }
    let s = rational_sqrt(neg_disc)?;
    let two_a = Rational::integer(2).checked_mul(a)?;

    let mut parts: Vec<CasExpr> = Vec::new();
    // ln term (present only when the numerator has an x-component).
    if !c1.is_zero() {
        let ln_coeff = c1.checked_div(two_a)?;
        let ln = CasExpr::Unary(
            UnaryFunc::Ln,
            Box::new(MultiPoly::from_univariate(var, dd).to_expr()),
        );
        parts.push(scaled_term(ln_coeff, ln));
    }
    // atan term: coefficient (2a·c₀ − b·c₁)/(a·s), argument (2a·x + b)/s.
    let atan_coeff = two_a
        .checked_mul(c0)?
        .checked_sub(b.checked_mul(c1)?)?
        .checked_div(a.checked_mul(s)?)?;
    if !atan_coeff.is_zero() {
        let arg =
            MultiPoly::from_univariate(var, &[b.checked_div(s)?, two_a.checked_div(s)?]).to_expr();
        let atan = CasExpr::Unary(UnaryFunc::Atan, Box::new(arg));
        parts.push(if atan_coeff == Rational::integer(1) {
            atan
        } else if atan_coeff == Rational::integer(-1) {
            CasExpr::Neg(Box::new(atan))
        } else {
            CasExpr::Mul(vec![CasExpr::Const(atan_coeff), atan])
        });
    }
    match parts.len() {
        0 => None,
        1 => parts.into_iter().next(),
        _ => Some(CasExpr::Add(parts)),
    }
}

/// The exact square root of a non-negative rational, if it is rational (i.e.
/// numerator and denominator are both perfect squares); else `None`.
fn rational_sqrt(r: Rational) -> Option<Rational> {
    let sn = isqrt(r.numerator())?;
    let sd = isqrt(r.denominator())?;
    if sn.checked_mul(sn)? == r.numerator() && sd.checked_mul(sd)? == r.denominator() {
        Rational::checked_new(sn, sd)
    } else {
        None
    }
}

/// Decompose `√value` (for `value ≥ 0`) into `coeff · √radicand` with a
/// **square-free integer** `radicand`, so `√8 → 2·√2` and `√(8) / 2 → √2`.
/// Returns `(coeff, radicand)`; `radicand == 1` means `value` is a perfect
/// rational square (`coeff = √value`). `None` for negative input or overflow.
///
/// `√(p/q) = √(p·q)/q`; factor `p·q`, pull each prime pair outside the root.
fn simplify_surd(value: Rational) -> Option<(Rational, Rational)> {
    if value.numerator() < 0 {
        return None;
    }
    let q = value.denominator();
    let under = value.numerator().checked_mul(q)?; // p·q, the integer under the root
    if under == 0 {
        return Some((Rational::zero(), Rational::integer(1)));
    }
    let mut coeff_num = 1_i128;
    let mut radicand = 1_i128;
    for (prime, mult) in ntheory::factorize(under) {
        for _ in 0..mult / 2 {
            coeff_num = coeff_num.checked_mul(prime)?;
        }
        if mult % 2 == 1 {
            radicand = radicand.checked_mul(prime)?;
        }
    }
    // √value = √under / q = (coeff_num / q)·√radicand.
    let coeff = Rational::checked_new(coeff_num, q)?;
    Some((coeff, Rational::integer(radicand)))
}

/// Integer floor square root via Newton's method (`None` for negative input).
fn isqrt(n: i128) -> Option<i128> {
    if n < 0 {
        return None;
    }
    if n < 2 {
        return Some(n);
    }
    let mut x = n;
    let mut y = x.midpoint(1);
    while y < x {
        x = y;
        y = x.midpoint(n / x);
    }
    Some(x)
}

/// `coeff · ln_expr`, presenting `±1` cleanly (`ln_expr` / `−ln_expr`).
fn scaled_term(coeff: Rational, ln_expr: CasExpr) -> CasExpr {
    if coeff == Rational::integer(1) {
        ln_expr
    } else if coeff == Rational::integer(-1) {
        CasExpr::Neg(Box::new(ln_expr))
    } else {
        CasExpr::Mul(vec![CasExpr::Const(coeff), ln_expr])
    }
}

/// `∫ p dx` for a univariate polynomial coefficient vector: coefficient `i`
/// becomes `p[i]/(i+1)` at degree `i+1` (constant of integration dropped).
fn integrate_univariate_poly(p: &[Rational]) -> Option<Vec<Rational>> {
    if ratint::is_zero(p) {
        return Some(Vec::new());
    }
    let mut out = vec![Rational::zero(); p.len() + 1];
    for (i, c) in p.iter().enumerate() {
        out[i + 1] = c.checked_div(Rational::integer(i128::try_from(i + 1).ok()?))?;
    }
    Some(out)
}

/// Build `num/den` as a `CasExpr` from univariate coefficient vectors, collapsing
/// a constant-`1` denominator to just the numerator.
fn ratfunc_to_expr(var: &str, num: &[Rational], den: &[Rational]) -> CasExpr {
    let num_expr = MultiPoly::from_univariate(var, num).to_expr();
    if den.len() == 1 && den[0] == Rational::integer(1) {
        num_expr
    } else {
        CasExpr::Div(
            Box::new(num_expr),
            Box::new(MultiPoly::from_univariate(var, den).to_expr()),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::poly;

    fn v(name: &str) -> CasExpr {
        CasExpr::var(name)
    }

    fn assert_equal(a: &CasExpr, b: &CasExpr) {
        match equal(a, b) {
            ZeroTest::Certified { equal, witness } => {
                assert!(equal, "expected equal; difference witness = {witness:?}");
            }
            ZeroTest::Unknown => panic!("expected a decidable (Certified) result"),
        }
    }

    fn assert_not_equal(a: &CasExpr, b: &CasExpr) {
        match equal(a, b) {
            ZeroTest::Certified { equal, .. } => assert!(!equal, "expected not-equal"),
            ZeroTest::Unknown => panic!("expected a decidable (Certified) result"),
        }
    }

    #[test]
    fn exemplar_d_x2_plus_c_is_2x() {
        // The motivating exemplar: D[x² + c] = 2x, with c a symbolic constant.
        let f = v("x").pow(2) + v("c");
        let df = f.differentiate("x");
        let claimed = CasExpr::int(2) * v("x");
        assert_equal(&df, &claimed);

        // And it is certified with a re-checkable zero witness.
        let result = prove_derivative(&f, "x", &claimed);
        assert_eq!(result.certainty(), Certainty::Certified);
        match result {
            ZeroTest::Certified { equal, witness } => {
                assert!(equal);
                assert!(witness.is_zero());
            }
            ZeroTest::Unknown => panic!(),
        }
    }

    #[test]
    fn derivative_of_c_wrt_x_is_zero() {
        // c is a parameter, not the differentiation variable.
        let df = v("c").differentiate("x");
        assert_equal(&df, &CasExpr::zero());
    }

    #[test]
    fn power_rule() {
        // d/dx x³ = 3x²
        let df = v("x").pow(3).differentiate("x");
        let claimed = CasExpr::int(3) * v("x").pow(2);
        assert_equal(&df, &claimed);
    }

    #[test]
    fn product_rule() {
        // d/dx (x+1)(x+2) = 2x + 3
        let f = (v("x") + CasExpr::int(1)) * (v("x") + CasExpr::int(2));
        let df = f.differentiate("x");
        let claimed = CasExpr::int(2) * v("x") + CasExpr::int(3);
        assert_equal(&df, &claimed);
    }

    #[test]
    fn multivariate_partial_derivative() {
        // f = x²y + y³ ;  ∂f/∂x = 2xy
        let f = v("x").pow(2) * v("y") + v("y").pow(3);
        let partial_x = f.differentiate("x");
        assert_equal(&partial_x, &(CasExpr::int(2) * v("x") * v("y")));
        // ∂f/∂y = x² + 3y²
        let partial_y = f.differentiate("y");
        let claimed = v("x").pow(2) + CasExpr::int(3) * v("y").pow(2);
        assert_equal(&partial_y, &claimed);
    }

    #[test]
    fn zero_test_detects_inequality() {
        // 2x + 1 ≠ 2x
        assert_not_equal(
            &(CasExpr::int(2) * v("x") + CasExpr::int(1)),
            &(CasExpr::int(2) * v("x")),
        );
    }

    #[test]
    fn rational_coefficients_are_exact() {
        // d/dx ( (1/2) x² ) = x
        let f = CasExpr::rat(1, 2) * v("x").pow(2);
        assert_equal(&f.differentiate("x"), &v("x"));
    }

    #[test]
    fn differentiation_matches_poly_rat_derivative_univariate() {
        // Independent cross-check: for single-variable polynomials, our symbolic
        // differentiate + normalize must agree exactly with the trusted numeric
        // `poly::rat_derivative` on the extracted coefficient vector.
        // Test polynomials in x (coefficients chosen deterministically).
        let polys = [
            // 5 - 2x + 3x³
            CasExpr::int(5) - CasExpr::int(2) * v("x") + CasExpr::int(3) * v("x").pow(3),
            // (2x - 1)(x + 4)
            (CasExpr::int(2) * v("x") - CasExpr::int(1)) * (v("x") + CasExpr::int(4)),
            // (1/3)x⁴ + 7x
            CasExpr::rat(1, 3) * v("x").pow(4) + CasExpr::int(7) * v("x"),
            // x⁵
            v("x").pow(5),
        ];
        for f in &polys {
            let ours = normalize(&f.differentiate("x"))
                .expect("no overflow")
                .to_univariate("x")
                .expect("univariate");
            let base = normalize(f)
                .expect("no overflow")
                .to_univariate("x")
                .expect("univariate");
            let trusted = poly::rat_derivative(&base).expect("no overflow");
            // Compare up to trailing-zero trimming.
            let trim = |mut v: Vec<Rational>| {
                while v.last().is_some_and(|c| c.is_zero()) {
                    v.pop();
                }
                v
            };
            assert_eq!(
                trim(ours),
                trim(trusted),
                "symbolic derivative disagrees with poly::rat_derivative for {f:?}"
            );
        }
    }

    #[test]
    fn normalize_preserves_value_under_evaluation() {
        // Self-check in the axeyum-scenarios spirit: the canonical form must have
        // the same denotation as the expression, confirmed by the trusted
        // evaluator at several exact rational points.
        let f = (v("x") + CasExpr::int(2)).pow(2) * v("y") - CasExpr::int(3) * v("x");
        let p = normalize(&f).expect("no overflow");
        let points: [(i128, i128); 4] = [(0, 1), (1, 1), (-2, 3), (5, 2)];
        for (i, (xn, xd)) in points.iter().enumerate() {
            let mut env = BTreeMap::new();
            env.insert("x".to_owned(), Rational::new(*xn, *xd));
            env.insert(
                "y".to_owned(),
                Rational::integer(i128::try_from(i).unwrap() + 1),
            );
            assert_eq!(
                f.eval(&env),
                p.eval(&env),
                "normalize changed the value at point {i}"
            );
        }
    }

    #[test]
    fn certified_equal_agrees_with_evaluation() {
        // If the zero-test certifies equality, the two sides must agree at every
        // sample point under the trusted evaluator (an independent confirmation
        // of the certificate).
        let f = (v("x") + v("y")).pow(2);
        let g = v("x").pow(2) + CasExpr::int(2) * v("x") * v("y") + v("y").pow(2);
        assert_equal(&f, &g);
        let points: [(i128, i128); 3] = [(1, 1), (-3, 2), (4, 1)];
        for (xn, yn) in points {
            let mut env = BTreeMap::new();
            env.insert("x".to_owned(), Rational::integer(xn));
            env.insert("y".to_owned(), Rational::integer(yn));
            assert_eq!(f.eval(&env), g.eval(&env));
        }
    }

    #[test]
    fn quotient_rule_reciprocal() {
        // d/dx (1/x) = -1/x²
        let f = CasExpr::int(1) / v("x");
        let claimed = CasExpr::int(-1) / v("x").pow(2);
        assert_equal(&f.differentiate("x"), &claimed);
    }

    #[test]
    fn quotient_rule_general() {
        // d/dx ( x / (x+1) ) = 1 / (x+1)²
        let f = v("x") / (v("x") + CasExpr::int(1));
        let df = f.differentiate("x");
        let claimed = CasExpr::int(1) / (v("x") + CasExpr::int(1)).pow(2);
        assert_equal(&df, &claimed);

        // Independent confirmation by the trusted evaluator at sample points.
        let points: [i128; 3] = [0, 2, -3];
        for xn in points {
            let mut env = BTreeMap::new();
            env.insert("x".to_owned(), Rational::integer(xn));
            assert_eq!(df.eval(&env), claimed.eval(&env), "mismatch at x={xn}");
        }
    }

    #[test]
    fn rational_equality_by_cross_multiplication() {
        // (x² − 1)/(x − 1) = x + 1  — certified without computing a GCD.
        let lhs = (v("x").pow(2) - CasExpr::int(1)) / (v("x") - CasExpr::int(1));
        let rhs = v("x") + CasExpr::int(1);
        assert_equal(&lhs, &rhs);
    }

    #[test]
    fn expand_is_certified_and_matches_hand_expansion() {
        // expand((x+1)³) = x³ + 3x² + 3x + 1, value-equal to the original.
        let f = (v("x") + CasExpr::int(1)).pow(3);
        let e = expand(&f).expect("polynomial");
        assert_equal(&e, &f);
        let hand = v("x").pow(3)
            + CasExpr::int(3) * v("x").pow(2)
            + CasExpr::int(3) * v("x")
            + CasExpr::int(1);
        assert_equal(&e, &hand);
    }

    #[test]
    fn trigsimp_applies_pythagorean_identity() {
        let x = || v("x");
        let i = CasExpr::int;
        // sin²+cos² → 1; 2sin²+2cos² → 2; (sin²+cos²)² → 1.
        assert_equal(&trigsimp(&(x().sin().pow(2) + x().cos().pow(2))), &i(1));
        assert_equal(
            &trigsimp(&(i(2) * x().sin().pow(2) + i(2) * x().cos().pow(2))),
            &i(2),
        );
        assert_equal(
            &trigsimp(
                &(x().sin().pow(4)
                    + i(2) * x().sin().pow(2) * x().cos().pow(2)
                    + x().cos().pow(4)),
            ),
            &i(1),
        );
        // 1−cos² → sin², 1−sin² → cos² (clean heads, value-equal).
        let s2 = trigsimp(&(i(1) - x().cos().pow(2)));
        assert_equal(&s2, &x().sin().pow(2));
        assert!(!s2.to_string().contains('\0'));
        // Every result is value-equal; a trig-free input is untouched.
        assert_eq!(trigsimp(&(x().pow(2) + i(1))), x().pow(2) + i(1));
    }

    #[test]
    fn transforms_do_not_leak_atom_keys() {
        // Regression: expand/cancel/simplify normalize transcendental heads to
        // opaque `\0head:…` atoms internally; the de-atomization post-pass must
        // rebuild clean heads so no raw atom key ever reaches the caller.
        let x = || v("x");
        let y = || v("y");
        let cases = [
            x().sin(),
            (CasExpr::int(2) * x() + CasExpr::int(1)).sin(),
            x().tan(),
            x().ln() + x().sqrt() + x().atan(),
            x().exp(),
            (x() - y()).exp(),
            (CasExpr::int(2) * x() - CasExpr::int(3) * y()).exp(),
            x() * x().sin() + x().cos(),
        ];
        for case in cases {
            for transformed in [expand(&case), cancel(&case), Some(simplify(&case))]
                .into_iter()
                .flatten()
            {
                let rendered = transformed.to_string();
                assert!(
                    !rendered.contains('\0') && !rendered.contains(':'),
                    "atom key leaked for {case}: {rendered}",
                );
                // De-atomization must stay value-preserving.
                assert_equal(&transformed, &case);
            }
        }
    }

    #[test]
    fn expand_rational_function_is_value_preserving() {
        // expand of a rational function stays value-equal to the original.
        let f = (v("x").pow(2) - CasExpr::int(1)) / (v("x") + CasExpr::int(2));
        let e = expand(&f).expect("rational");
        assert_equal(&e, &f);
    }

    #[test]
    fn cancel_multivariate_via_mvpoly() {
        // (x²−y²)/(x−y) = x+y — needs the multivariate GCD.
        let f = (v("x").pow(2) - v("y").pow(2)) / (v("x") - v("y"));
        let c = cancel(&f).expect("rational");
        assert_equal(&c, &(v("x") + v("y")));
        assert_equal(&c, &f);
        // (x²y − y³)/(x − y) = x·y + y²
        let g = (v("x").pow(2) * v("y") - v("y").pow(3)) / (v("x") - v("y"));
        assert_equal(
            &cancel(&g).expect("rational"),
            &(v("x") * v("y") + v("y").pow(2)),
        );
    }

    #[test]
    fn cancel_reduces_to_lowest_terms() {
        // (x² − 1)/(x − 1) cancels to the polynomial x + 1.
        let f = (v("x").pow(2) - CasExpr::int(1)) / (v("x") - CasExpr::int(1));
        let c = cancel(&f).expect("univariate");
        assert_equal(&c, &(v("x") + CasExpr::int(1)));
        assert!(
            normalize(&c).is_some(),
            "fully cancelled result should be a polynomial (denominator 1)"
        );
    }

    #[test]
    fn cancel_common_factor() {
        // (2x² + 2x)/(x + 1) = 2x
        let f = (CasExpr::int(2) * v("x").pow(2) + CasExpr::int(2) * v("x"))
            / (v("x") + CasExpr::int(1));
        assert_equal(
            &cancel(&f).expect("univariate"),
            &(CasExpr::int(2) * v("x")),
        );
    }

    #[test]
    fn cancel_preserves_value_where_defined() {
        // (x² − 4)/(x − 2) = x + 2, confirmed by the trusted evaluator.
        let f = (v("x").pow(2) - CasExpr::int(4)) / (v("x") - CasExpr::int(2));
        let c = cancel(&f).expect("univariate");
        for xn in [0_i128, 3, -5, 7] {
            let mut env = BTreeMap::new();
            env.insert("x".to_owned(), Rational::integer(xn));
            assert_eq!(c.eval(&env), Some(Rational::integer(xn + 2)));
        }
    }

    #[test]
    fn division_by_zero_is_unknown() {
        // 1/0 is undefined: the zero-test must decline, never certify.
        let bad = CasExpr::int(1) / CasExpr::zero();
        assert_eq!(equal(&bad, &CasExpr::int(1)), ZeroTest::Unknown);
    }

    #[test]
    fn integrate_polynomial_is_certified() {
        // ∫ (3x² + 2x) dx = x³ + x², and the answer PROVES itself: differentiating
        // it back and zero-testing against the integrand certifies equality.
        let integrand = CasExpr::int(3) * v("x").pow(2) + CasExpr::int(2) * v("x");
        let result = integrate(&integrand, "x").expect("polynomial");
        assert!(
            result.is_certified(),
            "integration answer must carry its proof"
        );
        assert_equal(&result.antiderivative, &(v("x").pow(3) + v("x").pow(2)));
        // The certificate is exactly d/dx(F) − integrand ≡ 0.
        assert_eq!(result.certificate.certainty(), Certainty::Certified);
    }

    #[test]
    fn integrate_produces_rational_coefficients() {
        // ∫ x⁴ dx = (1/5) x⁵ — exact rational coefficient, certified.
        let result = integrate(&v("x").pow(4), "x").expect("polynomial");
        assert!(result.is_certified());
        assert_equal(
            &result.antiderivative,
            &(CasExpr::rat(1, 5) * v("x").pow(5)),
        );
    }

    #[test]
    fn integrate_treats_other_variables_as_constants() {
        // ∫ (x·y + y²) dx = (1/2)x²·y + y²·x, certified.
        let integrand = v("x") * v("y") + v("y").pow(2);
        let result = integrate(&integrand, "x").expect("polynomial");
        assert!(result.is_certified());
        let claimed = CasExpr::rat(1, 2) * v("x").pow(2) * v("y") + v("y").pow(2) * v("x");
        assert_equal(&result.antiderivative, &claimed);
    }

    #[test]
    fn fundamental_theorem_roundtrip() {
        // d/dx ∫ f dx = f, for a batch of polynomials — the certificate proves it.
        let fs = [
            CasExpr::int(7),
            v("x").pow(5) - CasExpr::int(4) * v("x").pow(2) + CasExpr::int(1),
            CasExpr::rat(2, 3) * v("x").pow(3) + CasExpr::int(9) * v("x"),
        ];
        for f in &fs {
            let integral = integrate(f, "x").expect("polynomial");
            assert!(integral.is_certified(), "not certified for {f:?}");
            // Explicit: differentiating the antiderivative returns the integrand.
            assert_equal(&integral.antiderivative.differentiate("x"), f);
        }
    }

    #[test]
    fn integrate_rational_with_rational_antiderivative() {
        // ∫ 1/x² dx = −1/x, certified by differentiate-and-check.
        let f = CasExpr::int(1) / v("x").pow(2);
        let result = integrate(&f, "x").expect("rational antiderivative exists");
        assert!(result.is_certified());
        assert_equal(&result.antiderivative, &(CasExpr::int(-1) / v("x")));
    }

    #[test]
    fn integrate_improper_rational() {
        // ∫ (x² + 1)/x² dx = x − 1/x  (polynomial part + Horowitz rational part).
        let f = (v("x").pow(2) + CasExpr::int(1)) / v("x").pow(2);
        let result = integrate(&f, "x").expect("rational");
        assert!(result.is_certified());
        assert_equal(&result.antiderivative.differentiate("x"), &f);
    }

    #[test]
    fn integrate_rational_roundtrip_via_differentiation() {
        // For each rational R with a rational antiderivative, ∫ R' dx must
        // certify and differentiate back to R' — a self-certifying round trip.
        let rs = [
            CasExpr::int(1) / v("x"),                            // R' = −1/x²
            CasExpr::int(1) / (v("x").pow(2) + CasExpr::int(1)), // R' = −2x/(x²+1)²
            v("x") / (v("x") + CasExpr::int(1)),                 // R' = 1/(x+1)²
        ];
        for r in &rs {
            let integrand = r.differentiate("x");
            let result = integrate(&integrand, "x").expect("rational antiderivative exists");
            assert!(result.is_certified(), "not certified for R = {r}");
            assert_equal(&result.antiderivative.differentiate("x"), &integrand);
        }
    }

    #[test]
    fn integrate_linear_logarithm() {
        // ∫ 1/x dx = ln(x), certified by d/dx ln(x) = 1/x.
        let f = CasExpr::int(1) / v("x");
        let result = integrate(&f, "x").expect("logarithmic integral");
        assert!(result.is_certified());
        assert_equal(&result.antiderivative.differentiate("x"), &f);
        // ∫ 1/(2x + 1) dx = (1/2) ln(2x + 1).
        let g = CasExpr::int(1) / (CasExpr::int(2) * v("x") + CasExpr::int(1));
        let r2 = integrate(&g, "x").expect("logarithmic integral");
        assert!(r2.is_certified());
        assert_equal(&r2.antiderivative.differentiate("x"), &g);
    }

    #[test]
    fn integrate_quadratic_logarithm() {
        // ∫ 2x/(x²+1) dx = ln(x²+1) (Rothstein–Trager, root t=1, v=x²+1).
        let f = (CasExpr::int(2) * v("x")) / (v("x").pow(2) + CasExpr::int(1));
        let r1 = integrate(&f, "x").expect("logarithmic integral");
        assert!(r1.is_certified());
        assert_equal(&r1.antiderivative.differentiate("x"), &f);
        // ∫ 1/(x²−1) dx = ½·ln(x−1) − ½·ln(x+1) (two rational roots ±½).
        let g = CasExpr::int(1) / (v("x").pow(2) - CasExpr::int(1));
        let r2 = integrate(&g, "x").expect("logarithmic integral");
        assert!(r2.is_certified());
        assert_equal(&r2.antiderivative.differentiate("x"), &g);
    }

    #[test]
    fn integrate_arctangent() {
        // ∫ 1/(x²+1) dx = atan(x), certified by d/dx atan(x) = 1/(x²+1).
        let f = CasExpr::int(1) / (v("x").pow(2) + CasExpr::int(1));
        let r1 = integrate(&f, "x").expect("arctangent integral");
        assert!(r1.is_certified());
        assert_equal(&r1.antiderivative.differentiate("x"), &f);
        // ∫ 1/(x²+4) dx = ½·atan(x/2).
        let g = CasExpr::int(1) / (v("x").pow(2) + CasExpr::int(4));
        let r2 = integrate(&g, "x").expect("arctangent integral");
        assert!(r2.is_certified());
        assert_equal(&r2.antiderivative.differentiate("x"), &g);
        // ∫ (x+1)/(x²+1) dx = ½·ln(x²+1) + atan(x) (mixed ln + atan).
        let h = (v("x") + CasExpr::int(1)) / (v("x").pow(2) + CasExpr::int(1));
        let r3 = integrate(&h, "x").expect("mixed integral");
        assert!(r3.is_certified());
        assert_equal(&r3.antiderivative.differentiate("x"), &h);
    }

    #[test]
    fn integrate_declines_irrational_quadratic() {
        // ∫ 1/(x²+2) dx = (1/√2)·atan(x/√2): the coefficient is irrational
        // (needs algebraic numbers), so honest None — never a wrong answer.
        let f = CasExpr::int(1) / (v("x").pow(2) + CasExpr::int(2));
        assert!(integrate(&f, "x").is_none());
    }

    #[test]
    fn substitute_composes_expressions() {
        // x² with x := (y+1)  →  (y+1)², i.e. y² + 2y + 1.
        let f = v("x").pow(2);
        let g = f.substitute("x", &(v("y") + CasExpr::int(1)));
        let claimed = v("y").pow(2) + CasExpr::int(2) * v("y") + CasExpr::int(1);
        assert_equal(&g, &claimed);
        // Other variables are untouched.
        assert_eq!(v("z").substitute("x", &v("y")), v("z"));
    }

    #[test]
    fn substitute_verifies_a_root() {
        // 1 is a double root of x² − 2x + 1 = (x−1)²: substituting x := 1 gives 0.
        let p = v("x").pow(2) - CasExpr::int(2) * v("x") + CasExpr::int(1);
        let at_one = p.substitute("x", &CasExpr::int(1));
        assert_equal(&at_one, &CasExpr::zero());
    }

    #[test]
    fn display_is_readable() {
        assert_eq!(format!("{}", v("x").pow(2) + v("c")), "x^2 + c");
        assert_eq!(format!("{}", CasExpr::int(2) * v("x")), "2*x");
        assert_eq!(
            format!("{}", (v("x") + CasExpr::int(1)).pow(2)),
            "(x + 1)^2"
        );
        assert_eq!(format!("{}", v("x") - CasExpr::int(3)), "x - 3");
        assert_eq!(
            format!("{}", CasExpr::rat(1, 5) * v("x").pow(5)),
            "(1/5)*x^5"
        );
    }

    #[test]
    fn dsolve_constant_coefficient_odes() {
        let ig = Rational::integer;
        // y″ − y = 0  → C0·eˣ + C1·e⁻ˣ ; verify y″ − y = 0.
        let y = dsolve_homogeneous(&[ig(-1), ig(0), ig(1)], "x").expect("solvable");
        let ypp = y.differentiate("x").differentiate("x");
        assert_equal(&(ypp - y.clone()), &CasExpr::zero());
        // y″ − 3y′ + 2y = 0  (roots 1, 2)
        assert!(dsolve_homogeneous(&[ig(2), ig(-3), ig(1)], "x").is_some());
        // y″ + y = 0  → C0·cos x + C1·sin x (complex roots ±i); verify y″ + y = 0.
        let h = dsolve_homogeneous(&[ig(1), ig(0), ig(1)], "x").expect("solvable");
        let hpp = h.differentiate("x").differentiate("x");
        assert_equal(&(hpp + h.clone()), &CasExpr::zero());
    }

    #[test]
    fn solve_recurrence_closed_forms() {
        let ig = Rational::integer;
        // aₙ = 5aₙ₋₁ − 6aₙ₋₂, a₀=0, a₁=1 ⇒ aₙ = 3ⁿ − 2ⁿ. Certified inside; here we
        // independently verify it reproduces the sequence 0,1,5,19,65 by evalf.
        let closed = solve_recurrence(&[ig(5), ig(-6)], &[ig(0), ig(1)], "n").expect("solvable");
        let expected = [0.0, 1.0, 5.0, 19.0, 65.0];
        for (n, &want) in expected.iter().enumerate() {
            #[allow(clippy::cast_precision_loss)]
            let got = evalf(&closed, &[("n", n as f64)]).unwrap();
            assert!((got - want).abs() < 1e-9, "a_{n} = {got}, want {want}");
        }

        // aₙ = 3aₙ₋₁ − 2aₙ₋₂, a₀=2, a₁=3 ⇒ roots 1,2 ⇒ aₙ = 1 + 2ⁿ.
        let closed2 = solve_recurrence(&[ig(3), ig(-2)], &[ig(2), ig(3)], "n").expect("solvable");
        for (n, want) in [(0usize, 2.0), (1, 3.0), (2, 5.0), (3, 9.0)] {
            #[allow(clippy::cast_precision_loss)]
            let got = evalf(&closed2, &[("n", n as f64)]).unwrap();
            assert!((got - want).abs() < 1e-9);
        }

        // Golden-ratio family: aₙ = 3aₙ₋₁ − aₙ₋₂ has roots (3±√5)/2 = φ², ψ² (both
        // positive, irrational). With a₀=2, a₁=3 it is the Lucas-of-even-index
        // sequence 2,3,7,18,47,123. Certified over ℚ(√5); verify by evalf.
        let phi_sq =
            solve_recurrence(&[ig(3), ig(-1)], &[ig(2), ig(3)], "n").expect("golden family");
        for (n, want) in [(0usize, 2.0), (1, 3.0), (2, 7.0), (3, 18.0), (4, 47.0)] {
            #[allow(clippy::cast_precision_loss)]
            let got = evalf(&phi_sq, &[("n", n as f64)]).unwrap();
            assert!((got - want).abs() < 1e-6, "a_{n} = {got}, want {want}");
        }

        // Fibonacci: aₙ = aₙ₋₁ + aₙ₋₂, a₀=0, a₁=1 ⇒ Binet's formula (roots φ>0 and
        // ψ=(1−√5)/2 < 0, the negative root via cos(πn)·exp(n·ln|ψ|)). Certified over
        // ℚ(√5); verify it reproduces 0,1,1,2,3,5,8,13.
        let fib = solve_recurrence(&[ig(1), ig(1)], &[ig(0), ig(1)], "n").expect("Fibonacci");
        for (n, want) in [
            (0usize, 0.0),
            (1, 1.0),
            (2, 1.0),
            (3, 2.0),
            (4, 3.0),
            (5, 5.0),
            (6, 8.0),
            (7, 13.0),
        ] {
            #[allow(clippy::cast_precision_loss)]
            let got = evalf(&fib, &[("n", n as f64)]).unwrap();
            assert!((got - want).abs() < 1e-6, "F({n}) = {got}, want {want}");
        }
        // Lucas numbers: same recurrence, a₀=2, a₁=1 ⇒ 2,1,3,4,7,11,18.
        let lucas = solve_recurrence(&[ig(1), ig(1)], &[ig(2), ig(1)], "n").expect("Lucas");
        for (n, want) in [
            (0usize, 2.0),
            (1, 1.0),
            (2, 3.0),
            (3, 4.0),
            (4, 7.0),
            (5, 11.0),
        ] {
            #[allow(clippy::cast_precision_loss)]
            let got = evalf(&lucas, &[("n", n as f64)]).unwrap();
            assert!((got - want).abs() < 1e-6, "L({n}) = {got}, want {want}");
        }
    }

    #[test]
    fn dsolve_first_order_linear_integrating_factor() {
        let x = || v("x");
        // y′ + y = x  ⇒  certified; verify y′ + y = x independently.
        let sol = dsolve_first_order_linear(&CasExpr::int(1), &x(), "x").expect("solvable");
        assert_equal(&(sol.differentiate("x") + sol.clone()), &x());
        // y′ + 2y = x  (constant coefficient, polynomial forcing).
        let sol2 = dsolve_first_order_linear(&CasExpr::int(2), &x(), "x").expect("solvable");
        assert_equal(
            &(sol2.differentiate("x") + CasExpr::int(2) * sol2.clone()),
            &x(),
        );
        // y′ − y = x²  ⇒  residual y′ − y = x².
        let sol3 =
            dsolve_first_order_linear(&CasExpr::int(-1), &x().pow(2), "x").expect("solvable");
        assert_equal(&(sol3.differentiate("x") - sol3.clone()), &x().pow(2));
    }

    #[test]
    fn dsolve_separable_first_order() {
        let x = || v("x");
        let y = || v("y");
        // For the implicit solution S(x,y) = G(y) − F(x) − C0, verify the defining
        // antiderivative identities: ∂S/∂y = 1/g and −∂S/∂x = f, so along y′=f·g
        // the total derivative d/dx S = (1/g)·y′ − f = 0.
        let check = |f: CasExpr, g: CasExpr| {
            let s = dsolve_separable(&f, &g, "x", "y").expect("separable");
            // ∂S/∂y = 1/g(y).
            assert_equal(&s.differentiate("y"), &(CasExpr::int(1) / g.clone()));
            // ∂S/∂x = −f(x).
            assert_equal(&s.differentiate("x"), &(-f));
        };
        check(CasExpr::int(1), y()); // y′ = y → ln y − x − C0
        check(x(), y()); // y′ = xy
        check(x(), CasExpr::int(1) / y()); // y′ = x/y → y²/2 − x²/2 − C0
        check(CasExpr::int(1), y().pow(2)); // y′ = y²
    }

    #[test]
    fn dsolve_inhomogeneous_polynomial_forcing() {
        let ig = Rational::integer;
        let x = || v("x");
        // Each solution is certified inside the call; here we re-verify the ODE
        // residual against the forcing independently.
        // y′ + y = x  ⇒  y = (x − 1) + C0·e^(−x).
        let sol = dsolve_inhomogeneous(&[ig(1), ig(1)], &x(), "x").expect("solvable");
        let residual = sol.differentiate("x") + sol.clone();
        assert_equal(&residual, &x());

        // y″ − y = x²  ⇒  particular −x² − 2.
        let sol2 =
            dsolve_inhomogeneous(&[ig(-1), ig(0), ig(1)], &x().pow(2), "x").expect("solvable");
        let residual2 = sol2.differentiate("x").differentiate("x") - sol2.clone();
        assert_equal(&residual2, &x().pow(2));

        // Resonance: y′ = x (root 0), needs the xˢ factor ⇒ particular x²/2.
        let sol3 = dsolve_inhomogeneous(&[ig(0), ig(1)], &x(), "x").expect("solvable");
        assert_equal(&sol3.differentiate("x"), &x());

        // y″ − 3y′ + 2y = x (roots 1,2): particular (1/2)x + 3/4.
        let sol4 = dsolve_inhomogeneous(&[ig(2), ig(-3), ig(1)], &x(), "x").expect("solvable");
        let residual4 = sol4.differentiate("x").differentiate("x")
            - CasExpr::int(3) * sol4.differentiate("x")
            + CasExpr::int(2) * sol4.clone();
        assert_equal(&residual4, &x());
    }

    #[test]
    fn definite_summation() {
        let k = || v("k");
        let n = || v("n");
        // Σ_{k=1}^{n} k = n(n+1)/2.
        assert_equal(
            &definite_sum(&k(), "k", &CasExpr::int(1), &n()).unwrap(),
            &(CasExpr::rat(1, 2) * n() * (n() + CasExpr::int(1))),
        );
        // Σ_{k=1}^{n} k² = n(n+1)(2n+1)/6.
        assert_equal(
            &definite_sum(&k().pow(2), "k", &CasExpr::int(1), &n()).unwrap(),
            &(CasExpr::rat(1, 6)
                * n()
                * (n() + CasExpr::int(1))
                * (CasExpr::int(2) * n() + CasExpr::int(1))),
        );
        // Concrete bounds: Σ_{k=1}^{10} k = 55.
        assert_equal(
            &definite_sum(&k(), "k", &CasExpr::int(1), &CasExpr::int(10)).unwrap(),
            &CasExpr::int(55),
        );
        // Σ_{k=3}^{5} k² = 9+16+25 = 50.
        assert_equal(
            &definite_sum(&k().pow(2), "k", &CasExpr::int(3), &CasExpr::int(5)).unwrap(),
            &CasExpr::int(50),
        );
    }

    #[test]
    fn finite_products_over_concrete_bounds() {
        let k = || v("k");
        let x = || v("x");
        // ∏_{k=1}^{5} k = 120 = 5!.
        assert_equal(
            &finite_product(&k(), "k", &CasExpr::int(1), &CasExpr::int(5)).unwrap(),
            &CasExpr::int(120),
        );
        // ∏_{k=1}^{4} (2k−1) = 1·3·5·7 = 105.
        assert_equal(
            &finite_product(
                &(CasExpr::int(2) * k() - CasExpr::int(1)),
                "k",
                &CasExpr::int(1),
                &CasExpr::int(4),
            )
            .unwrap(),
            &CasExpr::int(105),
        );
        // ∏_{k=1}^{3} (x+k) = (x+1)(x+2)(x+3).
        assert_equal(
            &finite_product(&(x() + k()), "k", &CasExpr::int(1), &CasExpr::int(3)).unwrap(),
            &((x() + CasExpr::int(1)) * (x() + CasExpr::int(2)) * (x() + CasExpr::int(3))),
        );
        // Empty product (upper < lower) is 1.
        assert_equal(
            &finite_product(&k(), "k", &CasExpr::int(3), &CasExpr::int(1)).unwrap(),
            &CasExpr::int(1),
        );
        // Non-integer bound is declined.
        assert!(finite_product(&k(), "k", &CasExpr::rat(1, 2), &CasExpr::int(3)).is_none());
    }

    #[test]
    fn bernoulli_polynomials_and_their_defining_identity() {
        let x = || v("x");
        // Known low-order values.
        assert_equal(&bernoulli_polynomial(0, "x").unwrap(), &CasExpr::int(1));
        assert_equal(
            &bernoulli_polynomial(1, "x").unwrap(),
            &(x() - CasExpr::rat(1, 2)),
        );
        assert_equal(
            &bernoulli_polynomial(2, "x").unwrap(),
            &(x().pow(2) - x() + CasExpr::rat(1, 6)),
        );
        // Defining identities: Bₙ′(x) = n·Bₙ₋₁(x), and Bₙ(x+1) − Bₙ(x) = n·x^{n−1}.
        for n in 1..=6u32 {
            let bn = bernoulli_polynomial(n, "x").unwrap();
            let bn_prev = bernoulli_polynomial(n - 1, "x").unwrap();
            assert_equal(&bn.differentiate("x"), &(CasExpr::int(i128::from(n)) * bn_prev));
            let shifted = bn.substitute("x", &(x() + CasExpr::int(1)));
            let power = if n == 1 {
                CasExpr::int(1)
            } else {
                x().pow(n - 1)
            };
            assert_equal(&(shifted - bn), &(CasExpr::int(i128::from(n)) * power));
        }
    }

    #[test]
    fn euler_polynomials_and_their_defining_identity() {
        let x = || v("x");
        assert_equal(&euler_polynomial(0, "x").unwrap(), &CasExpr::int(1));
        assert_equal(
            &euler_polynomial(2, "x").unwrap(),
            &(x().pow(2) - x()),
        );
        assert_equal(
            &euler_polynomial(3, "x").unwrap(),
            &(x().pow(3) - CasExpr::rat(3, 2) * x().pow(2) + CasExpr::rat(1, 4)),
        );
        // Eₙ′(x) = n·Eₙ₋₁(x) and Eₙ(x+1) + Eₙ(x) = 2xⁿ.
        for n in 1..=6u32 {
            let en = euler_polynomial(n, "x").unwrap();
            let en_prev = euler_polynomial(n - 1, "x").unwrap();
            assert_equal(&en.differentiate("x"), &(CasExpr::int(i128::from(n)) * en_prev));
            let shifted = en.substitute("x", &(x() + CasExpr::int(1)));
            assert_equal(&(shifted + en), &(CasExpr::int(2) * x().pow(n)));
        }
    }

    #[test]
    fn summation_closed_forms() {
        let n = || v("n");
        // ∑_{k=0}^{n−1} 1 = n
        assert_equal(&sum_polynomial(&CasExpr::int(1), "n").unwrap(), &n());
        // ∑_{k=0}^{n−1} k = (n²−n)/2
        assert_equal(
            &sum_polynomial(&n(), "n").unwrap(),
            &(CasExpr::rat(1, 2) * n().pow(2) - CasExpr::rat(1, 2) * n()),
        );
        // ∑_{k=0}^{n−1} k² = (2n³−3n²+n)/6  — the certificate proves it regardless.
        let s2 = sum_polynomial(&n().pow(2), "n").unwrap();
        // spot-check at n=3: 0+1+4 = 5
        let mut env = BTreeMap::new();
        env.insert("n".to_owned(), Rational::integer(3));
        assert_eq!(s2.eval(&env), Some(Rational::integer(5)));
    }

    #[test]
    fn apart_partial_fractions() {
        let x = || v("x");
        // 1/(x²−1) = ½/(x−1) − ½/(x+1)
        let f = CasExpr::int(1) / (x().pow(2) - CasExpr::int(1));
        assert_equal(&apart(&f, "x").expect("distinct linear factors"), &f);
        // x/((x−1)(x−2)) = −1/(x−1) + 2/(x−2)
        let g = x() / ((x() - CasExpr::int(1)) * (x() - CasExpr::int(2)));
        assert_equal(&apart(&g, "x").expect("distinct linear factors"), &g);
        // Repeated factor: x/(x−1)² = 1/(x−1) + 1/(x−1)² — each certified equal.
        let repeated = x() / (x() - CasExpr::int(1)).pow(2);
        assert_equal(
            &apart(&repeated, "x").expect("repeated linear factor"),
            &repeated,
        );
        // Mixed distinct + repeated: 1/((x−1)(x−2)²).
        let mixed = CasExpr::int(1) / ((x() - CasExpr::int(1)) * (x() - CasExpr::int(2)).pow(2));
        assert_equal(&apart(&mixed, "x").expect("mixed factors"), &mixed);
        // Improper (numerator degree ≥ denominator): (x³)/(x−1)² has a polynomial part.
        let improper = x().pow(3) / (x() - CasExpr::int(1)).pow(2);
        assert_equal(&apart(&improper, "x").expect("improper"), &improper);
        // Irreducible quadratic factor: 1/(x²+1) is already partial → itself.
        let irr = CasExpr::int(1) / (x().pow(2) + CasExpr::int(1));
        assert_equal(&apart(&irr, "x").expect("irreducible quadratic"), &irr);
        // Mixed linear + irreducible quadratic: x/((x−1)(x²+1)).
        let mixed_q = x() / ((x() - CasExpr::int(1)) * (x().pow(2) + CasExpr::int(1)));
        assert_equal(&apart(&mixed_q, "x").expect("linear + quadratic"), &mixed_q);
        // Repeated irreducible quadratic: 1/(x²+1)².
        let rep_q = CasExpr::int(1) / (x().pow(2) + CasExpr::int(1)).pow(2);
        assert_equal(&apart(&rep_q, "x").expect("repeated quadratic"), &rep_q);
    }

    #[test]
    fn residues_of_rational_functions() {
        let x = || v("x");
        let ig = Rational::integer;
        // 1/((x−1)(x−2)): Res₁ = −1, Res₂ = +1, Res₃ = 0 (not a pole).
        let f = CasExpr::int(1) / ((x() - CasExpr::int(1)) * (x() - CasExpr::int(2)));
        assert_equal(&residue(&f, "x", ig(1)).unwrap(), &CasExpr::int(-1));
        assert_equal(&residue(&f, "x", ig(2)).unwrap(), &CasExpr::int(1));
        assert_equal(&residue(&f, "x", ig(3)).unwrap(), &CasExpr::zero());
        // x/(x−1)² (double pole): Res₁ = 1 (the 1/(x−1) coefficient).
        let g = x() / (x() - CasExpr::int(1)).pow(2);
        assert_equal(&residue(&g, "x", ig(1)).unwrap(), &CasExpr::int(1));
        // 1/(x−1)² has residue 0 at 1 (purely a double-pole term).
        assert_equal(
            &residue(
                &(CasExpr::int(1) / (x() - CasExpr::int(1)).pow(2)),
                "x",
                ig(1),
            )
            .unwrap(),
            &CasExpr::zero(),
        );
        // (x²+1)/((x−2)(x−3)): Res₂ = (4+1)/(2−3) = −5, Res₃ = (9+1)/(3−2) = 10.
        let h =
            (x().pow(2) + CasExpr::int(1)) / ((x() - CasExpr::int(2)) * (x() - CasExpr::int(3)));
        assert_equal(&residue(&h, "x", ig(2)).unwrap(), &CasExpr::int(-5));
        assert_equal(&residue(&h, "x", ig(3)).unwrap(), &CasExpr::int(10));
    }

    #[test]
    fn simplify_picks_smaller_equal_form() {
        let x = || v("x");
        // (x²−1)/(x−1) simplifies to x+1, and stays value-equal.
        let f = (x().pow(2) - CasExpr::int(1)) / (x() - CasExpr::int(1));
        let s = simplify(&f);
        assert_equal(&s, &(x() + CasExpr::int(1)));
        assert_equal(&s, &f);
    }

    #[test]
    fn laplace_transforms() {
        let t = || v("t");
        let s = || v("s");
        let holds = |f: CasExpr, expected: CasExpr| {
            assert_equal(&laplace_transform(&f, "t", "s").unwrap(), &expected);
        };
        // L{1} = 1/s, L{t} = 1/s², L{t²} = 2/s³.
        holds(CasExpr::int(1), CasExpr::int(1) / s());
        holds(t(), CasExpr::int(1) / s().pow(2));
        holds(t().pow(2), CasExpr::int(2) / s().pow(3));
        // L{e^{3t}} = 1/(s−3).
        holds(
            (CasExpr::int(3) * t()).exp(),
            CasExpr::int(1) / (s() - CasExpr::int(3)),
        );
        // L{sin(2t)} = 2/(s²+4); L{cos(2t)} = s/(s²+4).
        holds(
            (CasExpr::int(2) * t()).sin(),
            CasExpr::int(2) / (s().pow(2) + CasExpr::int(4)),
        );
        holds(
            (CasExpr::int(2) * t()).cos(),
            s() / (s().pow(2) + CasExpr::int(4)),
        );
        // L{t·e^{2t}} = 1/(s−2)² (frequency-shift via differentiation).
        holds(
            t() * (CasExpr::int(2) * t()).exp(),
            CasExpr::int(1) / (s() - CasExpr::int(2)).pow(2),
        );
        // Linearity: L{3t + 2e^{t}} = 3/s² + 2/(s−1).
        holds(
            CasExpr::int(3) * t() + CasExpr::int(2) * t().exp(),
            CasExpr::int(3) / s().pow(2) + CasExpr::int(2) / (s() - CasExpr::int(1)),
        );
        // Inverse Laplace (simple real poles), certified by the L round-trip.
        // L⁻¹{1/(s−2)} = e^{2t}.
        assert_equal(
            &inverse_laplace(&(CasExpr::int(1) / (s() - CasExpr::int(2))), "s", "t").unwrap(),
            &(CasExpr::int(2) * t()).exp(),
        );
        // L⁻¹{1/((s−1)(s−2))} = −e^t + e^{2t}.
        assert_equal(
            &inverse_laplace(
                &(CasExpr::int(1) / ((s() - CasExpr::int(1)) * (s() - CasExpr::int(2)))),
                "s",
                "t",
            )
            .unwrap(),
            &(-t().exp() + (CasExpr::int(2) * t()).exp()),
        );
    }

    #[test]
    fn z_transforms_round_trip() {
        let n = || v("n");
        let z = || v("z");
        // Forward: Z{aⁿ} = z/(z−a); Z{1} = z/(z−1); linearity.
        assert_equal(
            &z_transform(&geometric_power(Rational::integer(2), "n"), "n", "z").unwrap(),
            &(z() / (z() - CasExpr::int(2))),
        );
        assert_equal(
            &z_transform(&CasExpr::int(1), "n", "z").unwrap(),
            &(z() / (z() - CasExpr::int(1))),
        );
        // Inverse (simple rational poles > 0), certified by the Z round-trip.
        let x = z() / (z() - CasExpr::int(2));
        let signal = inverse_z_transform(&x, "z", "n").unwrap();
        assert_equal(&signal, &geometric_power(Rational::integer(2), "n")); // 2ⁿ
        // Two poles: Z⁻¹{z/((z−2)(z−3))} = −2ⁿ + 3ⁿ, round-trip recovers X(z).
        let two_pole = z() / ((z() - CasExpr::int(2)) * (z() - CasExpr::int(3)));
        let sig2 = inverse_z_transform(&two_pole, "z", "n").unwrap();
        assert_equal(&z_transform(&sig2, "n", "z").unwrap(), &two_pole);
        // A non-positive pole (z/(z+1)) is declined (aⁿ needs a > 0).
        assert!(inverse_z_transform(&(z() / (z() + CasExpr::int(1))), "z", "n").is_none());
        let _ = n;
    }

    #[test]
    fn series_reversion_inverts() {
        let x = || v("x");
        // reversion(sin x) = arcsin series = x + x³/6 + 3x⁵/40 + …
        let arcsin = series_reversion(&x().sin(), "x", 5).unwrap();
        assert_equal(
            &arcsin,
            &(x() + CasExpr::rat(1, 6) * x().pow(3) + CasExpr::rat(3, 40) * x().pow(5)),
        );
        // reversion(eˣ − 1) = ln(1+x) series = x − x²/2 + x³/3 − x⁴/4.
        let log1p = series_reversion(&(x().exp() - CasExpr::int(1)), "x", 4).unwrap();
        assert_equal(
            &log1p,
            &(x() - CasExpr::rat(1, 2) * x().pow(2) + CasExpr::rat(1, 3) * x().pow(3)
                - CasExpr::rat(1, 4) * x().pow(4)),
        );
        // Reversion is a genuine inverse: composing f(g(x)) recovers x to the order.
        // Verify for f = x + x²: f(reversion(f)) ≡ x mod x⁵.
        let f = x() + x().pow(2);
        let g = series_reversion(&f, "x", 4).unwrap();
        let composed = series(&f.substitute("x", &g), "x", 4).unwrap();
        assert_equal(&composed, &x());
    }

    #[test]
    fn laurent_series_with_principal_part() {
        let x = || v("x");
        // 1/(x(1−x)) = 1/x + 1 + x + x².
        let f = CasExpr::int(1) / (x() * (CasExpr::int(1) - x()));
        assert_equal(
            &laurent_series(&f, "x", 2).unwrap(),
            &(CasExpr::int(1) / x() + CasExpr::int(1) + x() + x().pow(2)),
        );
        // 1/x² is its own Laurent series.
        assert_equal(
            &laurent_series(&(CasExpr::int(1) / x().pow(2)), "x", 1).unwrap(),
            &(CasExpr::int(1) / x().pow(2)),
        );
        // (x+1)/x = 1/x + 1.
        assert_equal(
            &laurent_series(&((x() + CasExpr::int(1)) / x()), "x", 0).unwrap(),
            &(CasExpr::int(1) / x() + CasExpr::int(1)),
        );
        // The x⁻¹ coefficient is the residue at 0: for 1/(x(1−x)) it is 1.
        assert_equal(
            &residue(&f, "x", Rational::zero()).unwrap(),
            &CasExpr::int(1),
        );
        // An analytic function's Laurent series is its Taylor series (no principal
        // part): 1/(1−x) = 1 + x + x².
        assert_equal(
            &laurent_series(&(CasExpr::int(1) / (CasExpr::int(1) - x())), "x", 2).unwrap(),
            &(CasExpr::int(1) + x() + x().pow(2)),
        );
    }

    #[test]
    fn transcendental_limits_via_series() {
        let x = || v("x");
        let at0 = LimitPoint::Finite(Rational::zero());
        // lim_{x→0} sin(x)/x = 1.
        assert_equal(
            &limit(&(x().sin() / x()), "x", at0).unwrap(),
            &CasExpr::int(1),
        );
        // lim_{x→0} (1 − cos x)/x² = 1/2.
        assert_equal(
            &limit(&((CasExpr::int(1) - x().cos()) / x().pow(2)), "x", at0).unwrap(),
            &CasExpr::rat(1, 2),
        );
        // lim_{x→0} (eˣ − 1)/x = 1.
        assert_equal(
            &limit(&((x().exp() - CasExpr::int(1)) / x()), "x", at0).unwrap(),
            &CasExpr::int(1),
        );
        // lim_{x→0} sin(3x)/x = 3.
        assert_equal(
            &limit(&((CasExpr::int(3) * x()).sin() / x()), "x", at0).unwrap(),
            &CasExpr::int(3),
        );
        // Analytic point: lim_{x→0} cos(x) = 1; lim_{x→0} (sin x + 2) = 2.
        assert_equal(&limit(&x().cos(), "x", at0).unwrap(), &CasExpr::int(1));
        assert_equal(
            &limit(&(x().sin() + CasExpr::int(2)), "x", at0).unwrap(),
            &CasExpr::int(2),
        );
        // Shifted point: lim_{x→1} sin(x−1)/(x−1) = 1.
        assert_equal(
            &limit(
                &((x() - CasExpr::int(1)).sin() / (x() - CasExpr::int(1))),
                "x",
                LimitPoint::Finite(Rational::integer(1)),
            )
            .unwrap(),
            &CasExpr::int(1),
        );
        // A genuine pole (no cancellation): lim_{x→0} cos(x)/x is infinite → None.
        assert!(limit(&(x().cos() / x()), "x", at0).is_none());
    }

    #[test]
    fn limits_of_rational_functions() {
        let x = || v("x");
        let at = |n: i128| LimitPoint::Finite(Rational::integer(n));
        // continuous: lim_{x→1} (x+1)/(x−2) = −2
        assert_equal(
            &limit(
                &((x() + CasExpr::int(1)) / (x() - CasExpr::int(2))),
                "x",
                at(1),
            )
            .unwrap(),
            &CasExpr::int(-2),
        );
        // 0/0 via cancellation: lim_{x→2} (x²−4)/(x−2) = 4
        assert_equal(
            &limit(
                &((x().pow(2) - CasExpr::int(4)) / (x() - CasExpr::int(2))),
                "x",
                at(2),
            )
            .unwrap(),
            &CasExpr::int(4),
        );
        // lim_{x→0} (x²+3x)/x = 3
        assert_equal(
            &limit(&((x().pow(2) + CasExpr::int(3) * x()) / x()), "x", at(0)).unwrap(),
            &CasExpr::int(3),
        );
        // at infinity: lim (2x²+1)/(x²+x) = 2 ; lim (x+1)/(x²+1) = 0
        assert_equal(
            &limit(
                &((CasExpr::int(2) * x().pow(2) + CasExpr::int(1)) / (x().pow(2) + x())),
                "x",
                LimitPoint::PosInfinity,
            )
            .unwrap(),
            &CasExpr::int(2),
        );
        assert_equal(
            &limit(
                &((x() + CasExpr::int(1)) / (x().pow(2) + CasExpr::int(1))),
                "x",
                LimitPoint::PosInfinity,
            )
            .unwrap(),
            &CasExpr::zero(),
        );
        // pole: lim_{x→2} 1/(x−2) has no finite limit
        assert!(limit(&(CasExpr::int(1) / (x() - CasExpr::int(2))), "x", at(2)).is_none());
    }

    #[test]
    fn limits_with_exponential_dominance() {
        let x = || v("x");
        // Exp beats any polynomial: x²/eˣ → 0, x⁵·e^{−x} → 0, (x²+1)/e^{2x} → 0.
        assert_equal(
            &limit(&(x().pow(2) / x().exp()), "x", LimitPoint::PosInfinity).unwrap(),
            &CasExpr::zero(),
        );
        assert_equal(
            &limit(
                &(x().pow(5) * (CasExpr::int(-1) * x()).exp()),
                "x",
                LimitPoint::PosInfinity,
            )
            .unwrap(),
            &CasExpr::zero(),
        );
        // eˣ → 0 as x → −∞; x·eˣ → 0 as x → −∞.
        assert_equal(
            &limit(&x().exp(), "x", LimitPoint::NegInfinity).unwrap(),
            &CasExpr::zero(),
        );
        assert_equal(
            &limit(&(x() * x().exp()), "x", LimitPoint::NegInfinity).unwrap(),
            &CasExpr::zero(),
        );
        // Growth diverges (no finite limit): eˣ/x → +∞.
        assert!(limit(&(x().exp() / x()), "x", LimitPoint::PosInfinity).is_none());
    }

    #[test]
    fn characteristic_polynomial_and_eigenvalues() {
        // diag(2,3): char poly (2−λ)(3−λ) = λ²−5λ+6, eigenvalues {2,3}
        let m = Matrix::from_rows(vec![
            vec![CasExpr::int(2), CasExpr::zero()],
            vec![CasExpr::zero(), CasExpr::int(3)],
        ])
        .unwrap();
        let cp = characteristic_polynomial(&m, "L").unwrap();
        assert_equal(
            &cp,
            &(v("L").pow(2) - CasExpr::int(5) * v("L") + CasExpr::int(6)),
        );
        assert_equal(&trace(&m).unwrap(), &CasExpr::int(5)); // 2 + 3
        assert_eq!(matrix_rank(&m), Some(2));
        // rank-deficient [[1,2],[2,4]] has rank 1
        let dep = Matrix::from_rows(vec![
            vec![CasExpr::int(1), CasExpr::int(2)],
            vec![CasExpr::int(2), CasExpr::int(4)],
        ])
        .unwrap();
        assert_eq!(matrix_rank(&dep), Some(1));
        let eig = eigenvalues(&m, "L").unwrap();
        assert_eq!(eig.len(), 2);
        for e in &eig {
            assert_equal(&cp.substitute("L", e), &CasExpr::zero());
        }
        // rotation [[0,-1],[1,0]]: char poly λ²+1, eigenvalues ±I
        let rot = Matrix::from_rows(vec![
            vec![CasExpr::zero(), CasExpr::int(-1)],
            vec![CasExpr::int(1), CasExpr::zero()],
        ])
        .unwrap();
        assert_equal(
            &characteristic_polynomial(&rot, "L").unwrap(),
            &(v("L").pow(2) + CasExpr::int(1)),
        );
        assert_eq!(eigenvalues(&rot, "L").unwrap().len(), 2);
    }

    #[test]
    fn diagonalization_certifies() {
        // [[1,1],[0,2]]: eigenvalues 1,2 (distinct → diagonalizable). A = P·D·P⁻¹.
        let a = Matrix::from_rows(vec![
            vec![CasExpr::int(1), CasExpr::int(1)],
            vec![CasExpr::zero(), CasExpr::int(2)],
        ])
        .unwrap();
        let (p, d) = diagonalize(&a, "L").unwrap();
        // D is diagonal; A·P = P·D (the certificate, re-checked here).
        assert!(d.is_diagonal());
        let left = a.mul(&p).unwrap();
        let right = p.mul(&d).unwrap();
        for i in 0..2 {
            for j in 0..2 {
                assert_equal(left.get(i, j).unwrap(), right.get(i, j).unwrap());
            }
        }
        // A defective matrix ([[3,1],[0,3]], repeated eigenvalue, 1-D eigenspace) is
        // NOT diagonalizable over ℚ → None.
        let defective = Matrix::from_rows(vec![
            vec![CasExpr::int(3), CasExpr::int(1)],
            vec![CasExpr::zero(), CasExpr::int(3)],
        ])
        .unwrap();
        assert!(diagonalize(&defective, "L").is_none());
    }

    #[test]
    fn eigenvectors_certify_a_v_equals_lambda_v() {
        // [[2,0],[0,3]]: eigenvalue 2 → e₁, eigenvalue 3 → e₂.
        let m = Matrix::from_rows(vec![
            vec![CasExpr::int(2), CasExpr::zero()],
            vec![CasExpr::zero(), CasExpr::int(3)],
        ])
        .unwrap();
        let pairs = eigenvectors(&m, "L").unwrap();
        assert_eq!(pairs.len(), 2);
        for (lambda, basis) in &pairs {
            assert_eq!(basis.len(), 1); // each eigenspace is 1-dimensional
            for v in basis {
                // Certificate: A·v = λ·v.
                let av = m.mul(v).unwrap();
                let scaled = Matrix::from_rows(
                    (0..v.rows())
                        .map(|i| vec![lambda.clone() * v.get(i, 0).unwrap().clone()])
                        .collect(),
                )
                .unwrap();
                for i in 0..v.rows() {
                    assert_equal(av.get(i, 0).unwrap(), scaled.get(i, 0).unwrap());
                }
            }
        }
    }

    #[test]
    fn eigenvectors_of_a_shear_and_a_repeated_eigenvalue() {
        // [[3,1],[0,3]]: eigenvalue 3 (double), but only a 1-D eigenspace (defective).
        let shear = Matrix::from_rows(vec![
            vec![CasExpr::int(3), CasExpr::int(1)],
            vec![CasExpr::zero(), CasExpr::int(3)],
        ])
        .unwrap();
        let pairs = eigenvectors(&shear, "L").unwrap();
        assert_eq!(pairs.len(), 1); // 3 appears once after dedup
        let (lambda, basis) = &pairs[0];
        assert_equal(lambda, &CasExpr::int(3));
        assert_eq!(basis.len(), 1); // geometric multiplicity 1 (defective)
        // The eigenvector is (1,0): A·v = 3·v.
        let v = &basis[0];
        let av = shear.mul(v).unwrap();
        for i in 0..v.rows() {
            assert_equal(
                av.get(i, 0).unwrap(),
                &(CasExpr::int(3) * v.get(i, 0).unwrap().clone()),
            );
        }
    }

    #[test]
    fn jordan_form_of_defective_and_diagonalizable_matrices() {
        let int_matrix =
            |rows: &[&[i128]]| Matrix::from_rows(
                rows.iter()
                    .map(|r| r.iter().map(|&x| CasExpr::int(x)).collect())
                    .collect(),
            )
            .unwrap();
        // Every case is validated by the defining similarity A·P = P·J.
        let check = |a: &Matrix, expect_super: &[(usize, usize)]| {
            let (p, j) = jordan_form(a, "L").expect("rational spectrum");
            let n = a.rows();
            let ap = a.mul(&p).unwrap();
            let pj = p.mul(&j).unwrap();
            for i in 0..n {
                for c in 0..n {
                    assert_equal(ap.get(i, c).unwrap(), pj.get(i, c).unwrap());
                }
            }
            // The expected super-diagonal 1s (Jordan block couplings).
            for &(i, jc) in expect_super {
                assert_equal(j.get(i, jc).unwrap(), &CasExpr::int(1));
            }
        };
        // Defective shear: one 2×2 block (super-diagonal 1 at (0,1)).
        check(&int_matrix(&[&[3, 1], &[0, 3]]), &[(0, 1)]);
        // Diagonalizable: no super-diagonal 1s.
        check(&int_matrix(&[&[2, 0], &[0, 3]]), &[]);
        // 3×3 single Jordan block (super-diagonal 1s at (0,1),(1,2)).
        check(&int_matrix(&[&[2, 1, 0], &[0, 2, 1], &[0, 0, 2]]), &[(0, 1), (1, 2)]);
        // Defective with two 2×2 blocks for eigenvalue 2.
        check(
            &int_matrix(&[&[2, 1, 0, 0], &[0, 2, 0, 0], &[0, 0, 2, 1], &[0, 0, 0, 2]]),
            &[(0, 1), (2, 3)],
        );
        // An irrational-spectrum matrix ([[0,1],[-1,0]], eigenvalues ±i) is declined.
        assert!(jordan_form(&int_matrix(&[&[0, 1], &[-1, 0]]), "L").is_none());
    }

    #[test]
    fn matrix_exp_solves_the_defining_ivp() {
        let t = || v("t");
        // A companion-like matrix [[0,1],[-2,-3]] (eigenvalues -1, -2).
        let a = Matrix::from_rows(vec![
            vec![CasExpr::int(0), CasExpr::int(1)],
            vec![CasExpr::int(-2), CasExpr::int(-3)],
        ])
        .unwrap();
        let m = matrix_exp(&a, "t").expect("diagonalizable → matrix exp");
        // M(0) = I and d/dt M = A·M (the values `matrix_exp` certifies internally).
        let am = a.mul(&m).unwrap();
        for i in 0..2 {
            for j in 0..2 {
                let entry = m.get(i, j).unwrap();
                let at_zero = entry.substitute("t", &CasExpr::zero());
                let expected0 = if i == j { CasExpr::int(1) } else { CasExpr::int(0) };
                assert_equal(&at_zero, &expected0);
                assert_equal(&entry.differentiate("t"), am.get(i, j).unwrap());
            }
        }
        // M(0,0) = 2e^{-t} − e^{-2t}.
        let expected00 = CasExpr::int(2) * (-t()).exp() - (CasExpr::int(-2) * t()).exp();
        assert_equal(m.get(0, 0).unwrap(), &expected00);
        // A DEFECTIVE matrix is now handled via Jordan form: exp([[2,1],[0,2]]·t)
        // = e^{2t}·[[1, t],[0, 1]].
        let shear = Matrix::from_rows(vec![
            vec![CasExpr::int(2), CasExpr::int(1)],
            vec![CasExpr::zero(), CasExpr::int(2)],
        ])
        .unwrap();
        let se = matrix_exp(&shear, "t").expect("defective handled via Jordan");
        let e2t = (CasExpr::int(2) * t()).exp();
        assert_equal(se.get(0, 0).unwrap(), &e2t);
        assert_equal(se.get(0, 1).unwrap(), &(t() * e2t.clone()));
        assert_equal(se.get(1, 0).unwrap(), &CasExpr::zero());
        assert_equal(se.get(1, 1).unwrap(), &e2t);
        // A complex-eigenvalue matrix ([[0,1],[-1,0]], eigenvalues ±i) is declined.
        let rotation = Matrix::from_rows(vec![
            vec![CasExpr::int(0), CasExpr::int(1)],
            vec![CasExpr::int(-1), CasExpr::int(0)],
        ])
        .unwrap();
        assert!(matrix_exp(&rotation, "t").is_none());
    }

    #[test]
    fn linear_ode_system_satisfies_ivp() {
        // x′ = [[0,1],[-2,-3]]·x, x(0) = (1, 0). Solution x(t) with x′ = A·x.
        let a = Matrix::from_rows(vec![
            vec![CasExpr::int(0), CasExpr::int(1)],
            vec![CasExpr::int(-2), CasExpr::int(-3)],
        ])
        .unwrap();
        let x0 = Matrix::from_rows(vec![vec![CasExpr::int(1)], vec![CasExpr::int(0)]]).unwrap();
        let x = linear_ode_system(&a, &x0, "t").expect("diagonalizable system");
        // x(0) = x0.
        for i in 0..2 {
            let at_zero = x.get(i, 0).unwrap().substitute("t", &CasExpr::zero());
            assert_equal(&at_zero, x0.get(i, 0).unwrap());
        }
        // x′(t) = A·x(t) componentwise.
        let ax = a.mul(&x).unwrap();
        for i in 0..2 {
            assert_equal(&x.get(i, 0).unwrap().differentiate("t"), ax.get(i, 0).unwrap());
        }
        // Wrong-shaped initial condition is declined.
        let bad = Matrix::from_rows(vec![vec![CasExpr::int(1)]]).unwrap();
        assert!(linear_ode_system(&a, &bad, "t").is_none());
    }

    #[test]
    fn bareiss_determinant_matches_cofactor() {
        // A 4×4 integer matrix — Bareiss (O(n³)) must agree with cofactor expansion.
        let m = Matrix::from_rows(vec![
            vec![
                CasExpr::int(2),
                CasExpr::int(1),
                CasExpr::int(0),
                CasExpr::int(3),
            ],
            vec![
                CasExpr::int(1),
                CasExpr::int(4),
                CasExpr::int(2),
                CasExpr::int(1),
            ],
            vec![
                CasExpr::int(0),
                CasExpr::int(2),
                CasExpr::int(5),
                CasExpr::int(1),
            ],
            vec![
                CasExpr::int(3),
                CasExpr::int(1),
                CasExpr::int(1),
                CasExpr::int(6),
            ],
        ])
        .unwrap();
        assert_equal(&m.bareiss_determinant().unwrap(), &m.determinant().unwrap());
        // A matrix needing a pivot swap (zero at (0,0)).
        let swap = Matrix::from_rows(vec![
            vec![CasExpr::zero(), CasExpr::int(2)],
            vec![CasExpr::int(3), CasExpr::int(4)],
        ])
        .unwrap();
        assert_equal(&swap.bareiss_determinant().unwrap(), &CasExpr::int(-6)); // 0·4 − 2·3
        // Singular matrix → 0.
        let singular = Matrix::from_rows(vec![
            vec![CasExpr::int(1), CasExpr::int(2)],
            vec![CasExpr::int(2), CasExpr::int(4)],
        ])
        .unwrap();
        assert_equal(&singular.bareiss_determinant().unwrap(), &CasExpr::zero());
    }

    #[test]
    fn hadamard_and_kronecker_products() {
        let a = Matrix::from_rows(vec![
            vec![CasExpr::int(1), CasExpr::int(2)],
            vec![CasExpr::int(3), CasExpr::int(4)],
        ])
        .unwrap();
        let b = Matrix::from_rows(vec![
            vec![CasExpr::int(0), CasExpr::int(5)],
            vec![CasExpr::int(6), CasExpr::int(7)],
        ])
        .unwrap();
        // Hadamard: entrywise [[0,10],[18,28]].
        let had = a.hadamard(&b).unwrap();
        assert_equal(had.get(0, 1).unwrap(), &CasExpr::int(10));
        assert_equal(had.get(1, 0).unwrap(), &CasExpr::int(18));
        // Kronecker: 4×4, top-left block = a[0][0]·b = b, so (0,1) entry = 5.
        let kron = a.kronecker(&b);
        assert_eq!((kron.rows(), kron.cols()), (4, 4));
        assert_equal(kron.get(0, 1).unwrap(), &CasExpr::int(5));
        // (2,3) entry = a[1][1]·b[0][1] = 4·5 = 20.
        assert_equal(kron.get(2, 3).unwrap(), &CasExpr::int(20));
    }

    #[test]
    fn adjugate_power_and_symmetry() {
        let m = Matrix::from_rows(vec![
            vec![CasExpr::int(1), CasExpr::int(2)],
            vec![CasExpr::int(3), CasExpr::int(4)],
        ])
        .unwrap();
        // Adjugate certificate: M·adj(M) = det(M)·I. det = −2.
        let adj = m.adjugate().unwrap();
        let product = m.mul(&adj).unwrap();
        let det = m.determinant().unwrap();
        for i in 0..2 {
            for j in 0..2 {
                let expected = if i == j { det.clone() } else { CasExpr::zero() };
                assert_equal(product.get(i, j).unwrap(), &expected);
            }
        }
        // M² = [[7,10],[15,22]].
        let square = m.pow(2).unwrap();
        assert_equal(square.get(0, 0).unwrap(), &CasExpr::int(7));
        assert_equal(square.get(1, 1).unwrap(), &CasExpr::int(22));
        // M⁰ = I.
        assert_equal(m.pow(0).unwrap().get(0, 0).unwrap(), &CasExpr::int(1));
        assert_equal(m.pow(0).unwrap().get(0, 1).unwrap(), &CasExpr::zero());
        // Symmetry predicate.
        assert!(!m.is_symmetric());
        let sym = Matrix::from_rows(vec![
            vec![CasExpr::int(1), CasExpr::int(2)],
            vec![CasExpr::int(2), CasExpr::int(5)],
        ])
        .unwrap();
        assert!(sym.is_symmetric());
    }

    #[test]
    fn lu_decomposition_reconstructs() {
        // A matrix needing a pivot swap (zero in the (0,0) position).
        let a = Matrix::from_rows(vec![
            vec![CasExpr::zero(), CasExpr::int(2), CasExpr::int(1)],
            vec![CasExpr::int(1), CasExpr::int(1), CasExpr::int(1)],
            vec![CasExpr::int(2), CasExpr::int(1), CasExpr::int(3)],
        ])
        .unwrap();
        let (p, l, u) = a.lu().expect("invertible");
        // Certificate: P·A = L·U.
        let left = p.mul(&a).unwrap();
        let right = l.mul(&u).unwrap();
        for i in 0..3 {
            for j in 0..3 {
                assert_equal(left.get(i, j).unwrap(), right.get(i, j).unwrap());
                // L is unit-lower-triangular; U is upper-triangular.
                match i.cmp(&j) {
                    std::cmp::Ordering::Less => {
                        assert_equal(l.get(i, j).unwrap(), &CasExpr::zero());
                    }
                    std::cmp::Ordering::Greater => {
                        assert_equal(u.get(i, j).unwrap(), &CasExpr::zero());
                    }
                    std::cmp::Ordering::Equal => {
                        assert_equal(l.get(i, i).unwrap(), &CasExpr::int(1));
                    }
                }
            }
        }
    }

    #[test]
    fn null_space_basis_is_certified() {
        // [[1,2],[2,4]] has null space spanned by (−2,1): A·(−2,1)ᵀ = 0.
        let m = Matrix::from_rows(vec![
            vec![CasExpr::int(1), CasExpr::int(2)],
            vec![CasExpr::int(2), CasExpr::int(4)],
        ])
        .unwrap();
        let basis = null_space(&m).unwrap();
        assert_eq!(basis.len(), 1); // nullity = 2 − rank(1)
        for v in &basis {
            let product = m.mul(v).unwrap();
            for i in 0..product.rows() {
                assert_equal(product.get(i, 0).unwrap(), &CasExpr::zero());
            }
        }
        // Full-rank matrix → trivial null space.
        let full = Matrix::from_rows(vec![
            vec![CasExpr::int(1), CasExpr::zero()],
            vec![CasExpr::zero(), CasExpr::int(1)],
        ])
        .unwrap();
        assert!(null_space(&full).unwrap().is_empty());
    }

    #[test]
    fn minimal_polynomial_annihilates_the_matrix() {
        // diag(2,3): minimal poly = (x−2)(x−3) = x²−5x+6 (distinct eigenvalues).
        let m = Matrix::from_rows(vec![
            vec![CasExpr::int(2), CasExpr::zero()],
            vec![CasExpr::zero(), CasExpr::int(3)],
        ])
        .unwrap();
        let mp = minimal_polynomial(&m, "x").unwrap();
        assert_equal(
            &mp,
            &(v("x").pow(2) - CasExpr::int(5) * v("x") + CasExpr::int(6)),
        );

        // 2·I: minimal poly = x−2 (degree 1, below the char-poly degree 2).
        let scalar = Matrix::from_rows(vec![
            vec![CasExpr::int(2), CasExpr::zero()],
            vec![CasExpr::zero(), CasExpr::int(2)],
        ])
        .unwrap();
        assert_equal(
            &minimal_polynomial(&scalar, "x").unwrap(),
            &(v("x") - CasExpr::int(2)),
        );

        // Defective shear [[3,1],[0,3]]: minimal poly = (x−3)² = char poly.
        let shear = Matrix::from_rows(vec![
            vec![CasExpr::int(3), CasExpr::int(1)],
            vec![CasExpr::zero(), CasExpr::int(3)],
        ])
        .unwrap();
        assert_equal(
            &minimal_polynomial(&shear, "x").unwrap(),
            &(v("x").pow(2) - CasExpr::int(6) * v("x") + CasExpr::int(9)),
        );
    }

    #[test]
    fn definite_integral_certifies_by_ftc() {
        let x = || v("x");
        // ∫₀¹ 3x² dx = 1.
        let d = definite_integrate(
            &(CasExpr::int(3) * x().pow(2)),
            "x",
            &CasExpr::int(0),
            &CasExpr::int(1),
        )
        .unwrap();
        assert!(d.is_certified());
        assert_equal(&d.value, &CasExpr::int(1));

        // ∫₁³ (2x) dx = 9 − 1 = 8.
        let d2 = definite_integrate(
            &(CasExpr::int(2) * x()),
            "x",
            &CasExpr::int(1),
            &CasExpr::int(3),
        )
        .unwrap();
        assert!(d2.is_certified());
        assert_equal(&d2.value, &CasExpr::int(8));

        // Reversed bounds negate: ∫₃¹ 2x dx = −8.
        let d3 = definite_integrate(
            &(CasExpr::int(2) * x()),
            "x",
            &CasExpr::int(3),
            &CasExpr::int(1),
        )
        .unwrap();
        assert_equal(&d3.value, &CasExpr::int(-8));
    }

    #[test]
    fn improper_integrals_converge_or_decline() {
        let x = || v("x");
        let zero = || LimitPoint::Finite(Rational::zero());
        // ∫₀^∞ e^{−x} = 1; ∫₀^∞ x·e^{−x} = 1; ∫₀^∞ x²·e^{−x} = 2 (= Γ(3)).
        let e_neg_x = (CasExpr::int(-1) * x()).exp();
        let r1 = improper_integrate(&e_neg_x, "x", zero(), LimitPoint::PosInfinity).unwrap();
        assert!(r1.is_certified());
        assert_equal(&r1.value, &CasExpr::int(1));
        let r2 = improper_integrate(&(x() * e_neg_x.clone()), "x", zero(), LimitPoint::PosInfinity)
            .unwrap();
        assert_equal(&r2.value, &CasExpr::int(1));
        let r3 =
            improper_integrate(&(x().pow(2) * e_neg_x), "x", zero(), LimitPoint::PosInfinity)
                .unwrap();
        assert_equal(&r3.value, &CasExpr::int(2));
        // ∫₁^∞ 1/x² = 1; ∫_{−∞}^0 eˣ = 1.
        let one = || LimitPoint::Finite(Rational::integer(1));
        let r4 = improper_integrate(&(CasExpr::int(1) / x().pow(2)), "x", one(), LimitPoint::PosInfinity)
            .unwrap();
        assert_equal(&r4.value, &CasExpr::int(1));
        let r5 = improper_integrate(&x().exp(), "x", LimitPoint::NegInfinity, zero()).unwrap();
        assert_equal(&r5.value, &CasExpr::int(1));
        // ∫₁^∞ 1/x diverges (ln x → ∞) — declined, not a wrong finite value.
        assert!(
            improper_integrate(&(CasExpr::int(1) / x()), "x", one(), LimitPoint::PosInfinity)
                .is_none()
        );
    }

    #[test]
    fn definite_integral_folds_elementary_constants() {
        let x = || v("x");
        let pi = || v("pi");
        // ∫₀^π sin x = −cos π + cos 0 = 2 (trig constants folded).
        let s = definite_integrate(&x().sin(), "x", &CasExpr::int(0), &pi()).unwrap();
        assert!(s.is_certified());
        assert_equal(&s.value, &CasExpr::int(2));
        // ∫₁² 1/x = ln 2 − ln 1 = ln 2 (ln 1 = 0 folded).
        let l = definite_integrate(
            &(CasExpr::int(1) / x()),
            "x",
            &CasExpr::int(1),
            &CasExpr::int(2),
        )
        .unwrap();
        assert_equal(&l.value, &CasExpr::int(2).ln());
        // ∫₀^{π/2} cos x = sin(π/2) − sin 0 = 1.
        let c = definite_integrate(&x().cos(), "x", &CasExpr::int(0), &(pi() / CasExpr::int(2)))
            .unwrap();
        assert_equal(&c.value, &CasExpr::int(1));
    }

    #[test]
    fn taylor_about_nonzero_center() {
        let x = || v("x");
        // 1/x about x=1 to order 3: 1 − (x−1) + (x−1)² − (x−1)³, i.e. agrees with
        // 1/x through the cubic term. Check values match at several points via the
        // (x−1) form expanded.
        let approx = series_at(&(CasExpr::int(1) / x()), "x", &CasExpr::int(1), 3).unwrap();
        let shift = x() - CasExpr::int(1);
        let expected = CasExpr::int(1) - shift.clone() + shift.clone().pow(2) - shift.pow(3);
        assert_equal(&approx, &expected);

        // A polynomial's Taylor series about any center is itself: x² about x=2.
        let poly = series_at(&x().pow(2), "x", &CasExpr::int(2), 2).unwrap();
        assert_equal(&poly, &x().pow(2));

        // exp(x) about a nonzero center leaves the rational fragment → None.
        assert!(series_at(&x().exp(), "x", &CasExpr::int(1), 3).is_none());
    }

    #[test]
    fn finite_difference_calculus() {
        let x = || v("x");
        // Falling factorial x⁽³⁾ = x(x−1)(x−2) = x³ − 3x² + 2x.
        let ff3 = falling_factorial(&x(), 3);
        assert_equal(
            &ff3,
            &(x().pow(3) - CasExpr::int(3) * x().pow(2) + CasExpr::int(2) * x()),
        );
        // The finite power rule: Δ[x⁽³⁾] = 3·x⁽²⁾.
        assert_equal(
            &forward_difference(&ff3, "x"),
            &(CasExpr::int(3) * falling_factorial(&x(), 2)),
        );
        // Rising factorial x⁽³⁾↑ = x(x+1)(x+2) = x³ + 3x² + 2x.
        assert_equal(
            &rising_factorial(&x(), 3),
            &(x().pow(3) + CasExpr::int(3) * x().pow(2) + CasExpr::int(2) * x()),
        );
        // Forward difference of x² = 2x + 1; backward difference of x² = 2x − 1.
        assert_equal(
            &forward_difference(&x().pow(2), "x"),
            &(CasExpr::int(2) * x() + CasExpr::int(1)),
        );
        assert_equal(
            &backward_difference(&x().pow(2), "x"),
            &(CasExpr::int(2) * x() - CasExpr::int(1)),
        );
        // Δ of a constant is 0; falling_factorial(x, 0) = 1.
        assert_equal(&forward_difference(&CasExpr::int(5), "x"), &CasExpr::zero());
        assert_equal(&falling_factorial(&x(), 0), &CasExpr::int(1));
    }

    #[test]
    fn least_squares_fitting() {
        let x = || v("x");
        let ig = Rational::integer;
        // Exact line through collinear points: (0,1),(1,3),(2,5) → 2x + 1.
        let line =
            least_squares_polynomial(&[(ig(0), ig(1)), (ig(1), ig(3)), (ig(2), ig(5))], 1, "x")
                .unwrap();
        assert_equal(&line, &(CasExpr::int(2) * x() + CasExpr::int(1)));
        // Overdetermined least squares: fit a line to (0,0),(1,0),(2,2),(3,2) — the
        // exact rational best fit is y = (2/3)x − 1/5? Compute and re-check via the
        // symmetric-data slope: points symmetric about (1.5, 1) with slope 2/3.
        let fit = least_squares_polynomial(
            &[
                (ig(0), ig(0)),
                (ig(1), ig(0)),
                (ig(2), ig(2)),
                (ig(3), ig(2)),
            ],
            1,
            "x",
        )
        .unwrap();
        // The fit passes through the centroid (3/2, 1): evaluating at x = 3/2 gives 1.
        assert_equal(&fit.substitute("x", &CasExpr::rat(3, 2)), &CasExpr::int(1));
        // Exact quadratic through 3 points: (0,0),(1,1),(2,4) → x².
        let quad =
            least_squares_polynomial(&[(ig(0), ig(0)), (ig(1), ig(1)), (ig(2), ig(4))], 2, "x")
                .unwrap();
        assert_equal(&quad, &x().pow(2));
    }

    #[test]
    fn hessian_and_laplacian() {
        let x = || v("x");
        let y = || v("y");
        // f = x³ + x²y + y²: Hessian = [[6x+2y, 2x],[2x, 2]].
        let f = x().pow(3) + x().pow(2) * y() + y().pow(2);
        let h = hessian(&f, &["x", "y"]).unwrap();
        assert_equal(
            h.get(0, 0).unwrap(),
            &(CasExpr::int(6) * x() + CasExpr::int(2) * y()),
        );
        assert_equal(h.get(0, 1).unwrap(), &(CasExpr::int(2) * x()));
        assert_equal(h.get(1, 0).unwrap(), &(CasExpr::int(2) * x())); // symmetric
        assert_equal(h.get(1, 1).unwrap(), &CasExpr::int(2));
        // Laplacian ∇²(x³+x²y+y²) = (6x+2y) + 2 = 6x+2y+2.
        assert_equal(
            &laplacian(&f, &["x", "y"]),
            &(CasExpr::int(6) * x() + CasExpr::int(2) * y() + CasExpr::int(2)),
        );
        // A harmonic function has zero Laplacian: ∇²(x²−y²) = 2 − 2 = 0.
        assert_equal(
            &laplacian(&(x().pow(2) - y().pow(2)), &["x", "y"]),
            &CasExpr::zero(),
        );
    }

    #[test]
    fn wronskian_of_function_families() {
        let x = || v("x");
        // W(x, x²) = x².
        assert_equal(&wronskian(&[x(), x().pow(2)], "x").unwrap(), &x().pow(2));
        // W(1, x, x²) = 2 (constant Wronskian of the monomial basis).
        assert_equal(
            &wronskian(&[CasExpr::int(1), x(), x().pow(2)], "x").unwrap(),
            &CasExpr::int(2),
        );
        // W(eˣ, e⁻ˣ) = −2 — needs the exp tower (eˣ·e⁻ˣ = 1).
        assert_equal(
            &wronskian(&[x().exp(), (-x()).exp()], "x").unwrap(),
            &CasExpr::int(-2),
        );
        // W(sin x, cos x) = −1 — needs the Pythagorean identity.
        assert_equal(
            &wronskian(&[x().sin(), x().cos()], "x").unwrap(),
            &CasExpr::int(-1),
        );
        // Linearly dependent functions have a zero Wronskian: W(x, 2x) = 0.
        assert_equal(
            &wronskian(&[x(), CasExpr::int(2) * x()], "x").unwrap(),
            &CasExpr::zero(),
        );
    }

    #[test]
    fn gradient_jacobian_divergence_curl() {
        let x = || v("x");
        let y = || v("y");
        let z = || v("z");
        // field = x²y + y·z: ∇field = (2xy, x²+z, y).
        let scalar = x().pow(2) * y() + y() * z();
        let grad = gradient(&scalar, &["x", "y", "z"]);
        assert_equal(&grad[0], &(CasExpr::int(2) * x() * y()));
        assert_equal(&grad[1], &(x().pow(2) + z()));
        assert_equal(&grad[2], &y());

        // Jacobian of (x·y, x+y) w.r.t. (x,y) = [[y, x],[1, 1]].
        let jac = jacobian(&[x() * y(), x() + y()], &["x", "y"]).unwrap();
        assert_equal(jac.get(0, 0).unwrap(), &y());
        assert_equal(jac.get(0, 1).unwrap(), &x());
        assert_equal(jac.get(1, 0).unwrap(), &CasExpr::int(1));
        assert_equal(jac.get(1, 1).unwrap(), &CasExpr::int(1));

        // div(x², y², z²) = 2x + 2y + 2z.
        let div = divergence(&[x().pow(2), y().pow(2), z().pow(2)], &["x", "y", "z"]).unwrap();
        assert_equal(
            &div,
            &(CasExpr::int(2) * x() + CasExpr::int(2) * y() + CasExpr::int(2) * z()),
        );

        // A gradient field (−y, x, 0)? curl = (0,0,2). Standard example curl of
        // (−y, x, 0) = (0, 0, 2).
        let rotor = curl(&[-y(), x(), CasExpr::zero()], &["x", "y", "z"]).unwrap();
        assert_equal(&rotor[0], &CasExpr::zero());
        assert_equal(&rotor[1], &CasExpr::zero());
        assert_equal(&rotor[2], &CasExpr::int(2));
    }

    #[test]
    fn assumptions_gated_simplification() {
        let x = || v("x");
        // Under x ≥ 0: √(x²) = x (not |x|); |x| = x.
        let nonneg = Assumptions::new().nonnegative("x");
        assert_equal(
            &simplify_under_assumptions(&x().pow(2).sqrt(), &nonneg),
            &x(),
        );
        assert_equal(&simplify_under_assumptions(&x().abs(), &nonneg), &x());
        // Under x < 0: |x| = −x.
        let neg = Assumptions::new().negative("x");
        assert_equal(&simplify_under_assumptions(&x().abs(), &neg), &(-x()));
        // Without assumptions: √(x²) stays |x|, |x| stays |x|.
        let none = Assumptions::new();
        assert_equal(
            &simplify_under_assumptions(&x().pow(2).sqrt(), &none),
            &x().abs(),
        );
        // √(x⁴) under x ≥ 0 = x²; |x·y| under both positive = x·y.
        assert_equal(
            &simplify_under_assumptions(&x().pow(4).sqrt(), &nonneg),
            &x().pow(2),
        );
        let both = Assumptions::new().positive("x").positive("y");
        assert_equal(
            &simplify_under_assumptions(&(x() * v("y")).abs(), &both),
            &(x() * v("y")),
        );
    }

    #[test]
    fn radical_simplification_extracts_squares() {
        // √12 = 2√3.
        let s = simplify_radicals(&CasExpr::int(12).sqrt());
        assert_equal(&s, &(CasExpr::int(2) * CasExpr::int(3).sqrt()));
        // √9 = 3 (perfect square → rational).
        assert_equal(
            &simplify_radicals(&CasExpr::int(9).sqrt()),
            &CasExpr::int(3),
        );
        // √(1/2) = (1/2)·√2 (rationalized denominator).
        let half = simplify_radicals(&CasExpr::rat(1, 2).sqrt());
        assert_equal(&half, &(CasExpr::rat(1, 2) * CasExpr::int(2).sqrt()));
        // √8/9 wrapped: √(8/9) = (2/3)√2.
        assert_equal(
            &simplify_radicals(&CasExpr::rat(8, 9).sqrt()),
            &(CasExpr::rat(2, 3) * CasExpr::int(2).sqrt()),
        );
        // Certificate (square it back): (2√3)² = 12, checked by squaring the rational
        // coefficient and the square-free part — here 2²·3 = 12.
        // √2 is already square-free — left unchanged.
        assert_equal(
            &simplify_radicals(&CasExpr::int(2).sqrt()),
            &CasExpr::int(2).sqrt(),
        );
        // Negative radicand is left symbolic (no real simplification).
        let neg = CasExpr::int(-3).sqrt();
        assert_equal(&simplify_radicals(&neg), &neg);
        // A constant denominator cancels the extracted surd coefficient:
        // √8/2 → √2, √18/3 → √2, √12/2 → √3.
        assert_equal(
            &simplify_radicals(&(CasExpr::int(8).sqrt() / CasExpr::int(2))),
            &CasExpr::int(2).sqrt(),
        );
        assert_equal(
            &simplify_radicals(&(CasExpr::int(18).sqrt() / CasExpr::int(3))),
            &CasExpr::int(2).sqrt(),
        );
        assert_equal(
            &simplify_radicals(&(CasExpr::int(12).sqrt() / CasExpr::int(2))),
            &CasExpr::int(3).sqrt(),
        );
    }

    #[test]
    fn covariance_and_correlation() {
        let ig = Rational::integer;
        let xs = [ig(1), ig(2), ig(3), ig(4)];
        // Perfectly correlated: y = 2x + 1 → ρ = 1.
        let ys_pos = [ig(3), ig(5), ig(7), ig(9)];
        assert_equal(&correlation(&xs, &ys_pos).unwrap(), &CasExpr::int(1));
        // Perfectly anti-correlated: y = −x → ρ = −1.
        let ys_neg = [ig(-1), ig(-2), ig(-3), ig(-4)];
        assert_equal(&correlation(&xs, &ys_neg).unwrap(), &CasExpr::int(-1));
        // Covariance of x with itself is its variance (5/4 for 1..4).
        assert_eq!(stats::covariance(&xs, &xs), stats::variance(&xs));
        assert_eq!(stats::covariance(&xs, &xs), Some(Rational::new(5, 4)));
    }

    #[test]
    fn standard_deviation_is_exact() {
        // {2,4,4,4,5,5,7,9}: population variance 4 → stddev 2.
        let data: Vec<Rational> = [2, 4, 4, 4, 5, 5, 7, 9]
            .into_iter()
            .map(Rational::integer)
            .collect();
        assert_equal(&standard_deviation(&data).unwrap(), &CasExpr::int(2));
        // {1,2,3}: population variance 2/3 → stddev √(2/3) = (1/3)√6.
        let small: Vec<Rational> = [1, 2, 3].into_iter().map(Rational::integer).collect();
        assert_equal(
            &standard_deviation(&small).unwrap(),
            &(CasExpr::rat(1, 3) * CasExpr::int(6).sqrt()),
        );
        // Sample variance of {1,2,3} = 1 → sample stddev 1.
        assert_equal(
            &sample_standard_deviation(&small).unwrap(),
            &CasExpr::int(1),
        );
    }

    #[test]
    fn absolute_value_head() {
        let x = || v("x");
        // Constant folds: |−3| = 3, |5| = 5, |−1/2| = 1/2.
        assert_equal(&CasExpr::int(-3).abs(), &CasExpr::int(3));
        assert_equal(&CasExpr::int(5).abs(), &CasExpr::int(5));
        assert_equal(&CasExpr::rat(-1, 2).abs(), &CasExpr::rat(1, 2));
        // Symbolic |x| renders and round-trips through the zero-test.
        assert_eq!(x().abs().to_string(), "abs(x)");
        assert_equal(&x().abs(), &x().abs());
        // evalf(|−4|) = 4; evalf(|x|) at x = −2 is 2.
        assert!((evalf(&CasExpr::int(-4).abs(), &[]).unwrap() - 4.0).abs() < 1e-12);
        assert!((evalf(&x().abs(), &[("x", -2.0)]).unwrap() - 2.0).abs() < 1e-12);
        // d/dx |x| = x/|x|.
        assert_equal(&x().abs().differentiate("x"), &(x() / x().abs()));
        // √(x²) = |x| (sound identity via simplify_radicals).
        assert_equal(&simplify_radicals(&x().pow(2).sqrt()), &x().abs());
        // √(x⁴) = |x²| = x² … as |x²|; check it equals abs(x²).
        assert_equal(&simplify_radicals(&x().pow(4).sqrt()), &x().pow(2).abs());
    }

    #[test]
    fn logcombine_rules() {
        let x = || v("x");
        let y = || v("y");
        // ln x + ln y = ln(x·y).
        assert_equal(&logcombine(&(x().ln() + y().ln())), &(x() * y()).ln());
        // 2·ln x = ln(x²).
        assert_equal(&logcombine(&(CasExpr::int(2) * x().ln())), &x().pow(2).ln());
        // ln x − ln y = ln(x/y).
        assert_equal(&logcombine(&(x().ln() - y().ln())), &(x() / y()).ln());
        // 2·ln x + 3·ln y = ln(x²·y³).
        assert_equal(
            &logcombine(&(CasExpr::int(2) * x().ln() + CasExpr::int(3) * y().ln())),
            &(x().pow(2) * y().pow(3)).ln(),
        );
        // Inverse of expand_log: logcombine(expand_log(ln(x²·y))) = ln(x²·y).
        let start = (x().pow(2) * y()).ln();
        assert_equal(&logcombine(&expand_log(&start)), &start);
        // Non-log terms are preserved: ln x + 3 stays ln x + 3.
        assert_equal(
            &logcombine(&(x().ln() + CasExpr::int(3))),
            &(x().ln() + CasExpr::int(3)),
        );
    }

    #[test]
    fn expand_log_rules() {
        let x = || v("x");
        let y = || v("y");
        // ln(x·y) = ln x + ln y.
        assert_equal(&expand_log(&(x() * y()).ln()), &(x().ln() + y().ln()));
        // ln(x/y) = ln x − ln y.
        assert_equal(&expand_log(&(x() / y()).ln()), &(x().ln() - y().ln()));
        // ln(x³) = 3·ln x.
        assert_equal(&expand_log(&x().pow(3).ln()), &(CasExpr::int(3) * x().ln()));
        // ln(x²·y) = 2·ln x + ln y (product + power together).
        assert_equal(
            &expand_log(&(x().pow(2) * y()).ln()),
            &(CasExpr::int(2) * x().ln() + y().ln()),
        );
        // A bare ln is untouched.
        assert_equal(&expand_log(&x().ln()), &x().ln());
    }

    #[test]
    fn trig_identities_via_euler() {
        let x = || v("x");
        let y = || v("y");
        // Compare the Euler rewrites of the two sides; the exp tower + I²=−1 decide.
        let holds = |a: CasExpr, b: CasExpr| {
            matches!(
                equal(&rewrite_exp(&a), &rewrite_exp(&b)),
                ZeroTest::Certified { equal: true, .. }
            )
        };
        // Double angle: cos(2x) = 2cos²x − 1 = 1 − 2sin²x.
        assert!(holds(
            (CasExpr::int(2) * x()).cos(),
            CasExpr::int(2) * x().cos().pow(2) - CasExpr::int(1)
        ));
        assert!(holds(
            (CasExpr::int(2) * x()).cos(),
            CasExpr::int(1) - CasExpr::int(2) * x().sin().pow(2)
        ));
        // sin(2x) = 2 sin x cos x.
        assert!(holds(
            (CasExpr::int(2) * x()).sin(),
            CasExpr::int(2) * x().sin() * x().cos()
        ));
        // Pythagorean (already known, but via Euler too): sin²x + cos²x = 1.
        assert!(holds(x().sin().pow(2) + x().cos().pow(2), CasExpr::int(1)));
        // Angle-sum: cos(x+y) = cos x cos y − sin x sin y.
        assert!(holds(
            (x() + y()).cos(),
            x().cos() * y().cos() - x().sin() * y().sin(),
        ));
        // sin(x+y) = sin x cos y + cos x sin y.
        assert!(holds(
            (x() + y()).sin(),
            x().sin() * y().cos() + x().cos() * y().sin(),
        ));
        // Power reduction: sin²x = (1 − cos 2x)/2.
        assert!(holds(
            x().sin().pow(2),
            (CasExpr::int(1) - (CasExpr::int(2) * x()).cos()) / CasExpr::int(2),
        ));
        // A NON-identity is not falsely certified: cos(2x) ≠ 2cos²x.
        assert!(!holds(
            (CasExpr::int(2) * x()).cos(),
            CasExpr::int(2) * x().cos().pow(2)
        ));
    }

    #[test]
    fn exact_trig_values() {
        let pi = || v("pi");
        let sin = |c: CasExpr| evaluate_trig(&c.sin());
        let cos = |c: CasExpr| evaluate_trig(&c.cos());
        let tan = |c: CasExpr| evaluate_trig(&c.tan());
        // Standard unit-circle values.
        assert_equal(&sin(pi() / CasExpr::int(6)), &CasExpr::rat(1, 2));
        assert_equal(&cos(pi() / CasExpr::int(3)), &CasExpr::rat(1, 2));
        assert_equal(
            &sin(pi() / CasExpr::int(4)),
            &(CasExpr::rat(1, 2) * CasExpr::int(2).sqrt()),
        );
        assert_equal(
            &cos(pi() / CasExpr::int(6)),
            &(CasExpr::rat(1, 2) * CasExpr::int(3).sqrt()),
        );
        assert_equal(&tan(pi() / CasExpr::int(4)), &CasExpr::int(1));
        assert_equal(&tan(pi() / CasExpr::int(3)), &CasExpr::int(3).sqrt());
        // sin(0) = 0, cos(0) = 1, sin(π/2) = 1, cos(π/2) = 0, sin(π) = 0.
        assert_equal(&sin(CasExpr::int(0) * pi()), &CasExpr::zero());
        assert_equal(&cos(CasExpr::int(0) * pi()), &CasExpr::int(1));
        assert_equal(&sin(pi() / CasExpr::int(2)), &CasExpr::int(1));
        assert_equal(&cos(pi() / CasExpr::int(2)), &CasExpr::zero());
        assert_equal(&sin(pi()), &CasExpr::zero());
        // 15° = π/12 = (√6 − √2)/4 — the fine-grained table entry.
        assert_equal(
            &sin(pi() / CasExpr::int(12)),
            &(CasExpr::rat(1, 4) * CasExpr::int(6).sqrt()
                - CasExpr::rat(1, 4) * CasExpr::int(2).sqrt()),
        );
        // Pythagorean check on the exact values: sin²(π/5? no) — use π/6: (1/2)²+(√3/2)²=1.
        let s = sin(pi() / CasExpr::int(6));
        let c = cos(pi() / CasExpr::int(6));
        assert_equal(&(s.pow(2) + c.pow(2)), &CasExpr::int(1));
        // tan(π/2) is a pole → left unevaluated.
        assert!(matches!(
            tan(pi() / CasExpr::int(2)),
            CasExpr::Unary(UnaryFunc::Tan, _)
        ));
        // A non-special angle (π/5) is left unevaluated.
        assert!(matches!(
            sin(pi() / CasExpr::int(5)),
            CasExpr::Unary(UnaryFunc::Sin, _)
        ));
    }

    #[test]
    fn rationalize_recovers_nice_fractions() {
        assert_eq!(rationalize(0.5, 100), Some(Rational::new(1, 2)));
        assert_eq!(rationalize(0.25, 100), Some(Rational::new(1, 4)));
        assert_eq!(rationalize(1.0 / 3.0, 100), Some(Rational::new(1, 3)));
        assert_eq!(rationalize(-2.0 / 7.0, 100), Some(Rational::new(-2, 7)));
        // π ≈ 3.14159 → 355/113 (the famous convergent) with denominator ≤ 1000.
        assert_eq!(
            rationalize(std::f64::consts::PI, 1000),
            Some(Rational::new(355, 113))
        );
        // An exact integer.
        assert_eq!(rationalize(5.0, 100), Some(Rational::integer(5)));
        assert!(rationalize(f64::NAN, 100).is_none());
    }

    #[test]
    fn evalf_approximates() {
        let x = || v("x");
        // √2 ≈ 1.4142…
        assert!(
            (evalf(&CasExpr::int(2).sqrt(), &[]).unwrap() - std::f64::consts::SQRT_2).abs() < 1e-12
        );
        // exp(0) = 1, sin(0) = 0.
        assert!((evalf(&CasExpr::int(0).exp(), &[]).unwrap() - 1.0).abs() < 1e-12);
        // A bound variable: 2x² + 1 at x = 3 → 19.
        assert!(
            (evalf(
                &(CasExpr::int(2) * x().pow(2) + CasExpr::int(1)),
                &[("x", 3.0)]
            )
            .unwrap()
                - 19.0)
                .abs()
                < 1e-12
        );
        // stddev {1,2,3} = (1/3)√6 ≈ 0.8165.
        let data: Vec<Rational> = [1, 2, 3].into_iter().map(Rational::integer).collect();
        let sd = standard_deviation(&data).unwrap();
        assert!((evalf(&sd, &[]).unwrap() - (6.0_f64).sqrt() / 3.0).abs() < 1e-12);
        // Unbound free variable → None.
        assert!(evalf(&x(), &[]).is_none());
    }

    #[test]
    fn gram_schmidt_orthogonalizes() {
        let c = |n: i128| CasExpr::int(n);
        // (1,1,0), (1,0,1), (0,1,1) → mutually orthogonal rational vectors.
        let vectors = vec![
            vec![c(1), c(1), c(0)],
            vec![c(1), c(0), c(1)],
            vec![c(0), c(1), c(1)],
        ];
        let basis = gram_schmidt(&vectors).unwrap();
        assert_eq!(basis.len(), 3);
        // Every distinct pair is orthogonal (dot = 0), certified.
        for i in 0..basis.len() {
            for j in (i + 1)..basis.len() {
                assert_equal(&dot(&basis[i], &basis[j]).unwrap(), &CasExpr::zero());
            }
        }
        // A linearly dependent vector is dropped: (1,0),(2,0),(0,1) → 2 orthogonal.
        let dependent = vec![vec![c(1), c(0)], vec![c(2), c(0)], vec![c(0), c(1)]];
        let reduced = gram_schmidt(&dependent).unwrap();
        assert_eq!(reduced.len(), 2);
        assert_equal(&dot(&reduced[0], &reduced[1]).unwrap(), &CasExpr::zero());
    }

    #[test]
    fn vector_dot_cross_norm() {
        let x = || v("x");
        let y = || v("y");
        let z = || v("z");
        // Dot product: (1,2,3)·(4,5,6) = 32.
        let lhs = [CasExpr::int(1), CasExpr::int(2), CasExpr::int(3)];
        let rhs = [CasExpr::int(4), CasExpr::int(5), CasExpr::int(6)];
        assert_equal(&dot(&lhs, &rhs).unwrap(), &CasExpr::int(32));
        // Symbolic dot: (x,y)·(y,x) = 2xy.
        assert_equal(
            &dot(&[x(), y()], &[y(), x()]).unwrap(),
            &(CasExpr::int(2) * x() * y()),
        );
        // Cross product of the standard basis: e₁ × e₂ = e₃.
        let basis_x = [CasExpr::int(1), CasExpr::zero(), CasExpr::zero()];
        let basis_y = [CasExpr::zero(), CasExpr::int(1), CasExpr::zero()];
        let basis_cross = cross(&basis_x, &basis_y).unwrap();
        assert_equal(&basis_cross[0], &CasExpr::zero());
        assert_equal(&basis_cross[1], &CasExpr::zero());
        assert_equal(&basis_cross[2], &CasExpr::int(1));
        // (u × w) ⟂ u (dot is zero) — for a generic symbolic pair.
        let vec_u = [x(), y(), z()];
        let vec_w = [y(), z(), x()];
        let perpendicular = cross(&vec_u, &vec_w).unwrap();
        assert_equal(&dot(&perpendicular, &vec_u).unwrap(), &CasExpr::zero());
        // Norm: ‖(3,4)‖ = 5; ‖(1,1)‖ = √2.
        assert_equal(
            &norm(&[CasExpr::int(3), CasExpr::int(4)]).unwrap(),
            &CasExpr::int(5),
        );
        assert_equal(
            &norm(&[CasExpr::int(1), CasExpr::int(1)]).unwrap(),
            &CasExpr::int(2).sqrt(),
        );
    }

    #[test]
    fn exponential_addition_law() {
        let x = || v("x");
        let y = || v("y");
        // exp(x + y) = exp(x)·exp(y) — the addition law, via per-term decomposition.
        assert_equal(&(x() + y()).exp(), &(x().exp() * y().exp()));
        // exp(x)·exp(y) = exp(x + y).
        assert_equal(&(x().exp() * y().exp()), &(x() + y()).exp());
        // exp(a + b − a) = exp(b): the mixed cancel-and-combine the ODE cert needs.
        let a = || CasExpr::var("a");
        let b = || CasExpr::var("b");
        assert_equal(&(a() + b() - a()).exp(), &b().exp());
        // exp(x + 1)·exp(−x) = exp(1) (constant term survives, x cancels).
        assert_equal(
            &((x() + CasExpr::int(1)).exp() * (-x()).exp()),
            &CasExpr::int(1).exp(),
        );
        // A polynomial exponent splits into per-monomial factors and recombines:
        // exp(x² + x) = exp(x²)·exp(x).
        assert_equal(&(x().pow(2) + x()).exp(), &(x().pow(2).exp() * x().exp()));
        // Integer scaling: exp(2x) = exp(x)², and exp(x)·exp(2x) = exp(3x).
        assert_equal(&(CasExpr::int(2) * x()).exp(), &x().exp().pow(2));
        assert_equal(
            &(x().exp() * (CasExpr::int(2) * x()).exp()),
            &(CasExpr::int(3) * x()).exp(),
        );
        // exp(2) = exp(1)² (constant argument, integer scaling).
        assert_equal(&CasExpr::int(2).exp(), &CasExpr::int(1).exp().pow(2));
        // exp/ln inverse: exp(ln 5) = 5, exp(2·ln 3) = 9, exp(−ln 2) = 1/2.
        assert_equal(&CasExpr::int(5).ln().exp(), &CasExpr::int(5));
        assert_equal(
            &(CasExpr::int(2) * CasExpr::int(3).ln()).exp(),
            &CasExpr::int(9),
        );
        assert_equal(&(-CasExpr::int(2).ln()).exp(), &CasExpr::rat(1, 2));
        // Sanity: the general non-cancelling product stays honest — exp(x)·exp(y) is
        // not equal to exp(x) alone.
        assert_not_equal(&(x().exp() * y().exp()), &x().exp());
    }

    #[test]
    fn exponential_reciprocal_cancels() {
        let x = || v("x");
        // exp(x)·exp(−x) = 1 — the reciprocal canonicalization makes this decidable.
        assert_equal(&(x().exp() * (-x()).exp()), &CasExpr::int(1));
        // exp(0) = 1.
        assert_equal(&CasExpr::zero().exp(), &CasExpr::int(1));
        // exp(x)/exp(x) = 1 (already worked, still holds).
        assert_equal(&(x().exp() / x().exp()), &CasExpr::int(1));
        // exp(2x)·exp(−2x) = 1 with a scaled argument.
        assert_equal(
            &((CasExpr::int(2) * x()).exp() * (CasExpr::int(-2) * x()).exp()),
            &CasExpr::int(1),
        );
        // exp(P)·exp(−P) = 1 for a polynomial argument P = x² − 3.
        let poly_arg = x().pow(2) - CasExpr::int(3);
        assert_equal(
            &(poly_arg.clone().exp() * (-poly_arg).exp()),
            &CasExpr::int(1),
        );
        // Sanity: exp(x)·exp(y) is NOT reduced (different atoms) — must stay unknown-
        // /non-equal to exp(x+y) (the general law needs the exp tower). Assert it does
        // not falsely certify equal to something wrong: exp(x) ≠ 1.
        assert!(!matches!(
            equal(&x().exp(), &CasExpr::int(1)),
            ZeroTest::Certified { equal: true, .. }
        ));
    }

    #[test]
    fn radical_arithmetic_certifies() {
        // √2·√2 = 2, (√8)² = 8, and (1+√2)² = 3 + 2√2 — all decided by the
        // sqrt(c)²→c fold in the zero-test.
        let sqrt2 = CasExpr::int(2).sqrt();
        assert_equal(&(sqrt2.clone() * sqrt2.clone()), &CasExpr::int(2));
        assert_equal(&CasExpr::int(8).sqrt().pow(2), &CasExpr::int(8));
        let one_plus_sqrt2 = CasExpr::int(1) + sqrt2.clone();
        assert_equal(
            &one_plus_sqrt2.pow(2),
            &(CasExpr::int(3) + CasExpr::int(2) * sqrt2),
        );
        // Difference of squares with surds: (√3−1)(√3+1) = 2.
        let sqrt3 = CasExpr::int(3).sqrt();
        assert_equal(
            &((sqrt3.clone() - CasExpr::int(1)) * (sqrt3 + CasExpr::int(1))),
            &CasExpr::int(2),
        );
    }

    #[test]
    fn polynomial_inequalities() {
        let x = || v("x");
        let ig = Rational::integer;
        // x² − 5x + 6 > 0  ⇒  (−∞, 2) ∪ (3, ∞).
        let p = x().pow(2) - CasExpr::int(5) * x() + CasExpr::int(6);
        let gt = solve_polynomial_inequality(&p, "x", InequalityOp::Greater).unwrap();
        assert_eq!(gt.len(), 2);
        assert_eq!(
            gt[0],
            RealInterval {
                lower: None,
                lower_closed: false,
                upper: Some(ig(2)),
                upper_closed: false
            }
        );
        assert_eq!(
            gt[1],
            RealInterval {
                lower: Some(ig(3)),
                lower_closed: false,
                upper: None,
                upper_closed: false
            }
        );
        // x² − 5x + 6 ≤ 0  ⇒  [2, 3].
        let le = solve_polynomial_inequality(&p, "x", InequalityOp::LessEqual).unwrap();
        assert_eq!(
            le,
            vec![RealInterval {
                lower: Some(ig(2)),
                lower_closed: true,
                upper: Some(ig(3)),
                upper_closed: true
            }]
        );
        // x² + 1 > 0  ⇒  all reals (no real roots, positive everywhere).
        let all = solve_polynomial_inequality(
            &(x().pow(2) + CasExpr::int(1)),
            "x",
            InequalityOp::Greater,
        )
        .unwrap();
        assert_eq!(
            all,
            vec![RealInterval {
                lower: None,
                lower_closed: false,
                upper: None,
                upper_closed: false
            }]
        );
        // x² + 1 < 0  ⇒  empty.
        assert!(
            solve_polynomial_inequality(&(x().pow(2) + CasExpr::int(1)), "x", InequalityOp::Less)
                .unwrap()
                .is_empty()
        );
        // (x−1)² ≥ 0  ⇒  all reals (double root included, both sides positive).
        let sq = x().pow(2) - CasExpr::int(2) * x() + CasExpr::int(1);
        let ge = solve_polynomial_inequality(&sq, "x", InequalityOp::GreaterEqual).unwrap();
        assert_eq!(
            ge,
            vec![RealInterval {
                lower: None,
                lower_closed: false,
                upper: None,
                upper_closed: false
            }]
        );
        // An irrational-root polynomial (x² − 2 > 0) declines (endpoints ±√2).
        assert!(
            solve_polynomial_inequality(
                &(x().pow(2) - CasExpr::int(2)),
                "x",
                InequalityOp::Greater
            )
            .is_none()
        );
    }

    #[test]
    fn cyclotomic_polynomials() {
        let x = || v("x");
        // Known small cases.
        assert_equal(
            &cyclotomic_polynomial(1, "x").unwrap(),
            &(x() - CasExpr::int(1)),
        );
        assert_equal(
            &cyclotomic_polynomial(2, "x").unwrap(),
            &(x() + CasExpr::int(1)),
        );
        assert_equal(
            &cyclotomic_polynomial(3, "x").unwrap(),
            &(x().pow(2) + x() + CasExpr::int(1)),
        );
        assert_equal(
            &cyclotomic_polynomial(4, "x").unwrap(),
            &(x().pow(2) + CasExpr::int(1)),
        );
        assert_equal(
            &cyclotomic_polynomial(6, "x").unwrap(),
            &(x().pow(2) - x() + CasExpr::int(1)),
        );
        // Φ₁₂ = x⁴ − x² + 1.
        assert_equal(
            &cyclotomic_polynomial(12, "x").unwrap(),
            &(x().pow(4) - x().pow(2) + CasExpr::int(1)),
        );
        // Certificate: ∏_{d|6} Φ_d = Φ₁·Φ₂·Φ₃·Φ₆ = x⁶ − 1.
        let product = cyclotomic_polynomial(1, "x").unwrap()
            * cyclotomic_polynomial(2, "x").unwrap()
            * cyclotomic_polynomial(3, "x").unwrap()
            * cyclotomic_polynomial(6, "x").unwrap();
        assert_equal(&product, &(x().pow(6) - CasExpr::int(1)));
    }

    #[test]
    fn resultant_and_discriminant() {
        let x = || v("x");
        // Common root ⇒ resultant 0; coprime ⇒ nonzero.
        assert_equal(
            &resultant(
                &(x().pow(2) - CasExpr::int(1)),
                &(x() - CasExpr::int(1)),
                "x",
            )
            .unwrap(),
            &CasExpr::zero(),
        );
        assert!(matches!(
            resultant(&(x().pow(2) - CasExpr::int(1)), &(x() - CasExpr::int(3)), "x").unwrap(),
            CasExpr::Const(c) if !c.is_zero()
        ));
        // disc(x²−5x+6) = 1 (roots 2,3 distinct); disc(x²+1) = −4; disc(x²−4x+4) = 0
        // (double root 2).
        assert_equal(
            &discriminant(&(x().pow(2) - CasExpr::int(5) * x() + CasExpr::int(6)), "x").unwrap(),
            &CasExpr::int(1),
        );
        assert_equal(
            &discriminant(&(x().pow(2) + CasExpr::int(1)), "x").unwrap(),
            &CasExpr::int(-4),
        );
        assert_equal(
            &discriminant(&(x().pow(2) - CasExpr::int(4) * x() + CasExpr::int(4)), "x").unwrap(),
            &CasExpr::zero(),
        );
        // Cubic with a double root has zero discriminant: (x−1)²(x−2) = x³−4x²+5x−2.
        let cubic =
            x().pow(3) - CasExpr::int(4) * x().pow(2) + CasExpr::int(5) * x() - CasExpr::int(2);
        assert_equal(&discriminant(&cubic, "x").unwrap(), &CasExpr::zero());
    }

    #[test]
    fn polynomial_queries() {
        let x = || v("x");
        let p = CasExpr::int(3) * x().pow(2) - CasExpr::int(5) * x() + CasExpr::int(7);
        assert_eq!(degree(&p, "x"), Some(2));
        assert_equal(&leading_coeff(&p, "x").unwrap(), &CasExpr::int(3));
        assert_equal(&coeff(&p, "x", 1).unwrap(), &CasExpr::int(-5));
        assert_equal(&coeff(&p, "x", 0).unwrap(), &CasExpr::int(7));
        assert_equal(&coeff(&p, "x", 5).unwrap(), &CasExpr::zero());
    }

    #[test]
    fn content_primitive_and_matrix_predicates() {
        let x = || v("x");
        // content(6x² + 4x + 2) = 2; primitive part = 3x² + 2x + 1.
        assert_equal(
            &content(
                &(CasExpr::int(6) * x().pow(2) + CasExpr::int(4) * x() + CasExpr::int(2)),
                "x",
            )
            .unwrap(),
            &CasExpr::int(2),
        );
        assert_equal(
            &primitive_part(
                &(CasExpr::int(6) * x().pow(2) + CasExpr::int(4) * x() + CasExpr::int(2)),
                "x",
            )
            .unwrap(),
            &(CasExpr::int(3) * x().pow(2) + CasExpr::int(2) * x() + CasExpr::int(1)),
        );
        // content((1/2)x + (1/3)) = 1/6.
        assert_equal(
            &content(&(CasExpr::rat(1, 2) * x() + CasExpr::rat(1, 3)), "x").unwrap(),
            &CasExpr::rat(1, 6),
        );
        // Matrix predicates.
        let diag = Matrix::from_rows(vec![
            vec![CasExpr::int(2), CasExpr::zero()],
            vec![CasExpr::zero(), CasExpr::int(3)],
        ])
        .unwrap();
        assert!(diag.is_diagonal() && diag.is_upper_triangular() && diag.is_lower_triangular());
        assert!(!diag.is_identity());
        assert!(Matrix::identity(3).is_identity());
        let upper = Matrix::from_rows(vec![
            vec![CasExpr::int(1), CasExpr::int(2)],
            vec![CasExpr::zero(), CasExpr::int(3)],
        ])
        .unwrap();
        assert!(
            upper.is_upper_triangular() && !upper.is_lower_triangular() && !upper.is_diagonal()
        );
    }

    #[test]
    fn polynomial_lcm_and_irreducibility() {
        let x = || v("x");
        // lcm(x²−1, x²−2x+1) = (x−1)(x+1)(x−1)/gcd... = (x−1)²(x+1)/(x−1) monic
        // Actually lcm((x-1)(x+1), (x-1)²) = (x-1)²(x+1) = x³−x²−x+1.
        assert_equal(
            &poly_lcm(
                &(x().pow(2) - CasExpr::int(1)),
                &(x().pow(2) - CasExpr::int(2) * x() + CasExpr::int(1)),
                "x",
            )
            .unwrap(),
            &(x().pow(3) - x().pow(2) - x() + CasExpr::int(1)),
        );
        // Irreducibility over ℚ: x²+1 and x²−2 irreducible; x²−1 reducible.
        assert_eq!(
            is_irreducible(&(x().pow(2) + CasExpr::int(1)), "x"),
            Some(true)
        );
        assert_eq!(
            is_irreducible(&(x().pow(2) - CasExpr::int(2)), "x"),
            Some(true)
        );
        assert_eq!(
            is_irreducible(&(x().pow(2) - CasExpr::int(1)), "x"),
            Some(false)
        );
        // Swinnerton–Dyer quartic x⁴−10x²+1 is irreducible over ℚ.
        assert_eq!(
            is_irreducible(
                &(x().pow(4) - CasExpr::int(10) * x().pow(2) + CasExpr::int(1)),
                "x"
            ),
            Some(true),
        );
    }

    #[test]
    fn polynomial_gcd_and_division() {
        let x = || v("x");
        // gcd(x²−1, x²−2x+1) = x−1
        assert_equal(
            &poly_gcd(
                &(x().pow(2) - CasExpr::int(1)),
                &(x().pow(2) - CasExpr::int(2) * x() + CasExpr::int(1)),
                "x",
            )
            .unwrap(),
            &(x() - CasExpr::int(1)),
        );
        // (x³−1) = (x²+x+1)(x−1) + 0
        let (q, r) = poly_div(
            &(x().pow(3) - CasExpr::int(1)),
            &(x() - CasExpr::int(1)),
            "x",
        )
        .unwrap();
        assert_equal(&q, &(x().pow(2) + x() + CasExpr::int(1)));
        assert_equal(&r, &CasExpr::zero());
    }

    #[test]
    fn factor_polynomials() {
        let x = || v("x");
        // x² − 3x + 2 = (x−1)(x−2)
        let f = x().pow(2) - CasExpr::int(3) * x() + CasExpr::int(2);
        let factored = factor(&f, "x").expect("factorable");
        assert_equal(&factored, &f); // certified equal to the input
        assert_equal(
            &factored,
            &((x() - CasExpr::int(1)) * (x() - CasExpr::int(2))),
        );
        // 2x² − 6x + 4 = 2·(x−1)(x−2) (non-monic leading constant preserved)
        let g = CasExpr::int(2) * x().pow(2) - CasExpr::int(6) * x() + CasExpr::int(4);
        assert_equal(&factor(&g, "x").expect("factorable"), &g);
        // x² − 2x + 1 = (x−1)² (repeated root grouped into a power)
        let h = x().pow(2) - CasExpr::int(2) * x() + CasExpr::int(1);
        assert_equal(
            &factor(&h, "x").expect("factorable"),
            &(x() - CasExpr::int(1)).pow(2),
        );
        // 4th derivative of x⁴ is 24
        assert_equal(&x().pow(4).differentiate_n("x", 4), &CasExpr::int(24));
    }

    #[test]
    fn pythagorean_identity_is_certified() {
        let x = || v("x");
        // sin²x + cos²x = 1
        assert_equal(&(x().sin().pow(2) + x().cos().pow(2)), &CasExpr::int(1));
        // 1 − cos²x = sin²x
        assert_equal(&(CasExpr::int(1) - x().cos().pow(2)), &x().sin().pow(2));
        // cos⁴x − sin⁴x = cos²x − sin²x  (factors as (cos²+sin²)(cos²−sin²))
        assert_equal(
            &(x().cos().pow(4) - x().sin().pow(4)),
            &(x().cos().pow(2) - x().sin().pow(2)),
        );
        // per-argument: sin²(2x) + cos²(2x) = 1
        assert_equal(
            &((CasExpr::int(2) * x()).sin().pow(2) + (CasExpr::int(2) * x()).cos().pow(2)),
            &CasExpr::int(1),
        );
    }

    #[test]
    fn complex_conjugate_real_imaginary() {
        let im = CasExpr::imaginary_unit;
        let z = CasExpr::int(3) + CasExpr::int(4) * im(); // 3 + 4I
        assert_equal(&conjugate(&z), &(CasExpr::int(3) - CasExpr::int(4) * im()));
        assert_equal(&real_part(&z).unwrap(), &CasExpr::int(3));
        assert_equal(&imaginary_part(&z).unwrap(), &CasExpr::int(4));
        // |z|² = z·conj(z) = 25 (real)
        assert_equal(
            &real_part(&(z.clone() * conjugate(&z))).unwrap(),
            &CasExpr::int(25),
        );
        assert_equal(
            &imaginary_part(&(z.clone() * conjugate(&z))).unwrap(),
            &CasExpr::zero(),
        );
    }

    #[test]
    fn complex_modulus_and_roots_of_unity() {
        let i = CasExpr::imaginary_unit();
        // |3 + 4i| = 5; |1 + i| = √2; |5| = 5.
        assert_equal(
            &modulus(&(CasExpr::int(3) + CasExpr::int(4) * i.clone())).unwrap(),
            &CasExpr::int(5),
        );
        assert_equal(
            &modulus(&(CasExpr::int(1) + i.clone())).unwrap(),
            &CasExpr::int(2).sqrt(),
        );
        assert_equal(&modulus(&CasExpr::int(5)).unwrap(), &CasExpr::int(5));
        // 4th roots of unity: 1, i, −1, −i.
        let roots = roots_of_unity(4).unwrap();
        assert_eq!(roots.len(), 4);
        assert_equal(&roots[0], &CasExpr::int(1));
        assert_equal(&roots[1], &i);
        assert_equal(&roots[2], &CasExpr::int(-1));
        assert_equal(&roots[3], &(-i.clone()));
        // Each 4th root of unity satisfies z⁴ = 1 (via the I²=−1 fold).
        for z in &roots {
            assert_equal(&z.clone().pow(4), &CasExpr::int(1));
        }
        // 6th roots include the primitive (1+√3 i)/2 at k=1: cos(π/3)+i sin(π/3).
        let six = roots_of_unity(6).unwrap();
        assert_equal(
            &six[1],
            &(CasExpr::rat(1, 2) + CasExpr::rat(1, 2) * CasExpr::int(3).sqrt() * i),
        );
    }

    #[test]
    fn complex_arithmetic_is_certified() {
        let im = CasExpr::imaginary_unit;
        // I² = −1
        assert_equal(&im().pow(2), &CasExpr::int(-1));
        // (1 + I)(1 − I) = 2
        assert_equal(
            &((CasExpr::int(1) + im()) * (CasExpr::int(1) - im())),
            &CasExpr::int(2),
        );
        // (1 + I)² = 2I
        assert_equal(&(CasExpr::int(1) + im()).pow(2), &(CasExpr::int(2) * im()));
        // complex roots of x²+1 verify: I²+1 = 0
        for r in solve(&(v("x").pow(2) + CasExpr::int(1)), "x").unwrap() {
            assert_equal(
                &(v("x").pow(2) + CasExpr::int(1)).substitute("x", &r),
                &CasExpr::zero(),
            );
        }
    }

    #[test]
    fn solve_complex_roots() {
        let x = || v("x");
        let strs = |e: CasExpr| -> Vec<String> {
            solve(&e, "x")
                .unwrap()
                .iter()
                .map(ToString::to_string)
                .collect()
        };
        // x² + 1 = 0 → ±I
        assert_eq!(strs(x().pow(2) + CasExpr::int(1)), vec!["I", "-I"]);
        // x² + 2x + 5 = 0 → −1 ± 2I
        assert_eq!(
            strs(x().pow(2) + CasExpr::int(2) * x() + CasExpr::int(5)),
            vec!["-1 + 2*I", "-1 - 2*I"]
        );
    }

    #[test]
    fn linear_system_solving() {
        let x = || v("x");
        let y = || v("y");
        let z = || v("z");
        // x + y = 3, x − y = 1 ⇒ x=2, y=1.
        let sol = solve_linear_system(
            &[x() + y() - CasExpr::int(3), x() - y() - CasExpr::int(1)],
            &["x", "y"],
        )
        .unwrap();
        assert_equal(&sol[0].1, &CasExpr::int(2));
        assert_equal(&sol[1].1, &CasExpr::int(1));
        // 3×3: x+y+z=6, 2y+z=... solve x+y+z=6, x−y=−1, y−z=−1 ⇒ x=1,y=2,z=3.
        let sol3 = solve_linear_system(
            &[
                x() + y() + z() - CasExpr::int(6),
                x() - y() + CasExpr::int(1),
                y() - z() + CasExpr::int(1),
            ],
            &["x", "y", "z"],
        )
        .unwrap();
        assert_equal(&sol3[0].1, &CasExpr::int(1));
        assert_equal(&sol3[1].1, &CasExpr::int(2));
        assert_equal(&sol3[2].1, &CasExpr::int(3));
        // Singular system (no unique solution) declines.
        assert!(
            solve_linear_system(
                &[x() + y(), CasExpr::int(2) * x() + CasExpr::int(2) * y()],
                &["x", "y"]
            )
            .is_none()
        );
    }

    #[test]
    fn solve_polynomials() {
        let x = || v("x");
        // x² − 3x + 2 = 0  ⇒  {1, 2}
        let f = x().pow(2) - CasExpr::int(3) * x() + CasExpr::int(2);
        let roots = solve(&f, "x").expect("solvable");
        assert_eq!(roots.len(), 2);
        for r in &roots {
            assert_equal(&f.substitute("x", r), &CasExpr::zero());
        }
        // x² − 4 = 0  ⇒  {2, −2} (quadratic formula, perfect-square discriminant)
        let g = x().pow(2) - CasExpr::int(4);
        let roots2 = solve(&g, "x").expect("solvable");
        assert_eq!(roots2.len(), 2);
        for r in &roots2 {
            assert_equal(&g.substitute("x", r), &CasExpr::zero());
        }
    }

    #[test]
    fn solve_irrational_roots_are_simplified_surds() {
        let x = || v("x");
        // x² − 12 = 0 ⇒ ±2√3 (surd extracted and reduced, not ±√12/1).
        let f = x().pow(2) - CasExpr::int(12);
        let roots = solve(&f, "x").expect("solvable");
        assert_eq!(roots.len(), 2);
        let two_sqrt3 = CasExpr::int(2) * CasExpr::int(3).sqrt();
        assert_equal(&roots[0], &two_sqrt3);
        assert_equal(&roots[1], &(-two_sqrt3));
        for r in &roots {
            assert_equal(&f.substitute("x", r), &CasExpr::zero());
        }
        // x² − 2 = 0 ⇒ ±√2 exactly (the /2a cancels the extracted factor).
        let g = x().pow(2) - CasExpr::int(2);
        let g_roots = solve(&g, "x").unwrap();
        assert_equal(&g_roots[0], &CasExpr::int(2).sqrt());
        // 2x² − 4x − 3 = 0 ⇒ 1 ± √10/2.
        let h = CasExpr::int(2) * x().pow(2) - CasExpr::int(4) * x() - CasExpr::int(3);
        for r in &solve(&h, "x").unwrap() {
            assert_equal(&h.substitute("x", r), &CasExpr::zero());
        }
    }

    #[test]
    fn solve_elementary_transcendental_equations() {
        let x = || v("x");
        // eˣ − 5 = 0 ⇒ ln 5 (certified: e^{ln 5} = 5 via the exp tower).
        let roots = solve(&(x().exp() - CasExpr::int(5)), "x").expect("solvable");
        assert_eq!(roots.len(), 1);
        assert_equal(&roots[0], &CasExpr::int(5).ln());
        // 2·e^{3x} − 8 = 0 ⇒ ln 4 / 3.
        let r2 = solve(
            &(CasExpr::int(2) * (CasExpr::int(3) * x()).exp() - CasExpr::int(8)),
            "x",
        )
        .expect("solvable");
        assert_equal(&r2[0], &(CasExpr::int(4).ln() / CasExpr::int(3)));
        // e^{x−1} − 1 = 0 ⇒ x = 1 (ln 1 folds to 0).
        let r3 = solve(&((x() - CasExpr::int(1)).exp() - CasExpr::int(1)), "x").expect("solvable");
        assert_equal(&r3[0], &CasExpr::int(1));
        // eˣ + 1 = 0 has no real root (exp > 0) — declined.
        assert!(solve(&(x().exp() + CasExpr::int(1)), "x").is_none());
        // ln roots (`ln x − 2`) are not yet certifiable (ln∘exp unreduced) — declined.
        assert!(solve(&(x().ln() - CasExpr::int(2)), "x").is_none());
        // A polynomial still routes to the polynomial solver.
        assert_eq!(
            solve(&(x().pow(2) - CasExpr::int(4)), "x").unwrap().len(),
            2
        );
    }

    #[test]
    fn solve_trigonometric_equations() {
        let x = || v("x");
        let pi = || v("pi");
        // 2sin x − 1 = 0 ⇒ x ∈ {π/6, 5π/6}; each root certifies against the equation.
        let s = solve(&(CasExpr::int(2) * x().sin() - CasExpr::int(1)), "x").expect("solvable");
        assert_eq!(s.len(), 2);
        for root in &s {
            let residual = evaluate_trig(
                &(CasExpr::int(2) * root.clone().sin() - CasExpr::int(1)),
            );
            assert_equal(&residual, &CasExpr::zero());
        }
        assert!(s.contains(&(CasExpr::rat(1, 6) * pi())));
        assert!(s.contains(&(CasExpr::rat(5, 6) * pi())));
        // tan x − 1 = 0 ⇒ {π/4, 5π/4}.
        let t = solve(&(x().tan() - CasExpr::int(1)), "x").unwrap();
        assert!(t.contains(&(CasExpr::rat(1, 4) * pi())));
        assert!(t.contains(&(CasExpr::rat(5, 4) * pi())));
        // 2sin x − 3 = 0 has no solution (|sin| ≤ 1) — declined.
        assert!(solve(&(CasExpr::int(2) * x().sin() - CasExpr::int(3)), "x").is_none());
    }

    #[test]
    fn solve_bivariate_polynomial_systems() {
        let x = || v("x");
        let y = || v("y");
        // Circle ∩ hyperbola: x²+y²=25, x²−y²=7 ⇒ (±4, ±3).
        let sols = solve_polynomial_system(
            &(x().pow(2) + y().pow(2) - CasExpr::int(25)),
            &(x().pow(2) - y().pow(2) - CasExpr::int(7)),
            "x",
            "y",
        )
        .expect("solvable");
        assert_eq!(sols.len(), 4);
        for (xr, yr) in &sols {
            // Each pair satisfies both equations.
            let on_circle = (xr.clone().pow(2) + yr.clone().pow(2)) - CasExpr::int(25);
            let on_hyper = (xr.clone().pow(2) - yr.clone().pow(2)) - CasExpr::int(7);
            assert_equal(&on_circle, &CasExpr::zero());
            assert_equal(&on_hyper, &CasExpr::zero());
        }
        // Parabola ∩ line: y=x², y=x ⇒ (0,0), (1,1).
        let pl = solve_polynomial_system(
            &(y() - x().pow(2)),
            &(y() - x()),
            "x",
            "y",
        )
        .expect("solvable");
        assert_eq!(pl.len(), 2);
        assert!(pl.contains(&(CasExpr::int(0), CasExpr::int(0))));
        assert!(pl.contains(&(CasExpr::int(1), CasExpr::int(1))));
        // A three-variable input is declined.
        assert!(
            solve_polynomial_system(&(x() + y() + v("z")), &(x() - y()), "x", "y").is_none()
        );
    }

    #[test]
    fn solve_quartic_via_factorization() {
        let x = || v("x");
        // x⁴ + 5x² + 4 = (x²+1)(x²+4): no rational roots, four complex roots ±I, ±2I.
        // Factorization over ℚ splits it into quadratics that solve() then solves; the
        // rational-imaginary roots certify via the I²=−1 fold in the zero-test.
        let quartic = x().pow(4) + CasExpr::int(5) * x().pow(2) + CasExpr::int(4);
        let roots = solve(&quartic, "x").expect("solvable via factorization");
        assert_eq!(roots.len(), 4);
        for r in &roots {
            assert_equal(&quartic.substitute("x", r), &CasExpr::zero());
        }
        // (x²−2)(x²−3) = x⁴ − 5x² + 6: four real irrational roots ±√2, ±√3. Each now
        // certifies on substitution via the sqrt(c)²→c fold in the zero-test.
        let real = x().pow(4) - CasExpr::int(5) * x().pow(2) + CasExpr::int(6);
        let real_roots = solve(&real, "x").expect("solvable");
        assert_eq!(real_roots.len(), 4);
        for r in &real_roots {
            assert_equal(&real.substitute("x", r), &CasExpr::zero());
        }
        // Mixed: (x−1)(x²+1) = x³ − x² + x − 1 → rational 1 plus ±I.
        let mixed = x().pow(3) - x().pow(2) + x() - CasExpr::int(1);
        let mixed_roots = solve(&mixed, "x").expect("solvable");
        assert_eq!(mixed_roots.len(), 3);
        for r in &mixed_roots {
            assert_equal(&mixed.substitute("x", r), &CasExpr::zero());
        }
    }

    #[test]
    fn integrate_log_atan_and_poly_log() {
        let x = || v("x");
        // Each certified by d/dx(answer) = integrand.
        for integrand in [
            x().ln(),                                             // ∫ ln x = x ln x − x
            x().atan(),                                           // ∫ atan x = x·atan x − ½ln(1+x²)
            x() * x().ln(),                                       // ∫ x ln x = ½x² ln x − ¼x²
            x().pow(2) * x().ln(),                                // ∫ x² ln x
            (CasExpr::int(3) * x() + CasExpr::int(1)) * x().ln(), // ∫ (3x+1) ln x
        ] {
            let result = integrate(&integrand, "x").expect("integrable");
            assert!(result.is_certified(), "not certified: ∫{integrand}");
            assert_equal(&result.antiderivative.differentiate("x"), &integrand);
        }
    }

    #[test]
    fn integrate_elementary_functions() {
        let x = || v("x");
        // Each certified by d/dx(answer) = integrand.
        for integrand in [
            x().exp(),                     // ∫ exp(x) = exp(x)
            x().sin(),                     // ∫ sin(x) = -cos(x)
            x().cos(),                     // ∫ cos(x) = sin(x)
            (CasExpr::int(3) * x()).exp(), // ∫ exp(3x) = (1/3)exp(3x)
            (CasExpr::int(2) * x()).cos(), // ∫ cos(2x) = (1/2)sin(2x)
            x().ln(),                      // ∫ ln(x) = x·ln(x) - x
        ] {
            let result = integrate(&integrand, "x").expect("elementary integral");
            assert!(result.is_certified(), "not certified: ∫{integrand}");
            assert_equal(&result.antiderivative.differentiate("x"), &integrand);
        }
    }

    #[test]
    fn integrate_polynomial_times_exponential() {
        let x = || v("x");
        // ∫ x·eˣ dx = (x−1)eˣ ; ∫ x²·eˣ = (x²−2x+2)eˣ — certified by differentiation.
        for integrand in [
            x() * x().exp(),
            x().pow(2) * x().exp(),
            (CasExpr::int(3) * x() + CasExpr::int(1)) * (CasExpr::int(2) * x()).exp(),
        ] {
            let result = integrate(&integrand, "x").expect("poly·exp integral");
            assert!(result.is_certified(), "not certified: ∫{integrand}");
            assert_equal(&result.antiderivative.differentiate("x"), &integrand);
        }
    }

    #[test]
    fn integrate_polynomial_times_trig() {
        let x = || v("x");
        // ∫ x·sin x, ∫ x²·cos x, ∫ (2x+1)·sin(3x) — certified by differentiation.
        for integrand in [
            x() * x().sin(),
            x().pow(2) * x().cos(),
            (CasExpr::int(2) * x() + CasExpr::int(1)) * (CasExpr::int(3) * x()).sin(),
        ] {
            let result = integrate(&integrand, "x").expect("poly·trig integral");
            assert!(result.is_certified(), "not certified: ∫{integrand}");
            assert_equal(&result.antiderivative.differentiate("x"), &integrand);
        }
    }

    #[test]
    fn integrate_trig_squares() {
        let x = || v("x");
        // ∫ sin²x, ∫ cos²x, ∫ sin²(2x) — certified via the Pythagorean identity.
        for integrand in [
            x().sin().pow(2),
            x().cos().pow(2),
            (CasExpr::int(2) * x()).sin().pow(2),
        ] {
            let result = integrate(&integrand, "x").expect("trig-square integral");
            assert!(result.is_certified(), "not certified: ∫{integrand}");
            assert_equal(&result.antiderivative.differentiate("x"), &integrand);
        }
    }

    #[test]
    fn integrate_exponential_times_sinusoid() {
        let x = || v("x");
        // ∫ eˣ·sin x, ∫ e^{2x}·cos x, ∫ x·eˣ·sin x, ∫ eˣ·cos(2x) — each recovered
        // by the coupled linear system and certified by differentiation.
        for integrand in [
            x().exp() * x().sin(),
            (CasExpr::int(2) * x()).exp() * x().cos(),
            x() * x().exp() * x().sin(),
            x().exp() * (CasExpr::int(2) * x()).cos(),
        ] {
            let result = integrate(&integrand, "x").expect("exp·trig integral");
            assert!(result.is_certified(), "not certified: ∫{integrand}");
            assert_equal(&result.antiderivative.differentiate("x"), &integrand);
        }
    }

    #[test]
    fn integrate_tangent() {
        let x = || v("x");
        // ∫ tan x = -ln(cos x); ∫ tan(3x) = -(1/3)ln(cos 3x). Certified via the
        // Euler fallback in `equal` (which folds tan into sin/cos).
        for integrand in [x().tan(), (CasExpr::int(3) * x()).tan()] {
            let result = integrate(&integrand, "x").expect("tangent integral");
            assert!(result.is_certified(), "not certified: ∫{integrand}");
            assert_equal(&result.antiderivative.differentiate("x"), &integrand);
        }
    }

    #[test]
    fn equal_is_sound_for_related_trig_atoms() {
        let x = || v("x");
        // Regression: the core atom test would report these TRUE identities as
        // `Certified{equal:false}` (a false proof) because it treats tan/sin/cos
        // and multiple angles as independent atoms. The Euler fallback fixes it.
        let identities = [
            (x().tan(), x().sin() / x().cos()),
            (
                (CasExpr::int(2) * x()).cos(),
                CasExpr::int(2) * x().cos().pow(2) - CasExpr::int(1),
            ),
            (
                (CasExpr::int(2) * x()).sin(),
                CasExpr::int(2) * x().sin() * x().cos(),
            ),
        ];
        for (a, b) in identities {
            assert!(
                matches!(equal(&a, &b), ZeroTest::Certified { equal: true, .. }),
                "identity not certified equal: {a} = {b}",
            );
        }
        // Genuinely unequal trig expressions must NOT be reported equal (and are
        // still soundly certified unequal, not silently downgraded).
        for (a, b) in [
            (x().tan(), x().sin()),
            ((CasExpr::int(2) * x()).cos(), x().cos()),
        ] {
            assert!(
                matches!(equal(&a, &b), ZeroTest::Certified { equal: false, .. }),
                "unequal pair not certified unequal: {a} vs {b}",
            );
        }
    }

    #[test]
    fn integrate_trig_monomial_odd_power() {
        let x = || v("x");
        // ∫ sin x·cos x, ∫ sin³x, ∫ cos³x, ∫ sin²x·cos x, ∫ sin x·cos²x — the
        // odd-power substitution reduces each to a polynomial; certified by
        // differentiation.
        for integrand in [
            x().sin() * x().cos(),
            x().sin().pow(3),
            x().cos().pow(3),
            x().sin().pow(2) * x().cos(),
            x().sin() * x().cos().pow(2),
        ] {
            let result = integrate(&integrand, "x").expect("trig-monomial integral");
            assert!(result.is_certified(), "not certified: ∫{integrand}");
            assert_equal(&result.antiderivative.differentiate("x"), &integrand);
        }
    }

    #[test]
    fn integrate_declines_nonlinear_argument() {
        // ∫ sin(x²) dx has no elementary closed form: honest None.
        assert!(integrate(&v("x").pow(2).sin(), "x").is_none());
    }

    #[test]
    fn repeated_differentiation_stays_clean() {
        let x = || v("x");
        // dⁿ/dxⁿ folds the product/chain-rule `·1`/`·0` noise each step, so it
        // neither blows up nor leaks — and stays value-correct.
        assert_equal(&x().sin().differentiate_n("x", 3), &(-x().cos()));
        assert_equal(&x().sin().differentiate_n("x", 4), &x().sin());
        // d²/dx² x³ = 6x, d³/dx³ x⁴ = 24x — folded to a single constant factor.
        assert_eq!(
            x().pow(3).differentiate_n("x", 2),
            CasExpr::int(6) * x(),
        );
        assert_equal(&x().pow(4).differentiate_n("x", 3), &(CasExpr::int(24) * x()));
        // exp is a fixed point.
        assert_equal(&x().exp().differentiate_n("x", 5), &x().exp());
    }

    #[test]
    fn elementary_function_derivatives() {
        let x = || v("x");
        // d/dx exp(x) = exp(x)
        assert_equal(&x().exp().differentiate("x"), &x().exp());
        // d/dx sin(x) = cos(x)
        assert_equal(&x().sin().differentiate("x"), &x().cos());
        // d/dx cos(x) = -sin(x)
        assert_equal(&x().cos().differentiate("x"), &(-x().sin()));
        // d/dx ln(x) = 1/x
        assert_equal(&x().ln().differentiate("x"), &(CasExpr::int(1) / x()));
        // d/dx atan(x) = 1/(1+x²)
        assert_equal(
            &x().atan().differentiate("x"),
            &(CasExpr::int(1) / (CasExpr::int(1) + x().pow(2))),
        );
    }

    #[test]
    fn chain_rule_on_elementary_functions() {
        let x = || v("x");
        // d/dx sin(x²) = 2x·cos(x²)
        assert_equal(
            &x().pow(2).sin().differentiate("x"),
            &(CasExpr::int(2) * x() * x().pow(2).cos()),
        );
        // d/dx exp(3x) = 3·exp(3x)
        assert_equal(
            &(CasExpr::int(3) * x()).exp().differentiate("x"),
            &(CasExpr::int(3) * (CasExpr::int(3) * x()).exp()),
        );
        // d/dx ln(x²+1) = 2x/(x²+1)
        assert_equal(
            &(x().pow(2) + CasExpr::int(1)).ln().differentiate("x"),
            &((CasExpr::int(2) * x()) / (x().pow(2) + CasExpr::int(1))),
        );
    }

    #[test]
    fn overflow_is_reported_as_unknown_not_wrong() {
        // 10¹⁸ · 10¹⁸ · 10¹⁸ = 10⁵⁴ overflows i128 (~1.7·10³⁸): the zero-test
        // must decline to Unknown, never return a wrong decision.
        let big = CasExpr::int(1_000_000_000_000_000_000);
        let cube = CasExpr::Mul(vec![big.clone(), big.clone(), big]);
        match equal(&cube, &CasExpr::zero()) {
            ZeroTest::Unknown => {}
            ZeroTest::Certified { .. } => panic!("expected Unknown on overflow"),
        }
    }
}
