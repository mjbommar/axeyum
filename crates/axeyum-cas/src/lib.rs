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

pub mod groebner;
mod factor_int;
mod gosper;
mod matrix;
pub mod mvpoly;
pub mod ntheory;
pub mod ntheory_advanced;
mod ratint;
mod series;
pub mod stats;

pub use factor_int::{factor_expr, factor_univariate_over_q};
pub use gosper::{geometric_power, gosper_sum};
pub use groebner::{groebner_basis, ideal_contains, reduce};
pub use matrix::Matrix;
pub use mvpoly::MvPoly;
pub use series::{series, series_at};

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
            result = result.differentiate(var);
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
        CasExpr::Unary(func, arg) => Some(RatFunc::from_poly(MultiPoly::single_var(&atom_name(
            func.name(),
            arg,
        )))),
    }
}

/// A collision-resistant variable name standing for a transcendental atom
/// `head(arg)`, keyed by `arg`'s canonical rendering. The `\0` prefix cannot occur
/// in a user variable name.
fn atom_name(head: &str, arg: &CasExpr) -> String {
    format!("\0{head}:{}", arg.render(0))
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
#[must_use]
pub fn equal(a: &CasExpr, b: &CasExpr) -> ZeroTest {
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
    Some(CasExpr::Const(coeffs.get(n).copied().unwrap_or_else(Rational::zero)))
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

/// Solve `expr = 0` for `var` over a univariate polynomial: returns the distinct
/// real roots. Rational roots are exact; a leftover real quadratic is solved by
/// the quadratic formula (rational when the discriminant is a perfect square,
/// else a symbolic `sqrt`). Complex roots and degree-≥3 irreducible factors are
/// omitted. `None` if `expr` is not a univariate polynomial.
#[must_use]
pub fn solve(expr: &CasExpr, var: &str) -> Option<Vec<CasExpr>> {
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
        remaining =
            poly::rat_exact_div(&remaining, &[root.checked_neg()?, Rational::integer(1)])?;
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
        if let Some(root) = rational_sqrt(disc) {
            for sign in [Rational::integer(1), Rational::integer(-1)] {
                out.push(CasExpr::Const(
                    neg_b_over.checked_add(sign.checked_mul(root)?.checked_div(two_a)?)?,
                ));
            }
        } else {
            let sqrt_disc = CasExpr::Const(disc).sqrt();
            for sign in [CasExpr::int(1), CasExpr::int(-1)] {
                out.push(
                    CasExpr::Const(neg_b_over) + sign * (sqrt_disc.clone() / CasExpr::Const(two_a)),
                );
            }
        }
    } else {
        // Complex conjugate roots: (−b/2a) ± (√(−disc)/2a)·I.
        let neg_disc = Rational::zero().checked_sub(disc)?;
        let imag_unit = CasExpr::var("I");
        for sign in [1_i128, -1] {
            let imaginary = if let Some(root) = rational_sqrt(neg_disc) {
                scaled_term(
                    Rational::integer(sign).checked_mul(root)?.checked_div(two_a)?,
                    imag_unit.clone(),
                )
            } else {
                CasExpr::int(sign)
                    * (CasExpr::Const(neg_disc).sqrt() / CasExpr::Const(two_a))
                    * imag_unit.clone()
            };
            out.push(if neg_b_over.is_zero() {
                imaginary
            } else {
                CasExpr::Const(neg_b_over) + imaginary
            });
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

/// The closed form of `∑_{k=0}^{var−1} f(k)` for a polynomial summand `f`, i.e. the
/// **discrete antiderivative** `S` with `S(var+1) − S(var) = f(var)` and `S(0)=0`
/// (so `∑_{k=0}^{n−1} f(k) = S(n)`). Solved as one exact linear system; **certified**
/// by the telescoping zero-test `S(var+1) − S(var) − f ≡ 0`. E.g. `∑ k = (n²−n)/2`,
/// `∑ 1 = n`. `None` if `f` is not a univariate polynomial or on overflow.
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

/// Partial-fraction decomposition of a univariate rational function whose
/// denominator splits into **distinct** rational linear factors: `p/q =
/// (polynomial part) + Σ Aᵢ/(x − rᵢ)` with residues `Aᵢ = rem(rᵢ)/q′(rᵢ)`. Returns
/// the decomposition, **certified** equal to the input (re-combination zero-test),
/// or `None` if the denominator has a repeated or non-rational root, or `expr` is
/// not a univariate rational function.
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
    let roots = ratint::rational_roots(&den)?;
    if roots.len() != deg_den {
        return None; // repeated or non-rational roots — not distinct linear
    }
    let den_deriv = poly::rat_derivative(&den)?;
    let mut parts: Vec<CasExpr> = Vec::new();
    if !ratint::is_zero(&quotient) {
        parts.push(MultiPoly::from_univariate(var, &quotient).to_expr());
    }
    for root in roots {
        let residue = poly::eval_rat_poly(&remainder, root)?
            .checked_div(poly::eval_rat_poly(&den_deriv, root)?)?;
        // Aᵢ / (x − rᵢ)
        let denom = CasExpr::var(var) - CasExpr::Const(root);
        parts.push(CasExpr::Const(residue) / denom);
    }
    let result = match parts.len() {
        0 => CasExpr::zero(),
        1 => parts.into_iter().next()?,
        _ => CasExpr::Add(parts),
    };
    match equal(&result, expr) {
        ZeroTest::Certified { equal: true, .. } => Some(result),
        _ => None,
    }
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
    for candidate in [cancel(expr), expand(expr)].into_iter().flatten() {
        let size = node_count(&candidate);
        if size < best_size {
            best = candidate;
            best_size = size;
        }
    }
    best
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
            row.push(if i == j { entry - lambda.clone() } else { entry });
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
        let flat: Vec<Rational> = matrix_to_rationals(&current)?.into_iter().flatten().collect();
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
        CasExpr::Mul(factors) => CasExpr::Mul(factors.iter().map(simplify_radicals).collect()),
        CasExpr::Neg(inner) => CasExpr::Neg(Box::new(simplify_radicals(inner))),
        CasExpr::Div(numerator, denominator) => CasExpr::Div(
            Box::new(simplify_radicals(numerator)),
            Box::new(simplify_radicals(denominator)),
        ),
        CasExpr::Pow(base, exponent) => {
            CasExpr::Pow(Box::new(simplify_radicals(base)), *exponent)
        }
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
            if matches!(equal(&cosine, &CasExpr::zero()), ZeroTest::Certified { equal: true, .. }) {
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
            trig_special_value(*func, &inner).unwrap_or_else(|| CasExpr::Unary(*func, Box::new(inner)))
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

/// Numerically approximate an expression as an `f64`, given `bindings` for its free
/// variables (each `(name, value)`). Rational constants are exact-to-`f64`; the
/// transcendental heads map to the corresponding `f64` functions.
///
/// This is a **compute** operation — the returned float is an approximation, not a
/// certified value — so it is the bridge from an exact symbolic result to a decimal
/// (e.g. `evalf(√2) ≈ 1.4142…`). Returns `None` for an unbound free variable (the
/// reserved imaginary unit `I` included — the result would be complex) or a domain
/// error is not checked (e.g. `ln` of a negative yields a `NaN`/`f64` per the std
/// library). Closed expressions need no bindings.
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
            .map(|&(_, value)| value),
        CasExpr::Add(terms) => terms.iter().try_fold(0.0, |acc, term| Some(acc + evalf(term, bindings)?)),
        CasExpr::Mul(factors) => factors
            .iter()
            .try_fold(1.0, |acc, factor| Some(acc * evalf(factor, bindings)?)),
        CasExpr::Neg(inner) => Some(-evalf(inner, bindings)?),
        CasExpr::Div(numerator, denominator) => {
            Some(evalf(numerator, bindings)? / evalf(denominator, bindings)?)
        }
        CasExpr::Pow(base, exponent) => Some(evalf(base, bindings)?.powi(i32::try_from(*exponent).ok()?)),
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
            // den(a) = 0: an indeterminate 0/0 (cancel) or a pole.
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
                core::cmp::Ordering::Greater => None, // ±∞
            }
        }
    }
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
    if rf.den == MultiPoly::constant(Rational::integer(1)) {
        Some(num)
    } else {
        Some(CasExpr::Div(Box::new(num), Box::new(rf.den.to_expr())))
    }
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
    if rf.den == MultiPoly::constant(Rational::integer(1)) {
        Some(num)
    } else {
        Some(CasExpr::Div(Box::new(num), Box::new(rf.den.to_expr())))
    }
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
        integrate_poly_times_sinusoid(expr, var),
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
    let value = simplify(&(at_upper - at_lower));
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
    let antiderivative = scaled_term(Rational::new(1, 2), CasExpr::var(var))
        + scaled_term(cross_coeff, product);
    Some(scaled_term(coeff, antiderivative))
}

/// Integrate `p(x)·e^(a·x+b)` for a polynomial `p` and a linear exponent:
/// `∫ p·e^(ax+b) = Q·e^(ax+b)` where `Q` solves `Q′ + a·Q = p` (one exact linear
/// system). Covers `∫ x·eˣ = (x−1)eˣ`, `∫ x²·eˣ = (x²−2x+2)eˣ`, etc. `None`
/// outside this shape; certified downstream by differentiate-and-check.
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
        // atan / tan / sqrt closed forms are later slices.
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
        let ln = CasExpr::Unary(UnaryFunc::Ln, Box::new(MultiPoly::from_univariate(var, &dd).to_expr()));
        return Some(scaled_term(coeff, ln));
    }
    // Degree ≥ 2: Rothstein–Trager. ∫ C/D₁ = Σ cᵢ·ln(vᵢ), cᵢ the rational roots
    // of Res_t, vᵢ = gcd(C − cᵢ·D₁', D₁).
    if let Some(terms) = ratint::log_terms(&cc, &dd) {
        let mut sum: Vec<CasExpr> = Vec::with_capacity(terms.len());
        for (coeff, v_poly) in terms {
            let ln = CasExpr::Unary(UnaryFunc::Ln, Box::new(MultiPoly::from_univariate(var, &v_poly).to_expr()));
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
        let ln = CasExpr::Unary(UnaryFunc::Ln, Box::new(MultiPoly::from_univariate(var, dd).to_expr()));
        parts.push(scaled_term(ln_coeff, ln));
    }
    // atan term: coefficient (2a·c₀ − b·c₁)/(a·s), argument (2a·x + b)/s.
    let atan_coeff =
        two_a.checked_mul(c0)?.checked_sub(b.checked_mul(c1)?)?.checked_div(a.checked_mul(s)?)?;
    if !atan_coeff.is_zero() {
        let arg = MultiPoly::from_univariate(var, &[b.checked_div(s)?, two_a.checked_div(s)?])
            .to_expr();
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
        assert_equal(&cancel(&g).expect("rational"), &(v("x") * v("y") + v("y").pow(2)));
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
        let sol2 = dsolve_inhomogeneous(&[ig(-1), ig(0), ig(1)], &x().pow(2), "x").expect("solvable");
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
    fn limits_of_rational_functions() {
        let x = || v("x");
        let at = |n: i128| LimitPoint::Finite(Rational::integer(n));
        // continuous: lim_{x→1} (x+1)/(x−2) = −2
        assert_equal(
            &limit(&((x() + CasExpr::int(1)) / (x() - CasExpr::int(2))), "x", at(1)).unwrap(),
            &CasExpr::int(-2),
        );
        // 0/0 via cancellation: lim_{x→2} (x²−4)/(x−2) = 4
        assert_equal(
            &limit(&((x().pow(2) - CasExpr::int(4)) / (x() - CasExpr::int(2))), "x", at(2)).unwrap(),
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
        let d = definite_integrate(&(CasExpr::int(3) * x().pow(2)), "x", &CasExpr::int(0), &CasExpr::int(1))
            .unwrap();
        assert!(d.is_certified());
        assert_equal(&d.value, &CasExpr::int(1));

        // ∫₁³ (2x) dx = 9 − 1 = 8.
        let d2 = definite_integrate(&(CasExpr::int(2) * x()), "x", &CasExpr::int(1), &CasExpr::int(3))
            .unwrap();
        assert!(d2.is_certified());
        assert_equal(&d2.value, &CasExpr::int(8));

        // Reversed bounds negate: ∫₃¹ 2x dx = −8.
        let d3 = definite_integrate(&(CasExpr::int(2) * x()), "x", &CasExpr::int(3), &CasExpr::int(1))
            .unwrap();
        assert_equal(&d3.value, &CasExpr::int(-8));
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
        assert_equal(&div, &(CasExpr::int(2) * x() + CasExpr::int(2) * y() + CasExpr::int(2) * z()));

        // A gradient field (−y, x, 0)? curl = (0,0,2). Standard example curl of
        // (−y, x, 0) = (0, 0, 2).
        let rotor = curl(&[-y(), x(), CasExpr::zero()], &["x", "y", "z"]).unwrap();
        assert_equal(&rotor[0], &CasExpr::zero());
        assert_equal(&rotor[1], &CasExpr::zero());
        assert_equal(&rotor[2], &CasExpr::int(2));
    }

    #[test]
    fn radical_simplification_extracts_squares() {
        // √12 = 2√3.
        let s = simplify_radicals(&CasExpr::int(12).sqrt());
        assert_equal(&s, &(CasExpr::int(2) * CasExpr::int(3).sqrt()));
        // √9 = 3 (perfect square → rational).
        assert_equal(&simplify_radicals(&CasExpr::int(9).sqrt()), &CasExpr::int(3));
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
        assert_equal(&simplify_radicals(&CasExpr::int(2).sqrt()), &CasExpr::int(2).sqrt());
        // Negative radicand is left symbolic (no real simplification).
        let neg = CasExpr::int(-3).sqrt();
        assert_equal(&simplify_radicals(&neg), &neg);
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
        assert_equal(&sample_standard_deviation(&small).unwrap(), &CasExpr::int(1));
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
    fn exact_trig_values() {
        let pi = || v("pi");
        let sin = |c: CasExpr| evaluate_trig(&c.sin());
        let cos = |c: CasExpr| evaluate_trig(&c.cos());
        let tan = |c: CasExpr| evaluate_trig(&c.tan());
        // Standard unit-circle values.
        assert_equal(&sin(pi() / CasExpr::int(6)), &CasExpr::rat(1, 2));
        assert_equal(&cos(pi() / CasExpr::int(3)), &CasExpr::rat(1, 2));
        assert_equal(&sin(pi() / CasExpr::int(4)), &(CasExpr::rat(1, 2) * CasExpr::int(2).sqrt()));
        assert_equal(&cos(pi() / CasExpr::int(6)), &(CasExpr::rat(1, 2) * CasExpr::int(3).sqrt()));
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
            &(CasExpr::rat(1, 4) * CasExpr::int(6).sqrt() - CasExpr::rat(1, 4) * CasExpr::int(2).sqrt()),
        );
        // Pythagorean check on the exact values: sin²(π/5? no) — use π/6: (1/2)²+(√3/2)²=1.
        let s = sin(pi() / CasExpr::int(6));
        let c = cos(pi() / CasExpr::int(6));
        assert_equal(&(s.pow(2) + c.pow(2)), &CasExpr::int(1));
        // tan(π/2) is a pole → left unevaluated.
        assert!(matches!(tan(pi() / CasExpr::int(2)), CasExpr::Unary(UnaryFunc::Tan, _)));
        // A non-special angle (π/5) is left unevaluated.
        assert!(matches!(sin(pi() / CasExpr::int(5)), CasExpr::Unary(UnaryFunc::Sin, _)));
    }

    #[test]
    fn evalf_approximates() {
        let x = || v("x");
        // √2 ≈ 1.4142…
        assert!((evalf(&CasExpr::int(2).sqrt(), &[]).unwrap() - std::f64::consts::SQRT_2).abs() < 1e-12);
        // exp(0) = 1, sin(0) = 0.
        assert!((evalf(&CasExpr::int(0).exp(), &[]).unwrap() - 1.0).abs() < 1e-12);
        // A bound variable: 2x² + 1 at x = 3 → 19.
        assert!((evalf(&(CasExpr::int(2) * x().pow(2) + CasExpr::int(1)), &[("x", 3.0)]).unwrap() - 19.0).abs() < 1e-12);
        // stddev {1,2,3} = (1/3)√6 ≈ 0.8165.
        let data: Vec<Rational> = [1, 2, 3].into_iter().map(Rational::integer).collect();
        let sd = standard_deviation(&data).unwrap();
        assert!((evalf(&sd, &[]).unwrap() - (6.0_f64).sqrt() / 3.0).abs() < 1e-12);
        // Unbound free variable → None.
        assert!(evalf(&x(), &[]).is_none());
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
        assert_equal(&norm(&[CasExpr::int(3), CasExpr::int(4)]).unwrap(), &CasExpr::int(5));
        assert_equal(&norm(&[CasExpr::int(1), CasExpr::int(1)]).unwrap(), &CasExpr::int(2).sqrt());
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
    fn cyclotomic_polynomials() {
        let x = || v("x");
        // Known small cases.
        assert_equal(&cyclotomic_polynomial(1, "x").unwrap(), &(x() - CasExpr::int(1)));
        assert_equal(&cyclotomic_polynomial(2, "x").unwrap(), &(x() + CasExpr::int(1)));
        assert_equal(
            &cyclotomic_polynomial(3, "x").unwrap(),
            &(x().pow(2) + x() + CasExpr::int(1)),
        );
        assert_equal(&cyclotomic_polynomial(4, "x").unwrap(), &(x().pow(2) + CasExpr::int(1)));
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
            &resultant(&(x().pow(2) - CasExpr::int(1)), &(x() - CasExpr::int(1)), "x").unwrap(),
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
        let cubic = x().pow(3) - CasExpr::int(4) * x().pow(2) + CasExpr::int(5) * x() - CasExpr::int(2);
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
    fn polynomial_gcd_and_division() {
        let x = || v("x");
        // gcd(x²−1, x²−2x+1) = x−1
        assert_equal(
            &poly_gcd(&(x().pow(2) - CasExpr::int(1)), &(x().pow(2) - CasExpr::int(2) * x() + CasExpr::int(1)), "x").unwrap(),
            &(x() - CasExpr::int(1)),
        );
        // (x³−1) = (x²+x+1)(x−1) + 0
        let (q, r) = poly_div(&(x().pow(3) - CasExpr::int(1)), &(x() - CasExpr::int(1)), "x").unwrap();
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
        assert_equal(&factor(&h, "x").expect("factorable"), &(x() - CasExpr::int(1)).pow(2));
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
        assert_equal(&real_part(&(z.clone() * conjugate(&z))).unwrap(), &CasExpr::int(25));
        assert_equal(&imaginary_part(&(z.clone() * conjugate(&z))).unwrap(), &CasExpr::zero());
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
            assert_equal(&(v("x").pow(2) + CasExpr::int(1)).substitute("x", &r), &CasExpr::zero());
        }
    }

    #[test]
    fn solve_complex_roots() {
        let x = || v("x");
        let strs = |e: CasExpr| -> Vec<String> {
            solve(&e, "x").unwrap().iter().map(ToString::to_string).collect()
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
    fn integrate_elementary_functions() {
        let x = || v("x");
        // Each certified by d/dx(answer) = integrand.
        for integrand in [
            x().exp(),                              // ∫ exp(x) = exp(x)
            x().sin(),                              // ∫ sin(x) = -cos(x)
            x().cos(),                              // ∫ cos(x) = sin(x)
            (CasExpr::int(3) * x()).exp(),          // ∫ exp(3x) = (1/3)exp(3x)
            (CasExpr::int(2) * x()).cos(),          // ∫ cos(2x) = (1/2)sin(2x)
            x().ln(),                               // ∫ ln(x) = x·ln(x) - x
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
    fn integrate_declines_nonlinear_argument() {
        // ∫ sin(x²) dx has no elementary closed form: honest None.
        assert!(integrate(&v("x").pow(2).sin(), "x").is_none());
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
