//! Exact multivariate polynomials over ℚ and their core algorithms.
//!
//! This module gives the crate a self-contained **sparse multivariate
//! polynomial** [`MvPoly`] with exact [`Rational`] coefficients, together with
//! the algorithms `SymPy`'s `polys` package provides at the multivariate level:
//! ring arithmetic, exact multivariate long division, and — the correctness
//! critical piece the crate previously lacked — **multivariate GCD**.
//!
//! The univariate GCD already available through `axeyum_ir::poly::rat_gcd` only
//! reduces univariate rational functions to lowest terms. A multivariate GCD is
//! what unlocks multivariate `cancel`, `factor`, and partial fractions, so this
//! module is the substrate those later transforms build on.
//!
//! # Representation
//!
//! An [`MvPoly`] is a canonical map from a [`Monomial`] (a sorted variable →
//! exponent map, exponents all `> 0`) to a nonzero [`Rational`] coefficient.
//! Because the form is canonical, structural equality is value equality and
//! [`MvPoly::is_zero`] is exact.
//!
//! # Monomial order
//!
//! Division and leading-term selection use the **pure lexicographic order**
//! (`lex`): variables are ranked alphabetically ascending, with the
//! alphabetically-*first* variable the most significant. Monomial `a > b` iff,
//! at the first variable (scanning most-significant-first) where their exponents
//! differ, `a` has the larger exponent. `lex` is a well-order on the monomials in
//! finitely many variables, which is what makes the division loop terminate.
//!
//! # Overflow
//!
//! All arithmetic is overflow-safe: every fallible operation returns `None` on
//! `i128` coefficient or `u32` exponent overflow rather than panicking. No
//! `unsafe`, no `unwrap`/`expect` on fallible paths.
//!
//! The one algorithm whose *intermediates* outgrow `i128` on inputs whose
//! coefficients and answer both fit comfortably is the GCD: a pseudo-remainder
//! sequence swells by a factor of the leading coefficient at every degree step.
//! [`MvPoly::gcd`] therefore runs in the unbounded-integer ring of the private
//! `big` submodule and converts only the answer back, so a declined GCD is now a
//! statement about the *result*, never about the scratch space. The bounded
//! `Copy` coefficient type, and the checked contract above, are unchanged for
//! every other operation.

pub(crate) mod big;

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::Rational;

use crate::CasExpr;
use big::BigPoly;

/// A monomial: a product of variable powers such as `x²·y`.
///
/// Canonical: every stored exponent is `> 0` and variables are kept sorted, so
/// structural equality is value equality. The empty monomial denotes the
/// constant term `1`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Monomial {
    powers: BTreeMap<String, u32>,
}

impl Monomial {
    /// The constant monomial `1` (no variables).
    #[must_use]
    pub fn one() -> Self {
        Monomial {
            powers: BTreeMap::new(),
        }
    }

    /// Build a monomial from `(variable, exponent)` pairs.
    ///
    /// Zero exponents are dropped and repeated variables have their exponents
    /// summed (saturating, so an astronomically large duplicate exponent cannot
    /// panic). The result is canonical.
    #[must_use]
    pub fn from_powers(factors: &[(&str, u32)]) -> Self {
        let mut powers: BTreeMap<String, u32> = BTreeMap::new();
        for (name, exp) in factors {
            if *exp == 0 {
                continue;
            }
            let slot = powers.entry((*name).to_owned()).or_insert(0);
            *slot = slot.saturating_add(*exp);
        }
        Monomial { powers }
    }

    /// The total degree (sum of exponents); the constant monomial has degree `0`.
    #[must_use]
    pub fn total_degree(&self) -> u64 {
        self.powers.values().map(|&exp| u64::from(exp)).sum()
    }

    /// The exponent of `var` in this monomial (`0` if absent).
    #[must_use]
    pub fn exponent_of(&self, var: &str) -> u32 {
        self.powers.get(var).copied().unwrap_or(0)
    }

    /// The `(variable, exponent)` pairs in ascending variable order; every
    /// exponent is `> 0`. The constant monomial yields an empty iterator.
    pub fn powers(&self) -> impl Iterator<Item = (&str, u32)> {
        self.powers.iter().map(|(name, exp)| (name.as_str(), *exp))
    }

    /// The product of two monomials (add exponents), or `None` on `u32` exponent
    /// overflow.
    fn mul(&self, other: &Monomial) -> Option<Monomial> {
        let mut powers = self.powers.clone();
        for (var, exp) in &other.powers {
            let slot = powers.entry(var.clone()).or_insert(0);
            *slot = slot.checked_add(*exp)?;
        }
        Some(Monomial { powers })
    }

    /// The quotient `self / divisor` as a monomial, or `None` when `divisor` does
    /// not divide `self` (some divisor exponent exceeds this monomial's).
    fn checked_div(&self, divisor: &Monomial) -> Option<Monomial> {
        for (var, exp) in &divisor.powers {
            if self.exponent_of(var) < *exp {
                return None;
            }
        }
        let mut powers: BTreeMap<String, u32> = BTreeMap::new();
        for (var, exp) in &self.powers {
            let reduced = exp - divisor.exponent_of(var);
            if reduced > 0 {
                powers.insert(var.clone(), reduced);
            }
        }
        Some(Monomial { powers })
    }

    /// Compare two monomials under the pure lexicographic order documented at the
    /// module level (alphabetically-first variable most significant).
    fn lex_cmp(&self, other: &Monomial) -> Ordering {
        let mut vars: BTreeSet<&str> = BTreeSet::new();
        vars.extend(self.powers.keys().map(String::as_str));
        vars.extend(other.powers.keys().map(String::as_str));
        for var in vars {
            let mine = self.exponent_of(var);
            let theirs = other.exponent_of(var);
            match mine.cmp(&theirs) {
                Ordering::Equal => {}
                unequal => return unequal,
            }
        }
        Ordering::Equal
    }
}

/// What one [`MvPoly::gcd_cost`] call observed about the coefficients it passed
/// through. Widths are in bits of the largest coefficient *magnitude*.
///
/// The reference value is **127**: an `i128` numerator holds no more than that,
/// so `peak_bits > 127` means the sequence could not have been run in this
/// crate's bounded coefficient type, whatever the algorithm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct GcdCost {
    /// The widest coefficient of either input.
    pub input_bits: u64,
    /// The widest coefficient reached anywhere in the remainder sequence.
    pub peak_bits: u64,
    /// The widest coefficient the sequence would reach **without** the per-step
    /// content division — the growth the crate's previous, `i128`-bounded
    /// primitive PRS actually ran into on the same inputs.
    ///
    /// A value above `127` is a proof that the old implementation could not have
    /// finished this GCD: it is what that code computed, measured in a type wide
    /// enough to hold it.
    pub legacy_peak_bits: u64,
    /// The widest coefficient of the answer.
    pub result_bits: u64,
    /// Pseudo-remainder steps taken across the whole recursion.
    pub steps: u64,
    /// Whether the answer converts back into `i128` rationals — i.e. whether
    /// [`MvPoly::gcd`] returns `Some` for the same inputs.
    pub fits_i128: bool,
}

/// A sparse multivariate polynomial over ℚ in canonical form.
///
/// The terms are a map from [`Monomial`] to a nonzero [`Rational`] coefficient;
/// zero-coefficient terms are never stored. Equality of two `MvPoly` values is
/// therefore exact value equality.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MvPoly {
    terms: BTreeMap<Monomial, Rational>,
}

impl MvPoly {
    // --- Construction -------------------------------------------------------

    /// The zero polynomial.
    #[must_use]
    pub fn zero() -> Self {
        MvPoly {
            terms: BTreeMap::new(),
        }
    }

    /// A constant polynomial (the zero polynomial when `value` is zero).
    #[must_use]
    pub fn constant(value: Rational) -> Self {
        MvPoly::single_term(Monomial::one(), value)
    }

    /// The degree-one polynomial in a single variable `name`.
    #[must_use]
    pub fn var(name: &str) -> Self {
        MvPoly::single_term(Monomial::from_powers(&[(name, 1)]), Rational::integer(1))
    }

    /// Build a polynomial from `(monomial, coefficient)` pairs, combining like
    /// monomials and dropping zero coefficients. `None` on `i128` overflow while
    /// combining coefficients.
    pub fn from_terms<I>(terms: I) -> Option<MvPoly>
    where
        I: IntoIterator<Item = (Monomial, Rational)>,
    {
        let mut result = MvPoly::zero();
        for (mono, coeff) in terms {
            result = result.add(&MvPoly::single_term(mono, coeff))?;
        }
        Some(result)
    }

    /// A single-term polynomial (the zero polynomial when `coeff` is zero).
    #[must_use]
    fn single_term(mono: Monomial, coeff: Rational) -> MvPoly {
        let mut terms = BTreeMap::new();
        if !coeff.is_zero() {
            terms.insert(mono, coeff);
        }
        MvPoly { terms }
    }

    // --- Accessors ----------------------------------------------------------

    /// Returns `true` if this is the zero polynomial.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The number of stored `(monomial, coefficient)` terms.
    ///
    /// Deliberately **not** named `len`: `is_zero` is already the emptiness
    /// predicate, and the count exists so callers can impose a size ceiling on
    /// an expansion (a product of two dense polynomials squares the term count),
    /// not to make `MvPoly` look like a collection.
    #[must_use]
    pub fn term_count(&self) -> usize {
        self.terms.len()
    }

    /// The stored `(monomial, coefficient)` terms in ascending [`Monomial`]
    /// order.
    ///
    /// The order is the `BTreeMap` key order, so it is canonical and
    /// deterministic: equal polynomials yield identical sequences. Coefficients
    /// are always nonzero. This is the accessor a certificate emitter uses to
    /// serialize the polynomial normal form.
    pub fn terms(&self) -> impl Iterator<Item = (&Monomial, &Rational)> {
        self.terms.iter()
    }

    /// The set of variables occurring in this polynomial.
    #[must_use]
    pub fn variables(&self) -> BTreeSet<String> {
        let mut vars = BTreeSet::new();
        for mono in self.terms.keys() {
            for var in mono.powers.keys() {
                vars.insert(var.clone());
            }
        }
        vars
    }

    /// The degree of `var` in this polynomial (the largest exponent of `var`
    /// across all terms); `0` for the zero polynomial or a polynomial free of
    /// `var`.
    #[must_use]
    pub fn degree_in(&self, var: &str) -> u32 {
        self.terms
            .keys()
            .map(|mono| mono.exponent_of(var))
            .max()
            .unwrap_or(0)
    }

    /// The total degree (the largest monomial total degree); `0` for the zero
    /// polynomial and for a nonzero constant.
    #[must_use]
    pub fn total_degree(&self) -> u64 {
        self.terms
            .keys()
            .map(Monomial::total_degree)
            .max()
            .unwrap_or(0)
    }

    /// The leading coefficient of this polynomial viewed as univariate in
    /// `main_var`: the coefficient (itself an [`MvPoly`] over the remaining
    /// variables) of the highest power of `main_var`. The zero polynomial yields
    /// the zero polynomial.
    #[must_use]
    pub fn leading_coeff(&self, main_var: &str) -> MvPoly {
        self.coefficient_of(main_var, self.degree_in(main_var))
    }

    /// The greatest monomial present under the `lex` order, or `None` if this is
    /// the zero polynomial.
    fn leading_monomial(&self) -> Option<Monomial> {
        self.terms
            .keys()
            .max_by(|left, right| left.lex_cmp(right))
            .cloned()
    }

    /// The `lex`-leading `(monomial, coefficient)` pair, or `None` if zero.
    fn leading_term(&self) -> Option<(Monomial, Rational)> {
        let mono = self.leading_monomial()?;
        let coeff = *self.terms.get(&mono)?;
        Some((mono, coeff))
    }

    /// The coefficient of `main_var^exp`, returned as an [`MvPoly`] over the
    /// remaining variables (with `main_var` stripped from each monomial).
    fn coefficient_of(&self, main_var: &str, exp: u32) -> MvPoly {
        let mut result = MvPoly::zero();
        for (mono, coeff) in &self.terms {
            if mono.exponent_of(main_var) == exp {
                let mut powers = mono.powers.clone();
                powers.remove(main_var);
                // Distinct source monomials with the same `main_var` exponent map
                // to distinct stripped monomials, so there is never a collision.
                result.terms.insert(Monomial { powers }, *coeff);
            }
        }
        result
    }

    // --- Ring operations ----------------------------------------------------

    /// Exact polynomial addition, or `None` on `i128` coefficient overflow.
    pub fn add(&self, other: &MvPoly) -> Option<MvPoly> {
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
    pub fn neg(&self) -> Option<MvPoly> {
        let mut out = MvPoly::zero();
        for (mono, coeff) in &self.terms {
            out.terms.insert(mono.clone(), coeff.checked_neg()?);
        }
        Some(out)
    }

    /// Exact polynomial subtraction, or `None` on `i128` overflow.
    pub fn sub(&self, other: &MvPoly) -> Option<MvPoly> {
        self.add(&other.neg()?)
    }

    /// Exact polynomial multiplication, or `None` on `i128`/`u32` overflow.
    pub fn mul(&self, other: &MvPoly) -> Option<MvPoly> {
        let mut out = MvPoly::zero();
        for (left_mono, left_coeff) in &self.terms {
            for (right_mono, right_coeff) in &other.terms {
                let mono = left_mono.mul(right_mono)?;
                let coeff = left_coeff.checked_mul(*right_coeff)?;
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
    pub fn pow(&self, exp: u32) -> Option<MvPoly> {
        let mut acc = MvPoly::constant(Rational::integer(1));
        for _ in 0..exp {
            acc = acc.mul(self)?;
        }
        Some(acc)
    }

    /// The partial derivative with respect to `var`, or `None` on `i128`
    /// overflow.
    pub fn derivative_in(&self, var: &str) -> Option<MvPoly> {
        let mut result = MvPoly::zero();
        for (mono, coeff) in &self.terms {
            let exp = mono.exponent_of(var);
            if exp == 0 {
                continue;
            }
            let new_coeff = coeff.checked_mul(Rational::integer(i128::from(exp)))?;
            let mut powers = mono.powers.clone();
            if exp == 1 {
                powers.remove(var);
            } else {
                powers.insert(var.to_owned(), exp - 1);
            }
            result = result.add(&MvPoly::single_term(Monomial { powers }, new_coeff))?;
        }
        Some(result)
    }

    // --- Evaluation ---------------------------------------------------------

    /// Exact evaluation at a rational point assigning every variable. `None` if a
    /// variable used by this polynomial is unassigned, or on `i128` overflow.
    pub fn evaluate(&self, assignment: &BTreeMap<String, Rational>) -> Option<Rational> {
        let mut total = Rational::zero();
        for (mono, coeff) in &self.terms {
            let mut term_value = *coeff;
            for (var, exp) in &mono.powers {
                let base = *assignment.get(var)?;
                for _ in 0..*exp {
                    term_value = term_value.checked_mul(base)?;
                }
            }
            total = total.checked_add(term_value)?;
        }
        Some(total)
    }

    // --- Division -----------------------------------------------------------

    /// Multivariate long division of `self` by `divisor` under the `lex`
    /// monomial order, returning `(quotient, remainder)` with `self = quotient ·
    /// divisor + remainder` and no monomial of `remainder` divisible by the
    /// leading monomial of `divisor`.
    ///
    /// Returns `None` if `divisor` is the zero polynomial or on `i128`/`u32`
    /// overflow. Because the remainder's leading monomials are all
    /// `lex`-indivisible by the divisor's, `divisor` divides `self` exactly iff
    /// the remainder is zero. Termination is guaranteed: each step strictly
    /// lowers the `lex`-leading monomial of the running dividend, and `lex` is a
    /// well-order.
    pub fn divide(&self, divisor: &MvPoly) -> Option<(MvPoly, MvPoly)> {
        let (divisor_mono, divisor_coeff) = divisor.leading_term()?; // None if divisor is zero
        let mut quotient = MvPoly::zero();
        let mut remainder = MvPoly::zero();
        let mut dividend = self.clone();
        while let Some((mono, coeff)) = dividend.leading_term() {
            if let Some(quot_mono) = mono.checked_div(&divisor_mono) {
                let quot_coeff = coeff.checked_div(divisor_coeff)?;
                let quot_term = MvPoly::single_term(quot_mono, quot_coeff);
                quotient = quotient.add(&quot_term)?;
                dividend = dividend.sub(&quot_term.mul(divisor)?)?;
            } else {
                let lead = MvPoly::single_term(mono, coeff);
                remainder = remainder.add(&lead)?;
                dividend = dividend.sub(&lead)?;
            }
        }
        Some((quotient, remainder))
    }

    /// Returns `Some(true)` iff `self` divides `other` exactly. `None` on
    /// overflow (or if `self` is zero, which cannot divide a nonzero polynomial).
    pub fn divides(&self, other: &MvPoly) -> Option<bool> {
        if self.is_zero() {
            return Some(other.is_zero());
        }
        let (_, remainder) = other.divide(self)?;
        Some(remainder.is_zero())
    }

    /// The exact quotient `self / divisor` when the division is exact, else
    /// `None` (a nonzero remainder, a zero divisor, or overflow).
    pub fn exact_div(&self, divisor: &MvPoly) -> Option<MvPoly> {
        let (quotient, remainder) = self.divide(divisor)?;
        if remainder.is_zero() {
            Some(quotient)
        } else {
            None
        }
    }

    // --- GCD ----------------------------------------------------------------

    /// The greatest common divisor of `self` and `other`, normalized to its
    /// **primitive** integer form with a positive `lex`-leading coefficient.
    ///
    /// The algorithm is the classic **recursive primitive polynomial remainder
    /// sequence** (Knuth, *TAOCP* vol. 2 §4.6.1; Geddes, Czapor & Labahn,
    /// *Algorithms for Computer Algebra*, ch. 7, primitive PRS). Viewing both
    /// inputs as univariate in a chosen main variable with coefficients in
    /// ℚ[remaining variables]:
    ///
    /// 1. factor each input into `content · primitive_part` — the content is the
    ///    GCD of the main-variable coefficients (a recursive call over fewer
    ///    variables), the primitive part is the exact quotient by the content;
    /// 2. the content of the GCD is the GCD of the two contents (recursion);
    /// 3. the primitive part of the GCD is the primitive part of the last nonzero
    ///    element of the pseudo-remainder Euclidean sequence on the two primitive
    ///    parts;
    /// 4. multiply the two together and normalize.
    ///
    /// The recursion bottoms out at zero variables, where every nonzero rational
    /// is a unit so the GCD of constants is `1`; univariate-over-ℚ inputs thus
    /// reduce to the Euclidean algorithm with the result made primitive.
    ///
    /// # Where the arithmetic happens
    ///
    /// The sequence itself runs over **unbounded integers** (the private `big`
    /// submodule), not over this type's `i128` rationals. That is not an
    /// optimization but a correctness-of-coverage fix: a pseudo-remainder step
    /// multiplies the whole running remainder by a leading coefficient, so the
    /// sequence passes through coefficients far larger than either the inputs or
    /// the answer. Measured on the shift quotient of Apéry's summand, inputs
    /// with largest coefficient `120` overflowed `i128` mid-sequence and the GCD
    /// declined. Only the finished GCD is converted back, so `None` now means
    /// *the answer* does not fit `i128` (or a `u32` exponent overflowed) — never
    /// that the scratch space did not.
    ///
    /// `gcd(a, 0)` is `a` normalized, `gcd(0, 0)` is `0`.
    pub fn gcd(&self, other: &MvPoly) -> Option<MvPoly> {
        BigPoly::from_mvpoly(self)
            .gcd(&BigPoly::from_mvpoly(other), &mut big::Cost::off())?
            .to_mvpoly()
    }

    /// [`MvPoly::gcd`] with the width of the intermediate coefficients recorded.
    ///
    /// Same answer, same algorithm; the difference is that the returned
    /// [`GcdCost`] says how wide the remainder sequence actually got. That number
    /// is the difference between "this GCD is hard" and "this GCD was run in a
    /// type too narrow to hold its own scratch space", and the second claim is
    /// the one that was previously unfalsifiable — a declined GCD looked exactly
    /// like an expensive one.
    ///
    /// This runs the sequence **twice** — once as it is, once with the per-step
    /// content division switched off to recover [`GcdCost::legacy_peak_bits`] —
    /// and the second run carries deliberately unreduced coefficients. It is a
    /// diagnostic, not a hot path; callers who want the answer should use
    /// [`MvPoly::gcd`].
    #[must_use]
    pub fn gcd_cost(&self, other: &MvPoly) -> GcdCost {
        let left = BigPoly::from_mvpoly(self);
        let right = BigPoly::from_mvpoly(other);
        let mut cost = big::Cost::on();
        let gcd = left.gcd(&right, &mut cost);
        let mut unstripped = big::Cost::unstripped();
        let _ = left.gcd(&right, &mut unstripped);
        GcdCost {
            input_bits: left.coefficient_bits().max(right.coefficient_bits()),
            peak_bits: cost.peak_bits(),
            legacy_peak_bits: unstripped.peak_bits(),
            result_bits: gcd.as_ref().map_or(0, BigPoly::coefficient_bits),
            steps: cost.steps(),
            fits_i128: gcd.and_then(|poly| poly.to_mvpoly()).is_some(),
        }
    }

    /// This polynomial rescaled to its canonical **primitive** associate: integer
    /// coefficients with content `1` and a positive `lex`-leading coefficient.
    /// The zero polynomial maps to itself. `None` only when a coefficient of the
    /// *normalized* form leaves the `i128` range, which requires the input to
    /// already be that large.
    fn normalized(&self) -> Option<MvPoly> {
        BigPoly::from_mvpoly(self).normalized().to_mvpoly()
    }

    // --- CasExpr interoperability ------------------------------------------

    /// Reconstruct a [`CasExpr`] (expanded sum-of-monomials form) denoting this
    /// polynomial. Terms are emitted in descending total degree with `lex` as a
    /// stable tie-break, matching the crate's canonical rendering.
    #[must_use]
    pub fn to_cas_expr(&self) -> CasExpr {
        if self.terms.is_empty() {
            return CasExpr::zero();
        }
        let mut ordered: Vec<(&Monomial, &Rational)> = self.terms.iter().collect();
        ordered.sort_by(|left, right| {
            right
                .0
                .total_degree()
                .cmp(&left.0.total_degree())
                .then_with(|| right.0.lex_cmp(left.0))
        });
        let mut sum: Vec<CasExpr> = Vec::with_capacity(ordered.len());
        for (mono, coeff) in ordered {
            let mut factors: Vec<CasExpr> = Vec::new();
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

    /// Expand a [`CasExpr`] over the polynomial fragment (`Const`, `Var`, `Add`,
    /// `Mul`, `Neg`, `Pow`) into an [`MvPoly`]. Returns `None` on a `Div` or
    /// transcendental (`Unary`) head — those are outside the polynomial fragment
    /// — or on `i128`/`u32` overflow during expansion.
    #[must_use]
    pub fn from_cas_expr(expr: &CasExpr) -> Option<MvPoly> {
        match expr {
            CasExpr::Const(value) => Some(MvPoly::constant(*value)),
            CasExpr::Var(name) => Some(MvPoly::var(name)),
            CasExpr::Add(terms) => terms.iter().try_fold(MvPoly::zero(), |acc, term| {
                acc.add(&MvPoly::from_cas_expr(term)?)
            }),
            CasExpr::Mul(factors) => factors
                .iter()
                .try_fold(MvPoly::constant(Rational::integer(1)), |acc, factor| {
                    acc.mul(&MvPoly::from_cas_expr(factor)?)
                }),
            CasExpr::Neg(inner) => MvPoly::from_cas_expr(inner)?.neg(),
            CasExpr::Pow(base, exp) => MvPoly::from_cas_expr(base)?.pow(*exp),
            CasExpr::Div(..) | CasExpr::Unary(..) => None,
        }
    }

    // --- Square-free factorization -----------------------------------------

    /// Square-free factorization with respect to `main_var` via **Yun's
    /// algorithm** (Yun, 1976; Geddes et al. ch. 8).
    ///
    /// Returns the non-unit square-free factors paired with their multiplicity:
    /// a list of `(factor, i)` where each `factor` is primitive-normalized, has
    /// positive main-variable degree, is square-free, the factors are pairwise
    /// coprime, and `∏ factor^i` is an associate of the input's primitive part.
    /// The empty list is returned when the input is zero or is a unit in
    /// `main_var` (degree 0). `None` on overflow.
    ///
    /// Yun's algorithm needs only GCD, exact division, and the derivative with
    /// respect to `main_var`, all provided here; over ℚ (characteristic 0) it is
    /// complete.
    pub fn squarefree(&self, main_var: &str) -> Option<Vec<(MvPoly, u32)>> {
        if self.is_zero() {
            return Some(Vec::new());
        }
        let derivative = self.derivative_in(main_var)?;
        let common = self.gcd(&derivative)?;
        let mut base = self.exact_div(&common)?;
        let mut cofactor = derivative.exact_div(&common)?;
        let mut delta = cofactor.sub(&base.derivative_in(main_var)?)?;
        let mut factors: Vec<(MvPoly, u32)> = Vec::new();
        let mut multiplicity: u32 = 1;
        while base.degree_in(main_var) >= 1 {
            let factor = base.gcd(&delta)?;
            base = base.exact_div(&factor)?;
            cofactor = delta.exact_div(&factor)?;
            delta = cofactor.sub(&base.derivative_in(main_var)?)?;
            if factor.degree_in(main_var) >= 1 {
                factors.push((factor.normalized()?, multiplicity));
            }
            multiplicity += 1;
        }
        Some(factors)
    }
}

#[cfg(test)]
mod tests {
    use super::{Monomial, MvPoly};
    use crate::{CasExpr, ZeroTest, equal};
    use axeyum_ir::Rational;
    use std::collections::{BTreeMap, BTreeSet};

    /// Integer-rational shorthand for tests.
    fn ri(value: i128) -> Rational {
        Rational::integer(value)
    }

    /// The variable polynomial `x`.
    fn var_x() -> MvPoly {
        MvPoly::var("x")
    }

    /// The variable polynomial `y`.
    fn var_y() -> MvPoly {
        MvPoly::var("y")
    }

    /// A single-term polynomial built from `(variable, exponent)` factors.
    fn term(coeff: i128, factors: &[(&str, u32)]) -> MvPoly {
        MvPoly::from_terms([(Monomial::from_powers(factors), ri(coeff))]).expect("no overflow")
    }

    /// `x^2 - 1`.
    fn x_squared_minus_one() -> MvPoly {
        term(1, &[("x", 2)]).sub(&MvPoly::constant(ri(1))).unwrap()
    }

    /// `x^2 - 2x + 1 = (x - 1)^2`.
    fn x_minus_one_squared() -> MvPoly {
        let x_minus_one = var_x().sub(&MvPoly::constant(ri(1))).unwrap();
        x_minus_one.pow(2).unwrap()
    }

    #[test]
    fn univariate_gcd_is_x_minus_one() {
        let gcd = x_squared_minus_one().gcd(&x_minus_one_squared()).unwrap();
        let x_minus_one = var_x().sub(&MvPoly::constant(ri(1))).unwrap();
        assert_eq!(gcd, x_minus_one);
    }

    #[test]
    fn bivariate_gcd_is_x_minus_y_up_to_constant() {
        // a = (x - y)(x + y),  b = (x - y)^2.  gcd should be an associate of x - y.
        let x_minus_y = var_x().sub(&var_y()).unwrap();
        let x_plus_y = var_x().add(&var_y()).unwrap();
        let poly_a = x_minus_y.mul(&x_plus_y).unwrap();
        let poly_b = x_minus_y.pow(2).unwrap();
        let gcd = poly_a.gcd(&poly_b).unwrap();
        // Associate check: each divides the other.
        assert_eq!(gcd.divides(&x_minus_y), Some(true));
        assert_eq!(x_minus_y.divides(&gcd), Some(true));
        // And with normalization the representative is exactly x - y.
        assert_eq!(gcd, x_minus_y);
    }

    #[test]
    fn gcd_of_coprime_polys_is_constant() {
        let poly_a = var_x().add(&MvPoly::constant(ri(1))).unwrap();
        let poly_b = var_x().add(&MvPoly::constant(ri(2))).unwrap();
        let gcd = poly_a.gcd(&poly_b).unwrap();
        assert!(gcd.variables().is_empty());
        assert_eq!(gcd.total_degree(), 0);
        assert_eq!(gcd, MvPoly::constant(ri(1)));
    }

    #[test]
    fn gcd_certified_by_division_and_cofactor_coprimality() {
        // To certify gcd(a, b) = g: g divides a and b, and a/g, b/g are coprime.
        let poly_a = x_squared_minus_one();
        let poly_b = x_minus_one_squared();
        let gcd = poly_a.gcd(&poly_b).unwrap();
        assert!(!gcd.is_zero());

        let (quot_a, rem_a) = poly_a.divide(&gcd).unwrap();
        let (quot_b, rem_b) = poly_b.divide(&gcd).unwrap();
        assert!(rem_a.is_zero(), "g must divide a");
        assert!(rem_b.is_zero(), "g must divide b");

        let cofactor_gcd = quot_a.gcd(&quot_b).unwrap();
        assert_eq!(cofactor_gcd.total_degree(), 0, "cofactors must be coprime");

        // Cross-check the certificate through the crate's certified zero-test.
        for (dividend, quotient) in [(&poly_a, &quot_a), (&poly_b, &quot_b)] {
            let recombined = quotient.mul(&gcd).unwrap();
            match equal(&recombined.to_cas_expr(), &dividend.to_cas_expr()) {
                ZeroTest::Certified { equal: true, .. } => {}
                other => panic!("recombination not certified: {other:?}"),
            }
        }
    }

    #[test]
    fn constructed_gcd_is_associate_of_the_shared_factor() {
        // a = p·d, b = q·d with p, q coprime; gcd(a, b) must be an associate of d.
        let shared = var_x().sub(&var_y()).unwrap(); // d = x - y
        let poly_p = var_x().add(&MvPoly::constant(ri(1))).unwrap(); // p = x + 1
        let poly_q = var_x().add(&MvPoly::constant(ri(2))).unwrap(); // q = x + 2
        assert_eq!(
            poly_p.gcd(&poly_q).unwrap().total_degree(),
            0,
            "p, q coprime"
        );

        let poly_a = poly_p.mul(&shared).unwrap();
        let poly_b = poly_q.mul(&shared).unwrap();
        let gcd = poly_a.gcd(&poly_b).unwrap();

        assert_eq!(shared.divides(&gcd), Some(true));
        assert_eq!(gcd.divides(&shared), Some(true));
    }

    #[test]
    fn divide_is_exact_for_a_true_factor() {
        // (x^2 - 1) / (x - 1) = x + 1, remainder 0.
        let x_minus_one = var_x().sub(&MvPoly::constant(ri(1))).unwrap();
        let (quotient, remainder) = x_squared_minus_one().divide(&x_minus_one).unwrap();
        assert!(remainder.is_zero());
        assert_eq!(quotient, var_x().add(&MvPoly::constant(ri(1))).unwrap());
    }

    #[test]
    fn multivariate_product_divides_back_exactly() {
        // p = x^2·y + 3,  q = x - 2y + 1.  (p·q)/q == p with zero remainder.
        let poly_p = term(1, &[("x", 2), ("y", 1)])
            .add(&MvPoly::constant(ri(3)))
            .unwrap();
        let poly_q = var_x()
            .sub(&term(2, &[("y", 1)]))
            .unwrap()
            .add(&MvPoly::constant(ri(1)))
            .unwrap();
        let product = poly_p.mul(&poly_q).unwrap();
        let (quotient, remainder) = product.divide(&poly_q).unwrap();
        assert!(remainder.is_zero());
        assert_eq!(quotient, poly_p);
        assert_eq!(product.exact_div(&poly_p).unwrap(), poly_q);
    }

    #[test]
    fn divide_leaves_a_remainder_when_not_divisible() {
        // (x^2) / (x - 1) = x + 1 remainder 1.
        let x_minus_one = var_x().sub(&MvPoly::constant(ri(1))).unwrap();
        let (quotient, remainder) = term(1, &[("x", 2)]).divide(&x_minus_one).unwrap();
        assert_eq!(quotient, var_x().add(&MvPoly::constant(ri(1))).unwrap());
        assert_eq!(remainder, MvPoly::constant(ri(1)));
    }

    #[test]
    fn evaluate_matches_hand_computation() {
        // f = x^2·y - 3,  at x = 2, y = 5  →  4·5 - 3 = 17.
        let poly = term(1, &[("x", 2), ("y", 1)])
            .sub(&MvPoly::constant(ri(3)))
            .unwrap();
        let mut assignment: BTreeMap<String, Rational> = BTreeMap::new();
        assignment.insert("x".to_owned(), ri(2));
        assignment.insert("y".to_owned(), ri(5));
        assert_eq!(poly.evaluate(&assignment), Some(ri(17)));
    }

    #[test]
    fn accessors_report_degrees_and_variables() {
        let poly = term(4, &[("x", 3), ("y", 2)])
            .add(&term(1, &[("y", 5)]))
            .unwrap();
        assert_eq!(poly.degree_in("x"), 3);
        assert_eq!(poly.degree_in("y"), 5);
        assert_eq!(poly.total_degree(), 5);
        let mut expected: BTreeSet<String> = BTreeSet::new();
        expected.insert("x".to_owned());
        expected.insert("y".to_owned());
        assert_eq!(poly.variables(), expected);
    }

    #[test]
    fn cas_expr_round_trips() {
        // p = 2·x^2·y - x + 3.
        let poly = term(2, &[("x", 2), ("y", 1)])
            .sub(&var_x())
            .unwrap()
            .add(&MvPoly::constant(ri(3)))
            .unwrap();
        let round_tripped = MvPoly::from_cas_expr(&poly.to_cas_expr()).unwrap();
        assert_eq!(round_tripped, poly);
    }

    #[test]
    fn from_cas_expr_declines_non_polynomial_heads() {
        let quotient = CasExpr::var("x") / CasExpr::var("y");
        assert_eq!(MvPoly::from_cas_expr(&quotient), None);
        assert_eq!(MvPoly::from_cas_expr(&CasExpr::var("x").ln()), None);
    }

    #[test]
    fn squarefree_recovers_multiplicities() {
        // f = (x - 1)^2·(x - 2).  Yun should return {(x - 2, 1), (x - 1, 2)}.
        let x_minus_one = var_x().sub(&MvPoly::constant(ri(1))).unwrap();
        let x_minus_two = var_x().sub(&MvPoly::constant(ri(2))).unwrap();
        let poly = x_minus_one.pow(2).unwrap().mul(&x_minus_two).unwrap();
        let factors = poly.squarefree("x").unwrap();

        assert_eq!(factors.len(), 2);
        let mult_of = |target: &MvPoly| {
            factors
                .iter()
                .find(|(factor, _)| factor == target)
                .map(|(_, mult)| *mult)
        };
        assert_eq!(mult_of(&x_minus_one), Some(2));
        assert_eq!(mult_of(&x_minus_two), Some(1));

        // ∏ factor^i reconstructs the primitive part (here the monic input itself).
        let mut product = MvPoly::constant(ri(1));
        for (factor, mult) in &factors {
            product = product.mul(&factor.pow(*mult).unwrap()).unwrap();
        }
        assert_eq!(product.divides(&poly), Some(true));
        assert_eq!(poly.divides(&product), Some(true));
    }

    #[test]
    fn squarefree_of_squarefree_input_is_the_input() {
        // f = (x - 1)(x - 2) is already square-free (all multiplicities 1).
        let poly = var_x()
            .sub(&MvPoly::constant(ri(1)))
            .unwrap()
            .mul(&var_x().sub(&MvPoly::constant(ri(2))).unwrap())
            .unwrap();
        let factors = poly.squarefree("x").unwrap();
        assert_eq!(factors.len(), 1);
        assert_eq!(factors[0].1, 1);
        assert_eq!(factors[0].0.divides(&poly), Some(true));
        assert_eq!(poly.divides(&factors[0].0), Some(true));
    }

    #[test]
    fn normalization_makes_leading_coefficient_positive_and_primitive() {
        // -2x - 2  normalizes (via gcd with 0) to the primitive positive x + 1.
        let poly = term(-2, &[("x", 1)]).sub(&MvPoly::constant(ri(2))).unwrap();
        let normalized = poly.gcd(&MvPoly::zero()).unwrap();
        assert_eq!(normalized, var_x().add(&MvPoly::constant(ri(1))).unwrap());
    }

    // -------------------------------------------------------------------
    // `Monomial::exponent_of` and `MvPoly::derivative_in`.
    //
    // Neither had a direct unit test anywhere in the crate before this: both
    // are reachable only through several layers of higher-level machinery
    // (the SOS Lie-derivative checker, Gosper/WZ summation, creative
    // telescoping's ratio derivation), each of which is itself
    // self-checking, so a bug here was not GUARANTEED to surface as a wrong
    // verdict -- it would surface only if it happened to break one of those
    // downstream identities rather than cancel out. These pin the power
    // rule directly, independent of any of that machinery.
    // -------------------------------------------------------------------

    #[test]
    fn exponent_of_reads_the_stored_power_and_zero_for_an_absent_or_constant_variable() {
        let mono = Monomial::from_powers(&[("x", 2), ("y", 3)]);
        assert_eq!(mono.exponent_of("x"), 2);
        assert_eq!(mono.exponent_of("y"), 3);
        // A variable the monomial does not mention reads back as exponent 0,
        // not a panic or a sentinel -- this is what lets `derivative_in`
        // treat "does not appear" and "appears to the 0th power" the same.
        assert_eq!(mono.exponent_of("z"), 0);
        assert_eq!(Monomial::one().exponent_of("x"), 0);
    }

    #[test]
    fn derivative_in_applies_the_power_rule_to_a_pure_power() {
        // d/dx(x^3) = 3x^2.
        let cubed = var_x().pow(3).unwrap();
        let derivative = cubed.derivative_in("x").unwrap();
        assert_eq!(derivative, term(3, &[("x", 2)]));
        // A wrong coefficient (the classic off-by-one power-rule bug) must
        // NOT be accepted as equal -- this is the negative half of the same
        // check, not a separate decorative assertion.
        assert_ne!(derivative, term(2, &[("x", 2)]));
        assert_ne!(derivative, term(3, &[("x", 3)]));
    }

    #[test]
    fn derivative_in_holds_other_variables_fixed_in_a_mixed_monomial() {
        // d/dx(x^2 y^3) = 2x y^3;  d/dy(x^2 y^3) = 3 x^2 y^2.
        let mixed = term(1, &[("x", 2), ("y", 3)]);
        assert_eq!(
            mixed.derivative_in("x").unwrap(),
            term(2, &[("x", 1), ("y", 3)])
        );
        assert_eq!(
            mixed.derivative_in("y").unwrap(),
            term(3, &[("x", 2), ("y", 2)])
        );
    }

    #[test]
    fn derivative_in_drops_terms_not_containing_the_variable() {
        // d/dx(5) = 0; d/dx(y) = 0 -- a term the variable does not appear in
        // contributes nothing, rather than being left in place unchanged.
        let five = MvPoly::constant(ri(5));
        assert!(five.derivative_in("x").unwrap().is_zero());
        assert!(var_y().derivative_in("x").unwrap().is_zero());
    }

    #[test]
    fn derivative_in_is_linear_across_a_multi_term_polynomial() {
        // d/dx(x^3 + x*y - y^2) = 3x^2 + y.
        let poly = var_x()
            .pow(3)
            .unwrap()
            .add(&var_x().mul(&var_y()).unwrap())
            .unwrap()
            .sub(&var_y().pow(2).unwrap())
            .unwrap();
        let derivative = poly.derivative_in("x").unwrap();
        let expected = term(3, &[("x", 2)]).add(&var_y()).unwrap();
        assert_eq!(derivative, expected);
    }

    #[test]
    fn derivative_in_of_a_linear_term_is_the_coefficient_and_forgets_the_variable() {
        // d/dx(x) = 1, and the result mentions no variable at all -- the
        // exponent-1 branch removes `var` from the monomial rather than
        // storing a spurious exponent 0.
        let derivative = var_x().derivative_in("x").unwrap();
        assert_eq!(derivative, MvPoly::constant(ri(1)));
        assert!(derivative.variables().is_empty());
    }
}
