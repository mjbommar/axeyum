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

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::Rational;

use crate::CasExpr;

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

    /// The polynomial `var^exp` (the constant `1` when `exp` is zero).
    #[must_use]
    fn monomial_power(var: &str, exp: u32) -> MvPoly {
        MvPoly::single_term(Monomial::from_powers(&[(var, exp)]), Rational::integer(1))
    }

    // --- Accessors ----------------------------------------------------------

    /// Returns `true` if this is the zero polynomial.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
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
    /// `gcd(a, 0)` is `a` normalized, `gcd(0, 0)` is `0`. `None` on overflow.
    pub fn gcd(&self, other: &MvPoly) -> Option<MvPoly> {
        if self.is_zero() {
            return other.normalized();
        }
        if other.is_zero() {
            return self.normalized();
        }
        let mut vars = self.variables();
        vars.extend(other.variables());
        let Some(main_var) = vars.into_iter().next() else {
            // Both are nonzero constants: their GCD is the unit 1.
            return Some(MvPoly::constant(Rational::integer(1)));
        };

        let content_left = self.content_in(&main_var)?;
        let content_right = other.content_in(&main_var)?;
        let content_gcd = content_left.gcd(&content_right)?;

        let prim_left = self.primitive_part_in(&main_var)?;
        let prim_right = other.primitive_part_in(&main_var)?;
        let prim_gcd = MvPoly::primitive_prs(&prim_left, &prim_right, &main_var)?;

        content_gcd.mul(&prim_gcd)?.normalized()
    }

    /// The content of `self` with respect to `main_var`: the GCD of its
    /// main-variable coefficients, a polynomial over the remaining variables.
    /// `None` on overflow.
    fn content_in(&self, main_var: &str) -> Option<MvPoly> {
        if self.is_zero() {
            return Some(MvPoly::zero());
        }
        let degree = self.degree_in(main_var);
        let mut content = MvPoly::zero();
        for exp in 0..=degree {
            let coeff = self.coefficient_of(main_var, exp);
            if coeff.is_zero() {
                continue;
            }
            content = if content.is_zero() {
                coeff
            } else {
                content.gcd(&coeff)?
            };
        }
        content.normalized()
    }

    /// The primitive part of `self` with respect to `main_var`: the exact
    /// quotient of `self` by its content. `None` on overflow.
    fn primitive_part_in(&self, main_var: &str) -> Option<MvPoly> {
        if self.is_zero() {
            return Some(MvPoly::zero());
        }
        let content = self.content_in(main_var)?;
        self.exact_div(&content)
    }

    /// The pseudo-remainder of `self` by `divisor`, both viewed as univariate in
    /// `main_var`.
    ///
    /// Returns an `R` with `leading_coeff(divisor)^k · self = Q · divisor + R`
    /// for some `k` and `deg_{main_var}(R) < deg_{main_var}(divisor)`. The exact
    /// power `k` is left implicit because the caller only uses the primitive part
    /// of `R`, which is invariant under a coefficient-ring factor — this also
    /// avoids the coefficient blow-up of forming `leading_coeff(divisor)^k`
    /// explicitly. `None` on overflow.
    fn pseudo_remainder(&self, divisor: &MvPoly, main_var: &str) -> Option<MvPoly> {
        let divisor_degree = divisor.degree_in(main_var);
        let divisor_lead = divisor.leading_coeff(main_var);
        let mut remainder = self.clone();
        while !remainder.is_zero() && remainder.degree_in(main_var) >= divisor_degree {
            let remainder_degree = remainder.degree_in(main_var);
            let remainder_lead = remainder.leading_coeff(main_var);
            let shift = remainder_degree - divisor_degree;
            // remainder ← divisor_lead·remainder − remainder_lead·main_var^shift·divisor.
            // The two products share the leading term divisor_lead·remainder_lead·
            // main_var^remainder_degree, which therefore cancels; the main-variable
            // degree strictly drops, guaranteeing termination.
            let scaled = remainder.mul(&divisor_lead)?;
            let shift_mono = MvPoly::monomial_power(main_var, shift);
            let subtrahend = remainder_lead.mul(&shift_mono)?.mul(divisor)?;
            remainder = scaled.sub(&subtrahend)?;
        }
        Some(remainder)
    }

    /// The primitive-part GCD of two **primitive** polynomials `left` and
    /// `right`, viewed as univariate in `main_var`, via the primitive
    /// pseudo-remainder Euclidean sequence. `None` on overflow.
    fn primitive_prs(left: &MvPoly, right: &MvPoly, main_var: &str) -> Option<MvPoly> {
        let mut higher = left.clone();
        let mut lower = right.clone();
        if higher.degree_in(main_var) < lower.degree_in(main_var) {
            std::mem::swap(&mut higher, &mut lower);
        }
        // A primitive polynomial of main-variable degree 0 is a unit, so the two
        // inputs are coprime in `main_var`: their primitive-part GCD is 1.
        if lower.degree_in(main_var) == 0 {
            return Some(MvPoly::constant(Rational::integer(1)));
        }
        loop {
            let remainder = higher.pseudo_remainder(&lower, main_var)?;
            if remainder.is_zero() {
                return lower.primitive_part_in(main_var);
            }
            if remainder.degree_in(main_var) == 0 {
                return Some(MvPoly::constant(Rational::integer(1)));
            }
            higher = lower;
            lower = remainder.primitive_part_in(main_var)?;
        }
    }

    /// This polynomial rescaled to its canonical **primitive** associate: integer
    /// coefficients with content `1` and a positive `lex`-leading coefficient.
    /// The zero polynomial maps to itself. `None` on the (astronomically rare)
    /// `i128` overflow while clearing denominators.
    fn normalized(&self) -> Option<MvPoly> {
        if self.is_zero() {
            return Some(MvPoly::zero());
        }
        // Clear denominators: scale by the least common multiple of all of them.
        let mut denom_lcm: i128 = 1;
        for coeff in self.terms.values() {
            denom_lcm = integer_lcm(denom_lcm, coeff.denominator())?;
        }
        // Integer numerators after scaling, and the GCD of their magnitudes.
        let mut content: i128 = 0;
        let mut scaled: BTreeMap<Monomial, i128> = BTreeMap::new();
        for (mono, coeff) in &self.terms {
            let factor = denom_lcm / coeff.denominator(); // exact: lcm is a multiple
            let numer = coeff.numerator().checked_mul(factor)?;
            content = integer_gcd(content, numer)?;
            scaled.insert(mono.clone(), numer);
        }
        // Sign so the leading coefficient is positive.
        let lead_mono = self.leading_monomial()?;
        let sign: i128 = if scaled.get(&lead_mono).copied().unwrap_or(0) < 0 {
            -1
        } else {
            1
        };
        let mut result = MvPoly::zero();
        for (mono, numer) in scaled {
            let reduced = (numer / content).checked_mul(sign)?;
            result.terms.insert(mono, Rational::integer(reduced));
        }
        Some(result)
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

/// The GCD of two `i128` values as a non-negative `i128`, or `None` in the
/// degenerate case where a magnitude does not fit back in `i128` (only possible
/// from `i128::MIN`). Never panics.
fn integer_gcd(left: i128, right: i128) -> Option<i128> {
    let mut current = left.unsigned_abs();
    let mut next = right.unsigned_abs();
    while next != 0 {
        let remainder = current % next;
        current = next;
        next = remainder;
    }
    i128::try_from(current).ok()
}

/// The least common multiple of two non-negative `i128` values as a non-negative
/// `i128`, or `None` on overflow. `lcm(x, 0) = 0`.
fn integer_lcm(left: i128, right: i128) -> Option<i128> {
    if left == 0 || right == 0 {
        return Some(0);
    }
    let gcd = integer_gcd(left, right)?;
    (left / gcd).checked_mul(right).map(i128::abs)
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
}
