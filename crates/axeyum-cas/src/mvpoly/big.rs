//! The unbounded-integer polynomial ring the multivariate GCD computes in —
//! and, since [ADR-1670], the ring the zero-test retries in when its bounded
//! normal form overflows.
//!
//! Both callers are the same shape of problem stated at different scales: a
//! computation whose *inputs* and *answer* both fit `i128` while the work in
//! between does not. For the GCD it is a pseudo-remainder sequence; for the
//! zero-test it is the expansion of a product whose terms cancel. `BigPoly` is
//! shared by both rather than duplicated, and `BigRatFunc` in `lib.rs` reaches
//! rational coefficients without a rational coefficient *type* by carrying a
//! separate integer denominator polynomial.
//!
//! [ADR-1670]: ../../../../docs/research/09-decisions/adr-1670-i128-fast-path-with-a-big-integer-overflow-fallback-for-the-cas-zero-test.md
//!
//! # Why this module exists
//!
//! [`MvPoly`](super::MvPoly) stores `i128`-backed [`Rational`] coefficients, and
//! every one of its operations is checked: a coefficient that leaves the `i128`
//! range yields `None` rather than a wrong answer. That is the right contract for
//! a public, bounded, `Copy` polynomial — but it is the wrong ring to run a
//! *polynomial remainder sequence* in.
//!
//! The reason is expression swell that is entirely **intermediate**. A
//! pseudo-remainder step multiplies the whole running remainder by the divisor's
//! leading coefficient, once per degree step, so a PRS on inputs of degree `d`
//! passes through coefficients of size roughly `lc^d` before the content is
//! divided back out. Measured on the frontier case — the shift quotient of
//! Apéry's summand `∑_k C(n,k)²·C(n+k,k)²` — the *inputs* have largest
//! coefficient **120** and the *result* is small, yet the sequence between them
//! overflows `i128` and the GCD declines. The bound that binds is not on the
//! question or the answer; it is on the scratch space.
//!
//! So the GCD is computed here, over [`BigInt`], and only the *answer* is
//! converted back into `i128` rationals. Callers keep the bounded type and the
//! bounded cost of `MvPoly`; the unbounded arithmetic is confined to the one
//! algorithm that provably needs it.
//!
//! # Why not a subresultant PRS instead
//!
//! A subresultant PRS *reduces* the growth (to polynomial rather than
//! exponential) but does not *eliminate* it: the coefficients still grow with the
//! input degree, so a large enough input still overflows a fixed-width type, and
//! a decline would still be a fact about `i128` rather than about mathematics.
//! Unbounded coefficients remove the failure mode instead of postponing it, which
//! also lets the growth be controlled by the strongest available means — dividing
//! the integer content back out at **every** step of the sequence, not only at
//! the end (see [`BigPoly::pseudo_remainder`]).
//!
//! # Semantics
//!
//! `BigPoly` holds integer coefficients but the GCD it computes is the GCD in
//! **ℚ[vars]**, normalized to its primitive integer associate with a positive
//! `lex`-leading coefficient — exactly the contract [`MvPoly::gcd`](super::MvPoly::gcd)
//! documents. Concretely, the GCD of two nonzero constants is `1`, not their
//! integer GCD, so `gcd(2x + 2, 4x + 4) = x + 1`.
//!
//! [`Rational`]: axeyum_ir::Rational

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::{Monomial, MvPoly};
use axeyum_ir::Rational;

/// A sparse multivariate polynomial with unbounded integer coefficients.
///
/// Canonical in the same sense as [`MvPoly`]: zero coefficients are never
/// stored, so structural equality is value equality and [`BigPoly::is_zero`] is
/// exact.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct BigPoly {
    terms: BTreeMap<Monomial, BigInt>,
}

/// A running record of how wide the coefficients of one GCD computation got.
///
/// The recorder exists because "the GCD overflowed" was, for a long time, the
/// only thing this crate could say about a declined reduction — and it was a
/// statement about `i128` rather than about the polynomials. Peak width in bits
/// is the number that distinguishes the two: an `i128` numerator holds 127 bits,
/// so any sequence whose peak exceeds that could not have been run in the
/// bounded type no matter how the algorithm were tuned.
// Deliberately NOT `Default`: the derived default would leave `strip_content`
// false, i.e. would silently select the growth this module exists to avoid.
// Construct through `off`, `on` or `unstripped`.
#[derive(Debug, Clone, Copy)]
pub(super) struct Cost {
    /// Whether to record at all; recording is skipped on the hot path.
    enabled: bool,
    /// Whether the sequence divides the integer content back out at every step.
    ///
    /// Always `true` in production. Setting it `false` reproduces the growth of
    /// the primitive PRS **as this crate ran it before**, which is the only way
    /// to state the improvement as a measurement on the same inputs rather than
    /// as a claim about a deleted implementation.
    strip_content: bool,
    /// The widest coefficient magnitude seen anywhere in the sequence, in bits.
    peak_bits: u64,
    /// Pseudo-remainder steps taken across the whole recursion.
    steps: u64,
}

impl Cost {
    /// A recorder that observes nothing (the default for production calls).
    pub(super) fn off() -> Cost {
        Cost {
            enabled: false,
            strip_content: true,
            peak_bits: 0,
            steps: 0,
        }
    }

    /// A recorder that observes every intermediate.
    pub(super) fn on() -> Cost {
        Cost {
            enabled: true,
            ..Cost::off()
        }
    }

    /// A recorder that observes every intermediate of the sequence **without**
    /// the per-step content division — the shape of the growth this crate used
    /// to run into.
    pub(super) fn unstripped() -> Cost {
        Cost {
            enabled: true,
            strip_content: false,
            ..Cost::off()
        }
    }

    /// The widest coefficient magnitude seen, in bits.
    pub(super) fn peak_bits(&self) -> u64 {
        self.peak_bits
    }

    /// Pseudo-remainder steps taken.
    pub(super) fn steps(&self) -> u64 {
        self.steps
    }

    /// Fold one intermediate polynomial into the record.
    fn observe(&mut self, poly: &BigPoly) {
        if !self.enabled {
            return;
        }
        self.peak_bits = self.peak_bits.max(poly.coefficient_bits());
    }

    /// Count one pseudo-remainder step.
    fn step(&mut self) {
        if self.enabled {
            self.steps += 1;
        }
    }
}

impl BigPoly {
    // --- Construction -------------------------------------------------------

    /// The zero polynomial.
    pub(crate) fn zero() -> BigPoly {
        BigPoly {
            terms: BTreeMap::new(),
        }
    }

    /// The constant polynomial `1`.
    pub(crate) fn one() -> BigPoly {
        BigPoly::single_term(Monomial::one(), BigInt::one())
    }

    /// The constant polynomial `value` (the zero polynomial when `value` is `0`).
    pub(crate) fn constant(value: BigInt) -> BigPoly {
        BigPoly::single_term(Monomial::one(), value)
    }

    /// The degree-1 polynomial in a single variable.
    pub(crate) fn variable(name: &str) -> BigPoly {
        BigPoly::single_term(Monomial::from_powers(&[(name, 1)]), BigInt::one())
    }

    /// The `(monomial, coefficient)` pairs in ascending monomial order; every
    /// stored coefficient is nonzero.
    pub(crate) fn terms(&self) -> impl Iterator<Item = (&Monomial, &BigInt)> {
        self.terms.iter()
    }

    /// A single-term polynomial; the zero polynomial when `coeff` is zero.
    fn single_term(mono: Monomial, coeff: BigInt) -> BigPoly {
        let mut terms = BTreeMap::new();
        if !coeff.is_zero() {
            terms.insert(mono, coeff);
        }
        BigPoly { terms }
    }

    /// Add `coeff·mono` in place, dropping the term if it cancels.
    fn accumulate(&mut self, mono: &Monomial, coeff: &BigInt) {
        match self.terms.get_mut(mono) {
            Some(slot) => {
                *slot += coeff;
                if slot.is_zero() {
                    self.terms.remove(mono);
                }
            }
            None => {
                if !coeff.is_zero() {
                    self.terms.insert(mono.clone(), coeff.clone());
                }
            }
        }
    }

    /// The integer polynomial denoting the same rational function as `poly` up to
    /// a positive rational factor: every denominator cleared by the least common
    /// multiple of all of them.
    ///
    /// Scaling by a nonzero rational is invisible to everything this module
    /// computes, because a GCD over ℚ is defined only up to a unit and the result
    /// is normalized to its primitive associate at the end.
    ///
    /// Total: `BigInt` cannot overflow, so unlike every `MvPoly` operation this
    /// conversion has no failure case.
    pub(super) fn from_mvpoly(poly: &MvPoly) -> BigPoly {
        let mut denominator_lcm = BigInt::one();
        for coeff in poly.terms.values() {
            let den = BigInt::from(coeff.denominator());
            let gcd = integer_gcd(&denominator_lcm, &den);
            denominator_lcm = &denominator_lcm / &gcd * &den;
        }
        let mut terms = BTreeMap::new();
        for (mono, coeff) in &poly.terms {
            // Exact: `denominator_lcm` is a multiple of every denominator.
            let scale = &denominator_lcm / BigInt::from(coeff.denominator());
            let numer = BigInt::from(coeff.numerator()) * scale;
            if !numer.is_zero() {
                terms.insert(mono.clone(), numer);
            }
        }
        BigPoly { terms }
    }

    /// This polynomial as an [`MvPoly`], or `None` when a coefficient does not
    /// fit `i128`.
    ///
    /// This is the *only* remaining width failure on the GCD route, and it is a
    /// statement about the answer rather than about the scratch space: a GCD
    /// divides both inputs, so its coefficients are bounded by theirs in every
    /// case that arises in practice.
    pub(super) fn to_mvpoly(&self) -> Option<MvPoly> {
        let mut terms = BTreeMap::new();
        for (mono, coeff) in &self.terms {
            let value = i128::try_from(coeff).ok()?;
            terms.insert(mono.clone(), Rational::integer(value));
        }
        Some(MvPoly { terms })
    }

    // --- Accessors ----------------------------------------------------------

    /// Returns `true` if this is the zero polynomial.
    pub(crate) fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The width in bits of the widest coefficient magnitude; `0` when zero.
    ///
    /// The comparison point is `127`: an `i128` numerator holds no more.
    pub(super) fn coefficient_bits(&self) -> u64 {
        self.terms
            .values()
            .map(num_bigint::BigInt::bits)
            .max()
            .unwrap_or(0)
    }

    /// The set of variables occurring in this polynomial.
    pub(crate) fn variables(&self) -> BTreeSet<String> {
        let mut vars = BTreeSet::new();
        for mono in self.terms.keys() {
            for (name, _) in mono.powers() {
                vars.insert(name.to_owned());
            }
        }
        vars
    }

    /// The degree of `var` (the largest exponent of `var` across all terms).
    fn degree_in(&self, var: &str) -> u32 {
        self.terms
            .keys()
            .map(|mono| mono.exponent_of(var))
            .max()
            .unwrap_or(0)
    }

    /// The coefficient of `var^exp`, as a polynomial over the remaining
    /// variables (with `var` stripped from each monomial).
    fn coefficient_of(&self, var: &str, exp: u32) -> BigPoly {
        let mut result = BigPoly::zero();
        for (mono, coeff) in &self.terms {
            if mono.exponent_of(var) == exp {
                let mut powers = mono.powers.clone();
                powers.remove(var);
                // Distinct source monomials with the same `var` exponent strip to
                // distinct monomials, so there is never a collision.
                result.terms.insert(Monomial { powers }, coeff.clone());
            }
        }
        result
    }

    /// The leading coefficient viewed as univariate in `var`.
    fn leading_coeff_in(&self, var: &str) -> BigPoly {
        self.coefficient_of(var, self.degree_in(var))
    }

    /// The greatest monomial under the `lex` order, or `None` if zero.
    fn leading_monomial(&self) -> Option<Monomial> {
        self.terms
            .keys()
            .max_by(|left, right| left.lex_cmp(right))
            .cloned()
    }

    /// The `lex`-leading `(monomial, coefficient)` pair, or `None` if zero.
    fn leading_term(&self) -> Option<(Monomial, BigInt)> {
        let mono = self.leading_monomial()?;
        let coeff = self.terms.get(&mono)?.clone();
        Some((mono, coeff))
    }

    // --- Ring operations ----------------------------------------------------

    /// Exact polynomial addition.
    pub(crate) fn add(&self, other: &BigPoly) -> BigPoly {
        let mut out = self.clone();
        for (mono, coeff) in &other.terms {
            out.accumulate(mono, coeff);
        }
        out
    }

    /// Exact polynomial subtraction.
    pub(crate) fn sub(&self, other: &BigPoly) -> BigPoly {
        let mut out = self.clone();
        for (mono, coeff) in &other.terms {
            out.accumulate(mono, &-coeff.clone());
        }
        out
    }

    /// Exact negation.
    pub(crate) fn neg(&self) -> BigPoly {
        BigPoly::zero().sub(self)
    }

    /// `self` raised to a non-negative integer power, or `None` on `u32`
    /// exponent overflow inside a monomial product. `self^0` is `1`.
    ///
    /// Binary exponentiation: `⌈log₂ exp⌉` squarings rather than `exp`
    /// multiplications, which matters because these are the coefficients that
    /// outgrew `i128` in the first place.
    pub(crate) fn pow(&self, exp: u32) -> Option<BigPoly> {
        let mut result = BigPoly::one();
        let mut base = self.clone();
        let mut remaining = exp;
        while remaining > 0 {
            if remaining & 1 == 1 {
                result = result.mul(&base)?;
            }
            remaining >>= 1;
            if remaining > 0 {
                base = base.mul(&base)?;
            }
        }
        Some(result)
    }

    /// Exact polynomial multiplication, or `None` on `u32` exponent overflow.
    ///
    /// The coefficients cannot overflow; only the exponent sum can, and only for
    /// monomials no realistic input produces.
    pub(crate) fn mul(&self, other: &BigPoly) -> Option<BigPoly> {
        let mut out = BigPoly::zero();
        for (left_mono, left_coeff) in &self.terms {
            for (right_mono, right_coeff) in &other.terms {
                let mono = left_mono.mul(right_mono)?;
                out.accumulate(&mono, &(left_coeff * right_coeff));
            }
        }
        Some(out)
    }

    /// `self` multiplied by the single term `coeff·mono`, or `None` on exponent
    /// overflow.
    fn scale(&self, mono: &Monomial, coeff: &BigInt) -> Option<BigPoly> {
        let mut out = BigPoly::zero();
        for (term_mono, term_coeff) in &self.terms {
            let product = term_mono.mul(mono)?;
            out.accumulate(&product, &(term_coeff * coeff));
        }
        Some(out)
    }

    /// The exact quotient `self / divisor` in ℤ[vars], or `None` when the
    /// division is not exact there (a nonzero remainder, a coefficient that does
    /// not divide, or a zero divisor).
    ///
    /// The loop is `lex` long division. When `divisor` truly divides `self` in
    /// ℤ[vars] every step is exact: the `lex`-leading term of the dividend is the
    /// product of the leading terms of quotient and divisor, so the divisor's
    /// leading monomial and leading coefficient both divide it, and subtracting
    /// leaves `(quotient − leading)·divisor`, to which the same argument applies.
    fn exact_div(&self, divisor: &BigPoly) -> Option<BigPoly> {
        let (divisor_mono, divisor_coeff) = divisor.leading_term()?;
        let mut quotient = BigPoly::zero();
        let mut dividend = self.clone();
        while let Some((mono, coeff)) = dividend.leading_term() {
            let quot_mono = mono.checked_div(&divisor_mono)?;
            if (&coeff % &divisor_coeff) != BigInt::zero() {
                return None;
            }
            let quot_coeff = &coeff / &divisor_coeff;
            quotient.accumulate(&quot_mono, &quot_coeff);
            dividend = dividend.sub(&divisor.scale(&quot_mono, &quot_coeff)?);
        }
        Some(quotient)
    }

    // --- Normalization ------------------------------------------------------

    /// The GCD of every coefficient magnitude; zero for the zero polynomial.
    fn integer_content(&self) -> BigInt {
        let mut content = BigInt::zero();
        for coeff in self.terms.values() {
            content = integer_gcd(&content, coeff);
            if content.is_one() {
                break;
            }
        }
        content
    }

    /// This polynomial divided by the GCD of its coefficients, leaving the signs
    /// untouched. The zero polynomial maps to itself.
    ///
    /// Only ever applied where the value is needed up to a rational unit, which
    /// is what makes it a legitimate — and, on a polynomial remainder sequence,
    /// an essential — growth control.
    fn integer_primitive(&self) -> BigPoly {
        let content = self.integer_content();
        if content.is_zero() || content.is_one() {
            return self.clone();
        }
        let mut terms = BTreeMap::new();
        for (mono, coeff) in &self.terms {
            terms.insert(mono.clone(), coeff / &content);
        }
        BigPoly { terms }
    }

    /// This polynomial rescaled to its canonical primitive associate: coefficient
    /// GCD `1` and a positive `lex`-leading coefficient. Zero maps to itself.
    pub(super) fn normalized(&self) -> BigPoly {
        if self.is_zero() {
            return BigPoly::zero();
        }
        let primitive = self.integer_primitive();
        let negate = primitive
            .leading_monomial()
            .and_then(|mono| primitive.terms.get(&mono).cloned())
            .is_some_and(|lead| lead.is_negative());
        if !negate {
            return primitive;
        }
        let mut terms = BTreeMap::new();
        for (mono, coeff) in &primitive.terms {
            terms.insert(mono.clone(), -coeff.clone());
        }
        BigPoly { terms }
    }

    // --- GCD ----------------------------------------------------------------

    /// The GCD in ℚ[vars], normalized to its primitive integer associate with a
    /// positive `lex`-leading coefficient.
    ///
    /// The algorithm is the recursive **primitive polynomial remainder sequence**
    /// (Knuth, *TAOCP* vol. 2 §4.6.1; Geddes, Czapor & Labahn, *Algorithms for
    /// Computer Algebra*, ch. 7) — the same one [`MvPoly`] documented before this
    /// module existed, unchanged except that it now runs where its intermediates
    /// fit.
    ///
    /// `None` only on `u32` exponent overflow.
    pub(super) fn gcd(&self, other: &BigPoly, cost: &mut Cost) -> Option<BigPoly> {
        cost.observe(self);
        cost.observe(other);
        if self.is_zero() {
            return Some(other.normalized());
        }
        if other.is_zero() {
            return Some(self.normalized());
        }
        let mut vars = self.variables();
        vars.extend(other.variables());
        let Some(main_var) = vars.into_iter().next() else {
            // Both are nonzero constants. Their GCD *in ℚ* is the unit 1 — this
            // is the step that makes the whole recursion compute a rational GCD
            // out of integer arithmetic.
            return Some(BigPoly::one());
        };

        let content_gcd = self
            .content_in(&main_var, cost)?
            .gcd(&other.content_in(&main_var, cost)?, cost)?;
        let prim_gcd = BigPoly::primitive_prs(
            &self.primitive_part_in(&main_var, cost)?,
            &other.primitive_part_in(&main_var, cost)?,
            &main_var,
            cost,
        )?;
        Some(content_gcd.mul(&prim_gcd)?.normalized())
    }

    /// The content of `self` with respect to `main_var`: the GCD of its
    /// main-variable coefficients, a polynomial over the remaining variables.
    fn content_in(&self, main_var: &str, cost: &mut Cost) -> Option<BigPoly> {
        if self.is_zero() {
            return Some(BigPoly::zero());
        }
        let mut content = BigPoly::zero();
        for exp in 0..=self.degree_in(main_var) {
            let coeff = self.coefficient_of(main_var, exp);
            if coeff.is_zero() {
                continue;
            }
            content = if content.is_zero() {
                coeff
            } else {
                content.gcd(&coeff, cost)?
            };
        }
        Some(content.normalized())
    }

    /// The primitive part of `self` with respect to `main_var`: the exact
    /// quotient by its content, with the integer content also divided out.
    ///
    /// Removing the integer content as well is what keeps the remainder sequence
    /// small. It is sound because every caller uses the result only up to a
    /// rational unit — the content GCD is recovered separately in
    /// [`BigPoly::gcd`], and the final answer is normalized to its primitive
    /// associate regardless.
    fn primitive_part_in(&self, main_var: &str, cost: &mut Cost) -> Option<BigPoly> {
        if self.is_zero() {
            return Some(BigPoly::zero());
        }
        let content = self.content_in(main_var, cost)?;
        let quotient = self.exact_div(&content)?;
        cost.observe(&quotient);
        Some(if cost.strip_content {
            quotient.integer_primitive()
        } else {
            quotient
        })
    }

    /// The pseudo-remainder of `self` by `divisor`, both viewed as univariate in
    /// `main_var`, taken up to a positive rational factor.
    ///
    /// Returns an `R` with `lc(divisor)^k·self = Q·divisor + c·R` for some `k` and
    /// some positive integer `c`, and `deg_{main_var}(R) < deg_{main_var}(divisor)`.
    /// The caller uses only the primitive part of `R`, which is invariant under
    /// that factor — which is exactly what licenses dividing the integer content
    /// out **inside** the loop rather than after it. That single line is the
    /// difference between a sequence whose coefficients grow like `lc^degree` and
    /// one that stays near the size of its own primitive parts.
    ///
    /// `None` only on `u32` exponent overflow.
    fn pseudo_remainder(
        &self,
        divisor: &BigPoly,
        main_var: &str,
        cost: &mut Cost,
    ) -> Option<BigPoly> {
        let divisor_degree = divisor.degree_in(main_var);
        let divisor_lead = divisor.leading_coeff_in(main_var);
        let mut remainder = self.clone();
        while !remainder.is_zero() && remainder.degree_in(main_var) >= divisor_degree {
            let remainder_degree = remainder.degree_in(main_var);
            let remainder_lead = remainder.leading_coeff_in(main_var);
            let shift = remainder_degree - divisor_degree;
            // remainder <- divisor_lead·remainder − remainder_lead·main_var^shift·divisor.
            // The two products share the leading term, which therefore cancels;
            // the main-variable degree strictly drops, guaranteeing termination.
            let scaled = remainder.mul(&divisor_lead)?;
            cost.observe(&scaled);
            cost.step();
            let shift_mono = Monomial::from_powers(&[(main_var, shift)]);
            let subtrahend = remainder_lead
                .mul(divisor)?
                .scale(&shift_mono, &BigInt::one())?;
            cost.observe(&subtrahend);
            let stepped = scaled.sub(&subtrahend);
            cost.observe(&stepped);
            remainder = if cost.strip_content {
                stepped.integer_primitive()
            } else {
                stepped
            };
        }
        Some(remainder)
    }

    /// The primitive-part GCD of two **primitive** polynomials viewed as
    /// univariate in `main_var`, via the primitive pseudo-remainder Euclidean
    /// sequence.
    fn primitive_prs(
        left: &BigPoly,
        right: &BigPoly,
        main_var: &str,
        cost: &mut Cost,
    ) -> Option<BigPoly> {
        let mut higher = left.clone();
        let mut lower = right.clone();
        if higher.degree_in(main_var) < lower.degree_in(main_var) {
            std::mem::swap(&mut higher, &mut lower);
        }
        // A primitive polynomial of main-variable degree 0 is a unit, so the two
        // inputs are coprime in `main_var`: their primitive-part GCD is 1.
        if lower.degree_in(main_var) == 0 {
            return Some(BigPoly::one());
        }
        loop {
            let remainder = higher.pseudo_remainder(&lower, main_var, cost)?;
            if remainder.is_zero() {
                return lower.primitive_part_in(main_var, cost);
            }
            if remainder.degree_in(main_var) == 0 {
                return Some(BigPoly::one());
            }
            higher = lower;
            lower = remainder.primitive_part_in(main_var, cost)?;
        }
    }
}

/// The GCD of two `BigInt` values as a non-negative `BigInt` (Euclid).
fn integer_gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut current = left.abs();
    let mut next = right.abs();
    while !next.is_zero() {
        let remainder = &current % &next;
        current = next;
        next = remainder;
    }
    current
}

#[cfg(test)]
mod tests {
    use super::{BigPoly, Cost, integer_gcd};
    use crate::mvpoly::{Monomial, MvPoly};
    use axeyum_ir::Rational;
    use num_bigint::BigInt;

    /// A single-term `MvPoly` from `(variable, exponent)` factors.
    fn term(coeff: i128, factors: &[(&str, u32)]) -> MvPoly {
        MvPoly::from_terms([(Monomial::from_powers(factors), Rational::integer(coeff))])
            .expect("no overflow")
    }

    #[test]
    fn integer_gcd_is_euclid() {
        assert_eq!(
            integer_gcd(&BigInt::from(48), &BigInt::from(-18)),
            BigInt::from(6)
        );
        assert_eq!(
            integer_gcd(&BigInt::from(0), &BigInt::from(7)),
            BigInt::from(7)
        );
        assert_eq!(
            integer_gcd(&BigInt::from(0), &BigInt::from(0)),
            BigInt::from(0)
        );
    }

    #[test]
    fn conversion_clears_denominators_and_round_trips_up_to_content() {
        // x/2 + 1/3  ->  3x + 2 after clearing denominators.
        let poly = MvPoly::from_terms([
            (Monomial::from_powers(&[("x", 1)]), Rational::new(1, 2)),
            (Monomial::one(), Rational::new(1, 3)),
        ])
        .expect("no overflow");
        let big = BigPoly::from_mvpoly(&poly);
        let back = big.to_mvpoly().expect("fits i128");
        let expected = term(3, &[("x", 1)])
            .add(&MvPoly::constant(Rational::integer(2)))
            .expect("no overflow");
        assert_eq!(back, expected);
    }

    #[test]
    fn exact_div_declines_an_inexact_integer_division() {
        // 2x is not divisible by 3x in Z[x], even though it is in Q[x].
        let two_x = BigPoly::from_mvpoly(&term(2, &[("x", 1)]));
        let three_x = BigPoly::from_mvpoly(&term(3, &[("x", 1)]));
        assert_eq!(two_x.exact_div(&three_x), None);
    }

    #[test]
    fn gcd_of_constants_is_the_rational_unit_not_the_integer_gcd() {
        // The recursion's base case: over Q every nonzero constant is a unit, so
        // gcd(2x + 2, 4x + 4) is x + 1 rather than 2x + 2.
        let left = term(2, &[("x", 1)])
            .add(&MvPoly::constant(Rational::integer(2)))
            .expect("no overflow");
        let right = term(4, &[("x", 1)])
            .add(&MvPoly::constant(Rational::integer(4)))
            .expect("no overflow");
        let gcd = BigPoly::from_mvpoly(&left)
            .gcd(&BigPoly::from_mvpoly(&right), &mut Cost::off())
            .expect("no exponent overflow")
            .to_mvpoly()
            .expect("fits i128");
        let expected = MvPoly::var("x")
            .add(&MvPoly::constant(Rational::integer(1)))
            .expect("no overflow");
        assert_eq!(gcd, expected);
    }

    #[test]
    fn pseudo_remainder_stays_small_across_the_sequence() {
        // The measurement this module exists for: on inputs whose coefficients
        // fit in two digits, the primitive PRS must not pass through anything an
        // `i128` could not hold if the content is removed each step.
        //
        // f = (x^4 + 3x^2 + 1)·(x^3 - 5),  g = (x^4 + 3x^2 + 1)·(x^3 + 7).
        let shared = term(1, &[("x", 4)])
            .add(&term(3, &[("x", 2)]))
            .and_then(|p| p.add(&MvPoly::constant(Rational::integer(1))))
            .expect("no overflow");
        let left = shared
            .mul(
                &term(1, &[("x", 3)])
                    .sub(&MvPoly::constant(Rational::integer(5)))
                    .expect("no overflow"),
            )
            .expect("no overflow");
        let right = shared
            .mul(
                &term(1, &[("x", 3)])
                    .add(&MvPoly::constant(Rational::integer(7)))
                    .expect("no overflow"),
            )
            .expect("no overflow");
        let gcd = BigPoly::from_mvpoly(&left)
            .gcd(&BigPoly::from_mvpoly(&right), &mut Cost::off())
            .expect("no exponent overflow")
            .to_mvpoly()
            .expect("fits i128");
        assert_eq!(gcd, shared);
    }
}
