//! Univariate polynomials over ℤ and ℚ, with fraction-free operations, Sturm
//! sequences and real-root isolation (ADR-1710 migration slices 3–5).
//!
//! # What is here and why
//!
//! The design note's §2.1 inventory counts **eight** univariate
//! polynomial-over-ℚ implementations in this workspace, five of them over
//! [`BigRational`], and **six** separate Sturm chains. This module is the one
//! they migrate onto. [`ZPoly`] is the integer carrier — the one that can
//! afford a fraction-free gcd — and [`QPoly`] is the rational carrier the five
//! copies actually spell.
//!
//! Coefficients are **little-endian**: `coefficients()[k]` multiplies `x^k`.
//! Both carriers are kept trimmed, so [`ZPoly::degree`] and [`QPoly::degree`]
//! are well defined and `PartialEq` is mathematical equality.
//!
//! # The normalization convention, which is the load-bearing detail
//!
//! Of the six chains in the inventory, `fps_analytic.rs` scales every member to
//! a **primitive integer polynomial by a positive rational** and `qe_big.rs`
//! does not. A positive scale changes no sign variation, so the two conventions
//! produce **identical root counts on every interval** — that equality is what
//! the migration's differential tests assert, and it is why one chain can
//! replace both.
//!
//! This module adopts the primitive-integer convention, because it is the one
//! that stops the coefficients doubling in size at every Euclidean step. A
//! chain member is therefore a [`ZPoly`], and [`SturmCertificate::chain`] — a
//! `Vec<Vec<BigInt>>` — holds it exactly.
//!
//! # Certificates
//!
//! [`crate::BezoutCertificate`] (integers) and [`PolyBezoutCertificate`] (ℚ[x])
//! re-multiply `u·a + v·b = g`; [`PolyGcdCertificate`] additionally carries the
//! divisibility quotients and the content, so every distinction the producer
//! makes is recorded; [`SturmCertificate`] recomputes the chain from its own
//! first member *and*, separately, recounts the sign variations. Every one of
//! those conditions is independently failable, and each has a forgery test.

use num_bigint::{BigInt, BigUint, Sign};
use num_rational::BigRational;

use crate::{BezoutCertificate, FractionFree, SturmCertificate, UnivariatePoly};

// ---------------------------------------------------------------------------
// Small helpers.
//
// `num-traits` is deliberately not imported: this crate's manifest carries
// exactly two dependencies (ADR-1710), and every trait method used below has a
// two-line inherent equivalent.
// ---------------------------------------------------------------------------

/// The integer zero.
fn int_zero() -> BigInt {
    BigInt::from(0)
}

/// The integer one.
fn int_one() -> BigInt {
    BigInt::from(1)
}

/// Whether an integer is zero, without `num_traits::Zero`.
fn int_is_zero(value: &BigInt) -> bool {
    value.sign() == Sign::NoSign
}

/// The rational zero.
fn rat_zero() -> BigRational {
    BigRational::from(int_zero())
}

/// The rational one.
fn rat_one() -> BigRational {
    BigRational::from(int_one())
}

/// Whether a rational is zero.
fn rat_is_zero(value: &BigRational) -> bool {
    value.numer().sign() == Sign::NoSign
}

/// `-1`, `0` or `1`.
fn rat_sign(value: &BigRational) -> i8 {
    match value.numer().sign() {
        Sign::Minus => -1,
        Sign::NoSign => 0,
        Sign::Plus => 1,
    }
}

/// `|value|`, without `num_traits::Signed`.
fn rat_abs(value: &BigRational) -> BigRational {
    if value.numer().sign() == Sign::Minus {
        -value.clone()
    } else {
        value.clone()
    }
}

/// `base^exponent` by repeated squaring.
fn int_pow(base: &BigInt, exponent: u32) -> BigInt {
    let mut result = int_one();
    let mut square = base.clone();
    let mut remaining = exponent;
    while remaining > 0 {
        if remaining & 1 == 1 {
            result *= &square;
        }
        remaining >>= 1;
        if remaining > 0 {
            square = &square * &square;
        }
    }
    result
}

/// Euclid's gcd on magnitudes.
fn gcd_uint(left: &BigUint, right: &BigUint) -> BigUint {
    let mut a = left.clone();
    let mut b = right.clone();
    while b != BigUint::from(0u32) {
        let remainder = a % &b;
        a = core::mem::replace(&mut b, remainder);
    }
    a
}

/// The greatest common divisor of two integers, non-negative.
fn gcd_int(left: &BigInt, right: &BigInt) -> BigInt {
    BigInt::from(gcd_uint(left.magnitude(), right.magnitude()))
}

// ---------------------------------------------------------------------------
// ZPoly
// ---------------------------------------------------------------------------

/// A univariate polynomial over ℤ, little-endian and trimmed.
///
/// This is the carrier the fraction-free operations live on: pseudo-division,
/// the subresultant polynomial remainder sequence, the resultant, and the
/// primitive gcd. Working over ℚ and clearing denominators at the end is what
/// six modules in this workspace independently wrote; the coefficient growth
/// that makes it slow is what the subresultant PRS exists to bound.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ZPoly {
    /// Little-endian coefficients with no trailing zero.
    coeffs: Vec<BigInt>,
}

impl ZPoly {
    /// The zero polynomial.
    pub fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Build from little-endian coefficients, trimming trailing zeros.
    pub fn from_coefficients(mut coeffs: Vec<BigInt>) -> Self {
        while coeffs.last().is_some_and(int_is_zero) {
            coeffs.pop();
        }
        Self { coeffs }
    }

    /// Build from little-endian `i64` coefficients. Convenience for tests and
    /// small literals.
    pub fn from_i64(coeffs: &[i64]) -> Self {
        Self::from_coefficients(coeffs.iter().copied().map(BigInt::from).collect())
    }

    /// The constant polynomial.
    pub fn constant(value: BigInt) -> Self {
        Self::from_coefficients(vec![value])
    }

    /// The little-endian coefficients, with no trailing zero.
    pub fn coefficients(&self) -> &[BigInt] {
        &self.coeffs
    }

    /// Whether this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// The leading coefficient, or zero for the zero polynomial.
    pub fn leading(&self) -> BigInt {
        self.coeffs.last().cloned().unwrap_or_else(int_zero)
    }

    /// `self + other`.
    pub fn add(&self, other: &Self) -> Self {
        let mut out = vec![int_zero(); self.coeffs.len().max(other.coeffs.len())];
        for (index, value) in self.coeffs.iter().enumerate() {
            out[index] += value;
        }
        for (index, value) in other.coeffs.iter().enumerate() {
            out[index] += value;
        }
        Self::from_coefficients(out)
    }

    /// `self - other`.
    pub fn sub(&self, other: &Self) -> Self {
        let mut out = vec![int_zero(); self.coeffs.len().max(other.coeffs.len())];
        for (index, value) in self.coeffs.iter().enumerate() {
            out[index] += value;
        }
        for (index, value) in other.coeffs.iter().enumerate() {
            out[index] -= value;
        }
        Self::from_coefficients(out)
    }

    /// `-self`.
    pub fn negated(&self) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(core::ops::Neg::neg).collect(),
        }
    }

    /// `self · other`.
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut out = vec![int_zero(); self.coeffs.len() + other.coeffs.len() - 1];
        for (i, left) in self.coeffs.iter().enumerate() {
            if int_is_zero(left) {
                continue;
            }
            for (j, right) in other.coeffs.iter().enumerate() {
                out[i + j] += left * right;
            }
        }
        Self::from_coefficients(out)
    }

    /// `self · factor` for an integer scalar.
    pub fn scale(&self, factor: &BigInt) -> Self {
        if int_is_zero(factor) {
            return Self::zero();
        }
        Self {
            coeffs: self.coeffs.iter().map(|c| c * factor).collect(),
        }
    }

    /// `self · x^by`.
    pub fn shifted(&self, by: usize) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let mut out = vec![int_zero(); by];
        out.extend(self.coeffs.iter().cloned());
        Self { coeffs: out }
    }

    /// The content: the non-negative gcd of the coefficients. Zero for the zero
    /// polynomial.
    pub fn content(&self) -> BigUint {
        let mut acc = BigUint::from(0u32);
        for coeff in &self.coeffs {
            acc = gcd_uint(&acc, coeff.magnitude());
        }
        acc
    }

    /// The primitive part: `self` divided by its content.
    ///
    /// The **sign of the leading coefficient is preserved**, because the
    /// content is non-negative. That is the property the Sturm chain depends
    /// on — a positive scale changes no sign variation — and it is why this is
    /// not [`ZPoly::with_positive_leading`].
    pub fn primitive_part(&self) -> Self {
        let content = self.content();
        if content == BigUint::from(0u32) || content == BigUint::from(1u32) {
            return self.clone();
        }
        let divisor = BigInt::from(content);
        Self {
            coeffs: self.coeffs.iter().map(|c| c / &divisor).collect(),
        }
    }

    /// `self`, negated if needed so the leading coefficient is positive.
    pub fn with_positive_leading(&self) -> Self {
        if self.leading().sign() == Sign::Minus {
            self.negated()
        } else {
            self.clone()
        }
    }

    /// `self / divisor` when every coefficient divides exactly; `None`
    /// otherwise, or when `divisor` is zero.
    pub fn exact_div_scalar(&self, divisor: &BigInt) -> Option<Self> {
        if int_is_zero(divisor) {
            return None;
        }
        let mut out = Vec::with_capacity(self.coeffs.len());
        for coeff in &self.coeffs {
            let quotient = coeff / divisor;
            let remainder = coeff % divisor;
            if !int_is_zero(&remainder) {
                return None;
            }
            out.push(quotient);
        }
        Some(Self::from_coefficients(out))
    }

    /// The polynomial exact quotient `self / divisor`, or `None` when the
    /// division is not exact in ℤ[x] (which includes a zero divisor).
    ///
    /// Bareiss's §V warning applies here in miniature: exact division is a
    /// **precondition**, not an invariant, and the cheap mitigation is free —
    /// the remainder is available, so it is checked.
    pub fn exact_div(&self, divisor: &Self) -> Option<Self> {
        let divisor_degree = divisor.degree()?;
        let lead = divisor.leading();
        let mut remainder = self.clone();
        let mut quotient = vec![int_zero(); self.coeffs.len().saturating_sub(divisor_degree) + 1];
        while let Some(remainder_degree) = remainder.degree() {
            if remainder_degree < divisor_degree {
                break;
            }
            let top = remainder.coeffs[remainder_degree].clone();
            if !int_is_zero(&(&top % &lead)) {
                return None;
            }
            let factor = top / &lead;
            let shift = remainder_degree - divisor_degree;
            quotient[shift] = factor.clone();
            remainder = remainder.sub(&divisor.scale(&factor).shifted(shift));
        }
        if remainder.is_zero() {
            Some(Self::from_coefficients(quotient))
        } else {
            None
        }
    }

    /// Evaluate at a rational point. Horner; exact.
    pub fn evaluate_rational(&self, at: &BigRational) -> BigRational {
        let mut acc = rat_zero();
        for coeff in self.coeffs.iter().rev() {
            acc = acc * at + BigRational::from(coeff.clone());
        }
        acc
    }

    /// The sign of `self` at a rational point: `-1`, `0` or `1`.
    pub fn sign_at(&self, at: &BigRational) -> i8 {
        rat_sign(&self.evaluate_rational(at))
    }

    /// The square-free part `self / gcd(self, self')`, primitive with a
    /// positive leading coefficient. `None` for the zero polynomial.
    pub fn squarefree_part(&self) -> Option<Self> {
        self.degree()?;
        let derivative = UnivariatePoly::derivative(self);
        if derivative.is_zero() {
            return Some(self.primitive_part().with_positive_leading());
        }
        let common = self.gcd(&derivative);
        if common.degree() == Some(0) {
            return Some(self.primitive_part().with_positive_leading());
        }
        let quotient = self.exact_div(&common)?;
        Some(quotient.primitive_part().with_positive_leading())
    }

    /// The primitive gcd over ℤ[x], with a positive leading coefficient.
    ///
    /// `gcd(0, 0)` is the zero polynomial. The content is handled separately
    /// from the primitive parts, which is what makes the subresultant PRS
    /// applicable: it computes a gcd of *primitive* polynomials.
    pub fn gcd(&self, other: &Self) -> Self {
        if self.is_zero() {
            return other.primitive_part().with_positive_leading();
        }
        if other.is_zero() {
            return self.primitive_part().with_positive_leading();
        }
        let content = gcd_int(
            &BigInt::from(self.content()),
            &BigInt::from(other.content()),
        );
        let left = self.primitive_part();
        let right = other.primitive_part();
        let primitive = primitive_prs_gcd(&left, &right);
        primitive.scale(&content).with_positive_leading()
    }

    /// The resultant of `self` and `other`, by fraction-free (Bareiss)
    /// elimination on the Sylvester matrix.
    ///
    /// `None` when either argument is zero or constant, where the Sylvester
    /// matrix is not defined at a positive dimension.
    ///
    /// The design note §5 sketches this as "computed from the subresultant
    /// PRS". Bareiss on the Sylvester matrix is used instead because every
    /// intermediate is identically a minor of the input (Bareiss Eq. (3)), so
    /// the operand-size argument is the same one, and the code has no sign
    /// bookkeeping to get wrong. [`ZPoly::subresultant_prs`] is still here and
    /// still the gcd route; the two are cross-checked in this module's tests.
    pub fn resultant_int(&self, other: &Self) -> Option<BigInt> {
        let m = self.degree()?;
        let n = other.degree()?;
        if m == 0 || n == 0 {
            return None;
        }
        let dimension = m + n;
        let mut matrix = vec![vec![int_zero(); dimension]; dimension];
        for row in 0..n {
            for (index, coeff) in self.coeffs.iter().enumerate() {
                matrix[row][row + m - index] = coeff.clone();
            }
        }
        for row in 0..m {
            for (index, coeff) in other.coeffs.iter().enumerate() {
                matrix[n + row][row + n - index] = coeff.clone();
            }
        }
        bareiss_determinant(matrix)
    }
}

impl UnivariatePoly for ZPoly {
    type Coeff = BigInt;

    fn degree(&self) -> Option<usize> {
        self.coeffs.len().checked_sub(1)
    }

    fn coefficient(&self, index: usize) -> BigInt {
        self.coeffs.get(index).cloned().unwrap_or_else(int_zero)
    }

    fn evaluate(&self, at: &BigInt) -> BigInt {
        let mut acc = int_zero();
        for coeff in self.coeffs.iter().rev() {
            acc = acc * at + coeff;
        }
        acc
    }

    fn derivative(&self) -> Self {
        Self::from_coefficients(
            self.coeffs
                .iter()
                .enumerate()
                .skip(1)
                .map(|(index, coeff)| coeff * BigInt::from(index))
                .collect(),
        )
    }
}

/// Fraction-free elimination (Bareiss) for the determinant of an integer
/// matrix. `None` on a non-square or empty matrix, or when a division that
/// Bareiss Eq. (3) says is exact turns out not to be.
fn bareiss_determinant(mut matrix: Vec<Vec<BigInt>>) -> Option<BigInt> {
    let dimension = matrix.len();
    if dimension == 0 || matrix.iter().any(|row| row.len() != dimension) {
        return None;
    }
    let mut sign = 1i8;
    let mut previous = int_one();
    for k in 0..dimension - 1 {
        if int_is_zero(&matrix[k][k]) {
            let Some(swap) = (k + 1..dimension).find(|&r| !int_is_zero(&matrix[r][k])) else {
                return Some(int_zero());
            };
            matrix.swap(k, swap);
            sign = -sign;
        }
        for i in k + 1..dimension {
            for j in k + 1..dimension {
                let numerator = &matrix[i][j] * &matrix[k][k] - &matrix[i][k] * &matrix[k][j];
                // Bareiss Eq. (3): this division is exact. Checked, not assumed.
                if !int_is_zero(&(&numerator % &previous)) {
                    return None;
                }
                matrix[i][j] = numerator / &previous;
            }
        }
        previous = matrix[k][k].clone();
    }
    let value = matrix[dimension - 1][dimension - 1].clone();
    Some(if sign < 0 { -value } else { value })
}

/// The gcd of two **primitive** integer polynomials, via the subresultant PRS.
fn primitive_prs_gcd(left: &ZPoly, right: &ZPoly) -> ZPoly {
    let sequence = left.subresultant_prs(right);
    let Some(last) = sequence.last() else {
        return ZPoly::zero();
    };
    if last.is_zero() || last.degree() == Some(0) {
        return ZPoly::constant(int_one());
    }
    last.primitive_part()
}

impl FractionFree for ZPoly {
    type GcdCertificate = PolyGcdCertificate;

    fn pseudo_remainder(&self, divisor: &Self) -> Option<Self> {
        let divisor_degree = divisor.degree()?;
        let lead = divisor.leading();
        let Some(self_degree) = self.degree() else {
            return Some(Self::zero());
        };
        if self_degree < divisor_degree {
            return Some(self.clone());
        }
        let mut exponent = u32::try_from(self_degree - divisor_degree + 1).ok()?;
        let mut remainder = self.clone();
        while let Some(remainder_degree) = remainder.degree() {
            if remainder_degree < divisor_degree {
                break;
            }
            let factor = remainder.coeffs[remainder_degree].clone();
            let shift = remainder_degree - divisor_degree;
            remainder = remainder
                .scale(&lead)
                .sub(&divisor.scale(&factor).shifted(shift));
            exponent -= 1;
        }
        Some(remainder.scale(&int_pow(&lead, exponent)))
    }

    fn subresultant_prs(&self, other: &Self) -> Vec<Self> {
        let (mut f, mut g) = match (self.degree(), other.degree()) {
            (None, _) => return vec![other.clone()],
            (_, None) => return vec![self.clone()],
            (Some(a), Some(b)) if a < b => (other.clone(), self.clone()),
            _ => (self.clone(), other.clone()),
        };
        let mut sequence = vec![f.clone(), g.clone()];
        // Brown (TOMS 4(3), 1978) / Knuth TAOCP 4.6.1 Algorithm C. `beta` is
        // the exact divisor of each pseudo-remainder and `psi` the auxiliary
        // that keeps it exact. Every division below is checked rather than
        // assumed — exactness here is a theorem, not a local invariant, and the
        // check is free because the remainder is already in hand.
        let mut delta = f.degree().unwrap_or(0) - g.degree().unwrap_or(0);
        let mut beta = if delta % 2 == 0 {
            -int_one()
        } else {
            int_one()
        };
        let mut psi = -int_one();
        loop {
            let Some(remainder) = f.pseudo_remainder(&g) else {
                break;
            };
            if remainder.is_zero() {
                break;
            }
            let Some(next) = remainder.exact_div_scalar(&beta) else {
                break;
            };
            sequence.push(next.clone());
            let lead = g.leading();
            let new_delta = g.degree().unwrap_or(0) - next.degree().unwrap_or(0);
            let Ok(delta_exp) = u32::try_from(delta) else {
                break;
            };
            psi = if delta > 1 {
                let numerator = int_pow(&-lead.clone(), delta_exp);
                let denominator = int_pow(&psi, delta_exp - 1);
                if int_is_zero(&denominator) || !int_is_zero(&(&numerator % &denominator)) {
                    break;
                }
                numerator / denominator
            } else {
                -lead.clone()
            };
            let Ok(new_exp) = u32::try_from(new_delta) else {
                break;
            };
            beta = -&lead * int_pow(&psi, new_exp);
            delta = new_delta;
            f = g;
            g = next;
        }
        sequence
    }

    fn resultant(&self, other: &Self) -> Option<Self> {
        ZPoly::resultant_int(self, other).map(ZPoly::constant)
    }

    fn gcd_certified(&self, other: &Self) -> (Self, Self::GcdCertificate) {
        let gcd = self.gcd(other);
        let certificate = PolyGcdCertificate::produce(self, other, &gcd);
        (gcd, certificate)
    }
}

// ---------------------------------------------------------------------------
// QPoly
// ---------------------------------------------------------------------------

/// A univariate polynomial over ℚ, little-endian and trimmed.
///
/// This is the shape the five `BigRational` copies in the inventory spell:
/// `Vec<BigRational>`, least-significant coefficient first, trailing zeros
/// dropped. [`QPoly::from_coefficients`] and [`QPoly::into_coefficients`] are
/// the boundary a caller crosses.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct QPoly {
    /// Little-endian coefficients with no trailing zero.
    coeffs: Vec<BigRational>,
}

impl QPoly {
    /// The zero polynomial.
    pub fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Build from little-endian coefficients, trimming trailing zeros.
    pub fn from_coefficients(mut coeffs: Vec<BigRational>) -> Self {
        while coeffs.last().is_some_and(rat_is_zero) {
            coeffs.pop();
        }
        Self { coeffs }
    }

    /// Build from a slice, trimming trailing zeros.
    pub fn from_slice(coeffs: &[BigRational]) -> Self {
        Self::from_coefficients(coeffs.to_vec())
    }

    /// The constant polynomial.
    pub fn constant(value: BigRational) -> Self {
        Self::from_coefficients(vec![value])
    }

    /// The little-endian coefficients, with no trailing zero.
    pub fn coefficients(&self) -> &[BigRational] {
        &self.coeffs
    }

    /// Consume, yielding the trimmed little-endian coefficients.
    pub fn into_coefficients(self) -> Vec<BigRational> {
        self.coeffs
    }

    /// Whether this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// The leading coefficient, or zero for the zero polynomial.
    pub fn leading(&self) -> BigRational {
        self.coeffs.last().cloned().unwrap_or_else(rat_zero)
    }

    /// `self + other`.
    pub fn add(&self, other: &Self) -> Self {
        let mut out = vec![rat_zero(); self.coeffs.len().max(other.coeffs.len())];
        for (index, value) in self.coeffs.iter().enumerate() {
            out[index] += value;
        }
        for (index, value) in other.coeffs.iter().enumerate() {
            out[index] += value;
        }
        Self::from_coefficients(out)
    }

    /// `self - other`.
    pub fn sub(&self, other: &Self) -> Self {
        let mut out = vec![rat_zero(); self.coeffs.len().max(other.coeffs.len())];
        for (index, value) in self.coeffs.iter().enumerate() {
            out[index] += value;
        }
        for (index, value) in other.coeffs.iter().enumerate() {
            out[index] -= value;
        }
        Self::from_coefficients(out)
    }

    /// `-self`.
    pub fn negated(&self) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(core::ops::Neg::neg).collect(),
        }
    }

    /// `self · other`.
    pub fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut out = vec![rat_zero(); self.coeffs.len() + other.coeffs.len() - 1];
        for (i, left) in self.coeffs.iter().enumerate() {
            if rat_is_zero(left) {
                continue;
            }
            for (j, right) in other.coeffs.iter().enumerate() {
                out[i + j] += left * right;
            }
        }
        Self::from_coefficients(out)
    }

    /// `self · factor` for a rational scalar.
    pub fn scale(&self, factor: &BigRational) -> Self {
        if rat_is_zero(factor) {
            return Self::zero();
        }
        Self {
            coeffs: self.coeffs.iter().map(|c| c * factor).collect(),
        }
    }

    /// `self · x^by`.
    pub fn shifted(&self, by: usize) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let mut out = vec![rat_zero(); by];
        out.extend(self.coeffs.iter().cloned());
        Self { coeffs: out }
    }

    /// The sign of `self` at a rational point: `-1`, `0` or `1`.
    pub fn sign_at(&self, at: &BigRational) -> i8 {
        rat_sign(&UnivariatePoly::evaluate(self, at))
    }

    /// `(quotient, remainder)` of long division in ℚ[x]. `None` exactly when
    /// `divisor` is the zero polynomial.
    pub fn div_rem(&self, divisor: &Self) -> Option<(Self, Self)> {
        let divisor_degree = divisor.degree()?;
        let lead = divisor.leading();
        let mut remainder = self.clone();
        let mut quotient = vec![rat_zero(); self.coeffs.len().saturating_sub(divisor_degree) + 1];
        while let Some(remainder_degree) = remainder.degree() {
            if remainder_degree < divisor_degree {
                break;
            }
            let factor = &remainder.coeffs[remainder_degree] / &lead;
            let shift = remainder_degree - divisor_degree;
            quotient[shift] = factor.clone();
            remainder = remainder.sub(&divisor.scale(&factor).shifted(shift));
        }
        Some((Self::from_coefficients(quotient), remainder))
    }

    /// The remainder of `self` on division by `divisor`. `None` exactly when
    /// `divisor` is the zero polynomial.
    pub fn rem(&self, divisor: &Self) -> Option<Self> {
        self.div_rem(divisor).map(|(_, remainder)| remainder)
    }

    /// The polynomial scaled so its leading coefficient is `1`. The zero
    /// polynomial is returned unchanged.
    pub fn monic(&self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let inverse = self.leading().recip();
        self.scale(&inverse)
    }

    /// `gcd(self, other)`, monic. `gcd(0, 0)` is the zero polynomial.
    ///
    /// The Euclidean loop runs over ℚ[x] but each remainder is scaled to a
    /// primitive integer polynomial before the next step, which is what stops
    /// the coefficients doubling in size at every step. The answer is made
    /// monic, so the scaling changes nothing observable — this is the
    /// normalization `fps_analytic.rs` applies and `numberfield.rs` does not,
    /// and the two agree on every input because of that final `monic`.
    pub fn gcd(&self, other: &Self) -> Self {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let Some(remainder) = a.rem(&b) else {
                break;
            };
            a = b;
            b = Self::from_integer_poly(&remainder.to_integer_poly());
        }
        a.monic()
    }

    /// The exact quotient `self / divisor`; the remainder is discarded.
    /// `None` exactly when `divisor` is the zero polynomial.
    pub fn div_exact(&self, divisor: &Self) -> Option<Self> {
        self.div_rem(divisor).map(|(quotient, _)| quotient)
    }

    /// The monic square-free part `self / gcd(self, self')` — the polynomial
    /// with the same real roots as `self`, each simple. `None` for the zero
    /// polynomial.
    pub fn squarefree_part(&self) -> Option<Self> {
        self.degree()?;
        let derivative = UnivariatePoly::derivative(self);
        if derivative.is_zero() {
            return Some(self.monic());
        }
        let common = self.gcd(&derivative);
        if common.degree().is_none_or(|degree| degree == 0) {
            return Some(self.monic());
        }
        let quotient = self.div_exact(&common)?;
        Some(quotient.monic())
    }

    /// A Cauchy bound `B = 1 + maxₖ |aₖ / aₙ|`: every real root lies in the
    /// **open** interval `(−B, B)`. `None` for the zero polynomial or a
    /// constant.
    pub fn cauchy_bound(&self) -> Option<BigRational> {
        let degree = self.degree()?;
        if degree == 0 {
            return None;
        }
        let lead = self.leading();
        let mut worst = rat_zero();
        for coeff in &self.coeffs[..degree] {
            let ratio = rat_abs(&(coeff / &lead));
            if ratio > worst {
                worst = ratio;
            }
        }
        Some(worst + rat_one())
    }

    /// Scale by a **positive** rational so the coefficients are coprime
    /// integers, and return them as a [`ZPoly`].
    ///
    /// This is the normalization `fps_analytic.rs` applies to every Sturm chain
    /// member. Sign variations are what a Sturm chain counts and a positive
    /// scale changes none of them, so the operation is free of semantic content
    /// — it exists only to stop the bignum coefficients doubling in size at
    /// every Euclidean step.
    pub fn to_integer_poly(&self) -> ZPoly {
        if self.is_zero() {
            return ZPoly::zero();
        }
        let mut denominator_lcm = BigUint::from(1u32);
        for coeff in &self.coeffs {
            let denominator = coeff.denom().magnitude().clone();
            let gcd = gcd_uint(&denominator_lcm, &denominator);
            denominator_lcm = &denominator_lcm / &gcd * &denominator;
        }
        let multiplier = BigInt::from(denominator_lcm);
        let scaled: Vec<BigInt> = self
            .coeffs
            .iter()
            .map(|coeff| (coeff * BigRational::from(multiplier.clone())).to_integer())
            .collect();
        ZPoly::from_coefficients(scaled).primitive_part()
    }

    /// Reinterpret an integer polynomial over ℚ.
    pub fn from_integer_poly(poly: &ZPoly) -> Self {
        Self::from_coefficients(
            poly.coefficients()
                .iter()
                .map(|c| BigRational::from(c.clone()))
                .collect(),
        )
    }

    /// Extended Euclid in ℚ[x]: `(g, u, v)` with `u·self + v·other = g` and `g`
    /// monic, packaged as a certificate the caller can re-derive.
    ///
    /// `g` is the zero polynomial exactly when both inputs are zero.
    pub fn ext_gcd(&self, other: &Self) -> PolyBezoutCertificate {
        let mut remainder_prev = self.clone();
        let mut remainder_curr = other.clone();
        let mut s_prev = Self::constant(rat_one());
        let mut s_curr = Self::zero();
        let mut t_prev = Self::zero();
        let mut t_curr = Self::constant(rat_one());
        while !remainder_curr.is_zero() {
            let Some((quotient, remainder)) = remainder_prev.div_rem(&remainder_curr) else {
                break;
            };
            let s_next = s_prev.sub(&quotient.mul(&s_curr));
            let t_next = t_prev.sub(&quotient.mul(&t_curr));
            remainder_prev = core::mem::replace(&mut remainder_curr, remainder);
            s_prev = core::mem::replace(&mut s_curr, s_next);
            t_prev = core::mem::replace(&mut t_curr, t_next);
        }
        let (gcd, cofactor_a, cofactor_b) = if remainder_prev.is_zero() {
            (remainder_prev, s_prev, t_prev)
        } else {
            let inverse = remainder_prev.leading().recip();
            (
                remainder_prev.scale(&inverse),
                s_prev.scale(&inverse),
                t_prev.scale(&inverse),
            )
        };
        PolyBezoutCertificate {
            gcd,
            cofactor_a,
            cofactor_b,
            input_a: self.clone(),
            input_b: other.clone(),
        }
    }

    /// The **half**-extended Euclidean algorithm: `(g, s)` with
    /// `g = gcd(self, modulus)` monic and `s · self ≡ g (mod modulus)`.
    ///
    /// Only the cofactor of `self` is tracked, which is all an inverse modulo
    /// `modulus` needs. A unit `g` therefore hands back `self⁻¹` directly, and
    /// **a non-unit `g` hands back a proper factor of `modulus`** — that is a
    /// first-class outcome, not an error. `qe_fibre.rs`'s on-demand modulus
    /// splitting is exactly a caller that treats it as one: a non-unit gcd is
    /// its signal to restart the enclosing quantifier elimination with a
    /// factored modulus (design note §5).
    ///
    /// Both components are the zero polynomial when the Euclidean chain ends at
    /// zero, which happens exactly when `modulus` and `self` are both zero.
    pub fn half_ext_gcd(&self, modulus: &Self) -> (Self, Self) {
        let mut r0 = modulus.clone();
        let mut r1 = self.clone();
        let mut s0 = Self::zero();
        let mut s1 = Self::constant(rat_one());
        while !r1.is_zero() {
            let Some((quotient, remainder)) = r0.div_rem(&r1) else {
                break;
            };
            r0 = r1;
            r1 = remainder;
            let next = s0.sub(&quotient.mul(&s1));
            s0 = s1;
            s1 = next;
        }
        if r0.is_zero() {
            return (Self::zero(), Self::zero());
        }
        let inverse = r0.leading().recip();
        (r0.scale(&inverse), s0.scale(&inverse))
    }
}

impl UnivariatePoly for QPoly {
    type Coeff = BigRational;

    fn degree(&self) -> Option<usize> {
        self.coeffs.len().checked_sub(1)
    }

    fn coefficient(&self, index: usize) -> BigRational {
        self.coeffs.get(index).cloned().unwrap_or_else(rat_zero)
    }

    fn evaluate(&self, at: &BigRational) -> BigRational {
        evaluate_slice(&self.coeffs, at)
    }

    fn derivative(&self) -> Self {
        Self::from_coefficients(
            self.coeffs
                .iter()
                .enumerate()
                .skip(1)
                .map(|(index, coeff)| coeff * BigRational::from(BigInt::from(index)))
                .collect(),
        )
    }
}

// ---------------------------------------------------------------------------
// Certificates
// ---------------------------------------------------------------------------

/// Bézout data over ℚ[x]: `gcd = cofactor_a·input_a + cofactor_b·input_b`.
///
/// ℚ[x] is a Euclidean domain, so unlike ℤ[x] the gcd genuinely is a ℚ[x]
/// combination of the inputs, and re-deriving it is two multiplications and an
/// addition. That is the whole checker; nothing of the producer's Euclidean
/// bookkeeping is reused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolyBezoutCertificate {
    /// The claimed gcd, monic (or zero when both inputs are zero).
    pub gcd: QPoly,
    /// The multiplier of `input_a`.
    pub cofactor_a: QPoly,
    /// The multiplier of `input_b`.
    pub cofactor_b: QPoly,
    /// The first input.
    pub input_a: QPoly,
    /// The second input.
    pub input_b: QPoly,
}

impl PolyBezoutCertificate {
    /// Re-derive the Bézout identity, the monic normalization, and the two
    /// divisibility conditions.
    ///
    /// Four independently-failable conditions, in this order:
    ///
    /// 1. the zero case — a zero gcd is admissible only when both inputs are;
    /// 2. `gcd` is monic;
    /// 3. `cofactor_a·input_a + cofactor_b·input_b = gcd`;
    /// 4. `gcd` divides each input with zero remainder.
    ///
    /// Condition 3 alone is not enough: `u·a + v·b` is a multiple of the true
    /// gcd for *any* cofactors, so a forger can hit the identity with a
    /// non-divisor. Condition 4 alone is not enough either: any common divisor
    /// passes it. Together they pin the gcd up to the unit that condition 2
    /// then fixes.
    pub fn verify(&self) -> bool {
        if self.gcd.is_zero() {
            return self.input_a.is_zero() && self.input_b.is_zero();
        }
        if self.gcd.leading() != rat_one() {
            return false;
        }
        let combination = self
            .cofactor_a
            .mul(&self.input_a)
            .add(&self.cofactor_b.mul(&self.input_b));
        if combination != self.gcd {
            return false;
        }
        for input in [&self.input_a, &self.input_b] {
            if input.is_zero() {
                continue;
            }
            let Some((_, remainder)) = input.div_rem(&self.gcd) else {
                return false;
            };
            if !remainder.is_zero() {
                return false;
            }
        }
        true
    }
}

/// The receipt a fraction-free ℤ[x] gcd carries.
///
/// ℤ[x] is **not** a Bézout domain, so `u·a + v·b = g` is not available over ℤ.
/// The certificate therefore records the two halves separately, which is also
/// what makes each half independently checkable:
///
/// - *`g` is a common divisor* — the exact quotients, re-multiplied;
/// - *`g` is a greatest one* — a ℚ[x] Bézout identity on the primitive parts,
///   which forces every common divisor to divide `g` in ℚ[x], plus the content
///   condition, which does the same in ℤ.
///
/// That split is the design note §6 rule "the certificate must carry every
/// distinction the producer makes": the producer computes the content and the
/// primitive part separately, so the receipt records both.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolyGcdCertificate {
    /// The claimed gcd, with a positive leading coefficient.
    pub gcd: ZPoly,
    /// `input_a / gcd`, exact.
    pub quotient_a: ZPoly,
    /// `input_b / gcd`, exact.
    pub quotient_b: ZPoly,
    /// The first input.
    pub input_a: ZPoly,
    /// The second input.
    pub input_b: ZPoly,
    /// The gcd of the two contents.
    pub content: BigUint,
    /// The maximality witness over ℚ[x], on the **primitive parts**.
    pub maximality: PolyBezoutCertificate,
}

impl PolyGcdCertificate {
    /// Build the receipt for a claimed gcd. Producing side; the checker is
    /// [`PolyGcdCertificate::verify`].
    fn produce(input_a: &ZPoly, input_b: &ZPoly, gcd: &ZPoly) -> Self {
        let quotient_a = input_a.exact_div(gcd).unwrap_or_else(ZPoly::zero);
        let quotient_b = input_b.exact_div(gcd).unwrap_or_else(ZPoly::zero);
        let content = gcd_uint(&input_a.content(), &input_b.content());
        let maximality = QPoly::from_integer_poly(&input_a.primitive_part())
            .ext_gcd(&QPoly::from_integer_poly(&input_b.primitive_part()));
        Self {
            gcd: gcd.clone(),
            quotient_a,
            quotient_b,
            input_a: input_a.clone(),
            input_b: input_b.clone(),
            content,
            maximality,
        }
    }

    /// Re-derive every recorded condition.
    ///
    /// Five independently-failable guards: the two divisibility identities, the
    /// content, the leading sign, and the ℚ[x] maximality witness (which is
    /// itself four more, in [`PolyBezoutCertificate::verify`]).
    pub fn verify(&self) -> bool {
        if self.gcd.is_zero() {
            return self.input_a.is_zero() && self.input_b.is_zero();
        }
        if self.gcd.leading().sign() != Sign::Plus {
            return false;
        }
        if self.gcd.mul(&self.quotient_a) != self.input_a {
            return false;
        }
        if self.gcd.mul(&self.quotient_b) != self.input_b {
            return false;
        }
        if self.gcd.content() != self.content {
            return false;
        }
        if !self.maximality.verify() {
            return false;
        }
        // The ℚ[x] gcd of the primitive parts must be the primitive part of the
        // claimed gcd, up to the monic normalization the witness carries.
        let claimed_primitive = QPoly::from_integer_poly(&self.gcd.primitive_part()).monic();
        self.maximality.gcd == claimed_primitive
    }
}

// ---------------------------------------------------------------------------
// Sturm chains and real-root isolation
// ---------------------------------------------------------------------------

/// The chain is bounded by the degree: each remainder drops the degree by at
/// least one, so `degree + 2` members is already unreachable. Named because
/// ADR-1702's caution applies — the `i128` copies used arithmetic exhaustion as
/// their termination argument, and a bignum carrier has to state the bound.
const CHAIN_LENGTH_SLACK: usize = 2;

/// A Sturm chain: `s₀ = primitive(squarefree(p))`, `s₁ = primitive(s₀′)`,
/// `s_{k+1} = primitive(−rem(s_{k−1}, s_k))`.
///
/// Every member is a primitive integer polynomial, reached from the ℚ[x]
/// remainder by a **positive** rational scale. Sign variations — the only thing
/// the chain is read for — are invariant under a positive scale, so this chain
/// gives the same count on every interval as an unnormalized one; it is the
/// bound on coefficient growth that differs, which is why `fps_analytic.rs`
/// normalizes and `qe_big.rs` does not.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SturmChain {
    members: Vec<ZPoly>,
}

impl SturmChain {
    /// Build the chain for a rational polynomial. `None` for the zero
    /// polynomial.
    pub fn new(polynomial: &QPoly) -> Option<Self> {
        let squarefree = polynomial.squarefree_part()?;
        Self::from_first_member(&squarefree.to_integer_poly())
    }

    /// Build the chain for an integer polynomial. `None` for the zero
    /// polynomial.
    pub fn from_integer_polynomial(polynomial: &ZPoly) -> Option<Self> {
        let squarefree = polynomial.squarefree_part()?;
        Self::from_first_member(&squarefree)
    }

    /// The chain from an already square-free, already primitive first member.
    fn from_first_member(first: &ZPoly) -> Option<Self> {
        let degree = first.degree()?;
        let mut members = vec![first.clone()];
        if degree == 0 {
            return Some(Self { members }); // a nonzero constant: no roots
        }
        let derivative = UnivariatePoly::derivative(first).primitive_part();
        if derivative.is_zero() {
            return Some(Self { members });
        }
        members.push(derivative);
        while members.len() <= degree + CHAIN_LENGTH_SLACK {
            let length = members.len();
            let previous = QPoly::from_integer_poly(&members[length - 2]);
            let current = QPoly::from_integer_poly(&members[length - 1]);
            let remainder = previous.rem(&current)?;
            if remainder.is_zero() {
                break;
            }
            members.push(remainder.negated().to_integer_poly());
        }
        Some(Self { members })
    }

    /// The chain members, first to last.
    pub fn members(&self) -> &[ZPoly] {
        &self.members
    }

    /// The number of sign changes in the chain at `x`, zeros skipped.
    pub fn variations(&self, x: &BigRational) -> usize {
        sign_variations(&self.members, x)
    }

    /// The number of **distinct** real roots in the half-open `(lower, upper]`.
    pub fn count_in(&self, lower: &BigRational, upper: &BigRational) -> usize {
        self.variations(lower)
            .saturating_sub(self.variations(upper))
    }

    /// Package a count on one interval as a re-derivable certificate.
    pub fn certificate(&self, lower: &BigRational, upper: &BigRational) -> SturmCertificate {
        SturmCertificate {
            chain: self
                .members
                .iter()
                .map(|member| member.coefficients().to_vec())
                .collect(),
            lower: lower.clone(),
            upper: upper.clone(),
            root_count: self.count_in(lower, upper),
        }
    }
}

/// Sign changes in a chain at `x`, zeros skipped.
///
/// This is the one routine [`SturmCertificate::verify`] shares with the
/// producer, and deliberately: the certificate records the chain, so recounting
/// it is the *check*, not a restatement of what the producer decided. What
/// `verify` does not reuse is how the chain was built — it rebuilds that from
/// the recorded first member.
pub(crate) fn sign_variations(chain: &[ZPoly], x: &BigRational) -> usize {
    let mut variations = 0usize;
    let mut previous: Option<i8> = None;
    for member in chain {
        let sign = member.sign_at(x);
        if sign == 0 {
            continue;
        }
        if previous.is_some_and(|prev| prev != sign) {
            variations += 1;
        }
        previous = Some(sign);
    }
    variations
}

/// How many bisections [`isolate_real_roots`] spends before declining.
///
/// The default matches `qe_big.rs`'s `MAX_ISOLATION_STEPS`, which is documented
/// as comfortable for a `10⁶⁰` coefficient (about 200 halvings) and finite for
/// everything else.
pub const DEFAULT_ISOLATION_STEPS: usize = 4096;

/// Isolate every distinct real root of `polynomial`, ascending.
///
/// Returns disjoint half-open brackets `(lower, upper]`, each Sturm-certified
/// to contain exactly one distinct real root; multiplicity is collapsed,
/// because the chain is built from the square-free part. `Some(vec![])` when
/// there are no real roots, including for a nonzero constant.
///
/// `None` for the zero polynomial, or when `max_steps` bisections are exhausted
/// — a resource cap, declining rather than looping.
pub fn isolate_real_roots(
    polynomial: &QPoly,
    max_steps: usize,
) -> Option<Vec<(BigRational, BigRational)>> {
    let degree = polynomial.degree()?;
    if degree == 0 {
        return Some(Vec::new());
    }
    let squarefree = polynomial.squarefree_part()?;
    let chain = SturmChain::new(&squarefree)?;
    let bound = squarefree.cauchy_bound()?;
    let two = BigRational::from(BigInt::from(2));
    let total = chain.count_in(&-bound.clone(), &bound);
    if total == 0 {
        return Some(Vec::new());
    }
    // A work list rather than recursion: the depth is data-dependent and the
    // step budget must be global, not per branch.
    let mut pending = vec![(-bound.clone(), bound, total)];
    let mut isolated: Vec<(BigRational, BigRational)> = Vec::new();
    let mut steps = 0usize;
    while let Some((lower, upper, count)) = pending.pop() {
        if count == 0 {
            continue;
        }
        if count == 1 {
            isolated.push((lower, upper));
            continue;
        }
        steps += 1;
        if steps > max_steps {
            return None;
        }
        let middle = (&lower + &upper) / &two;
        let left = chain.count_in(&lower, &middle);
        pending.push((middle.clone(), upper, count - left));
        pending.push((lower, middle, left));
    }
    isolated.sort_by(|a, b| a.0.cmp(&b.0));
    Some(isolated)
}

/// The number of distinct real roots of `polynomial` in the half-open interval
/// `(lower, upper]`. `None` only for the zero polynomial.
pub fn count_real_roots_in(
    polynomial: &QPoly,
    lower: &BigRational,
    upper: &BigRational,
) -> Option<usize> {
    let degree = polynomial.degree()?;
    if degree == 0 {
        return Some(0);
    }
    Some(SturmChain::new(polynomial)?.count_in(lower, upper))
}

/// The number of distinct real roots of `polynomial` in all of ℝ. `None` for
/// the zero polynomial.
pub fn count_real_roots(polynomial: &QPoly) -> Option<usize> {
    let degree = polynomial.degree()?;
    if degree == 0 {
        return Some(0);
    }
    let bound = polynomial.cauchy_bound()?;
    Some(SturmChain::new(polynomial)?.count_in(&-bound.clone(), &bound))
}

// ---------------------------------------------------------------------------
// The bodies of the two certificate checkers declared in `lib.rs`
// ---------------------------------------------------------------------------

/// [`SturmCertificate::verify`]'s body; see there for the contract.
pub(crate) fn verify_sturm_certificate(certificate: &SturmCertificate) -> bool {
    if certificate.chain.is_empty() {
        return false;
    }
    if certificate.lower > certificate.upper {
        return false;
    }
    let recorded: Vec<ZPoly> = certificate
        .chain
        .iter()
        .map(|coeffs| ZPoly::from_coefficients(coeffs.clone()))
        .collect();
    if recorded[0].is_zero() {
        return false;
    }
    // Guard 1: the chain is what this module's construction produces from the
    // recorded first member. A tampered member fails here and only here.
    let Some(rebuilt) = SturmChain::from_integer_polynomial(&recorded[0]) else {
        return false;
    };
    if rebuilt.members() != recorded.as_slice() {
        return false;
    }
    // Guard 2: the claimed count is the sign-variation difference of the
    // RECORDED chain. A tampered count fails here and only here.
    let at_lower = sign_variations(&recorded, &certificate.lower);
    let at_upper = sign_variations(&recorded, &certificate.upper);
    at_lower.saturating_sub(at_upper) == certificate.root_count
}

/// [`BezoutCertificate::verify`]'s body; see there for the contract.
pub(crate) fn verify_bezout_certificate(certificate: &BezoutCertificate) -> bool {
    if int_is_zero(&certificate.gcd) {
        return int_is_zero(&certificate.input_a) && int_is_zero(&certificate.input_b);
    }
    // Guard 1: Bézout certifies a gcd only up to sign, so the sign is pinned.
    if certificate.gcd.sign() != Sign::Plus {
        return false;
    }
    // Guard 2: the identity itself.
    let combination = &certificate.cofactor_a * &certificate.input_a
        + &certificate.cofactor_b * &certificate.input_b;
    if combination != certificate.gcd {
        return false;
    }
    // Guard 3: divisibility. The identity alone admits any multiple of the true
    // gcd, so this is what rules a forged `u·a + v·b` out.
    for input in [&certificate.input_a, &certificate.input_b] {
        if !int_is_zero(&(input % &certificate.gcd)) {
            return false;
        }
    }
    true
}

/// The extended Euclidean algorithm over ℤ, packaged as a certificate.
///
/// `gcd(0, 0)` is zero with zero cofactors. The gcd is always non-negative,
/// which is the normalization [`BezoutCertificate::verify`] pins.
pub fn extended_gcd(left: &BigInt, right: &BigInt) -> BezoutCertificate {
    let mut old_r = left.clone();
    let mut r = right.clone();
    let mut old_s = int_one();
    let mut s = int_zero();
    let mut old_t = int_zero();
    let mut t = int_one();
    while !int_is_zero(&r) {
        let quotient = &old_r / &r;
        let next_r = &old_r - &quotient * &r;
        let next_s = &old_s - &quotient * &s;
        let next_t = &old_t - &quotient * &t;
        old_r = core::mem::replace(&mut r, next_r);
        old_s = core::mem::replace(&mut s, next_s);
        old_t = core::mem::replace(&mut t, next_t);
    }
    if old_r.sign() == Sign::Minus {
        old_r = -old_r;
        old_s = -old_s;
        old_t = -old_t;
    }
    BezoutCertificate {
        gcd: old_r,
        cofactor_a: old_s,
        cofactor_b: old_t,
        input_a: left.clone(),
        input_b: right.clone(),
    }
}

// ---------------------------------------------------------------------------
// Zero-copy helpers for callers that hold a `&[BigRational]`
// ---------------------------------------------------------------------------

/// The degree of a little-endian coefficient slice, or `None` for the zero
/// polynomial. Does not require the slice to be trimmed.
///
/// This exists so a migrating caller does not have to clone a `Vec` into a
/// [`QPoly`] just to ask for a degree — `qe_big.rs` calls it inside the
/// isolation loop, where an allocation per query would be a real regression.
pub fn slice_degree(coeffs: &[BigRational]) -> Option<usize> {
    coeffs.iter().rposition(|c| !rat_is_zero(c))
}

/// Horner evaluation of a little-endian coefficient slice. Exact; total.
pub fn evaluate_slice(coeffs: &[BigRational], at: &BigRational) -> BigRational {
    let mut acc = rat_zero();
    for coeff in coeffs.iter().rev() {
        acc = acc * at + coeff;
    }
    acc
}

/// The sign of a little-endian coefficient slice at a rational point.
pub fn sign_at_slice(coeffs: &[BigRational], at: &BigRational) -> i8 {
    rat_sign(&evaluate_slice(coeffs, at))
}

/// Drop trailing zero coefficients. Consumes and returns the same allocation.
pub fn trim_coefficients(coeffs: Vec<BigRational>) -> Vec<BigRational> {
    QPoly::from_coefficients(coeffs).into_coefficients()
}

/// `-1`, `0` or `1` — the sign of a rational, without `num_traits::Signed`.
pub fn sign_of_rational(value: &BigRational) -> i8 {
    rat_sign(value)
}

/// Sign changes at `x` in a chain given as little-endian rational coefficient
/// vectors, zeros skipped.
///
/// The slice-shaped twin of [`SturmChain::variations`], for a caller that holds
/// the chain in the `Vec<Vec<BigRational>>` shape rather than as a
/// [`SturmChain`]. `fps_analytic.rs` is such a caller: its `RootCounter` carries
/// the chain in that shape across a fallback boundary.
pub fn sign_variations_rational(chain: &[Vec<BigRational>], x: &BigRational) -> usize {
    let mut variations = 0usize;
    let mut previous: Option<i8> = None;
    for member in chain {
        let sign = sign_at_slice(member, x);
        if sign == 0 {
            continue;
        }
        if previous.is_some_and(|prev| prev != sign) {
            variations += 1;
        }
        previous = Some(sign);
    }
    variations
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(values: &[(i64, i64)]) -> QPoly {
        QPoly::from_coefficients(
            values
                .iter()
                .map(|&(n, d)| BigRational::new(BigInt::from(n), BigInt::from(d)))
                .collect(),
        )
    }

    fn qi(values: &[i64]) -> QPoly {
        QPoly::from_coefficients(
            values
                .iter()
                .map(|&n| BigRational::from(BigInt::from(n)))
                .collect(),
        )
    }

    fn r(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    // -- ZPoly ring laws and the fraction-free layer --------------------------

    #[test]
    fn pseudo_remainder_satisfies_its_defining_identity() {
        // `lc(b)^(deg a - deg b + 1) · a ≡ prem(a, b)` modulo `b`, which is the
        // only property callers may rely on. Checked by re-deriving the
        // quotient: the scaled dividend minus the pseudo-remainder must be
        // exactly divisible by `b`.
        let cases: [(&[i64], &[i64]); 4] = [
            (&[-6, 11, -6, 1], &[-2, 1]),
            (&[1, 0, 0, 0, 3], &[5, 2, 7]),
            (&[2, 2, 2], &[3, 3]),
            (&[1], &[1, 1]),
        ];
        for (a, b) in cases {
            let a = ZPoly::from_i64(a);
            let b = ZPoly::from_i64(b);
            let remainder = FractionFree::pseudo_remainder(&a, &b).unwrap();
            let Some(degree_a) = a.degree() else { continue };
            let degree_b = b.degree().unwrap();
            if degree_a < degree_b {
                assert_eq!(remainder, a, "prem is the dividend below the divisor");
                continue;
            }
            let exponent = u32::try_from(degree_a - degree_b + 1).unwrap();
            let scaled = a.scale(&int_pow(&b.leading(), exponent));
            let difference = scaled.sub(&remainder);
            assert!(
                difference.exact_div(&b).is_some(),
                "prem identity failed for {a:?} / {b:?}"
            );
            assert!(remainder.degree().is_none_or(|d| d < degree_b));
        }
    }

    #[test]
    fn subresultant_prs_divisions_stay_exact_and_end_at_the_gcd() {
        // `(x-1)(x-2)(x-3)` and `(x-2)(x-3)(x-5)` share `(x-2)(x-3)`.
        let left = ZPoly::from_i64(&[-6, 11, -6, 1]);
        let right = ZPoly::from_i64(&[-30, 31, -10, 1]);
        let sequence = FractionFree::subresultant_prs(&left, &right);
        assert!(sequence.len() >= 3, "the PRS has at least one remainder");
        let gcd = left.gcd(&right);
        assert_eq!(gcd, ZPoly::from_i64(&[6, -5, 1]), "gcd is x^2 - 5x + 6");
        // Degrees must be strictly decreasing after the first pair.
        for window in sequence[1..].windows(2) {
            assert!(window[0].degree() > window[1].degree(), "PRS degrees drop");
        }
    }

    #[test]
    fn integer_gcd_keeps_the_content_and_the_positive_leading_sign() {
        // 2(x-1)(x-2) and 6(x-1)(x-3): content gcd 2, primitive gcd (x-1).
        let left = ZPoly::from_i64(&[4, -6, 2]);
        let right = ZPoly::from_i64(&[18, -24, 6]);
        assert_eq!(left.gcd(&right), ZPoly::from_i64(&[-2, 2]));
        // A negated input must not flip the answer's sign.
        assert_eq!(left.negated().gcd(&right), ZPoly::from_i64(&[-2, 2]));
        assert_eq!(ZPoly::zero().gcd(&ZPoly::zero()), ZPoly::zero());
    }

    #[test]
    fn resultant_matches_the_product_over_the_roots() {
        // For monic `f = Π(x - rᵢ)`, `Res(f, g) = Π g(rᵢ)`.
        let f = ZPoly::from_i64(&[-6, 11, -6, 1]); // roots 1, 2, 3
        let g = ZPoly::from_i64(&[5, 1]); // x + 5
        let expected: BigInt = [1i64, 2, 3]
            .iter()
            .map(|&root| UnivariatePoly::evaluate(&g, &BigInt::from(root)))
            .product();
        assert_eq!(f.resultant_int(&g), Some(expected));
        // A shared root forces a zero resultant.
        let shared = ZPoly::from_i64(&[-1, 1]);
        assert_eq!(f.resultant_int(&shared), Some(BigInt::from(0)));
        // Constants and the zero polynomial have no Sylvester matrix.
        assert_eq!(f.resultant_int(&ZPoly::from_i64(&[7])), None);
        assert_eq!(f.resultant_int(&ZPoly::zero()), None);
    }

    #[test]
    fn exact_division_declines_rather_than_rounding() {
        let a = ZPoly::from_i64(&[1, 0, 1]);
        let b = ZPoly::from_i64(&[1, 1]);
        assert_eq!(a.exact_div(&b), None, "x^2+1 is not divisible by x+1");
        assert_eq!(a.exact_div_scalar(&BigInt::from(2)), None);
        assert_eq!(a.exact_div_scalar(&BigInt::from(0)), None);
        let c = ZPoly::from_i64(&[-1, 0, 1]);
        assert_eq!(c.exact_div(&b), Some(ZPoly::from_i64(&[-1, 1])));
    }

    // -- QPoly ---------------------------------------------------------------

    #[test]
    fn rational_division_reassembles_the_dividend() {
        let a = q(&[(1, 2), (0, 1), (3, 4), (5, 1)]);
        let b = q(&[(2, 3), (1, 1)]);
        let (quotient, remainder) = a.div_rem(&b).unwrap();
        assert_eq!(quotient.mul(&b).add(&remainder), a);
        assert!(remainder.degree() < b.degree());
        assert_eq!(a.div_rem(&QPoly::zero()), None);
    }

    #[test]
    fn to_integer_poly_is_a_positive_scale() {
        // 1/2 + 3/4 x - 1/6 x^2 clears to 6 + 9x - 2x^2 (lcm 12, content 1).
        let p = q(&[(1, 2), (3, 4), (-1, 6)]);
        let z = p.to_integer_poly();
        assert_eq!(z, ZPoly::from_i64(&[6, 9, -2]));
        // The sign of the leading coefficient survives, which is what the
        // Sturm chain depends on.
        assert_eq!(z.leading().sign(), Sign::Minus);
        assert_eq!(QPoly::zero().to_integer_poly(), ZPoly::zero());
    }

    #[test]
    fn rational_gcd_and_squarefree_part_agree_with_hand_computation() {
        // (x-1)^2 (x-2) -> squarefree part (x-1)(x-2) = x^2 - 3x + 2, monic.
        let p = qi(&[-2, 5, -4, 1]);
        assert_eq!(p.squarefree_part(), Some(qi(&[2, -3, 1])));
        let a = qi(&[-6, 11, -6, 1]);
        let b = qi(&[6, -5, 1]);
        assert_eq!(a.gcd(&b), qi(&[6, -5, 1]));
        assert_eq!(a.scale(&r(-7, 3)).gcd(&b), qi(&[6, -5, 1]), "gcd is monic");
        assert_eq!(QPoly::zero().gcd(&QPoly::zero()), QPoly::zero());
    }

    // -- Certificates: the producer round-trips ------------------------------

    #[test]
    fn integer_bezout_round_trips() {
        for (a, b) in [(6i64, 4i64), (-6, 4), (0, 5), (5, 0), (0, 0), (17, 13)] {
            let certificate = extended_gcd(&BigInt::from(a), &BigInt::from(b));
            assert!(certificate.verify(), "bezout({a}, {b})");
        }
        assert_eq!(
            extended_gcd(&BigInt::from(-6), &BigInt::from(4)).gcd,
            BigInt::from(2),
            "the gcd is pinned non-negative"
        );
    }

    #[test]
    fn polynomial_bezout_round_trips() {
        let a = qi(&[-6, 11, -6, 1]);
        let b = qi(&[-30, 31, -10, 1]);
        let certificate = a.ext_gcd(&b);
        assert!(certificate.verify());
        assert_eq!(certificate.gcd, qi(&[6, -5, 1]));
        assert!(QPoly::zero().ext_gcd(&QPoly::zero()).verify());
        assert!(a.ext_gcd(&QPoly::zero()).verify());
    }

    #[test]
    fn half_ext_gcd_returns_the_inverse_or_the_factor() {
        // Modulus x^2 - 2 is irreducible over ℚ, so every nonzero element is a
        // unit and `g` comes back 1 with `s` the inverse.
        let modulus = qi(&[-2, 0, 1]);
        let element = qi(&[1, 1]); // 1 + x
        let (gcd, cofactor) = element.half_ext_gcd(&modulus);
        assert_eq!(gcd, qi(&[1]), "a unit gcd");
        let product = cofactor.mul(&element).rem(&modulus).unwrap();
        assert_eq!(product, qi(&[1]), "s · a ≡ 1 (mod m)");
        // A reducible modulus hands back a proper factor as the gcd, which is
        // the outcome `qe_fibre.rs` splits on rather than an error.
        let reducible = qi(&[-2, -1, 1]); // (x-2)(x+1)
        let (split, _) = qi(&[-2, 1]).half_ext_gcd(&reducible);
        assert_eq!(split, qi(&[-2, 1]), "the non-unit gcd is x - 2");
        assert_eq!(
            QPoly::zero().half_ext_gcd(&QPoly::zero()),
            (QPoly::zero(), QPoly::zero())
        );
    }

    #[test]
    fn integer_gcd_certificate_round_trips() {
        let left = ZPoly::from_i64(&[4, -6, 2]);
        let right = ZPoly::from_i64(&[18, -24, 6]);
        let (gcd, certificate) = FractionFree::gcd_certified(&left, &right);
        assert_eq!(gcd, ZPoly::from_i64(&[-2, 2]));
        assert!(certificate.verify());
        let (_, zero_certificate) = FractionFree::gcd_certified(&ZPoly::zero(), &ZPoly::zero());
        assert!(zero_certificate.verify());
    }

    // -- Certificates: the forgeries, one per guard --------------------------
    //
    // Each of these tampers with EXACTLY ONE recorded field and asserts the
    // certificate is rejected. If a guard is deleted, exactly one of these
    // dies — which is the property `CLAUDE.md` requires of a checker, and the
    // reason the guards are written as separate early returns rather than one
    // conjunction.

    #[test]
    fn a_forged_bezout_gcd_sign_is_rejected() {
        let mut certificate = extended_gcd(&BigInt::from(6), &BigInt::from(4));
        certificate.gcd = -certificate.gcd;
        certificate.cofactor_a = -certificate.cofactor_a;
        certificate.cofactor_b = -certificate.cofactor_b;
        // The identity and both divisibilities still hold; only the sign
        // normalization is violated.
        assert!(!certificate.verify());
    }

    #[test]
    fn a_forged_bezout_identity_is_rejected() {
        let mut certificate = extended_gcd(&BigInt::from(6), &BigInt::from(4));
        certificate.cofactor_a += BigInt::from(1);
        // `g` still divides both inputs; the combination no longer equals it.
        assert!(!certificate.verify());
    }

    #[test]
    fn a_bezout_non_divisor_is_rejected_even_though_the_identity_holds() {
        // 6·1 + 4·1 = 10, and 10 is a perfectly good value of `u·a + v·b` —
        // but it divides neither input. This is the forgery the identity guard
        // alone cannot catch.
        let certificate = BezoutCertificate {
            gcd: BigInt::from(10),
            cofactor_a: BigInt::from(1),
            cofactor_b: BigInt::from(1),
            input_a: BigInt::from(6),
            input_b: BigInt::from(4),
        };
        let combination = &certificate.cofactor_a * &certificate.input_a
            + &certificate.cofactor_b * &certificate.input_b;
        assert_eq!(
            combination, certificate.gcd,
            "the identity really does hold"
        );
        assert!(!certificate.verify());
    }

    #[test]
    fn a_forged_bezout_zero_gcd_is_rejected() {
        let certificate = BezoutCertificate {
            gcd: BigInt::from(0),
            cofactor_a: BigInt::from(0),
            cofactor_b: BigInt::from(0),
            input_a: BigInt::from(6),
            input_b: BigInt::from(0),
        };
        assert!(!certificate.verify());
    }

    #[test]
    fn a_forged_polynomial_bezout_is_rejected_three_ways() {
        let a = qi(&[-6, 11, -6, 1]);
        let b = qi(&[-30, 31, -10, 1]);
        let good = a.ext_gcd(&b);

        let mut wrong_identity = good.clone();
        wrong_identity.cofactor_a = wrong_identity.cofactor_a.add(&qi(&[1]));
        assert!(!wrong_identity.verify(), "identity guard");

        let mut not_monic = good.clone();
        not_monic.gcd = not_monic.gcd.scale(&r(2, 1));
        not_monic.cofactor_a = not_monic.cofactor_a.scale(&r(2, 1));
        not_monic.cofactor_b = not_monic.cofactor_b.scale(&r(2, 1));
        assert!(!not_monic.verify(), "monic guard");

        // `x·(x−1) − x·(x−2) = x`, so the identity holds exactly — and `x`
        // divides neither `x−1` nor `x−2`. This is the forgery the identity
        // guard alone cannot catch: `u·a + v·b` is a multiple of the true gcd
        // for ANY cofactors, so hitting the identity proves nothing on its own.
        let forged = PolyBezoutCertificate {
            gcd: qi(&[0, 1]),
            cofactor_a: qi(&[0, 1]),
            cofactor_b: qi(&[0, -1]),
            input_a: qi(&[-1, 1]),
            input_b: qi(&[-2, 1]),
        };
        let combination = forged
            .cofactor_a
            .mul(&forged.input_a)
            .add(&forged.cofactor_b.mul(&forged.input_b));
        assert_eq!(combination, forged.gcd, "the identity really does hold");
        assert!(!forged.verify(), "divisibility guard");
    }

    #[test]
    fn a_forged_integer_gcd_certificate_is_rejected_per_field() {
        let left = ZPoly::from_i64(&[4, -6, 2]);
        let right = ZPoly::from_i64(&[18, -24, 6]);
        let (_, good) = FractionFree::gcd_certified(&left, &right);

        let mut wrong_quotient = good.clone();
        wrong_quotient.quotient_a = wrong_quotient.quotient_a.add(&ZPoly::from_i64(&[1]));
        assert!(!wrong_quotient.verify(), "divisibility guard");

        let mut wrong_content = good.clone();
        wrong_content.content = BigUint::from(1u32);
        assert!(!wrong_content.verify(), "content guard");

        let mut wrong_sign = good.clone();
        wrong_sign.gcd = wrong_sign.gcd.negated();
        wrong_sign.quotient_a = wrong_sign.quotient_a.negated();
        wrong_sign.quotient_b = wrong_sign.quotient_b.negated();
        assert!(!wrong_sign.verify(), "leading-sign guard");

        let mut wrong_maximality = good.clone();
        wrong_maximality.maximality.cofactor_a =
            wrong_maximality.maximality.cofactor_a.add(&qi(&[1]));
        assert!(!wrong_maximality.verify(), "maximality guard");
    }

    // -- Sturm ---------------------------------------------------------------

    #[test]
    fn sturm_counts_match_hand_computation() {
        // (x-1)(x-2)(x-3).
        let p = qi(&[-6, 11, -6, 1]);
        assert_eq!(count_real_roots(&p), Some(3));
        assert_eq!(count_real_roots_in(&p, &r(0, 1), &r(2, 1)), Some(2));
        assert_eq!(count_real_roots_in(&p, &r(2, 1), &r(4, 1)), Some(1));
        assert_eq!(count_real_roots_in(&p, &r(4, 1), &r(10, 1)), Some(0));
        // Multiplicity collapses: (x-1)^2 has one distinct root.
        assert_eq!(count_real_roots(&qi(&[1, -2, 1])), Some(1));
        // No real roots, and the constant / zero boundary.
        assert_eq!(count_real_roots(&qi(&[1, 0, 1])), Some(0));
        assert_eq!(count_real_roots(&qi(&[7])), Some(0));
        assert_eq!(count_real_roots(&QPoly::zero()), None);
    }

    #[test]
    fn isolation_brackets_exactly_one_root_each() {
        let p = qi(&[-6, 11, -6, 1]);
        let brackets = isolate_real_roots(&p, DEFAULT_ISOLATION_STEPS).unwrap();
        assert_eq!(brackets.len(), 3);
        for (lower, upper) in &brackets {
            assert_eq!(count_real_roots_in(&p, lower, upper), Some(1));
        }
        // Ascending and pairwise disjoint.
        for pair in brackets.windows(2) {
            assert!(pair[0].1 <= pair[1].0);
        }
        // Irrational roots: x^2 - 2.
        let irrational = qi(&[-2, 0, 1]);
        let two = isolate_real_roots(&irrational, DEFAULT_ISOLATION_STEPS).unwrap();
        assert_eq!(two.len(), 2);
        assert_eq!(
            isolate_real_roots(&qi(&[7]), DEFAULT_ISOLATION_STEPS),
            Some(Vec::new())
        );
        assert_eq!(
            isolate_real_roots(&QPoly::zero(), DEFAULT_ISOLATION_STEPS),
            None
        );
    }

    #[test]
    fn the_isolation_step_budget_declines_rather_than_looping() {
        // Zero steps cannot separate three roots, so the cap must fire. This is
        // the bound ADR-1702 requires a bignum route to state explicitly: the
        // `i128` copies used arithmetic exhaustion instead.
        assert_eq!(isolate_real_roots(&qi(&[-6, 11, -6, 1]), 0), None);
    }

    #[test]
    fn a_positive_rescale_of_the_input_changes_no_count() {
        // The whole argument for one shared chain replacing two normalization
        // conventions: a positive scale is invisible to sign variations.
        let p = qi(&[-6, 11, -6, 1]);
        for factor in [r(1, 1), r(7, 1), r(1, 12), r(100_000, 3)] {
            assert_eq!(
                count_real_roots(&p.scale(&factor)),
                Some(3),
                "scaled by {factor}"
            );
        }
        // A NEGATIVE scale is also invisible, because the chain is rebuilt from
        // the square-free part which is re-normalized monic.
        assert_eq!(count_real_roots(&p.scale(&r(-5, 1))), Some(3));
    }

    #[test]
    fn sturm_certificate_round_trips() {
        let p = qi(&[-6, 11, -6, 1]);
        let chain = SturmChain::new(&p).unwrap();
        let certificate = chain.certificate(&r(0, 1), &r(2, 1));
        assert_eq!(certificate.root_count, 2);
        assert!(certificate.verify());
    }

    #[test]
    fn a_forged_sturm_count_is_rejected() {
        let p = qi(&[-6, 11, -6, 1]);
        let chain = SturmChain::new(&p).unwrap();
        let mut certificate = chain.certificate(&r(0, 1), &r(2, 1));
        certificate.root_count += 1;
        assert!(!certificate.verify(), "the count guard");
    }

    #[test]
    fn a_forged_sturm_chain_member_is_rejected() {
        let p = qi(&[-6, 11, -6, 1]);
        let chain = SturmChain::new(&p).unwrap();
        let mut certificate = chain.certificate(&r(0, 1), &r(2, 1));
        // Scale one interior member by a positive constant. The sign variations
        // — and therefore the recorded count — are UNCHANGED, so only the
        // chain-recomputation guard can catch this.
        let index = certificate.chain.len() - 1;
        certificate.chain[index] = certificate.chain[index]
            .iter()
            .map(|c| c * BigInt::from(3))
            .collect();
        let recorded: Vec<ZPoly> = certificate
            .chain
            .iter()
            .map(|coeffs| ZPoly::from_coefficients(coeffs.clone()))
            .collect();
        assert_eq!(
            sign_variations(&recorded, &certificate.lower)
                .saturating_sub(sign_variations(&recorded, &certificate.upper)),
            certificate.root_count,
            "the count guard still passes, so only the chain guard can fire"
        );
        assert!(!certificate.verify(), "the chain guard");
    }

    #[test]
    fn a_forged_sturm_first_member_is_rejected() {
        // A chain whose head is not square-free rebuilds to something else.
        let p = qi(&[1, -2, 1]); // (x-1)^2
        let chain = SturmChain::new(&qi(&[-1, 1])).unwrap();
        let mut certificate = chain.certificate(&r(0, 1), &r(2, 1));
        certificate.chain[0] = p.to_integer_poly().coefficients().to_vec();
        assert!(!certificate.verify());
    }

    #[test]
    fn a_sturm_certificate_with_an_inverted_interval_is_rejected() {
        // `x² + 1` has no real roots, so the count is 0 on every interval and
        // `saturating_sub` gives 0 on an inverted one too. That is deliberate:
        // it makes the COUNT guard indifferent to the swap, so only the
        // interval guard can reject this certificate. Picking a polynomial with
        // roots would let the count guard catch it and the interval guard would
        // then be untestable — a guard nobody can remove is decoration.
        let chain = SturmChain::new(&qi(&[1, 0, 1])).unwrap();
        let mut certificate = chain.certificate(&r(0, 1), &r(2, 1));
        assert_eq!(certificate.root_count, 0);
        core::mem::swap(&mut certificate.lower, &mut certificate.upper);
        let recorded: Vec<ZPoly> = certificate
            .chain
            .iter()
            .map(|coeffs| ZPoly::from_coefficients(coeffs.clone()))
            .collect();
        assert_eq!(
            sign_variations(&recorded, &certificate.lower)
                .saturating_sub(sign_variations(&recorded, &certificate.upper)),
            certificate.root_count,
            "the count guard still passes, so only the interval guard can fire"
        );
        assert!(!certificate.verify(), "the interval guard");
    }

    #[test]
    fn an_empty_sturm_chain_is_rejected() {
        let certificate = SturmCertificate {
            chain: Vec::new(),
            lower: r(0, 1),
            upper: r(1, 1),
            root_count: 0,
        };
        assert!(!certificate.verify());
    }

    #[test]
    fn a_zero_headed_sturm_chain_is_rejected() {
        let certificate = SturmCertificate {
            chain: vec![vec![BigInt::from(0)]],
            lower: r(0, 1),
            upper: r(1, 1),
            root_count: 0,
        };
        assert!(!certificate.verify());
    }

    #[test]
    fn big_coefficients_do_not_overflow_the_way_the_i128_copies_do() {
        // `x^2 - 10^30`: the wall `qe_big.rs`'s module doc names, where the
        // `i128` Sturm chain squares a Cauchy bound of 10^30 + 1.
        let big = BigInt::from(10u8).pow(30);
        let p = QPoly::from_coefficients(vec![
            BigRational::from(-big),
            BigRational::from(BigInt::from(0)),
            BigRational::from(BigInt::from(1)),
        ]);
        assert_eq!(count_real_roots(&p), Some(2));
        let brackets = isolate_real_roots(&p, DEFAULT_ISOLATION_STEPS).unwrap();
        assert_eq!(brackets.len(), 2);
    }
}
