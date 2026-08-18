//! Bounded bit-packed polynomials and irreducibility certificates over `GF(2)`.
//!
//! Search is not trusted.  [`certify_irreducible`] emits the polynomial
//! identities required by Rabin's criterion, and [`check_irreducible_certificate`]
//! checks those identities without calling the producer's irreducibility
//! verdict.  All potentially large work runs through [`Gf2Context`].

use core::fmt;

/// A normalized polynomial over `GF(2)`, packed coefficient-first into words.
///
/// Bit `i` is the coefficient of `x^i`; trailing zero words are absent.
#[derive(Clone, Default, Eq, PartialEq)]
pub struct Gf2Poly {
    words: Vec<u64>,
}

impl fmt::Debug for Gf2Poly {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Gf2Poly")
            .field("exponents", &self.exponents())
            .finish()
    }
}

impl Gf2Poly {
    /// Construct from little-endian coefficient words and normalize.
    #[must_use]
    pub fn from_words(mut words: Vec<u64>) -> Self {
        trim(&mut words);
        Self { words }
    }

    /// Construct from a list of nonzero exponents under an allocation limit.
    ///
    /// # Errors
    ///
    /// Returns [`Gf2Error::DegreeLimit`] when the largest exponent exceeds the
    /// intermediate-polynomial ceiling.
    pub fn from_exponents(exponents: &[usize], limits: Gf2Limits) -> Result<Self, Gf2Error> {
        let degree = exponents.iter().copied().max().unwrap_or(0);
        if !exponents.is_empty() && degree > limits.max_intermediate_degree {
            return Err(Gf2Error::DegreeLimit {
                observed: degree,
                limit: limits.max_intermediate_degree,
            });
        }
        let word_count = if exponents.is_empty() {
            0
        } else {
            degree / 64 + 1
        };
        let mut words = vec![0; word_count];
        for &exponent in exponents {
            words[exponent / 64] ^= 1_u64 << (exponent % 64);
        }
        Ok(Self::from_words(words))
    }

    /// The zero polynomial.
    #[must_use]
    pub const fn zero() -> Self {
        Self { words: Vec::new() }
    }

    /// The constant polynomial one.
    #[must_use]
    pub fn one() -> Self {
        Self { words: vec![1] }
    }

    /// The polynomial `x`.
    #[must_use]
    pub fn x() -> Self {
        Self { words: vec![2] }
    }

    /// Return the coefficient words in canonical little-endian order.
    #[must_use]
    pub fn words(&self) -> &[u64] {
        &self.words
    }

    /// Return the degree, or `None` for zero.
    #[must_use]
    pub fn degree(&self) -> Option<usize> {
        let last = *self.words.last()?;
        let high = usize::try_from(u64::BITS - 1 - last.leading_zeros()).ok()?;
        Some((self.words.len() - 1) * 64 + high)
    }

    /// Whether this is zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.words.is_empty()
    }

    /// Whether the coefficient at `exponent` is one.
    #[must_use]
    pub fn coefficient(&self, exponent: usize) -> bool {
        self.words
            .get(exponent / 64)
            .is_some_and(|word| word & (1_u64 << (exponent % 64)) != 0)
    }

    /// Return the nonzero exponents in ascending order.
    #[must_use]
    pub fn exponents(&self) -> Vec<usize> {
        let mut result = Vec::new();
        for (word_index, &source) in self.words.iter().enumerate() {
            let mut word = source;
            while word != 0 {
                let bit = usize::try_from(word.trailing_zeros()).unwrap_or(0);
                result.push(word_index * 64 + bit);
                word &= word - 1;
            }
        }
        result
    }
}

/// Deterministic resource ceilings for `GF(2)[x]` work.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Gf2Limits {
    /// Maximum degree of a candidate presented for irreducibility checking.
    pub max_input_degree: usize,
    /// Maximum degree of an intermediate polynomial.
    pub max_intermediate_degree: usize,
    /// Maximum number of Frobenius squarings in one certificate.
    pub max_frobenius_steps: usize,
    /// Approximate word-level work ceiling shared by an operation context.
    pub max_word_ops: u64,
}

impl Default for Gf2Limits {
    fn default() -> Self {
        Self {
            max_input_degree: 4_096,
            max_intermediate_degree: 8_192,
            max_frobenius_steps: 4_096,
            max_word_ops: 50_000_000,
        }
    }
}

/// Typed failure or bounded decline from `GF(2)[x]` work.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Gf2Error {
    /// Irreducibility is defined here only for positive-degree polynomials.
    NotPositiveDegree,
    /// Division by the zero polynomial was requested.
    DivisionByZero,
    /// A polynomial exceeded a configured degree ceiling.
    DegreeLimit {
        /// Degree that was encountered.
        observed: usize,
        /// Configured degree ceiling.
        limit: usize,
    },
    /// A certificate requires more Frobenius steps than allowed.
    FrobeniusLimit {
        /// Number of steps required by the input degree.
        observed: usize,
        /// Configured step ceiling.
        limit: usize,
    },
    /// The deterministic word-operation budget was exhausted.
    WorkLimit {
        /// Work that the attempted operation would have consumed.
        used: u64,
        /// Configured work ceiling.
        limit: u64,
    },
    /// A supplied certificate failed a structural or algebraic check.
    InvalidCertificate(&'static str),
}

impl fmt::Display for Gf2Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotPositiveDegree => write!(formatter, "polynomial has no positive degree"),
            Self::DivisionByZero => write!(formatter, "division by the zero polynomial"),
            Self::DegreeLimit { observed, limit } => {
                write!(
                    formatter,
                    "polynomial degree {observed} exceeds limit {limit}"
                )
            }
            Self::FrobeniusLimit { observed, limit } => {
                write!(formatter, "{observed} Frobenius steps exceed limit {limit}")
            }
            Self::WorkLimit { used, limit } => {
                write!(
                    formatter,
                    "word-operation count {used} exceeds limit {limit}"
                )
            }
            Self::InvalidCertificate(message) => {
                write!(formatter, "invalid certificate: {message}")
            }
        }
    }
}

impl std::error::Error for Gf2Error {}

/// A bounded arithmetic context.  Its work counter is monotone.
#[derive(Clone, Debug)]
pub struct Gf2Context {
    limits: Gf2Limits,
    word_ops: u64,
}

impl Gf2Context {
    /// Start a fresh context with the supplied ceilings.
    #[must_use]
    pub const fn new(limits: Gf2Limits) -> Self {
        Self {
            limits,
            word_ops: 0,
        }
    }

    /// Approximate word-level work charged so far.
    #[must_use]
    pub const fn word_ops(&self) -> u64 {
        self.word_ops
    }

    fn charge(&mut self, amount: usize) -> Result<(), Gf2Error> {
        let amount = u64::try_from(amount).unwrap_or(u64::MAX);
        let used = self.word_ops.saturating_add(amount);
        if used > self.limits.max_word_ops {
            return Err(Gf2Error::WorkLimit {
                used,
                limit: self.limits.max_word_ops,
            });
        }
        self.word_ops = used;
        Ok(())
    }

    fn ensure_intermediate(&self, polynomial: &Gf2Poly) -> Result<(), Gf2Error> {
        if let Some(observed) = polynomial.degree()
            && observed > self.limits.max_intermediate_degree
        {
            return Err(Gf2Error::DegreeLimit {
                observed,
                limit: self.limits.max_intermediate_degree,
            });
        }
        Ok(())
    }

    /// Add polynomials (coefficient-wise XOR).
    ///
    /// # Errors
    ///
    /// Returns a typed degree or work-limit decline.
    pub fn add(&mut self, left: &Gf2Poly, right: &Gf2Poly) -> Result<Gf2Poly, Gf2Error> {
        self.ensure_intermediate(left)?;
        self.ensure_intermediate(right)?;
        let length = left.words.len().max(right.words.len());
        self.charge(length)?;
        let mut words = vec![0; length];
        for (index, word) in words.iter_mut().enumerate() {
            *word = left.words.get(index).copied().unwrap_or(0)
                ^ right.words.get(index).copied().unwrap_or(0);
        }
        Ok(Gf2Poly::from_words(words))
    }

    /// Carryless polynomial multiplication.
    ///
    /// # Errors
    ///
    /// Returns a typed degree or work-limit decline.
    pub fn multiply(&mut self, left: &Gf2Poly, right: &Gf2Poly) -> Result<Gf2Poly, Gf2Error> {
        self.ensure_intermediate(left)?;
        self.ensure_intermediate(right)?;
        if left.is_zero() || right.is_zero() {
            return Ok(Gf2Poly::zero());
        }
        let degree = left
            .degree()
            .and_then(|value| value.checked_add(right.degree()?))
            .ok_or(Gf2Error::DegreeLimit {
                observed: usize::MAX,
                limit: self.limits.max_intermediate_degree,
            })?;
        if degree > self.limits.max_intermediate_degree {
            return Err(Gf2Error::DegreeLimit {
                observed: degree,
                limit: self.limits.max_intermediate_degree,
            });
        }
        let mut words = vec![0; degree / 64 + 1];
        for exponent in left.exponents() {
            self.charge(right.words.len().saturating_add(1))?;
            xor_shifted(&mut words, &right.words, exponent);
        }
        Ok(Gf2Poly::from_words(words))
    }

    /// Square a polynomial using characteristic-two exponent doubling.
    ///
    /// # Errors
    ///
    /// Returns a typed degree or work-limit decline.
    pub fn square(&mut self, polynomial: &Gf2Poly) -> Result<Gf2Poly, Gf2Error> {
        self.ensure_intermediate(polynomial)?;
        let Some(degree) = polynomial.degree() else {
            return Ok(Gf2Poly::zero());
        };
        let square_degree = degree.checked_mul(2).ok_or(Gf2Error::DegreeLimit {
            observed: usize::MAX,
            limit: self.limits.max_intermediate_degree,
        })?;
        if square_degree > self.limits.max_intermediate_degree {
            return Err(Gf2Error::DegreeLimit {
                observed: square_degree,
                limit: self.limits.max_intermediate_degree,
            });
        }
        let exponents = polynomial.exponents();
        self.charge(polynomial.words.len().saturating_add(exponents.len()))?;
        let mut words = vec![0; square_degree / 64 + 1];
        for exponent in exponents {
            let doubled = exponent * 2;
            words[doubled / 64] |= 1_u64 << (doubled % 64);
        }
        Ok(Gf2Poly::from_words(words))
    }

    /// Divide by a nonzero polynomial, returning `(quotient, remainder)`.
    ///
    /// # Errors
    ///
    /// Returns [`Gf2Error::DivisionByZero`] for a zero divisor, or a typed
    /// degree or work-limit decline.
    pub fn div_rem(
        &mut self,
        dividend: &Gf2Poly,
        divisor: &Gf2Poly,
    ) -> Result<(Gf2Poly, Gf2Poly), Gf2Error> {
        self.ensure_intermediate(dividend)?;
        self.ensure_intermediate(divisor)?;
        let divisor_degree = divisor.degree().ok_or(Gf2Error::DivisionByZero)?;
        let mut remainder = dividend.words.clone();
        let quotient_length = dividend
            .degree()
            .filter(|degree| *degree >= divisor_degree)
            .map_or(0, |degree| (degree - divisor_degree) / 64 + 1);
        let mut quotient = vec![0; quotient_length];
        while let Some(remainder_degree) = degree_words(&remainder) {
            if remainder_degree < divisor_degree {
                break;
            }
            let shift = remainder_degree - divisor_degree;
            quotient[shift / 64] ^= 1_u64 << (shift % 64);
            self.charge(divisor.words.len().saturating_add(1))?;
            xor_shifted(&mut remainder, &divisor.words, shift);
            trim(&mut remainder);
        }
        Ok((
            Gf2Poly::from_words(quotient),
            Gf2Poly::from_words(remainder),
        ))
    }

    /// Greatest common divisor, normalized to monic (automatic over `GF(2)`).
    ///
    /// # Errors
    ///
    /// Returns a typed degree or work-limit decline from polynomial division.
    pub fn gcd(&mut self, left: &Gf2Poly, right: &Gf2Poly) -> Result<Gf2Poly, Gf2Error> {
        let mut first = left.clone();
        let mut second = right.clone();
        while !second.is_zero() {
            let (_, remainder) = self.div_rem(&first, &second)?;
            first = second;
            second = remainder;
        }
        Ok(first)
    }

    fn extended_gcd(
        &mut self,
        left: &Gf2Poly,
        right: &Gf2Poly,
    ) -> Result<(Gf2Poly, Gf2Poly, Gf2Poly), Gf2Error> {
        let mut old_remainder = left.clone();
        let mut remainder = right.clone();
        let mut old_left = Gf2Poly::one();
        let mut left_coefficient = Gf2Poly::zero();
        let mut old_right = Gf2Poly::zero();
        let mut right_coefficient = Gf2Poly::one();

        while !remainder.is_zero() {
            let (quotient, new_remainder) = self.div_rem(&old_remainder, &remainder)?;
            old_remainder = remainder;
            remainder = new_remainder;

            let product = self.multiply(&quotient, &left_coefficient)?;
            let next = self.add(&old_left, &product)?;
            old_left = left_coefficient;
            left_coefficient = next;

            let product = self.multiply(&quotient, &right_coefficient)?;
            let next = self.add(&old_right, &product)?;
            old_right = right_coefficient;
            right_coefficient = next;
        }
        Ok((old_remainder, old_left, old_right))
    }
}

/// One checked Frobenius reduction `previous^2 = quotient*f + remainder`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FrobeniusReduction {
    /// Quotient multiplying the candidate polynomial.
    pub quotient: Gf2Poly,
    /// Reduced residue, whose degree must be below the candidate degree.
    pub remainder: Gf2Poly,
}

/// Bezout evidence for one distinct prime divisor of the polynomial degree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RabinBezout {
    /// A distinct prime divisor of the candidate degree.
    pub prime_divisor: usize,
    /// Coefficient of the candidate polynomial.
    pub polynomial_coefficient: Gf2Poly,
    /// Coefficient of `r_(n/p) + x`.
    pub frobenius_coefficient: Gf2Poly,
}

/// Portable polynomial-identity evidence for Rabin irreducibility.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IrreducibilityCertificate {
    /// Candidate whose irreducibility is witnessed.
    pub polynomial: Gf2Poly,
    /// Complete chain from `x^2` through `x^(2^n)`, reduced modulo the candidate.
    pub frobenius: Vec<FrobeniusReduction>,
    /// One identity for each distinct prime divisor of the candidate degree.
    pub bezout: Vec<RabinBezout>,
}

/// Produce an irreducibility certificate, or `None` for a reducible polynomial.
///
/// Degree-one polynomials receive an empty certificate: every linear
/// polynomial over a field is irreducible.
///
/// # Errors
///
/// Returns [`Gf2Error::NotPositiveDegree`] for zero or constants, and typed
/// degree, Frobenius-step, or work-limit declines.
pub fn certify_irreducible(
    polynomial: &Gf2Poly,
    limits: Gf2Limits,
) -> Result<Option<IrreducibilityCertificate>, Gf2Error> {
    let degree = polynomial.degree().ok_or(Gf2Error::NotPositiveDegree)?;
    if degree == 0 {
        return Err(Gf2Error::NotPositiveDegree);
    }
    ensure_candidate_limits(degree, limits)?;
    if degree == 1 {
        return Ok(Some(IrreducibilityCertificate {
            polynomial: polynomial.clone(),
            frobenius: Vec::new(),
            bezout: Vec::new(),
        }));
    }

    let mut context = Gf2Context::new(limits);
    let mut current = Gf2Poly::x();
    let mut reductions = Vec::with_capacity(degree);
    let mut residues = Vec::with_capacity(degree);
    for _ in 0..degree {
        let square = context.square(&current)?;
        let (quotient, remainder) = context.div_rem(&square, polynomial)?;
        current = remainder.clone();
        residues.push(remainder.clone());
        reductions.push(FrobeniusReduction {
            quotient,
            remainder,
        });
    }
    if current != Gf2Poly::x() {
        return Ok(None);
    }

    let mut bezout = Vec::new();
    for prime_divisor in distinct_prime_factors(degree) {
        let residue = &residues[degree / prime_divisor - 1];
        let target = context.add(residue, &Gf2Poly::x())?;
        let (gcd, polynomial_coefficient, frobenius_coefficient) =
            context.extended_gcd(polynomial, &target)?;
        if gcd != Gf2Poly::one() {
            return Ok(None);
        }
        bezout.push(RabinBezout {
            prime_divisor,
            polynomial_coefficient,
            frobenius_coefficient,
        });
    }

    Ok(Some(IrreducibilityCertificate {
        polynomial: polynomial.clone(),
        frobenius: reductions,
        bezout,
    }))
}

/// Check Rabin identity evidence without calling [`certify_irreducible`].
///
/// # Errors
///
/// Returns [`Gf2Error::InvalidCertificate`] for a failed structural or
/// polynomial-identity obligation, or a typed resource-limit decline.
pub fn check_irreducible_certificate(
    certificate: &IrreducibilityCertificate,
    limits: Gf2Limits,
) -> Result<(), Gf2Error> {
    let polynomial = &certificate.polynomial;
    let degree = polynomial.degree().ok_or(Gf2Error::NotPositiveDegree)?;
    if degree == 0 {
        return Err(Gf2Error::NotPositiveDegree);
    }
    ensure_candidate_limits(degree, limits)?;
    if degree == 1 {
        if certificate.frobenius.is_empty() && certificate.bezout.is_empty() {
            return Ok(());
        }
        return Err(Gf2Error::InvalidCertificate(
            "linear certificate must have no obligations",
        ));
    }
    if certificate.frobenius.len() != degree {
        return Err(Gf2Error::InvalidCertificate(
            "Frobenius chain length differs from the degree",
        ));
    }

    let expected_primes = distinct_prime_factors(degree);
    let supplied_primes: Vec<usize> = certificate
        .bezout
        .iter()
        .map(|witness| witness.prime_divisor)
        .collect();
    if supplied_primes != expected_primes {
        return Err(Gf2Error::InvalidCertificate(
            "Bezout obligations do not match the complete prime-divisor set",
        ));
    }

    let mut context = Gf2Context::new(limits);
    let mut current = Gf2Poly::x();
    for reduction in &certificate.frobenius {
        if reduction
            .remainder
            .degree()
            .is_some_and(|value| value >= degree)
        {
            return Err(Gf2Error::InvalidCertificate(
                "Frobenius remainder is not reduced",
            ));
        }
        let square = context.square(&current)?;
        let product = context.multiply(&reduction.quotient, polynomial)?;
        let reconstructed = context.add(&product, &reduction.remainder)?;
        if reconstructed != square {
            return Err(Gf2Error::InvalidCertificate(
                "Frobenius reduction identity does not hold",
            ));
        }
        current = reduction.remainder.clone();
    }
    if current != Gf2Poly::x() {
        return Err(Gf2Error::InvalidCertificate(
            "final Frobenius residue is not x",
        ));
    }

    for witness in &certificate.bezout {
        let residue_index = degree / witness.prime_divisor - 1;
        let residue = &certificate.frobenius[residue_index].remainder;
        let target = context.add(residue, &Gf2Poly::x())?;
        let left = context.multiply(&witness.polynomial_coefficient, polynomial)?;
        let right = context.multiply(&witness.frobenius_coefficient, &target)?;
        if context.add(&left, &right)? != Gf2Poly::one() {
            return Err(Gf2Error::InvalidCertificate(
                "Rabin Bezout identity does not equal one",
            ));
        }
    }
    Ok(())
}

fn ensure_candidate_limits(degree: usize, limits: Gf2Limits) -> Result<(), Gf2Error> {
    if degree > limits.max_input_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: degree,
            limit: limits.max_input_degree,
        });
    }
    if degree > limits.max_frobenius_steps {
        return Err(Gf2Error::FrobeniusLimit {
            observed: degree,
            limit: limits.max_frobenius_steps,
        });
    }
    let required_intermediate = degree.checked_mul(2).ok_or(Gf2Error::DegreeLimit {
        observed: usize::MAX,
        limit: limits.max_intermediate_degree,
    })?;
    if required_intermediate > limits.max_intermediate_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: required_intermediate,
            limit: limits.max_intermediate_degree,
        });
    }
    Ok(())
}

fn distinct_prime_factors(mut value: usize) -> Vec<usize> {
    let mut factors = Vec::new();
    let mut divisor = 2;
    while divisor <= value / divisor {
        if value.is_multiple_of(divisor) {
            factors.push(divisor);
            while value.is_multiple_of(divisor) {
                value /= divisor;
            }
        }
        divisor += if divisor == 2 { 1 } else { 2 };
    }
    if value > 1 {
        factors.push(value);
    }
    factors
}

fn degree_words(words: &[u64]) -> Option<usize> {
    let last = *words.last()?;
    let high = usize::try_from(u64::BITS - 1 - last.leading_zeros()).ok()?;
    Some((words.len() - 1) * 64 + high)
}

fn xor_shifted(target: &mut [u64], source: &[u64], shift: usize) {
    let word_shift = shift / 64;
    let bit_shift = shift % 64;
    for (index, &word) in source.iter().enumerate() {
        target[word_shift + index] ^= word << bit_shift;
        if bit_shift != 0 && word_shift + index + 1 < target.len() {
            target[word_shift + index + 1] ^= word >> (64 - bit_shift);
        }
    }
}

fn trim(words: &mut Vec<u64>) {
    while words.last() == Some(&0) {
        words.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn poly(exponents: &[usize]) -> Gf2Poly {
        Gf2Poly::from_exponents(exponents, Gf2Limits::default()).unwrap()
    }

    fn degree_u128(value: u128) -> Option<usize> {
        if value == 0 {
            None
        } else {
            usize::try_from(u128::BITS - 1 - value.leading_zeros()).ok()
        }
    }

    fn brute_remainder(mut dividend: u128, divisor: u128) -> u128 {
        let divisor_degree = degree_u128(divisor).unwrap();
        while let Some(dividend_degree) = degree_u128(dividend) {
            if dividend_degree < divisor_degree {
                break;
            }
            dividend ^= divisor << (dividend_degree - divisor_degree);
        }
        dividend
    }

    fn brute_irreducible(candidate: u128, degree: usize) -> bool {
        if degree == 1 {
            return true;
        }
        for divisor_degree in 1..=degree / 2 {
            for tail in 0..(1_u128 << divisor_degree) {
                let divisor = (1_u128 << divisor_degree) | tail;
                if brute_remainder(candidate, divisor) == 0 {
                    return false;
                }
            }
        }
        true
    }

    #[test]
    fn bit_packing_and_ring_operations_cross_word_boundaries() {
        let limits = Gf2Limits::default();
        let mut context = Gf2Context::new(limits);
        let left = poly(&[0, 1, 63, 64, 130]);
        let right = poly(&[1, 64]);
        assert_eq!(context.add(&left, &right).unwrap(), poly(&[0, 63, 130]));
        let product = context.multiply(&poly(&[0, 1]), &poly(&[0, 64])).unwrap();
        assert_eq!(product, poly(&[0, 1, 64, 65]));
        let square = context.square(&poly(&[0, 1, 65])).unwrap();
        assert_eq!(square, poly(&[0, 2, 130]));
    }

    #[test]
    fn division_reconstructs_the_dividend() {
        let mut context = Gf2Context::new(Gf2Limits::default());
        let dividend = poly(&[0, 2, 5, 70]);
        let divisor = poly(&[0, 1, 3]);
        let (quotient, remainder) = context.div_rem(&dividend, &divisor).unwrap();
        assert!(remainder.degree().is_none_or(|value| value < 3));
        let product = context.multiply(&quotient, &divisor).unwrap();
        assert_eq!(context.add(&product, &remainder).unwrap(), dividend);
    }

    #[test]
    fn certificates_agree_with_two_small_degree_oracles_through_degree_ten() {
        let limits = Gf2Limits::default();
        for degree in 1..=10 {
            for tail in 0..(1_usize << degree) {
                let bits = tail | (1_usize << degree);
                let exponents: Vec<usize> = (0..=degree)
                    .filter(|exponent| bits & (1_usize << exponent) != 0)
                    .collect();
                let candidate = poly(&exponents);
                let generic: Vec<i128> = (0..=degree)
                    .map(|exponent| i128::from(bits & (1_usize << exponent) != 0))
                    .collect();
                let expected = crate::gfp::is_irreducible(&generic, 2).unwrap();
                assert_eq!(
                    expected,
                    brute_irreducible(u128::try_from(bits).unwrap(), degree),
                    "the generic checker and independent trial division disagree for {bits:#b}"
                );
                let certificate = certify_irreducible(&candidate, limits).unwrap();
                assert_eq!(certificate.is_some(), expected, "bits={bits:#b}");
                if let Some(certificate) = certificate {
                    check_irreducible_certificate(&certificate, limits).unwrap();
                }
            }
        }
    }

    #[test]
    fn degree_400_known_witness_is_checked() {
        let limits = Gf2Limits::default();
        let candidate = poly(&[0, 2, 3, 5, 400]);
        let certificate = certify_irreducible(&candidate, limits)
            .unwrap()
            .expect("known witness must be irreducible");
        check_irreducible_certificate(&certificate, limits).unwrap();
    }

    #[test]
    fn malformed_certificate_components_are_rejected() {
        let limits = Gf2Limits::default();
        let candidate = poly(&[0, 1, 4]);
        let certificate = certify_irreducible(&candidate, limits)
            .unwrap()
            .expect("x^4+x+1 is irreducible");

        let mut bad_remainder = certificate.clone();
        bad_remainder.frobenius[0].remainder = Gf2Poly::one();
        assert!(matches!(
            check_irreducible_certificate(&bad_remainder, limits),
            Err(Gf2Error::InvalidCertificate(_))
        ));

        let mut bad_quotient = certificate.clone();
        bad_quotient.frobenius[0].quotient = Gf2Poly::one();
        assert!(matches!(
            check_irreducible_certificate(&bad_quotient, limits),
            Err(Gf2Error::InvalidCertificate(_))
        ));

        let mut missing_prime = certificate.clone();
        missing_prime.bezout.clear();
        assert!(matches!(
            check_irreducible_certificate(&missing_prime, limits),
            Err(Gf2Error::InvalidCertificate(_))
        ));

        let mut bad_bezout = certificate;
        bad_bezout.bezout[0].polynomial_coefficient = Gf2Poly::zero();
        bad_bezout.bezout[0].frobenius_coefficient = Gf2Poly::zero();
        assert!(matches!(
            check_irreducible_certificate(&bad_bezout, limits),
            Err(Gf2Error::InvalidCertificate(_))
        ));
    }

    #[test]
    fn resource_limits_return_typed_declines() {
        let candidate = poly(&[0, 1, 20]);
        let tight_degree = Gf2Limits {
            max_input_degree: 10,
            ..Gf2Limits::default()
        };
        assert_eq!(
            certify_irreducible(&candidate, tight_degree),
            Err(Gf2Error::DegreeLimit {
                observed: 20,
                limit: 10
            })
        );

        let tight_work = Gf2Limits {
            max_word_ops: 1,
            ..Gf2Limits::default()
        };
        assert!(matches!(
            certify_irreducible(&candidate, tight_work),
            Err(Gf2Error::WorkLimit { .. })
        ));
    }
}
