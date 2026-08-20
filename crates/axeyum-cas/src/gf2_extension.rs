//! Bounded exact short-interval traces over binary extension fields.
//!
//! This module evaluates the fixed-polynomial-degree, varying-base-field
//! Frobenius traces used by the long-cycle diagnostic.  It is deliberately
//! separate from [`crate::gf2_hayes`]: a degree-`n` interval over
//! `GF(2^r)` is not the degree-`rn` identity population over `GF(2)`.

use core::fmt;

use crate::gf2::{
    Gf2Error, Gf2Limits, Gf2Poly, certify_irreducible, check_irreducible_certificate,
};

/// Deterministic limits for one extension-field interval trace.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BinaryExtensionTraceLimits {
    /// Largest admitted extension degree `r` in `GF(2^r)`.
    pub max_field_degree: usize,
    /// Largest admitted polynomial degree.
    pub max_polynomial_degree: usize,
    /// Largest admitted interval population `(2^r)^h`.
    pub max_candidates: u64,
}

impl Default for BinaryExtensionTraceLimits {
    fn default() -> Self {
        Self {
            max_field_degree: 8,
            max_polynomial_degree: 16,
            max_candidates: 1_000_000,
        }
    }
}

/// Exact fixed-degree long-cycle trace over one binary extension field.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryExtensionLongCycleTraceReport {
    /// Packed monic irreducible modulus defining `GF(2^r)`.
    pub field_modulus: u64,
    /// Extension degree `r`.
    pub field_degree: usize,
    /// Field order `2^r`.
    pub field_order: u64,
    /// Degree of every monic polynomial in the interval.
    pub polynomial_degree: usize,
    /// Number of prescribed zero next-to-leading coefficients.
    pub fixed_leading_coefficients: usize,
    /// Number of free low coefficients.
    pub free_coefficients: usize,
    /// Exact number `(2^r)^free_coefficients` of interval polynomials.
    pub candidate_count: u64,
    /// Exact sum of the polynomial von Mangoldt function on the interval.
    pub mangoldt_sum: u128,
    /// Signed long-cycle error `mangoldt_sum-candidate_count`.
    pub error: i128,
}

/// Typed failure from bounded binary-extension trace work.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BinaryExtensionTraceError {
    /// A parameter lies outside the mathematical domain.
    InvalidParameter(String),
    /// The packed field modulus is reducible.
    ReducibleFieldModulus,
    /// A configured deterministic limit was exceeded.
    ResourceLimit(String),
    /// An exact arithmetic invariant failed.
    Invariant(String),
    /// The underlying certified `GF(2)[x]` checker declined.
    Gf2(Gf2Error),
}

impl fmt::Display for BinaryExtensionTraceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidParameter(message) => write!(formatter, "invalid parameter: {message}"),
            Self::ReducibleFieldModulus => {
                write!(formatter, "field modulus is reducible over GF(2)")
            }
            Self::ResourceLimit(message) => write!(formatter, "resource limit: {message}"),
            Self::Invariant(message) => write!(formatter, "invariant failed: {message}"),
            Self::Gf2(error) => write!(formatter, "GF(2) certificate error: {error}"),
        }
    }
}

impl std::error::Error for BinaryExtensionTraceError {}

impl From<Gf2Error> for BinaryExtensionTraceError {
    fn from(error: Gf2Error) -> Self {
        Self::Gf2(error)
    }
}

#[derive(Clone, Copy, Debug)]
struct BinaryExtensionField {
    modulus: u64,
    degree: usize,
    order: u64,
    mask: u64,
}

impl BinaryExtensionField {
    fn new(
        modulus: u64,
        limits: BinaryExtensionTraceLimits,
    ) -> Result<Self, BinaryExtensionTraceError> {
        let degree = packed_degree(modulus).ok_or_else(|| {
            BinaryExtensionTraceError::InvalidParameter(
                "field modulus must have positive degree".to_owned(),
            )
        })?;
        if degree == 0 {
            return Err(BinaryExtensionTraceError::InvalidParameter(
                "field modulus must have positive degree".to_owned(),
            ));
        }
        if degree > limits.max_field_degree || degree >= 63 {
            return Err(BinaryExtensionTraceError::ResourceLimit(format!(
                "field degree {degree} exceeds limit {}",
                limits.max_field_degree
            )));
        }
        let polynomial = Gf2Poly::from_words(vec![modulus]);
        let gf2_limits = Gf2Limits {
            max_input_degree: limits.max_field_degree,
            max_intermediate_degree: limits.max_field_degree.saturating_mul(2),
            max_frobenius_steps: limits.max_field_degree,
            max_word_ops: 1_000_000,
        };
        let Some(certificate) = certify_irreducible(&polynomial, gf2_limits)? else {
            return Err(BinaryExtensionTraceError::ReducibleFieldModulus);
        };
        check_irreducible_certificate(&certificate, gf2_limits)?;
        let order = 1_u64 << degree;
        Ok(Self {
            modulus,
            degree,
            order,
            mask: order - 1,
        })
    }

    fn multiply(self, mut left: u64, mut right: u64) -> u64 {
        let reduction = self.modulus & self.mask;
        let high_bit = 1_u64 << (self.degree - 1);
        let mut result = 0_u64;
        while right != 0 {
            if right & 1 != 0 {
                result ^= left;
            }
            right >>= 1;
            let carry = left & high_bit != 0;
            left = (left << 1) & self.mask;
            if carry {
                left ^= reduction;
            }
        }
        result & self.mask
    }

    fn power(self, mut base: u64, mut exponent: u64) -> u64 {
        let mut result = 1_u64;
        while exponent != 0 {
            if exponent & 1 != 0 {
                result = self.multiply(result, base);
            }
            exponent >>= 1;
            if exponent != 0 {
                base = self.multiply(base, base);
            }
        }
        result
    }

    fn inverse(self, value: u64) -> Option<u64> {
        (value != 0).then(|| self.power(value, self.order - 2))
    }

    fn inverse_frobenius(self, mut value: u64, steps: usize) -> u64 {
        let inverse_steps = (self.degree - (steps % self.degree)) % self.degree;
        for _ in 0..inverse_steps {
            value = self.multiply(value, value);
        }
        value
    }
}

type ExtensionPoly = Vec<u64>;

/// Compute an exact fixed-degree short-interval Mangoldt trace over
/// `GF(2^r)`.
///
/// The interval consists of
///
/// ```text
/// T^n + a_(h-1) T^(h-1) + ... + a_0,
/// h = n-fixed_leading_coefficients.
/// ```
///
/// Its signed error is the Frobenius-power/long-cycle diagnostic `A_r(n)`.
/// Search contributes no theorem credit: the result is an exact bounded
/// enumeration with a certified irreducible binary field modulus.
///
/// # Errors
///
/// Rejects a reducible field modulus, an empty or malformed interval, a
/// configured degree/population excess, or a failed exact invariant.
pub fn binary_extension_long_cycle_trace(
    field_modulus: u64,
    polynomial_degree: usize,
    fixed_leading_coefficients: usize,
    limits: BinaryExtensionTraceLimits,
) -> Result<BinaryExtensionLongCycleTraceReport, BinaryExtensionTraceError> {
    let field = BinaryExtensionField::new(field_modulus, limits)?;
    if polynomial_degree == 0 || fixed_leading_coefficients >= polynomial_degree {
        return Err(BinaryExtensionTraceError::InvalidParameter(
            "require 0 <= fixed leading coefficients < polynomial degree".to_owned(),
        ));
    }
    if polynomial_degree > limits.max_polynomial_degree {
        return Err(BinaryExtensionTraceError::ResourceLimit(format!(
            "polynomial degree {polynomial_degree} exceeds limit {}",
            limits.max_polynomial_degree
        )));
    }
    let free_coefficients = polynomial_degree - fixed_leading_coefficients;
    let exponent = u32::try_from(free_coefficients).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit(
            "free-coefficient count does not fit exponent domain".to_owned(),
        )
    })?;
    let candidate_count = field.order.checked_pow(exponent).ok_or_else(|| {
        BinaryExtensionTraceError::ResourceLimit("candidate count overflow".to_owned())
    })?;
    if candidate_count > limits.max_candidates {
        return Err(BinaryExtensionTraceError::ResourceLimit(format!(
            "candidate count {candidate_count} exceeds limit {}",
            limits.max_candidates
        )));
    }

    let mut mangoldt_sum = 0_u128;
    for encoded in 0..candidate_count {
        let mut digits = encoded;
        let mut polynomial = vec![0_u64; polynomial_degree + 1];
        for coefficient in polynomial.iter_mut().take(free_coefficients) {
            *coefficient = digits % field.order;
            digits /= field.order;
        }
        polynomial[polynomial_degree] = 1;
        let lambda = polynomial_mangoldt(&polynomial, field)?;
        mangoldt_sum = mangoldt_sum.checked_add(lambda as u128).ok_or_else(|| {
            BinaryExtensionTraceError::ResourceLimit("Mangoldt sum overflow".to_owned())
        })?;
    }
    let signed_sum = i128::try_from(mangoldt_sum).map_err(|_| {
        BinaryExtensionTraceError::ResourceLimit("Mangoldt sum exceeds i128".to_owned())
    })?;
    let signed_candidates = i128::from(candidate_count);

    Ok(BinaryExtensionLongCycleTraceReport {
        field_modulus,
        field_degree: field.degree,
        field_order: field.order,
        polynomial_degree,
        fixed_leading_coefficients,
        free_coefficients,
        candidate_count,
        mangoldt_sum,
        error: signed_sum - signed_candidates,
    })
}

fn polynomial_mangoldt(
    polynomial: &[u64],
    field: BinaryExtensionField,
) -> Result<usize, BinaryExtensionTraceError> {
    let degree = poly_degree(polynomial).ok_or_else(|| {
        BinaryExtensionTraceError::Invariant("enumerated polynomial is zero".to_owned())
    })?;
    for exponent in (1..=degree).rev() {
        if !degree.is_multiple_of(exponent) {
            continue;
        }
        let Some(root) = polynomial_power_root(polynomial, exponent, field) else {
            continue;
        };
        if polynomial_is_irreducible(&root, field)? {
            return Ok(degree / exponent);
        }
    }
    Ok(0)
}

fn polynomial_power_root(
    polynomial: &[u64],
    exponent: usize,
    field: BinaryExtensionField,
) -> Option<ExtensionPoly> {
    let two_power_exponent = exponent.trailing_zeros() as usize;
    let two_power = 1_usize.checked_shl(u32::try_from(two_power_exponent).ok()?)?;
    let odd_exponent = exponent / two_power;
    let degree = poly_degree(polynomial)?;
    if !degree.is_multiple_of(exponent) {
        return None;
    }

    let mut stripped = vec![0_u64; degree / two_power + 1];
    for (index, &coefficient) in polynomial.iter().enumerate() {
        if coefficient == 0 {
            continue;
        }
        if !index.is_multiple_of(two_power) {
            return None;
        }
        stripped[index / two_power] = field.inverse_frobenius(coefficient, two_power_exponent);
    }
    trim_poly(&mut stripped);

    let root_degree = degree / exponent;
    let mut root = vec![0_u64; root_degree + 1];
    root[root_degree] = 1;
    for offset in 1..=root_degree {
        let current = poly_power(&root, odd_exponent, field);
        let target_degree = odd_exponent * root_degree - offset;
        let current_value = current.get(target_degree).copied().unwrap_or(0);
        let target_value = stripped.get(target_degree).copied().unwrap_or(0);
        root[root_degree - offset] = current_value ^ target_value;
    }
    (poly_power(&root, odd_exponent, field) == stripped).then_some(root)
}

fn polynomial_is_irreducible(
    polynomial: &[u64],
    field: BinaryExtensionField,
) -> Result<bool, BinaryExtensionTraceError> {
    let Some(degree) = poly_degree(polynomial) else {
        return Ok(false);
    };
    if degree == 0 {
        return Ok(false);
    }
    if degree == 1 {
        return Ok(true);
    }
    if polynomial[degree] != 1 {
        return Err(BinaryExtensionTraceError::Invariant(
            "irreducibility input is not monic".to_owned(),
        ));
    }

    let x = vec![0, 1];
    let prime_divisors = distinct_prime_factors(degree);
    let mut current = x.clone();
    for step in 1..=degree {
        for _ in 0..field.degree {
            current = poly_square_mod(&current, polynomial, field)?;
        }
        for &prime in &prime_divisors {
            if step == degree / prime {
                let difference = poly_add(&current, &x);
                if poly_degree(&poly_gcd(polynomial, &difference, field)?) != Some(0) {
                    return Ok(false);
                }
            }
        }
    }
    Ok(current == x)
}

fn poly_add(left: &[u64], right: &[u64]) -> ExtensionPoly {
    let mut result = vec![0_u64; left.len().max(right.len())];
    for (index, value) in result.iter_mut().enumerate() {
        *value = left.get(index).copied().unwrap_or(0) ^ right.get(index).copied().unwrap_or(0);
    }
    trim_poly(&mut result);
    result
}

fn poly_multiply(left: &[u64], right: &[u64], field: BinaryExtensionField) -> ExtensionPoly {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let mut result = vec![0_u64; left.len() + right.len() - 1];
    for (left_index, &left_value) in left.iter().enumerate() {
        for (right_index, &right_value) in right.iter().enumerate() {
            result[left_index + right_index] ^= field.multiply(left_value, right_value);
        }
    }
    trim_poly(&mut result);
    result
}

fn poly_power(
    polynomial: &[u64],
    mut exponent: usize,
    field: BinaryExtensionField,
) -> ExtensionPoly {
    let mut base = polynomial.to_vec();
    let mut result = vec![1_u64];
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = poly_multiply(&result, &base, field);
        }
        exponent >>= 1;
        if exponent != 0 {
            base = poly_multiply(&base, &base, field);
        }
    }
    result
}

fn poly_div_rem(
    dividend: &[u64],
    divisor: &[u64],
    field: BinaryExtensionField,
) -> Result<(ExtensionPoly, ExtensionPoly), BinaryExtensionTraceError> {
    let divisor_degree = poly_degree(divisor).ok_or_else(|| {
        BinaryExtensionTraceError::Invariant("polynomial division by zero".to_owned())
    })?;
    let inverse_lead = field.inverse(divisor[divisor_degree]).ok_or_else(|| {
        BinaryExtensionTraceError::Invariant("polynomial divisor has zero lead".to_owned())
    })?;
    let mut remainder = dividend.to_vec();
    trim_poly(&mut remainder);
    let mut quotient = vec![0_u64; remainder.len().saturating_sub(divisor_degree)];
    while let Some(remainder_degree) = poly_degree(&remainder) {
        if remainder_degree < divisor_degree {
            break;
        }
        let shift = remainder_degree - divisor_degree;
        let factor = field.multiply(remainder[remainder_degree], inverse_lead);
        quotient[shift] ^= factor;
        for (index, &coefficient) in divisor.iter().enumerate() {
            remainder[index + shift] ^= field.multiply(factor, coefficient);
        }
        trim_poly(&mut remainder);
    }
    trim_poly(&mut quotient);
    Ok((quotient, remainder))
}

fn poly_mod(
    polynomial: &[u64],
    modulus: &[u64],
    field: BinaryExtensionField,
) -> Result<ExtensionPoly, BinaryExtensionTraceError> {
    Ok(poly_div_rem(polynomial, modulus, field)?.1)
}

fn poly_square_mod(
    polynomial: &[u64],
    modulus: &[u64],
    field: BinaryExtensionField,
) -> Result<ExtensionPoly, BinaryExtensionTraceError> {
    let mut square = vec![0_u64; polynomial.len().saturating_mul(2).saturating_sub(1)];
    for (index, &coefficient) in polynomial.iter().enumerate() {
        square[2 * index] = field.multiply(coefficient, coefficient);
    }
    poly_mod(&square, modulus, field)
}

fn poly_gcd(
    left: &[u64],
    right: &[u64],
    field: BinaryExtensionField,
) -> Result<ExtensionPoly, BinaryExtensionTraceError> {
    let mut first = left.to_vec();
    let mut second = right.to_vec();
    trim_poly(&mut first);
    trim_poly(&mut second);
    while !second.is_empty() {
        let remainder = poly_div_rem(&first, &second, field)?.1;
        first = second;
        second = remainder;
    }
    let Some(degree) = poly_degree(&first) else {
        return Ok(first);
    };
    let inverse_lead = field.inverse(first[degree]).ok_or_else(|| {
        BinaryExtensionTraceError::Invariant("gcd has zero leading coefficient".to_owned())
    })?;
    for coefficient in &mut first {
        *coefficient = field.multiply(*coefficient, inverse_lead);
    }
    Ok(first)
}

fn packed_degree(polynomial: u64) -> Option<usize> {
    (polynomial != 0).then(|| (u64::BITS - 1 - polynomial.leading_zeros()) as usize)
}

fn poly_degree(polynomial: &[u64]) -> Option<usize> {
    polynomial.iter().rposition(|&coefficient| coefficient != 0)
}

fn trim_poly(polynomial: &mut ExtensionPoly) {
    while polynomial.last() == Some(&0) {
        polynomial.pop();
    }
}

fn distinct_prime_factors(mut value: usize) -> Vec<usize> {
    let mut factors = Vec::new();
    let mut divisor = 2_usize;
    while divisor <= value / divisor {
        if value.is_multiple_of(divisor) {
            factors.push(divisor);
            while value.is_multiple_of(divisor) {
                value /= divisor;
            }
        }
        divisor += 1;
    }
    if value > 1 {
        factors.push(value);
    }
    factors
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extension_field_long_cycle_traces_match_small_exact_formulas() {
        let limits = BinaryExtensionTraceLimits::default();
        let rows = [
            (0b11_u64, 1_usize, -2_i128),
            (0b111, 2, 12),
            (0b1011, 3, -56),
        ];
        for (modulus, extension_degree, expected_error) in rows {
            let report = binary_extension_long_cycle_trace(modulus, 5, 2, limits).unwrap();
            let power = u32::try_from(extension_degree).unwrap();
            assert_eq!(report.field_degree, extension_degree);
            assert_eq!(report.error, expected_error);
            assert_eq!(report.error, (-4_i128).pow(power) - (-2_i128).pow(power));
        }

        let degree_nine = binary_extension_long_cycle_trace(0b11, 9, 4, limits).unwrap();
        assert_eq!(degree_nine.candidate_count, 32);
        assert_eq!(degree_nine.mangoldt_sum, 37);
        assert_eq!(degree_nine.error, 5);

        for (modulus, expected_error) in [(0b111_u64, 129_i128), (0b1011, -1_771)] {
            let report = binary_extension_long_cycle_trace(modulus, 9, 4, limits).unwrap();
            assert_eq!(report.error, expected_error);
        }
    }

    #[test]
    fn extension_field_trace_rejects_bad_moduli_and_candidate_excess() {
        let limits = BinaryExtensionTraceLimits::default();
        assert_eq!(
            binary_extension_long_cycle_trace(0b101, 5, 2, limits),
            Err(BinaryExtensionTraceError::ReducibleFieldModulus)
        );
        let tight = BinaryExtensionTraceLimits {
            max_candidates: 31,
            ..limits
        };
        assert!(matches!(
            binary_extension_long_cycle_trace(0b11, 9, 4, tight),
            Err(BinaryExtensionTraceError::ResourceLimit(_))
        ));
    }

    #[test]
    fn extension_field_mangoldt_recognizes_separable_and_inseparable_powers() {
        let field =
            BinaryExtensionField::new(0b111, BinaryExtensionTraceLimits::default()).unwrap();
        let irreducible_quadratic = vec![2, 1, 1];
        assert!(polynomial_is_irreducible(&irreducible_quadratic, field).unwrap());
        for exponent in [2_usize, 3, 6] {
            let power = poly_power(&irreducible_quadratic, exponent, field);
            assert_eq!(polynomial_mangoldt(&power, field).unwrap(), 2);
        }

        let first_linear = vec![1, 1];
        let second_linear = vec![2, 1];
        let mixed = poly_multiply(&first_linear, &second_linear, field);
        assert_eq!(polynomial_mangoldt(&mixed, field).unwrap(), 0);
    }

    #[test]
    #[ignore = "33,554,432-candidate long-cycle research probe"]
    fn extension_field_degree_nine_four_coefficient_probe() {
        let limits = BinaryExtensionTraceLimits {
            max_field_degree: 5,
            max_polynomial_degree: 9,
            max_candidates: 33_554_432,
        };
        let report = binary_extension_long_cycle_trace(0b10_0101, 9, 4, limits).unwrap();
        assert_eq!(report.field_order, 32);
        assert_eq!(report.candidate_count, 33_554_432);
        assert_eq!(report.mangoldt_sum, 33_525_757);
        assert_eq!(report.error, -28_675);
    }
}
