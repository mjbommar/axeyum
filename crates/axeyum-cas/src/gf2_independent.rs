//! A deliberately separate checker for `GF(2)` irreducibility certificates.
//!
//! The producer and primary checker in [`crate::gf2`] use packed `u64`
//! arithmetic.  This module expands coefficients to bytes and implements
//! schoolbook identities directly.  It shares the public certificate syntax,
//! but not the packed arithmetic, division, GCD, or producer verdict.

use crate::gf2::{Gf2Error, Gf2Poly, IrreducibilityCertificate};

/// Resource ceilings for the dense independent checker.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IndependentCheckLimits {
    /// Maximum candidate degree.
    pub max_degree: usize,
    /// Maximum number of coefficient reads/XORs.
    pub max_coefficient_ops: u64,
}

impl Default for IndependentCheckLimits {
    fn default() -> Self {
        Self {
            max_degree: 4_096,
            max_coefficient_ops: 500_000_000,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct DensePoly(Vec<u8>);

impl DensePoly {
    fn from_packed(polynomial: &Gf2Poly, budget: &mut Budget) -> Result<Self, Gf2Error> {
        let Some(degree) = polynomial.degree() else {
            return Ok(Self(Vec::new()));
        };
        budget.charge(degree.saturating_add(1))?;
        let mut coefficients = vec![0; degree + 1];
        for (exponent, coefficient) in coefficients.iter_mut().enumerate() {
            *coefficient = u8::from(polynomial.coefficient(exponent));
        }
        Ok(Self(coefficients))
    }

    fn one() -> Self {
        Self(vec![1])
    }

    fn x() -> Self {
        Self(vec![0, 1])
    }

    fn degree(&self) -> Option<usize> {
        self.0.len().checked_sub(1)
    }

    fn add(&self, right: &Self, budget: &mut Budget) -> Result<Self, Gf2Error> {
        let length = self.0.len().max(right.0.len());
        budget.charge(length)?;
        let mut result = vec![0; length];
        for (index, coefficient) in result.iter_mut().enumerate() {
            *coefficient =
                self.0.get(index).copied().unwrap_or(0) ^ right.0.get(index).copied().unwrap_or(0);
        }
        trim(&mut result);
        Ok(Self(result))
    }

    fn square(&self, budget: &mut Budget) -> Result<Self, Gf2Error> {
        let Some(degree) = self.degree() else {
            return Ok(Self(Vec::new()));
        };
        budget.charge(self.0.len())?;
        let mut result = vec![0; degree * 2 + 1];
        for (exponent, &coefficient) in self.0.iter().enumerate() {
            result[exponent * 2] = coefficient;
        }
        trim(&mut result);
        Ok(Self(result))
    }

    fn multiply(&self, right: &Self, budget: &mut Budget) -> Result<Self, Gf2Error> {
        let (Some(left_degree), Some(right_degree)) = (self.degree(), right.degree()) else {
            return Ok(Self(Vec::new()));
        };
        let mut result = vec![0; left_degree + right_degree + 1];
        for (left_exponent, &left_coefficient) in self.0.iter().enumerate() {
            if left_coefficient == 0 {
                continue;
            }
            budget.charge(right.0.len())?;
            for (right_exponent, &right_coefficient) in right.0.iter().enumerate() {
                result[left_exponent + right_exponent] ^= right_coefficient;
            }
        }
        trim(&mut result);
        Ok(Self(result))
    }
}

#[derive(Clone, Copy, Debug)]
struct Budget {
    used: u64,
    limit: u64,
}

impl Budget {
    const fn new(limit: u64) -> Self {
        Self { used: 0, limit }
    }

    fn charge(&mut self, amount: usize) -> Result<(), Gf2Error> {
        let amount = u64::try_from(amount).unwrap_or(u64::MAX);
        let used = self.used.saturating_add(amount);
        if used > self.limit {
            return Err(Gf2Error::WorkLimit {
                used,
                limit: self.limit,
            });
        }
        self.used = used;
        Ok(())
    }
}

/// Check a Rabin certificate with dense coefficient arithmetic.
///
/// # Errors
///
/// Returns [`Gf2Error::InvalidCertificate`] when a structural or identity
/// obligation fails, or a typed degree/work-limit decline.
pub fn check_irreducible_certificate_independent(
    certificate: &IrreducibilityCertificate,
    limits: IndependentCheckLimits,
) -> Result<(), Gf2Error> {
    let degree = certificate
        .polynomial
        .degree()
        .ok_or(Gf2Error::NotPositiveDegree)?;
    if degree == 0 {
        return Err(Gf2Error::NotPositiveDegree);
    }
    if degree > limits.max_degree {
        return Err(Gf2Error::DegreeLimit {
            observed: degree,
            limit: limits.max_degree,
        });
    }
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

    let mut budget = Budget::new(limits.max_coefficient_ops);
    let polynomial = DensePoly::from_packed(&certificate.polynomial, &mut budget)?;
    let mut current = DensePoly::x();
    let mut dense_remainders = Vec::with_capacity(degree);
    for reduction in &certificate.frobenius {
        let quotient = DensePoly::from_packed(&reduction.quotient, &mut budget)?;
        let remainder = DensePoly::from_packed(&reduction.remainder, &mut budget)?;
        if remainder.degree().is_some_and(|value| value >= degree) {
            return Err(Gf2Error::InvalidCertificate(
                "Frobenius remainder is not reduced",
            ));
        }
        let square = current.square(&mut budget)?;
        let product = quotient.multiply(&polynomial, &mut budget)?;
        if product.add(&remainder, &mut budget)? != square {
            return Err(Gf2Error::InvalidCertificate(
                "Frobenius reduction identity does not hold",
            ));
        }
        current = remainder.clone();
        dense_remainders.push(remainder);
    }
    if current != DensePoly::x() {
        return Err(Gf2Error::InvalidCertificate(
            "final Frobenius residue is not x",
        ));
    }

    for witness in &certificate.bezout {
        let residue = &dense_remainders[degree / witness.prime_divisor - 1];
        let target = residue.add(&DensePoly::x(), &mut budget)?;
        let polynomial_coefficient =
            DensePoly::from_packed(&witness.polynomial_coefficient, &mut budget)?;
        let frobenius_coefficient =
            DensePoly::from_packed(&witness.frobenius_coefficient, &mut budget)?;
        let left = polynomial_coefficient.multiply(&polynomial, &mut budget)?;
        let right = frobenius_coefficient.multiply(&target, &mut budget)?;
        if left.add(&right, &mut budget)? != DensePoly::one() {
            return Err(Gf2Error::InvalidCertificate(
                "Rabin Bezout identity does not equal one",
            ));
        }
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

fn trim(coefficients: &mut Vec<u8>) {
    while coefficients.last() == Some(&0) {
        coefficients.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf2::{Gf2Limits, certify_irreducible};

    fn certificate(exponents: &[usize]) -> IrreducibilityCertificate {
        let limits = Gf2Limits::default();
        let polynomial = Gf2Poly::from_exponents(exponents, limits).unwrap();
        certify_irreducible(&polynomial, limits)
            .unwrap()
            .expect("test polynomial must be irreducible")
    }

    #[test]
    fn independent_checker_accepts_degree_400_witness() {
        check_irreducible_certificate_independent(
            &certificate(&[0, 2, 3, 5, 400]),
            IndependentCheckLimits::default(),
        )
        .unwrap();
    }

    #[test]
    fn independent_checker_rejects_packed_checker_mutations() {
        let mut candidate = certificate(&[0, 1, 4]);
        candidate.frobenius[0].quotient = Gf2Poly::one();
        assert!(matches!(
            check_irreducible_certificate_independent(
                &candidate,
                IndependentCheckLimits::default()
            ),
            Err(Gf2Error::InvalidCertificate(_))
        ));
    }

    #[test]
    fn independent_checker_has_its_own_work_ceiling() {
        let candidate = certificate(&[0, 1, 4]);
        let limits = IndependentCheckLimits {
            max_coefficient_ops: 1,
            ..IndependentCheckLimits::default()
        };
        assert!(matches!(
            check_irreducible_certificate_independent(&candidate, limits),
            Err(Gf2Error::WorkLimit { .. })
        ));
    }
}
