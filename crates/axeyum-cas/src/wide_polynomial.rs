//! Opt-in exact polynomial normalization with bounded promoted coefficients.
//! A normal form is a computation result, not an equality certificate.
use crate::rewrite_trace::{TraceError, TraceLimits};
use crate::{CasExpr, Monomial, MultiPoly, Rational};
use std::collections::BTreeMap;

/// Hard coefficient cap for version-2 trace arithmetic.
pub const COEFFICIENT_BITS: u64 = 16_384;
fn resource(reason: &str) -> TraceError {
    TraceError::ResourceLimit(reason.into())
}
struct Normalizer {
    limits: TraceLimits,
    remaining: u64,
    nodes: usize,
}
impl Normalizer {
    fn charge(&mut self, count: u64) -> Result<(), TraceError> {
        self.remaining = self
            .remaining
            .checked_sub(count)
            .ok_or_else(|| resource("wide arithmetic work"))?;
        Ok(())
    }
    fn coefficient(&mut self, value: Rational) -> Result<Rational, TraceError> {
        let bits = value
            .numerator_big()
            .bits()
            .max(value.denominator_big().bits());
        if bits > COEFFICIENT_BITS {
            return Err(resource("wide coefficient bit cap"));
        }
        self.charge(bits.div_ceil(64).max(1))?;
        Ok(value)
    }
    fn polynomial(&self, poly: &MultiPoly) -> Result<(), TraceError> {
        if poly.terms.len() as u64 > self.limits.terms
            || poly
                .terms
                .keys()
                .any(|m| m.total_degree() > u64::from(self.limits.degree))
        {
            return Err(resource("wide polynomial expansion cap"));
        }
        Ok(())
    }
    fn add(&mut self, left: MultiPoly, right: &MultiPoly) -> Result<MultiPoly, TraceError> {
        let mut terms = left.terms;
        for (monomial, value) in &right.terms {
            let old = terms.get(monomial).copied().unwrap_or(Rational::integer(0));
            self.coefficient(old)?;
            self.coefficient(*value)?;
            let sum = self.coefficient(
                old.wide_add(*value)
                    .ok_or_else(|| resource("wide addition"))?,
            )?;
            if sum.is_zero() {
                terms.remove(monomial);
            } else {
                terms.insert(monomial.clone(), sum);
            }
            self.polynomial(&MultiPoly {
                terms: terms.clone(),
            })?;
        }
        Ok(MultiPoly { terms })
    }
    fn mul(&mut self, left: &MultiPoly, right: &MultiPoly) -> Result<MultiPoly, TraceError> {
        let mut terms = BTreeMap::new();
        for (a, av) in &left.terms {
            for (b, bv) in &right.terms {
                self.coefficient(*av)?;
                self.coefficient(*bv)?;
                let monomial = a.mul(b).ok_or_else(|| resource("wide monomial degree"))?;
                if monomial.total_degree() > u64::from(self.limits.degree) {
                    return Err(resource("wide polynomial degree"));
                }
                let product = self.coefficient(
                    av.wide_mul(*bv)
                        .ok_or_else(|| resource("wide multiplication"))?,
                )?;
                let old = terms
                    .get(&monomial)
                    .copied()
                    .unwrap_or(Rational::integer(0));
                let value = self.coefficient(
                    old.wide_add(product)
                        .ok_or_else(|| resource("wide accumulation"))?,
                )?;
                if value.is_zero() {
                    terms.remove(&monomial);
                } else {
                    terms.insert(monomial, value);
                }
                if terms.len() as u64 > self.limits.terms {
                    return Err(resource("wide polynomial term cap"));
                }
            }
        }
        Ok(MultiPoly { terms })
    }
    fn expression(&mut self, expression: &CasExpr, depth: usize) -> Result<MultiPoly, TraceError> {
        self.nodes += 1;
        if self.nodes > self.limits.nodes || depth > self.limits.depth {
            return Err(resource("wide syntax cap"));
        }
        self.charge(1)?;
        let result = match expression {
            CasExpr::Const(value) => MultiPoly::constant(self.coefficient(*value)?),
            CasExpr::Var(name) => {
                if name.is_empty() || name.len() > 128 {
                    return Err(TraceError::Rejected {
                        step: None,
                        reason: "invalid parameter name".into(),
                    });
                }
                MultiPoly::single_var(name)
            }
            CasExpr::Add(children) => {
                let mut result = MultiPoly::zero();
                for child in children {
                    let next = self.expression(child, depth + 1)?;
                    result = self.add(result, &next)?;
                }
                result
            }
            CasExpr::Mul(children) => {
                let mut result = MultiPoly::constant(Rational::integer(1));
                for child in children {
                    let next = self.expression(child, depth + 1)?;
                    result = self.mul(&result, &next)?;
                }
                result
            }
            CasExpr::Neg(child) => {
                let mut result = self.expression(child, depth + 1)?;
                for value in result.terms.values_mut() {
                    *value = self
                        .coefficient(value.wide_neg().ok_or_else(|| resource("wide negation"))?)?;
                }
                result
            }
            CasExpr::Pow(child, exponent) => {
                if *exponent > 512 {
                    return Err(resource("wide constant exponent cap"));
                }
                let mut base = self.expression(child, depth + 1)?;
                if base.terms.keys().any(|m| {
                    m.total_degree()
                        .checked_mul(u64::from(*exponent))
                        .is_none_or(|d| d > u64::from(self.limits.degree))
                }) {
                    return Err(resource("wide power degree"));
                }
                let mut result = MultiPoly::constant(Rational::integer(1));
                let mut remaining = *exponent;
                while remaining != 0 {
                    if remaining & 1 != 0 {
                        result = self.mul(&result, &base)?;
                    }
                    remaining >>= 1;
                    if remaining != 0 {
                        base = self.mul(&base, &base)?;
                    }
                }
                result
            }
            CasExpr::Div(numerator, denominator) => {
                let numerator = self.expression(numerator, depth + 1)?;
                let denominator = self.expression(denominator, depth + 1)?;
                if denominator.is_zero() {
                    return Err(TraceError::Rejected {
                        step: None,
                        reason: "zero denominator".into(),
                    });
                }
                let Some(divisor) = denominator
                    .terms
                    .get(&Monomial::one())
                    .copied()
                    .filter(|_| denominator.terms.len() == 1)
                else {
                    return Err(TraceError::Unsupported(
                        "symbolic denominator needs an external nonzero context".into(),
                    ));
                };
                let mut result = numerator;
                for value in result.terms.values_mut() {
                    *value = self.coefficient(
                        value
                            .wide_div(divisor)
                            .ok_or_else(|| resource("wide division"))?,
                    )?;
                }
                result
            }
            CasExpr::Unary(..) => return Err(TraceError::Unsupported("nonpolynomial head".into())),
        };
        self.polynomial(&result)?;
        Ok(result)
    }
}
/// Compute an exact wide normal form, admitting only provably constant denominators.
/// This opt-in computation carries no trace or kernel-admission receipt.
///
/// # Errors
/// Declines nonpolynomial heads, symbolic/zero denominators and exhausted local
/// syntax, coefficient, expansion or width-weighted arithmetic limits.
pub fn normalize_with_limits(
    expression: &CasExpr,
    limits: TraceLimits,
) -> Result<CasExpr, TraceError> {
    let mut remaining = limits.work;
    normalize_with_budget(expression, limits, &mut remaining)
}
pub(crate) fn normalize_with_budget(
    expression: &CasExpr,
    limits: TraceLimits,
    remaining: &mut u64,
) -> Result<CasExpr, TraceError> {
    let limits = limits.policy()?;
    let mut normalizer = Normalizer {
        limits,
        remaining: (*remaining).min(limits.work),
        nodes: 0,
    };
    let result = normalizer.expression(expression, 0).map(|p| p.to_expr());
    *remaining = normalizer.remaining;
    result
}
#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_rational::BigRational;
    #[test]
    fn promoted_polynomial_arithmetic_is_exact() {
        let huge =
            Rational::from_big_rational(&BigRational::new(BigInt::from(1) << 200, BigInt::from(3)))
                .unwrap();
        let x = CasExpr::var("x");
        let expr = CasExpr::Mul(vec![
            CasExpr::Const(huge),
            CasExpr::Add(vec![x.clone(), x.clone()]),
        ]);
        let result = normalize_with_limits(&expr, TraceLimits::default()).unwrap();
        assert_eq!(
            result,
            CasExpr::Mul(vec![CasExpr::Const(huge.wide_add(huge).unwrap()), x])
        );
        assert!(crate::normalize(&expr).is_none());
    }
    #[test]
    fn closed_power_and_quotient_preserve_exact_fractions() {
        let base = CasExpr::rat(241, 240);
        let power = CasExpr::Pow(Box::new(base), 360);
        let result = normalize_with_limits(&power, TraceLimits::default()).unwrap();
        let expected = Rational::from_big_rational(&BigRational::new(
            BigInt::from(241).pow(360),
            BigInt::from(240).pow(360),
        ))
        .unwrap();
        assert_eq!(result, CasExpr::Const(expected));
        let reciprocal = CasExpr::Div(Box::new(CasExpr::int(1)), Box::new(power));
        assert_eq!(
            normalize_with_limits(&reciprocal, TraceLimits::default()).unwrap(),
            CasExpr::Const(expected.wide_recip().unwrap())
        );
    }
    #[test]
    fn domain_and_resource_corners_are_explicit() {
        let limits = TraceLimits::default();
        assert!(matches!(
            normalize_with_limits(
                &CasExpr::Div(Box::new(CasExpr::int(1)), Box::new(CasExpr::zero())),
                limits
            ),
            Err(TraceError::Rejected { .. })
        ));
        assert!(matches!(
            normalize_with_limits(
                &CasExpr::Div(Box::new(CasExpr::int(1)), Box::new(CasExpr::var("x"))),
                limits
            ),
            Err(TraceError::Unsupported(_))
        ));
        let too_wide = Rational::from_big_rational(&BigRational::new(
            BigInt::from(1) << COEFFICIENT_BITS,
            BigInt::from(1),
        ))
        .unwrap();
        assert!(matches!(
            normalize_with_limits(&CasExpr::Const(too_wide), limits),
            Err(TraceError::ResourceLimit(_))
        ));
        assert!(matches!(
            normalize_with_limits(&CasExpr::int(1), TraceLimits { work: 0, ..limits }),
            Err(TraceError::ResourceLimit(_))
        ));
    }
}
