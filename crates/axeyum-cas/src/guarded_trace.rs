//! Conditional quotient certificates bound to an external nonzero context.
//! These prove rational equality under assumptions, never kernel admission.
use serde::{Deserialize, Serialize};

use crate::rewrite_trace::{
    PolynomialExpr, RewriteTrace, TraceError, TraceLimits, check_trace, normalize_with_trace,
};
use crate::{CasExpr, Rational, normalize};

/// A quotient subject; division is defined only when its denominator is nonzero.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct QuotientSubject {
    /// Original numerator, without simplification.
    pub numerator: PolynomialExpr,
    /// Original denominator, without simplification.
    pub denominator: PolynomialExpr,
}
/// One conditional cancellation step, with independently replayable premises.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GuardedQuotientTrace {
    /// Versioned conditional contract, distinct from unconditional trace v1.
    pub version: String,
    /// Original rational-function subject.
    pub input: QuotientSubject,
    /// Claimed polynomial quotient.
    pub result: PolynomialExpr,
    /// Ordered context: every entry is assumed nonzero, not proved nonzero.
    pub nonzero_assumptions: Vec<PolynomialExpr>,
    /// Index of the exact denominator-nonzero premise in the external context.
    pub denominator_premise: usize,
    /// Local normalization of the original numerator.
    pub numerator_identity: RewriteTrace,
    /// Local normalization of denominator times the claimed result.
    pub product_identity: RewriteTrace,
}
fn reject(reason: &str) -> TraceError {
    TraceError::Rejected {
        step: Some(0),
        reason: reason.into(),
    }
}
fn product(subject: &QuotientSubject, result: &PolynomialExpr) -> PolynomialExpr {
    PolynomialExpr::Mul(vec![subject.denominator.clone(), result.clone()])
}
/// Check a conditional equality against the caller's subject, result and context.
///
/// # Errors
/// Rejects changed subjects/contexts, missing nonzero premises, zero denominators,
/// invalid polynomial witnesses, unsupported versions or resource exhaustion.
pub fn check_guarded_trace(
    trace: &GuardedQuotientTrace,
    subject: &QuotientSubject,
    result: &PolynomialExpr,
    nonzero_assumptions: &[PolynomialExpr],
    limits: TraceLimits,
) -> Result<(), TraceError> {
    if trace.version != "cas-guarded-quotient-v1" {
        return Err(TraceError::Unsupported("guarded quotient version".into()));
    }
    if trace.input != *subject
        || trace.result != *result
        || trace.nonzero_assumptions != nonzero_assumptions
    {
        return Err(reject(
            "conditional statement or assumption context mismatch",
        ));
    }
    if nonzero_assumptions.len() > limits.nodes {
        return Err(TraceError::ResourceLimit("assumption count".into()));
    }
    for assumption in nonzero_assumptions {
        assumption.to_cas(limits)?;
    }
    if nonzero_assumptions.get(trace.denominator_premise) != Some(&subject.denominator) {
        return Err(reject("missing exact denominator-nonzero premise"));
    }
    let denominator = subject.denominator.to_cas(limits)?;
    if normalize(&denominator)
        .ok_or_else(|| TraceError::ResourceLimit("denominator arithmetic".into()))?
        .is_zero()
    {
        return Err(reject("zero denominator"));
    }
    let multiplied = product(subject, result);
    check_trace(
        &trace.numerator_identity,
        &subject.numerator,
        &trace.numerator_identity.result,
        limits,
    )?;
    check_trace(
        &trace.product_identity,
        &multiplied,
        &trace.product_identity.result,
        limits,
    )?;
    if trace.numerator_identity.result != trace.product_identity.result {
        return Err(reject("cross-multiplication identity mismatch"));
    }
    Ok(())
}
/// Cancel a syntactically present denominator factor and produce conditional evidence.
///
/// # Errors
/// Declines absent factors/assumptions, zero denominators or bounded arithmetic.
pub fn cancel_factor_with_trace(
    subject: &QuotientSubject,
    nonzero_assumptions: &[PolynomialExpr],
    limits: TraceLimits,
) -> Result<GuardedQuotientTrace, TraceError> {
    // Validate before cloning or running normalization.
    subject.numerator.to_cas(limits)?;
    subject.denominator.to_cas(limits)?;
    if nonzero_assumptions.len() > limits.nodes {
        return Err(TraceError::ResourceLimit("assumption count".into()));
    }
    let premise = nonzero_assumptions
        .iter()
        .position(|p| p == &subject.denominator)
        .ok_or_else(|| reject("missing denominator-nonzero assumption"))?;
    let raw_result = if subject.numerator == subject.denominator {
        CasExpr::Const(Rational::integer(1))
    } else {
        match &subject.numerator {
            PolynomialExpr::Mul(factors) => {
                let position = factors
                    .iter()
                    .position(|p| p == &subject.denominator)
                    .ok_or_else(|| {
                        TraceError::Unsupported("no syntactic denominator factor".into())
                    })?;
                let mut factors = factors.clone();
                factors.remove(position);
                PolynomialExpr::Mul(factors).to_cas(limits)?
            }
            PolynomialExpr::Pow { base, exponent }
                if **base == subject.denominator && *exponent > 0 =>
            {
                PolynomialExpr::Pow {
                    base: base.clone(),
                    exponent: exponent - 1,
                }
                .to_cas(limits)?
            }
            _ => {
                return Err(TraceError::Unsupported(
                    "no syntactic denominator factor".into(),
                ));
            }
        }
    };
    let result = normalize_with_trace(&raw_result, limits)?.result;
    let numerator_identity = normalize_with_trace(&subject.numerator.to_cas(limits)?, limits)?;
    let product_identity =
        normalize_with_trace(&product(subject, &result).to_cas(limits)?, limits)?;
    let trace = GuardedQuotientTrace {
        version: "cas-guarded-quotient-v1".into(),
        input: subject.clone(),
        result,
        nonzero_assumptions: nonzero_assumptions.to_vec(),
        denominator_premise: premise,
        numerator_identity,
        product_identity,
    };
    check_guarded_trace(&trace, subject, &trace.result, nonzero_assumptions, limits)?;
    trace.to_json(limits)?;
    Ok(trace)
}
impl GuardedQuotientTrace {
    /// Export checked evidence; external context binding still requires replay.
    ///
    /// # Errors
    /// Invalid evidence or aggregate serialized-byte exhaustion.
    pub fn to_json(&self, limits: TraceLimits) -> Result<String, TraceError> {
        check_guarded_trace(
            self,
            &self.input,
            &self.result,
            &self.nonzero_assumptions,
            limits,
        )?;
        let bytes = serde_json::to_string(self).map_err(|_| reject("JSON serialization"))?;
        if bytes.len() > limits.bytes {
            return Err(TraceError::ResourceLimit(
                "guarded certificate byte limit".into(),
            ));
        }
        Ok(bytes)
    }
}
/// Parse and replay evidence against an external conditional statement.
///
/// # Errors
/// Malformed/oversized data, unsupported scope, or failed checking obligations.
pub fn replay_guarded_json(
    bytes: &[u8],
    subject: &QuotientSubject,
    result: &PolynomialExpr,
    nonzero_assumptions: &[PolynomialExpr],
    limits: TraceLimits,
) -> Result<GuardedQuotientTrace, TraceError> {
    if bytes.len() > limits.bytes {
        return Err(TraceError::ResourceLimit(
            "guarded certificate byte limit".into(),
        ));
    }
    let trace: GuardedQuotientTrace =
        serde_json::from_slice(bytes).map_err(|_| reject("malformed guarded JSON"))?;
    check_guarded_trace(&trace, subject, result, nonzero_assumptions, limits)?;
    Ok(trace)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> (QuotientSubject, Vec<PolynomialExpr>, TraceLimits) {
        let x = PolynomialExpr::Var("x".into());
        (
            QuotientSubject {
                numerator: PolynomialExpr::Mul(vec![x.clone(), x.clone()]),
                denominator: x.clone(),
            },
            vec![x],
            TraceLimits::default(),
        )
    }
    #[test]
    fn quotient_bytes_bind_the_original_conditional_statement() {
        let (subject, assumptions, limits) = fixture();
        let trace = cancel_factor_with_trace(&subject, &assumptions, limits).unwrap();
        assert_eq!(trace.result, PolynomialExpr::Var("x".into()));
        let bytes = trace.to_json(limits).unwrap();
        replay_guarded_json(
            bytes.as_bytes(),
            &subject,
            &trace.result,
            &assumptions,
            limits,
        )
        .unwrap();
        assert!(
            replay_guarded_json(bytes.as_bytes(), &subject, &trace.result, &[], limits).is_err()
        );
        let changed = vec![PolynomialExpr::Var("y".into())];
        assert!(
            replay_guarded_json(bytes.as_bytes(), &subject, &trace.result, &changed, limits)
                .is_err()
        );
    }
    #[test]
    fn external_context_extension_requires_recertification() {
        let (subject, assumptions, limits) = fixture();
        let trace = cancel_factor_with_trace(&subject, &assumptions, limits).unwrap();
        let mut extended = assumptions;
        extended.push(PolynomialExpr::Var("y".into()));
        assert!(check_guarded_trace(&trace, &subject, &trace.result, &extended, limits).is_err());
    }
    #[test]
    fn false_quotient_and_missing_premise_are_rejected() {
        let (subject, assumptions, limits) = fixture();
        let mut trace = cancel_factor_with_trace(&subject, &assumptions, limits).unwrap();
        trace.result = PolynomialExpr::Var("y".into());
        trace.product_identity = normalize_with_trace(
            &product(&subject, &trace.result).to_cas(limits).unwrap(),
            limits,
        )
        .unwrap();
        assert!(
            check_guarded_trace(&trace, &subject, &trace.result, &assumptions, limits).is_err()
        );
        assert!(cancel_factor_with_trace(&subject, &[], limits).is_err());
    }
    #[test]
    fn zero_denominator_is_not_cancelled() {
        let zero = PolynomialExpr::Const {
            numerator: "0".into(),
            denominator: "1".into(),
        };
        let subject = QuotientSubject {
            numerator: zero.clone(),
            denominator: zero.clone(),
        };
        assert!(cancel_factor_with_trace(&subject, &[zero], TraceLimits::default()).is_err());
    }
}
