//! Nested conditional cancellation with source-bound congruence (ADR-8400).
//! Equality preserves partial definedness under the caller's nonzero context.
use crate::guarded_trace::{
    GuardedQuotientTrace, QuotientSubject, cancel_factor_with_trace_wide, check_guarded_trace,
};
use crate::rewrite_trace::{PolynomialExpr, TraceError, TraceLimits};
use serde::{Deserialize, Serialize};

/// One guarded replacement in its complete surrounding expression.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConditionalStep {
    /// Consecutive zero-based ID.
    pub id: usize,
    /// Previous step ID, absent on the first step.
    pub predecessor: Option<usize>,
    /// Full input expression.
    pub before: PolynomialExpr,
    /// Full output expression.
    pub after: PolynomialExpr,
    /// Child indices selecting the quotient.
    pub location: Vec<usize>,
    /// Checked local quotient cancellation, including its exact context.
    pub witness: GuardedQuotientTrace,
}
/// An ordered conditional equality; checking grants no kernel admission.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConditionalTrace {
    /// Explicit composition version, separate from polynomial/quotient versions.
    pub version: String,
    /// Original subject.
    pub input: PolynomialExpr,
    /// Claimed endpoint.
    pub result: PolynomialExpr,
    /// Ordered caller assumptions, each interpreted as nonzero.
    pub nonzero_assumptions: Vec<PolynomialExpr>,
    /// Ordered contextual replacements.
    pub steps: Vec<ConditionalStep>,
}
fn reject(step: Option<usize>, reason: &str) -> TraceError {
    TraceError::Rejected {
        step,
        reason: reason.into(),
    }
}
fn resource(reason: &str) -> TraceError {
    TraceError::ResourceLimit(reason.into())
}
fn syntax(expr: &PolynomialExpr, limits: TraceLimits) -> Result<(), TraceError> {
    fn visit(
        expr: &PolynomialExpr,
        depth: usize,
        nodes: &mut usize,
        limits: TraceLimits,
    ) -> Result<(), TraceError> {
        *nodes += 1;
        if depth > limits.depth || *nodes > limits.nodes {
            return Err(resource("conditional expression shape"));
        }
        match expr {
            PolynomialExpr::Const { .. } | PolynomialExpr::Var(_) => {
                expr.to_cas_wide(limits)?;
            }
            PolynomialExpr::Pow { exponent, .. } if *exponent > limits.degree => {
                return Err(resource("conditional exponent"));
            }
            _ => {}
        }
        for child in expr.children() {
            visit(child, depth + 1, nodes, limits)?;
        }
        Ok(())
    }
    visit(expr, 0, &mut 0, limits)
}
fn subject(expr: &PolynomialExpr) -> Option<QuotientSubject> {
    match expr {
        PolynomialExpr::Div {
            numerator,
            denominator,
        } => Some(QuotientSubject {
            numerator: (**numerator).clone(),
            denominator: (**denominator).clone(),
        }),
        _ => None,
    }
}
/// Check source, context, all local witnesses, congruence and final continuity.
///
/// # Errors
/// Rejects mismatched/corrupt evidence; declines unsupported witnesses or exhausted policy.
pub fn check_conditional_trace(
    trace: &ConditionalTrace,
    input: &PolynomialExpr,
    result: &PolynomialExpr,
    context: &[PolynomialExpr],
    limits: TraceLimits,
) -> Result<(), TraceError> {
    let limits = limits.policy()?;
    if trace.version != "cas-conditional-composition-v1" {
        return Err(TraceError::Unsupported(
            "conditional composition version".into(),
        ));
    }
    if trace.input != *input || trace.result != *result || trace.nonzero_assumptions != context {
        return Err(reject(None, "conditional source or context mismatch"));
    }
    if trace.steps.len() > limits.steps || context.len() > limits.nodes {
        return Err(resource("conditional step/context count"));
    }
    syntax(input, limits)?;
    syntax(result, limits)?;
    for assumption in context {
        assumption.to_cas_wide(limits)?;
    }
    let mut previous = input;
    let mut work = 0_u64;
    for (id, step) in trace.steps.iter().enumerate() {
        if step.id != id || step.predecessor != id.checked_sub(1) || step.before != *previous {
            return Err(reject(Some(id), "conditional ordering or continuity"));
        }
        syntax(&step.before, limits)?;
        syntax(&step.after, limits)?;
        if step.location.len() > limits.depth {
            return Err(resource("conditional path depth"));
        }
        let local = step
            .before
            .local(&step.location)
            .and_then(subject)
            .ok_or_else(|| reject(Some(id), "conditional quotient location"))?;
        if step.witness.version != "cas-guarded-quotient-v2" {
            return Err(TraceError::Unsupported(
                "conditional witness version".into(),
            ));
        }
        for identity in [
            &step.witness.numerator_identity,
            &step.witness.product_identity,
        ] {
            work = work
                .checked_add(identity.limits.work)
                .ok_or_else(|| resource("conditional aggregate witness work"))?;
            if work > limits.work {
                return Err(resource("conditional aggregate witness work"));
            }
        }
        check_guarded_trace(&step.witness, &local, &step.witness.result, context, limits)?;
        if step
            .before
            .replace(&step.location, &step.witness.result)
            .as_ref()
            != Some(&step.after)
        {
            return Err(reject(
                Some(id),
                "conditional surrounding expression changed",
            ));
        }
        previous = &step.after;
    }
    if previous != result {
        return Err(reject(None, "conditional final endpoint"));
    }
    let bytes = serde_json::to_vec(trace).map_err(|_| reject(None, "conditional JSON"))?;
    if bytes.len() > limits.bytes {
        return Err(resource("conditional aggregate bytes"));
    }
    Ok(())
}
/// Produce deterministic nested cancellation steps under the supplied assumptions.
///
/// # Errors
/// Unsupported quotient operands, absent premises, zero denominators, or resource exhaustion.
pub fn cancel_nested_with_trace(
    input: &PolynomialExpr,
    context: &[PolynomialExpr],
    limits: TraceLimits,
) -> Result<ConditionalTrace, TraceError> {
    let limits = limits.policy()?;
    syntax(input, limits)?;
    fn locations(expr: &PolynomialExpr, path: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        for (index, child) in expr.children().into_iter().enumerate() {
            path.push(index);
            locations(child, path, out);
            path.pop();
        }
        if matches!(expr, PolynomialExpr::Div { .. }) {
            out.push(path.clone());
        }
    }
    let mut paths = Vec::new();
    locations(input, &mut Vec::new(), &mut paths);
    if paths.len() > limits.steps {
        return Err(resource("conditional producer step count"));
    }
    let count = u64::try_from(paths.len().max(1)).map_err(|_| resource("conditional count"))?;
    let local_limits = TraceLimits {
        work: limits.work / (2 * count),
        ..limits
    };
    let mut current = input.clone();
    let mut steps = Vec::new();
    for path in paths {
        let local = current
            .local(&path)
            .and_then(subject)
            .ok_or_else(|| reject(None, "conditional producer location"))?;
        let witness = cancel_factor_with_trace_wide(&local, context, local_limits)?;
        let after = current
            .replace(&path, &witness.result)
            .ok_or_else(|| reject(None, "conditional producer replacement"))?;
        let id = steps.len();
        steps.push(ConditionalStep {
            id,
            predecessor: id.checked_sub(1),
            before: current,
            after: after.clone(),
            location: path,
            witness,
        });
        current = after;
    }
    let trace = ConditionalTrace {
        version: "cas-conditional-composition-v1".into(),
        input: input.clone(),
        result: current,
        nonzero_assumptions: context.to_vec(),
        steps,
    };
    check_conditional_trace(&trace, input, &trace.result, context, limits)?;
    Ok(trace)
}
/// Restore and replay a conditional trace without invoking production.
///
/// # Errors
/// Invalid/oversized bytes, failed source binding, unsupported witnesses or exhausted policy.
pub fn replay_conditional_json(
    bytes: &[u8],
    input: &PolynomialExpr,
    result: &PolynomialExpr,
    context: &[PolynomialExpr],
    limits: TraceLimits,
) -> Result<ConditionalTrace, TraceError> {
    let limits = limits.policy()?;
    if bytes.len() > limits.bytes {
        return Err(resource("conditional JSON byte cap"));
    }
    let trace: ConditionalTrace =
        serde_json::from_slice(bytes).map_err(|_| reject(None, "malformed conditional JSON"))?;
    check_conditional_trace(&trace, input, result, context, limits)?;
    Ok(trace)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn x() -> PolynomialExpr {
        PolynomialExpr::Var("x".into())
    }
    fn quotient() -> PolynomialExpr {
        PolynomialExpr::Div {
            numerator: Box::new(PolynomialExpr::Mul(vec![x(), x()])),
            denominator: Box::new(x()),
        }
    }
    fn fixture() -> (PolynomialExpr, Vec<PolynomialExpr>) {
        (
            PolynomialExpr::Add(vec![quotient(), PolynomialExpr::Neg(Box::new(quotient()))]),
            vec![x()],
        )
    }
    fn evaluate(expr: &PolynomialExpr, value: crate::Rational) -> Option<crate::Rational> {
        use crate::Rational;
        match expr {
            PolynomialExpr::Var(name) if name == "x" => Some(value),
            PolynomialExpr::Const {
                numerator,
                denominator,
            } => Rational::checked_new(numerator.parse().ok()?, denominator.parse().ok()?),
            PolynomialExpr::Add(xs) => xs.iter().try_fold(Rational::integer(0), |sum, x| {
                sum.wide_add(evaluate(x, value)?)
            }),
            PolynomialExpr::Mul(xs) => xs.iter().try_fold(Rational::integer(1), |product, x| {
                product.wide_mul(evaluate(x, value)?)
            }),
            PolynomialExpr::Neg(x) => evaluate(x, value)?.wide_neg(),
            PolynomialExpr::Div {
                numerator,
                denominator,
            } => evaluate(numerator, value)?.wide_div(evaluate(denominator, value)?),
            PolynomialExpr::Pow { base, exponent } => (0..*exponent)
                .try_fold(Rational::integer(1), |product, _| {
                    product.wide_mul(evaluate(base, value)?)
                }),
            _ => None,
        }
    }
    #[test]
    fn two_nested_steps_replay_and_preserve_exact_values() {
        let (input, context) = fixture();
        let limits = TraceLimits::default();
        let trace = cancel_nested_with_trace(&input, &context, limits).unwrap();
        assert_eq!(trace.steps.len(), 2);
        let bytes = serde_json::to_vec(&trace).unwrap();
        let repeated = cancel_nested_with_trace(&input, &context, limits).unwrap();
        assert_eq!(bytes, serde_json::to_vec(&repeated).unwrap());
        assert_eq!(
            trace,
            replay_conditional_json(&bytes, &input, &trace.result, &context, limits).unwrap()
        );
        for n in [-7, -1, 1, 3, 11] {
            let value = crate::Rational::checked_new(n, 3).unwrap();
            assert_eq!(evaluate(&input, value), evaluate(&trace.result, value));
        }
        assert!(evaluate(&input, crate::Rational::integer(0)).is_none());
        assert!(check_conditional_trace(&trace, &input, &trace.result, &[], limits).is_err());
    }
    #[test]
    fn contextual_replacement_rejects_changed_surrounding_subtree() {
        let input = PolynomialExpr::Add(vec![quotient(), x()]);
        let limits = TraceLimits::default();
        let mut trace = cancel_nested_with_trace(&input, &[x()], limits).unwrap();
        trace.result = PolynomialExpr::Add(vec![x(), PolynomialExpr::Neg(Box::new(x()))]);
        trace.steps[0].after = trace.result.clone();
        assert!(check_conditional_trace(&trace, &input, &trace.result, &[x()], limits).is_err());
    }
    #[test]
    fn altered_paths_order_witnesses_and_endpoints_reject() {
        let (input, context) = fixture();
        let limits = TraceLimits::default();
        let trace = cancel_nested_with_trace(&input, &context, limits).unwrap();
        let mut mutants = Vec::new();
        let mut m = trace.clone();
        m.steps[0].location = vec![1];
        mutants.push(m);
        let mut m = trace.clone();
        m.steps.swap(0, 1);
        mutants.push(m);
        let mut m = trace.clone();
        m.steps.pop();
        mutants.push(m);
        let mut m = trace.clone();
        m.steps[0].witness.denominator_premise = 1;
        mutants.push(m);
        let mut m = trace.clone();
        m.steps[0].witness.result = PolynomialExpr::Neg(Box::new(x()));
        mutants.push(m);
        for mutant in mutants {
            assert!(
                check_conditional_trace(&mutant, &input, &trace.result, &context, limits).is_err()
            );
        }
        assert!(
            check_conditional_trace(&trace, &quotient(), &trace.result, &context, limits).is_err()
        );
    }
    #[test]
    fn zero_and_missing_premises_do_not_license_cancellation() {
        assert!(cancel_nested_with_trace(&quotient(), &[], TraceLimits::default()).is_err());
        let zero = PolynomialExpr::Const {
            numerator: "0".into(),
            denominator: "1".into(),
        };
        let input = PolynomialExpr::Div {
            numerator: Box::new(zero.clone()),
            denominator: Box::new(zero.clone()),
        };
        assert!(cancel_nested_with_trace(&input, &[zero], TraceLimits::default()).is_err());
    }
    #[test]
    fn aggregate_work_step_and_byte_caps_decline() {
        let (input, context) = fixture();
        let limits = TraceLimits::default();
        let trace = cancel_nested_with_trace(&input, &context, limits).unwrap();
        for policy in [
            TraceLimits { steps: 1, ..limits },
            TraceLimits { work: 1, ..limits },
            TraceLimits { bytes: 1, ..limits },
        ] {
            assert!(matches!(
                check_conditional_trace(&trace, &input, &trace.result, &context, policy),
                Err(TraceError::ResourceLimit(_))
            ));
        }
        assert!(matches!(
            replay_conditional_json(
                b"{}",
                &input,
                &trace.result,
                &context,
                TraceLimits { bytes: 1, ..limits }
            ),
            Err(TraceError::ResourceLimit(_))
        ));
    }
}
