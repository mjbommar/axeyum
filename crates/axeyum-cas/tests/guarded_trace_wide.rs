use axeyum_cas::guarded_trace::{
    QuotientSubject, cancel_factor_with_trace, cancel_factor_with_trace_wide, check_guarded_trace,
    replay_guarded_json,
};
use axeyum_cas::rewrite_trace::{PolynomialExpr, TraceError, TraceLimits};

fn fixture() -> (QuotientSubject, Vec<PolynomialExpr>) {
    let x = PolynomialExpr::Var("x".into());
    let coefficient = PolynomialExpr::Const {
        numerator: "1606938044258990275541962092341162602522202993782792835301376".into(),
        denominator: "3".into(),
    };
    (
        QuotientSubject {
            numerator: PolynomialExpr::Mul(vec![x.clone(), coefficient]),
            denominator: x.clone(),
        },
        vec![x],
    )
}

#[test]
fn wide_conditional_bytes_replay_and_v1_declines() {
    let (subject, context) = fixture();
    let limits = TraceLimits::default();
    assert!(cancel_factor_with_trace(&subject, &context, limits).is_err());
    let trace = cancel_factor_with_trace_wide(&subject, &context, limits).unwrap();
    assert_eq!(trace.version, "cas-guarded-quotient-v2");
    assert_eq!(trace.numerator_identity.version, "cas-polynomial-trace-v2");
    assert_eq!(
        trace.result,
        match &subject.numerator {
            PolynomialExpr::Mul(factors) => factors[1].clone(),
            _ => unreachable!(),
        }
    );
    let bytes = trace.to_json(limits).unwrap();
    assert_eq!(
        replay_guarded_json(bytes.as_bytes(), &subject, &trace.result, &context, limits).unwrap(),
        trace
    );
}

#[test]
fn wide_identity_versions_are_bound_to_the_envelope() {
    let x = PolynomialExpr::Var("x".into());
    let subject = QuotientSubject {
        numerator: x.clone(),
        denominator: x.clone(),
    };
    let limits = TraceLimits::default();
    let context = vec![x];
    let mut trace = cancel_factor_with_trace_wide(&subject, &context, limits).unwrap();
    // The same identity is mathematically valid under v1. Mixing versions must
    // still fail even when coefficient width cannot incidentally reject it.
    trace.numerator_identity.version = "cas-polynomial-trace-v1".into();
    assert!(matches!(
        check_guarded_trace(&trace, &subject, &trace.result, &context, limits),
        Err(TraceError::Rejected { .. })
    ));
}

#[test]
fn wide_context_endpoint_and_budget_corruption_are_rejected() {
    let (subject, context) = fixture();
    let limits = TraceLimits::default();
    let trace = cancel_factor_with_trace_wide(&subject, &context, limits).unwrap();
    let mut changed_context = context.clone();
    changed_context.push(PolynomialExpr::Var("y".into()));
    assert!(
        check_guarded_trace(&trace, &subject, &trace.result, &changed_context, limits).is_err()
    );
    assert!(check_guarded_trace(&trace, &subject, &subject.denominator, &context, limits).is_err());
    let mut limited = limits;
    limited.work = 0;
    assert!(matches!(
        cancel_factor_with_trace_wide(&subject, &context, limited),
        Err(TraceError::ResourceLimit(_))
    ));
}

#[test]
fn wide_zero_polynomial_denominator_is_not_licensed_by_an_assumption() {
    let x = PolynomialExpr::Var("x".into());
    let zero = PolynomialExpr::Add(vec![x.clone(), PolynomialExpr::Neg(Box::new(x))]);
    let subject = QuotientSubject {
        numerator: zero.clone(),
        denominator: zero.clone(),
    };
    assert!(matches!(
        cancel_factor_with_trace_wide(&subject, &[zero], TraceLimits::default()),
        Err(TraceError::Rejected { .. })
    ));
}
