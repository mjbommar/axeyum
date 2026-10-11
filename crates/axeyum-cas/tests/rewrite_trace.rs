//! Source binding and failure sensitivity for the CAS step-log contract.
use axeyum_cas::{
    CasExpr,
    rewrite_trace::{
        PolynomialExpr, TraceError, TraceLimits, check_trace, normalize_with_trace, replay_json,
    },
};
use axeyum_ir::Rational;
use std::collections::BTreeMap;

fn example() -> CasExpr {
    let x = CasExpr::var("x");
    (x.clone() + CasExpr::int(1) + CasExpr::int(2)) * (-(-(x + CasExpr::int(1))))
}

#[test]
fn multi_step_trace_is_deterministic_and_replays_serialized_evidence() {
    let expr = example();
    let limits = TraceLimits::default();
    let trace = normalize_with_trace(&expr, limits).unwrap();
    assert!(
        trace.steps.len() >= 3,
        "must exercise continuity, not a one-step wrapper"
    );
    let bytes = trace.to_json(limits).unwrap();
    assert_eq!(
        bytes,
        normalize_with_trace(&expr, limits)
            .unwrap()
            .to_json(limits)
            .unwrap()
    );
    assert_eq!(
        replay_json(bytes.as_bytes(), &trace.input, &trace.result, limits).unwrap(),
        trace
    );
    // Independently evaluate the claimed identity at discriminating rationals.
    let canonical = trace.result.to_cas(limits).unwrap();
    for value in [-3, 0, 2, 7] {
        let env = BTreeMap::from([("x".to_owned(), Rational::new(value, 2))]);
        assert_eq!(expr.eval(&env), canonical.eval(&env));
        assert!(expr.eval(&env).is_some());
    }
}

#[test]
fn a_changed_endpoint_is_rejected() {
    let limits = TraceLimits::default();
    let trace = normalize_with_trace(&example(), limits).unwrap();
    let mut corrupt = trace.clone();
    corrupt.result = PolynomialExpr::from_cas(&CasExpr::int(19), limits).unwrap();
    assert!(matches!(
        check_trace(&corrupt, &trace.input, &corrupt.result, limits),
        Err(TraceError::Rejected { .. })
    ));
}

#[test]
fn corrupt_steps_witnesses_and_contexts_are_rejected() {
    let limits = TraceLimits::default();
    let trace = normalize_with_trace(&example(), limits).unwrap();
    let mut variants = Vec::new();
    let mut t = trace.clone();
    t.steps.remove(0);
    variants.push(t);
    let mut t = trace.clone();
    t.steps.swap(0, 1);
    variants.push(t);
    let mut t = trace.clone();
    t.steps[0].id = 5;
    variants.push(t);
    let mut t = trace.clone();
    t.steps[0].location = vec![999];
    variants.push(t);
    let mut t = trace.clone();
    t.steps[0].context = "invented".to_owned();
    variants.push(t);
    let mut t = trace.clone();
    t.steps[0].premises = vec![0];
    variants.push(t);
    let mut t = trace.clone();
    t.steps[0].side_conditions.push(trace.input.clone());
    variants.push(t);
    let mut t = trace.clone();
    t.steps[0].witness = PolynomialExpr::from_cas(&CasExpr::int(999), limits).unwrap();
    variants.push(t);
    let mut t = trace.clone();
    t.steps[0].rule = "polynomial.pow.v1".to_owned();
    variants.push(t);
    let mut t = trace.clone();
    t.steps[0].exponent = Some(5);
    variants.push(t);
    let mut t = trace.clone();
    t.steps[0].after = trace.input.clone();
    variants.push(t);
    for (index, t) in variants.iter().enumerate() {
        assert!(
            check_trace(t, &trace.input, &trace.result, limits).is_err(),
            "corruption {index} passed"
        );
    }
}

#[test]
fn source_binding_and_empty_traces_are_not_vacuous() {
    let limits = TraceLimits::default();
    let trace = normalize_with_trace(&CasExpr::int(2), limits).unwrap();
    assert!(trace.steps.is_empty());
    assert!(check_trace(&trace, &trace.input, &trace.result, limits).is_ok());
    let other = PolynomialExpr::from_cas(&CasExpr::int(3), limits).unwrap();
    assert!(matches!(
        check_trace(&trace, &other, &trace.result, limits),
        Err(TraceError::Rejected { .. })
    ));
    let mut invalid = trace.clone();
    invalid.result = other;
    assert!(check_trace(&invalid, &invalid.input, &invalid.result, limits).is_err());
}

#[test]
fn unsupported_domains_and_exhausted_resources_are_distinct() {
    let limits = TraceLimits::default();
    let fraction = CasExpr::Div(
        Box::new(CasExpr::var("x").pow(2)),
        Box::new(CasExpr::var("x")),
    );
    assert!(matches!(
        normalize_with_trace(&fraction, limits),
        Err(TraceError::Unsupported(_))
    ));
    let zero_denominator = CasExpr::Div(Box::new(CasExpr::int(1)), Box::new(CasExpr::zero()));
    assert!(matches!(
        normalize_with_trace(&zero_denominator, limits),
        Err(TraceError::Unsupported(_))
    ));
    assert!(matches!(
        normalize_with_trace(&example(), TraceLimits { work: 0, ..limits }),
        Err(TraceError::ResourceLimit(_))
    ));
    assert!(matches!(
        normalize_with_trace(&example(), TraceLimits { steps: 0, ..limits }),
        Err(TraceError::ResourceLimit(_))
    ));
    assert!(matches!(
        normalize_with_trace(
            &CasExpr::Add(vec![CasExpr::var("x"), CasExpr::int(1)]).pow(32),
            limits
        ),
        Err(TraceError::ResourceLimit(_))
    ));
    let trace = normalize_with_trace(&example(), limits).unwrap();
    let bytes = trace.to_json(limits).unwrap();
    assert!(matches!(
        replay_json(
            bytes.as_bytes(),
            &trace.input,
            &trace.result,
            TraceLimits { bytes: 1, ..limits }
        ),
        Err(TraceError::ResourceLimit(_))
    ));
    assert!(replay_json(b"{}", &trace.input, &trace.result, limits).is_err());
}

#[test]
fn malformed_coefficients_are_rejections_and_wide_coefficients_are_limits() {
    let limits = TraceLimits::default();
    for numerator in ["abc", "+1", "-", "-0", "01"] {
        let expr = PolynomialExpr::Const {
            numerator: numerator.to_owned(),
            denominator: "1".to_owned(),
        };
        assert!(matches!(
            expr.to_cas(limits),
            Err(TraceError::Rejected { .. })
        ));
    }
    let wide = PolynomialExpr::Const {
        numerator: "340282366920938463463374607431768211456".to_owned(),
        denominator: "1".to_owned(),
    };
    assert!(matches!(
        wide.to_cas(limits),
        Err(TraceError::ResourceLimit(_))
    ));
}

#[test]
fn power_and_empty_operators_have_checked_numeric_semantics() {
    let limits = TraceLimits::default();
    let env = BTreeMap::from([("x".to_owned(), Rational::new(3, 2))]);
    for (expr, expected) in [
        (
            (CasExpr::var("x") + CasExpr::int(1)).pow(2),
            Rational::new(25, 4),
        ),
        (CasExpr::zero().pow(0), Rational::integer(1)),
        (CasExpr::Add(Vec::new()), Rational::zero()),
        (CasExpr::Mul(Vec::new()), Rational::integer(1)),
        (-CasExpr::int(3), Rational::integer(-3)),
    ] {
        let trace = normalize_with_trace(&expr, limits).unwrap();
        assert!(!trace.steps.is_empty());
        assert!(check_trace(&trace, &trace.input, &trace.result, limits).is_ok());
        assert_eq!(expr.eval(&env), Some(expected));
        assert_eq!(
            trace.result.to_cas(limits).unwrap().eval(&env),
            Some(expected)
        );
        if trace.steps[0].rule == "polynomial.pow.v1" {
            let mut corrupt = trace.clone();
            corrupt.steps[0].exponent = Some(31);
            assert!(matches!(
                check_trace(&corrupt, &trace.input, &trace.result, limits),
                Err(TraceError::Rejected { step: Some(0), .. })
            ));
        }
    }
}

#[test]
fn malformed_local_witness_reports_the_failing_step() {
    let limits = TraceLimits::default();
    let source = (CasExpr::var("x") + CasExpr::int(1)) * CasExpr::int(2);
    let trace = normalize_with_trace(&source, limits).unwrap();
    let mut corrupt = trace.clone();
    corrupt.steps[0].witness = PolynomialExpr::Const {
        numerator: "not_a_number".to_owned(),
        denominator: "1".to_owned(),
    };
    assert!(matches!(
        check_trace(&corrupt, &trace.input, &trace.result, limits),
        Err(TraceError::Rejected { step: Some(0), .. })
    ));
}
