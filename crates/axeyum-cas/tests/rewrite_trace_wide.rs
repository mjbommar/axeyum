//! Version-two trace transport never narrows promoted coefficients.
use axeyum_cas::{
    CasExpr,
    rewrite_trace::{
        PolynomialExpr, TraceError, TraceLimits, normalize_with_trace, normalize_with_trace_wide,
        replay_json,
    },
};
use axeyum_ir::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;

fn fixture() -> CasExpr {
    let coefficient =
        Rational::from_big_rational(&BigRational::new(BigInt::from(1) << 200, BigInt::from(3)))
            .unwrap();
    let x = CasExpr::var("x");
    CasExpr::Mul(vec![
        CasExpr::Const(coefficient),
        CasExpr::Add(vec![x.clone(), x]),
    ])
}
#[test]
fn promoted_local_witnesses_round_trip_and_v1_stays_narrow() {
    let source = fixture();
    let limits = TraceLimits::default();
    assert!(matches!(
        normalize_with_trace(&source, limits),
        Err(TraceError::ResourceLimit(_))
    ));
    let trace = normalize_with_trace_wide(&source, limits).unwrap();
    assert_eq!(trace.version, "cas-polynomial-trace-v2");
    assert!(trace.steps.len() >= 2);
    assert!(
        trace
            .steps
            .iter()
            .all(|step| step.context == "empty-v2" && step.side_conditions.is_empty())
    );
    let bytes = trace.to_json(limits).unwrap();
    replay_json(
        bytes.as_bytes(),
        &PolynomialExpr::from_cas_wide(&source, limits).unwrap(),
        &trace.result,
        limits,
    )
    .unwrap();
    assert_eq!(trace.input.to_cas_wide(limits).unwrap(), source);
    assert!(trace.result.to_cas(limits).is_err());
    assert_eq!(
        normalize_with_trace_wide(&source, limits)
            .unwrap()
            .to_json(limits)
            .unwrap(),
        bytes
    );
}
#[test]
fn closed_360th_power_has_an_exact_checked_wide_endpoint() {
    let source = CasExpr::Pow(
        Box::new(CasExpr::Add(vec![CasExpr::int(1), CasExpr::rat(1, 240)])),
        360,
    );
    let limits = TraceLimits::default();
    let trace = normalize_with_trace_wide(&source, limits).unwrap();
    let expected = Rational::from_big_rational(&BigRational::new(
        BigInt::from(241).pow(360),
        BigInt::from(240).pow(360),
    ))
    .unwrap();
    assert_eq!(
        trace.result.to_cas_wide(limits).unwrap(),
        CasExpr::Const(expected)
    );
    assert_eq!(trace.steps.len(), 2);
    replay_json(
        trace.to_json(limits).unwrap().as_bytes(),
        &trace.input,
        &trace.result,
        limits,
    )
    .unwrap();
}
#[test]
fn changed_context_witness_and_subject_cannot_replay() {
    let limits = TraceLimits::default();
    let trace = normalize_with_trace_wide(&fixture(), limits).unwrap();
    let bytes = trace.to_json(limits).unwrap();
    let mut changed = trace.clone();
    changed.steps[0].context = "empty-v1".into();
    assert!(changed.to_json(limits).is_err());
    let mut changed = trace.clone();
    changed.steps[0].witness = PolynomialExpr::Const {
        numerator: "99".into(),
        denominator: "1".into(),
    };
    let corrupt = serde_json::to_vec(&changed).unwrap();
    assert!(replay_json(&corrupt, &trace.input, &trace.result, limits).is_err());
    let source = PolynomialExpr::Var("different".into());
    assert!(replay_json(bytes.as_bytes(), &source, &trace.result, limits).is_err());
    let mut changed = trace.clone();
    changed.steps.pop();
    assert!(changed.to_json(limits).is_err());
}
#[test]
fn canonical_and_bit_work_degree_caps_are_checked() {
    let limits = TraceLimits::default();
    for (numerator, denominator) in [("01", "1"), ("-0", "1"), ("2", "4"), ("1", "-1")] {
        let wire = PolynomialExpr::Const {
            numerator: numerator.into(),
            denominator: denominator.into(),
        };
        assert!(matches!(
            wire.to_cas_wide(limits),
            Err(TraceError::Rejected { .. })
        ));
    }
    let too_wide = PolynomialExpr::Const {
        numerator: (BigInt::from(1) << 16_384_usize).to_string(),
        denominator: "1".into(),
    };
    assert!(matches!(
        too_wide.to_cas_wide(limits),
        Err(TraceError::ResourceLimit(_))
    ));
    assert!(matches!(
        normalize_with_trace_wide(&fixture(), TraceLimits { work: 0, ..limits }),
        Err(TraceError::ResourceLimit(_))
    ));
    assert!(matches!(
        normalize_with_trace_wide(&CasExpr::Pow(Box::new(CasExpr::var("x")), 33), limits),
        Err(TraceError::ResourceLimit(_))
    ));
    assert!(matches!(
        normalize_with_trace_wide(&CasExpr::Pow(Box::new(CasExpr::int(2)), 513), limits),
        Err(TraceError::ResourceLimit(_))
    ));
}

#[test]
fn exact_amortization_replays_two_checked_divisions() {
    let limits = TraceLimits::default();
    let rate = CasExpr::rat(1, 240);
    let growth = CasExpr::Pow(
        Box::new(CasExpr::Add(vec![CasExpr::int(1), rate.clone()])),
        360,
    );
    let reciprocal = CasExpr::Div(Box::new(CasExpr::int(1)), Box::new(growth));
    let source = CasExpr::Div(
        Box::new(CasExpr::Mul(vec![CasExpr::int(300_000), rate])),
        Box::new(CasExpr::Add(vec![
            CasExpr::int(1),
            CasExpr::Neg(Box::new(reciprocal)),
        ])),
    );
    let trace = normalize_with_trace_wide(&source, limits).unwrap();
    let high = BigInt::from(241).pow(360);
    let low = BigInt::from(240).pow(360);
    let expected = Rational::from_big_rational(&BigRational::new(
        BigInt::from(300_000) * &high,
        BigInt::from(240) * (high - low),
    ))
    .unwrap();
    assert_eq!(
        trace.result.to_cas_wide(limits).unwrap(),
        CasExpr::Const(expected)
    );
    let divisions: Vec<_> = trace
        .steps
        .iter()
        .filter(|step| step.rule == "rational.div.constant.v2")
        .collect();
    assert_eq!(divisions.len(), 2);
    assert!(divisions.iter().all(|step| step.side_conditions.len() == 1));
    replay_json(
        trace.to_json(limits).unwrap().as_bytes(),
        &trace.input,
        &trace.result,
        limits,
    )
    .unwrap();
}
#[test]
fn division_steps_bind_the_recorded_nonzero_condition() {
    let limits = TraceLimits::default();
    let source = CasExpr::Div(Box::new(CasExpr::int(1)), Box::new(CasExpr::int(2)));
    assert!(normalize_with_trace(&source, limits).is_err());
    let mut trace = normalize_with_trace_wide(&source, limits).unwrap();
    assert_eq!(trace.steps[0].side_conditions.len(), 1);
    trace.steps[0].side_conditions.clear();
    assert!(
        replay_json(
            &serde_json::to_vec(&trace).unwrap(),
            &trace.input,
            &trace.result,
            limits
        )
        .is_err()
    );
}
#[test]
fn an_empty_trace_cannot_certify_an_undefined_quotient() {
    let limits = TraceLimits::default();
    let mut trace = normalize_with_trace_wide(&CasExpr::int(1), limits).unwrap();
    let zero = PolynomialExpr::Const {
        numerator: "0".into(),
        denominator: "1".into(),
    };
    let one = PolynomialExpr::Const {
        numerator: "1".into(),
        denominator: "1".into(),
    };
    let undefined = PolynomialExpr::Div {
        numerator: Box::new(one),
        denominator: Box::new(zero),
    };
    trace.input = undefined.clone();
    trace.result = undefined;
    assert!(matches!(
        replay_json(
            &serde_json::to_vec(&trace).unwrap(),
            &trace.input,
            &trace.result,
            limits
        ),
        Err(TraceError::Rejected { .. })
    ));
    assert!(
        normalize_with_trace_wide(
            &CasExpr::Div(Box::new(CasExpr::int(1)), Box::new(CasExpr::var("x"))),
            limits
        )
        .is_err()
    );
}
