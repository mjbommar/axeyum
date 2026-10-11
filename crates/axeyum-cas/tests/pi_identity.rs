//! Distinguished pi semantics, source binding, and regression controls.
use axeyum_cas::enclosure::{enclose, enclose_constant};
use axeyum_cas::{CasExpr, evalf, evaluate_trig, expand};
use axeyum_ir::Rational;
use std::collections::BTreeMap;

#[test]
fn constant_identity_is_independent_of_variable_bindings() {
    let pi = CasExpr::pi();
    let variable = CasExpr::var("pi");
    assert_ne!(pi, variable);
    assert_eq!(pi.differentiate("pi"), CasExpr::zero());
    assert_eq!(variable.differentiate("pi"), CasExpr::one());
    assert_eq!(pi.substitute("pi", &CasExpr::int(2)), pi);
    assert_eq!(variable.substitute("pi", &CasExpr::int(2)), CasExpr::int(2));
    assert_eq!(evalf(&pi, &[("pi", 2.0)]), Some(core::f64::consts::PI));
    assert_eq!(evalf(&variable, &[("pi", 2.0)]), Some(2.0));
    assert_eq!(evalf(&variable, &[]), None);
    let mut bindings = BTreeMap::new();
    bindings.insert("pi".to_owned(), Rational::integer(2));
    assert_eq!(pi.eval(&bindings), None);
    assert_eq!(variable.eval(&bindings), Some(Rational::integer(2)));
}

#[test]
fn exact_trig_never_reinterprets_a_variable_named_pi() {
    let constant = CasExpr::pi().sin();
    assert_eq!(evaluate_trig(&constant), CasExpr::zero());
    let variable = CasExpr::var("pi").sin();
    let result = evaluate_trig(&variable);
    assert_eq!(
        evalf(&result, &[("pi", 2.0)]),
        evalf(&variable, &[("pi", 2.0)])
    );
    assert!(evalf(&result, &[("pi", 2.0)]).unwrap() > 0.9);
    let nested = (CasExpr::int(2) * CasExpr::var("pi")).cos();
    assert_eq!(
        evalf(&evaluate_trig(&nested), &[("pi", 2.0)]),
        evalf(&nested, &[("pi", 2.0)])
    );
}

#[test]
fn algebraic_round_trip_preserves_the_constant_leaf() {
    let pi = CasExpr::pi();
    assert_eq!(
        expand(&(pi.clone() + pi.clone())),
        Some(CasExpr::int(2) * pi)
    );
}

#[test]
fn enclosure_is_bound_to_constant_or_variable_subject() {
    let pi = CasExpr::pi();
    let variable = CasExpr::var("pi");
    let certificate = enclose_constant("pi", 20).expect("constant enclosure");
    certificate.verify(&pi, &[]).expect("Pi evidence checks");
    assert!(certificate.verify(&variable, &[]).is_err());
    // Matching numeric intervals must not erase the source constant/variable tag.
    let same_interval = axeyum_cas::interval_arith::Interval::new(
        Rational::from_big_rational(certificate.interval.lo()).unwrap(),
        Rational::from_big_rational(certificate.interval.hi()).unwrap(),
    )
    .unwrap();
    assert!(
        certificate
            .verify(&variable, &[("pi", same_interval)])
            .is_err()
    );
    assert!(enclose(&variable, &[], 20).is_none());
    let bindings = [(
        "pi",
        axeyum_cas::interval_arith::Interval::new(Rational::integer(2), Rational::integer(2))
            .unwrap(),
    )];
    let rebound = enclose(&pi, &bindings, 20).expect("Pi ignores same-name variable binding");
    rebound
        .verify(&pi, &bindings)
        .expect("constant head stays bound to Pi");
    assert!(rebound.verify(&variable, &bindings).is_err());
    let bound_variable = enclose(&variable, &bindings, 20).expect("ordinary bound variable");
    bound_variable
        .verify(&variable, &bindings)
        .expect("variable head replay");
    assert!(bound_variable.verify(&pi, &bindings).is_err());
    let mut corrupted = certificate.clone();
    corrupted.evidence[0].head = axeyum_cas::enclosure::StepHead::Var("pi".to_owned());
    assert!(corrupted.verify(&pi, &[]).is_err());
}

#[test]
fn opaque_heads_and_reserved_keys_cannot_confuse_pi_with_a_variable() {
    use axeyum_cas::{ZeroTest, equal};
    let result = equal(&CasExpr::pi().sin(), &CasExpr::var("pi").sin());
    assert!(!matches!(
        result,
        ZeroTest::Certified { equal: true, .. } | ZeroTest::CertifiedBig { equal: true, .. }
    ));
    let forged = CasExpr::var("\0constant:pi");
    assert!(expand(&forged).is_none());
    let result = equal(&CasExpr::pi(), &forged);
    assert!(!matches!(
        result,
        ZeroTest::Certified { equal: true, .. } | ZeroTest::CertifiedBig { equal: true, .. }
    ));
}

#[test]
fn pi_inequality_requires_value_evidence_and_forged_witnesses_fail() {
    use axeyum_cas::{ZeroTest, equal, normalize, recheck_zero_test};
    let pi = CasExpr::pi();
    for (a, b) in [
        (pi.clone().pow(2), CasExpr::zero()),
        (pi.clone().pow(2), CasExpr::int(2)),
        (pi.clone().exp(), CasExpr::int(2)),
        (pi.clone().sin(), CasExpr::one()),
    ] {
        assert!(matches!(equal(&a, &b), ZeroTest::Unknown));
    }
    let forged = ZeroTest::Certified {
        equal: false,
        witness: normalize(&pi.clone().pow(2)).expect("formal polynomial exists"),
    };
    assert!(!recheck_zero_test(
        &pi.clone().pow(2),
        &CasExpr::zero(),
        &forged
    ));
    let left = pi.clone() + pi.clone();
    let right = CasExpr::int(2) * pi;
    let identity = equal(&left, &right);
    assert!(matches!(identity, ZeroTest::Certified { equal: true, .. }));
    assert!(recheck_zero_test(&left, &right, &identity));
    let left = CasExpr::var("pi").pow(2);
    let variable = equal(&left, &CasExpr::zero());
    assert!(matches!(variable, ZeroTest::Certified { equal: false, .. }));
    assert!(recheck_zero_test(&left, &CasExpr::zero(), &variable));
}

#[test]
fn raw_atom_names_cannot_forge_a_pi_expression_identity() {
    use axeyum_cas::{MultiPoly, ZeroTest, equal, recheck_zero_test};
    let constant = CasExpr::pi().exp();
    let forged_variable = CasExpr::var("\0exp:Pi");
    assert!(matches!(
        equal(&constant, &forged_variable),
        ZeroTest::Unknown
    ));
    let forged = ZeroTest::Certified {
        equal: true,
        witness: MultiPoly::zero(),
    };
    assert!(!recheck_zero_test(&constant, &forged_variable, &forged));
    let ordinary = CasExpr::var("pi").exp();
    let identity = equal(&ordinary, &ordinary);
    assert!(matches!(identity, ZeroTest::Certified { equal: true, .. }));
    assert!(recheck_zero_test(&ordinary, &ordinary, &identity));
}
