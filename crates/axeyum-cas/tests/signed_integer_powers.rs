//! Signed-power convenience must preserve existing rational domains.
use axeyum_cas::{CasExpr, ZeroTest, equal, recheck_zero_test};
use axeyum_ir::Rational;
use std::collections::BTreeMap;

#[test]
fn negative_powers_are_explicit_reciprocal_nodes() {
    let expression = CasExpr::var("x").pow_signed(-3).unwrap();
    let CasExpr::Div(numerator, denominator) = expression else {
        panic!("expected quotient")
    };
    assert_eq!(*numerator, CasExpr::one());
    assert_eq!(*denominator, CasExpr::Pow(Box::new(CasExpr::var("x")), 3));
    assert_eq!(
        CasExpr::var("x").pow_signed(3).unwrap(),
        CasExpr::var("x").pow(3)
    );
}

#[test]
fn nonzero_rational_powers_have_recheckable_identity_witnesses() {
    for (base, exponent, expected) in [
        (Rational::integer(2), -3, Rational::new(1, 8)),
        (Rational::integer(-2), -3, Rational::new(-1, 8)),
        (Rational::new(2, 3), -3, Rational::new(27, 8)),
        (Rational::new(-2, 3), -2, Rational::new(9, 4)),
    ] {
        let expression = CasExpr::Const(base).pow_signed(exponent).unwrap();
        assert_eq!(expression.eval(&BTreeMap::new()), Some(expected));
        let result = CasExpr::Const(expected);
        let certificate = equal(&expression, &result);
        assert!(matches!(
            certificate,
            ZeroTest::Certified { equal: true, .. } | ZeroTest::CertifiedBig { equal: true, .. }
        ));
        assert!(recheck_zero_test(&expression, &result, &certificate));
        assert!(!recheck_zero_test(
            &expression,
            &CasExpr::zero(),
            &certificate
        ));
    }
}

#[test]
fn zero_and_missing_bases_do_not_acquire_reciprocal_values() {
    let zero = CasExpr::zero().pow_signed(-1).unwrap();
    assert_eq!(zero.eval(&BTreeMap::new()), None);
    assert!(matches!(equal(&zero, &CasExpr::zero()), ZeroTest::Unknown));
    assert_eq!(
        CasExpr::zero()
            .pow_signed(0)
            .unwrap()
            .eval(&BTreeMap::new()),
        Some(Rational::integer(1))
    );
    let undefined = CasExpr::Div(Box::new(CasExpr::one()), Box::new(CasExpr::zero()));
    assert_eq!(
        undefined.pow_signed(0).unwrap().eval(&BTreeMap::new()),
        None
    );
    let inverse = CasExpr::var("x").pow_signed(-1).unwrap();
    assert_eq!(inverse.eval(&BTreeMap::new()), None);
    assert_eq!(
        inverse.eval(&BTreeMap::from([("x".to_owned(), Rational::zero())])),
        None
    );
    assert_eq!(
        inverse.eval(&BTreeMap::from([("x".to_owned(), Rational::integer(2))])),
        Some(Rational::new(1, 2))
    );
}

#[test]
fn signed_exponent_boundaries_decline_without_overflow() {
    let maximum = i64::from(u32::MAX);
    assert!(CasExpr::one().pow_signed(maximum).is_some());
    assert!(CasExpr::one().pow_signed(-maximum).is_some());
    for exponent in [maximum, -maximum] {
        assert_eq!(
            CasExpr::one()
                .pow_signed(exponent)
                .unwrap()
                .eval(&BTreeMap::new()),
            Some(Rational::integer(1))
        );
    }
    assert_eq!(
        CasExpr::int(-1)
            .pow_signed(-maximum)
            .unwrap()
            .eval(&BTreeMap::new()),
        Some(Rational::integer(-1))
    );
    assert_eq!(
        CasExpr::int(2)
            .pow_signed(maximum)
            .unwrap()
            .eval(&BTreeMap::new()),
        None
    );
    assert_eq!(
        CasExpr::int(i128::MIN)
            .pow_signed(1)
            .unwrap()
            .eval(&BTreeMap::new()),
        Some(Rational::integer(i128::MIN))
    );
    for exponent in [maximum + 1, -maximum - 1, i64::MIN, i64::MAX] {
        assert!(CasExpr::one().pow_signed(exponent).is_none());
    }
}
