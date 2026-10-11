//! Exact source transport, malformed inputs and paired hard-cap controls.
use axeyum_cas::{
    CasExpr, UnaryFunc,
    expression_wire::{WireError, from_json, to_json},
};
use axeyum_ir::Rational;
use num_bigint::BigInt;
use num_rational::BigRational;

#[test]
fn source_tags_and_wide_rationals_round_trip_without_normalization() {
    let pi = CasExpr::pi();
    let var = CasExpr::var("pi");
    assert_ne!(to_json(&pi).unwrap(), to_json(&var).unwrap());
    assert_eq!(
        to_json(&pi).unwrap(),
        r#"{"version":1,"expression":{"kind":"pi"}}"#
    );
    let r = Rational::from_big_rational(&BigRational::new(
        (BigInt::from(1) << 512) + 1,
        BigInt::from(7),
    ))
    .unwrap();
    let expr = CasExpr::Add(vec![
        pi,
        var,
        CasExpr::Const(r),
        CasExpr::Mul(vec![]),
        CasExpr::Add(vec![]),
        CasExpr::Neg(Box::new(CasExpr::var("\0constant:pi\"\\\nπ"))),
        CasExpr::Div(
            Box::new(CasExpr::int(1)),
            Box::new(CasExpr::Pow(Box::new(CasExpr::var("x")), u32::MAX)),
        ),
    ]);
    let bytes = to_json(&expr).unwrap();
    let rebuilt = from_json(&bytes).unwrap();
    assert_eq!(rebuilt, expr);
    assert_eq!(to_json(&rebuilt).unwrap(), bytes);
    assert!(bytes.contains("kind\":\"var"));
}

#[test]
fn every_unary_head_preserves_exact_identity_and_order() {
    use UnaryFunc::*;
    let heads = [
        Ln,
        Exp,
        Sin,
        Cos,
        Tan,
        Atan,
        Sqrt,
        Abs,
        Sign,
        Floor,
        Ceiling,
        Erf,
        Si,
        Ci,
        Ei,
        Li,
        Shi,
        Chi,
        FresnelS,
        FresnelC,
        BesselJ(0),
        BesselJ(u32::MAX),
        BesselI(13),
        Asin,
        Acos,
        Asinh,
        Acosh,
        Gamma,
        NthRoot(3),
        PolyGamma(0),
        PolyGamma(u32::MAX),
        Ai,
        AiPrime,
        Bi,
        BiPrime,
        LambertW,
    ];
    for head in heads {
        let e = CasExpr::Unary(head, Box::new(CasExpr::pi()));
        assert_eq!(from_json(&to_json(&e).unwrap()).unwrap(), e);
    }
}

#[test]
fn malformed_wire_and_noncanonical_rationals_reject() {
    for s in [
        r#"{"version":2,"expression":{"kind":"pi"}}"#,
        r#"{"version":1,"version":1,"expression":{"kind":"pi"}}"#,
        r#"{"version":1,"extra":true,"expression":{"kind":"pi"}}"#,
        r#"{"version":1,"expression":{"kind":"pi","args":"pi"}}"#,
        r#"{"version":1,"expression":{"kind":"euler"}}"#,
        r#"{"version":1,"expression":{"kind":"const","args":{"numerator":"1","numerator":"2","denominator":"1"}}}"#,
    ] {
        assert!(matches!(from_json(s), Err(WireError::Invalid(_))), "{s}");
    }
    for (n, d) in [
        ("1", "0"),
        ("1", "-2"),
        ("2", "4"),
        ("01", "1"),
        ("+1", "1"),
        ("-0", "1"),
        ("0", "2"),
    ] {
        let s = format!(
            r#"{{"version":1,"expression":{{"kind":"const","args":{{"numerator":"{n}","denominator":"{d}"}}}}}}"#
        );
        assert!(matches!(from_json(&s), Err(WireError::Invalid(_))), "{s}");
    }
    assert!(from_json(&(to_json(&CasExpr::pi()).unwrap() + " true")).is_err());
}

#[test]
fn hard_caps_have_positive_and_negative_controls() {
    let mut e = CasExpr::pi();
    for _ in 1..32 {
        e = CasExpr::Neg(Box::new(e));
    }
    let valid = to_json(&e).unwrap();
    assert_eq!(from_json(&valid).unwrap(), e);
    let deep_wire = valid.replacen(
        r#""expression":"#,
        r#""expression":{"kind":"neg","args":"#,
        1,
    ) + "}";
    assert!(matches!(
        from_json(&deep_wire),
        Err(WireError::ResourceLimit(_))
    ));
    e = CasExpr::Neg(Box::new(e));
    assert!(matches!(to_json(&e), Err(WireError::ResourceLimit(_))));
    for (n, good) in [(4095, true), (4096, false)] {
        let e = CasExpr::Add(vec![CasExpr::pi(); n]);
        assert_eq!(to_json(&e).is_ok(), good);
        let s = format!(
            r#"{{"version":1,"expression":{{"kind":"add","args":[{}]}}}}"#,
            vec![r#"{"kind":"pi"}"#; n].join(",")
        );
        assert_eq!(from_json(&s).is_ok(), good);
    }
    for (n, good) in [(1024, true), (1025, false)] {
        assert_eq!(to_json(&CasExpr::var(&"a".repeat(n))).is_ok(), good);
        let s = format!(
            r#"{{"version":1,"expression":{{"kind":"var","args":"{}"}}}}"#,
            "a".repeat(n)
        );
        assert_eq!(from_json(&s).is_ok(), good);
    }
    assert!(matches!(
        from_json(&" ".repeat(1_048_577)),
        Err(WireError::ResourceLimit(_))
    ));
    for (bits, good) in [(16384, true), (16385, false)] {
        let r =
            Rational::from_big_rational(&BigRational::from_integer(BigInt::from(1) << (bits - 1)))
                .unwrap();
        assert_eq!(to_json(&CasExpr::Const(r)).is_ok(), good);
        let n = r.numerator_big().to_string();
        let s = format!(
            r#"{{"version":1,"expression":{{"kind":"const","args":{{"numerator":"{n}","denominator":"1"}}}}}}"#
        );
        assert_eq!(from_json(&s).is_ok(), good);
    }
}
