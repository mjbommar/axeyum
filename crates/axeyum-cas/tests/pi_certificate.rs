//! Source-bound Pi enclosure bytes, tamper controls and transport caps.
use axeyum_cas::{
    CasExpr,
    expression_wire::WireError,
    pi_certificate::{PiEnclosureCertificate, enclose_pi},
};
use num_bigint::BigInt;
use num_rational::BigRational;
use serde_json::Value;

#[test]
fn exact_pi_bounds_round_trip_and_replay() {
    for precision in [0, 8, 16, 32, 64, 256] {
        let certificate = enclose_pi(precision).unwrap();
        let bytes = certificate.to_json().unwrap();
        let replay = PiEnclosureCertificate::from_json(&bytes).unwrap();
        assert_eq!(replay.to_json().unwrap(), bytes);
        let report = replay.check(&CasExpr::Pi);
        assert!(report.accepted);
        assert_eq!((report.examined, report.discharged), (1, 1));
        assert!(replay.lower().unwrap() > BigRational::from_integer(3.into()));
        assert!(replay.upper().unwrap() < BigRational::new(22.into(), 7.into()));
        assert!(
            replay.upper().unwrap() - replay.lower().unwrap()
                <= BigRational::new(1.into(), BigInt::from(1) << precision)
        );
    }
}
#[test]
fn certificate_source_binding_cannot_be_substituted() {
    let c = enclose_pi(16).unwrap();
    assert!(!c.check(&CasExpr::var("pi")).accepted);
    let mut v: Value = serde_json::from_str(&c.to_json().unwrap()).unwrap();
    v["source_expression"] = axeyum_cas::expression_wire::to_json(&CasExpr::var("pi"))
        .unwrap()
        .into();
    let c = PiEnclosureCertificate::from_json(&v.to_string()).unwrap();
    let report = c.check(&CasExpr::Pi);
    assert!(!report.accepted);
    assert_eq!(report.discharged, 0);
    assert!(report.reason.unwrap().contains("source"));
}
#[test]
fn numerical_and_order_tampering_fails_replay() {
    let c = enclose_pi(16).unwrap();
    let original: Value = serde_json::from_str(&c.to_json().unwrap()).unwrap();
    for field in ["lower", "upper", "remainder"] {
        let mut v = original.clone();
        v[field] = serde_json::json!({"numerator": if field == "remainder" { "0" } else { "4" },"denominator":"1"});
        match PiEnclosureCertificate::from_json(&v.to_string()) {
            Ok(c) => assert!(!c.check(&CasExpr::Pi).accepted, "{field}"),
            Err(WireError::Invalid(_)) => (),
            Err(e) => panic!("unexpected {e}"),
        }
    }
    let mut v = original.clone();
    v["order"] = 0.into();
    assert!(
        !PiEnclosureCertificate::from_json(&v.to_string())
            .unwrap()
            .check(&CasExpr::Pi)
            .accepted
    );
    let mut v = original;
    v["precision"] = 32.into();
    assert!(
        !PiEnclosureCertificate::from_json(&v.to_string())
            .unwrap()
            .check(&CasExpr::Pi)
            .accepted
    );
}
#[test]
fn malformed_and_oversized_certificates_decline() {
    assert!(matches!(enclose_pi(257), Err(WireError::ResourceLimit(_))));
    assert!(matches!(
        PiEnclosureCertificate::from_json(&" ".repeat(65537)),
        Err(WireError::ResourceLimit(_))
    ));
    let bytes = enclose_pi(16).unwrap().to_json().unwrap();
    assert!(
        PiEnclosureCertificate::from_json(
            &bytes.replace("\"version\":1", "\"version\":1,\"version\":1")
        )
        .is_err()
    );
    for (field, value) in [
        ("version", serde_json::json!(2)),
        ("order", serde_json::json!(129)),
        ("precision", serde_json::json!(257)),
        ("extra", serde_json::json!(true)),
        (
            "lower",
            serde_json::json!({"numerator":"2","denominator":"4"}),
        ),
        (
            "upper",
            serde_json::json!({"numerator":"1","denominator":"0"}),
        ),
    ] {
        let mut v: Value = serde_json::from_str(&bytes).unwrap();
        v[field] = value;
        assert!(
            PiEnclosureCertificate::from_json(&v.to_string()).is_err(),
            "{field}"
        );
    }
}
