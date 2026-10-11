//! Constructor, exact arithmetic, syntax and bounded-intake parser controls.
use axeyum_cas::{CasExpr, UnaryFunc, expression_wire, text_parser::parse};

#[test]
fn precedence_and_signed_powers_preserve_constructor_syntax() {
    let x = CasExpr::var("x");
    assert_eq!(
        parse("-x^2").unwrap(),
        CasExpr::Neg(Box::new(CasExpr::pow(x.clone(), 2)))
    );
    assert_eq!(
        parse("(-x)^2").unwrap(),
        CasExpr::pow(CasExpr::Neg(Box::new(x.clone())), 2)
    );
    assert_eq!(
        parse("x ** -360").unwrap(),
        x.clone().pow_signed(-360).unwrap()
    );
    assert_eq!(
        parse("x/2/3").unwrap(),
        CasExpr::Div(
            Box::new(CasExpr::Div(Box::new(x), Box::new(CasExpr::int(2)))),
            Box::new(CasExpr::int(3))
        )
    );
    assert_eq!(
        parse("1+2*3").unwrap(),
        CasExpr::Add(vec![
            CasExpr::int(1),
            CasExpr::Mul(vec![CasExpr::int(2), CasExpr::int(3)])
        ])
    );
}

#[test]
fn exact_literals_and_pi_round_trip_through_canonical_wire() {
    assert_eq!(parse("0.125").unwrap(), CasExpr::rat(1, 8));
    assert_eq!(parse("00012.5000").unwrap(), CasExpr::rat(25, 2));
    assert_eq!(parse("pi").unwrap(), CasExpr::Pi);
    assert_eq!(parse("π").unwrap(), CasExpr::Pi);
    assert_ne!(parse("pi").unwrap(), CasExpr::var("pi"));
    let wide = parse("1606938044258990275541962092341162602522202993782792835301376").unwrap();
    assert!(matches!(wide, CasExpr::Const(value) if value.numerator_big().bits() == 201));
    for text in ["π+sin(x)", "1.25/(x^-2)", "x^-2", "cbrt(8)"] {
        let expr = parse(text).unwrap_or_else(|e| panic!("{text}: {e}"));
        let encoded = expression_wire::to_json(&expr).unwrap();
        assert_eq!(expression_wire::from_json(&encoded).unwrap(), expr);
    }
}

#[test]
fn unary_calls_agree_with_supported_heads() {
    for (name, head) in [
        ("sin", UnaryFunc::Sin),
        ("cos", UnaryFunc::Cos),
        ("tan", UnaryFunc::Tan),
        ("atan", UnaryFunc::Atan),
        ("ln", UnaryFunc::Ln),
        ("exp", UnaryFunc::Exp),
        ("sqrt", UnaryFunc::Sqrt),
        ("cbrt", UnaryFunc::NthRoot(3)),
        ("abs", UnaryFunc::Abs),
        ("sign", UnaryFunc::Sign),
        ("floor", UnaryFunc::Floor),
        ("ceiling", UnaryFunc::Ceiling),
    ] {
        assert_eq!(
            parse(&format!("{name}(x)")).unwrap(),
            CasExpr::Unary(head, Box::new(CasExpr::var("x")))
        );
    }
}

#[test]
fn malformed_inputs_and_utf8_error_spans_are_explicit() {
    for text in [
        "",
        " ",
        "x+",
        "(x",
        "x)",
        "foo(x)",
        "x^y",
        "x^1.5",
        "x^2^3",
        "x^4294967296",
        "x^-4294967296",
        "x**--2",
        "1e3",
        "1.",
        ".5",
        "x,y",
        "x[0]",
        "π(x)",
    ] {
        assert!(parse(text).is_err(), "accepted {text}");
    }
    let e = parse("π + 💥").unwrap_err();
    assert_eq!((e.start, e.end), (5, 9));
    assert_eq!(e.message, "unexpected character");
    assert!(parse("x^4294967295").is_ok());
    assert!(parse("x^-4294967295").is_ok());
}

#[test]
fn all_shape_and_intake_caps_have_negative_controls() {
    assert!(parse(&" ".repeat(8192)).is_err()); // empty syntax at admitted byte limit
    assert!(
        parse(&" ".repeat(8193))
            .unwrap_err()
            .message
            .contains("source")
    );
    assert!(parse(&"1".repeat(1024)).is_ok());
    assert!(
        parse(&"1".repeat(1025))
            .unwrap_err()
            .message
            .contains("digit")
    );
    assert!(parse(&format!("{}x{}", "(".repeat(32), ")".repeat(32))).is_ok());
    assert!(
        parse(&format!("{}x{}", "(".repeat(33), ")".repeat(33)))
            .unwrap_err()
            .message
            .contains("depth")
    );
    assert!(parse(&vec!["x"; 32].join("+")).is_ok());
    assert!(
        parse(&vec!["x"; 33].join("+"))
            .unwrap_err()
            .message
            .contains("node")
    );
    assert!(
        parse(&vec!["x"; 257].join("+"))
            .unwrap_err()
            .message
            .contains("token")
    );
    // Subtraction lowers to Add+Neg, so actual AST capacity matters too.
    assert!(parse(&vec!["x"; 22].join("-")).is_ok());
    assert!(
        parse(&vec!["x"; 23].join("-"))
            .unwrap_err()
            .message
            .contains("shape")
    );
}

#[test]
fn native_grammar_matches_independent_python_parser_fixtures() {
    let corpus: serde_json::Value =
        serde_json::from_str(include_str!("data/python_text_parser.json")).unwrap();
    let rows = corpus["cases"].as_array().unwrap();
    assert_eq!(rows.len(), 37);
    let mut accepted = 0;
    let mut rejected = 0;
    for row in rows {
        let source = row["source"].as_str().unwrap();
        if let Some(expected) = row.get("expression") {
            let parsed = parse(source).unwrap_or_else(|e| panic!("{source}: {e}"));
            let actual: serde_json::Value =
                serde_json::from_str(&expression_wire::to_json(&parsed).unwrap()).unwrap();
            assert_eq!(
                &actual, expected,
                "structural grammar mismatch for {source}"
            );
            accepted += 1;
        } else {
            assert!(
                parse(source).is_err(),
                "native accepted rejected input {source}"
            );
            rejected += 1;
        }
    }
    assert!(accepted > 20 && rejected > 10);
}
