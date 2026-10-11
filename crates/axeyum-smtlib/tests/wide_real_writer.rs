//! Promoted rational constants retain exact SMT-LIB source identities.
use axeyum_ir::{Assignment, Op, Rational, Sort, TermArena, TermNode, Value, eval};
use axeyum_smtlib::{SmtError, parse_script, write_script};

#[test]
fn promoted_real_constants_serialize_without_narrowing() {
    let twice_max = Rational::integer(i128::MAX)
        .wide_mul(Rational::integer(2))
        .unwrap();
    let tiny = Rational::new(1, i128::MAX)
        .wide_mul(Rational::new(1, 2))
        .unwrap();
    for (value, expected) in [
        (twice_max, "340282366920938463463374607431768211454.0"),
        (
            twice_max.wide_neg().unwrap(),
            "(- 340282366920938463463374607431768211454.0)",
        ),
        (tiny, "(/ 1.0 340282366920938463463374607431768211454.0)"),
        (
            tiny.wide_neg().unwrap(),
            "(- (/ 1.0 340282366920938463463374607431768211454.0))",
        ),
    ] {
        let mut arena = TermArena::new();
        let symbol = arena.declare("x", Sort::Real).unwrap();
        let x = arena.var(symbol);
        let constant = arena.real_const(value);
        let assertion = arena.eq(x, constant).unwrap();
        let source = write_script(&arena, &[assertion]);
        assert!(source.contains(expected), "{source}");
        assert!(source.contains("(assert (= x "));
        let parsed = parse_script(&source).unwrap();
        assert_eq!(write_script(&parsed.arena, &parsed.assertions), source);
    }
}

#[test]
fn long_fractional_decimal_preserves_exact_value() {
    let literal = format!("0.{}1", "0".repeat(200));
    let script = parse_script(&format!(
        "(declare-const x Real)(assert (= x {literal}))(check-sat)"
    ))
    .unwrap();
    let expected = Rational::from_big_rational(&num_rational::BigRational::new(
        num_bigint::BigInt::from(1),
        num_bigint::BigInt::from(10).pow(201),
    ))
    .unwrap();
    assert!((0..script.arena.len()).any(|index| {
        matches!(script.arena.node(script.arena.term_by_index(index).unwrap()), TermNode::RealConst(value) if *value == expected)
    }));
    let rendered = write_script(&script.arena, &script.assertions);
    let reparsed = parse_script(&rendered).unwrap();
    assert_eq!(
        write_script(&reparsed.arena, &reparsed.assertions),
        rendered
    );
}

#[test]
fn wide_constant_floor_and_integer_predicate_are_exact() {
    let big = "340282366920938463463374607431768211454";
    for formula in [
        format!("(= (to_int {big}.5) {big})"),
        format!("(is_int {big}.0)"),
        format!("(not (is_int {big}.5))"),
        format!("(= (to_int (- {big}.5)) (- 340282366920938463463374607431768211455))"),
        format!("(= (to_int (- 0.{}1)) (- 1))", "0".repeat(200)),
    ] {
        let script = parse_script(&format!("(assert {formula})(check-sat)")).unwrap();
        assert_eq!(
            eval(&script.arena, script.assertions[0], &Assignment::new()).unwrap(),
            Value::Bool(true),
            "{formula}"
        );
    }
}

#[test]
fn decimal_resource_limit_is_distinct_from_malformed_syntax() {
    let oversized = format!("(assert (= {}.0 0.0))", "9".repeat(4096));
    assert!(matches!(
        parse_script(&oversized),
        Err(SmtError::ResourceLimit(_))
    ));
    for bad in ["1.2.3", "1.a", ".", "-1.5"] {
        let result = parse_script(&format!("(assert (= {bad} 0.0))"));
        assert!(
            result.is_err() && !matches!(result, Err(SmtError::ResourceLimit(_))),
            "{bad}"
        );
    }
    let boundary = format!(
        "(declare-const x Real)(assert (= x {}.0))",
        "9".repeat(4095)
    );
    assert!(parse_script(&boundary).is_ok());
}

#[test]
fn promoted_real_fp_rounder_declines_without_panicking() {
    let value = Rational::integer(i128::MAX)
        .wide_mul(Rational::integer(2))
        .unwrap();
    let mut arena = TermArena::new();
    assert!(
        axeyum_fp::from_real(
            &mut arena,
            axeyum_fp::FloatFormat {
                exp_bits: 8,
                sig_bits: 24
            },
            axeyum_fp::RoundingMode::NearestEven,
            value
        )
        .unwrap()
        .is_none()
    );
    let source =
        "(assert (= ((_ to_fp 8 24) RNE 340282366920938463463374607431768211454.0) (_ +oo 8 24)))";
    assert!(matches!(
        parse_script(source),
        Err(SmtError::Unsupported(_))
    ));
}

#[test]
fn wide_zero_divisor_remains_a_symbolic_total_operation() {
    let source = "(declare-const x Real)(assert (= x (/ 340282366920938463463374607431768211454.0 0.0)))(check-sat)";
    let script = parse_script(source).unwrap();
    assert!((0..script.arena.len()).any(|index| {
        matches!(
            script
                .arena
                .node(script.arena.term_by_index(index).unwrap()),
            TermNode::App {
                op: Op::RealDiv,
                ..
            }
        )
    }));
    let rendered = write_script(&script.arena, &script.assertions);
    let parsed = parse_script(&rendered).unwrap();
    assert_eq!(write_script(&parsed.arena, &parsed.assertions), rendered);
}
