//! Public parser contracts for signed integer convenience atoms (ADR-2400).
use axeyum_ir::{Assignment, Value, eval};
use axeyum_smtlib::{parse_script, write_script};

fn true_assertion(term: &str) {
    let script = parse_script(&format!("(assert {term}) (check-sat)")).unwrap();
    assert_eq!(
        eval(&script.arena, script.assertions[0], &Assignment::default()).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn signed_atoms_have_exact_integer_values() {
    for literal in [
        "-1",
        "-0",
        "-0001",
        "-170141183460469231731687303715884105728",
        "-170141183460469231731687303715884105729",
        "-999999999999999999999999999999999999999999999999999999999999",
    ] {
        let magnitude = literal.trim_start_matches('-');
        true_assertion(&format!("(= {literal} (- {magnitude}))"));
        let script = parse_script(&format!("(assert (= {literal} (- {magnitude})))")).unwrap();
        let exported = write_script(&script.arena, &script.assertions);
        let roundtrip = parse_script(&exported).unwrap();
        assert_eq!(
            eval(
                &roundtrip.arena,
                roundtrip.assertions[0],
                &Assignment::default()
            )
            .unwrap(),
            Value::Bool(true)
        );
        let symbolic =
            parse_script(&format!("(declare-const x Int) (assert (= x {literal}))")).unwrap();
        let symbolic_output = write_script(&symbolic.arena, &symbolic.assertions);
        if literal == "-1" {
            assert!(symbolic_output.contains("(- 1)"));
        }
        assert!(parse_script(&symbolic_output).is_ok());
    }
}

#[test]
fn signed_atoms_flow_through_coercion_let_and_macros() {
    true_assertion("(= (+ -1 2.0) 1.0)");
    true_assertion("(let ((x -1)) (= (abs x) 1))");
    true_assertion("(not (distinct (abs -1) 1))");
    let script =
        parse_script("(define-fun f ((x Int)) Int (+ x -1)) (assert (= (f 2) 1))").unwrap();
    assert_eq!(
        eval(&script.arena, script.assertions[0], &Assignment::default()).unwrap(),
        Value::Bool(true)
    );
}

#[test]
fn quoted_signed_numeric_symbols_are_not_literals() {
    assert!(parse_script("(assert (= |-1| -1))").is_err());
    let script =
        parse_script("(declare-const |-1| Bool) (assert |-1|) (assert (= -1 (- 1)))").unwrap();
    assert_eq!(script.assertions.len(), 2);
    assert!(script.arena.find_symbol("|-1|").is_some());
    let output = write_script(&script.arena, &script.assertions);
    assert!(parse_script(&output).is_ok());
}

#[test]
fn declared_simple_signed_symbols_keep_lookup_precedence() {
    let script = parse_script("(declare-const -1 Bool) (assert -1)").unwrap();
    assert_eq!(script.assertions.len(), 1);
    assert!(script.arena.find_symbol("-1").is_some());
}

#[test]
fn malformed_and_signed_decimal_atoms_are_declined() {
    for bad in ["--1", "-", "+1", "-1x", "-1.0", "-١"] {
        assert!(
            parse_script(&format!("(assert (= {bad} 0))")).is_err(),
            "unexpected acceptance: {bad}"
        );
    }
    true_assertion("(= (- 1.0) (+ -1 0.0))");
}
