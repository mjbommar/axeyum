//! Constant rules must prove their stated truth value, not an arbitrary atom.
use axeyum_cnf::{check_alethe, parse_alethe};

#[test]
fn checked_constant_rules_close_genuine_contradictions() {
    for text in [
        "(assume h false) (step pin (cl (not false)) :rule false) (step end (cl) :rule resolution :premises (h pin))",
        "(assume h (not true)) (step pin (cl true) :rule true) (step end (cl) :rule resolution :premises (h pin))",
    ] {
        assert_eq!(check_alethe(&parse_alethe(text).unwrap()), Ok(true));
    }
}

#[test]
fn a_forged_false_pin_cannot_refute_a_true_assumption() {
    let proof = parse_alethe("(assume h true) (step pin (cl (not true)) :rule false) (step end (cl) :rule resolution :premises (h pin))").unwrap();
    assert!(check_alethe(&proof).is_err());
}

#[test]
fn a_forged_true_pin_cannot_refute_a_satisfiable_assumption() {
    let proof = parse_alethe("(assume h (not p)) (step pin (cl p) :rule true) (step end (cl) :rule resolution :premises (h pin))").unwrap();
    assert!(check_alethe(&proof).is_err());
}

#[test]
fn quoted_symbols_keep_spaces_delimiters_and_comments_inside_the_atom() {
    for name in ["|a b|", "|a(b)|", "|a;b|", "|true|"] {
        let text = format!(
            "(assume p {name}) (assume n (not {name})) (step end (cl) :rule resolution :premises (p n))"
        );
        assert_eq!(check_alethe(&parse_alethe(&text).unwrap()), Ok(true));
    }
    assert!(parse_alethe("(assume h |unterminated)").is_err());
    assert!(parse_alethe("(assume h |a\\b|)").is_err());
}
