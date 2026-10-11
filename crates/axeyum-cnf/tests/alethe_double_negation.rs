//! The narrow arithmetic normalization rule must retain the cancelled operand.
use axeyum_cnf::{check_alethe, parse_alethe};

#[test]
fn double_negation_identity_checks_without_proving_unsat() {
    for text in [
        "(step eq (cl (= (- (- x)) x)) :rule minus_simplify)",
        "(step eq (cl (= x (- (- x)))) :rule minus_simplify)",
    ] {
        assert_eq!(check_alethe(&parse_alethe(text).unwrap()), Ok(false));
    }
}

#[test]
fn double_negation_cannot_change_the_operand() {
    let proof = parse_alethe("(step eq (cl (= (- (- x)) y)) :rule minus_simplify)").unwrap();
    assert!(check_alethe(&proof).is_err());
}
