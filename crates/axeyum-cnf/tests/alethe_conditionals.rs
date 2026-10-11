//! Conditional clausification validates the exact gate and operand polarities.
use axeyum_cnf::{check_alethe, parse_alethe};

const CLAUSES: &[(&str, &str)] = &[
    ("implies_pos", "(not (=> p q)) (not p) q"),
    ("implies_neg1", "(=> p q) p"),
    ("implies_neg2", "(=> p q) (not q)"),
    ("ite_pos1", "(not (ite p q r)) p r"),
    ("ite_pos2", "(not (ite p q r)) (not p) q"),
    ("ite_neg1", "(ite p q r) p (not r)"),
    ("ite_neg2", "(ite p q r) (not p) (not q)"),
];

#[test]
fn conditional_clausification_accepts_the_specified_rows() {
    for &(rule, clause) in CLAUSES {
        let text = format!("(step row (cl {clause}) :rule {rule})");
        // A checked tautology row is not a closed UNSAT refutation.
        assert_eq!(check_alethe(&parse_alethe(&text).unwrap()), Ok(false));
    }
}

#[test]
fn conditional_clausification_rejects_changed_operands() {
    for &(rule, clause) in CLAUSES {
        let text = format!("(step row (cl {clause}) :rule {rule})");
        let mut proof = parse_alethe(&text).unwrap();
        let mut wrong_polarity = proof.clone();
        let axeyum_cnf::AletheCommand::Step { clause, .. } = &mut wrong_polarity[0] else {
            panic!("expected one rule step");
        };
        clause.last_mut().unwrap().negated = !clause.last().unwrap().negated;
        assert!(check_alethe(&wrong_polarity).is_err());
        let axeyum_cnf::AletheCommand::Step { clause, .. } = &mut proof[0] else {
            panic!("expected one rule step");
        };
        clause.last_mut().unwrap().atom =
            axeyum_cnf::AletheTerm::Const("different_operand".to_owned());
        assert!(check_alethe(&proof).is_err());
    }
}
