//! Checked congruence-then-arithmetic refutations for mixed-sort `QF_UFLIA`.
//!
//! This certificate covers rows like cvc5 `bug303`: congruence over an
//! uninterpreted carrier sort first derives an equality between integer-valued
//! applications, and the resulting Boolean-structured linear-arithmetic residual
//! is unsatisfiable. The checker re-runs the Ackermann/congruence construction,
//! keeps only linear-arithmetic residual formulas plus arithmetic-sorted
//! congruence consequents, and verifies that residual with the existing
//! arithmetic-DPLL certificate.

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};

use crate::backend::SolverConfig;
use crate::dpll_lia::{ArithDpllOutcome, certify_arith_dpll_unsat};
use crate::qfufbv_alethe::build_ackermann_congruence;

/// A self-checking mixed UF+arithmetic refutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UfArithCongruenceCertificate {
    /// Number of rewritten original assertions retained in the arithmetic
    /// residual.
    pub arithmetic_assertions: usize,
    /// Number of derived arithmetic-sorted congruence consequents retained in
    /// the arithmetic residual.
    pub congruence_consequents: usize,
}

/// Returns a certificate when an Ackermannized mixed-sort UF problem has a
/// Boolean-structured linear-arithmetic residual refuted by checked arithmetic
/// DPLL, using at least one derived congruence consequent.
#[must_use]
pub fn uf_arith_congruence_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<UfArithCongruenceCertificate> {
    let mut scratch = arena.clone();
    let congruence = build_ackermann_congruence(&mut scratch, assertions)?;

    let mut residual = Vec::new();
    let mut arithmetic_assertions = 0usize;
    for &assertion in congruence.rewritten_assertions() {
        if is_bool_linear_arithmetic_formula(&scratch, assertion) {
            residual.push(assertion);
            arithmetic_assertions += 1;
        }
    }

    let mut congruence_consequents = 0usize;
    for consequent in congruence.consequent_assertions() {
        if is_bool_linear_arithmetic_formula(&scratch, consequent) {
            residual.push(consequent);
            congruence_consequents += 1;
        }
    }

    if arithmetic_assertions == 0 || congruence_consequents == 0 {
        return None;
    }

    match certify_arith_dpll_unsat(&mut scratch, &residual, &SolverConfig::default()).ok()? {
        ArithDpllOutcome::Unsat(refutation) if refutation.verify(&scratch).ok()? => {
            Some(UfArithCongruenceCertificate {
                arithmetic_assertions,
                congruence_consequents,
            })
        }
        _ => None,
    }
}

fn is_bool_linear_arithmetic_formula(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::BoolConst(_) => true,
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => is_bool_linear_arithmetic_formula(arena, args[0]),
        TermNode::App {
            op: Op::BoolAnd | Op::BoolOr | Op::BoolXor | Op::BoolImplies,
            args,
        } => args
            .iter()
            .copied()
            .all(|arg| is_bool_linear_arithmetic_formula(arena, arg)),
        TermNode::App { op: Op::Ite, args } if args.len() == 3 => {
            arena.sort_of(args[1]) == Sort::Bool
                && arena.sort_of(args[2]) == Sort::Bool
                && args
                    .iter()
                    .copied()
                    .all(|arg| is_bool_linear_arithmetic_formula(arena, arg))
        }
        _ => is_linear_arithmetic_atom(arena, term),
    }
}

fn is_linear_arithmetic_atom(arena: &TermArena, term: TermId) -> bool {
    let TermNode::App { op, args } = arena.node(term) else {
        return false;
    };
    if args.len() != 2 {
        return false;
    }
    match op {
        Op::Eq => match (arena.sort_of(args[0]), arena.sort_of(args[1])) {
            (Sort::Int, Sort::Int) => {
                crate::alethe_lra::int_atom_to_alethe_pub(arena, term).is_some()
            }
            (Sort::Real, Sort::Real) => {
                crate::alethe_lra::real_atom_to_alethe_pub(arena, term).is_some()
            }
            _ => false,
        },
        Op::IntLe | Op::IntLt | Op::IntGe | Op::IntGt => {
            crate::alethe_lra::int_atom_to_alethe_pub(arena, term).is_some()
        }
        Op::RealLe | Op::RealLt | Op::RealGe | Op::RealGt => {
            crate::alethe_lra::real_atom_to_alethe_pub(arena, term).is_some()
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use axeyum_smtlib::parse_script;

    use super::uf_arith_congruence_refutation;

    #[test]
    fn recognizes_cvc5_bug303() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__bug303.smt2"
        ))
        .expect("parse bug303");
        let cert = uf_arith_congruence_refutation(&script.arena, &script.assertions)
            .expect("bug303 is congruence-then-arithmetic unsat");
        assert_eq!(cert.arithmetic_assertions, 3);
        assert_eq!(cert.congruence_consequents, 1);
    }

    #[test]
    fn rejects_pure_arithmetic() {
        let script = parse_script(
            r"
            (set-logic QF_LIA)
            (declare-const x Int)
            (assert (= x 0))
            (assert (not (= x 0)))
            (check-sat)
        ",
        )
        .expect("parse pure arithmetic");
        assert!(uf_arith_congruence_refutation(&script.arena, &script.assertions).is_none());
    }

    #[test]
    fn rejects_satisfiable_mixed_uf_arithmetic() {
        let script = parse_script(
            r"
            (set-logic QF_UFLIA)
            (declare-sort A 0)
            (declare-fun a () A)
            (declare-fun b () A)
            (declare-fun f (A) Int)
            (assert (= (f a) 0))
            (assert (= (f b) 1))
            (check-sat)
        ",
        )
        .expect("parse satisfiable mixed UF arithmetic");
        assert!(uf_arith_congruence_refutation(&script.arena, &script.assertions).is_none());
    }
}
