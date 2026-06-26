//! Checked Boolean-structured EUF refutations.
//!
//! This is a small proof bridge for `QF_UF` rows whose contradiction is hidden by
//! propositional structure (`not =>`, CNF, Boolean `ite`) rather than present as a
//! top-level conjunction of equality/disequality atoms. The checker abstracts
//! each EUF equality atom to a Boolean, enumerates every satisfying Boolean
//! skeleton assignment, and requires the corresponding equality/disequality
//! conjunction to be refuted by the existing congruence checker. Any accepted
//! certificate is therefore a bounded DPLL(T)-style proof checked from the
//! original assertions.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};

use crate::backend::CheckResult;

const MAX_ATOMS: usize = 16;

/// A self-checking refutation of a Boolean-structured pure-EUF formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoolEufExhaustiveCertificate {
    /// Equality atoms in deterministic term-id order.
    pub atoms: Vec<TermId>,
    /// Number of satisfying Boolean skeleton assignments checked and refuted by
    /// congruence. `0` means the equality-atom skeleton is already
    /// propositionally inconsistent.
    pub cases: u64,
}

/// A self-checking refutation of a larger Boolean-structured pure-EUF formula.
///
/// The checker re-runs the online EUF DPLL(T) refuter over the original
/// assertions and accepts only if it deterministically returns `unsat`. This is
/// wider than [`BoolEufExhaustiveCertificate`]: it avoids enumerating every
/// equality-atom assignment, while still rejecting anything outside the pure-EUF
/// Boolean skeleton the online checker can encode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoolEufOnlineCertificate {
    /// Equality atoms collected from the original Boolean skeleton.
    pub atoms: usize,
}

/// Returns a certificate when every satisfying Boolean assignment to the EUF
/// equality atoms is itself refuted by congruence closure.
#[must_use]
pub fn bool_euf_exhaustive_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BoolEufExhaustiveCertificate> {
    if assertions.is_empty() {
        return None;
    }
    let mut atoms = BTreeSet::new();
    for &assertion in assertions {
        collect_bool_euf_atoms(arena, assertion, &mut atoms)?;
    }
    if atoms.is_empty() || atoms.len() > MAX_ATOMS {
        return None;
    }
    let atoms: Vec<_> = atoms.into_iter().collect();
    let total = 1_u64.checked_shl(u32::try_from(atoms.len()).ok()?)?;
    let mut cases = 0_u64;
    for case in 0..total {
        let assignment = decode_assignment(&atoms, case);
        if assertions
            .iter()
            .copied()
            .map(|assertion| eval_bool_skeleton(arena, assertion, &assignment))
            .collect::<Option<Vec<_>>>()?
            .into_iter()
            .all(|value| value)
        {
            cases = cases.checked_add(1)?;
            if !assignment_refuted_by_congruence(arena, &atoms, &assignment)? {
                return None;
            }
        }
    }
    Some(BoolEufExhaustiveCertificate { atoms, cases })
}

/// Returns a certificate when the online EUF DPLL(T) checker refutes the
/// Boolean-structured pure-EUF formula.
#[must_use]
pub fn bool_euf_online_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BoolEufOnlineCertificate> {
    if assertions.is_empty() {
        return None;
    }
    let mut atoms = BTreeSet::new();
    for &assertion in assertions {
        collect_bool_euf_atoms(arena, assertion, &mut atoms)?;
    }
    if atoms.is_empty() {
        return None;
    }
    let mut scratch = arena.clone();
    match crate::euf_egraph::solve_qf_uf_online(&mut scratch, assertions) {
        CheckResult::Unsat => Some(BoolEufOnlineCertificate { atoms: atoms.len() }),
        CheckResult::Sat(_) | CheckResult::Unknown(_) => None,
    }
}

fn collect_bool_euf_atoms(
    arena: &TermArena,
    term: TermId,
    atoms: &mut BTreeSet<TermId>,
) -> Option<()> {
    match arena.node(term) {
        TermNode::BoolConst(_) => Some(()),
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => collect_bool_euf_atoms(arena, args[0], atoms),
        TermNode::App {
            op: Op::BoolAnd | Op::BoolOr | Op::BoolXor | Op::BoolImplies,
            args,
        } => {
            for &arg in &**args {
                collect_bool_euf_atoms(arena, arg, atoms)?;
            }
            Some(())
        }
        TermNode::App { op: Op::Ite, args } if args.len() == 3 => {
            if arena.sort_of(args[1]) != Sort::Bool || arena.sort_of(args[2]) != Sort::Bool {
                return None;
            }
            collect_bool_euf_atoms(arena, args[0], atoms)?;
            collect_bool_euf_atoms(arena, args[1], atoms)?;
            collect_bool_euf_atoms(arena, args[2], atoms)
        }
        TermNode::App { op: Op::Eq, args } if args.len() == 2 => {
            if !is_pure_euf_value_term(arena, args[0]) || !is_pure_euf_value_term(arena, args[1]) {
                return None;
            }
            atoms.insert(term);
            Some(())
        }
        _ => None,
    }
}

fn is_pure_euf_value_term(arena: &TermArena, term: TermId) -> bool {
    match arena.sort_of(term) {
        Sort::Uninterpreted(_) => {}
        _ => return false,
    }
    match arena.node(term) {
        TermNode::Symbol(symbol) => matches!(arena.symbol(*symbol).1, Sort::Uninterpreted(_)),
        TermNode::App {
            op: Op::Apply(func),
            args,
        } => {
            let (_, params, result) = arena.function(*func);
            matches!(result, Sort::Uninterpreted(_))
                && params
                    .iter()
                    .all(|sort| matches!(sort, Sort::Uninterpreted(_)))
                && args
                    .iter()
                    .copied()
                    .all(|arg| is_pure_euf_value_term(arena, arg))
        }
        _ => false,
    }
}

fn decode_assignment(atoms: &[TermId], case: u64) -> BTreeMap<TermId, bool> {
    atoms
        .iter()
        .copied()
        .enumerate()
        .map(|(idx, atom)| (atom, ((case >> idx) & 1) != 0))
        .collect()
}

fn eval_bool_skeleton(
    arena: &TermArena,
    term: TermId,
    assignment: &BTreeMap<TermId, bool>,
) -> Option<bool> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(*value),
        TermNode::App { op: Op::Eq, .. } => assignment.get(&term).copied(),
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => Some(!eval_bool_skeleton(arena, args[0], assignment)?),
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } => {
            for &arg in &**args {
                if !eval_bool_skeleton(arena, arg, assignment)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        TermNode::App {
            op: Op::BoolOr,
            args,
        } => {
            for &arg in &**args {
                if eval_bool_skeleton(arena, arg, assignment)? {
                    return Some(true);
                }
            }
            Some(false)
        }
        TermNode::App {
            op: Op::BoolXor,
            args,
        } => {
            let mut odd = false;
            for &arg in &**args {
                odd ^= eval_bool_skeleton(arena, arg, assignment)?;
            }
            Some(odd)
        }
        TermNode::App {
            op: Op::BoolImplies,
            args,
        } if args.len() == 2 => {
            let lhs = eval_bool_skeleton(arena, args[0], assignment)?;
            let rhs = eval_bool_skeleton(arena, args[1], assignment)?;
            Some(!lhs || rhs)
        }
        TermNode::App { op: Op::Ite, args } if args.len() == 3 => {
            let cond = eval_bool_skeleton(arena, args[0], assignment)?;
            eval_bool_skeleton(arena, if cond { args[1] } else { args[2] }, assignment)
        }
        _ => None,
    }
}

fn assignment_refuted_by_congruence(
    arena: &TermArena,
    atoms: &[TermId],
    assignment: &BTreeMap<TermId, bool>,
) -> Option<bool> {
    let mut scratch = arena.clone();
    let mut core = Vec::with_capacity(atoms.len());
    for &atom in atoms {
        if assignment.get(&atom).copied()? {
            core.push(atom);
        } else {
            core.push(scratch.not(atom).ok()?);
        }
    }
    Some(crate::prove_unsat_by_congruence(&scratch, &core).is_some())
}

#[cfg(test)]
mod tests {
    use axeyum_smtlib::parse_script;

    use super::{MAX_ATOMS, bool_euf_exhaustive_refutation, bool_euf_online_refutation};

    #[test]
    fn recognizes_negated_implication_congruence() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__simple-uf.smt2"
        ))
        .expect("parse simple-uf");
        let cert = bool_euf_exhaustive_refutation(&script.arena, &script.assertions)
            .expect("simple-uf is Boolean-structured EUF unsat");
        assert_eq!(cert.atoms.len(), 2);
        assert_eq!(cert.cases, 1);
    }

    #[test]
    fn recognizes_cnf_disjunction_congruence() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__uf__cnf-and-neg.smt2"
        ))
        .expect("parse cnf-and-neg");
        let cert = bool_euf_exhaustive_refutation(&script.arena, &script.assertions)
            .expect("cnf-and-neg is Boolean-structured EUF unsat");
        assert_eq!(cert.atoms.len(), 4);
        assert_eq!(cert.cases, 3);
    }

    #[test]
    fn recognizes_ite_congruence() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__uf__cnf-ite.smt2"
        ))
        .expect("parse cnf-ite");
        let cert = bool_euf_exhaustive_refutation(&script.arena, &script.assertions)
            .expect("cnf-ite is Boolean-structured EUF unsat");
        assert!(cert.atoms.len() <= 16);
        assert_eq!(cert.cases, 0);
    }

    #[test]
    fn rejects_satisfiable_uf_disequality() {
        let script = parse_script(
            r"
            (set-logic QF_UF)
            (declare-sort A 0)
            (declare-fun x () A)
            (declare-fun y () A)
            (assert (not (= x y)))
            (check-sat)
        ",
        )
        .expect("parse satisfiable disequality");
        assert!(bool_euf_exhaustive_refutation(&script.arena, &script.assertions).is_none());
    }

    #[test]
    fn rejects_mixed_arithmetic_bug303_shape() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded/cli__regress0__bug303.smt2"
        ))
        .expect("parse bug303");
        assert!(bool_euf_exhaustive_refutation(&script.arena, &script.assertions).is_none());
    }

    #[test]
    fn online_refutes_overbound_cnf_abc() {
        let script = parse_script(include_str!(
            "../../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-overbound/cli__regress0__uf__cnf_abc.smt2"
        ))
        .expect("parse overbound cnf_abc");
        let cert = bool_euf_online_refutation(&script.arena, &script.assertions)
            .expect("online EUF refutes cnf_abc");
        assert!(cert.atoms > MAX_ATOMS);
    }
}
