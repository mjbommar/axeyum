//! Small checked Boolean-simplification refutations.
//!
//! This module recognizes assertions that normalize to Boolean `false` using a
//! deliberately tiny propositional simplifier: constants, double negation,
//! associative/idempotent `and`/`or`, and complement pairs (`p ∧ ¬p`, `p ∨ ¬p`).
//! Non-Boolean-theory structure is kept opaque, so every accepted certificate is
//! re-checkable by re-running the same normalizer over the original assertions.

use std::collections::BTreeSet;

use axeyum_ir::{Op, TermArena, TermId, TermNode};

/// A self-checking refutation: one original assertion simplifies to `false`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoolSimplificationRefutationCertificate {
    /// The original top-level assertion that normalizes to Boolean `false`.
    pub assertion: TermId,
}

/// Returns a certificate when any assertion is propositionally `false` under the
/// small checked Boolean normalizer.
#[must_use]
pub fn bool_simplification_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<BoolSimplificationRefutationCertificate> {
    assertions.iter().copied().find_map(|assertion| {
        matches!(simplify_bool(arena, assertion), BoolExpr::False)
            .then_some(BoolSimplificationRefutationCertificate { assertion })
    })
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum BoolExpr {
    False,
    True,
    Atom(TermId),
    Not(Box<BoolExpr>),
    And(Vec<BoolExpr>),
    Or(Vec<BoolExpr>),
}

fn simplify_bool(arena: &TermArena, term: TermId) -> BoolExpr {
    match arena.node(term) {
        TermNode::BoolConst(false) => BoolExpr::False,
        TermNode::BoolConst(true) => BoolExpr::True,
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => simplify_not(simplify_bool(arena, args[0])),
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } => simplify_nary(arena, true, args),
        TermNode::App {
            op: Op::BoolOr,
            args,
        } => simplify_nary(arena, false, args),
        _ => BoolExpr::Atom(term),
    }
}

fn simplify_not(expr: BoolExpr) -> BoolExpr {
    match expr {
        BoolExpr::False => BoolExpr::True,
        BoolExpr::True => BoolExpr::False,
        BoolExpr::Not(inner) => *inner,
        other => BoolExpr::Not(Box::new(other)),
    }
}

fn simplify_nary(arena: &TermArena, is_and: bool, args: &[TermId]) -> BoolExpr {
    let mut set = BTreeSet::new();
    for &arg in args {
        match simplify_bool(arena, arg) {
            BoolExpr::False if is_and => return BoolExpr::False,
            BoolExpr::True if !is_and => return BoolExpr::True,
            BoolExpr::True | BoolExpr::False => {}
            BoolExpr::And(items) if is_and => set.extend(items),
            BoolExpr::Or(items) if !is_and => set.extend(items),
            item => {
                set.insert(item);
            }
        }
    }

    for item in &set {
        if set.contains(&complement(item)) {
            return if is_and {
                BoolExpr::False
            } else {
                BoolExpr::True
            };
        }
    }

    let items: Vec<_> = set.into_iter().collect();
    match items.as_slice() {
        [] if is_and => BoolExpr::True,
        [] => BoolExpr::False,
        [single] => single.clone(),
        _ if is_and => BoolExpr::And(items),
        _ => BoolExpr::Or(items),
    }
}

fn complement(expr: &BoolExpr) -> BoolExpr {
    match expr {
        BoolExpr::Not(inner) => (**inner).clone(),
        other => BoolExpr::Not(Box::new(other.clone())),
    }
}

#[cfg(test)]
mod tests {
    use axeyum_ir::{Sort, TermArena};

    use super::bool_simplification_refutation;

    #[test]
    fn recognizes_negated_complement_tautology() {
        let mut arena = TermArena::new();
        let p_symbol = arena.declare("p", Sort::Bool).unwrap();
        let p = arena.var(p_symbol);
        let not_p = arena.not(p).unwrap();
        let tautology = arena.or(p, not_p).unwrap();
        let assertion = arena.not(tautology).unwrap();

        let cert = bool_simplification_refutation(&arena, &[assertion])
            .expect("not (p or not p) simplifies to false");
        assert_eq!(cert.assertion, assertion);
    }

    #[test]
    fn rejects_bare_tautology_assertion() {
        let mut arena = TermArena::new();
        let p_symbol = arena.declare("p", Sort::Bool).unwrap();
        let p = arena.var(p_symbol);
        let not_p = arena.not(p).unwrap();
        let tautology = arena.or(p, not_p).unwrap();

        assert!(bool_simplification_refutation(&arena, &[tautology]).is_none());
    }
}
