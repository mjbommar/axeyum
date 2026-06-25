//! Small checked term-identity refutations.
//!
//! This module recognizes asserted disequalities whose two sides are equal after
//! a tiny, local identity normalization. It is deliberately narrow and
//! re-checkable: callers use the certificate only after the matcher re-scans the
//! original assertions.

use axeyum_ir::{Op, TermArena, TermId, TermNode};

/// The checked identity class used by a term-identity refutation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TermIdentityKind {
    /// The asserted disequality is literally `not (= t t)`.
    Reflexive,
    /// The two sides coincide after constant-condition/equal-branch `ite`
    /// simplification.
    IteSimplification,
}

/// A self-checking refutation of `not (= lhs rhs)` where `lhs` and `rhs` are
/// identical under [`TermIdentityKind`]'s tiny identity normalizer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TermIdentityRefutationCertificate {
    /// The original top-level disequality assertion, or the conjunct containing
    /// it when the original assertion was a conjunction.
    pub assertion: TermId,
    /// The left side of the asserted equality inside the negation.
    pub lhs: TermId,
    /// The right side of the asserted equality inside the negation.
    pub rhs: TermId,
    /// Which identity class refutes the disequality.
    pub kind: TermIdentityKind,
}

/// Returns a certificate when any top-level conjunct is a disequality whose two
/// sides are equal by one of the checked term identities.
#[must_use]
pub fn term_identity_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<TermIdentityRefutationCertificate> {
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }

    for assertion in conjuncts {
        let Some((lhs, rhs)) = match_disequality(arena, assertion) else {
            continue;
        };
        let Some(kind) = term_identity_kind(arena, lhs, rhs) else {
            continue;
        };
        return Some(TermIdentityRefutationCertificate {
            assertion,
            lhs,
            rhs,
            kind,
        });
    }
    None
}

fn collect_top_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if args.len() == 2 => {
            collect_top_conjuncts(arena, args[0], out);
            collect_top_conjuncts(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

fn match_disequality(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(*inner) else {
        return None;
    };
    let [lhs, rhs] = &**args else {
        return None;
    };
    Some((*lhs, *rhs))
}

fn term_identity_kind(arena: &TermArena, lhs: TermId, rhs: TermId) -> Option<TermIdentityKind> {
    if lhs == rhs {
        return Some(TermIdentityKind::Reflexive);
    }
    let (lhs_norm, lhs_changed) = identity_normal_form(arena, lhs);
    let (rhs_norm, rhs_changed) = identity_normal_form(arena, rhs);
    (lhs_norm == rhs_norm && (lhs_changed || rhs_changed))
        .then_some(TermIdentityKind::IteSimplification)
}

fn identity_normal_form(arena: &TermArena, term: TermId) -> (TermId, bool) {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return (term, false);
    };
    let [condition, then_term, else_term] = &**args else {
        return (term, false);
    };
    match arena.node(*condition) {
        TermNode::BoolConst(true) => {
            let (norm, _) = identity_normal_form(arena, *then_term);
            (norm, true)
        }
        TermNode::BoolConst(false) => {
            let (norm, _) = identity_normal_form(arena, *else_term);
            (norm, true)
        }
        _ => {
            let (then_norm, then_changed) = identity_normal_form(arena, *then_term);
            let (else_norm, else_changed) = identity_normal_form(arena, *else_term);
            if then_norm == else_norm {
                (then_norm, true)
            } else {
                (term, then_changed || else_changed)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use axeyum_ir::{Sort, TermArena};

    use super::{TermIdentityKind, term_identity_refutation};

    #[test]
    fn recognizes_ite_true_identity_disequality() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let y = arena.real_var("y").unwrap();
        let true_ = arena.bool_const(true);
        let ite = arena.ite(true_, x, y).unwrap();
        let eq = arena.eq(x, ite).unwrap();
        let diseq = arena.not(eq).unwrap();

        let cert = term_identity_refutation(&arena, &[diseq]).expect("ite true identity refutes");
        assert_eq!(cert.lhs, x);
        assert_eq!(cert.rhs, ite);
        assert_eq!(cert.kind, TermIdentityKind::IteSimplification);
    }

    #[test]
    fn rejects_nonconstant_distinct_ite_branches() {
        let mut arena = TermArena::new();
        let c = {
            let symbol = arena.declare("c", Sort::Bool).unwrap();
            arena.var(symbol)
        };
        let x = arena.real_var("x").unwrap();
        let y = arena.real_var("y").unwrap();
        let ite = arena.ite(c, x, y).unwrap();
        let eq = arena.eq(x, ite).unwrap();
        let diseq = arena.not(eq).unwrap();

        assert!(term_identity_refutation(&arena, &[diseq]).is_none());
    }
}
