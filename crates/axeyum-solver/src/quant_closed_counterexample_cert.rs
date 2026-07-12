//! Evaluator-replayed counterexamples to closed universal assertions (ADR-0100).
//!
//! The checker also accepts a top-level vacuous existential prefix above the
//! closed universal sentence: if the carried existential binders do not occur in
//! the remainder of the assertion, the prefix is semantically inert over the
//! nonempty scalar domains this route admits.

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

/// A concrete assignment that falsifies the quantifier-free body of one
/// top-level closed universal assertion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosedUniversalCounterexampleCertificate {
    /// The original top-level universal assertion being refuted.
    pub assertion: TermId,
    /// One concrete value per universal binder, in outer-to-inner order.
    pub bindings: Vec<(SymbolId, Value)>,
}

/// Independently checks a closed-universal counterexample against original IR.
///
/// This checker performs no rewriting, substitution, or solver call. It accepts
/// only a nonempty universal prefix over scalar binders whose quantifier-free
/// body is closed, then evaluates that original body under the carried values.
#[must_use]
pub fn check_closed_universal_counterexample(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &ClosedUniversalCounterexampleCertificate,
) -> bool {
    if !assertions.contains(&certificate.assertion) || certificate.assertion.index() >= arena.len()
    {
        return false;
    }

    let Some((exists, binders, body)) = peel_exists_foralls(arena, certificate.assertion) else {
        return false;
    };
    let bound: BTreeSet<SymbolId> = binders.iter().copied().collect();
    let vacuous: BTreeSet<SymbolId> = exists.iter().copied().collect();
    if bound.len() != binders.len()
        || exists.len() != vacuous.len()
        || certificate.bindings.len() != binders.len()
        || !body_is_closed_qf(arena, body, &bound, &vacuous)
    {
        return false;
    }

    let mut assignment = Assignment::new();
    for (&binder, (carried_binder, value)) in binders.iter().zip(&certificate.bindings) {
        let sort = arena.symbol(binder).1;
        if binder != *carried_binder || !is_admitted_scalar(sort) || value.sort() != sort {
            return false;
        }
        assignment.set(binder, value.clone());
    }

    matches!(eval(arena, body, &assignment), Ok(Value::Bool(false)))
}

pub(crate) fn peel_exists_foralls(
    arena: &TermArena,
    mut term: TermId,
) -> Option<(Vec<SymbolId>, Vec<SymbolId>, TermId)> {
    let mut exists = Vec::new();
    while let TermNode::App {
        op: Op::Exists(binder),
        args,
    } = arena.node(term)
    {
        if args.len() != 1 || !is_admitted_scalar(arena.symbol(*binder).1) {
            return None;
        }
        exists.push(*binder);
        term = args[0];
    }

    let mut binders = Vec::new();
    loop {
        match arena.node(term) {
            TermNode::App {
                op: Op::Forall(binder),
                args,
            } if args.len() == 1 => {
                binders.push(*binder);
                term = args[0];
            }
            _ => break,
        }
    }
    (!binders.is_empty()).then_some((exists, binders, term))
}

fn body_is_closed_qf(
    arena: &TermArena,
    body: TermId,
    bound: &BTreeSet<SymbolId>,
    vacuous: &BTreeSet<SymbolId>,
) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) if vacuous.contains(symbol) => return false,
            TermNode::Symbol(symbol) if !bound.contains(symbol) => return false,
            TermNode::App { op, args } => {
                if matches!(op, Op::Forall(_) | Op::Exists(_) | Op::Apply(_)) {
                    return false;
                }
                stack.extend(args.iter().copied());
            }
            _ => {}
        }
    }
    arena.sort_of(body) == Sort::Bool
}

const fn is_admitted_scalar(sort: Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_) | Sort::Int | Sort::Real)
}
