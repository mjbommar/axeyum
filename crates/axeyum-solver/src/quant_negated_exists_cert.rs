//! Evaluator-replayed witnesses for negated existential assertions (ADR-0126).

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

/// Maximum existential binders admitted by the source checker.
pub const NEGATED_EXISTENTIAL_BINDER_CAP: usize = 128;
/// Maximum distinct nodes admitted in the existential body.
pub const NEGATED_EXISTENTIAL_NODE_CAP: usize = 4_096;

/// A concrete witness satisfying the body of one top-level negated existential.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NegatedExistentialWitnessCertificate {
    /// The original top-level `not (exists+ body)` assertion being refuted.
    pub assertion: TermId,
    /// One concrete value per existential binder, in outer-to-inner order.
    pub bindings: Vec<(SymbolId, Value)>,
}

/// Independently checks a negated-existential witness against original IR.
///
/// The checker performs no rewriting, substitution, or solver call. It accepts
/// only a bounded closed Bool/BV existential body and evaluates that untouched
/// body under the complete carried assignment.
#[must_use]
pub fn check_negated_existential_witness(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &NegatedExistentialWitnessCertificate,
) -> bool {
    if !assertions.contains(&certificate.assertion) || certificate.assertion.index() >= arena.len()
    {
        return false;
    }

    let Some((binders, body)) = peel_negated_exists(arena, certificate.assertion) else {
        return false;
    };
    let bound: BTreeSet<SymbolId> = binders.iter().copied().collect();
    if binders.len() > NEGATED_EXISTENTIAL_BINDER_CAP
        || bound.len() != binders.len()
        || certificate.bindings.len() != binders.len()
        || !body_is_closed_qf_bv(arena, body, &bound)
    {
        return false;
    }

    let mut assignment = Assignment::new();
    for (&binder, (carried_binder, value)) in binders.iter().zip(&certificate.bindings) {
        let sort = arena.symbol(binder).1;
        if binder != *carried_binder || !is_admitted_sort(sort) || value.sort() != sort {
            return false;
        }
        assignment.set(binder, value.clone());
    }

    matches!(eval(arena, body, &assignment), Ok(Value::Bool(true)))
}

pub(crate) fn admitted_negated_existential(
    arena: &TermArena,
    assertion: TermId,
) -> Option<(Vec<SymbolId>, TermId)> {
    let TermNode::App {
        op: Op::BoolNot,
        args: not_args,
    } = arena.node(assertion)
    else {
        return None;
    };
    if not_args.len() != 1 {
        return None;
    }

    let mut term = not_args[0];
    let mut binders = Vec::new();
    while let TermNode::App {
        op: Op::Exists(binder),
        args,
    } = arena.node(term)
    {
        if args.len() != 1
            || binders.len() == NEGATED_EXISTENTIAL_BINDER_CAP
            || !is_admitted_sort(arena.symbol(*binder).1)
        {
            return None;
        }
        binders.push(*binder);
        term = args[0];
    }
    if binders.is_empty() {
        return None;
    }

    let bound: BTreeSet<SymbolId> = binders.iter().copied().collect();
    if bound.len() != binders.len() || !body_is_closed_qf_bv(arena, term, &bound) {
        return None;
    }
    Some((binders, term))
}

fn peel_negated_exists(arena: &TermArena, assertion: TermId) -> Option<(Vec<SymbolId>, TermId)> {
    admitted_negated_existential(arena, assertion)
}

fn body_is_closed_qf_bv(arena: &TermArena, body: TermId, bound: &BTreeSet<SymbolId>) -> bool {
    if arena.sort_of(body) != Sort::Bool {
        return false;
    }

    let mut seen = BTreeSet::new();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > NEGATED_EXISTENTIAL_NODE_CAP || !is_admitted_sort(arena.sort_of(term)) {
            return false;
        }
        match arena.node(term) {
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
    true
}

const fn is_admitted_sort(sort: Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_))
}
