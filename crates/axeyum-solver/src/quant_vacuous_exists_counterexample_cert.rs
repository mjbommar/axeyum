//! Checked counterexamples below vacuous existential prefixes (ADR-0128).

use std::collections::BTreeSet;

use axeyum_ir::{Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

/// Maximum total binders admitted by the source checker.
pub const VACUOUS_EXISTS_COUNTEREXAMPLE_BINDER_CAP: usize = 128;
/// Maximum distinct nodes admitted in the complete source assertion.
pub const VACUOUS_EXISTS_COUNTEREXAMPLE_NODE_CAP: usize = 4_096;

/// A concrete assignment that falsifies the universal body below one or more
/// syntactically vacuous leading existential binders.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VacuousExistsUniversalCounterexampleCertificate {
    /// The original top-level `exists+ forall+` assertion being refuted.
    pub assertion: TermId,
    /// One concrete value per universal binder, in outer-to-inner order.
    pub bindings: Vec<(SymbolId, Value)>,
}

#[derive(Debug, Clone)]
pub(crate) struct AdmittedVacuousExistsUniversal {
    pub universal_binders: Vec<SymbolId>,
    pub body: TermId,
}

/// Independently checks a vacuous-existential universal counterexample.
///
/// The checker admits only an exact nonempty `exists+ forall+` Bool/BV prefix.
/// Every existential binder must be absent from the quantifier-free body, and
/// the body must be closed apart from the universal binders. It then evaluates
/// the untouched original body under the carried universal values.
#[must_use]
pub fn check_vacuous_exists_universal_counterexample(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &VacuousExistsUniversalCounterexampleCertificate,
) -> bool {
    if !assertions.contains(&certificate.assertion) {
        return false;
    }
    let Some(admitted) = admitted_vacuous_exists_universal(arena, certificate.assertion) else {
        return false;
    };
    if certificate.bindings.len() != admitted.universal_binders.len() {
        return false;
    }

    let mut assignment = Assignment::new();
    for (&binder, (carried_binder, value)) in
        admitted.universal_binders.iter().zip(&certificate.bindings)
    {
        let sort = arena.symbol(binder).1;
        if binder != *carried_binder || value.sort() != sort || !is_bool_bv(sort) {
            return false;
        }
        assignment.set(binder, value.clone());
    }

    matches!(
        eval(arena, admitted.body, &assignment),
        Ok(Value::Bool(false))
    )
}

pub(crate) fn admitted_vacuous_exists_universal(
    arena: &TermArena,
    assertion: TermId,
) -> Option<AdmittedVacuousExistsUniversal> {
    if assertion.index() >= arena.len()
        || arena.sort_of(assertion) != Sort::Bool
        || !assertion_within_cap(arena, assertion)
    {
        return None;
    }

    let mut term = assertion;
    let mut existential_binders = Vec::new();
    while let TermNode::App {
        op: Op::Exists(binder),
        args,
    } = arena.node(term)
    {
        if args.len() != 1
            || existential_binders.len() == VACUOUS_EXISTS_COUNTEREXAMPLE_BINDER_CAP
            || !is_bool_bv(arena.symbol(*binder).1)
        {
            return None;
        }
        existential_binders.push(*binder);
        term = args[0];
    }
    if existential_binders.is_empty() {
        return None;
    }

    let mut universal_binders = Vec::new();
    while let TermNode::App {
        op: Op::Forall(binder),
        args,
    } = arena.node(term)
    {
        if args.len() != 1
            || existential_binders.len() + universal_binders.len()
                == VACUOUS_EXISTS_COUNTEREXAMPLE_BINDER_CAP
            || !is_bool_bv(arena.symbol(*binder).1)
        {
            return None;
        }
        universal_binders.push(*binder);
        term = args[0];
    }
    if universal_binders.is_empty() {
        return None;
    }

    let all_binders = existential_binders
        .iter()
        .chain(&universal_binders)
        .copied()
        .collect::<BTreeSet<_>>();
    let universal_set = universal_binders.iter().copied().collect::<BTreeSet<_>>();
    if all_binders.len() != existential_binders.len() + universal_binders.len()
        || !body_is_closed_qf_bv(arena, term, &universal_set)
    {
        return None;
    }

    Some(AdmittedVacuousExistsUniversal {
        universal_binders,
        body: term,
    })
}

fn assertion_within_cap(arena: &TermArena, assertion: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![assertion];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > VACUOUS_EXISTS_COUNTEREXAMPLE_NODE_CAP || !is_bool_bv(arena.sort_of(term)) {
            return false;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    true
}

fn body_is_closed_qf_bv(
    arena: &TermArena,
    body: TermId,
    universal_binders: &BTreeSet<SymbolId>,
) -> bool {
    if arena.sort_of(body) != Sort::Bool {
        return false;
    }
    let mut seen = BTreeSet::new();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if !is_bool_bv(arena.sort_of(term)) {
            return false;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) if !universal_binders.contains(symbol) => return false,
            TermNode::App {
                op: Op::Forall(_) | Op::Exists(_) | Op::Apply(_),
                ..
            } => return false,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    true
}

const fn is_bool_bv(sort: Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_))
}
