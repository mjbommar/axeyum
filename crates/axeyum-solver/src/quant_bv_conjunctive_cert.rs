//! Source-bound conjunctive universal instances over Bool/BV (ADR-0127).

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, Value};
use axeyum_rewrite::replace_subterms;

use crate::backend::SolverError;
use crate::proof::UnsatProof;

/// Maximum universal binders admitted by the source checker.
pub const BV_CONJUNCTIVE_UNIVERSAL_BINDER_CAP: usize = 128;
/// Maximum distinct nodes admitted in the complete source assertion.
pub const BV_CONJUNCTIVE_UNIVERSAL_NODE_CAP: usize = 4_096;

/// One source universal instance whose conjunctive context is QF_BV-UNSAT.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvConjunctiveUniversalInstanceCertificate {
    /// Original top-level assertion containing the selected universal conjunct.
    pub assertion: TermId,
    /// Exact universal term reached only through conjunction nodes.
    pub universal: TermId,
    /// One concrete value per leading universal binder, outermost first.
    pub bindings: Vec<(SymbolId, Value)>,
    /// Refutation of the source assertion with `universal` replaced by its
    /// concrete body instance.
    pub residual_proof: UnsatProof,
}

#[derive(Debug, Clone)]
pub(crate) struct AdmittedConjunctiveUniversal {
    pub binders: Vec<SymbolId>,
    pub body: TermId,
}

/// Rechecks a conjunctive universal instance against exact original IR.
///
/// # Errors
///
/// Returns [`SolverError`] if deterministic instantiation or proof replay
/// fails. Structural and binding mismatches return `Ok(false)`.
pub fn check_bv_conjunctive_universal_instance(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvConjunctiveUniversalInstanceCertificate,
) -> Result<bool, SolverError> {
    if !assertions.contains(&certificate.assertion)
        || certificate.assertion.index() >= arena.len()
        || certificate.universal.index() >= arena.len()
    {
        return Ok(false);
    }
    let Some(admitted) =
        admitted_conjunctive_universal(arena, certificate.assertion, certificate.universal)
    else {
        return Ok(false);
    };
    let Some((scratch, residual)) = instantiate_conjunctive_universal(
        arena,
        certificate.assertion,
        certificate.universal,
        &admitted,
        &certificate.bindings,
    )?
    else {
        return Ok(false);
    };
    certificate
        .residual_proof
        .recheck_for_bool_terms(&scratch, &[residual])
}

pub(crate) fn conjunctive_universals(arena: &TermArena, assertion: TermId) -> Vec<TermId> {
    if assertion.index() >= arena.len()
        || !assertion_within_cap(arena, assertion)
        || arena.sort_of(assertion) != Sort::Bool
    {
        return Vec::new();
    }
    let mut selected = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![assertion];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::App {
                op: Op::Forall(_), ..
            } => selected.push(term),
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    selected.sort_by_key(|term| term.index());
    selected.dedup();
    selected
}

pub(crate) fn admitted_conjunctive_universal(
    arena: &TermArena,
    assertion: TermId,
    universal: TermId,
) -> Option<AdmittedConjunctiveUniversal> {
    if assertion.index() >= arena.len()
        || universal.index() >= arena.len()
        || arena.sort_of(assertion) != Sort::Bool
        || !assertion_within_cap(arena, assertion)
        || total_occurrences(arena, assertion, universal) != 1
        || !assertion_is_qf_bv_except(arena, assertion, universal)
    {
        return None;
    }

    let mut term = universal;
    let mut binders = Vec::new();
    while let TermNode::App {
        op: Op::Forall(binder),
        args,
    } = arena.node(term)
    {
        if args.len() != 1
            || binders.len() == BV_CONJUNCTIVE_UNIVERSAL_BINDER_CAP
            || !is_bool_bv(arena.symbol(*binder).1)
        {
            return None;
        }
        binders.push(*binder);
        term = args[0];
    }
    let unique = binders.iter().copied().collect::<BTreeSet<_>>();
    if binders.is_empty() || unique.len() != binders.len() || !body_is_qf_bv(arena, term) {
        return None;
    }
    Some(AdmittedConjunctiveUniversal {
        binders,
        body: term,
    })
}

/// Relaxed admission for decision-only search: it keeps the same universal
/// chain and source-shape checks, but does not require the innermost body to be
/// quantifier-free. This is intentionally not used for certificate replay.
pub(crate) fn admitted_conjunctive_universal_loose(
    arena: &TermArena,
    assertion: TermId,
    universal: TermId,
) -> Option<AdmittedConjunctiveUniversal> {
    if assertion.index() >= arena.len()
        || universal.index() >= arena.len()
        || arena.sort_of(assertion) != Sort::Bool
        || !assertion_within_cap(arena, assertion)
        || total_occurrences(arena, assertion, universal) != 1
    {
        return None;
    }

    let mut term = universal;
    let mut binders = Vec::new();
    while let TermNode::App {
        op: Op::Forall(binder),
        args,
    } = arena.node(term)
    {
        if args.len() != 1
            || binders.len() == BV_CONJUNCTIVE_UNIVERSAL_BINDER_CAP
            || !is_bool_bv(arena.symbol(*binder).1)
        {
            return None;
        }
        binders.push(*binder);
        term = args[0];
    }
    let unique = binders.iter().copied().collect::<BTreeSet<_>>();
    if binders.is_empty() || unique.len() != binders.len() || arena.sort_of(term) != Sort::Bool {
        return None;
    }
    Some(AdmittedConjunctiveUniversal {
        binders,
        body: term,
    })
}

pub(crate) fn instantiate_conjunctive_universal(
    arena: &TermArena,
    assertion: TermId,
    universal: TermId,
    admitted: &AdmittedConjunctiveUniversal,
    bindings: &[(SymbolId, Value)],
) -> Result<Option<(TermArena, TermId)>, SolverError> {
    if bindings.len() != admitted.binders.len() {
        return Ok(None);
    }

    let mut scratch = arena.clone();
    let mut binder_replacements = HashMap::new();
    for (&binder, (carried, value)) in admitted.binders.iter().zip(bindings) {
        let sort = scratch.symbol(binder).1;
        if binder != *carried || value.sort() != sort || !is_bool_bv(sort) {
            return Ok(None);
        }
        let variable = scratch.var(binder);
        let constant = value_to_const(&mut scratch, value)?;
        binder_replacements.insert(variable, constant);
    }

    let mut body_memo = HashMap::new();
    let instance = replace_subterms(
        &mut scratch,
        admitted.body,
        &binder_replacements,
        &mut body_memo,
    )
    .map_err(|error| SolverError::Backend(error.to_string()))?;

    let mut assertion_replacements = HashMap::new();
    assertion_replacements.insert(universal, instance);
    let mut assertion_memo = HashMap::new();
    let residual = replace_subterms(
        &mut scratch,
        assertion,
        &assertion_replacements,
        &mut assertion_memo,
    )
    .map_err(|error| SolverError::Backend(error.to_string()))?;
    Ok(Some((scratch, residual)))
}

fn total_occurrences(arena: &TermArena, assertion: TermId, selected: TermId) -> usize {
    let mut count = 0usize;
    let mut visited = 0usize;
    let mut stack = vec![assertion];
    while let Some(term) = stack.pop() {
        visited += 1;
        if visited > BV_CONJUNCTIVE_UNIVERSAL_NODE_CAP * 2 {
            return 2;
        }
        if term == selected {
            count += 1;
            if count > 1 {
                return count;
            }
            continue;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    count
}

fn assertion_within_cap(arena: &TermArena, assertion: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![assertion];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > BV_CONJUNCTIVE_UNIVERSAL_NODE_CAP || !is_bool_bv(arena.sort_of(term)) {
            return false;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    true
}

fn assertion_is_qf_bv_except(arena: &TermArena, assertion: TermId, selected: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![assertion];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) || term == selected {
            continue;
        }
        match arena.node(term) {
            TermNode::App {
                op: Op::Forall(_) | Op::Exists(_) | Op::Apply(_),
                ..
            } => {
                return false;
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    true
}

fn body_is_qf_bv(arena: &TermArena, body: TermId) -> bool {
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
            TermNode::App {
                op: Op::Forall(_) | Op::Exists(_) | Op::Apply(_),
                ..
            } => {
                return false;
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    true
}

fn value_to_const(arena: &mut TermArena, value: &Value) -> Result<TermId, SolverError> {
    match value {
        Value::Bool(value) => Ok(arena.bool_const(*value)),
        Value::Bv { width, value } => arena
            .bv_const(*width, *value)
            .map_err(|error| SolverError::Backend(error.to_string())),
        Value::WideBv(value) => Ok(arena.wide_bv_const(value.clone())),
        _ => Err(SolverError::Backend(
            "conjunctive universal certificate carried a non-Bool/BV value".to_owned(),
        )),
    }
}

const fn is_bool_bv(sort: Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_))
}
