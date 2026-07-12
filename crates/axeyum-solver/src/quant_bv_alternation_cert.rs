//! Source-bound counterexamples to closed `forall+ exists+` Bool/BV formulas
//! (ADR-0124/0125).

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode, Value};
use axeyum_rewrite::replace_subterms;

use crate::backend::SolverError;
use crate::proof::UnsatProof;

/// Maximum admitted binders across both quantifier blocks (ADR-0125).
pub const BV_ALTERNATION_BINDER_CAP: usize = 1024;
/// Maximum reachable nodes in the quantifier-free matrix.
pub const BV_ALTERNATION_NODE_CAP: usize = 4096;

/// One universal assignment whose residual existential matrix is QF_BV-UNSAT.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvAlternationCounterexampleCertificate {
    /// The original top-level `forall+ exists+` assertion being refuted.
    pub assertion: TermId,
    /// One concrete value per universal binder, in outer-to-inner order.
    pub outer_bindings: Vec<(SymbolId, Value)>,
    /// A source-bound refutation of the matrix after outer substitution and
    /// deterministic freshening of the existential binders.
    pub residual_proof: UnsatProof,
}

#[derive(Debug, Clone)]
pub(crate) struct AdmittedAlternation {
    pub outer: Vec<SymbolId>,
    pub inner: Vec<SymbolId>,
    pub body: TermId,
    pub antecedent: TermId,
}

/// Rechecks a quantified counterexample against the exact original assertion.
///
/// # Errors
///
/// Returns [`SolverError`] if deterministic source instantiation or proof
/// parsing/checking fails. Structural or binding mismatches return `Ok(false)`.
pub fn check_bv_alternation_counterexample(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvAlternationCounterexampleCertificate,
) -> Result<bool, SolverError> {
    if !assertions.contains(&certificate.assertion) || certificate.assertion.index() >= arena.len()
    {
        return Ok(false);
    }
    let Some(admitted) = admitted_alternation(arena, certificate.assertion) else {
        return Ok(false);
    };
    let Some((scratch, residual)) = instantiate_residual(
        arena,
        certificate.assertion,
        &admitted,
        &certificate.outer_bindings,
    )?
    else {
        return Ok(false);
    };
    certificate
        .residual_proof
        .recheck_for_bool_terms(&scratch, &[residual])
}

pub(crate) fn admitted_alternation(
    arena: &TermArena,
    assertion: TermId,
) -> Option<AdmittedAlternation> {
    if assertion.index() >= arena.len() {
        return None;
    }
    let mut term = assertion;
    let mut outer = Vec::new();
    while let TermNode::App {
        op: Op::Forall(binder),
        args,
    } = arena.node(term)
    {
        if args.len() != 1 || !is_bool_bv(arena.symbol(*binder).1) {
            return None;
        }
        outer.push(*binder);
        term = args[0];
    }
    let mut inner = Vec::new();
    while let TermNode::App {
        op: Op::Exists(binder),
        args,
    } = arena.node(term)
    {
        if args.len() != 1 || !is_bool_bv(arena.symbol(*binder).1) {
            return None;
        }
        inner.push(*binder);
        term = args[0];
    }
    if outer.is_empty() || inner.is_empty() || outer.len() + inner.len() > BV_ALTERNATION_BINDER_CAP
    {
        return None;
    }
    let all = outer.iter().chain(&inner).copied().collect::<BTreeSet<_>>();
    if all.len() != outer.len() + inner.len() || !closed_qf_bool_bv(arena, term, &all) {
        return None;
    }
    let TermNode::App {
        op: Op::BoolImplies,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let outer_set = outer.iter().copied().collect::<BTreeSet<_>>();
    if !uses_only_symbols(arena, args[0], &outer_set) {
        return None;
    }
    Some(AdmittedAlternation {
        outer,
        inner,
        body: term,
        antecedent: args[0],
    })
}

pub(crate) fn instantiate_residual(
    arena: &TermArena,
    assertion: TermId,
    admitted: &AdmittedAlternation,
    bindings: &[(SymbolId, Value)],
) -> Result<Option<(TermArena, TermId)>, SolverError> {
    if bindings.len() != admitted.outer.len() {
        return Ok(None);
    }
    let mut scratch = arena.clone();
    let mut replacements = HashMap::new();
    for (&binder, (carried, value)) in admitted.outer.iter().zip(bindings) {
        let sort = scratch.symbol(binder).1;
        if binder != *carried || value.sort() != sort {
            return Ok(None);
        }
        let constant = value_to_const(&mut scratch, value)?;
        let variable = scratch.var(binder);
        replacements.insert(variable, constant);
    }

    let mut nonce = scratch.symbols().count();
    for &binder in &admitted.inner {
        let sort = scratch.symbol(binder).1;
        let fresh = loop {
            let name = format!(
                "!bv_alternation_{}_{}_{}",
                assertion.index(),
                binder.index(),
                nonce
            );
            nonce += 1;
            if scratch.find_internal_symbol(&name).is_none() {
                break scratch
                    .declare_internal(&name, sort)
                    .map_err(|error| SolverError::Backend(error.to_string()))?;
            }
        };
        let variable = scratch.var(binder);
        let fresh_term = scratch.var(fresh);
        replacements.insert(variable, fresh_term);
    }
    let mut memo = HashMap::new();
    let residual = replace_subterms(&mut scratch, admitted.body, &replacements, &mut memo)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    Ok(Some((scratch, residual)))
}

fn value_to_const(arena: &mut TermArena, value: &Value) -> Result<TermId, SolverError> {
    match value {
        Value::Bool(value) => Ok(arena.bool_const(*value)),
        Value::Bv { width, value } => arena
            .bv_const(*width, *value)
            .map_err(|error| SolverError::Backend(error.to_string())),
        Value::WideBv(value) => Ok(arena.wide_bv_const(value.clone())),
        _ => Err(SolverError::Backend(
            "BV alternation certificate carried a non-Bool/BV value".to_owned(),
        )),
    }
}

fn closed_qf_bool_bv(arena: &TermArena, body: TermId, bound: &BTreeSet<SymbolId>) -> bool {
    if arena.sort_of(body) != Sort::Bool {
        return false;
    }
    let mut seen = BTreeSet::new();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) || seen.len() > BV_ALTERNATION_NODE_CAP {
            continue;
        }
        if !is_bool_bv(arena.sort_of(term)) {
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
    seen.len() <= BV_ALTERNATION_NODE_CAP
}

fn uses_only_symbols(arena: &TermArena, term: TermId, admitted: &BTreeSet<SymbolId>) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) if !admitted.contains(symbol) => return false,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    true
}

const fn is_bool_bv(sort: Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::BitVec(_))
}
