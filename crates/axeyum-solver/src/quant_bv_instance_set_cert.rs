//! Query-scoped source instances for positive Bool/BV universals (ADR-0134).

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value};

use crate::backend::SolverError;
use crate::proof::UnsatProof;
use crate::quant_bool_model_sat::{
    admitted_positive_universal_bv, bool_bv_value_to_const, contains_quantifier, erase_quantifiers,
    rewrite_positive_universals,
};

/// Maximum source instances carried by one query-scoped certificate.
pub const BV_POSITIVE_INSTANCE_SET_CAP: usize = 256;

/// One complete concrete assignment to every positive universal binder in an
/// original assertion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvPositiveUniversalSourceInstance {
    /// Exact original assertion from which the instance is rebuilt.
    pub assertion: TermId,
    /// Complete binder assignment in deterministic source traversal order.
    pub bindings: Vec<(SymbolId, Value)>,
}

/// A checked query-scoped refutation by positive-universal Bool/BV instances.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BvPositiveUniversalInstanceSetCertificate {
    /// Exact original query assertion sequence.
    pub assertions: Vec<TermId>,
    /// Source instances used by the ground refutation.
    pub instances: Vec<BvPositiveUniversalSourceInstance>,
    /// Refutation of the deterministically rebuilt `QF_BV` skeleton and instances.
    pub residual_proof: UnsatProof,
}

/// Rebuilds and checks a query-scoped positive-universal instance refutation.
///
/// # Errors
///
/// Returns [`SolverError`] if deterministic source reconstruction or proof
/// replay fails. Structural and binding mismatches return `Ok(false)`.
pub fn check_bv_positive_universal_instance_set(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvPositiveUniversalInstanceSetCertificate,
) -> Result<bool, SolverError> {
    let Some((scratch, residual)) =
        rebuild_bv_positive_universal_instance_set(arena, assertions, certificate)?
    else {
        return Ok(false);
    };
    certificate
        .residual_proof
        .recheck_for_bool_terms(&scratch, &residual)
}

pub(crate) fn rebuild_bv_positive_universal_instance_set(
    arena: &TermArena,
    assertions: &[TermId],
    certificate: &BvPositiveUniversalInstanceSetCertificate,
) -> Result<Option<(TermArena, Vec<TermId>)>, SolverError> {
    if assertions.is_empty()
        || certificate.assertions != assertions
        || certificate.instances.is_empty()
        || certificate.instances.len() > BV_POSITIVE_INSTANCE_SET_CAP
        || assertions
            .iter()
            .any(|assertion| assertion.index() >= arena.len())
    {
        return Ok(None);
    }

    let assertion_set = assertions.iter().copied().collect::<BTreeSet<_>>();
    let mut scratch = arena.clone();
    let mut residual = Vec::with_capacity(assertions.len() + certificate.instances.len());
    for &assertion in assertions {
        if contains_quantifier(&scratch, assertion) {
            if admitted_positive_universal_bv(&scratch, assertion).is_none() {
                return Ok(None);
            }
            residual.push(erase_quantifiers(
                &mut scratch,
                assertion,
                &mut HashMap::new(),
            ));
        } else if qf_bv_assertion(&scratch, assertion) {
            residual.push(assertion);
        } else {
            return Ok(None);
        }
    }

    let mut seen = Vec::new();
    for source in &certificate.instances {
        if !assertion_set.contains(&source.assertion) || seen.contains(source) {
            return Ok(None);
        }
        seen.push(source.clone());
        let Some(instance) = instantiate_source(&mut scratch, source)? else {
            return Ok(None);
        };
        residual.push(instance);
    }
    Ok(Some((scratch, residual)))
}

fn instantiate_source(
    arena: &mut TermArena,
    source: &BvPositiveUniversalSourceInstance,
) -> Result<Option<TermId>, SolverError> {
    let Some(admitted) = admitted_positive_universal_bv(arena, source.assertion) else {
        return Ok(None);
    };
    if source.bindings.len() != admitted.binders.len() {
        return Ok(None);
    }
    let mut replacements = HashMap::new();
    for (&binder, (carried, value)) in admitted.binders.iter().zip(&source.bindings) {
        let sort = arena.symbol(binder).1;
        if binder != *carried
            || value.sort() != sort
            || !matches!(sort, Sort::Bool | Sort::BitVec(_))
        {
            return Ok(None);
        }
        let constant = bool_bv_value_to_const(arena, value)?;
        replacements.insert(arena.var(binder), constant);
    }
    let Some(instance) = rewrite_positive_universals(
        arena,
        source.assertion,
        true,
        &replacements,
        &mut HashMap::new(),
    ) else {
        return Ok(None);
    };
    Ok((!contains_quantifier(arena, instance)).then_some(instance))
}

fn qf_bv_assertion(arena: &TermArena, assertion: TermId) -> bool {
    if arena.sort_of(assertion) != Sort::Bool {
        return false;
    }
    let mut seen = BTreeSet::new();
    let mut stack = vec![assertion];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if !matches!(arena.sort_of(term), Sort::Bool | Sort::BitVec(_)) {
            return false;
        }
        match arena.node(term) {
            axeyum_ir::TermNode::App {
                op: axeyum_ir::Op::Forall(_) | axeyum_ir::Op::Exists(_) | axeyum_ir::Op::Apply(_),
                ..
            } => return false,
            axeyum_ir::TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    true
}
