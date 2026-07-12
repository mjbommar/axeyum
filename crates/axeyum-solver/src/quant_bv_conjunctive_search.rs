//! Untrusted candidate search for ADR-0127 conjunctive universal instances.

use std::collections::BTreeSet;
use std::time::Instant;

use axeyum_ir::{TermArena, TermId, TermNode, Value, well_founded_default};

use crate::backend::{SolverConfig, SolverError};
use crate::proof::{UnsatProofOutcome, export_qf_bv_unsat_proof_within};
use crate::quant_bv_conjunctive_cert::{
    AdmittedConjunctiveUniversal, BvConjunctiveUniversalInstanceCertificate,
    admitted_conjunctive_universal, check_bv_conjunctive_universal_instance,
    conjunctive_universals, instantiate_conjunctive_universal,
};

const SEARCH_CANDIDATE_CAP: usize = 256;

pub(crate) fn find_bv_conjunctive_universal_instance(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<BvConjunctiveUniversalInstanceCertificate>, SolverError> {
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    for &assertion in assertions {
        for universal in conjunctive_universals(arena, assertion) {
            let Some(admitted) = admitted_conjunctive_universal(arena, assertion, universal) else {
                continue;
            };
            let defaults = default_bindings(arena, &admitted);
            if defaults.len() != admitted.binders.len() {
                continue;
            }
            if let Some(certificate) = try_candidate(
                arena, assertions, assertion, universal, &admitted, &defaults, deadline,
            )? {
                return Ok(Some(certificate));
            }

            let source_values = collect_source_values(arena, assertion);
            let mut attempted = 1usize;
            for (index, &binder) in admitted.binders.iter().enumerate() {
                let sort = arena.symbol(binder).1;
                for value in source_values.iter().filter(|value| value.sort() == sort) {
                    if defaults[index].1 == *value {
                        continue;
                    }
                    if attempted == SEARCH_CANDIDATE_CAP
                        || deadline.is_some_and(|end| Instant::now() >= end)
                    {
                        return Ok(None);
                    }
                    attempted += 1;
                    let mut bindings = defaults.clone();
                    bindings[index].1 = value.clone();
                    if let Some(certificate) = try_candidate(
                        arena, assertions, assertion, universal, &admitted, &bindings, deadline,
                    )? {
                        return Ok(Some(certificate));
                    }
                }
            }
        }
    }
    Ok(None)
}

#[allow(clippy::too_many_arguments)]
fn try_candidate(
    arena: &TermArena,
    assertions: &[TermId],
    assertion: TermId,
    universal: TermId,
    admitted: &AdmittedConjunctiveUniversal,
    bindings: &[(axeyum_ir::SymbolId, Value)],
    deadline: Option<Instant>,
) -> Result<Option<BvConjunctiveUniversalInstanceCertificate>, SolverError> {
    let Some((scratch, residual)) =
        instantiate_conjunctive_universal(arena, assertion, universal, admitted, bindings)?
    else {
        return Ok(None);
    };
    let proof = match export_qf_bv_unsat_proof_within(&scratch, &[residual], deadline)? {
        UnsatProofOutcome::Proved(proof) => proof,
        UnsatProofOutcome::Satisfiable | UnsatProofOutcome::Inconclusive => return Ok(None),
    };
    let certificate = BvConjunctiveUniversalInstanceCertificate {
        assertion,
        universal,
        bindings: bindings.to_vec(),
        residual_proof: proof,
    };
    if check_bv_conjunctive_universal_instance(arena, assertions, &certificate)? {
        Ok(Some(certificate))
    } else {
        Err(SolverError::Backend(
            "generated conjunctive universal instance failed independent replay".to_owned(),
        ))
    }
}

fn default_bindings(
    arena: &TermArena,
    admitted: &AdmittedConjunctiveUniversal,
) -> Vec<(axeyum_ir::SymbolId, Value)> {
    admitted
        .binders
        .iter()
        .filter_map(|&binder| {
            let sort = arena.symbol(binder).1;
            well_founded_default(arena, sort).map(|value| (binder, value))
        })
        .collect()
}

fn collect_source_values(arena: &TermArena, assertion: TermId) -> Vec<Value> {
    let mut values = vec![Value::Bool(false), Value::Bool(true)];
    let mut seen = BTreeSet::new();
    let mut stack = vec![assertion];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::BvConst { width, value } => values.push(Value::Bv {
                width: *width,
                value: *value,
            }),
            TermNode::WideBvConst(value) => values.push(Value::WideBv(value.clone())),
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    values.sort_by_key(value_sort_key);
    values.dedup();
    values
}

fn value_sort_key(value: &Value) -> (u8, u32, u128) {
    match value {
        Value::Bool(value) => (0, 0, u128::from(*value)),
        Value::Bv { width, value } => (1, *width, *value),
        Value::WideBv(value) => (2, value.width(), 0),
        _ => (3, 0, 0),
    }
}
