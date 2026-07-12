//! Untrusted outer-witness search for ADR-0124/0125 BV quantifier alternation.

use std::collections::HashMap;
use std::time::Instant;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value, well_founded_default};
use axeyum_rewrite::replace_subterms;

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::proof::{UnsatProofOutcome, export_qf_bv_unsat_proof_within};
use crate::quant_bv_alternation_cert::{
    AdmittedAlternation, BvAlternationCounterexampleCertificate, admitted_alternation,
    check_bv_alternation_counterexample, instantiate_residual,
};

struct FreshOuter {
    source: SymbolId,
    search: SymbolId,
    sort: Sort,
}

pub(crate) fn find_bv_alternation_counterexample(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<BvAlternationCounterexampleCertificate>, SolverError> {
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    for &assertion in assertions {
        let Some(admitted) = admitted_alternation(arena, assertion) else {
            continue;
        };
        let (mut search_arena, antecedent, fresh) =
            freshen_outer_antecedent(arena, assertion, &admitted)?;

        if let Some(certificate) = try_search_query(
            arena,
            assertions,
            assertion,
            &admitted,
            &mut search_arena,
            antecedent,
            &fresh,
            config,
            deadline,
        )? {
            return Ok(Some(certificate));
        }

        for entry in &fresh {
            if deadline.is_some_and(|end| Instant::now() >= end) {
                return Ok(None);
            }
            let Some(default) = well_founded_default(&search_arena, entry.sort) else {
                continue;
            };
            let default_term = value_to_const(&mut search_arena, &default)?;
            let fresh_term = search_arena.var(entry.search);
            let equality = search_arena
                .eq(fresh_term, default_term)
                .map_err(|error| SolverError::Backend(error.to_string()))?;
            let perturb = search_arena
                .not(equality)
                .map_err(|error| SolverError::Backend(error.to_string()))?;
            let query = search_arena
                .and(antecedent, perturb)
                .map_err(|error| SolverError::Backend(error.to_string()))?;
            if let Some(certificate) = try_search_query(
                arena,
                assertions,
                assertion,
                &admitted,
                &mut search_arena,
                query,
                &fresh,
                config,
                deadline,
            )? {
                return Ok(Some(certificate));
            }
        }
    }
    Ok(None)
}

#[allow(clippy::too_many_arguments)]
fn try_search_query(
    source_arena: &TermArena,
    assertions: &[TermId],
    assertion: TermId,
    admitted: &AdmittedAlternation,
    search_arena: &mut TermArena,
    query: TermId,
    fresh: &[FreshOuter],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<Option<BvAlternationCounterexampleCertificate>, SolverError> {
    let search_config = remaining_config(config, deadline);
    let result = match check_auto(search_arena, &[query], &search_config) {
        Ok(result) => result,
        Err(SolverError::Unsupported(_)) => return Ok(None),
        Err(error) => return Err(error),
    };
    let CheckResult::Sat(model) = result else {
        return Ok(None);
    };
    let mut bindings = Vec::with_capacity(fresh.len());
    for entry in fresh {
        let Some(value) = model
            .get(entry.search)
            .or_else(|| well_founded_default(search_arena, entry.sort))
        else {
            return Ok(None);
        };
        bindings.push((entry.source, value));
    }
    let Some((scratch, residual)) =
        instantiate_residual(source_arena, assertion, admitted, &bindings)?
    else {
        return Ok(None);
    };
    let proof = match export_qf_bv_unsat_proof_within(&scratch, &[residual], deadline)? {
        UnsatProofOutcome::Proved(proof) => proof,
        UnsatProofOutcome::Satisfiable | UnsatProofOutcome::Inconclusive => return Ok(None),
    };
    let certificate = BvAlternationCounterexampleCertificate {
        assertion,
        outer_bindings: bindings,
        residual_proof: proof,
    };
    if check_bv_alternation_counterexample(source_arena, assertions, &certificate)? {
        Ok(Some(certificate))
    } else {
        Err(SolverError::Backend(
            "generated BV alternation counterexample failed independent replay".to_owned(),
        ))
    }
}

fn freshen_outer_antecedent(
    arena: &TermArena,
    assertion: TermId,
    admitted: &AdmittedAlternation,
) -> Result<(TermArena, TermId, Vec<FreshOuter>), SolverError> {
    let mut scratch = arena.clone();
    let mut replacements = HashMap::new();
    let mut fresh = Vec::with_capacity(admitted.outer.len());
    let mut nonce = scratch.symbols().count();
    for &binder in &admitted.outer {
        let sort = scratch.symbol(binder).1;
        let symbol = loop {
            let name = format!(
                "!bv_alternation_search_{}_{}_{}",
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
        let fresh_term = scratch.var(symbol);
        replacements.insert(variable, fresh_term);
        fresh.push(FreshOuter {
            source: binder,
            search: symbol,
            sort,
        });
    }
    let mut memo = HashMap::new();
    let antecedent = replace_subterms(&mut scratch, admitted.antecedent, &replacements, &mut memo)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    Ok((scratch, antecedent, fresh))
}

fn remaining_config(config: &SolverConfig, deadline: Option<Instant>) -> SolverConfig {
    let mut remaining = config.clone();
    if let Some(end) = deadline {
        remaining.timeout = Some(end.saturating_duration_since(Instant::now()));
    }
    remaining
}

fn value_to_const(arena: &mut TermArena, value: &Value) -> Result<TermId, SolverError> {
    match value {
        Value::Bool(value) => Ok(arena.bool_const(*value)),
        Value::Bv { width, value } => arena
            .bv_const(*width, *value)
            .map_err(|error| SolverError::Backend(error.to_string())),
        Value::WideBv(value) => Ok(arena.wide_bv_const(value.clone())),
        _ => Err(SolverError::Backend(
            "BV alternation search produced a non-Bool/BV value".to_owned(),
        )),
    }
}
