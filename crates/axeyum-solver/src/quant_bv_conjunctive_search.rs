//! Untrusted candidate search for ADR-0127 conjunctive universal instances.

use std::collections::{BTreeSet, HashMap};
use std::time::Instant;

use axeyum_ir::{TermArena, TermId, TermNode, Value, WideUint, well_founded_default};
use axeyum_rewrite::replace_subterms;

use crate::backend::{SolverConfig, SolverError};
use crate::model::Model;
use crate::proof::{UnsatProofOutcome, export_qf_bv_unsat_proof_within};
use crate::quant_bv_conjunctive_cert::{
    AdmittedConjunctiveUniversal, BvConjunctiveUniversalInstanceCertificate,
    admitted_conjunctive_universal, admitted_conjunctive_universal_loose,
    check_bv_conjunctive_universal_instance, conjunctive_universals,
    instantiate_conjunctive_universal,
};
use crate::{CheckResult, check_auto};

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
            let admitted = admitted_conjunctive_universal(arena, assertion, universal)
                .or_else(|| admitted_conjunctive_universal_loose(arena, assertion, universal));
            let Some(admitted) = admitted else {
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

            if let Some(certificate) = try_model_candidate(
                arena, assertions, assertion, universal, &admitted, config, deadline,
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

            if let Some(certificate) = try_candidate_combinations(
                arena,
                assertions,
                assertion,
                universal,
                &admitted,
                &defaults,
                &source_values,
                deadline,
            )? {
                return Ok(Some(certificate));
            }
        }
    }
    Ok(None)
}

/// Decision-only sibling of [`find_bv_conjunctive_universal_instance`]: it
/// reuses the same candidate search, but accepts a candidate when the residual
/// refutes directly through the qf front door even if proof export declines.
pub(crate) fn decide_bv_conjunctive_universal_instance(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<()>, SolverError> {
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    for &assertion in assertions {
        for universal in conjunctive_universals(arena, assertion) {
            let Some(admitted) = admitted_conjunctive_universal_loose(arena, assertion, universal)
            else {
                continue;
            };
            let defaults = default_bindings(arena, &admitted);
            if defaults.len() != admitted.binders.len() {
                continue;
            }
            if try_candidate_unsat(arena, assertion, universal, &admitted, &defaults, deadline)? {
                return Ok(Some(()));
            }
            if try_model_candidate_unsat(
                arena, assertions, assertion, universal, &admitted, config, deadline,
            )? {
                return Ok(Some(()));
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
                    if try_candidate_unsat(
                        arena, assertion, universal, &admitted, &bindings, deadline,
                    )? {
                        return Ok(Some(()));
                    }
                }
            }

            if try_candidate_combinations_unsat(
                arena,
                assertions,
                assertion,
                universal,
                &admitted,
                &defaults,
                &source_values,
                deadline,
            )? {
                return Ok(Some(()));
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

#[allow(clippy::too_many_arguments)]
fn try_model_candidate(
    arena: &TermArena,
    assertions: &[TermId],
    assertion: TermId,
    universal: TermId,
    admitted: &AdmittedConjunctiveUniversal,
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<Option<BvConjunctiveUniversalInstanceCertificate>, SolverError> {
    let mut search_arena = arena.clone();
    let mut replacements = HashMap::new();
    let mut fresh = Vec::with_capacity(admitted.binders.len());
    let mut nonce = search_arena.symbols().count();
    for &binder in &admitted.binders {
        let sort = search_arena.symbol(binder).1;
        let fresh_symbol = loop {
            let name = format!(
                "!bv_conjunctive_search_{}_{}_{}",
                assertion.index(),
                binder.index(),
                nonce
            );
            nonce += 1;
            if search_arena.find_internal_symbol(&name).is_none() {
                break search_arena
                    .declare_internal(&name, sort)
                    .map_err(|error| SolverError::Backend(error.to_string()))?;
            }
        };
        replacements.insert(search_arena.var(binder), search_arena.var(fresh_symbol));
        fresh.push((binder, fresh_symbol, sort));
    }

    let mut body_memo = HashMap::new();
    let fresh_body = replace_subterms(
        &mut search_arena,
        admitted.body,
        &replacements,
        &mut body_memo,
    )
    .map_err(|error| SolverError::Backend(error.to_string()))?;
    let fresh_negated = search_arena
        .not(fresh_body)
        .map_err(|error| SolverError::Backend(error.to_string()))?;

    let mut assertion_replacements = HashMap::new();
    assertion_replacements.insert(universal, search_arena.bool_const(true));
    let mut assertion_memo = HashMap::new();
    let fresh_assertion = replace_subterms(
        &mut search_arena,
        assertion,
        &assertion_replacements,
        &mut assertion_memo,
    )
    .map_err(|error| SolverError::Backend(error.to_string()))?;

    let mut searched = assertions.to_vec();
    for slot in &mut searched {
        if *slot == assertion {
            *slot = fresh_assertion;
            break;
        }
    }
    searched.push(fresh_negated);

    let search_config = config_with_deadline(config, deadline);
    let result = match check_auto(&mut search_arena, &searched, &search_config) {
        Ok(CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {
            crate::solve(&mut search_arena, &searched, &search_config)?
        }
        Ok(result) => result,
        Err(error) => return Err(error),
    };
    let CheckResult::Sat(model) = result else {
        return Ok(None);
    };

    let mut bindings = Vec::with_capacity(fresh.len());
    for (binder, fresh_symbol, sort) in fresh {
        let Some(value) = model
            .get(fresh_symbol)
            .or_else(|| well_founded_default(&search_arena, sort))
        else {
            return Ok(None);
        };
        bindings.push((binder, value));
    }
    try_candidate(
        arena, assertions, assertion, universal, admitted, &bindings, deadline,
    )
}

#[allow(clippy::too_many_arguments)]
fn try_candidate_unsat(
    arena: &TermArena,
    assertion: TermId,
    universal: TermId,
    admitted: &AdmittedConjunctiveUniversal,
    bindings: &[(axeyum_ir::SymbolId, Value)],
    deadline: Option<Instant>,
) -> Result<bool, SolverError> {
    let Some((scratch, residual)) =
        instantiate_conjunctive_universal(arena, assertion, universal, admitted, bindings)?
    else {
        return Ok(false);
    };
    let search_config = config_with_deadline(&SolverConfig::default(), deadline);
    let mut scratch = scratch;
    let result = match check_auto(&mut scratch, &[residual], &search_config) {
        Ok(result) => result,
        Err(SolverError::Unsupported(_)) => {
            crate::solve(&mut scratch, &[residual], &search_config)?
        }
        Err(error) => return Err(error),
    };
    match result {
        CheckResult::Unsat => Ok(true),
        CheckResult::Unknown(_) => Ok(matches!(
            crate::solve(&mut scratch, &[residual], &search_config)?,
            CheckResult::Unsat
        )),
        CheckResult::Sat(_) => Ok(false),
    }
}

#[allow(clippy::too_many_arguments)]
fn try_candidate_combinations(
    arena: &TermArena,
    assertions: &[TermId],
    assertion: TermId,
    universal: TermId,
    admitted: &AdmittedConjunctiveUniversal,
    defaults: &[(axeyum_ir::SymbolId, Value)],
    source_values: &[Value],
    deadline: Option<Instant>,
) -> Result<Option<BvConjunctiveUniversalInstanceCertificate>, SolverError> {
    let mut options: Vec<Vec<Value>> = Vec::with_capacity(admitted.binders.len());
    for (index, &binder) in admitted.binders.iter().enumerate() {
        let sort = arena.symbol(binder).1;
        let mut values: Vec<Value> = source_values
            .iter()
            .filter(|value| value.sort() == sort && **value != defaults[index].1)
            .take(4)
            .cloned()
            .collect();
        values.sort_by_key(value_sort_key);
        values.dedup();
        options.push(values);
    }

    let mut attempted = 0usize;
    let mut bindings = defaults.to_vec();
    try_candidate_combinations_rec(
        arena,
        assertions,
        assertion,
        universal,
        admitted,
        deadline,
        &mut attempted,
        &mut bindings,
        &options,
        0,
        0,
    )
}

#[allow(clippy::too_many_arguments)]
fn try_candidate_combinations_rec(
    arena: &TermArena,
    assertions: &[TermId],
    assertion: TermId,
    universal: TermId,
    admitted: &AdmittedConjunctiveUniversal,
    deadline: Option<Instant>,
    attempted: &mut usize,
    bindings: &mut [(axeyum_ir::SymbolId, Value)],
    options: &[Vec<Value>],
    depth: usize,
    changed: usize,
) -> Result<Option<BvConjunctiveUniversalInstanceCertificate>, SolverError> {
    if *attempted >= SEARCH_CANDIDATE_CAP || deadline.is_some_and(|end| Instant::now() >= end) {
        return Ok(None);
    }
    if depth == bindings.len() {
        if changed < 1 {
            return Ok(None);
        }
        *attempted += 1;
        return try_candidate(
            arena, assertions, assertion, universal, admitted, bindings, deadline,
        );
    }

    if let Some(certificate) = try_candidate_combinations_rec(
        arena,
        assertions,
        assertion,
        universal,
        admitted,
        deadline,
        attempted,
        bindings,
        options,
        depth + 1,
        changed,
    )? {
        return Ok(Some(certificate));
    }

    let original = bindings[depth].1.clone();
    for value in &options[depth] {
        bindings[depth].1 = value.clone();
        if let Some(certificate) = try_candidate_combinations_rec(
            arena,
            assertions,
            assertion,
            universal,
            admitted,
            deadline,
            attempted,
            bindings,
            options,
            depth + 1,
            changed + 1,
        )? {
            return Ok(Some(certificate));
        }
        if *attempted >= SEARCH_CANDIDATE_CAP {
            break;
        }
    }
    bindings[depth].1 = original;
    Ok(None)
}

#[allow(clippy::too_many_arguments)]
fn try_model_candidate_unsat(
    arena: &TermArena,
    assertions: &[TermId],
    assertion: TermId,
    universal: TermId,
    admitted: &AdmittedConjunctiveUniversal,
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<bool, SolverError> {
    let mut search_arena = arena.clone();
    let mut replacements = HashMap::new();
    let mut fresh = Vec::with_capacity(admitted.binders.len());
    let mut nonce = search_arena.symbols().count();
    for &binder in &admitted.binders {
        let sort = search_arena.symbol(binder).1;
        let fresh_symbol = loop {
            let name = format!(
                "!bv_conjunctive_search_{}_{}_{}",
                assertion.index(),
                binder.index(),
                nonce
            );
            nonce += 1;
            if search_arena.find_internal_symbol(&name).is_none() {
                break search_arena
                    .declare_internal(&name, sort)
                    .map_err(|error| SolverError::Backend(error.to_string()))?;
            }
        };
        replacements.insert(search_arena.var(binder), search_arena.var(fresh_symbol));
        fresh.push((binder, fresh_symbol, sort));
    }

    let mut body_memo = HashMap::new();
    let fresh_body = replace_subterms(
        &mut search_arena,
        admitted.body,
        &replacements,
        &mut body_memo,
    )
    .map_err(|error| SolverError::Backend(error.to_string()))?;
    let fresh_negated = search_arena
        .not(fresh_body)
        .map_err(|error| SolverError::Backend(error.to_string()))?;

    let mut assertion_replacements = HashMap::new();
    assertion_replacements.insert(universal, search_arena.bool_const(true));
    let mut assertion_memo = HashMap::new();
    let fresh_assertion = replace_subterms(
        &mut search_arena,
        assertion,
        &assertion_replacements,
        &mut assertion_memo,
    )
    .map_err(|error| SolverError::Backend(error.to_string()))?;

    let mut searched = assertions.to_vec();
    for slot in &mut searched {
        if *slot == assertion {
            *slot = fresh_assertion;
            break;
        }
    }
    searched.push(fresh_negated);

    let search_config = config_with_deadline(config, deadline);
    let result = match check_auto(&mut search_arena, &searched, &search_config) {
        Ok(CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {
            crate::solve(&mut search_arena, &searched, &search_config)?
        }
        Ok(result) => result,
        Err(error) => return Err(error),
    };
    match result {
        CheckResult::Unsat => Ok(true),
        CheckResult::Unknown(_) => Ok(matches!(
            crate::solve(&mut search_arena, &searched, &search_config)?,
            CheckResult::Unsat
        )),
        CheckResult::Sat(model) => {
            let mut bindings = Vec::with_capacity(fresh.len());
            for (binder, fresh_symbol, sort) in fresh {
                let Some(value) = model
                    .get(fresh_symbol)
                    .or_else(|| well_founded_default(&search_arena, sort))
                else {
                    return Ok(false);
                };
                bindings.push((binder, value));
            }
            if try_candidate_unsat(arena, assertion, universal, admitted, &bindings, deadline)? {
                return Ok(true);
            }

            let mut expanded_source_values = collect_source_values(arena, assertion);
            expanded_source_values
                .extend(collect_source_values_from_terms(&search_arena, &searched));
            expanded_source_values.extend(collect_model_values(&model));
            expanded_source_values.sort_by_key(value_sort_key);
            expanded_source_values.dedup();

            try_candidate_combinations_unsat(
                arena,
                assertions,
                assertion,
                universal,
                admitted,
                &bindings,
                &expanded_source_values,
                deadline,
            )
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn try_candidate_combinations_unsat(
    arena: &TermArena,
    assertions: &[TermId],
    assertion: TermId,
    universal: TermId,
    admitted: &AdmittedConjunctiveUniversal,
    defaults: &[(axeyum_ir::SymbolId, Value)],
    source_values: &[Value],
    deadline: Option<Instant>,
) -> Result<bool, SolverError> {
    let mut options: Vec<Vec<Value>> = Vec::with_capacity(admitted.binders.len());
    for (index, &binder) in admitted.binders.iter().enumerate() {
        let sort = arena.symbol(binder).1;
        let mut values: Vec<Value> = source_values
            .iter()
            .filter(|value| value.sort() == sort && **value != defaults[index].1)
            .take(4)
            .cloned()
            .collect();
        values.sort_by_key(value_sort_key);
        values.dedup();
        options.push(values);
    }

    let mut attempted = 0usize;
    let mut bindings = defaults.to_vec();
    try_candidate_combinations_unsat_rec(
        arena,
        assertions,
        assertion,
        universal,
        admitted,
        deadline,
        &mut attempted,
        &mut bindings,
        &options,
        0,
        0,
    )
}

#[allow(clippy::too_many_arguments)]
fn try_candidate_combinations_unsat_rec(
    arena: &TermArena,
    assertions: &[TermId],
    assertion: TermId,
    universal: TermId,
    admitted: &AdmittedConjunctiveUniversal,
    deadline: Option<Instant>,
    attempted: &mut usize,
    bindings: &mut [(axeyum_ir::SymbolId, Value)],
    options: &[Vec<Value>],
    depth: usize,
    changed: usize,
) -> Result<bool, SolverError> {
    if *attempted >= SEARCH_CANDIDATE_CAP || deadline.is_some_and(|end| Instant::now() >= end) {
        return Ok(false);
    }
    if depth == bindings.len() {
        if changed < 1 {
            return Ok(false);
        }
        *attempted += 1;
        return try_candidate_unsat(arena, assertion, universal, admitted, bindings, deadline);
    }

    if try_candidate_combinations_unsat_rec(
        arena,
        assertions,
        assertion,
        universal,
        admitted,
        deadline,
        attempted,
        bindings,
        options,
        depth + 1,
        changed,
    )? {
        return Ok(true);
    }

    let original = bindings[depth].1.clone();
    for value in &options[depth] {
        bindings[depth].1 = value.clone();
        if try_candidate_combinations_unsat_rec(
            arena,
            assertions,
            assertion,
            universal,
            admitted,
            deadline,
            attempted,
            bindings,
            options,
            depth + 1,
            changed + 1,
        )? {
            bindings[depth].1 = original;
            return Ok(true);
        }
        if *attempted >= SEARCH_CANDIDATE_CAP {
            break;
        }
    }
    bindings[depth].1 = original;
    Ok(false)
}

fn config_with_deadline(config: &SolverConfig, deadline: Option<Instant>) -> SolverConfig {
    let Some(deadline) = deadline else {
        return config.clone();
    };
    let mut out = config.clone();
    out.timeout = Some(deadline.saturating_duration_since(Instant::now()));
    out
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
    values.extend(bv_seed_values());
    values.sort_by_key(value_sort_key);
    values.dedup();

    let mut expanded = values.clone();
    for value in &values {
        for neighbour in bv_neighbours(value) {
            if !expanded.contains(&neighbour) {
                expanded.push(neighbour);
            }
        }
    }
    expanded.sort_by_key(value_sort_key);
    expanded.dedup();
    expanded
}

fn collect_source_values_from_terms(arena: &TermArena, assertions: &[TermId]) -> Vec<Value> {
    let mut values = Vec::new();
    for &assertion in assertions {
        values.extend(collect_source_values(arena, assertion));
    }
    values.sort_by_key(value_sort_key);
    values.dedup();
    values
}

fn collect_model_values(model: &Model) -> Vec<Value> {
    let mut values = model.iter().map(|(_, value)| value).collect::<Vec<_>>();
    values.sort_by_key(value_sort_key);
    values.dedup();
    let mut expanded = values.clone();
    for value in &values {
        for neighbour in bv_neighbours(value) {
            if !expanded.contains(&neighbour) {
                expanded.push(neighbour);
            }
        }
    }
    expanded.sort_by_key(value_sort_key);
    expanded.dedup();
    expanded
}

fn bv_neighbours(value: &Value) -> Vec<Value> {
    match value {
        Value::Bv { width, value } => {
            let mask = if *width == 128 {
                u128::MAX
            } else {
                (1u128 << *width) - 1
            };
            vec![
                Value::Bv {
                    width: *width,
                    value: value.wrapping_add(1) & mask,
                },
                Value::Bv {
                    width: *width,
                    value: value.wrapping_sub(1) & mask,
                },
                Value::Bv {
                    width: *width,
                    value: 0,
                },
                Value::Bv {
                    width: *width,
                    value: 1 & mask,
                },
                Value::Bv {
                    width: *width,
                    value: mask,
                },
                Value::Bv {
                    width: *width,
                    value: value.wrapping_add(2) & mask,
                },
                Value::Bv {
                    width: *width,
                    value: value.wrapping_sub(2) & mask,
                },
            ]
        }
        Value::WideBv(value) => {
            let width = value.width();
            let one = WideUint::from_u128(1, width);
            let two = WideUint::from_u128(2, width);
            vec![
                Value::WideBv(value.add(&one)),
                Value::WideBv(value.sub(&one)),
                Value::WideBv(WideUint::zero(width)),
                Value::WideBv(one),
                Value::WideBv(WideUint::ones(width)),
                Value::WideBv(value.add(&two)),
                Value::WideBv(value.sub(&two)),
            ]
        }
        _ => Vec::new(),
    }
}

fn bv_seed_values() -> Vec<Value> {
    vec![
        Value::Bv {
            width: 32,
            value: 0,
        },
        Value::Bv {
            width: 32,
            value: 1,
        },
        Value::Bv {
            width: 32,
            value: u128::from(u32::MAX),
        },
        Value::Bv {
            width: 32,
            value: u128::from(u32::MAX - 1),
        },
        Value::Bv {
            width: 32,
            value: 2,
        },
        Value::Bv {
            width: 32,
            value: u128::from(u32::MAX - 2),
        },
    ]
}

fn value_sort_key(value: &Value) -> (u8, u32, u128) {
    match value {
        Value::Bool(value) => (0, 0, u128::from(*value)),
        Value::Bv { width, value } => (1, *width, *value),
        Value::WideBv(value) => (2, value.width(), 0),
        _ => (3, 0, 0),
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use axeyum_smtlib::parse_script;

    use crate::{SolverConfig, check_auto};

    use super::{
        admitted_conjunctive_universal, admitted_conjunctive_universal_loose,
        conjunctive_universals, default_bindings, instantiate_conjunctive_universal,
    };

    #[test]
    fn psyco_107_bv_has_a_conjunctive_universal_candidate() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__psyco-107-bv.smt2",
        );
        let text = fs::read_to_string(path).expect("read psyco-107-bv");
        let script = parse_script(&text).expect("parse psyco-107-bv");
        let assertions = script.assertions;
        let mut found = Vec::new();
        for &assertion in &assertions {
            for universal in conjunctive_universals(&script.arena, assertion) {
                found.push((assertion, universal));
            }
        }
        assert!(
            !found.is_empty(),
            "psyco-107-bv should expose at least one universal candidate",
        );
        let (assertion, universal) = found[0];
        let admitted = admitted_conjunctive_universal(&script.arena, assertion, universal)
            .expect("candidate universal should admit");
        assert!(
            !admitted.binders.is_empty(),
            "candidate should carry at least one binder",
        );
        let _ = SolverConfig::default();
    }

    #[test]
    fn psyco_107_bv_default_residual_is_qf_sat() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__psyco-107-bv.smt2",
        );
        let text = fs::read_to_string(path).expect("read psyco-107-bv");
        let script = parse_script(&text).expect("parse psyco-107-bv");
        let assertion = script.assertions[0];
        let universal = conjunctive_universals(&script.arena, assertion)[0];
        let admitted = admitted_conjunctive_universal_loose(&script.arena, assertion, universal)
            .expect("loose candidate should admit");
        let defaults = default_bindings(&script.arena, &admitted);
        let (scratch, residual) = instantiate_conjunctive_universal(
            &script.arena,
            assertion,
            universal,
            &admitted,
            &defaults,
        )
        .expect("instantiate")
        .expect("default bindings should instantiate");
        assert!(
            conjunctive_universals(&scratch, residual).is_empty(),
            "default residual should be quantifier-free"
        );
        assert!(
            matches!(
                check_auto(&mut scratch.clone(), &[residual], &SolverConfig::default()),
                Ok(crate::CheckResult::Sat(_))
            ),
            "default residual should be satisfiable"
        );
    }

    #[test]
    fn smtcomp_qbv_053118_has_a_conjunctive_universal_candidate() {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__smtcomp-qbv-053118.smt2",
        );
        let text = fs::read_to_string(path).expect("read smtcomp-qbv-053118");
        let script = parse_script(&text).expect("parse smtcomp-qbv-053118");
        let assertions = script.assertions;
        let mut found = Vec::new();
        for &assertion in &assertions {
            for universal in conjunctive_universals(&script.arena, assertion) {
                found.push((assertion, universal));
            }
        }
        assert!(
            !found.is_empty(),
            "smtcomp-qbv-053118 should expose at least one universal candidate",
        );
        let (assertion, universal) = found[0];
        let admitted = admitted_conjunctive_universal(&script.arena, assertion, universal)
            .expect("candidate universal should admit");
        assert!(
            !admitted.binders.is_empty(),
            "candidate should carry at least one binder",
        );
        let _ = SolverConfig::default();
    }
}
