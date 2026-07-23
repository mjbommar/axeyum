//! Search-side bridge from MBQI candidates to checked quantified-UF models.
//!
//! The finite-profile proof lives in [`crate::quant_uf_model_sat_cert`], not in
//! this search adapter. A candidate receives SAT credit only when that separate
//! source checker accepts every original universal and returns one certificate
//! per assertion.

use std::collections::BTreeSet;

use axeyum_ir::{FuncId, FuncValue, Rational, Sort, TermArena, Value};

use crate::{Model, QuantifiedUfModelSatCertificate};

const DEFAULT_REPAIR_FUNCTION_CAP: usize = 8;
const DEFAULT_REPAIR_VALUE_CAP: usize = 32;
const DEFAULT_REPAIR_CANDIDATE_CAP: usize = 256;

/// Returns source-bound certificates when `model` is independently proved to
/// satisfy every universal in `assertions`; otherwise declines.
pub(crate) fn certify_all_universals(
    arena: &TermArena,
    assertions: &[axeyum_ir::TermId],
    model: &Model,
) -> Option<Vec<QuantifiedUfModelSatCertificate>> {
    if assertions.is_empty() {
        return None;
    }
    assertions
        .iter()
        .map(|&assertion| {
            crate::quant_uf_model_sat_cert::certify_quantified_uf_model_sat(arena, assertion, model)
        })
        .collect()
}

/// Searches a bounded set of alternative UF defaults and returns the first
/// candidate independently accepted for every exact source universal.
///
/// Existing scalar assignments and explicit function-table entries are copied
/// byte-for-byte; only total defaults change. This routine is untrusted search:
/// the returned certificates come from the independent finite-profile checker.
pub(crate) fn repair_and_certify_all_universals(
    arena: &TermArena,
    assertions: &[axeyum_ir::TermId],
    model: &Model,
) -> Option<(Model, Vec<QuantifiedUfModelSatCertificate>)> {
    if assertions.is_empty() {
        return None;
    }

    let mut functions = BTreeSet::new();
    for &assertion in assertions {
        functions.extend(
            crate::quant_uf_model_sat_cert::quantified_uf_model_functions(arena, assertion)?,
        );
    }
    if functions.is_empty() || functions.len() > DEFAULT_REPAIR_FUNCTION_CAP {
        return None;
    }

    let mut repairs = Vec::with_capacity(functions.len());
    let mut candidate_count = 1_usize;
    for function in functions {
        let (_, params, result) = arena.function(function);
        if !matches!(result, Sort::Int | Sort::Real) {
            return None;
        }
        if let Some(interpretation) = model.function(function)
            && (interpretation.params() != params
                || interpretation.result() != result
                || !interpretation.uses_value_storage())
        {
            return None;
        }
        let defaults = candidate_defaults(model, result)?;
        candidate_count = candidate_count.checked_mul(defaults.len())?;
        if candidate_count > DEFAULT_REPAIR_CANDIDATE_CAP {
            return None;
        }
        repairs.push((function, defaults));
    }

    search_default_repairs(arena, assertions, model, &repairs, 0)
}

fn candidate_defaults(model: &Model, result: Sort) -> Option<Vec<Value>> {
    let mut values = Vec::new();
    push_candidate(&mut values, zero_value(result)?)?;
    for (_, value) in model.iter() {
        if value.sort() == result {
            push_candidate(&mut values, value)?;
        }
    }
    for (_, interpretation) in model.functions() {
        if interpretation.result() != result || !interpretation.uses_value_storage() {
            continue;
        }
        push_candidate(&mut values, interpretation.default_value())?;
        for (_, value) in interpretation.value_entries() {
            push_candidate(&mut values, value.clone())?;
        }
    }

    let seeds = values.clone();
    for value in seeds {
        for neighbor in checked_neighbors(&value) {
            push_candidate(&mut values, neighbor)?;
        }
    }
    Some(values)
}

fn zero_value(sort: Sort) -> Option<Value> {
    match sort {
        Sort::Int => Some(Value::Int(0)),
        Sort::Real => Some(Value::Real(Rational::zero())),
        _ => None,
    }
}

fn checked_neighbors(value: &Value) -> Vec<Value> {
    match value {
        Value::Int(integer) => [integer.checked_sub(1), integer.checked_add(1)]
            .into_iter()
            .flatten()
            .map(Value::Int)
            .collect(),
        Value::Real(real) => {
            let one = Rational::integer(1);
            [real.checked_sub(one), real.checked_add(one)]
                .into_iter()
                .flatten()
                .map(Value::Real)
                .collect()
        }
        _ => Vec::new(),
    }
}

fn push_candidate(values: &mut Vec<Value>, value: Value) -> Option<()> {
    if values.contains(&value) {
        return Some(());
    }
    if values.len() >= DEFAULT_REPAIR_VALUE_CAP {
        return None;
    }
    values.push(value);
    Some(())
}

fn with_default(arena: &TermArena, model: &Model, function: FuncId, default: Value) -> FuncValue {
    let (_, params, result) = arena.function(function);
    let mut repaired = FuncValue::constant_value(params.to_vec(), result, default);
    if let Some(existing) = model.function(function) {
        for (arguments, value) in existing.value_entries() {
            repaired = repaired.define_value(arguments, value.clone());
        }
    }
    repaired
}

fn search_default_repairs(
    arena: &TermArena,
    assertions: &[axeyum_ir::TermId],
    model: &Model,
    repairs: &[(FuncId, Vec<Value>)],
    index: usize,
) -> Option<(Model, Vec<QuantifiedUfModelSatCertificate>)> {
    if index == repairs.len() {
        let certificates = certify_all_universals(arena, assertions, model)?;
        return Some((model.clone(), certificates));
    }

    let (function, defaults) = &repairs[index];
    for default in defaults {
        let mut candidate = model.clone();
        candidate.set_function(
            *function,
            with_default(arena, model, *function, default.clone()),
        );
        if let Some(repaired) =
            search_default_repairs(arena, assertions, &candidate, repairs, index + 1)
        {
            return Some(repaired);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::TermId;

    fn many_function_universal(arena: &mut TermArena, count: usize) -> TermId {
        let binder = arena.declare("x", Sort::Int).unwrap();
        let x = arena.var(binder);
        let zero = arena.int_const(0);
        let mut atoms = Vec::new();
        for index in 0..count {
            let function = arena
                .declare_fun(&format!("f{index}"), &[Sort::Int], Sort::Int)
                .unwrap();
            let application = arena.apply(function, &[x]).unwrap();
            atoms.push(arena.int_ge(application, zero).unwrap());
        }
        let mut body = atoms[0];
        for &atom in &atoms[1..] {
            body = arena.and(body, atom).unwrap();
        }
        arena.forall(binder, body).unwrap()
    }

    #[test]
    fn function_and_cartesian_caps_decline() {
        let mut arena = TermArena::new();
        let six_functions = many_function_universal(&mut arena, 6);
        assert!(
            repair_and_certify_all_universals(&arena, &[six_functions], &Model::new()).is_none(),
            "3^6 default combinations must exceed the 256-candidate cap"
        );

        let mut arena = TermArena::new();
        let nine_functions = many_function_universal(&mut arena, 9);
        assert!(
            repair_and_certify_all_universals(&arena, &[nine_functions], &Model::new()).is_none(),
            "nine relevant functions must exceed the explicit function cap"
        );
    }

    #[test]
    fn oversized_value_pool_declines() {
        let mut arena = TermArena::new();
        let universal = many_function_universal(&mut arena, 1);
        let mut model = Model::new();
        for index in 0..DEFAULT_REPAIR_VALUE_CAP {
            let symbol = arena.declare(&format!("y{index}"), Sort::Int).unwrap();
            model.set(symbol, Value::Int(i128::try_from(index + 10).unwrap()));
        }
        assert!(repair_and_certify_all_universals(&arena, &[universal], &model).is_none());
    }

    #[test]
    fn unsupported_result_sort_declines() {
        let mut arena = TermArena::new();
        let predicate = arena.declare_fun("p", &[Sort::Int], Sort::Bool).unwrap();
        let binder = arena.declare("x", Sort::Int).unwrap();
        let x = arena.var(binder);
        let body = arena.apply(predicate, &[x]).unwrap();
        let universal = arena.forall(binder, body).unwrap();
        assert!(repair_and_certify_all_universals(&arena, &[universal], &Model::new()).is_none());
    }

    #[test]
    fn neighbor_generation_is_overflow_safe() {
        let mut arena = TermArena::new();
        let universal = many_function_universal(&mut arena, 1);
        let symbol = arena.declare("limit", Sort::Int).unwrap();
        let mut model = Model::new();
        model.set(symbol, Value::Int(i128::MAX));
        assert!(repair_and_certify_all_universals(&arena, &[universal], &model).is_some());
    }
}
