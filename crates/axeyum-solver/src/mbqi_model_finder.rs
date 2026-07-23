//! Search-side bridge from MBQI candidates to checked quantified-UF models.
//!
//! The finite-profile proof lives in [`crate::quant_uf_model_sat_cert`], not in
//! this search adapter. A candidate receives SAT credit only when that separate
//! source checker accepts every original universal and returns one certificate
//! per assertion.

use std::{
    collections::{BTreeMap, BTreeSet},
    time::Instant,
};

use axeyum_ir::{FuncId, FuncValue, Rational, Sort, TermArena, TermId, TermNode, Value, eval};

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

/// Adds exact-source integer values to ADR-0359's default candidates for one
/// bounded, deadline-aware retry. This remains untrusted search: all returned
/// universals are independently certified from the repaired model.
pub(crate) fn repair_and_certify_all_universals_with_source_int_values(
    arena: &TermArena,
    source_assertions: &[TermId],
    universal_assertions: &[TermId],
    model: &Model,
    deadline: Option<Instant>,
) -> Option<(Model, Vec<QuantifiedUfModelSatCertificate>)> {
    if universal_assertions.is_empty() || deadline_expired(deadline) {
        return None;
    }

    let mut functions = BTreeSet::new();
    for &assertion in universal_assertions {
        functions.extend(
            crate::quant_uf_model_sat_cert::quantified_uf_model_functions(arena, assertion)?,
        );
    }
    if functions.is_empty() || functions.len() > DEFAULT_REPAIR_FUNCTION_CAP {
        return None;
    }

    let values = source_guided_int_defaults(arena, source_assertions, model)?;
    let baseline = candidate_defaults(model, Sort::Int)?;
    if same_value_set(&values, &baseline) {
        return None;
    }

    let mut repairs = Vec::with_capacity(functions.len());
    let mut candidate_count = 1_usize;
    for function in functions {
        let (_, params, result) = arena.function(function);
        if result != Sort::Int {
            return None;
        }
        if let Some(interpretation) = model.function(function)
            && (interpretation.params() != params
                || interpretation.result() != result
                || !interpretation.uses_value_storage())
        {
            return None;
        }
        candidate_count = candidate_count.checked_mul(values.len())?;
        if candidate_count > DEFAULT_REPAIR_CANDIDATE_CAP {
            return None;
        }
        repairs.push((function, values.clone()));
    }

    search_source_default_repairs(arena, universal_assertions, model, &repairs, 0, deadline)
}

/// Completes one untrusted candidate for ADR-0364's single-`Int`-binder
/// finite-profile loop.
///
/// Missing source functions receive a zero default so the profile is
/// evaluable. An exact top-level conjunct `f(binder) = ground_term` may then
/// propose the corresponding total constant function. Neither operation is
/// evidence; callers must independently certify and replay the returned model.
pub(crate) fn complete_profile_guided_int_candidate(
    arena: &TermArena,
    assertion: TermId,
    model: &Model,
) -> Option<Model> {
    let TermNode::App {
        op: axeyum_ir::Op::Forall(binder),
        args,
    } = arena.node(assertion)
    else {
        return None;
    };
    let [body] = &**args else {
        return None;
    };
    if arena.symbol(*binder).1 != Sort::Int
        || matches!(
            arena.node(*body),
            TermNode::App {
                op: axeyum_ir::Op::Forall(_),
                ..
            }
        )
    {
        return None;
    }

    let functions =
        crate::quant_uf_model_sat_cert::quantified_uf_model_functions(arena, assertion)?;
    let mut completed = model.clone();
    for function in functions {
        let (_, params, result) = arena.function(function);
        if result != Sort::Int || params.iter().any(|sort| *sort != Sort::Int) {
            return None;
        }
        if let Some(interpretation) = completed.function(function) {
            if interpretation.params() != params
                || interpretation.result() != result
                || !interpretation.uses_value_storage()
            {
                return None;
            }
        } else {
            completed.set_function(
                function,
                FuncValue::constant_value(params.to_vec(), result, Value::Int(0)),
            );
        }
    }

    let definitions = constant_int_function_definitions(arena, *body, *binder);
    for (function, value_term) in definitions {
        let value = eval(arena, value_term, &completed.to_assignment()).ok()?;
        let Value::Int(_) = value else {
            return None;
        };
        let (_, params, result) = arena.function(function);
        completed.set_function(
            function,
            FuncValue::constant_value(params.to_vec(), result, value),
        );
    }
    Some(completed)
}

fn constant_int_function_definitions(
    arena: &TermArena,
    body: TermId,
    binder: axeyum_ir::SymbolId,
) -> Vec<(FuncId, TermId)> {
    fn depends_on_symbol(
        arena: &TermArena,
        term: TermId,
        symbol: axeyum_ir::SymbolId,
        memo: &mut BTreeMap<TermId, bool>,
    ) -> bool {
        if let Some(depends) = memo.get(&term) {
            return *depends;
        }
        let depends = match arena.node(term) {
            TermNode::Symbol(candidate) => *candidate == symbol,
            TermNode::App { args, .. } => args
                .iter()
                .any(|&argument| depends_on_symbol(arena, argument, symbol, memo)),
            _ => false,
        };
        memo.insert(term, depends);
        depends
    }

    fn direct_binder_application(
        arena: &TermArena,
        term: TermId,
        binder: axeyum_ir::SymbolId,
    ) -> Option<FuncId> {
        let TermNode::App {
            op: axeyum_ir::Op::Apply(function),
            args,
        } = arena.node(term)
        else {
            return None;
        };
        let [argument] = &**args else {
            return None;
        };
        matches!(arena.node(*argument), TermNode::Symbol(symbol) if *symbol == binder)
            .then_some(*function)
    }

    let mut definitions = Vec::new();
    let mut dependency_memo = BTreeMap::new();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        match op {
            axeyum_ir::Op::BoolAnd => stack.extend(args.iter().rev().copied()),
            axeyum_ir::Op::Eq => {
                let [left, right] = &**args else {
                    continue;
                };
                let definition = direct_binder_application(arena, *left, binder)
                    .filter(|_| !depends_on_symbol(arena, *right, binder, &mut dependency_memo))
                    .map(|function| (function, *right))
                    .or_else(|| {
                        direct_binder_application(arena, *right, binder)
                            .filter(|_| {
                                !depends_on_symbol(arena, *left, binder, &mut dependency_memo)
                            })
                            .map(|function| (function, *left))
                    });
                if let Some(definition) = definition
                    && !definitions.contains(&definition)
                {
                    definitions.push(definition);
                }
            }
            _ => {}
        }
    }
    definitions
}

fn same_value_set(left: &[Value], right: &[Value]) -> bool {
    left.len() == right.len() && left.iter().all(|value| right.contains(value))
}

fn source_guided_int_defaults(
    arena: &TermArena,
    assertions: &[TermId],
    model: &Model,
) -> Option<Vec<Value>> {
    let mut values = BTreeSet::from([0_i128]);
    for (_, value) in model.iter() {
        if let Value::Int(integer) = value {
            values.insert(integer);
        }
    }
    for (_, interpretation) in model.functions() {
        if interpretation.result() != Sort::Int || !interpretation.uses_value_storage() {
            continue;
        }
        if let Value::Int(integer) = interpretation.default_value() {
            values.insert(integer);
        }
        for (_, value) in interpretation.value_entries() {
            if let Value::Int(integer) = value {
                values.insert(*integer);
            }
        }
    }

    let mut seen = BTreeSet::new();
    let mut visit_order = Vec::new();
    let mut binders = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        visit_order.push(term);
        match arena.node(term) {
            TermNode::IntConst(integer) => {
                values.insert(*integer);
            }
            TermNode::App { op, args } => {
                if let axeyum_ir::Op::Forall(symbol) | axeyum_ir::Op::Exists(symbol) = op {
                    binders.insert(*symbol);
                }
                stack.extend(args.iter().rev().copied());
            }
            _ => {}
        }
    }

    let assignment = model.to_assignment();
    let mut binder_dependent = BTreeSet::new();
    for term in visit_order.into_iter().rev() {
        let depends_on_binder = match arena.node(term) {
            TermNode::Symbol(symbol) => binders.contains(symbol),
            TermNode::App { args, .. } => args.iter().any(|arg| binder_dependent.contains(arg)),
            _ => false,
        };
        if depends_on_binder {
            binder_dependent.insert(term);
        } else if arena.sort_of(term) == Sort::Int
            && let Ok(Value::Int(integer)) = eval(arena, term, &assignment)
        {
            values.insert(integer);
        }
    }

    let bases: Vec<i128> = values.iter().copied().collect();
    for base in bases {
        if let Some(predecessor) = base.checked_sub(1) {
            values.insert(predecessor);
        }
        if let Some(successor) = base.checked_add(1) {
            values.insert(successor);
        }
    }
    if values.len() > DEFAULT_REPAIR_VALUE_CAP {
        return None;
    }
    Some(values.into_iter().map(Value::Int).collect())
}

fn deadline_expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|deadline| Instant::now() >= deadline)
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

fn search_source_default_repairs(
    arena: &TermArena,
    assertions: &[axeyum_ir::TermId],
    model: &Model,
    repairs: &[(FuncId, Vec<Value>)],
    index: usize,
    deadline: Option<Instant>,
) -> Option<(Model, Vec<QuantifiedUfModelSatCertificate>)> {
    if deadline_expired(deadline) {
        return None;
    }
    if index == repairs.len() {
        let certificates = certify_all_universals(arena, assertions, model)?;
        if deadline_expired(deadline) {
            return None;
        }
        return Some((model.clone(), certificates));
    }

    let (function, defaults) = &repairs[index];
    for default in defaults {
        if deadline_expired(deadline) {
            return None;
        }
        let mut candidate = model.clone();
        candidate.set_function(
            *function,
            with_default(arena, model, *function, default.clone()),
        );
        if let Some(repaired) = search_source_default_repairs(
            arena,
            assertions,
            &candidate,
            repairs,
            index + 1,
            deadline,
        ) {
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

    #[test]
    fn source_guided_int_values_include_ground_terms_but_not_binder_terms() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("source_guided_f", &[Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("source_guided_x", Sort::Int).unwrap();
        let scalar = arena.declare("source_guided_y", Sort::Int).unwrap();
        let binder_variable = arena.var(binder);
        let scalar_variable = arena.var(scalar);
        let three = arena.int_const(3);
        let four = arena.int_const(4);
        let binder_product = arena.int_mul(binder_variable, three).unwrap();
        let binder_application = arena.apply(function, &[binder_variable]).unwrap();
        let universal_body = arena.eq(binder_product, binder_application).unwrap();
        let universal = arena.forall(binder, universal_body).unwrap();
        let ground_product = arena.int_mul(scalar_variable, four).unwrap();
        let ground_application = arena.apply(function, &[scalar_variable]).unwrap();
        let ground = arena.int_le(ground_product, ground_application).unwrap();

        let interpretation = FuncValue::constant_value(vec![Sort::Int], Sort::Int, Value::Int(5))
            .define_value(&[Value::Int(2)], Value::Int(9));
        let mut model = Model::new();
        model.set(binder, Value::Int(100));
        model.set(scalar, Value::Int(2));
        model.set_function(function, interpretation);

        assert_eq!(
            source_guided_int_defaults(&arena, &[universal, ground], &model),
            Some(
                [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 99, 100, 101]
                    .into_iter()
                    .map(Value::Int)
                    .collect()
            )
        );
        assert!(
            !source_guided_int_defaults(&arena, &[universal, ground], &model)
                .unwrap()
                .contains(&Value::Int(300)),
            "the binder-dependent product must not become a source candidate"
        );
    }

    #[test]
    fn source_guided_repair_preserves_entries_and_honors_deadline() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("source_guided_entry_f", &[Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("source_guided_entry_x", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let application = arena.apply(function, &[variable]).unwrap();
        let four = arena.int_const(4);
        let body = arena.eq(application, four).unwrap();
        let universal = arena.forall(binder, body).unwrap();
        let seven = arena.int_const(7);
        let at_seven = arena.apply(function, &[seven]).unwrap();
        let ground = arena.eq(at_seven, four).unwrap();

        let interpretation = FuncValue::constant_value(vec![Sort::Int], Sort::Int, Value::Int(0))
            .define_value(&[Value::Int(7)], Value::Int(4));
        let mut model = Model::new();
        model.set_function(function, interpretation);

        let (repaired, certificates) = repair_and_certify_all_universals_with_source_int_values(
            &arena,
            &[universal, ground],
            &[universal],
            &model,
            None,
        )
        .expect("the exact source constant must repair the total default");
        assert_eq!(certificates.len(), 1);
        let repaired_function = repaired.function(function).unwrap();
        assert_eq!(repaired_function.default_value(), Value::Int(4));
        assert_eq!(
            repaired_function.apply_value(&[Value::Int(7)]),
            Value::Int(4)
        );
        assert!(
            repair_and_certify_all_universals_with_source_int_values(
                &arena,
                &[universal, ground],
                &[universal],
                &model,
                Some(Instant::now()),
            )
            .is_none()
        );
    }

    #[test]
    fn source_guided_repair_declines_over_cartesian_cap() {
        let mut arena = TermArena::new();
        let first = arena
            .declare_fun("source_guided_cap_f", &[Sort::Int], Sort::Int)
            .unwrap();
        let second = arena
            .declare_fun("source_guided_cap_g", &[Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("source_guided_cap_x", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let first_application = arena.apply(first, &[variable]).unwrap();
        let second_application = arena.apply(second, &[variable]).unwrap();
        let body = arena.eq(first_application, second_application).unwrap();
        let universal = arena.forall(binder, body).unwrap();
        let mut assertions = vec![universal];
        for value in (0_i128..=15).step_by(3) {
            let constant = arena.int_const(value);
            assertions.push(arena.eq(constant, constant).unwrap());
        }

        assert!(
            repair_and_certify_all_universals_with_source_int_values(
                &arena,
                &assertions,
                &[universal],
                &Model::new(),
                None,
            )
            .is_none(),
            "a source pool wider than 16 values over two functions must exceed 256 tuples"
        );

        let mut unsupported_arena = TermArena::new();
        let predicate = unsupported_arena
            .declare_fun("source_guided_bool", &[Sort::Int], Sort::Bool)
            .unwrap();
        let binder = unsupported_arena
            .declare("source_guided_bool_x", Sort::Int)
            .unwrap();
        let variable = unsupported_arena.var(binder);
        let body = unsupported_arena.apply(predicate, &[variable]).unwrap();
        let universal = unsupported_arena.forall(binder, body).unwrap();
        assert!(
            repair_and_certify_all_universals_with_source_int_values(
                &unsupported_arena,
                &[universal],
                &[universal],
                &Model::new(),
                None,
            )
            .is_none(),
            "the source-guided increment is Int-result-only"
        );
    }

    #[test]
    fn profile_completion_applies_exact_constant_definition_and_clears_entries() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("profile_constant_f", &[Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("profile_constant_x", Sort::Int).unwrap();
        let scalar = arena.declare("profile_constant_y", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let scalar_variable = arena.var(scalar);
        let application = arena.apply(function, &[variable]).unwrap();
        let body = arena.eq(application, scalar_variable).unwrap();
        let universal = arena.forall(binder, body).unwrap();

        let interpretation = FuncValue::constant_value(vec![Sort::Int], Sort::Int, Value::Int(8))
            .define_value(&[Value::Int(2)], Value::Int(9));
        let mut model = Model::new();
        model.set(scalar, Value::Int(-3));
        model.set_function(function, interpretation);

        let completed = complete_profile_guided_int_candidate(&arena, universal, &model)
            .expect("the exact source definition must produce a candidate");
        assert_eq!(completed.get(scalar), Some(Value::Int(-3)));
        let completed_function = completed.function(function).unwrap();
        assert_eq!(completed_function.default_value(), Value::Int(-3));
        assert_eq!(completed_function.value_entries().count(), 0);
    }

    #[test]
    fn profile_completion_does_not_treat_binder_dependent_equality_as_definition() {
        let mut arena = TermArena::new();
        let first = arena
            .declare_fun("profile_dependent_f", &[Sort::Int], Sort::Int)
            .unwrap();
        let second = arena
            .declare_fun("profile_dependent_g", &[Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("profile_dependent_x", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let first_application = arena.apply(first, &[variable]).unwrap();
        let second_application = arena.apply(second, &[variable]).unwrap();
        let body = arena.eq(first_application, second_application).unwrap();
        let universal = arena.forall(binder, body).unwrap();

        let interpretation = FuncValue::constant_value(vec![Sort::Int], Sort::Int, Value::Int(4))
            .define_value(&[Value::Int(2)], Value::Int(7));
        let mut model = Model::new();
        model.set_function(first, interpretation.clone());
        model.set_function(second, interpretation);

        let completed = complete_profile_guided_int_candidate(&arena, universal, &model)
            .expect("the supported profile must remain evaluable");
        assert_eq!(
            completed.function(first).unwrap().value_entries().count(),
            1,
            "a binder-dependent equality must not clear explicit entries"
        );
    }

    #[test]
    fn profile_completion_declines_non_int_and_multiple_binder_profiles() {
        let mut bool_result_arena = TermArena::new();
        let predicate = bool_result_arena
            .declare_fun("profile_bool_result_p", &[Sort::Int], Sort::Bool)
            .unwrap();
        let binder = bool_result_arena
            .declare("profile_bool_result_x", Sort::Int)
            .unwrap();
        let variable = bool_result_arena.var(binder);
        let body = bool_result_arena.apply(predicate, &[variable]).unwrap();
        let universal = bool_result_arena.forall(binder, body).unwrap();
        assert!(
            complete_profile_guided_int_candidate(&bool_result_arena, universal, &Model::new())
                .is_none(),
            "Bool-result functions are outside the Int-only profile"
        );

        let mut real_binder_arena = TermArena::new();
        let binder = real_binder_arena
            .declare("profile_real_binder_x", Sort::Real)
            .unwrap();
        let body = real_binder_arena.bool_const(true);
        let universal = real_binder_arena.forall(binder, body).unwrap();
        assert!(
            complete_profile_guided_int_candidate(&real_binder_arena, universal, &Model::new())
                .is_none(),
            "Real binders are outside the single-Int-binder profile"
        );

        let mut multiple_binder_arena = TermArena::new();
        let outer = multiple_binder_arena
            .declare("profile_multiple_outer", Sort::Int)
            .unwrap();
        let inner = multiple_binder_arena
            .declare("profile_multiple_inner", Sort::Int)
            .unwrap();
        let body = multiple_binder_arena.bool_const(true);
        let inner_universal = multiple_binder_arena.forall(inner, body).unwrap();
        let universal = multiple_binder_arena
            .forall(outer, inner_universal)
            .unwrap();
        assert!(
            complete_profile_guided_int_candidate(&multiple_binder_arena, universal, &Model::new())
                .is_none(),
            "nested universal binders must not enter the single-binder profile"
        );
    }
}
