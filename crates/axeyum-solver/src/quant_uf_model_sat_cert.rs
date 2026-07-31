//! Checked finite-profile models for the almost-uninterpreted quantified fragment.
//!
//! MBQI search is not evidence. This module independently checks one exact
//! source assertion against the returned total uninterpreted-function model.
//! Unsupported shapes decline rather than sampling an infinite domain.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{
    Assignment, FuncId, Op, Rational, Sort, SortId, SymbolId, TermArena, TermId, TermNode, Value,
    eval,
};

use crate::Model;

/// Maximum number of finite-profile tuples checked for one universal prefix.
pub const QUANTIFIED_UF_PROFILE_CAP: usize = 4096;

/// Maximum number of binders in one checked universal prefix.
pub const QUANTIFIED_UF_BINDER_CAP: usize = 16;

/// Source binding for one checked almost-uninterpreted universal model.
///
/// The function interpretation itself lives in [`Model`]. The checker trusts
/// neither a search-generated candidate list nor any derived profile metadata:
/// it reconstructs the complete finite representative set from `assertion` and
/// the model's finite function tables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedUfModelSatCertificate {
    /// Exact original quantified assertion covered by this certificate.
    pub assertion: TermId,
    /// Exact outer source binder, redundantly recorded so stale/tampered
    /// certificates fail closed before finite-profile evaluation. The assertion
    /// itself binds the complete leading prefix.
    pub binder: SymbolId,
}

/// Checks an almost-uninterpreted quantified-UF model against one exact source
/// assertion.
///
/// Accepted assertions have shape `forall x1 ... xn. body`, where every binder
/// is `Int` or `Real`, `body` is quantifier-free, and every binder occurrence is
/// a direct argument of an uninterpreted-function application. For every exact
/// argument position occupied by each binder, the checker derives all
/// corresponding finite-table key components plus one value outside the finite
/// set. The Cartesian product of those representative sets exhausts every
/// possible table/default profile.
#[must_use]
pub fn check_quantified_uf_model_sat(
    arena: &TermArena,
    assertion: TermId,
    model: &Model,
    certificate: &QuantifiedUfModelSatCertificate,
) -> bool {
    if certificate.assertion != assertion {
        return false;
    }
    // Finite-carrier route (pure uninterpreted domains): when every binder in
    // the assertion ranges over an uninterpreted sort and the model declares a
    // finite carrier for each, the assertion is checked exhaustively over the
    // canonical token domains. `Some(verdict)` is final; `None` falls through
    // to the established `Int`/`Real` finite-profile route unchanged.
    if let Some(verdict) =
        check_finite_uninterpreted_domains(arena, assertion, model, certificate.binder)
    {
        return verdict;
    }
    let Some((binders, body)) = universal_prefix(arena, assertion) else {
        return false;
    };
    if binders[0] != certificate.binder {
        return false;
    }

    if let [binder] = binders.as_slice()
        && check_vacuous_unary_uf_guard(arena, body, *binder, model)
    {
        return true;
    }

    let mut binder_representatives = Vec::with_capacity(binders.len());
    let mut profile_count = 1_usize;
    for &binder in &binders {
        let binder_sort = arena.symbol(binder).1;
        if !matches!(binder_sort, Sort::Int | Sort::Real) {
            return false;
        }
        let Some(positions) = relevant_function_positions(arena, body, binder) else {
            return false;
        };
        if positions.is_empty() {
            return false;
        }
        let Some(representatives) =
            representatives_for_binder(arena, model, binder_sort, &positions)
        else {
            return false;
        };
        let Some(next_count) = profile_count.checked_mul(representatives.len()) else {
            return false;
        };
        if next_count > QUANTIFIED_UF_PROFILE_CAP {
            return false;
        }
        profile_count = next_count;
        binder_representatives.push(representatives);
    }

    let assignment = model.to_assignment();
    let mut cloned = arena.clone();
    let binder_terms: Vec<_> = binders.iter().map(|&binder| cloned.var(binder)).collect();
    let mut representative_terms = Vec::with_capacity(binder_representatives.len());
    for representatives in &binder_representatives {
        let Some(terms) = representatives
            .iter()
            .map(|value| value_to_const(&mut cloned, value))
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        representative_terms.push(terms);
    }
    check_profile_product(
        &mut cloned,
        body,
        &binder_terms,
        &representative_terms,
        0,
        &mut HashMap::new(),
        &assignment,
    )
}

fn universal_prefix(arena: &TermArena, assertion: TermId) -> Option<(Vec<SymbolId>, TermId)> {
    let mut binders = Vec::new();
    let mut matrix = assertion;
    while let TermNode::App {
        op: Op::Forall(binder),
        args,
    } = arena.node(matrix)
    {
        let [body] = &**args else {
            return None;
        };
        if binders.contains(binder) || binders.len() >= QUANTIFIED_UF_BINDER_CAP {
            return None;
        }
        binders.push(*binder);
        matrix = *body;
    }
    if binders.is_empty() || contains_quantifier(arena, matrix) {
        return None;
    }
    Some((binders, matrix))
}

/// Exhaustively checks a quantified assertion whose binders all range over
/// **uninterpreted sorts with model-declared finite carriers** (finite model
/// finding, pure UF).
///
/// Returns `None` only when this route does not apply (the top node is not a
/// quantifier, or some binder ranges over a non-uninterpreted sort) so the
/// established `Int`/`Real` finite-profile route keeps its exact behavior.
/// Everything else is a final verdict, and every failure mode is closed:
///
/// * a binder whose sort has **no recorded cardinality** fails;
/// * a model carrying any uninterpreted token `>= k` for a recorded sort fails
///   (the model would not be a genuine structure on the declared carrier, and
///   quantifier enumeration over `0..k` would not be exact — the wrong-`sat`
///   hole);
/// * exceeding the profile/binder caps fails;
/// * any evaluation error or non-Boolean result fails.
///
/// With the closure check passed, the model **is** a finite structure whose
/// carrier for each recorded sort is exactly `0..k`, so `forall` is a finite
/// conjunction and `exists` a finite disjunction over those tokens — the
/// evaluation below is the exact truth value of the assertion in that
/// structure. Both quantifier polarities and arbitrary nesting are handled.
fn check_finite_uninterpreted_domains(
    arena: &TermArena,
    assertion: TermId,
    model: &Model,
    outer_binder: SymbolId,
) -> Option<bool> {
    // Route applicability: the assertion contains at least one
    // uninterpreted-sorted binder (its quantifiers may sit anywhere in the
    // Boolean structure — the expansion and this check are polarity-exact, so
    // quantifiers under negation are fine), and every binder is
    // uninterpreted- or `Bool`-sorted (`Bool` is the fixed two-element
    // carrier). Any other binder sort defers to the established routes.
    let binders = collect_all_binders(arena, assertion);
    if !binders
        .iter()
        .any(|&b| matches!(arena.symbol(b).1, Sort::Uninterpreted(_)))
        || binders
            .iter()
            .any(|&b| !matches!(arena.symbol(b).1, Sort::Uninterpreted(_) | Sort::Bool))
    {
        return None;
    }
    // From here on every outcome is final: fail closed. The redundant
    // source-binding check: the certificate must name the first binder of the
    // assertion (its outer binder when the assertion is a quantifier, the
    // deterministic first-visited binder otherwise).
    if binders[0] != outer_binder || binders.len() > QUANTIFIED_UF_BINDER_CAP {
        return Some(false);
    }
    let mut cardinalities: BTreeMap<SortId, u32> = BTreeMap::new();
    for &b in &binders {
        match arena.symbol(b).1 {
            Sort::Uninterpreted(sort) => {
                let Some(k) = model.uninterpreted_cardinality(sort) else {
                    // A binder over a carrier the model does not declare
                    // finite cannot be enumerated: fail closed.
                    return Some(false);
                };
                if k == 0 {
                    return Some(false);
                }
                cardinalities.insert(sort, k);
            }
            Sort::Bool => {}
            _ => return Some(false),
        }
    }
    // Model closure: every uninterpreted token the model carries for a
    // recorded sort must lie inside the declared carrier `0..k` — otherwise
    // the model is not a structure on that carrier and enumeration would be
    // unsound.
    if !model_closed_over_declared_carriers(model) {
        return Some(false);
    }
    let assignment = model.to_assignment();
    let mut budget = QUANTIFIED_UF_PROFILE_CAP;
    match eval_finite_uninterpreted(arena, assertion, &cardinalities, &assignment, &mut budget) {
        Some(verdict) => Some(verdict),
        None => Some(false),
    }
}

/// Every binder symbol of every quantifier reachable from `root`, in
/// deterministic first-visit order.
fn collect_all_binders(arena: &TermArena, root: TermId) -> Vec<SymbolId> {
    let mut binders = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if let Op::Forall(binder) | Op::Exists(binder) = op
                && !binders.contains(binder)
            {
                binders.push(*binder);
            }
            stack.extend(args.iter().copied());
        }
    }
    binders
}

/// Whether every [`Value::Uninterpreted`] token the model carries (symbol
/// values, function defaults, and function table keys/results) for a sort with
/// a **declared** cardinality `k` is `< k`. Sorts without a declared
/// cardinality are unconstrained (no quantifier enumerates them).
fn model_closed_over_declared_carriers(model: &Model) -> bool {
    let closed_value = |value: &Value| match value {
        Value::Uninterpreted { sort, value } => model
            .uninterpreted_cardinality(*sort)
            .is_none_or(|k| *value < u128::from(k)),
        _ => true,
    };
    if !model.iter().all(|(_, value)| closed_value(&value)) {
        return false;
    }
    for (_, interpretation) in model.functions() {
        if !closed_value(&interpretation.default_value()) {
            return false;
        }
        if interpretation.uses_value_storage() {
            for (key, result) in interpretation.value_entries() {
                if !key.iter().all(&closed_value) || !closed_value(result) {
                    return false;
                }
            }
        } else {
            let params = interpretation.params().to_vec();
            let result_sort = interpretation.result();
            for (key, result) in interpretation.entries() {
                if key.len() != params.len() {
                    return false;
                }
                for (&sort, &code) in params.iter().zip(key) {
                    if !closed_value(&Value::from_scalar_code(sort, code)) {
                        return false;
                    }
                }
                if !closed_value(&Value::from_scalar_code(result_sort, result)) {
                    return false;
                }
            }
        }
    }
    true
}

/// Exact finite evaluation of a Boolean term whose quantifiers all range over
/// declared finite uninterpreted carriers. `forall` is a conjunction and
/// `exists` a disjunction over the canonical tokens `0..k`; quantifier-free
/// subtrees delegate to the ground evaluator. `None` is a closed failure
/// (budget exhausted, unsupported shape, or evaluation error).
///
/// Each quantifier binding evaluates its body under a **cloned** assignment
/// (the same discipline as the trust-anchor evaluator's `eval_quantifier`), so
/// a binder can never leak a stale value into an enclosing scope — shadowed
/// binders and symbols occurring both free and bound stay exact.
#[allow(clippy::too_many_lines, reason = "one structural match per operator")]
fn eval_finite_uninterpreted(
    arena: &TermArena,
    term: TermId,
    cardinalities: &BTreeMap<SortId, u32>,
    assignment: &Assignment,
    budget: &mut usize,
) -> Option<bool> {
    if !contains_quantifier(arena, term) {
        *budget = budget.checked_sub(1)?;
        return match eval(arena, term, assignment) {
            Ok(Value::Bool(value)) => Some(value),
            _ => None,
        };
    }
    let TermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    match op {
        Op::Forall(binder) | Op::Exists(binder) => {
            let is_forall = matches!(op, Op::Forall(_));
            let [body] = &**args else {
                return None;
            };
            let carrier: Vec<Value> = match arena.symbol(*binder).1 {
                Sort::Uninterpreted(sort) => {
                    let k = *cardinalities.get(&sort)?;
                    (0..u128::from(k))
                        .map(|token| Value::Uninterpreted { sort, value: token })
                        .collect()
                }
                Sort::Bool => vec![Value::Bool(false), Value::Bool(true)],
                _ => return None,
            };
            let (binder, body) = (*binder, *body);
            for value in carrier {
                *budget = budget.checked_sub(1)?;
                let mut bound = assignment.clone();
                bound.set(binder, value);
                let outcome =
                    eval_finite_uninterpreted(arena, body, cardinalities, &bound, budget)?;
                if outcome != is_forall {
                    return Some(outcome);
                }
            }
            Some(is_forall)
        }
        Op::BoolNot => {
            let [inner] = &**args else {
                return None;
            };
            eval_finite_uninterpreted(arena, *inner, cardinalities, assignment, budget)
                .map(|value| !value)
        }
        Op::BoolAnd => {
            let args = args.clone();
            for &arg in &*args {
                if !eval_finite_uninterpreted(arena, arg, cardinalities, assignment, budget)? {
                    return Some(false);
                }
            }
            Some(true)
        }
        Op::BoolOr => {
            let args = args.clone();
            for &arg in &*args {
                if eval_finite_uninterpreted(arena, arg, cardinalities, assignment, budget)? {
                    return Some(true);
                }
            }
            Some(false)
        }
        Op::BoolImplies => {
            let [antecedent, consequent] = &**args else {
                return None;
            };
            let (antecedent, consequent) = (*antecedent, *consequent);
            if !eval_finite_uninterpreted(arena, antecedent, cardinalities, assignment, budget)? {
                return Some(true);
            }
            eval_finite_uninterpreted(arena, consequent, cardinalities, assignment, budget)
        }
        Op::BoolXor => {
            let [left, right] = &**args else {
                return None;
            };
            let (left, right) = (*left, *right);
            let left = eval_finite_uninterpreted(arena, left, cardinalities, assignment, budget)?;
            let right = eval_finite_uninterpreted(arena, right, cardinalities, assignment, budget)?;
            Some(left ^ right)
        }
        Op::Eq if args.len() == 2 && arena.sort_of(args[0]) == Sort::Bool => {
            let [left, right] = &**args else {
                return None;
            };
            let (left, right) = (*left, *right);
            let left = eval_finite_uninterpreted(arena, left, cardinalities, assignment, budget)?;
            let right = eval_finite_uninterpreted(arena, right, cardinalities, assignment, budget)?;
            Some(left == right)
        }
        Op::Ite if arena.sort_of(term) == Sort::Bool => {
            let [condition, then_branch, else_branch] = &**args else {
                return None;
            };
            let (condition, then_branch, else_branch) = (*condition, *then_branch, *else_branch);
            let branch = if eval_finite_uninterpreted(
                arena,
                condition,
                cardinalities,
                assignment,
                budget,
            )? {
                then_branch
            } else {
                else_branch
            };
            eval_finite_uninterpreted(arena, branch, cardinalities, assignment, budget)
        }
        // A quantifier below any other operator (a non-Boolean position) is
        // outside the supported shape: fail closed.
        _ => None,
    }
}

fn representatives_for_binder(
    arena: &TermArena,
    model: &Model,
    binder_sort: Sort,
    positions: &BTreeMap<FuncId, BTreeSet<usize>>,
) -> Option<Vec<Value>> {
    let mut representatives = Vec::new();
    for (&function, argument_positions) in positions {
        let (_, declared_params, declared_result) = arena.function(function);
        let interpretation = model.function(function)?;
        if interpretation.params() != declared_params
            || interpretation.result() != declared_result
            || !interpretation.uses_value_storage()
        {
            return None;
        }
        for (key, _) in interpretation.value_entries() {
            if key.len() != declared_params.len() {
                return None;
            }
            for &position in argument_positions {
                let component = key.get(position)?;
                if component.sort() != binder_sort {
                    return None;
                }
                if !representatives.contains(component) {
                    representatives.push(component.clone());
                    if representatives.len() >= QUANTIFIED_UF_PROFILE_CAP {
                        return None;
                    }
                }
            }
        }
    }
    representatives.push(fresh_value(binder_sort, &representatives)?);
    Some(representatives)
}

fn check_profile_product(
    arena: &mut TermArena,
    body: TermId,
    binder_terms: &[TermId],
    representative_terms: &[Vec<TermId>],
    depth: usize,
    replacements: &mut HashMap<TermId, TermId>,
    assignment: &axeyum_ir::Assignment,
) -> bool {
    if depth == binder_terms.len() {
        let mut memo = HashMap::new();
        let instantiated = substitute_terms(arena, body, replacements, &mut memo);
        return matches!(eval(arena, instantiated, assignment), Ok(Value::Bool(true)));
    }
    let binder = binder_terms[depth];
    for &representative in &representative_terms[depth] {
        replacements.insert(binder, representative);
        if !check_profile_product(
            arena,
            body,
            binder_terms,
            representative_terms,
            depth + 1,
            replacements,
            assignment,
        ) {
            replacements.remove(&binder);
            return false;
        }
    }
    replacements.remove(&binder);
    true
}

/// Constructs the minimal source-binding certificate only after the independent
/// checker accepts it.
pub(crate) fn certify_quantified_uf_model_sat(
    arena: &TermArena,
    assertion: TermId,
    model: &Model,
) -> Option<QuantifiedUfModelSatCertificate> {
    let binder = match arena.node(assertion) {
        TermNode::App {
            op: Op::Forall(binder) | Op::Exists(binder),
            ..
        } => *binder,
        // Quantifiers nested in Boolean structure (the finite
        // uninterpreted-carrier route): bind the deterministic first-visited
        // binder, mirroring the checker's redundant source-binding test.
        _ => *collect_all_binders(arena, assertion).first()?,
    };
    let certificate = QuantifiedUfModelSatCertificate { assertion, binder };
    check_quantified_uf_model_sat(arena, assertion, model, &certificate).then_some(certificate)
}

/// Returns every UF application needed to evaluate an accepted source shape.
///
/// This is search-side discovery only: callers may use the deterministic set to
/// construct candidate interpretations, but [`check_quantified_uf_model_sat`]
/// remains the acceptance boundary.
pub(crate) fn quantified_uf_model_functions(
    arena: &TermArena,
    assertion: TermId,
) -> Option<BTreeSet<FuncId>> {
    // Mirror of the finite uninterpreted-carrier route: every binder ranges
    // over an uninterpreted sort (the quantifiers may sit anywhere in the
    // Boolean structure). Discovery returns every applied function of the
    // assertion; acceptance stays with the exhaustive checker.
    {
        let binders = collect_all_binders(arena, assertion);
        if binders
            .iter()
            .any(|&binder| matches!(arena.symbol(binder).1, Sort::Uninterpreted(_)))
            && binders.iter().all(|&binder| {
                matches!(arena.symbol(binder).1, Sort::Uninterpreted(_) | Sort::Bool)
            })
        {
            let functions = applied_functions(arena, assertion);
            return (!functions.is_empty()).then_some(functions);
        }
    }
    let (binders, body) = universal_prefix(arena, assertion)?;
    if let [binder] = binders.as_slice()
        && let Some((function, _)) = vacuous_unary_uf_guard(arena, body, *binder)
    {
        return Some(BTreeSet::from([function]));
    }
    for &binder in &binders {
        let sort = arena.symbol(binder).1;
        if !matches!(sort, Sort::Int | Sort::Real) {
            return None;
        }
        if relevant_function_positions(arena, body, binder)?.is_empty() {
            return None;
        }
    }

    let functions = applied_functions(arena, body);
    (!functions.is_empty()).then_some(functions)
}

/// Every uninterpreted function applied anywhere under `root`.
fn applied_functions(arena: &TermArena, root: TermId) -> BTreeSet<FuncId> {
    let mut functions = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if let Op::Apply(function) = op {
                functions.insert(*function);
            }
            stack.extend(args.iter().copied());
        }
    }
    functions
}

/// Recognizes `f(x) = ground` as the antecedent of a top-level implication.
/// The consequent may mention `x` arbitrarily: when a total constant model for
/// `f` differs from `ground`, the antecedent is false for every `x` and the exact
/// source universal is true without sampling the consequent's arithmetic.
pub(crate) fn vacuous_unary_uf_guard(
    arena: &TermArena,
    body: TermId,
    binder: SymbolId,
) -> Option<(FuncId, TermId)> {
    fn application_at_binder(arena: &TermArena, term: TermId, binder: SymbolId) -> Option<FuncId> {
        let TermNode::App {
            op: Op::Apply(function),
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

    fn mentions_symbol(arena: &TermArena, root: TermId, symbol: SymbolId) -> bool {
        let mut seen = BTreeSet::new();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match arena.node(term) {
                TermNode::Symbol(candidate) if *candidate == symbol => return true,
                TermNode::App { args, .. } => stack.extend(args.iter().copied()),
                _ => {}
            }
        }
        false
    }

    if arena.symbol(binder).1 != Sort::Int {
        return None;
    }

    let TermNode::App {
        op: Op::BoolImplies,
        args,
    } = arena.node(body)
    else {
        return None;
    };
    let [antecedent, _] = &**args else {
        return None;
    };
    let TermNode::App {
        op: Op::Eq,
        args: equality,
    } = arena.node(*antecedent)
    else {
        return None;
    };
    let [left, right] = &**equality else {
        return None;
    };
    let candidate = application_at_binder(arena, *left, binder)
        .filter(|_| !mentions_symbol(arena, *right, binder))
        .map(|function| (function, *right))
        .or_else(|| {
            application_at_binder(arena, *right, binder)
                .filter(|_| !mentions_symbol(arena, *left, binder))
                .map(|function| (function, *left))
        })?;
    let (_, params, result) = arena.function(candidate.0);
    (params == [Sort::Int]
        && matches!(result, Sort::Uninterpreted(_))
        && arena.sort_of(candidate.1) == result)
        .then_some(candidate)
}

fn check_vacuous_unary_uf_guard(
    arena: &TermArena,
    body: TermId,
    binder: SymbolId,
    model: &Model,
) -> bool {
    let Some((function, ground)) = vacuous_unary_uf_guard(arena, body, binder) else {
        return false;
    };
    let binder_sort = arena.symbol(binder).1;
    let (_, params, result) = arena.function(function);
    if params != [binder_sort] || arena.sort_of(ground) != result {
        return false;
    }
    let Some(interpretation) = model.function(function) else {
        return false;
    };
    if interpretation.params() != params
        || interpretation.result() != result
        || interpretation.value_entries().next().is_some()
    {
        return false;
    }
    let Ok(ground_value) = eval(arena, ground, &model.to_assignment()) else {
        return false;
    };
    interpretation.default_value() != ground_value
}

/// Returns the first exact finite-profile value that falsifies a supported
/// single-`Int`-binder universal under `model`.
///
/// This is search guidance only. Absence is deliberately ambiguous between an
/// accepted profile and every unsupported/malformed case; callers must still
/// use [`check_quantified_uf_model_sat`] as the SAT authority.
pub(crate) fn first_quantified_uf_model_falsifier(
    arena: &TermArena,
    assertion: TermId,
    model: &Model,
) -> Option<Value> {
    let (binders, body) = universal_prefix(arena, assertion)?;
    let [binder] = binders.as_slice() else {
        return None;
    };
    if arena.symbol(*binder).1 != Sort::Int {
        return None;
    }
    let positions = relevant_function_positions(arena, body, *binder)?;
    if positions.is_empty() {
        return None;
    }
    let representatives = representatives_for_binder(arena, model, Sort::Int, &positions)?;
    let mut assignment = model.to_assignment();
    for representative in representatives {
        assignment.set(*binder, representative.clone());
        match eval(arena, body, &assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => return Some(representative),
            _ => return None,
        }
    }
    None
}

/// Returns the exact UF argument positions occupied by `binder`, or `None` when
/// an occurrence is not a direct UF argument.
fn relevant_function_positions(
    arena: &TermArena,
    root: TermId,
    binder: SymbolId,
) -> Option<BTreeMap<FuncId, BTreeSet<usize>>> {
    fn visit(
        arena: &TermArena,
        term: TermId,
        binder: SymbolId,
        direct_position: Option<(FuncId, usize)>,
        positions: &mut BTreeMap<FuncId, BTreeSet<usize>>,
    ) -> bool {
        match arena.node(term) {
            TermNode::Symbol(symbol) if *symbol == binder => {
                let Some((function, position)) = direct_position else {
                    return false;
                };
                positions.entry(function).or_default().insert(position);
                true
            }
            TermNode::App { op, args } => {
                let application = match op {
                    Op::Apply(function) => Some(*function),
                    _ => None,
                };
                let args = args.clone();
                args.iter().enumerate().all(|(position, &argument)| {
                    visit(
                        arena,
                        argument,
                        binder,
                        application.map(|function| (function, position)),
                        positions,
                    )
                })
            }
            _ => true,
        }
    }

    let mut positions = BTreeMap::new();
    visit(arena, root, binder, None, &mut positions).then_some(positions)
}

fn contains_quantifier(arena: &TermArena, root: TermId) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

fn fresh_value(sort: Sort, avoid: &[Value]) -> Option<Value> {
    let bound = avoid.len().checked_add(2)?;
    let mut integer = 0_i128;
    for _ in 0..=bound {
        let candidate = match sort {
            Sort::Int => Value::Int(integer),
            Sort::Real => Value::Real(Rational::integer(integer)),
            _ => return None,
        };
        if !avoid.contains(&candidate) {
            return Some(candidate);
        }
        integer = if integer > 0 { -integer } else { -integer + 1 };
    }
    None
}

fn value_to_const(arena: &mut TermArena, value: &Value) -> Option<TermId> {
    match value {
        Value::Int(integer) => Some(arena.int_const(*integer)),
        Value::Real(real) => Some(arena.real_const(*real)),
        _ => None,
    }
}

fn substitute_terms(
    arena: &mut TermArena,
    term: TermId,
    replacements: &HashMap<TermId, TermId>,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&replacement) = replacements.get(&term) {
        return replacement;
    }
    if let Some(&cached) = memo.get(&term) {
        return cached;
    }
    let rebuilt = match arena.node(term).clone() {
        TermNode::App { args, .. } => {
            let arguments: Vec<_> = args
                .iter()
                .map(|&argument| substitute_terms(arena, argument, replacements, memo))
                .collect();
            arena.rebuild_with_args(term, &arguments)
        }
        _ => term,
    };
    memo.insert(term, rebuilt);
    rebuilt
}

#[cfg(test)]
mod tests {
    use axeyum_ir::FuncValue;

    use super::*;

    /// A symbol occurring both free and bound must not have the quantifier's
    /// last binding leak into the free occurrence's evaluation (the checker
    /// clones the assignment per binding). Here `x`'s model value falsifies
    /// `not p(x)` while the universal's final enumeration token would satisfy
    /// it — accepting would be a wrong `sat`.
    #[test]
    fn finite_domain_check_does_not_leak_binder_into_free_occurrence() {
        let mut arena = TermArena::new();
        let carrier = arena.declare_uninterpreted_sort("LeakCarrier");
        let sort = Sort::Uninterpreted(carrier);
        let predicate = arena.declare_fun("leak_p", &[sort], Sort::Bool).unwrap();
        let symbol = arena.declare("leak_x", sort).unwrap();
        let variable = arena.var(symbol);
        let p_x = arena.apply(predicate, &[variable]).unwrap();
        let not_p_x = arena.not(p_x).unwrap();
        let tautology = arena.or(p_x, not_p_x).unwrap();
        let universal = arena.forall(symbol, tautology).unwrap();
        // `forall x. (p(x) or not p(x))` first, then the free occurrence.
        let assertion = arena.and(universal, not_p_x).unwrap();

        let mut model = Model::new();
        model.set(
            symbol,
            Value::Uninterpreted {
                sort: carrier,
                value: 0,
            },
        );
        model.set_function(
            predicate,
            FuncValue::constant(vec![sort], Sort::Bool, 0).define(&[0], 1),
        );
        model.set_uninterpreted_cardinality(carrier, 2);

        // p(0) = true, so `not p(x)` with x := 0 is false: the assertion is
        // false under this model and the checker must reject it even though
        // the universal's last enumerated token (1) has p(1) = false.
        assert!(certify_quantified_uf_model_sat(&arena, assertion, &model).is_none());

        // The complementary model (x := 1, p(1) = false) genuinely satisfies
        // the assertion and must certify.
        model.set(
            symbol,
            Value::Uninterpreted {
                sort: carrier,
                value: 1,
            },
        );
        let certificate = certify_quantified_uf_model_sat(&arena, assertion, &model)
            .expect("the aliased-free-occurrence model genuinely satisfies the assertion");
        assert!(check_quantified_uf_model_sat(
            &arena,
            assertion,
            &model,
            &certificate
        ));
    }

    #[test]
    fn position_gate_accepts_direct_and_repeated_arguments() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("f", &[Sort::Int, Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("x", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let application = arena.apply(function, &[variable, variable]).unwrap();
        let zero = arena.int_const(0);
        let body = arena.int_ge(application, zero).unwrap();
        assert_eq!(
            relevant_function_positions(&arena, body, binder),
            Some(BTreeMap::from([(function, BTreeSet::from([0, 1]))]))
        );
    }

    #[test]
    fn position_gate_rejects_interpreted_occurrence() {
        let mut arena = TermArena::new();
        let function = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let binder = arena.declare("x", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let application = arena.apply(function, &[variable]).unwrap();
        let sum = arena.int_add(application, variable).unwrap();
        let zero = arena.int_const(0);
        let body = arena.int_ge(sum, zero).unwrap();
        assert_eq!(relevant_function_positions(&arena, body, binder), None);
    }

    #[test]
    fn constant_distinct_uf_default_certifies_vacuous_guard() {
        let mut arena = TermArena::new();
        let carrier = arena.declare_uninterpreted_sort("GuardCarrier");
        let carrier_sort = Sort::Uninterpreted(carrier);
        let guarded_value = arena.declare("guarded_value", carrier_sort).unwrap();
        let function = arena
            .declare_fun("guard_function", &[Sort::Int], carrier_sort)
            .unwrap();
        let binder = arena.declare("guard_x", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let application = arena.apply(function, &[variable]).unwrap();
        let guarded_value_term = arena.var(guarded_value);
        let antecedent = arena.eq(application, guarded_value_term).unwrap();
        let five = arena.int_const(5);
        let consequent = arena.int_ge(variable, five).unwrap();
        let body = arena.implies(antecedent, consequent).unwrap();
        let universal = arena.forall(binder, body).unwrap();

        let mut model = Model::new();
        model.set(
            guarded_value,
            Value::Uninterpreted {
                sort: carrier,
                value: 0,
            },
        );
        model.set_function(
            function,
            axeyum_ir::FuncValue::constant_value(
                vec![Sort::Int],
                carrier_sort,
                Value::Uninterpreted {
                    sort: carrier,
                    value: 1,
                },
            ),
        );

        let certificate = certify_quantified_uf_model_sat(&arena, universal, &model)
            .expect("the source guard is false for every binder value");
        assert!(check_quantified_uf_model_sat(
            &arena,
            universal,
            &model,
            &certificate
        ));
        assert_eq!(
            quantified_uf_model_functions(&arena, universal),
            Some(BTreeSet::from([function]))
        );

        let nonconstant = model.function(function).unwrap().clone().define_value(
            &[Value::Int(2)],
            Value::Uninterpreted {
                sort: carrier,
                value: 0,
            },
        );
        model.set_function(function, nonconstant);
        assert!(!check_quantified_uf_model_sat(
            &arena,
            universal,
            &model,
            &certificate
        ));
    }

    #[test]
    fn fresh_value_avoids_the_complete_special_set() {
        let avoid = vec![Value::Int(0), Value::Int(1), Value::Int(-1), Value::Int(2)];
        let generic = fresh_value(Sort::Int, &avoid).unwrap();
        assert!(!avoid.contains(&generic));
    }

    #[test]
    fn single_int_profile_falsifier_uses_exact_table_keys() {
        let mut arena = TermArena::new();
        let function = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let binder = arena.declare("x", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let application = arena.apply(function, &[variable]).unwrap();
        let zero = arena.int_const(0);
        let body = arena.int_ge(application, zero).unwrap();
        let universal = arena.forall(binder, body).unwrap();

        let mut model = Model::new();
        model.set_function(
            function,
            axeyum_ir::FuncValue::constant_value(vec![Sort::Int], Sort::Int, Value::Int(0))
                .define_value(&[Value::Int(2)], Value::Int(-1)),
        );
        assert_eq!(
            first_quantified_uf_model_falsifier(&arena, universal, &model),
            Some(Value::Int(2))
        );

        model.set_function(
            function,
            axeyum_ir::FuncValue::constant_value(vec![Sort::Int], Sort::Int, Value::Int(0)),
        );
        assert_eq!(
            first_quantified_uf_model_falsifier(&arena, universal, &model),
            None
        );
    }
}
