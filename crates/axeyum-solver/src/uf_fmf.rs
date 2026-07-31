//! Finite model finding for pure-UF quantified queries (SAT-only).
//!
//! Many satisfiable quantified pure-UF queries (Bool plus uninterpreted
//! carriers and functions, arbitrary `forall`/`exists` nesting) have a
//! *small finite* model; a query whose models are all infinite simply never
//! certifies here and keeps the caller's `unknown`. This module searches
//! upward through per-sort carrier bounds `k`: each uninterpreted sort is
//! encoded as `BitVec(w)` with `k` internal domain-representative variables
//! `D_0..D_{k-1}` (duplicates allowed, so the semantics is "model of size
//! <= k" — monotone in `k`), a **closure axiom** pins every original free
//! symbol and every function value over represented tuples to a
//! representative, `forall` expands to a `k`-way conjunction and `exists` to
//! a `k`-way disjunction over the representatives, and the ground `QF_UFBV`
//! result is decided by the lazy-Ackermann bit-blast route (general
//! dispatcher as fallback).
//!
//! DIRECTIONALITY: the expansion is equisatisfiable with "the original has a
//! model of size <= k", so a ground `sat` transfers exactly (after the model
//! is normalized to the canonical token domain `0..k` and independently
//! re-checked). A ground `unsat` at size `k` transfers **nothing** — the loop
//! deepens `k` instead. This module never emits `unsat` and never emits an
//! unchecked `sat`: its only outputs are a certified model or a decline.
//!
//! SOUNDNESS rests on the independent checker, not on this search: the
//! returned model records each sort's carrier size, carries one
//! [`crate::QuantifiedUfModelSatCertificate`] per quantified source assertion,
//! and is accepted only after [`crate::check_quantified_uf_model_sat`]
//! exhaustively re-evaluates every quantified assertion over the declared
//! carriers (failing closed on any out-of-carrier token) and every ground
//! assertion replays through the trust-anchor evaluator.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use axeyum_ir::{
    FuncId, FuncValue, Op, Sort, SortId, SymbolId, TermArena, TermId, TermNode, Value, eval,
};

use crate::backend::{
    Capabilities, CheckResult, SolverBackend, SolverConfig, SolverError, UnknownKind, UnknownReason,
};
use crate::model::Model;

/// Largest per-sort carrier bound the deepening loop tries. The cvc5
/// finite-model-find probe over the public UF parity slice tops out at
/// per-sort cardinality 5; 8 leaves margin without inviting blowup.
const MAX_DOMAIN_SIZE: u32 = 8;

/// Total ground-instance budget for one expansion (quantifier instantiations
/// plus closure axioms). Exceeding it stops the deepening loop.
const MAX_GROUND_INSTANCES: usize = 64_000;

/// Admission bound on the source DAG size — the expander is DAG-linear per
/// instantiation, so a huge source formula is refused before any work.
const MAX_SOURCE_DAG_NODES: usize = 100_000;

/// SAT-only finite model finding over a pure-UF quantified query.
///
/// Returns `Ok(Some(model))` only for a model that already carries one checked
/// quantified-UF certificate per quantified assertion and replays every ground
/// assertion; callers still re-gate through [`crate::check_model`]. Returns
/// `Ok(None)` on every decline (outside the fragment, budget/deadline
/// exhausted, or no finite model found within the bounds) so the caller keeps
/// its own verdict — this routine never turns a decline into `unsat`.
///
/// # Errors
///
/// Propagates [`SolverError`] from the inner quantifier-free dispatcher.
pub(crate) fn find_uf_finite_model(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<Model>, SolverError> {
    // Diagnostics only (never a behavior switch): AXEYUM_UF_FMF_DEBUG=1
    // traces the deepening loop on stderr.
    let debug = std::env::var_os("AXEYUM_UF_FMF_DEBUG").is_some();
    let Some(shape) = analyze_pure_uf(arena, assertions) else {
        if debug {
            eprintln!("uf_fmf: query is outside the pure-UF fragment");
        }
        return Ok(None);
    };
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));

    let mut previous_bounds: Option<Vec<u32>> = None;
    for step in 1..=MAX_DOMAIN_SIZE {
        let bounds: Vec<u32> = shape
            .sorts
            .iter()
            .map(|sort| {
                let floor = if shape.diseq_sorts.contains(sort) {
                    2
                } else {
                    1
                };
                step.max(floor).min(MAX_DOMAIN_SIZE)
            })
            .collect();
        if previous_bounds.as_ref() == Some(&bounds) {
            continue;
        }
        previous_bounds = Some(bounds.clone());

        let Some(round_config) = crate::auto::config_with_remaining_timeout(config, deadline)
        else {
            if debug {
                eprintln!("uf_fmf: step={step} deadline exhausted before the round");
            }
            return Ok(None);
        };
        let Some(expansion) = build_expansion(arena, assertions, &shape, &bounds) else {
            // Budget exceeded: larger bounds only grow the expansion.
            if debug {
                eprintln!("uf_fmf: step={step} expansion budget exceeded");
            }
            return Ok(None);
        };
        let round_start = Instant::now();
        // The expansion is exactly scalar QF_UFBV: decide it on the lazy
        // Ackermann CEGAR over the pure-Rust bit-blast backend, which handles
        // the closure disjunctions the online e-graph routes cap out on. The
        // CEGAR loop re-enters the backend once per refinement round with the
        // caller's full config, so a shared wall-clock deadline is enforced
        // here through a deadline-clamping backend adapter — the aggregate
        // loop stays inside this route's remaining budget instead of
        // multiplying it. The general dispatcher remains the fallback for
        // anything the lazy route declines.
        let mut backend = DeadlineClampedBackend {
            inner: crate::SatBvBackend::new(),
            deadline,
        };
        let round = match crate::euf::check_qf_ufbv_lazy(
            &mut backend,
            arena,
            &expansion.assertions,
            &round_config,
        ) {
            Ok(result @ (CheckResult::Sat(_) | CheckResult::Unsat)) => result,
            Ok(CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {
                let Some(fallback_config) =
                    crate::auto::config_with_remaining_timeout(config, deadline)
                else {
                    if debug {
                        eprintln!("uf_fmf: step={step} deadline exhausted before fallback");
                    }
                    return Ok(None);
                };
                crate::auto::check_auto(arena, &expansion.assertions, &fallback_config)?
            }
            Err(error) => {
                if debug {
                    eprintln!("uf_fmf: step={step} ground engine error: {error}");
                }
                return Err(error);
            }
        };
        if debug {
            eprintln!(
                "uf_fmf: step={step} bounds={bounds:?} ground_instances={} solve={:?} result={}",
                expansion.assertions.len(),
                round_start.elapsed(),
                match &round {
                    CheckResult::Sat(_) => "sat".to_owned(),
                    CheckResult::Unsat => "unsat".to_owned(),
                    CheckResult::Unknown(reason) => format!("unknown({})", reason.detail),
                },
            );
        }
        match round {
            CheckResult::Sat(ground_model) => {
                if let Some(model) =
                    certified_source_model(arena, assertions, &shape, &expansion, &ground_model)
                {
                    return Ok(Some(model));
                }
                if debug {
                    eprintln!("uf_fmf: step={step} certification declined");
                }
                // The candidate did not certify: deepen rather than give up.
            }
            // UNSAT AT SIZE k TRANSFERS NOTHING about the original: deepen.
            CheckResult::Unsat => {}
            // The ground engine could not decide this size within budget;
            // larger sizes are strictly harder — stop.
            CheckResult::Unknown(_) => return Ok(None),
        }
    }
    Ok(None)
}

/// A [`SolverBackend`] adapter that clamps every `check` call's timeout to
/// the time remaining before a shared wall-clock deadline, and refuses with a
/// graceful `Unknown` once the deadline has passed. This bounds the
/// *aggregate* runtime of a CEGAR loop that re-enters the backend once per
/// refinement round with the caller's full per-call budget.
struct DeadlineClampedBackend<B> {
    inner: B,
    deadline: Option<Instant>,
}

impl<B: SolverBackend> SolverBackend for DeadlineClampedBackend<B> {
    fn capabilities(&self) -> Capabilities {
        self.inner.capabilities()
    }

    fn check(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        let Some(clamped) = crate::auto::config_with_remaining_timeout(config, self.deadline)
        else {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "uf-fmf: shared deadline exhausted before this refinement round".to_owned(),
            }));
        };
        self.inner.check(arena, assertions, &clamped)
    }
}

/// The pure-UF shape of a query admitted to finite model finding.
struct PureUfShape {
    /// Every uninterpreted sort reachable from the assertions.
    sorts: BTreeSet<SortId>,
    /// Original free (unbound) uninterpreted-sorted symbols, in first-visit
    /// order. Includes Skolem constants from earlier pipeline stages — every
    /// free symbol of an uninterpreted sort gets a closure axiom.
    free_symbols: Vec<(SymbolId, SortId)>,
    /// Original free Bool-sorted symbols.
    bool_symbols: Vec<SymbolId>,
    /// Applied uninterpreted functions, in first-visit order.
    functions: Vec<FuncId>,
    /// Sorts with at least one ground disequality between two terms — their
    /// carrier bound starts at 2.
    diseq_sorts: BTreeSet<SortId>,
}

/// Classifies `assertions` as pure UF: every sort is `Bool` or an
/// uninterpreted carrier, every operator is Boolean structure / equality /
/// `ite` / function application / quantification, every binder ranges over an
/// uninterpreted sort, at least one quantifier exists, and every quantifier
/// sits either at an assertion's top or nested inside another quantifier's
/// body (the certificate route covers exactly top-level-quantified
/// assertions). Declines (`None`) otherwise.
#[allow(clippy::too_many_lines)]
fn analyze_pure_uf(arena: &TermArena, assertions: &[TermId]) -> Option<PureUfShape> {
    let mut sorts = BTreeSet::new();
    let mut symbols: Vec<(SymbolId, Sort)> = Vec::new();
    let mut binders: BTreeSet<SymbolId> = BTreeSet::new();
    let mut functions: Vec<FuncId> = Vec::new();
    let mut has_quantifier = false;

    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut visited_nodes = 0usize;
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        visited_nodes += 1;
        if visited_nodes > MAX_SOURCE_DAG_NODES {
            return None;
        }
        match arena.sort_of(term) {
            Sort::Bool => {}
            Sort::Uninterpreted(sort) => {
                sorts.insert(sort);
            }
            _ => return None,
        }
        match arena.node(term) {
            TermNode::BoolConst(_) => {}
            TermNode::Symbol(symbol) => {
                if !symbols.iter().any(|(existing, _)| existing == symbol) {
                    symbols.push((*symbol, arena.symbol(*symbol).1));
                }
            }
            TermNode::App { op, args } => {
                match op {
                    Op::BoolNot
                    | Op::BoolAnd
                    | Op::BoolOr
                    | Op::BoolImplies
                    | Op::BoolXor
                    | Op::Eq
                    | Op::Ite => {}
                    Op::Apply(function) => {
                        let (_, params, result) = arena.function(*function);
                        let supported =
                            |sort: &Sort| matches!(sort, Sort::Bool | Sort::Uninterpreted(_));
                        if !params.iter().all(supported) || !supported(&result) {
                            return None;
                        }
                        for param in params {
                            if let Sort::Uninterpreted(sort) = param {
                                sorts.insert(*sort);
                            }
                        }
                        if let Sort::Uninterpreted(sort) = result {
                            sorts.insert(sort);
                        }
                        if !functions.contains(function) {
                            functions.push(*function);
                        }
                    }
                    Op::Forall(binder) | Op::Exists(binder) => {
                        has_quantifier = true;
                        match arena.symbol(*binder).1 {
                            Sort::Uninterpreted(sort) => {
                                sorts.insert(sort);
                            }
                            // A Bool binder ranges over the fixed two-element
                            // carrier; nothing to bound.
                            Sort::Bool => {}
                            _ => return None,
                        }
                        binders.insert(*binder);
                    }
                    _ => return None,
                }
                stack.extend(args.iter().copied());
            }
            _ => return None,
        }
    }
    if !has_quantifier || sorts.is_empty() {
        return None;
    }

    let mut free_symbols = Vec::new();
    let mut bool_symbols = Vec::new();
    for (symbol, sort) in symbols {
        if binders.contains(&symbol) {
            continue;
        }
        match sort {
            Sort::Uninterpreted(sort) => free_symbols.push((symbol, sort)),
            Sort::Bool => bool_symbols.push(symbol),
            _ => return None,
        }
    }

    let mut diseq_sorts = BTreeSet::new();
    for &assertion in assertions {
        collect_ground_diseq_sorts(arena, assertion, &mut diseq_sorts);
    }

    Some(PureUfShape {
        sorts,
        free_symbols,
        bool_symbols,
        functions,
        diseq_sorts,
    })
}

/// Records the sorts of `not (= a b)` facts along an assertion's conjunctive
/// spine — a sound *lower-bound hint* (such a sort needs >= 2 elements only if
/// the query is satisfiable at all; starting there merely skips a useless
/// size-1 round).
fn collect_ground_diseq_sorts(arena: &TermArena, term: TermId, out: &mut BTreeSet<SortId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } => {
            for &arg in &**args {
                collect_ground_diseq_sorts(arena, arg, out);
            }
        }
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => {
            if let [inner] = &**args
                && let TermNode::App {
                    op: Op::Eq,
                    args: operands,
                } = arena.node(*inner)
                && let [left, _] = &**operands
                && let Sort::Uninterpreted(sort) = arena.sort_of(*left)
            {
                out.insert(sort);
            }
        }
        _ => {}
    }
}

/// One bounded ground expansion, translated onto bit-vector carriers so the
/// pure-Rust bit-blast stack can decide it.
///
/// Each uninterpreted sort `s` with bound `k` becomes `BitVec(w)` with
/// `2^w >= k`; its carrier is *represented* by `k` internal BV **variables**
/// `D_0..D_{k-1}` (deliberately not fixed constants: duplicates keep the
/// "model of size <= k" semantics, which is monotone in `k` — a sort forced
/// small by the formula simply repeats a value while another sort uses all
/// `k`). Symmetry breaking pins `D_i <= i`, which is sound because carrier
/// tokens are interchangeable labels.
struct BvExpansion {
    assertions: Vec<TermId>,
    /// Per-sort domain-representative BV symbols `D_0..D_{k-1}`.
    domain_symbols: BTreeMap<SortId, Vec<SymbolId>>,
    /// original uninterpreted-sorted symbol -> its BV encoding.
    symbol_map: BTreeMap<SymbolId, SymbolId>,
    /// original function -> its BV-signature encoding.
    function_map: BTreeMap<FuncId, FuncId>,
}

/// The BV width carrying carrier bound `k` (`2^w >= k`, minimum 1).
fn carrier_width(bound: u32) -> u32 {
    (32 - bound.saturating_sub(1).leading_zeros()).max(1)
}

/// Builds the size-bounded, BV-encoded ground expansion, or `None` when the
/// instance budget is exceeded (or an internal builder declines).
#[allow(clippy::too_many_lines)]
fn build_expansion(
    arena: &mut TermArena,
    assertions: &[TermId],
    shape: &PureUfShape,
    bounds_list: &[u32],
) -> Option<BvExpansion> {
    let mut bounds: BTreeMap<SortId, u32> = BTreeMap::new();
    let mut widths: BTreeMap<SortId, u32> = BTreeMap::new();
    for (&sort, &bound) in shape.sorts.iter().zip(bounds_list) {
        bounds.insert(sort, bound);
        widths.insert(sort, carrier_width(bound));
    }
    // Deterministic per-round tag: `declare_internal*` reuses by name, and the
    // encoded widths change between rounds, so the round's bounds are part of
    // every minted name.
    let tag: String = bounds_list
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join("_");

    let mut expanded: Vec<TermId> = Vec::new();
    let mut budget = MAX_GROUND_INSTANCES;

    // Domain representatives per sort, with `D_i <= i` symmetry breaking.
    let mut domain_symbols: BTreeMap<SortId, Vec<SymbolId>> = BTreeMap::new();
    let mut domain_terms: BTreeMap<SortId, Vec<TermId>> = BTreeMap::new();
    for (&sort, &bound) in &bounds {
        let width = widths[&sort];
        let mut symbols = Vec::with_capacity(bound as usize);
        let mut terms = Vec::with_capacity(bound as usize);
        for index in 0..bound {
            let symbol = arena
                .declare_internal(
                    &format!("!uf_fmf.{tag}.s{}.d{index}", sort.index()),
                    Sort::BitVec(width),
                )
                .ok()?;
            let variable = arena.var(symbol);
            budget = budget.checked_sub(1)?;
            let cap = arena.bv_const(width, u128::from(index)).ok()?;
            expanded.push(arena.bv_ule(variable, cap).ok()?);
            symbols.push(symbol);
            terms.push(variable);
        }
        domain_symbols.insert(sort, symbols);
        domain_terms.insert(sort, terms);
    }

    // Encoded free symbols with their closure axioms (`c` equals some `D_i`).
    // This covers every free uninterpreted-sorted symbol of the assertions —
    // including Skolem constants minted by earlier pipeline stages, which are
    // ordinary free symbols by the time they reach this route.
    let mut symbol_map: BTreeMap<SymbolId, SymbolId> = BTreeMap::new();
    for &(symbol, sort) in &shape.free_symbols {
        let width = widths[&sort];
        let encoded = arena
            .declare_internal(
                &format!("!uf_fmf.{tag}.sym{}", symbol.index()),
                Sort::BitVec(width),
            )
            .ok()?;
        symbol_map.insert(symbol, encoded);
        budget = budget.checked_sub(1)?;
        let variable = arena.var(encoded);
        expanded.push(member_of_domain(arena, variable, &domain_terms[&sort])?);
    }

    // Encoded functions.
    let mut function_map: BTreeMap<FuncId, FuncId> = BTreeMap::new();
    for &function in &shape.functions {
        let (_, params, result) = arena.function(function);
        let encoded_params: Vec<Sort> = params
            .iter()
            .map(|&param| encode_sort(param, &widths))
            .collect::<Option<Vec<_>>>()?;
        let encoded_result = encode_sort(result, &widths)?;
        let encoded = arena
            .declare_internal_fun(
                &format!("!uf_fmf.{tag}.fn{}", function.index()),
                &encoded_params,
                encoded_result,
            )
            .ok()?;
        function_map.insert(function, encoded);
    }

    // Range-closure axioms: every function value over every represented
    // domain tuple must itself be a represented domain element, so the
    // extracted structure's functions map carriers into carriers.
    for &function in &shape.functions {
        let (_, params, result) = arena.function(function);
        let Sort::Uninterpreted(result_sort) = result else {
            continue;
        };
        let params = params.to_vec();
        let mut tuples: Vec<Vec<TermId>> = vec![Vec::new()];
        for param in &params {
            let choices: Vec<TermId> = match param {
                Sort::Uninterpreted(sort) => domain_terms[sort].clone(),
                Sort::Bool => vec![arena.bool_const(true), arena.bool_const(false)],
                _ => return None,
            };
            let mut next = Vec::with_capacity(tuples.len().checked_mul(choices.len())?);
            for tuple in &tuples {
                for &choice in &choices {
                    let mut extended = tuple.clone();
                    extended.push(choice);
                    next.push(extended);
                }
            }
            tuples = next;
            if tuples.len() > budget {
                return None;
            }
        }
        let encoded = function_map[&function];
        for tuple in tuples {
            budget = budget.checked_sub(1)?;
            let application = arena.apply(encoded, &tuple).ok()?;
            expanded.push(member_of_domain(
                arena,
                application,
                &domain_terms[&result_sort],
            )?);
        }
    }

    // The assertions themselves: quantifiers expand over the domain
    // representatives; symbols and applications rewrite onto the encoding.
    for &assertion in assertions {
        let mut env: BTreeMap<SymbolId, TermId> = BTreeMap::new();
        expanded.push(translate(
            arena,
            assertion,
            &symbol_map,
            &function_map,
            &domain_terms,
            &mut env,
            &mut budget,
        )?);
    }

    Some(BvExpansion {
        assertions: expanded,
        domain_symbols,
        symbol_map,
        function_map,
    })
}

/// The BV encoding of a pure-UF sort.
fn encode_sort(sort: Sort, widths: &BTreeMap<SortId, u32>) -> Option<Sort> {
    match sort {
        Sort::Bool => Some(Sort::Bool),
        Sort::Uninterpreted(sort) => widths.get(&sort).map(|&width| Sort::BitVec(width)),
        _ => None,
    }
}

/// `or_i (term = domain_i)`.
fn member_of_domain(arena: &mut TermArena, term: TermId, domain: &[TermId]) -> Option<TermId> {
    let mut clause: Option<TermId> = None;
    for &representative in domain {
        let equality = arena.eq(term, representative).ok()?;
        clause = Some(match clause {
            Some(previous) => arena.or(previous, equality).ok()?,
            None => equality,
        });
    }
    clause
}

/// Rewrites a pure-UF term onto the BV encoding, expanding `forall` to a
/// conjunction and `exists` to a disjunction over the binder sort's domain
/// representatives. `env` carries the active binder substitutions; `budget`
/// counts instantiated bodies and declines on exhaustion.
fn translate(
    arena: &mut TermArena,
    term: TermId,
    symbol_map: &BTreeMap<SymbolId, SymbolId>,
    function_map: &BTreeMap<FuncId, FuncId>,
    domains: &BTreeMap<SortId, Vec<TermId>>,
    env: &mut BTreeMap<SymbolId, TermId>,
    budget: &mut usize,
) -> Option<TermId> {
    match arena.node(term).clone() {
        TermNode::BoolConst(_) => Some(term),
        TermNode::Symbol(symbol) => {
            if let Some(&replacement) = env.get(&symbol) {
                return Some(replacement);
            }
            if let Some(&encoded) = symbol_map.get(&symbol) {
                return Some(arena.var(encoded));
            }
            // A free Bool symbol passes through unchanged.
            matches!(arena.symbol(symbol).1, Sort::Bool).then_some(term)
        }
        TermNode::App { op, args } => match op {
            Op::Forall(binder) | Op::Exists(binder) => {
                let is_forall = matches!(op, Op::Forall(_));
                let [body] = &*args else {
                    return None;
                };
                // A rebound binder would make the substitution capture: decline.
                if env.contains_key(&binder) {
                    return None;
                }
                let domain: Vec<TermId> = match arena.symbol(binder).1 {
                    Sort::Uninterpreted(sort) => domains.get(&sort)?.clone(),
                    Sort::Bool => vec![arena.bool_const(false), arena.bool_const(true)],
                    _ => return None,
                };
                let mut combined: Option<TermId> = None;
                for representative in domain {
                    *budget = budget.checked_sub(1)?;
                    env.insert(binder, representative);
                    let instance =
                        translate(arena, *body, symbol_map, function_map, domains, env, budget)?;
                    combined = Some(match combined {
                        Some(previous) => {
                            if is_forall {
                                arena.and(previous, instance).ok()?
                            } else {
                                arena.or(previous, instance).ok()?
                            }
                        }
                        None => instance,
                    });
                }
                env.remove(&binder);
                combined
            }
            Op::Apply(function) => {
                let encoded = *function_map.get(&function)?;
                let arguments: Vec<TermId> = args
                    .iter()
                    .map(|&arg| {
                        translate(arena, arg, symbol_map, function_map, domains, env, budget)
                    })
                    .collect::<Option<Vec<_>>>()?;
                arena.apply(encoded, &arguments).ok()
            }
            // `ite` is rebuilt through the typed builder: its result sort
            // changes when the branches translate from an uninterpreted sort
            // to its BV encoding, so `rebuild_with_args` (which pins the
            // original sort) must not be used.
            Op::Ite => {
                let arguments: Vec<TermId> = args
                    .iter()
                    .map(|&arg| {
                        translate(arena, arg, symbol_map, function_map, domains, env, budget)
                    })
                    .collect::<Option<Vec<_>>>()?;
                let [condition, then_branch, else_branch] = arguments.as_slice() else {
                    return None;
                };
                arena.ite(*condition, *then_branch, *else_branch).ok()
            }
            // Eq is rebuilt through the typed builder too (its operands may
            // change sort); the Bool connectives keep Bool operands and could
            // use either route — the typed builders keep everything uniform.
            Op::Eq => {
                let arguments: Vec<TermId> = args
                    .iter()
                    .map(|&arg| {
                        translate(arena, arg, symbol_map, function_map, domains, env, budget)
                    })
                    .collect::<Option<Vec<_>>>()?;
                let [left, right] = arguments.as_slice() else {
                    return None;
                };
                arena.eq(*left, *right).ok()
            }
            Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolImplies | Op::BoolXor => {
                let arguments: Vec<TermId> = args
                    .iter()
                    .map(|&arg| {
                        translate(arena, arg, symbol_map, function_map, domains, env, budget)
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(arena.rebuild_with_args(term, &arguments))
            }
            _ => None,
        },
        _ => None,
    }
}

fn term_contains_quantifier(arena: &TermArena, root: TermId) -> bool {
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

/// Lifts a BV-encoded ground model back onto the source query: BV values of
/// the domain representatives are deduplicated (in representative order) into
/// the canonical token domain `0..k`, every original symbol/function is
/// rebuilt over [`Value::Uninterpreted`] tokens, internal encoding symbols
/// are dropped, per-sort cardinalities are recorded, one checked certificate
/// is attached per quantified source assertion, and every ground assertion
/// replays. Any failure declines.
fn certified_source_model(
    arena: &TermArena,
    assertions: &[TermId],
    shape: &PureUfShape,
    expansion: &BvExpansion,
    ground_model: &Model,
) -> Option<Model> {
    // Canonical token maps: BV value of a representative -> canonical token.
    let mut token_maps: BTreeMap<SortId, BTreeMap<u128, u128>> = BTreeMap::new();
    for (&sort, symbols) in &expansion.domain_symbols {
        let map = token_maps.entry(sort).or_default();
        for &symbol in symbols {
            let Some(Value::Bv { value, .. }) = ground_model.get(symbol) else {
                continue;
            };
            let next = u128::try_from(map.len()).ok()?;
            map.entry(value).or_insert(next);
        }
        if map.is_empty() {
            // A sort the ground engine never constrained: a singleton carrier
            // represented by BV value 0.
            map.insert(0, 0);
        }
    }

    let remap =
        |sort: SortId, code: u128| -> Option<u128> { token_maps.get(&sort)?.get(&code).copied() };

    let mut model = Model::new();
    for &(symbol, sort) in &shape.free_symbols {
        let encoded = *expansion.symbol_map.get(&symbol)?;
        let token = match ground_model.get(encoded) {
            // The closure axiom pins the encoded symbol to a representative's
            // value, so the remap must hit; a miss declines.
            Some(Value::Bv { value, .. }) => remap(sort, value)?,
            // A symbol the ground engine left unconstrained can take any
            // carrier element; canonical 0 always exists.
            None => 0,
            Some(_) => return None,
        };
        model.set(symbol, Value::Uninterpreted { sort, value: token });
    }
    for &symbol in &shape.bool_symbols {
        let value = match ground_model.get(symbol) {
            Some(Value::Bool(value)) => value,
            None => false,
            Some(_) => return None,
        };
        model.set(symbol, Value::Bool(value));
    }

    for &function in &shape.functions {
        let (_, params, result) = arena.function(function);
        if FuncValue::uses_value_storage_for(params, result) {
            return None;
        }
        let encoded = *expansion.function_map.get(&function)?;
        let remap_scalar = |sort: Sort, code: u128| -> Option<u128> {
            match sort {
                Sort::Uninterpreted(sort) => remap(sort, code),
                Sort::Bool => Some(u128::from(code != 0)),
                _ => None,
            }
        };
        let mut rebuilt = FuncValue::constant(params.to_vec(), result, 0);
        if let Some(interpretation) = ground_model.function(encoded) {
            if interpretation.uses_value_storage() {
                return None;
            }
            // The range-closure axioms force every in-carrier point's value
            // into the carrier, so a default that does not remap is only ever
            // the value of out-of-carrier points — clamping it to canonical 0
            // cannot change any point the certificate check or replay visits.
            if let Some(default) = remap_scalar(result, interpretation.default_result()) {
                rebuilt = FuncValue::constant(params.to_vec(), result, default);
            }
            for (key, code) in interpretation.entries() {
                if key.len() != params.len() {
                    return None;
                }
                // Entries at out-of-carrier keys are unreachable in the
                // closed structure: drop them. The canonical map is injective
                // per sort, so distinct in-carrier keys never collide.
                let Some(remapped_key) = params
                    .iter()
                    .zip(key)
                    .map(|(&sort, &code)| remap_scalar(sort, code))
                    .collect::<Option<Vec<u128>>>()
                else {
                    continue;
                };
                let Some(remapped_result) = remap_scalar(result, code) else {
                    continue;
                };
                rebuilt = rebuilt.define(&remapped_key, remapped_result);
            }
        }
        model.set_function(function, rebuilt);
    }

    for &sort in &shape.sorts {
        let distinct = token_maps.get(&sort).map_or(1, BTreeMap::len);
        let cardinality = u32::try_from(distinct.max(1)).ok()?;
        model.set_uninterpreted_cardinality(sort, cardinality);
    }

    // Independent acceptance: certificates for quantified assertions (checked
    // exhaustively over the declared carriers, failing closed), evaluator
    // replay for ground assertions.
    for &assertion in assertions {
        if term_contains_quantifier(arena, assertion) {
            let certificate = crate::quant_uf_model_sat_cert::certify_quantified_uf_model_sat(
                arena, assertion, &model,
            )?;
            model.set_quantified_uf_model_sat_certificate(certificate);
        } else if !matches!(
            eval(arena, assertion, &model.to_assignment()),
            Ok(Value::Bool(true))
        ) {
            return None;
        }
    }
    Some(model)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config() -> SolverConfig {
        SolverConfig::new()
    }

    /// `forall x. p(x)` with `not p(c)` for a free `c` is unsat at every size;
    /// the finder must decline (never report a wrong sat, never unsat).
    #[test]
    fn contradictory_universal_declines() {
        let mut arena = TermArena::new();
        let carrier = arena.declare_uninterpreted_sort("FmfNeg");
        let sort = Sort::Uninterpreted(carrier);
        let predicate = arena.declare_fun("fmf_neg_p", &[sort], Sort::Bool).unwrap();
        let constant = arena.declare("fmf_neg_c", sort).unwrap();
        let binder = arena.declare("fmf_neg_x", sort).unwrap();
        let x = arena.var(binder);
        let p_x = arena.apply(predicate, &[x]).unwrap();
        let universal = arena.forall(binder, p_x).unwrap();
        let c = arena.var(constant);
        let p_c = arena.apply(predicate, &[c]).unwrap();
        let not_p_c = arena.not(p_c).unwrap();

        let result = find_uf_finite_model(&mut arena, &[universal, not_p_c], &config()).unwrap();
        assert!(result.is_none());
    }

    /// `forall x. p(x)` alone has the one-element model with `p` true.
    #[test]
    fn simple_universal_finds_size_one_model() {
        let mut arena = TermArena::new();
        let carrier = arena.declare_uninterpreted_sort("FmfUni");
        let sort = Sort::Uninterpreted(carrier);
        let predicate = arena.declare_fun("fmf_uni_p", &[sort], Sort::Bool).unwrap();
        let binder = arena.declare("fmf_uni_x", sort).unwrap();
        let x = arena.var(binder);
        let p_x = arena.apply(predicate, &[x]).unwrap();
        let universal = arena.forall(binder, p_x).unwrap();

        let model = find_uf_finite_model(&mut arena, &[universal], &config())
            .unwrap()
            .expect("a one-element model exists");
        assert_eq!(model.uninterpreted_cardinality(carrier), Some(1));
        assert!(crate::check_model(&arena, &[universal], &model).unwrap());
    }

    /// `exists x. p(x)` with `not p(c)`: needs two elements — exercises the
    /// existential finite disjunction and the deepening loop.
    #[test]
    fn existential_needs_two_elements() {
        let mut arena = TermArena::new();
        let carrier = arena.declare_uninterpreted_sort("FmfEx");
        let sort = Sort::Uninterpreted(carrier);
        let predicate = arena.declare_fun("fmf_ex_p", &[sort], Sort::Bool).unwrap();
        let constant = arena.declare("fmf_ex_c", sort).unwrap();
        let binder = arena.declare("fmf_ex_x", sort).unwrap();
        let x = arena.var(binder);
        let p_x = arena.apply(predicate, &[x]).unwrap();
        let existential = arena.exists(binder, p_x).unwrap();
        let c = arena.var(constant);
        let p_c = arena.apply(predicate, &[c]).unwrap();
        let not_p_c = arena.not(p_c).unwrap();
        let assertions = [existential, not_p_c];

        let model = find_uf_finite_model(&mut arena, &assertions, &config())
            .unwrap()
            .expect("a two-element model exists");
        assert!(model.uninterpreted_cardinality(carrier).unwrap_or(0) >= 2);
        assert!(crate::check_model(&arena, &assertions, &model).unwrap());
    }

    /// Exists-under-forall with a unary function: `forall x. exists y.
    /// f(x) = y` — satisfiable at size 1; the nested existential must expand.
    #[test]
    fn exists_under_forall_certifies() {
        let mut arena = TermArena::new();
        let carrier = arena.declare_uninterpreted_sort("FmfNest");
        let sort = Sort::Uninterpreted(carrier);
        let function = arena.declare_fun("fmf_nest_f", &[sort], sort).unwrap();
        let outer = arena.declare("fmf_nest_x", sort).unwrap();
        let inner = arena.declare("fmf_nest_y", sort).unwrap();
        let x = arena.var(outer);
        let y = arena.var(inner);
        let f_x = arena.apply(function, &[x]).unwrap();
        let body = arena.eq(f_x, y).unwrap();
        let existential = arena.exists(inner, body).unwrap();
        let universal = arena.forall(outer, existential).unwrap();

        let model = find_uf_finite_model(&mut arena, &[universal], &config())
            .unwrap()
            .expect("satisfiable at size one");
        assert!(crate::check_model(&arena, &[universal], &model).unwrap());
    }

    /// Non-UF content (an Int symbol) must decline the route entirely.
    #[test]
    fn arithmetic_content_declines() {
        let mut arena = TermArena::new();
        let carrier = arena.declare_uninterpreted_sort("FmfInt");
        let sort = Sort::Uninterpreted(carrier);
        let binder = arena.declare("fmf_int_x", sort).unwrap();
        let x = arena.var(binder);
        let same = arena.eq(x, x).unwrap();
        let universal = arena.forall(binder, same).unwrap();
        let integer = arena.declare("fmf_int_n", Sort::Int).unwrap();
        let n = arena.var(integer);
        let zero = arena.int_const(0);
        let ground = arena.int_ge(n, zero).unwrap();

        let result = find_uf_finite_model(&mut arena, &[universal, ground], &config()).unwrap();
        assert!(result.is_none());
    }
}
