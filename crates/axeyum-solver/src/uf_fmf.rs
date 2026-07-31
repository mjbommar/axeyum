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
//! symbol to a representative, every uninterpreted function becomes an
//! **explicit finite table** (one fresh scalar variable per parameter-domain
//! index tuple, with range-closure axioms pinning uninterpreted-sorted
//! entries to representatives), applications become first-match selector
//! `ite` chains over the representatives (so congruence holds by
//! construction; leftover budget adds redundant pairwise functionality
//! lemmas that speed up ground refutations), and `forall` expands to a
//! `k`-way conjunction and `exists` to a `k`-way disjunction over the
//! representatives. The ground expansion is then **pure scalar `QF_BV`** —
//! no uninterpreted functions survive — so it is decided by a single
//! bit-blast SAT solve per bound (general dispatcher as fallback), instead
//! of the congruence-CEGAR loop whose per-lemma re-solves dominated the
//! ground cost at `k >= 3`.
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

use crate::backend::{CheckResult, SolverBackend, SolverConfig, SolverError};
use crate::model::Model;

/// Largest per-sort carrier bound the deepening loop tries. The cvc5
/// finite-model-find probe over the public UF parity slice tops out at
/// per-sort cardinality 5; 8 leaves margin without inviting blowup.
const MAX_DOMAIN_SIZE: u32 = 8;

/// Total ground-instance budget for one expansion (quantifier
/// instantiations, closure axioms, table entries, functionality lemmas, and
/// selector leaves). Exceeding it stops the deepening loop.
const MAX_GROUND_INSTANCES: usize = 200_000;

/// Admission bound on the source DAG size — the expander is DAG-linear per
/// instantiation, so a huge source formula is refused before any work.
const MAX_SOURCE_DAG_NODES: usize = 100_000;

/// Maximum bound-lowering retries per deepening step. Each retry runs the
/// cheap cost estimator (no term building), so the descent stays fast even
/// on files with hundreds of sorts.
const MAX_EXPANSION_BACKOFFS: usize = 512;

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
#[allow(clippy::too_many_lines, reason = "one deepening loop with its backoff")]
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

    let floors: Vec<u32> = shape
        .sorts
        .iter()
        .map(|sort| {
            if shape.diseq_sorts.contains(sort) {
                2
            } else {
                1
            }
        })
        .collect();
    let mut solved_bounds: BTreeSet<Vec<u32>> = BTreeSet::new();
    'deepening: for step in 1..=MAX_DOMAIN_SIZE {
        // Per-sort non-uniform deepening by measured backoff: start from the
        // uniform `step` vector and, while the cheap cost estimator (or the
        // real build) says the expansion exceeds the instance budget, lower
        // the bound of the sort that CONTRIBUTES the most estimated cost
        // (quantifier-prefix products attribute to their binder sort, table
        // entries to their parameter sorts) and retry. Sorts that neither
        // multiply a quantifier prefix nor widen a table are never punished,
        // so a ground-diverse sort can ride to `step` while an expensive
        // binder sort backs off — the mismatched-cardinality profiles the
        // cvc5 probe showed. Every candidate is a valid "size <= bounds"
        // probe, so any descent path stays sound: `unsat` still transfers
        // nothing and only a certified model escapes.
        let mut bounds: Vec<u32> = floors
            .iter()
            .map(|&floor| step.max(floor).min(MAX_DOMAIN_SIZE))
            .collect();
        let mut expansion = None;
        for _attempt in 0..=MAX_EXPANSION_BACKOFFS {
            if solved_bounds.contains(&bounds) {
                // This exact vector was already ground-refuted on an earlier
                // step (floors and backoffs can repeat it): deepen instead.
                continue 'deepening;
            }
            if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                if debug {
                    eprintln!("uf_fmf: step={step} deadline exhausted during backoff");
                }
                return Ok(None);
            }
            let (estimate, tallies) = estimate_expansion(arena, assertions, &shape, &bounds);
            if estimate <= MAX_GROUND_INSTANCES as u64
                && let Some(built) = build_expansion(arena, assertions, &shape, &bounds)
            {
                expansion = Some(built);
                break;
            }
            // Lower the dominant-cost sort (largest tally still above its
            // floor). Far over budget, drop it straight to its floor so the
            // descent converges in few attempts even with hundreds of sorts.
            let mut target: Option<usize> = None;
            let mut best_tally = 0u64;
            for (index, sort) in shape.sorts.iter().enumerate() {
                let tally = tallies.get(sort).copied().unwrap_or(0);
                if bounds[index] > floors[index] && tally > best_tally {
                    best_tally = tally;
                    target = Some(index);
                }
            }
            let Some(target) = target else {
                // Nothing left to lower: deeper steps only grow the
                // expansion, so the whole search declines.
                if debug {
                    eprintln!("uf_fmf: step={step} expansion budget exceeded (floor reached)");
                }
                return Ok(None);
            };
            bounds[target] = if estimate / 8 > MAX_GROUND_INSTANCES as u64 {
                floors[target]
            } else {
                bounds[target] - 1
            };
            if debug {
                eprintln!(
                    "uf_fmf: step={step} estimate={estimate} over budget, lowering sort \
                     index {target} to {}",
                    bounds[target]
                );
            }
        }
        let Some(expansion) = expansion else {
            if debug {
                eprintln!("uf_fmf: step={step} expansion budget exceeded after backoffs");
            }
            return Ok(None);
        };
        solved_bounds.insert(bounds.clone());

        let Some(round_config) = crate::auto::config_with_remaining_timeout(config, deadline)
        else {
            if debug {
                eprintln!("uf_fmf: step={step} deadline exhausted before the round");
            }
            return Ok(None);
        };
        let round_start = Instant::now();
        // The expansion is pure scalar QF_BV (the function tables eliminated
        // every uninterpreted application), so it is decided by ONE bit-blast
        // SAT solve on the pure-Rust backend — no congruence-CEGAR loop, no
        // per-lemma re-solves. `round_config` is already clamped to the time
        // remaining before the shared deadline. The general dispatcher
        // remains the fallback for anything the direct route declines.
        let mut backend = crate::SatBvBackend::new();
        let round = match backend.check(arena, &expansion.assertions, &round_config) {
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
    /// original function -> its explicit finite table.
    function_tables: BTreeMap<FuncId, FunctionTable>,
}

/// One finite index into a function table: a representative ordinal of an
/// uninterpreted parameter, or a concrete Boolean for a `Bool` parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TableIndex {
    Rep(SortId, u32),
    Bool(bool),
}

/// The explicit finite table of one encoded function: one fresh scalar
/// variable per parameter-domain index tuple, in row-major enumeration order
/// (the last parameter varies fastest). Distinct representatives may carry
/// equal values (the "model of size <= k" duplicate semantics); the table
/// stays well defined because every read — the selector chains here and the
/// model lifting — resolves a value tuple to its lexicographically FIRST
/// matching index tuple, so entries at non-canonical tuples are never read.
struct FunctionTable {
    /// Declared parameter sorts (`Bool` or uninterpreted).
    params: Vec<Sort>,
    /// Per-position domain sizes (uninterpreted: the sort's bound; Bool: 2).
    sizes: Vec<usize>,
    /// `(index tuple, table variable)` in row-major order.
    entries: Vec<(Vec<TableIndex>, SymbolId)>,
}

/// The BV width carrying carrier bound `k` (`2^w >= k`, minimum 1).
fn carrier_width(bound: u32) -> u32 {
    (32 - bound.saturating_sub(1).leading_zeros()).max(1)
}

/// Cheap pre-build cost estimate for one bounds vector: a lower bound on the
/// build's budget usage (representatives + symbol closures + table entries +
/// quantifier-body instantiations; selector leaves are deliberately omitted
/// and caught by the real build's budget), plus a per-sort attribution the
/// backoff descent uses to pick which bound to lower. Quantifier costs
/// attribute to the binder's sort; a table's entry count attributes to each
/// of its uninterpreted parameter sorts. All arithmetic saturates.
fn estimate_expansion(
    arena: &TermArena,
    assertions: &[TermId],
    shape: &PureUfShape,
    bounds_list: &[u32],
) -> (u64, BTreeMap<SortId, u64>) {
    let bounds: BTreeMap<SortId, u32> = shape
        .sorts
        .iter()
        .copied()
        .zip(bounds_list.iter().copied())
        .collect();
    let mut tallies: BTreeMap<SortId, u64> = BTreeMap::new();
    let mut total: u64 = 0;

    for (&sort, &bound) in &bounds {
        total = total.saturating_add(u64::from(bound));
        *tallies.entry(sort).or_default() += u64::from(bound);
    }
    total = total.saturating_add(shape.free_symbols.len() as u64);

    for &function in &shape.functions {
        let (_, params, _) = arena.function(function);
        let mut entries: u64 = 1;
        for param in params {
            let size = match param {
                Sort::Uninterpreted(sort) => u64::from(*bounds.get(sort).unwrap_or(&1)),
                _ => 2,
            };
            entries = entries.saturating_mul(size);
        }
        total = total.saturating_add(entries);
        for param in params {
            if let Sort::Uninterpreted(sort) = param {
                *tallies.entry(*sort).or_default() = tallies
                    .get(sort)
                    .copied()
                    .unwrap_or(0)
                    .saturating_add(entries);
            }
        }
    }

    let mut memo: BTreeMap<TermId, u64> = BTreeMap::new();
    for &assertion in assertions {
        let cost = quantifier_cost(arena, assertion, &bounds, &mut memo, &mut tallies);
        total = total.saturating_add(cost);
    }
    (total, tallies)
}

/// The exact number of quantifier-body instantiations `translate` performs
/// for one occurrence of `term` (its budget decrements for quantifiers): a
/// quantifier over a domain of size `k` costs `k * (1 + cost(body))`; other
/// nodes sum their children per occurrence, mirroring the memo-free
/// traversal. Each quantifier node's own cost is attributed to its binder
/// sort once (ancestor multiplicity deliberately ignored — the tally is a
/// descent-ordering heuristic, not an invariant).
fn quantifier_cost(
    arena: &TermArena,
    term: TermId,
    bounds: &BTreeMap<SortId, u32>,
    memo: &mut BTreeMap<TermId, u64>,
    tallies: &mut BTreeMap<SortId, u64>,
) -> u64 {
    if let Some(&cost) = memo.get(&term) {
        return cost;
    }
    let cost = match arena.node(term).clone() {
        TermNode::App { op, args } => match op {
            Op::Forall(binder) | Op::Exists(binder) => {
                let (size, attributed_sort) = match arena.symbol(binder).1 {
                    Sort::Uninterpreted(sort) => {
                        (u64::from(*bounds.get(&sort).unwrap_or(&1)), Some(sort))
                    }
                    Sort::Bool => (2, None),
                    _ => (1, None),
                };
                let body_cost = args.first().map_or(0, |&body| {
                    quantifier_cost(arena, body, bounds, memo, tallies)
                });
                let own = size.saturating_mul(body_cost.saturating_add(1));
                if let Some(sort) = attributed_sort {
                    *tallies.entry(sort).or_default() =
                        tallies.get(&sort).copied().unwrap_or(0).saturating_add(own);
                }
                own
            }
            _ => args.iter().fold(0u64, |acc, &arg| {
                acc.saturating_add(quantifier_cost(arena, arg, bounds, memo, tallies))
            }),
        },
        _ => 0,
    };
    memo.insert(term, cost);
    cost
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

    // Explicit finite function tables: one fresh scalar variable per
    // parameter-domain index tuple, with a range-closure axiom on every
    // uninterpreted-sorted entry (the value is a represented domain element).
    // No functionality lemmas are needed: every read goes through a selector
    // chain that resolves each argument to its FIRST value-matching
    // representative, so two value-equal argument tuples always read the
    // same (lexicographically first matching) entry — congruence holds by
    // construction, and entries at non-canonical index tuples are simply
    // never read. Model lifting mirrors this with first-occurrence-wins.
    let mut function_tables: BTreeMap<FuncId, FunctionTable> = BTreeMap::new();
    for &function in &shape.functions {
        let (_, params, result) = arena.function(function);
        let params = params.to_vec();
        let encoded_result = encode_sort(result, &widths)?;
        let mut sizes = Vec::with_capacity(params.len());
        let mut tuples: Vec<Vec<TableIndex>> = vec![Vec::new()];
        for param in &params {
            let choices: Vec<TableIndex> = match param {
                Sort::Uninterpreted(sort) => (0..bounds[sort])
                    .map(|index| TableIndex::Rep(*sort, index))
                    .collect(),
                Sort::Bool => vec![TableIndex::Bool(false), TableIndex::Bool(true)],
                _ => return None,
            };
            sizes.push(choices.len());
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
        let mut entries = Vec::with_capacity(tuples.len());
        for (ordinal, tuple) in tuples.into_iter().enumerate() {
            budget = budget.checked_sub(1)?;
            let symbol = arena
                .declare_internal(
                    &format!("!uf_fmf.{tag}.fn{}.e{ordinal}", function.index()),
                    encoded_result,
                )
                .ok()?;
            if let Sort::Uninterpreted(result_sort) = result {
                let variable = arena.var(symbol);
                expanded.push(member_of_domain(
                    arena,
                    variable,
                    &domain_terms[&result_sort],
                )?);
            }
            entries.push((tuple, symbol));
        }
        function_tables.insert(
            function,
            FunctionTable {
                params,
                sizes,
                entries,
            },
        );
    }

    // The assertions themselves: quantifiers expand over the domain
    // representatives; symbols rewrite onto the encoding and applications
    // become table-selector `ite` chains (shared across instantiations
    // through the application memo).
    let mut apply_memo: BTreeMap<(FuncId, Vec<TermId>), TermId> = BTreeMap::new();
    for &assertion in assertions {
        let mut env: BTreeMap<SymbolId, TermId> = BTreeMap::new();
        expanded.push(translate(
            arena,
            assertion,
            &symbol_map,
            &function_tables,
            &domain_terms,
            &mut env,
            &mut apply_memo,
            &mut budget,
        )?);
    }

    // Optional redundancy: pairwise functionality lemmas over the table
    // entries (`args equal => entries equal` for every collidable index
    // pair). The first-match selectors make these logically superfluous for
    // every read entry, but they prune the SAT search dramatically on
    // refutation-heavy rounds (measured: an FFT k=4 ground refutation went
    // from deadline-death to ~3 s). They are funded strictly by LEFTOVER
    // budget after the semantic expansion is complete, so they can never
    // fail a build — files with huge tables simply get fewer or none, in
    // deterministic function/pair order.
    'pairs: for &function in &shape.functions {
        let table = &function_tables[&function];
        for i in 0..table.entries.len() {
            for j in (i + 1)..table.entries.len() {
                let mut equalities: Vec<(TermId, TermId)> = Vec::new();
                let mut collidable = true;
                for (a, b) in table.entries[i].0.iter().zip(&table.entries[j].0) {
                    match (*a, *b) {
                        (TableIndex::Bool(left), TableIndex::Bool(right)) => {
                            if left != right {
                                collidable = false;
                                break;
                            }
                        }
                        (TableIndex::Rep(sort, left), TableIndex::Rep(_, right)) => {
                            if left != right {
                                equalities.push((
                                    domain_terms[&sort][left as usize],
                                    domain_terms[&sort][right as usize],
                                ));
                            }
                        }
                        _ => return None,
                    }
                }
                if !collidable {
                    continue;
                }
                let Some(remaining) = budget.checked_sub(1) else {
                    break 'pairs;
                };
                budget = remaining;
                let mut antecedent: Option<TermId> = None;
                for (left, right) in equalities {
                    let equality = arena.eq(left, right).ok()?;
                    antecedent = Some(match antecedent {
                        Some(previous) => arena.and(previous, equality).ok()?,
                        None => equality,
                    });
                }
                // Distinct collidable tuples differ in at least one
                // representative ordinal, so the antecedent exists.
                let antecedent = antecedent?;
                let left = arena.var(table.entries[i].1);
                let right = arena.var(table.entries[j].1);
                let consequent = arena.eq(left, right).ok()?;
                expanded.push(arena.implies(antecedent, consequent).ok()?);
            }
        }
    }

    Some(BvExpansion {
        assertions: expanded,
        domain_symbols,
        symbol_map,
        function_tables,
    })
}

/// Translates an application of a table-encoded function: a nested selector
/// over the parameter domains ending at a table-entry variable.
///
/// For an uninterpreted parameter the selector is the `ite` chain
/// `ite(arg = D_0, ..entry 0.., ite(arg = D_1, ..entry 1.., ... ..entry k-1..))`
/// — sound because the range/symbol closure axioms pin every carrier-sorted
/// value to some representative, so falling through to the last branch is
/// exact. When the argument IS a representative `D_j`, the chain truncates at
/// index `j` (it always equals itself). Either way the resolved index is the
/// FIRST whose representative value equals the argument, so value-equal
/// argument tuples always read the same entry (congruence by construction).
#[allow(clippy::too_many_arguments)]
fn table_select(
    arena: &mut TermArena,
    table: &FunctionTable,
    domains: &BTreeMap<SortId, Vec<TermId>>,
    arguments: &[TermId],
    position: usize,
    base: usize,
    budget: &mut usize,
) -> Option<TermId> {
    if position == table.params.len() {
        *budget = budget.checked_sub(1)?;
        return Some(arena.var(table.entries[base].1));
    }
    let stride: usize = table.sizes[position + 1..].iter().product();
    match table.params[position] {
        Sort::Bool => {
            // Row-major order: `Bool(false)` is index 0, `Bool(true)` index 1.
            if let TermNode::BoolConst(value) = arena.node(arguments[position]) {
                let offset = if *value { stride } else { 0 };
                return table_select(
                    arena,
                    table,
                    domains,
                    arguments,
                    position + 1,
                    base + offset,
                    budget,
                );
            }
            let if_false =
                table_select(arena, table, domains, arguments, position + 1, base, budget)?;
            let if_true = table_select(
                arena,
                table,
                domains,
                arguments,
                position + 1,
                base + stride,
                budget,
            )?;
            arena.ite(arguments[position], if_true, if_false).ok()
        }
        Sort::Uninterpreted(sort) => {
            let representatives = domains.get(&sort)?.clone();
            let last = representatives
                .iter()
                .position(|&representative| representative == arguments[position])
                .unwrap_or(representatives.len().checked_sub(1)?);
            let mut selected = table_select(
                arena,
                table,
                domains,
                arguments,
                position + 1,
                base + last * stride,
                budget,
            )?;
            for index in (0..last).rev() {
                let equality = arena.eq(arguments[position], representatives[index]).ok()?;
                let branch = table_select(
                    arena,
                    table,
                    domains,
                    arguments,
                    position + 1,
                    base + index * stride,
                    budget,
                )?;
                selected = arena.ite(equality, branch, selected).ok()?;
            }
            Some(selected)
        }
        _ => None,
    }
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
/// counts instantiated bodies and selector leaves and declines on
/// exhaustion. `apply_memo` shares one selector chain per distinct
/// `(function, translated arguments)` across all instantiations.
#[allow(clippy::too_many_arguments)]
#[allow(clippy::too_many_lines, reason = "one structural match per operator")]
fn translate(
    arena: &mut TermArena,
    term: TermId,
    symbol_map: &BTreeMap<SymbolId, SymbolId>,
    function_tables: &BTreeMap<FuncId, FunctionTable>,
    domains: &BTreeMap<SortId, Vec<TermId>>,
    env: &mut BTreeMap<SymbolId, TermId>,
    apply_memo: &mut BTreeMap<(FuncId, Vec<TermId>), TermId>,
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
                    let instance = translate(
                        arena,
                        *body,
                        symbol_map,
                        function_tables,
                        domains,
                        env,
                        apply_memo,
                        budget,
                    )?;
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
                let table = function_tables.get(&function)?;
                let arguments: Vec<TermId> = args
                    .iter()
                    .map(|&arg| {
                        translate(
                            arena,
                            arg,
                            symbol_map,
                            function_tables,
                            domains,
                            env,
                            apply_memo,
                            budget,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?;
                let key = (function, arguments.clone());
                if let Some(&selected) = apply_memo.get(&key) {
                    return Some(selected);
                }
                let selected = table_select(arena, table, domains, &arguments, 0, 0, budget)?;
                apply_memo.insert(key, selected);
                Some(selected)
            }
            // `ite` is rebuilt through the typed builder: its result sort
            // changes when the branches translate from an uninterpreted sort
            // to its BV encoding, so `rebuild_with_args` (which pins the
            // original sort) must not be used.
            Op::Ite => {
                let arguments: Vec<TermId> = args
                    .iter()
                    .map(|&arg| {
                        translate(
                            arena,
                            arg,
                            symbol_map,
                            function_tables,
                            domains,
                            env,
                            apply_memo,
                            budget,
                        )
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
                        translate(
                            arena,
                            arg,
                            symbol_map,
                            function_tables,
                            domains,
                            env,
                            apply_memo,
                            budget,
                        )
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
                        translate(
                            arena,
                            arg,
                            symbol_map,
                            function_tables,
                            domains,
                            env,
                            apply_memo,
                            budget,
                        )
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
    // A representative the ground engine left unconstrained (absent from the
    // model) can take any value; it is completed to 0, which the symmetry cap
    // `D_i <= i` always admits — table keys below use the same completion, so
    // every key remap hits.
    let mut token_maps: BTreeMap<SortId, BTreeMap<u128, u128>> = BTreeMap::new();
    let mut rep_values: BTreeMap<SortId, Vec<u128>> = BTreeMap::new();
    for (&sort, symbols) in &expansion.domain_symbols {
        let map = token_maps.entry(sort).or_default();
        let values = rep_values.entry(sort).or_default();
        for &symbol in symbols {
            let value = match ground_model.get(symbol) {
                Some(Value::Bv { value, .. }) => value,
                None => 0,
                Some(_) => return None,
            };
            let next = u128::try_from(map.len()).ok()?;
            map.entry(value).or_insert(next);
            values.push(value);
        }
        if map.is_empty() {
            // A sort with no representatives cannot arise (bounds are >= 1),
            // but fail closed to a singleton carrier rather than panic.
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
        let table = expansion.function_tables.get(&function)?;
        if table.params.as_slice() != params {
            return None;
        }
        let mut rebuilt = FuncValue::constant(params.to_vec(), result, 0);
        // First occurrence in row-major order wins: that is exactly the entry
        // the selector chains read for a value tuple (the lexicographically
        // first index tuple whose representative values match), so the lifted
        // table agrees with every ground evaluation. Later duplicates of a
        // key are never read by the expansion and are skipped here.
        let mut defined: BTreeSet<Vec<u128>> = BTreeSet::new();
        for (tuple, symbol) in &table.entries {
            // Key: every representative ordinal maps through the SAME
            // completion as the token maps above, so the remap always hits.
            let mut key = Vec::with_capacity(tuple.len());
            for component in tuple {
                match *component {
                    TableIndex::Bool(value) => key.push(u128::from(value)),
                    TableIndex::Rep(sort, index) => {
                        let value = *rep_values.get(&sort)?.get(index as usize)?;
                        key.push(remap(sort, value)?);
                    }
                }
            }
            if !defined.insert(key.clone()) {
                continue;
            }
            // Result: the closure axiom pins a present entry to a
            // representative's value (a miss fails closed); an absent
            // (unconstrained, never-read-or-irrelevant) entry completes to
            // canonical 0.
            let token = match (result, ground_model.get(*symbol)) {
                (Sort::Uninterpreted(result_sort), Some(Value::Bv { value, .. })) => {
                    remap(result_sort, value)?
                }
                (Sort::Bool, Some(Value::Bool(value))) => u128::from(value),
                (_, None) => 0,
                _ => return None,
            };
            rebuilt = rebuilt.define(&key, token);
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

    /// A function with a `Bool` parameter exercises the table encoding's
    /// Boolean index branch with both constant and non-constant `Bool`
    /// arguments: `forall x. f(true, x) != c` (forces two carrier elements)
    /// plus `forall x. f(p(x), x) = f(false, x)` (satisfiable with `p`
    /// constantly false).
    #[test]
    fn bool_parameter_function_certifies() {
        let mut arena = TermArena::new();
        let carrier = arena.declare_uninterpreted_sort("FmfBoolParam");
        let sort = Sort::Uninterpreted(carrier);
        let function = arena
            .declare_fun("fmf_bp_f", &[Sort::Bool, sort], sort)
            .unwrap();
        let predicate = arena.declare_fun("fmf_bp_p", &[sort], Sort::Bool).unwrap();
        let constant = arena.declare("fmf_bp_c", sort).unwrap();
        let binder = arena.declare("fmf_bp_x", sort).unwrap();
        let x = arena.var(binder);
        let c = arena.var(constant);
        let truth = arena.bool_const(true);
        let falsity = arena.bool_const(false);

        let f_true_x = arena.apply(function, &[truth, x]).unwrap();
        let hit = arena.eq(f_true_x, c).unwrap();
        let miss = arena.not(hit).unwrap();
        let never_c = arena.forall(binder, miss).unwrap();

        let p_x = arena.apply(predicate, &[x]).unwrap();
        let f_p_x = arena.apply(function, &[p_x, x]).unwrap();
        let f_false_x = arena.apply(function, &[falsity, x]).unwrap();
        let same = arena.eq(f_p_x, f_false_x).unwrap();
        let agrees = arena.forall(binder, same).unwrap();

        let assertions = [never_c, agrees];
        let model = find_uf_finite_model(&mut arena, &assertions, &config())
            .unwrap()
            .expect("satisfiable with two carrier elements and p constantly false");
        assert!(model.uninterpreted_cardinality(carrier).unwrap_or(0) >= 2);
        assert!(crate::check_model(&arena, &assertions, &model).unwrap());
    }

    /// Mismatched per-sort cardinalities: one sort is forced to three
    /// elements by ground disequalities while a second sort is pinned to a
    /// singleton by a universal — the deepening must certify without forcing
    /// both sorts to the same bound.
    #[test]
    fn mismatched_sort_cardinalities_certify() {
        let mut arena = TermArena::new();
        let wide = arena.declare_uninterpreted_sort("FmfWide");
        let narrow = arena.declare_uninterpreted_sort("FmfNarrow");
        let wide_sort = Sort::Uninterpreted(wide);
        let narrow_sort = Sort::Uninterpreted(narrow);
        let a1 = arena.declare("fmf_mc_a1", wide_sort).unwrap();
        let a2 = arena.declare("fmf_mc_a2", wide_sort).unwrap();
        let a3 = arena.declare("fmf_mc_a3", wide_sort).unwrap();
        let b = arena.declare("fmf_mc_b", narrow_sort).unwrap();
        let binder = arena.declare("fmf_mc_y", narrow_sort).unwrap();

        let mut assertions = Vec::new();
        for (left, right) in [(a1, a2), (a1, a3), (a2, a3)] {
            let left = arena.var(left);
            let right = arena.var(right);
            let equal = arena.eq(left, right).unwrap();
            assertions.push(arena.not(equal).unwrap());
        }
        let y = arena.var(binder);
        let b_term = arena.var(b);
        let pinned = arena.eq(y, b_term).unwrap();
        assertions.push(arena.forall(binder, pinned).unwrap());

        let model = find_uf_finite_model(&mut arena, &assertions, &config())
            .unwrap()
            .expect("three wide elements and a singleton narrow carrier");
        assert!(model.uninterpreted_cardinality(wide).unwrap_or(0) >= 3);
        assert_eq!(model.uninterpreted_cardinality(narrow), Some(1));
        assert!(crate::check_model(&arena, &assertions, &model).unwrap());
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
