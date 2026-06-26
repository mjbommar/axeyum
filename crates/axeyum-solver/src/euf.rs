//! First-class `QF_UFBV` solving by eager Ackermann elimination (ADR-0013).
//!
//! [`check_with_function_elimination`] is the consumer-facing entry point for
//! queries that use uninterpreted-function applications: it eagerly eliminates
//! functions to `QF_BV` by Ackermann congruence reduction, solves the result
//! with any [`SolverBackend`], and on `sat` projects the model back to function
//! interpretations and replays it against the original assertions with the
//! ground evaluator. Pure `QF_BV` queries pass straight through unchanged.

use std::collections::HashSet;
use std::time::Instant;

use axeyum_ir::{Assignment, FuncId, Op, TermArena, TermId, TermNode, TermStats, Value, eval};
use axeyum_rewrite::{FuncElimError, eliminate_functions};

use crate::backend::{
    CheckResult, SolverBackend, SolverConfig, SolverError, UnknownKind, UnknownReason,
};
use crate::model::Model;

/// Deterministic admission bound on the number of **Ackermann congruence
/// constraints** the eager UF-elimination would generate — graceful `Unknown`,
/// never an unbounded hang/OOM (the standing hard rule).
///
/// Eager elimination ([`eliminate_functions`]) adds, for every *pair* of distinct
/// applications of the same uninterpreted function `f`, one congruence constraint
/// `(⋀ argsᵢ = argsⱼ) ⇒ f(argsᵢ) = f(argsⱼ)`. A function with `k` distinct
/// applications therefore contributes `k·(k−1)/2` constraints — **quadratic** in
/// the application count. This blowup happens entirely *inside a single
/// `eliminate_functions` construction call* (building the O(k²) constraint terms),
/// and the resulting eliminated formula then drives a downstream arithmetic solve
/// whose per-round deadline check cannot intercept a single oversized solve.
/// Neither the wall-clock nor `config.timeout` can bound either step once it has
/// started, so the only sound guard is to refuse *before* construction.
///
/// Measured on a synthetic integer instance with `k` distinct applications of one
/// function (one congruence pair = `k·(k−1)/2`): `k = 60` already generates 1 770
/// constraints whose downstream integer solve runs unbounded past a 2 s
/// `config.timeout` (killed at 200 s); `k = 700` generates 244 650 constraints,
/// taking ~1 s just to *build* and then overflowing the stack in the solve.
///
/// The real cvc5-regression `QF_UFLIA` / `QF_UFIDL` instances that hang under the
/// eager UF+arithmetic path carry hundreds of congruence pairs and hang **in the
/// downstream LIA/IDL solve** (which does not honor `config.timeout`) even when the
/// O(k²) construction itself is cheap — so the bound must sit *below* the smallest
/// hanging instance, not merely below the construction blowup. Measured pair counts:
/// `ooo.rf6` = 117 (truly unbounded, killed at 45 s), `hash_sat_06_19` = 328
/// (unbounded), `simple_cyclic2` = 805 (was unbounded). The committed *bounded*
/// `QF_UFLIA` / `QF_UF` slices (decided within budget) top out at **40** congruence
/// pairs. The value `64` is the documented boundary: above the 40-pair decidable
/// frontier (a 1.6x margin) yet below the 117-pair smallest hang, so every
/// genuinely-decidable in-tree instance is still admitted while the unbounded ones
/// degrade to a sound `Unknown` immediately. Closing the gap above it needs a
/// *lazy* (CEGAR) congruence route and a deadline-honoring LIA/IDL solve, not an
/// eager O(k²) expansion into an unbounded downstream solve.
pub(crate) const MAX_ACKERMANN_CONGRUENCE_PAIRS: usize = 64;

/// Counts the Ackermann congruence constraints the eager UF-elimination would
/// generate for `assertions`: the sum over each uninterpreted function `f` of
/// `k·(k−1)/2`, where `k` is the number of **distinct** (arena-interned)
/// applications of `f` reachable from the assertions.
///
/// This is a sound **over-approximation** of the real pair count: the arena
/// interns syntactically-identical applications to one `TermId`, so counting
/// distinct application `TermId`s never *under*-counts the pairs the eliminator
/// emits (post-rewrite argument canonicalization can only merge applications,
/// reducing the count). Over-approximating keeps the admission guard
/// conservative — it never lets a larger blowup slip through.
///
/// Saturates at [`usize::MAX`] on overflow (an astronomically large instance is
/// refused all the same), so the count itself never panics.
pub(crate) fn ackermann_congruence_pairs(arena: &TermArena, assertions: &[TermId]) -> usize {
    // Distinct application TermIds per function, collected by a deterministic
    // worklist DFS over the (interned) term DAG. `visited` dedups shared
    // subterms so each application is counted once.
    let mut visited: HashSet<TermId> = HashSet::new();
    let mut per_func: Vec<(FuncId, usize)> = Vec::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if let Op::Apply(func) = op {
                let func = *func;
                if let Some((_, count)) = per_func.iter_mut().find(|(f, _)| *f == func) {
                    *count += 1;
                } else {
                    per_func.push((func, 1));
                }
            }
            for &arg in args {
                stack.push(arg);
            }
        }
    }

    per_func.into_iter().fold(0usize, |acc, (_func, k)| {
        let pairs = k.saturating_mul(k.saturating_sub(1)) / 2;
        acc.saturating_add(pairs)
    })
}

/// The deterministic Ackermann admission check shared by every eager
/// UF-elimination entry point: returns `Some(Unknown)` — a graceful, sound refusal
/// — when `assertions` would generate more than [`MAX_ACKERMANN_CONGRUENCE_PAIRS`]
/// congruence constraints (see [`ackermann_congruence_pairs`] for the conservative
/// over-approximation), and `None` (admit) otherwise. `context` names the calling
/// route in the [`UnknownReason`] detail. A refusal only ever turns a would-be
/// unbounded hang/OOM into `Unknown`; it never changes a decided verdict.
pub(crate) fn refuse_oversized_ackermann(
    arena: &TermArena,
    assertions: &[TermId],
    context: &str,
) -> Option<CheckResult> {
    let pairs = ackermann_congruence_pairs(arena, assertions);
    if pairs <= MAX_ACKERMANN_CONGRUENCE_PAIRS {
        return None;
    }
    Some(CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::ResourceLimit,
        detail: format!(
            "{context}: eager Ackermann elimination would emit {pairs} congruence constraints, \
             exceeding the deterministic admission bound of {MAX_ACKERMANN_CONGRUENCE_PAIRS} (the \
             O(k²) expansion and its downstream solve run unbounded; this needs a lazy/CEGAR route)"
        ),
    }))
}

/// Secondary (pathological-input) admission bound on the **congruence-pair
/// count** for the *lazy* (CEGAR) UF+arithmetic route. This sits far above the
/// eager [`MAX_ACKERMANN_CONGRUENCE_PAIRS`] (which the lazy route deliberately
/// exceeds): the lazy loop never asserts all `O(pairs)` constraints up front —
/// it refines only on observed violations — so the *downstream solve* stays
/// bounded by the deadline regardless of pair count. The remaining cost the
/// lazy route still pays eagerly is the **one** [`eliminate_functions`] call it
/// makes to build the abstraction (which, as an artifact of the shared
/// eliminator, also constructs the `O(pairs)` congruence terms it then
/// discards). That construction is `O(pairs)` in time/memory and is *not*
/// deadline-bounded, so an astronomically large pair count is refused here
/// before construction — a graceful `Unknown`, never an OOM. The value is high
/// enough that every realistically-decidable in-tree instance is admitted
/// (the over-bound cvc5-regression files top out in the low thousands of
/// pairs) yet bounds the eager abstraction build to a few million terms.
pub(crate) const MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS: usize = 2_000_000;

/// Secondary (pathological-input) admission bound on the **DAG node count** for
/// the lazy UF+arithmetic route. The lazy abstraction build
/// ([`eliminate_functions`]) recurses over the assertion DAG; a huge graph
/// makes the (memoized, so DAG-linear) rewrite expensive and — together with
/// [`MAX_LAZY_DEPTH`] — bounds the work before any unbounded solve. Refusing an
/// over-large graph here keeps the route bounded; it is a graceful `Unknown`.
pub(crate) const MAX_LAZY_DAG_NODES: u64 = 2_000_000;

/// Secondary (pathological-input) admission bound on the **maximum term depth**
/// for the lazy UF+arithmetic route. The shared eliminator's `rewrite`
/// ([`eliminate_functions`]) and the upstream e-graph passes recurse on the
/// term structure, so a deeply-nested assertion can **stack-overflow before any
/// deadline check fires** (the exact failure mode `6233a7c` documented for the
/// eager path). Refusing beyond this depth keeps the route bounded and
/// crash-free. `64 Ki` is far above any realistic decidable nesting (the
/// over-bound cvc5-regression files are < 100 deep) yet well below a depth that
/// would overflow the default stack during the recursive rewrite.
pub(crate) const MAX_LAZY_DEPTH: u64 = 65_536;

/// Whether an over-eager-bound instance is *also* beyond the secondary
/// (pathological-input) bounds for the lazy route — in which case even the lazy
/// CEGAR path cannot help (its one eager abstraction build / recursive rewrite
/// would blow up or stack-overflow) and the instance must still be refused fast.
///
/// Returns `Some(Unknown)` (refuse) when the pair count exceeds
/// [`MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS`], the DAG exceeds [`MAX_LAZY_DAG_NODES`],
/// or the term depth exceeds [`MAX_LAZY_DEPTH`]; `None` (admit to the lazy route)
/// otherwise. All three checks run on iterative (non-recursive) passes
/// ([`ackermann_congruence_pairs`], [`TermStats::compute`]) so the guard itself
/// never recurses or hangs. A refusal only ever replaces a would-be hang/OOM/
/// stack-overflow with a sound `Unknown`; it never changes a decided verdict.
fn refuse_pathological_for_lazy(
    arena: &TermArena,
    assertions: &[TermId],
    context: &str,
) -> Option<CheckResult> {
    let pairs = ackermann_congruence_pairs(arena, assertions);
    if pairs > MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS {
        return Some(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: format!(
                "{context}: lazy Ackermann abstraction build would still construct {pairs} \
                 congruence terms, exceeding the secondary bound of \
                 {MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS}"
            ),
        }));
    }
    let stats = TermStats::compute(arena, assertions);
    if stats.dag_nodes > MAX_LAZY_DAG_NODES {
        return Some(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: format!(
                "{context}: query has {} DAG nodes, exceeding the lazy-route bound of \
                 {MAX_LAZY_DAG_NODES}",
                stats.dag_nodes
            ),
        }));
    }
    if stats.max_depth > MAX_LAZY_DEPTH {
        return Some(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: format!(
                "{context}: query term depth {} exceeds the lazy-route bound of {MAX_LAZY_DEPTH} \
                 (recursive rewrite would risk stack overflow)",
                stats.max_depth
            ),
        }));
    }
    None
}

/// The bounded **lazy-Ackermann fallback** for UF+arithmetic instances that the
/// eager admission bound ([`MAX_ACKERMANN_CONGRUENCE_PAIRS`]) would refuse.
///
/// Many such over-bound instances decide fine via the *lazy* (CEGAR) congruence
/// route ([`check_with_uf_arithmetic_lazy`]): it abstracts each application and
/// adds congruence constraints **on demand**, so it never pays the eager
/// `O(pairs)` downstream-solve blowup. This helper is the additive bridge: when
/// `refuse_oversized_ackermann` *would* fire (pairs > eager bound) **and** the
/// instance is not pathological ([`refuse_pathological_for_lazy`] admits it),
/// it tries the lazy route under the real `config`; a `Sat`/`Unsat` within
/// budget is returned, an `Unknown`/deadline degrades gracefully. Pathological
/// inputs (huge / deeply-nested) still refuse fast — never a hang or
/// stack-overflow.
///
/// Returns `Some(result)` when this over-bound instance was routed (decided or a
/// graceful `Unknown`), and `None` when the eager bound did **not** fire — the
/// caller then proceeds on the unchanged eager path, so small / in-bound
/// instances are byte-identical to before.
///
/// # Errors
///
/// Propagates [`SolverError`] from the lazy route's IR builders / dispatcher.
pub(crate) fn try_lazy_arith_for_overbound(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    context: &str,
) -> Result<Option<CheckResult>, SolverError> {
    // Only engage when the EAGER bound would have refused; otherwise signal the
    // caller to keep its byte-identical in-bound behaviour.
    if refuse_oversized_ackermann(arena, assertions, context).is_none() {
        return Ok(None);
    }
    // Genuinely-pathological inputs (even the lazy route's single eager
    // abstraction build / recursive rewrite would blow up): refuse fast.
    if let Some(refusal) = refuse_pathological_for_lazy(arena, assertions, context) {
        return Ok(Some(refusal));
    }
    // Admitted: try the lazy CEGAR route under the real config (deadline-bounded).
    Ok(Some(check_with_uf_arithmetic_lazy(
        arena, assertions, config,
    )?))
}

/// Checks a (possibly function-using) `QF_UFBV` conjunction with `backend`.
///
/// Uninterpreted functions are eliminated to `QF_BV` by Ackermann congruence
/// reduction; a `sat` model is projected back to function interpretations and
/// replayed against the original assertions, so the returned [`Model`] is over
/// the original query (carrying both symbol values and function
/// interpretations).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside the supported
/// fragment, or [`SolverError`] from the backend. A `sat` model that fails to
/// replay is a [`SolverError::Backend`].
pub fn check_with_function_elimination<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let elimination = eliminate_functions(arena, assertions).map_err(map_elim_error)?;
    let eliminated = elimination.assertions().to_vec();
    let result = backend.check(arena, &eliminated, config)?;

    let CheckResult::Sat(model) = result else {
        return Ok(result);
    };

    let assignment = model.to_assignment();
    Ok(project_replay_build(
        arena,
        &elimination,
        assertions,
        &assignment,
    ))
}

/// Projects a candidate model back to function interpretations, replays it
/// against the original `assertions`, and builds the output [`Model`] over the
/// original query — the shared `sat` tail of both the eager and lazy entry
/// points.
///
/// SOUNDNESS: the returned [`CheckResult::Sat`] is reached *only* after every
/// original assertion replays to `Bool(true)` through the ground evaluator
/// (which consults the projected UF interpretation for `Op::Apply`). A failed
/// projection, a non-`true` replay, or any indeterminate evaluation declines to a
/// sound [`CheckResult::Unknown`] — never an emitted (possibly wrong) `Sat`, and
/// never an error (`unknown` is a first-class result, not a failure).
fn project_replay_build(
    arena: &TermArena,
    elimination: &axeyum_rewrite::FunctionElimination,
    assertions: &[TermId],
    assignment: &Assignment,
) -> CheckResult {
    // Project the candidate model back to function interpretations. Arithmetic
    // (`Int`/`Real`) functions now project to a full-`Value`-keyed interpretation
    // (`project_model`); scalar functions to the original `u128`-coded tables.
    // SOUNDNESS rests entirely on the replay check below — a wrong projection can
    // only make replay fail (→ decline), never accept a wrong sat. Any projection
    // error (e.g. a value that cannot be reconstructed) is a sound decline to
    // `Unknown`, not a wrong answer.
    let projected = match elimination.project_model(arena, assignment) {
        Ok(projected) => projected,
        Err(error) => {
            return CheckResult::Unknown(crate::backend::UnknownReason {
                kind: crate::backend::UnknownKind::Incomplete,
                detail: format!("function model projection failed: {error}"),
            });
        }
    };

    // REPLAY CHECK (the soundness anchor): every original assertion must evaluate
    // to `Bool(true)` under the projected model through the ground evaluator
    // (which consults the projected UF interpretation for `Op::Apply`). Any
    // failure, non-Boolean, or indeterminate evaluation is a sound decline to
    // `Unknown` — never an emitted `Sat`.
    for &assertion in assertions {
        match eval(arena, assertion, &projected) {
            Ok(Value::Bool(true)) => {}
            Ok(_) | Err(_) => {
                return CheckResult::Unknown(crate::backend::UnknownReason {
                    kind: crate::backend::UnknownKind::Incomplete,
                    detail: format!(
                        "function sat model replay did not confirm assertion #{}",
                        assertion.index()
                    ),
                });
            }
        }
    }

    // Build a model over the original query (drop the internal fresh
    // application variables) carrying both symbol values and reconstructed
    // function interpretations.
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!fn_app_") {
            continue;
        }
        if let Some(value) = projected.get(symbol) {
            out.set(symbol, value);
        }
    }
    for (func, _name, _params, _result) in arena.functions() {
        if let Some(interp) = projected.function(func) {
            out.set_function(func, interp.clone());
        }
    }
    CheckResult::Sat(out)
}

/// Lazy/on-demand Ackermann for `QF_UFBV` (P1.6): abstracts each uninterpreted
/// application as a fresh variable, solves the abstraction, and adds a
/// functional-consistency lemma `(⋀ args_i = args_j) => fresh_i = fresh_j` ONLY
/// for an application pair a candidate model actually violates (equal argument
/// tuples, unequal results), re-solving until the model is functionally
/// consistent or the abstraction is UNSAT.
///
/// This is a CEGAR refinement of the eager [`check_with_function_elimination`]:
/// instead of asserting a congruence lemma for every pair of same-function
/// applications up front, it starts from the abstraction (the relaxation with no
/// lemmas) and refines only on observed violations. The abstraction is a
/// relaxation (strictly fewer constraints), so an UNSAT abstraction soundly
/// witnesses UNSAT of the original; a functionally-consistent `sat` model
/// projects, replays, and is returned over the original query exactly as in the
/// eager path.
///
/// Termination: there are finitely many application pairs and each lemma is
/// added at most once (tracked by index pair), so the loop adds at most
/// `O(applications²)` lemmas before either deciding UNSAT or returning a
/// consistent model.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside the supported
/// `QF_UFBV` fragment, or [`SolverError`] from the backend. A consistent `sat`
/// model that fails to replay against the original assertions is a
/// [`SolverError::Backend`].
pub fn check_qf_ufbv_lazy<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    check_with_function_consistency(arena, assertions, |a, asserts| {
        backend.check(a, asserts, config)
    })
}

/// EUF + arithmetic (`QF_UFLIA` / `QF_UFLRA`): eliminate uninterpreted functions by
/// **eager Ackermann** congruence reduction (so the consistency constraints
/// `(⋀ argsᵢ = argsⱼ) ⇒ resultᵢ = resultⱼ` are asserted up front for *all*
/// same-function application pairs), then solve the function-free arithmetic result
/// with the general dispatcher [`crate::check_auto`] — never bit-blasting.
///
/// Eager (vs the lazy CEGAR of [`check_qf_ufbv_lazy`]) because the lazy refinement
/// needs the abstracted model to assign every application's result, but an
/// arithmetic solver leaves variables that do not appear in the (post-abstraction)
/// assertions unconstrained — e.g. the *intermediate* result of `g` in `f(g(a))`.
/// Asserting all congruence constraints up front sidesteps that, giving a **complete**
/// decision for the combined conjunction (the classic `f(a)≠f(b) ∧ a≤b ∧ b≤a`,
/// `f(x+0)≠f(x)`, and nested `f(g(a))≠f(g(b)) ∧ a=b` all decide UNSAT).
///
/// `sat` projects the model back and replays it; for an arithmetic-sorted function
/// the witnessing model is not yet built (scalar-keyed function tables) so `sat`
/// degrades to a sound [`CheckResult::Unknown`] — never a wrong answer.
///
/// # Errors
///
/// Propagates [`SolverError`] from the dispatcher / IR builders.
pub fn check_with_uf_arithmetic(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Deterministic admission bound (graceful `unknown`, never an unbounded
    // hang/OOM): the O(k²) eager Ackermann construction and its downstream
    // arithmetic solve both run unbounded past `config.timeout`, so when the bound
    // would fire we DO NOT build them. Instead we first try the **lazy/CEGAR**
    // route (`try_lazy_arith_for_overbound`), which abstracts each application and
    // refines congruence on demand under the real `config` deadline — deciding many
    // such over-bound instances without the eager blowup — and only degrades to a
    // graceful `Unknown` if that route also declines / hits its deadline (or the
    // input is pathological, refused fast). This only ever turns a would-be hang
    // into a decided verdict or a sound `Unknown`; a decided verdict never changes.
    if let Some(result) = try_lazy_arith_for_overbound(arena, assertions, config, "UF+arithmetic")?
    {
        return Ok(result);
    }

    let elimination = eliminate_functions(arena, assertions).map_err(map_elim_error)?;
    let eliminated = elimination.assertions().to_vec();
    let result = crate::check_auto(arena, &eliminated, config)?;
    let CheckResult::Sat(model) = result else {
        return Ok(result);
    };
    let assignment = model.to_assignment();
    Ok(project_replay_build(
        arena,
        &elimination,
        assertions,
        &assignment,
    ))
}

/// **Lazy/CEGAR** EUF + arithmetic (`QF_UFLIA` / `QF_UFLRA`): the on-demand
/// counterpart of the eager [`check_with_uf_arithmetic`]. Instead of asserting
/// every same-function congruence constraint up front (the eager `O(k²)` blowup),
/// it abstracts each application to a fresh result variable, solves the abstraction
/// with the general dispatcher [`crate::check_auto`], and adds a congruence lemma
/// `(⋀ argsᵢ = argsⱼ) ⇒ resultᵢ = resultⱼ` ONLY for an application pair a candidate
/// model actually violates — re-solving until the model is functionally consistent
/// or the abstraction is UNSAT. This decides over-eager-bound instances the eager
/// route refuses, without ever feeding the downstream arithmetic solve the full
/// `O(k²)` constraint set.
///
/// SOUNDNESS is identical to the shared functional-consistency loop: the
/// abstraction is a relaxation (strictly fewer constraints), so an UNSAT
/// abstraction soundly witnesses UNSAT of the original; a functionally-consistent
/// `sat` model projects, replays against the originals, and is returned — a replay
/// failure / arith-sorted-function model that cannot be reconstructed degrades to a
/// sound `Unknown`, never a wrong `Sat`.
///
/// BOUNDEDNESS (the standing hard rule — graceful `Unknown`, never a hang/OOM):
/// every abstraction solve runs under a **shared wall-clock deadline** derived from
/// `config.timeout`; once it passes, the CEGAR loop returns `Unknown(ResourceLimit)`
/// rather than entering another (full-budget) solve. The loop itself terminates in
/// at most `O(applications²)` refinements (each lemma added once). Pathological
/// inputs (huge / deeply-nested) are rejected *before* this runs by the over-bound
/// caller's secondary admission guard, so the one eager abstraction build inside
/// cannot blow up or stack-overflow. When
/// `config.timeout` is `None` the loop is bounded only by its finite refinement
/// count (no wall-clock budget to honor — the same contract as the rest of the
/// dispatcher).
///
/// # Errors
///
/// Propagates [`SolverError`] from the dispatcher / IR builders.
pub fn check_with_uf_arithmetic_lazy(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // A single shared deadline for the WHOLE CEGAR loop: without it, each round's
    // `check_auto` would honor the full `config.timeout` independently, so N rounds
    // could run N×budget (unbounded in aggregate). With it, every per-round solve
    // gets only the *remaining* budget and an exhausted deadline ends the loop with
    // a graceful `Unknown` — the loop is bounded by `config.timeout`, not a multiple.
    let deadline = config.timeout.map(|t| Instant::now() + t);
    check_with_function_consistency(arena, assertions, |a, asserts| {
        if let Some(d) = deadline {
            let now = Instant::now();
            if now >= d {
                return Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::ResourceLimit,
                    detail: "lazy UF+arithmetic exhausted the configured timeout before \
                             converging"
                        .to_string(),
                }));
            }
            // Give this round only the remaining budget, so the aggregate loop stays
            // within `config.timeout`.
            let round_config = config.clone().with_timeout(d - now);
            crate::check_auto(a, asserts, &round_config)
        } else {
            crate::check_auto(a, asserts, config)
        }
    })
}

/// The shared functional-consistency CEGAR loop: abstract each uninterpreted
/// application to a fresh result variable, solve the abstraction with `solve`, and
/// add a congruence lemma `(⋀ argsᵢ = argsⱼ) ⇒ freshᵢ = freshⱼ` for each
/// model-observed violation, to a fixpoint. Sound (the abstraction is a relaxation,
/// so its UNSAT transfers; a `sat` model is projected and replayed against the
/// originals) and terminating (finitely many application pairs; each lemma added
/// once). `solve` decides the abstracted, function-free query — a bit-vector backend
/// ([`check_qf_ufbv_lazy`]) or the arithmetic dispatcher
/// ([`check_with_uf_arithmetic`]).
fn check_with_function_consistency<F>(
    arena: &mut TermArena,
    assertions: &[TermId],
    mut solve: F,
) -> Result<CheckResult, SolverError>
where
    F: FnMut(&mut TermArena, &[TermId]) -> Result<CheckResult, SolverError>,
{
    let elim = eliminate_functions(arena, assertions).map_err(map_elim_error)?;
    if !elim.had_functions() {
        // No uninterpreted functions: nothing to abstract, solve directly.
        return solve(arena, assertions);
    }

    // The application metadata is borrowed from `arena` (the arg slices), so
    // snapshot it into owned data before we start mutating `arena` with lemmas.
    let applications: Vec<(FuncId, Vec<TermId>, axeyum_ir::SymbolId)> = elim
        .applications()
        .into_iter()
        .map(|(func, args, fresh)| (func, args.to_vec(), fresh))
        .collect();

    // Group application indices by function, preserving discovery order.
    let mut groups: Vec<(FuncId, Vec<usize>)> = Vec::new();
    for (idx, (func, _args, _fresh)) in applications.iter().enumerate() {
        if let Some((_, members)) = groups.iter_mut().find(|(g, _)| g == func) {
            members.push(idx);
        } else {
            groups.push((*func, vec![idx]));
        }
    }

    let mut stats = FunctionConsistencyStats::new(applications.len(), &groups);
    let mut working = elim.abstraction().to_vec();
    // Index pairs whose congruence lemma has already been asserted; bounds the
    // loop and prevents re-adding the same lemma.
    let mut added: HashSet<(usize, usize)> = HashSet::new();

    loop {
        stats.solve_rounds += 1;
        let assignment = match solve(arena, &working)? {
            // The abstraction is a relaxation; its UNSAT implies the original's.
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => {
                return Ok(CheckResult::Unknown(stats.wrap_unknown(&reason)));
            }
            CheckResult::Sat(model) => {
                stats.sat_candidates += 1;
                model.to_assignment()
            }
        };

        // Collect every newly-violated pair before mutating the arena, so the
        // `assignment` borrow does not collide with the IR builders.
        let mut new_lemmas: Vec<(usize, usize)> = Vec::new();
        for (_func, members) in &groups {
            for a in 0..members.len() {
                for b in (a + 1)..members.len() {
                    let i = members[a];
                    let j = members[b];
                    let (_fi, args_i, fresh_i) = &applications[i];
                    let (_fj, args_j, fresh_j) = &applications[j];
                    if args_i.len() != args_j.len() {
                        continue;
                    }
                    if added.contains(&(i, j)) {
                        continue;
                    }
                    stats.pair_checks += 1;
                    if args_tuples_equal(arena, args_i, args_j, &assignment) {
                        stats.equal_arg_pairs += 1;
                        if results_differ(&assignment, *fresh_i, *fresh_j) {
                            stats.violated_pairs += 1;
                            new_lemmas.push((i, j));
                        }
                    }
                }
            }
        }

        if new_lemmas.is_empty() {
            // Model is functionally consistent: project, replay, and return.
            let result = project_replay_build(arena, &elim, assertions, &assignment);
            return Ok(match result {
                CheckResult::Unknown(reason) => CheckResult::Unknown(stats.wrap_unknown(&reason)),
                other => other,
            });
        }

        let new_count = new_lemmas.len();
        stats.last_new_lemmas = new_count;
        stats.lemmas_added += new_count;
        for (i, j) in new_lemmas {
            let lemma = congruence_lemma(
                arena,
                &applications[i].1,
                &applications[j].1,
                applications[i].2,
                applications[j].2,
            )?;
            working.push(lemma);
            added.insert((i, j));
        }
    }
}

#[derive(Debug, Clone)]
struct FunctionConsistencyStats {
    applications: usize,
    function_groups: usize,
    potential_pairs: usize,
    solve_rounds: usize,
    sat_candidates: usize,
    pair_checks: usize,
    equal_arg_pairs: usize,
    violated_pairs: usize,
    lemmas_added: usize,
    last_new_lemmas: usize,
}

impl FunctionConsistencyStats {
    fn new(applications: usize, groups: &[(FuncId, Vec<usize>)]) -> Self {
        let potential_pairs = groups.iter().fold(0usize, |acc, (_func, members)| {
            let pairs = members
                .len()
                .saturating_mul(members.len().saturating_sub(1))
                / 2;
            acc.saturating_add(pairs)
        });
        Self {
            applications,
            function_groups: groups.len(),
            potential_pairs,
            solve_rounds: 0,
            sat_candidates: 0,
            pair_checks: 0,
            equal_arg_pairs: 0,
            violated_pairs: 0,
            lemmas_added: 0,
            last_new_lemmas: 0,
        }
    }

    fn summary(&self) -> String {
        format!(
            "applications={}, function_groups={}, potential_pairs={}, solve_rounds={}, \
             sat_candidates={}, pair_checks={}, equal_arg_pairs={}, violated_pairs={}, \
             lemmas_added={}, last_new_lemmas={}",
            self.applications,
            self.function_groups,
            self.potential_pairs,
            self.solve_rounds,
            self.sat_candidates,
            self.pair_checks,
            self.equal_arg_pairs,
            self.violated_pairs,
            self.lemmas_added,
            self.last_new_lemmas
        )
    }

    fn wrap_unknown(&self, reason: &UnknownReason) -> UnknownReason {
        UnknownReason {
            kind: reason.kind,
            detail: format!(
                "lazy function-consistency CEGAR inconclusive ({}): {}",
                self.summary(),
                reason.detail
            ),
        }
    }
}

/// Whether every argument of two applications evaluates to the **same value** under
/// `assignment`. Compares whole [`Value`]s (works for `Int`/`Real` too, unlike
/// `scalar_code`, which only encodes finite scalars).
///
/// If an argument cannot be evaluated — e.g. it references a symbol the abstracted
/// model left unconstrained (the arg appears only inside abstracted applications, so
/// nothing pins it) — the pair is treated as **not provably equal**, so no
/// functional-consistency lemma is added. This is sound (a lemma is only ever added
/// for genuinely equal argument tuples) and graceful (never an error); it can leave
/// a `sat`/`unknown` where a value-dependent congruence would refute, which the
/// `sat`-model replay / arithmetic-`Unknown` guard then handles.
fn args_tuples_equal(
    arena: &TermArena,
    args_i: &[TermId],
    args_j: &[TermId],
    assignment: &Assignment,
) -> bool {
    for (&a, &b) in args_i.iter().zip(args_j) {
        match (eval(arena, a, assignment), eval(arena, b, assignment)) {
            (Ok(va), Ok(vb)) if va == vb => {}
            _ => return false,
        }
    }
    true
}

/// Whether the two fresh result symbols hold different values under `assignment`
/// (an unassigned symbol is treated as a non-match, conservatively no
/// violation).
fn results_differ(
    assignment: &Assignment,
    fresh_i: axeyum_ir::SymbolId,
    fresh_j: axeyum_ir::SymbolId,
) -> bool {
    match (assignment.get(fresh_i), assignment.get(fresh_j)) {
        (Some(vi), Some(vj)) => vi != vj,
        _ => false,
    }
}

/// Builds the functional-consistency lemma
/// `(⋀_k args_i[k] = args_j[k]) => (fresh_i = fresh_j)` over the fresh result
/// symbols of two same-function applications.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] if an IR builder fails.
fn congruence_lemma(
    arena: &mut TermArena,
    args_i: &[TermId],
    args_j: &[TermId],
    fresh_i: axeyum_ir::SymbolId,
    fresh_j: axeyum_ir::SymbolId,
) -> Result<TermId, SolverError> {
    let mut same_args: Option<TermId> = None;
    for (&a, &b) in args_i.iter().zip(args_j) {
        let eq = arena.eq(a, b).map_err(|error| {
            SolverError::Backend(format!("lazy congruence build failed: {error}"))
        })?;
        same_args = Some(match same_args {
            Some(acc) => arena
                .and(acc, eq)
                .map_err(|e| SolverError::Backend(format!("lazy congruence build failed: {e}")))?,
            None => eq,
        });
    }
    let var_i = arena.var(fresh_i);
    let var_j = arena.var(fresh_j);
    let same_result = arena
        .eq(var_i, var_j)
        .map_err(|error| SolverError::Backend(format!("lazy congruence build failed: {error}")))?;
    match same_args {
        Some(guard) => arena.implies(guard, same_result).map_err(|error| {
            SolverError::Backend(format!("lazy congruence build failed: {error}"))
        }),
        // A zero-arity application has a single tuple, so distinct applications
        // of it cannot both exist; defensively, assert equality unguarded.
        None => Ok(same_result),
    }
}

fn map_elim_error(error: FuncElimError) -> SolverError {
    match error {
        FuncElimError::Unsupported(what) => SolverError::Unsupported(what),
        FuncElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    }
}

// ===========================================================================
// Eager Ackermann UF-elimination UNSAT CERTIFICATE (narrows the
// `TrustId::Ackermann` hole for the eager-elimination UNSAT sub-case).
// ===========================================================================
//
// [`check_with_function_elimination`] reaches a TRUSTED `Unsat` for a `QF_UFBV`
// query: it eagerly Ackermann-eliminates the uninterpreted functions
// ([`eliminate_functions`]) to a pure `QF_BV` formula and refutes that. The
// `QF_BV` layer already carries DRAT (`export_qf_bv_unsat_proof` → `check_drat`),
// but the Int/UF→BV *reduction* — that the eliminated formula is a SOUND
// relaxation of the original UF formula — is the `Ackermann` trust hole.
//
// SOUNDNESS DIRECTION (why `QF_BV`-UNSAT ⇒ UF-UNSAT). `eliminate_functions`
// replaces every distinct application `f(a⃗)` by a fresh variable `v_{f(a⃗)}`
// (consistently: identical applications intern to one var) and, for every pair
// of same-`f` applications, appends the **congruence constraint**
// `(⋀ᵢ aᵢ = bᵢ) ⇒ (v_{f(a⃗)} = v_{f(b⃗)})`. Each such constraint is a VALID
// consequence of the semantics of an uninterpreted function (`f` is a function:
// equal arguments force equal results). Therefore EVERY model `M` of the
// original UF formula extends to a model of the eliminated `QF_BV` formula
// (interpret each `v_{f(a⃗)}` as `f^M(a⃗^M)`; the rewritten originals hold because
// the substitution is faithful, and every congruence constraint holds because
// `f^M` is a genuine function). So the eliminated formula is a sound
// over-approximation (relaxation): if it is UNSAT, the original has no model
// either. The congruence set being the FULL pairwise set is what we re-derive;
// note that for the UNSAT direction even a *subset* would remain sound (fewer
// constraints only enlarge the model set), so we never risk an unsound UNSAT by
// the congruence accounting — the witness simply confirms each appended
// constraint is a real, valid congruence (no spurious extra assertion that could
// make a satisfiable formula look UNSAT).
//
// The certificate makes this reduction INDEPENDENTLY RE-CHECKABLE. `recheck`
// re-runs the deterministic elimination on the ORIGINAL assertions, structurally
// re-derives the congruence set from the discovered application pairs and
// confirms the eliminated formula is exactly `rewritten-originals ++
// pairwise-congruence` (so it IS a sound relaxation, witnessed — not asserted),
// re-bit-blasts that eliminated formula to CNF and confirms the stored DIMACS is
// byte-identical (the DRAT refutes precisely the CNF of the re-derived eliminated
// formula), and re-runs `check_drat` over the stored DIMACS/DRAT. Trusting
// nothing the emitter computed.

/// A re-checkable certificate that a `QF_UFBV` query is `Unsat` via **eager
/// Ackermann UF-elimination**: the bit-blasted-CNF DRAT refutation of the
/// (deterministically) function-eliminated formula, plus the witnessed shape of
/// the elimination (the per-function congruence-pair counts) so the reduction
/// can be re-derived and confirmed. See [`AckermannUnsatCertificate::recheck`].
#[derive(Debug, Clone)]
pub struct AckermannUnsatCertificate {
    /// Per-function congruence-pair counts `(func, pairs)` in discovery order:
    /// `pairs = k·(k−1)/2` for a function with `k` distinct applications. Purely
    /// descriptive (re-derived and confirmed by `recheck`); records the witnessed
    /// shape of the Ackermann expansion this certificate stands for.
    congruence_pairs_per_func: Vec<(FuncId, usize)>,
    /// Total appended congruence constraints (`Σ pairs`): the size of the
    /// valid-consequence set the eliminated formula adds over the rewritten
    /// originals. Re-derived and confirmed by `recheck`.
    congruence_constraint_count: usize,
    /// DRAT (+ DIMACS) refutation of the bit-blasted, function-eliminated `QF_BV`
    /// CNF, independently re-checkable by `check_drat`.
    bv_proof: crate::proof::UnsatProof,
}

impl AckermannUnsatCertificate {
    /// The per-function congruence-pair counts `(func, pairs)`, in discovery order.
    #[must_use]
    pub fn congruence_pairs_per_func(&self) -> &[(FuncId, usize)] {
        &self.congruence_pairs_per_func
    }

    /// The total number of appended congruence constraints.
    #[must_use]
    pub fn congruence_constraint_count(&self) -> usize {
        self.congruence_constraint_count
    }

    /// The bit-blasted-CNF DRAT certificate of the function-eliminated formula.
    #[must_use]
    pub fn bv_proof(&self) -> &crate::proof::UnsatProof {
        &self.bv_proof
    }

    /// **Independently re-validates** the whole eager-Ackermann reduction plus the
    /// BV refutation, from the ORIGINAL `assertions` and this certificate's stored
    /// data, trusting nothing the emitter computed:
    ///
    ///  1. re-runs the deterministic [`eliminate_functions`] on `assertions`;
    ///  2. structurally re-derives the pairwise congruence set from the discovered
    ///     application pairs and confirms the eliminated formula is *exactly*
    ///     `rewritten-originals ++ that-congruence-set` (so each appended assertion
    ///     is a VALID UF congruence consequence — the eliminated formula is a sound
    ///     relaxation, witnessed) and that the recorded pair counts match;
    ///  3. re-bit-blasts the re-derived eliminated formula and confirms the stored
    ///     DIMACS is byte-identical (the DRAT refutes precisely *this* CNF);
    ///  4. re-runs `check_drat` (RUP/RAT) over the stored DIMACS/DRAT.
    ///
    /// Returns `Ok(true)` only when all four hold. With the reduction re-derived
    /// (2,3) and the refutation re-checked (4), `QF_BV`-UNSAT ⇒ UF-UNSAT, so this
    /// `Unsat` carries no residual `Ackermann` trust. A `false`/`Err` means the
    /// certificate does not establish the `Unsat` and must not be trusted.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the elimination/bit-blast fails or the stored
    /// DRAT/DIMACS is unparseable.
    pub fn recheck(&self, arena: &TermArena, assertions: &[TermId]) -> Result<bool, SolverError> {
        // (1) Re-run the deterministic elimination on a scratch copy of the
        //     ORIGINAL assertions. We trust nothing the emitter stored: the
        //     eliminated formula and its blast are recomputed here.
        let mut scratch = arena.clone();
        let Ok(elim) = eliminate_functions(&mut scratch, assertions) else {
            return Ok(false);
        };
        if !elim.had_functions() {
            // No applications: nothing was Ackermann-eliminated, so there is no
            // eager-Ackermann reduction for this certificate to stand for.
            return Ok(false);
        }

        // (2) Structurally re-derive the pairwise congruence set and confirm the
        //     eliminated formula is exactly `abstraction ++ congruence`.
        let Some((rederived, per_func)) = rederive_congruence(&mut scratch, &elim) else {
            return Ok(false);
        };
        // The eliminated assertions must be `abstraction` followed by exactly our
        // re-derived congruence constraints — same terms, same order, same count.
        let abstraction = elim.abstraction();
        let eliminated = elim.assertions();
        if eliminated.len() != abstraction.len() + rederived.len() {
            return Ok(false);
        }
        if eliminated[..abstraction.len()] != *abstraction {
            return Ok(false);
        }
        if eliminated[abstraction.len()..] != rederived[..] {
            return Ok(false);
        }
        // The recorded shape must match the witnessed one.
        if per_func != self.congruence_pairs_per_func
            || rederived.len() != self.congruence_constraint_count
        {
            return Ok(false);
        }

        // (3) Re-bit-blast the re-derived eliminated formula and confirm the stored
        //     DIMACS is byte-identical: the DRAT refutes precisely the CNF of the
        //     formula we just re-derived, not some unrelated CNF the emitter chose.
        let eliminated = eliminated.to_vec();
        match crate::proof::export_qf_bv_unsat_proof(&scratch, &eliminated)? {
            crate::proof::UnsatProofOutcome::Proved(fresh) => {
                if fresh.dimacs != self.bv_proof.dimacs {
                    return Ok(false);
                }
            }
            // The re-derived eliminated formula is SAT or undecided: the stored
            // UNSAT certificate cannot stand.
            crate::proof::UnsatProofOutcome::Satisfiable
            | crate::proof::UnsatProofOutcome::Inconclusive => return Ok(false),
        }

        // (4) Independently re-check the stored BV refutation (RUP/RAT) over the
        //     stored DIMACS/DRAT.
        self.bv_proof.recheck()
    }
}

/// The re-derived congruence set: the constraint terms (in eliminator-append
/// order) paired with the per-function congruence-pair counts `(func, pairs)`.
type RederivedCongruence = (Vec<TermId>, Vec<(FuncId, usize)>);

/// Structurally re-derives the eager-Ackermann congruence constraints from an
/// elimination's discovered applications, replicating exactly what
/// [`eliminate_functions`] appends: per function (discovery order), for every
/// `i < j` application pair, `(⋀ₖ argsᵢ[k] = argsⱼ[k]) ⇒ (freshᵢ = freshⱼ)`,
/// with the guard left-folded by `and` in argument order. Returns the constraint
/// terms (in the same order the eliminator appends them) and the per-function
/// pair counts. `None` on an IR builder failure or arity mismatch.
///
/// Because these terms are rebuilt on the SAME (post-elimination) `arena` whose
/// interning gives identity, the returned `TermId`s are directly comparable to
/// the eliminated formula's appended constraints — so a match *witnesses* that
/// every appended assertion is a genuine, valid congruence consequence.
fn rederive_congruence(
    arena: &mut TermArena,
    elim: &axeyum_rewrite::FunctionElimination,
) -> Option<RederivedCongruence> {
    // Snapshot the borrowed application metadata before mutating the arena.
    let applications: Vec<(FuncId, Vec<TermId>, axeyum_ir::SymbolId)> = elim
        .applications()
        .into_iter()
        .map(|(func, args, fresh)| (func, args.to_vec(), fresh))
        .collect();

    // Group application indices by function, preserving discovery order (the
    // same grouping order `eliminate_functions` uses).
    let mut groups: Vec<(FuncId, Vec<usize>)> = Vec::new();
    for (idx, (func, _args, _fresh)) in applications.iter().enumerate() {
        if let Some((_, members)) = groups.iter_mut().find(|(g, _)| g == func) {
            members.push(idx);
        } else {
            groups.push((*func, vec![idx]));
        }
    }

    let mut constraints = Vec::new();
    let mut per_func = Vec::new();
    for (func, members) in &groups {
        let mut pairs = 0usize;
        for a in 0..members.len() {
            for b in (a + 1)..members.len() {
                let (_fi, args_i, fresh_i) = &applications[members[a]];
                let (_fj, args_j, fresh_j) = &applications[members[b]];
                if args_i.len() != args_j.len() {
                    return None;
                }
                let mut same_args: Option<TermId> = None;
                for (&ai, &bj) in args_i.iter().zip(args_j) {
                    let eq = arena.eq(ai, bj).ok()?;
                    same_args = Some(match same_args {
                        Some(acc) => arena.and(acc, eq).ok()?,
                        None => eq,
                    });
                }
                let var_i = arena.var(*fresh_i);
                let var_j = arena.var(*fresh_j);
                let same_result = arena.eq(var_i, var_j).ok()?;
                let constraint = match same_args {
                    Some(guard) => arena.implies(guard, same_result).ok()?,
                    None => same_result,
                };
                constraints.push(constraint);
                pairs += 1;
            }
        }
        per_func.push((*func, pairs));
    }
    Some((constraints, per_func))
}

/// Attempts to produce a fully re-checkable [`AckermannUnsatCertificate`] for a
/// `QF_UFBV` `assertions`: eagerly Ackermann-eliminates the uninterpreted
/// functions ([`eliminate_functions`]), bit-blasts the eliminated `QF_BV` formula,
/// and — if that CNF is `Unsat` — emits the DRAT bundled with the witnessed shape
/// of the elimination.
///
/// Returns `Ok(None)` when there are no functions to eliminate (not the
/// eager-Ackermann fragment), the instance is over the deterministic admission
/// bound (`MAX_ACKERMANN_CONGRUENCE_PAIRS` — graceful, no O(k²) blowup), the
/// eliminated formula is `Sat`, or the proof core stays inconclusive. The verdict
/// path is unchanged; this only adds a certificate when one cleanly exists.
///
/// This is the **certifying** entry point for eager-Ackermann `QF_UFBV` `Unsat`:
/// a returned certificate, re-checked by [`AckermannUnsatCertificate::recheck`]
/// against the same `assertions`, establishes the `Unsat` with no residual
/// `Ackermann` trust for this eager-elimination sub-case.
///
/// # Errors
///
/// Returns [`SolverError`] on an internal elimination/encoding/blast failure.
pub fn certify_ackermann_unsat(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<AckermannUnsatCertificate>, SolverError> {
    // Deterministic admission bound: refuse the O(k²) eager expansion above the
    // cap rather than build it (graceful — no certificate, never a hang).
    if refuse_oversized_ackermann(arena, assertions, "certify_ackermann_unsat").is_some() {
        return Ok(None);
    }

    // Eliminate on a scratch arena (additive; the caller's arena is untouched).
    let mut scratch = arena.clone();
    let elim = eliminate_functions(&mut scratch, assertions).map_err(map_elim_error)?;
    if !elim.had_functions() {
        // No uninterpreted functions: there is no eager-Ackermann reduction to
        // certify here (pure QF_BV has its own exporter).
        return Ok(None);
    }

    // Witness the elimination's shape by structurally re-deriving the congruence
    // set; it must equal what `eliminate_functions` appended.
    let Some((rederived, per_func)) = rederive_congruence(&mut scratch, &elim) else {
        return Ok(None);
    };
    let abstraction = elim.abstraction();
    let eliminated = elim.assertions();
    if eliminated.len() != abstraction.len() + rederived.len()
        || eliminated[..abstraction.len()] != *abstraction
        || eliminated[abstraction.len()..] != rederived[..]
    {
        return Ok(None);
    }
    let congruence_constraint_count = rederived.len();

    let eliminated = eliminated.to_vec();
    match crate::proof::export_qf_bv_unsat_proof(&scratch, &eliminated)? {
        crate::proof::UnsatProofOutcome::Proved(bv_proof) => Ok(Some(AckermannUnsatCertificate {
            congruence_pairs_per_func: per_func,
            congruence_constraint_count,
            bv_proof,
        })),
        crate::proof::UnsatProofOutcome::Satisfiable
        | crate::proof::UnsatProofOutcome::Inconclusive => Ok(None),
    }
}

#[cfg(test)]
#[allow(clippy::many_single_char_names, clippy::similar_names)]
mod tests {
    use super::check_qf_ufbv_lazy;
    use crate::backend::{CheckResult, SolverConfig, UnknownKind, UnknownReason};
    use crate::combined::check_with_all_theories;
    use crate::lia::DEFAULT_INT_WIDTH;
    use crate::sat_bv_backend::SatBvBackend;
    use axeyum_ir::{Sort, TermArena, Value, eval};

    #[test]
    fn lazy_ufbv_refutes_congruence_violation() {
        // f(a) != f(b) AND a = b  over BV8  =>  UNSAT (a lemma is required to
        // refute: the abstraction alone is SAT).
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let fa_ne_fb = {
            let eq = arena.eq(fa, fb).unwrap();
            arena.not(eq).unwrap()
        };
        let a_eq_b = arena.eq(a, b).unwrap();

        let mut backend = SatBvBackend::new();
        let config = SolverConfig::default();
        let result =
            check_qf_ufbv_lazy(&mut backend, &mut arena, &[fa_ne_fb, a_eq_b], &config).unwrap();
        assert_eq!(result, CheckResult::Unsat);
    }

    #[test]
    fn lazy_function_consistency_unknown_reports_cegar_stats() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let assertion = arena.eq(fa, fb).unwrap();

        let result = super::check_with_function_consistency(&mut arena, &[assertion], |_a, _q| {
            Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "inner timeout".to_string(),
            }))
        })
        .unwrap();

        let CheckResult::Unknown(reason) = result else {
            panic!("expected wrapped unknown, got {result:?}");
        };
        assert_eq!(reason.kind, UnknownKind::ResourceLimit);
        assert!(reason.detail.contains("lazy function-consistency CEGAR"));
        assert!(reason.detail.contains("applications=2"));
        assert!(reason.detail.contains("function_groups=1"));
        assert!(reason.detail.contains("potential_pairs=1"));
        assert!(reason.detail.contains("solve_rounds=1"));
        assert!(reason.detail.contains("sat_candidates=0"));
        assert!(reason.detail.contains("inner timeout"));
    }

    #[test]
    fn lazy_ufbv_sat_model_replays() {
        // f(a) = c AND a = b  over BV8  =>  SAT, and the returned model replays.
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_const(8, 0x2a).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fa_eq_c = arena.eq(fa, c).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let originals = [fa_eq_c, a_eq_b];

        let mut backend = SatBvBackend::new();
        let config = SolverConfig::default();
        let result = check_qf_ufbv_lazy(&mut backend, &mut arena, &originals, &config).unwrap();
        let CheckResult::Sat(model) = result else {
            panic!("expected SAT, got {result:?}");
        };
        let assignment = model.to_assignment();
        for &t in &originals {
            assert_eq!(
                eval(&arena, t, &assignment).unwrap(),
                Value::Bool(true),
                "original assertion must replay to true"
            );
        }
    }

    #[test]
    fn lazy_ufbv_refutes_nested_application_congruence() {
        // f(f(a)) != a  AND  f(a) = a  over BV8. Here one application's argument is
        // itself an abstracted application: f(a) -> v1, f(f(a)) -> v2, with v1 = a
        // forced. The on-demand lemma (a = v1) => (v1 = v2) then forces v2 = a,
        // contradicting f(f(a)) != a. Exercises lazy Ackermann over nested apps.
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let a = arena.bv_var("a", 8).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ffa = arena.apply(f, &[fa]).unwrap();
        let ffa_ne_a = {
            let eq = arena.eq(ffa, a).unwrap();
            arena.not(eq).unwrap()
        };
        let fa_eq_a = arena.eq(fa, a).unwrap();

        let mut backend = SatBvBackend::new();
        let config = SolverConfig::default();
        let result =
            check_qf_ufbv_lazy(&mut backend, &mut arena, &[ffa_ne_a, fa_eq_a], &config).unwrap();
        assert_eq!(result, CheckResult::Unsat);
    }

    #[test]
    fn lazy_ufbv_nested_application_sat_replays() {
        // f(f(a)) = a  AND  f(a) = b: satisfiable (an involution f with f(a)=b,
        // f(b)=a, a != b). The nested application must project to a coherent
        // function interpretation that replays.
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ffa = arena.apply(f, &[fa]).unwrap();
        let ffa_eq_a = arena.eq(ffa, a).unwrap();
        let fa_eq_b = arena.eq(fa, b).unwrap();
        let originals = [ffa_eq_a, fa_eq_b];

        let mut backend = SatBvBackend::new();
        let config = SolverConfig::default();
        let CheckResult::Sat(model) =
            check_qf_ufbv_lazy(&mut backend, &mut arena, &originals, &config).unwrap()
        else {
            panic!("expected SAT for the involution");
        };
        let assignment = model.to_assignment();
        for &t in &originals {
            assert_eq!(
                eval(&arena, t, &assignment).unwrap(),
                Value::Bool(true),
                "nested-application sat model must replay"
            );
        }
    }

    #[test]
    fn lazy_ufbv_matches_eager_differential() {
        // ~300 deterministic-random small QF_UFBV formulas; the lazy verdict must
        // agree with the eager full-theory verdict whenever both decide.
        let config = SolverConfig::default();
        let mut jointly_decided = 0usize;
        let mut unsat_count = 0usize;

        // Simple LCG (no `rand` crate); seeded by a constant, varied per case.
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;

        for _case in 0..300usize {
            let mut arena = TermArena::new();
            let assertions = [build_case(&mut arena, &mut state)];

            let mut lazy_backend = SatBvBackend::new();
            let mut eager_backend = SatBvBackend::new();
            let lazy = check_qf_ufbv_lazy(&mut lazy_backend, &mut arena, &assertions, &config)
                .expect("lazy check");
            let eager = check_with_all_theories(
                &mut eager_backend,
                &mut arena,
                &assertions,
                DEFAULT_INT_WIDTH,
                &config,
            )
            .expect("eager check");

            if let (Some(l), Some(e)) = (verdict(&lazy), verdict(&eager)) {
                assert_eq!(
                    l, e,
                    "lazy/eager disagree on a jointly-decided case (lazy={lazy:?}, eager={eager:?})"
                );
                jointly_decided += 1;
                if !l {
                    unsat_count += 1;
                }
            }
        }

        assert!(
            jointly_decided > 0,
            "expected some jointly-decided cases, got none"
        );
        assert!(
            unsat_count > 0,
            "expected at least one UNSAT case, got none"
        );
    }

    /// Advances a 64-bit LCG and returns a 32-bit draw (no `rand` crate).
    fn next_rand(state: &mut u64) -> u32 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (*state >> 33) as u32
    }

    /// Builds one deterministic-random small `QF_UFBV` formula over `BitVec(4)`
    /// vars and two unary functions, returning its single top-level assertion.
    fn build_case(arena: &mut TermArena, state: &mut u64) -> axeyum_ir::TermId {
        let w = 4u32;
        let f = arena
            .declare_fun("f", &[Sort::BitVec(w)], Sort::BitVec(w))
            .unwrap();
        let g = arena
            .declare_fun("g", &[Sort::BitVec(w)], Sort::BitVec(w))
            .unwrap();
        let x = arena.bv_var("x", w).unwrap();
        let y = arena.bv_var("y", w).unwrap();
        let z = arena.bv_var("z", w).unwrap();

        // Term pool: vars, a constant, f/g applications, and a couple of bv ops.
        let mut pool: Vec<axeyum_ir::TermId> = vec![x, y, z];
        pool.push(
            arena
                .bv_const(w, u128::from(next_rand(state) & 0xf))
                .unwrap(),
        );
        for _ in 0..3 {
            let pick = pool[(next_rand(state) as usize) % pool.len()];
            let app = match next_rand(state) % 2 {
                0 => arena.apply(f, &[pick]).unwrap(),
                _ => arena.apply(g, &[pick]).unwrap(),
            };
            pool.push(app);
        }
        for _ in 0..2 {
            let lhs = pool[(next_rand(state) as usize) % pool.len()];
            let rhs = pool[(next_rand(state) as usize) % pool.len()];
            let op = match next_rand(state) % 3 {
                0 => arena.bv_add(lhs, rhs).unwrap(),
                1 => arena.bv_and(lhs, rhs).unwrap(),
                _ => arena.bv_xor(lhs, rhs).unwrap(),
            };
            pool.push(op);
        }

        // A few eq/diseq atoms.
        let atom_count = 2 + (next_rand(state) % 3) as usize;
        let mut atoms: Vec<axeyum_ir::TermId> = Vec::with_capacity(atom_count);
        for _ in 0..atom_count {
            let lhs = pool[(next_rand(state) as usize) % pool.len()];
            let rhs = pool[(next_rand(state) as usize) % pool.len()];
            let eq = arena.eq(lhs, rhs).unwrap();
            let atom = if next_rand(state) % 2 == 0 {
                eq
            } else {
                arena.not(eq).unwrap()
            };
            atoms.push(atom);
        }

        // Combine atoms into one formula with and/or, then maybe negate.
        let mut formula = atoms[0];
        for &atom in &atoms[1..] {
            formula = if next_rand(state) % 2 == 0 {
                arena.and(formula, atom).unwrap()
            } else {
                arena.or(formula, atom).unwrap()
            };
        }
        if next_rand(state) % 4 == 0 {
            formula = arena.not(formula).unwrap();
        }
        formula
    }

    /// `Some(true)` for SAT, `Some(false)` for UNSAT, `None` for Unknown — the
    /// shared verdict for differential comparison.
    fn verdict(result: &CheckResult) -> Option<bool> {
        match result {
            CheckResult::Sat(_) => Some(true),
            CheckResult::Unsat => Some(false),
            CheckResult::Unknown(_) => None,
        }
    }

    /// Builds an integer UF instance with `n` distinct applications of one unary
    /// function, returned as a **flat** list of equality assertions (one per
    /// adjacent application pair) so the term DAG stays shallow. The instance
    /// forces `n·(n−1)/2` congruence pairs — the quadratic Ackermann blowup —
    /// without a deeply-nested conjunction (which would stack-overflow unrelated
    /// recursive passes, an artifact rather than the bug under test).
    fn build_uf_blowup(arena: &mut TermArena, n: usize) -> Vec<axeyum_ir::TermId> {
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let mut apps = Vec::with_capacity(n);
        for i in 0..n {
            let v = arena.int_var(&format!("v{i}")).unwrap();
            apps.push(arena.apply(f, &[v]).unwrap());
        }
        apps.windows(2)
            .map(|w| arena.eq(w[0], w[1]).unwrap())
            .collect()
    }

    /// Builds an over-eager-bound **UNSAT** integer UF instance that the *lazy*
    /// route decides: `pad` distinct congruence pairs (to push past the eager
    /// `MAX_ACKERMANN_CONGRUENCE_PAIRS`) plus the classic congruence refutation
    /// `f(a) ≠ f(b) ∧ a = b`. The padding applies `f` to `n` fresh, mutually
    /// unconstrained variables — so it adds pairs without making the instance hard —
    /// and the refutation is the only thing forcing UNSAT. A handful of CEGAR
    /// refinements decide it.
    fn build_overbound_unsat(arena: &mut TermArena, n: usize) -> Vec<axeyum_ir::TermId> {
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let mut assertions = Vec::new();
        // Padding: `n` distinct applications => C(n,2) congruence pairs, but all over
        // fresh unconstrained vars (no model violation forces a lemma).
        for i in 0..n {
            let v = arena.int_var(&format!("pad{i}")).unwrap();
            let app = arena.apply(f, &[v]).unwrap();
            // Touch each application and pin its abstract result so the first
            // function-free abstraction has a complete candidate model; the
            // padding arguments remain unconstrained, so they do not force
            // congruence refinements.
            let value = arena.int_const(i as i128);
            let eq = arena.eq(app, value).unwrap();
            assertions.push(eq);
        }
        // The refutation: f(a) != f(b) AND a = b.
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let ne = {
            let eq = arena.eq(fa, fb).unwrap();
            arena.not(eq).unwrap()
        };
        let a_eq_b = arena.eq(a, b).unwrap();
        assertions.push(ne);
        assertions.push(a_eq_b);
        assertions
    }

    #[test]
    fn uf_arith_overbound_unsat_decided_by_lazy() {
        // An UNSAT instance ABOVE the eager admission bound is now DECIDED via the
        // lazy/CEGAR fallback (it was a refused `Unknown` under the eager-only cap).
        // The verdict matches the known-good oracle (congruence: a = b ⇒ f(a) = f(b)
        // contradicts f(a) ≠ f(b)).
        use super::{MAX_ACKERMANN_CONGRUENCE_PAIRS, ackermann_congruence_pairs};
        use std::time::{Duration, Instant};

        // 20 padding applications => C(20,2) = 190 congruence pairs, comfortably above
        // the 64 eager bound, plus the 2-app refutation => well over-bound.
        let mut arena = TermArena::new();
        let assertions = build_overbound_unsat(&mut arena, 20);
        let pairs = ackermann_congruence_pairs(&arena, &assertions);
        assert!(
            pairs > MAX_ACKERMANN_CONGRUENCE_PAIRS,
            "fixture must be over the eager bound, got {pairs} pairs"
        );

        let config = SolverConfig::default().with_timeout(Duration::from_secs(10));

        // Direct lazy entry decides UNSAT.
        let mut a1 = arena.clone();
        let direct = super::check_with_uf_arithmetic_lazy(&mut a1, &assertions, &config).unwrap();
        assert_eq!(
            direct,
            CheckResult::Unsat,
            "lazy UF+arithmetic must refute the over-bound congruence violation"
        );

        // The full `check_auto` dispatch also reaches the same verdict via the
        // over-bound lazy fallback, bounded.
        let mut a2 = arena.clone();
        let start = Instant::now();
        let auto = crate::check_auto(&mut a2, &assertions, &config).unwrap();
        let elapsed = start.elapsed();
        assert_eq!(
            auto,
            CheckResult::Unsat,
            "check_auto must decide the over-bound instance UNSAT via lazy"
        );
        assert!(
            elapsed < Duration::from_secs(10),
            "over-bound lazy decision must stay within budget, took {elapsed:?}"
        );
    }

    #[test]
    fn uf_arith_pathological_blowup_refused_quickly_as_unknown() {
        use super::{
            MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS, ackermann_congruence_pairs,
            check_with_uf_arithmetic,
        };
        use crate::backend::{UnknownKind, UnknownReason};
        use std::time::{Duration, Instant};

        // A pathologically large pair count — above the SECONDARY (lazy) bound — must
        // be refused *before* even the lazy route's single eager abstraction build.
        // `k` apps => C(k,2) pairs; pick the smallest `k` with C(k,2) strictly above
        // MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS by an integer search (no float casts).
        let mut k = 2usize;
        while k * (k - 1) / 2 <= MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS {
            k += 1;
        }
        let mut arena = TermArena::new();
        let assertions = build_uf_blowup(&mut arena, k);
        let pairs = ackermann_congruence_pairs(&arena, &assertions);
        assert!(
            pairs > MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS,
            "fixture must exceed the secondary lazy bound, got {pairs} pairs"
        );

        // Even with a generous 5 s timeout the secondary bound returns *immediately*
        // (the iterative pair count, not the clock, is what stops it).
        let config = SolverConfig::default().with_timeout(Duration::from_secs(5));
        let start = Instant::now();
        let result = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
        let elapsed = start.elapsed();

        assert!(
            matches!(
                result,
                CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::ResourceLimit,
                    ..
                })
            ),
            "expected a ResourceLimit Unknown, got {result:?}"
        );
        assert!(
            elapsed < Duration::from_secs(1),
            "pathological refusal must be effectively instant, took {elapsed:?}"
        );
    }

    #[test]
    fn uf_arith_blowup_via_check_auto_stays_bounded() {
        use std::time::{Duration, Instant};
        // The full `check_auto` dispatch must stay bounded on a large over-bound
        // instance: a 600-app flat instance (179_700 pairs — under the secondary
        // lazy bound, so it is routed to lazy) must return a verdict or a graceful
        // `Unknown` within a small multiple of the budget, never hang.
        let mut arena = TermArena::new();
        let assertions = build_uf_blowup(&mut arena, 600);

        let config = SolverConfig::default().with_timeout(Duration::from_secs(3));
        let start = Instant::now();
        let result = crate::check_auto(&mut arena, &assertions, &config).unwrap();
        let elapsed = start.elapsed();

        // The flat instance is SAT (all results may be equal; args unconstrained), so
        // lazy converges quickly with no violated pair — but a verdict OR a bounded
        // `Unknown` are both acceptable; boundedness is the invariant under test.
        assert!(
            matches!(result, CheckResult::Sat(_) | CheckResult::Unknown(_)),
            "blowup must decide or degrade to Unknown, got {result:?}"
        );
        assert!(
            elapsed < Duration::from_secs(15),
            "check_auto on the blowup must stay bounded, took {elapsed:?}"
        );
    }

    #[test]
    fn committed_bounded_corpora_stay_under_admission_bound() {
        // Calibration guard: every file in the committed *bounded* QF_UFLIA / QF_UF
        // slices (which `check_auto` decides within budget) must stay below the
        // admission bound, so the gate never refuses a decidable instance. Measured
        // max is 40 pairs vs the 512 bound (a 12x margin); the 15 excluded hang
        // files carry tens of thousands of pairs. Skips cleanly if the corpus dir
        // is absent (it is committed in-tree, so normally present).
        use super::{MAX_ACKERMANN_CONGRUENCE_PAIRS, ackermann_congruence_pairs};
        use std::path::Path;
        let roots = [
            "../../corpus/public-curated/non-incremental/QF_UFLIA/cvc5-regress-clean-bounded",
            "../../corpus/public-curated/non-incremental/QF_UF/cvc5-regress-clean-bounded",
        ];
        let mut checked = 0usize;
        let mut max_seen = 0usize;
        for root in roots {
            let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join(root);
            let Ok(entries) = std::fs::read_dir(&dir) else {
                continue;
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().and_then(|e| e.to_str()) != Some("smt2") {
                    continue;
                }
                let Ok(text) = std::fs::read_to_string(&path) else {
                    continue;
                };
                let Ok(script) = axeyum_smtlib::parse_script(&text) else {
                    continue;
                };
                let pairs = ackermann_congruence_pairs(&script.arena, &script.assertions);
                max_seen = max_seen.max(pairs);
                assert!(
                    pairs <= MAX_ACKERMANN_CONGRUENCE_PAIRS,
                    "{} would be newly refused ({pairs} pairs > bound)",
                    path.display()
                );
                checked += 1;
            }
        }
        if checked > 0 {
            assert!(max_seen <= MAX_ACKERMANN_CONGRUENCE_PAIRS);
        }
    }

    #[test]
    fn uf_arith_small_instances_decide_identically() {
        // Verdict invariance: small UF+arithmetic instances (below the bound) still
        // decide exactly as before — the admission gate only touches the blowup.
        use super::check_with_uf_arithmetic;
        let config = SolverConfig::default();

        // UNSAT: f(a) != f(b) AND a = b over Int.
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let ne = {
            let eq = arena.eq(fa, fb).unwrap();
            arena.not(eq).unwrap()
        };
        let a_eq_b = arena.eq(a, b).unwrap();
        let unsat = check_with_uf_arithmetic(&mut arena, &[ne, a_eq_b], &config).unwrap();
        assert_eq!(unsat, CheckResult::Unsat, "congruence refutation must hold");

        // The estimator is well below the bound for this small instance.
        let pairs = super::ackermann_congruence_pairs(&arena, &[ne, a_eq_b]);
        assert!(pairs <= super::MAX_ACKERMANN_CONGRUENCE_PAIRS);
    }
}
