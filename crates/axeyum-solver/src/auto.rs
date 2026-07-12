//! Unified solver front door: [`solve`] decides any supported query, and
//! [`check_auto`] the quantifier-free fragment, by routing on theory features.
//!
//! Engines:
//!
//! - the **bit-blasting composition** ([`crate::check_with_all_theories`]) for
//!   Bool, bit-vectors, arrays, uninterpreted functions, and bounded integers —
//!   it handles arbitrary Boolean structure natively, since `or`/`ite`/… lower
//!   straight to CNF;
//! - the **lazy-SMT / DPLL(T)** loop ([`crate::check_with_lra_dpll`]) for linear
//!   real arithmetic, which also drives a *complete combination* of reals with
//!   the bit-blasted theories: reals share no sort with them, so the only
//!   coupling is propositional and the loop's case split suffices (no
//!   interface-equality propagation);
//! - **quantifiers** ([`check_with_quantifiers`] finite-domain expansion, with a
//!   sound [`prove_unsat_by_instantiation`] fallback for infinite domains),
//!   chained by [`solve`].
//!
//! Every `sat` is replayed through the ground evaluator against the original
//! query, so no routing or combination step can yield an unsound `sat`.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{
    ArraySortKey, Assignment, Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value,
    eval,
};
use axeyum_rewrite::{
    DEFAULT_SOLVE_EQS_FUEL, ModelReconstructionTrail, QuantExpandError, build_app,
    canonicalize_terms, elim_unconstrained, expand_quantifiers, instantiate_universals,
    instantiate_with_triggers, propagate_values, replace_subterms, solve_eqs_bounded,
};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::combined::check_with_all_theories;
use crate::dpll_lia::{check_with_arith_dpll, check_with_lia_dpll};
use crate::lia::DEFAULT_INT_WIDTH;
use crate::lra::{check_with_lia_simplex_within, check_with_lra};
use crate::model::Model;
use crate::qinst_egraph::prove_quantified_unsat_via_egraph;
use crate::quant_guarded_int::{expand_guarded_int_universals, skolemize_positive_existentials};
use crate::route_trace::{DeclineReason, Recorder, RouteTrace, Verdict, with_recorder};
use crate::sat_bv_backend::SatBvBackend;

// Native uses the std clock; wasm uses the `web_time` drop-in (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::{Duration, Instant};
#[cfg(target_arch = "wasm32")]
use web_time::{Duration, Instant};

fn checked_quantified_fast_path(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    if !has_quantifier(arena, assertions) {
        return Ok(None);
    }
    if let Some(result) =
        crate::quant_guard_vacuity_search::decide_quantified_guard_vacuity_sat(arena, assertions)
    {
        return Ok(Some(result));
    }
    if let Some(result) =
        crate::quant_bool_model_sat::decide_quantified_by_bool_model(arena, assertions, config)?
    {
        return Ok(Some(result));
    }
    if crate::quant_bv_alternation_search::find_bv_alternation_counterexample(
        arena, assertions, config,
    )?
    .is_some()
        || crate::quant_negated_exists_search::find_negated_existential_witness(
            arena, assertions, config,
        )?
        .is_some()
        || crate::quant_bv_conjunctive_search::find_bv_conjunctive_universal_instance(
            arena, assertions, config,
        )?
        .is_some()
    {
        return Ok(Some(CheckResult::Unsat));
    }
    Ok(None)
}

/// The unified front door: decides any supported query — quantifier-free or
/// quantified, over any combination of the supported theories.
///
/// - A **quantifier-free** query is dispatched by [`check_auto`].
/// - A **quantified** query is first decided by finite-domain expansion
///   ([`check_with_quantifiers`], complete for `Bool`/`BitVec` domains); if a
///   quantifier ranges over an infinite domain (`Int`/`Real`), it falls back to
///   sound enumerative instantiation ([`prove_unsat_by_instantiation`], which
///   establishes `unsat` and otherwise reports `unknown`).
///
/// # Errors
///
/// Returns [`SolverError`] from the chosen engine; constructs outside the
/// supported fragment surface as [`SolverError::Unsupported`].
pub fn solve(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    if let Some(result) = checked_quantified_fast_path(arena, assertions, config)? {
        return Ok(result);
    }

    // Skolemize top-level existential assertions: `∃x. body` is equisatisfiable
    // with `body[x := fresh]` (the solver picks the witness), so this is exact and
    // — unlike finite expansion — decides infinite-domain existentials too.
    let skolemized = skolemize_top_existentials(arena, assertions)?;
    let assertions = &skolemized;

    // Lazy bit-blasting strategy (P2.1, opt-in via `SolverConfig::lazy_bv`):
    // abstract heavy BV gadgets and CEGAR-refine instead of eager-blasting the
    // multiplier "mountain" up front. Quantifier-free path only; the inner
    // abstraction solves run with the flag cleared so this hook is not re-entered,
    // and it is a safe no-op (just the heavy-op scan) when none are present.
    if config.lazy_bv && !has_quantifier(arena, assertions) {
        let inner = config.clone().with_lazy_bv(false);
        return Ok(crate::lazy_bv::solve_lazy_bv_abstraction(arena, assertions, &inner)?.result);
    }

    if !has_quantifier(arena, assertions) {
        return check_auto(arena, assertions, config);
    }

    // Valid-universal elimination (sat-side universal-closure validity check):
    // a top-level `∀x. body` with a quantifier-free body is *valid* (hence the
    // assertion is satisfiable) iff `¬body[x := c]` is UNSAT for a fresh
    // constant `c`. Proven-valid universals are replaced by `true` — exact (a
    // valid universal is true in every model) and strictly additive (a universal
    // we cannot prove valid is left untouched, so the problem is never weakened).
    // This decides standalone valid universals over Int/Real/UF that the
    // instantiation/MBQI fallback — which can only conclude `unsat`/`unknown` —
    // never reaches. The sub-checks dispatch to the quantifier-free decider only,
    // so this hook cannot re-enter itself.
    let eliminated =
        crate::quant_valid_universal::eliminate_valid_universals(arena, assertions, config)?;
    let assertions: &[TermId] = &eliminated.0;
    // If every universal was eliminated, the residual is quantifier-free and the
    // ordinary QF dispatch decides it directly.
    if eliminated.1 && !has_quantifier(arena, assertions) {
        return check_auto(arena, assertions, config);
    }

    // Vacuous-universal elimination: a top-level `∀x. body` (QF body) in which the
    // bound variable `x` is *truth-irrelevant* — every arithmetic atom mentioning
    // `x` has net `x`-coefficient `0` after linear normalization, and `x` appears
    // nowhere else — is logically equivalent to `body[x := 0]`. This decides the
    // residual `∀x. x + c >= x` (⟺ `c >= 0`) that skolemizing `∃y.∀x. x + y >= x`
    // leaves, which the *valid*-universal pass cannot (it is not valid). Exact
    // (changes no model) and strictly additive (a universal not proven vacuous is
    // left untouched), so it never weakens the problem nor risks a wrong verdict.
    let vacuous = crate::quant_vacuous_universal::eliminate_vacuous_universals(arena, assertions)?;
    let assertions: &[TermId] = &vacuous.0;
    if vacuous.1 && !has_quantifier(arena, assertions) {
        return check_auto(arena, assertions, config);
    }

    // Exact finite equality partition (ADR-0101): a closed Bool/Int formula in
    // which every Int binder is observed only through equality to explicit
    // constants has finitely many behavioral cells. Search returns a verdict
    // only after the independent original-IR checker accepts its certificate.
    if crate::quant_eq_partition_search::equality_partition_refutation(arena, assertions).is_some()
    {
        return Ok(CheckResult::Unsat);
    }

    // Unsatisfiable-universal detection: a top-level `∀x. (c·x ⋈ t)` whose body
    // is a *single* linear arithmetic atom in which `x` genuinely appears (net
    // coefficient `c ≠ 0`), `t` is `x`-free, and `⋈ ∈ {<, ≤, >, ≥, =}` (never
    // `≠`) is **false in every model** — an unbounded linear function of `x`
    // cannot satisfy a one-sided bound or an equality for *all* `x`. So such an
    // assertion makes the whole query `unsat`. This runs *after* the vacuous
    // pass so the complementary `c = 0` case is already rewritten away (no
    // overlap), and decides standalone `∀x. x > 0`, `∀x. 2·x = 5`, `∀x. x ≤ y`,
    // and the residual of `∃y.∀x. x ≤ y` (after `∃`-skolemization). Strictly
    // additive: only ever `unknown` → `unsat` for the proven-always-false shape.
    if crate::quant_unsat_universal::detect_unsatisfiable_universal(arena, assertions) {
        return Ok(CheckResult::Unsat);
    }

    // Single-variable real Fourier-Motzkin: a top-level `∀x:Real. φ` with a
    // quantifier-free body over linear real atoms is decided *exactly* by
    // eliminating `x` from `¬φ` (since `∀x. φ ⟺ ¬∃x. ¬φ`, and real FM is exact).
    // This decides the *multi-atom* real universals the vacuous and
    // unsat-single-atom passes above decline — e.g. `∀x. (x ≥ 0 ∧ x ≤ 10)`
    // (false ⇒ unsat) and `∀x. (x ≤ 0 ∨ x > 0)` (valid ⇒ rewrites to `true`).
    // Per-assertion: an `unsat` result decides the whole query; a `Rewrite`
    // replaces the universal with an equivalent `x`-free term that re-dispatches.
    // Strictly additive — every shape outside the exactly-eliminable real
    // fragment declines and is left byte-identical.
    //
    // Integer universals get a *sound one-directional* extension: a top-level
    // `∀x:Int. φ` is run through the same FM core treating `x` as a real, and
    // rewritten to `true` *iff* the real relaxation `∀x:Real. φ` is **valid**
    // (`Int ⊆ Real`, so a real-valid universal is integer-valid). This is the
    // ONLY verdict the integer path may act on: a real-`unsat` or a non-trivial
    // real-residual would be *unsound* on `ℤ` (the integer universal can still
    // hold in the gaps between integers, e.g. `∀x:Int. (x ≤ 0 ∨ x ≥ 1)`), so
    // those decline and the integer universal is left to the other passes. The
    // integer path runs *after* `quant_unsat_universal` above, so an
    // integer-false *single-atom* universal (`∀x:Int. x > 0`) is already
    // decided `unsat` there and never reaches here. Strictly additive: only
    // ever `unknown` → `true`-rewrite, never an `unsat`, never a wrong `sat`.
    let mut fm_rewritten: Vec<TermId> = Vec::with_capacity(assertions.len());
    let mut fm_changed = false;
    for &assertion in assertions {
        let outcome = crate::quant_fourier_motzkin::eliminate_real_universal(arena, assertion)
            // The real path declines `Sort::Int` universals. For a *closed*
            // integer universal (body mentions only `x`), the exact integer-
            // emptiness decision below decides BOTH verdicts — including the
            // inter-integer-gap cases the real relaxation declines (e.g.
            // `∀x:Int. (x ≤ 0 ∨ x ≥ 1)` is real-invalid but integer-valid).
            .or_else(|| {
                crate::quant_fourier_motzkin::eliminate_int_universal_closed(arena, assertion)
            })
            // On a decline from the closed path (an *open* integer universal,
            // whose bounds are symbolic), fall back to the sound one-directional
            // relaxation (valid-only ⇒ `true`-rewrite) the open case still needs.
            .or_else(|| {
                crate::quant_fourier_motzkin::eliminate_int_universal_valid(arena, assertion)
            })
            // Finally, the open *constant-width-gap* path: an `∀x:Int. φ` whose
            // `¬φ` clauses are symbolic intervals `[L, U]` of *constant* width
            // `U − L` over *integer-valued* endpoints. Integer content of such an
            // interval is translation-invariant, so it is the same for every
            // (integer) parameter assignment — decided exactly from the width and
            // strictness. Decides the gap the closed and relaxation paths both
            // decline, e.g. `∀x:Int. (x ≤ y ∨ x ≥ y + 2)` (open `(y, y + 2)`,
            // width 2, always holds `y + 1`) ⇒ `unsat`; `∀x:Int. (x ≤ y ∨ x ≥
            // y + 1)` (open `(y, y + 1)`, width 1, no integer) ⇒ `true`-rewrite.
            // Strictly additive: only ever `unknown` → a provably-correct verdict;
            // any clause outside the constant-width / integer-valued fragment (a
            // symbolic-width interval like `(y, z + 2)` with distinct params)
            // declines and is left byte-identical.
            .or_else(|| {
                crate::quant_fourier_motzkin::eliminate_int_universal_open_gap(arena, assertion)
            });
        match outcome {
            Some(crate::quant_fourier_motzkin::FmOutcome::Unsat) => {
                return Ok(CheckResult::Unsat);
            }
            Some(crate::quant_fourier_motzkin::FmOutcome::Rewrite(chi)) => {
                fm_changed = true;
                fm_rewritten.push(chi);
            }
            None => fm_rewritten.push(assertion),
        }
    }
    let fm_assertions: &[TermId] = if fm_changed {
        &fm_rewritten
    } else {
        assertions
    };
    if fm_changed && !has_quantifier(arena, fm_assertions) {
        return check_auto(arena, fm_assertions, config);
    }
    let assertions = fm_assertions;

    // Bounded `∀∃` witness synthesis (sat-side, one-directional): a prenex
    // `∀x⃗. ∃z. body` query whose inner existential `z` (Int/Real) is bounded by
    // clean `±1`-coefficient linear atoms is decided **Sat** by synthesizing a
    // Skolem witness `z := g(x⃗)`. The checked identity subclass also admits an
    // exact same-width BV universal witness. This decides
    // `∀x:Int. ∃z:Int. z > x` (g = x + 1), `issue4328-nqe` (b = a), and similar
    // shapes the finite-expansion / MBQI / e-matching fallbacks — which have no
    // sat-side ∀∃ decision — only ever report `unknown`.
    // Strictly additive and strictly one-directional: it returns `Sat` only for a
    // validated witness and otherwise declines (never `unsat`, never a wrong `sat`),
    // so it is safe to try before the refutation fallbacks. The validity sub-check
    // dispatches to the quantifier-free decider only, so it cannot re-enter here.
    if let Some(result) =
        crate::quant_exists_witness::decide_forall_exists_by_witness(arena, assertions, config)?
    {
        return Ok(result);
    }

    match check_with_quantifiers(arena, assertions, config) {
        // A finite-expansion `unknown` or an unsupported domain both leave room
        // for the sound refutation fallbacks. Try congruence-aware e-matching on
        // the e-graph keystone first (Track 2, P2.6): it instantiates inferred
        // triggers *modulo the ground congruence*, so equalities the bespoke loop
        // misses fire here. Its result is only ever `unsat` (sound — instances are
        // implied) or `unknown`; on `unknown` the model-based instantiation loop
        // (MBQI, which itself defers to the trigger-based family) takes over.
        Ok(CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {
            match prove_quantified_unsat_via_egraph(arena, assertions, config)? {
                CheckResult::Unsat => Ok(CheckResult::Unsat),
                _ => prove_unsat_by_mbqi(arena, assertions, config),
            }
        }
        other => other,
    }
}

/// Extracts a **minimal unsatisfiable core** of `assertions`: the indices of a
/// jointly-unsatisfiable subset in which every member is necessary (dropping any
/// one makes the rest satisfiable or undecided). Theory-agnostic — it works for
/// any query [`solve`] can decide.
///
/// The algorithm is deletion-based: starting from the full (unsat) set, it tries
/// removing each assertion in turn and keeps the removal only when the remainder
/// is still **definitively** `unsat` (an `unknown` remainder is conservatively
/// kept, so the result is always a genuine core). It costs `O(n)` solver calls
/// for `n` assertions and re-decides the final core as a defensive self-check.
///
/// Returns `Ok(None)` when the whole set is satisfiable or could not be decided
/// (`unknown`), so there is no core to report.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for queries outside the supported
/// fragment, or [`SolverError`] from the underlying engine, including a
/// [`SolverError::Backend`] if the extracted core fails to re-decide as `unsat`.
pub fn unsat_core(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<Vec<usize>>, SolverError> {
    // Only an unsatisfiable query has a core.
    if !matches!(solve(arena, assertions, config)?, CheckResult::Unsat) {
        return Ok(None);
    }

    // Deletion-based minimization over the assertion indices, in a fixed order
    // for determinism. `core` always denotes an unsatisfiable subset.
    let mut core: Vec<usize> = (0..assertions.len()).collect();
    for candidate in 0..assertions.len() {
        if !core.contains(&candidate) {
            continue;
        }
        let trial: Vec<TermId> = core
            .iter()
            .filter(|&&i| i != candidate)
            .map(|&i| assertions[i])
            .collect();
        // Keep the removal only if the smaller set is *definitively* unsat; an
        // `unknown` remainder cannot justify dropping the assertion.
        if !trial.is_empty() && matches!(solve(arena, &trial, config)?, CheckResult::Unsat) {
            core.retain(|&i| i != candidate);
        }
    }

    // Defensive self-check: the minimized subset must still be unsat.
    let subset: Vec<TermId> = core.iter().map(|&i| assertions[i]).collect();
    if !matches!(solve(arena, &subset, config)?, CheckResult::Unsat) {
        return Err(SolverError::Backend(
            "unsat-core self-check failed: extracted core is not unsatisfiable".to_owned(),
        ));
    }
    Ok(Some(core))
}

/// Skolemizes each top-level existential assertion `∃x. body` to `body[x := s]`
/// for a fresh constant `s` of `x`'s sort — equisatisfiable, and (unlike finite
/// expansion) complete for infinite domains. Non-existential assertions and
/// existentials in non-top-level positions are left unchanged.
fn skolemize_top_existentials(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut out = Vec::with_capacity(assertions.len());
    let mut k = 0u32;
    for &a in assertions {
        if let TermNode::App {
            op: Op::Exists(sym),
            args,
        } = arena.node(a)
        {
            let (sym, body) = (*sym, args[0]);
            let sort = arena.symbol(sym).1;
            let skolem = arena
                .declare_internal(&format!("!sk_{k}"), sort)
                .map_err(err)?;
            k += 1;
            let bound = arena.var(sym);
            let fresh = arena.var(skolem);
            let mut map: HashMap<TermId, TermId> = HashMap::new();
            map.insert(bound, fresh);
            let mut memo: HashMap<TermId, TermId> = HashMap::new();
            out.push(replace_subterms(arena, body, &map, &mut memo).map_err(err)?);
        } else {
            out.push(a);
        }
    }
    Ok(out)
}

/// Whether any assertion contains a quantifier.
fn has_quantifier(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = assertions.to_vec();
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

/// Decides any supported quantifier-free query, dispatching to the appropriate
/// engine: the lazy-SMT loop when reals are present (combined with the
/// bit-blasted theories), the bit-blasting composition otherwise. Integer
/// reasoning uses the default bounded bit-blasting width ([`DEFAULT_INT_WIDTH`]);
/// use the specific entry points for finer control.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for queries outside the supported
/// fragment, or [`SolverError`] from the chosen engine.
pub fn check_auto(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Thin wrapper: the *same* dispatch as `check_auto_explained`, with no trace
    // recorder. The recorder is a pure side effect at the existing decide/decline
    // sites — it never participates in a branch condition — so this returns
    // byte-for-byte the verdict `check_auto_explained` does (verdict invariance,
    // pinned by `tests/route_trace.rs`).
    let result = check_auto_with_recorder(arena, assertions, config, &mut None)?;
    if matches!(result, CheckResult::Unknown(_)) {
        // Integer-algebraic identity refutation (QF_NIA): cheap, exact, unsat-only.
        if crate::nra_real_root::integer_algebraic_refutation(arena, assertions) {
            return Ok(CheckResult::Unsat);
        }
        if let Some(unsat) = try_conjunct_refutation(arena, assertions, config)? {
            return Ok(unsat);
        }
        if let Some(verdict) = try_disjunct_refutation(arena, assertions, config)? {
            return Ok(verdict);
        }
        if let Some(verdict) = try_finite_domain_split(arena, assertions, config)? {
            return Ok(verdict);
        }
    }
    Ok(result)
}

/// Last-resort refutation for a `unknown` verdict: flatten the top-level
/// conjuncts and solve each ALONE with a small budget. If any single conjunct is
/// `unsat`, the whole conjunction is `unsat` — sound, because the dropped
/// conjuncts only ADD constraints (an unsat sub-system stays unsat under more
/// constraints). Only fires with ≥ 2 conjuncts (nothing to gain otherwise) under
/// a finite budget; the recursion terminates because a single-conjunct sub-solve
/// re-enters here, sees `< 2`, and stops. A `sat` conjunct is ignored (it says
/// nothing about the conjunction). Decides `issue3480`-style queries where one
/// conjunct (`a = 7 − a²`, no integer root) is alone unsat but buried in an `and`
/// beside constraints that route the whole query to `unknown`.
fn try_conjunct_refutation(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let Some(total) = config.timeout else {
        return Ok(None); // unbounded ⇒ skip (avoid runaway sub-solves)
    };
    let mut conjuncts: Vec<TermId> = Vec::new();
    for &a in assertions {
        collect_top_conjuncts(arena, a, &mut conjuncts);
    }
    conjuncts.sort_unstable();
    conjuncts.dedup();
    if conjuncts.len() < 2 || conjuncts.len() > 64 {
        return Ok(None);
    }
    // Split HALF the budget across the conjuncts: the fallback adds ≤ ~50%
    // wall-clock over the (already-`unknown`) main solve.
    let n = u32::try_from(conjuncts.len()).unwrap_or(64);
    let per = total / (2 * n);
    if per.is_zero() {
        return Ok(None);
    }
    let sub = config.clone().with_timeout(per);
    for &c in &conjuncts {
        if matches!(check_auto(arena, &[c], &sub)?, CheckResult::Unsat) {
            return Ok(Some(CheckResult::Unsat));
        }
    }
    Ok(None)
}

/// Last-resort refutation for a `unknown` verdict: flatten the top-level
/// conjuncts and solve each top-level disjunction *alone* with a small budget.
/// If every branch of every disjunction is unsat, the whole conjunction is unsat.
/// A satisfiable branch is returned only when its model canonically replays against
/// the untouched original assertions.
fn try_disjunct_refutation(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let Some(total) = config.timeout else {
        return Ok(None); // unbounded ⇒ skip (avoid runaway sub-solves)
    };
    let mut conjuncts: Vec<TermId> = Vec::new();
    for &a in assertions {
        collect_top_conjuncts(arena, a, &mut conjuncts);
    }
    let mut disjunctions: Vec<Vec<TermId>> = Vec::new();
    let mut rest: Vec<TermId> = Vec::new();
    for &c in &conjuncts {
        match as_disjunction(arena, c) {
            Some(ds) => disjunctions.push(ds),
            None => rest.push(c),
        }
    }
    if disjunctions.is_empty() {
        return Ok(None);
    }
    let mut branches: u64 = 1;
    for d in &disjunctions {
        branches = branches.saturating_mul(d.len() as u64);
        if branches > MAX_DISJUNCTIVE_BRANCHES {
            return Ok(None);
        }
    }
    if branches < 2 {
        return Ok(None);
    }
    let n = u32::try_from(branches).unwrap_or(u32::MAX);
    let per = total / (2 * n);
    if per.is_zero() {
        return Ok(None);
    }
    let sub = config.clone().with_timeout(per);
    let mut idx = vec![0usize; disjunctions.len()];
    let mut all_unsat = true;
    loop {
        let mut branch: Vec<TermId> = Vec::with_capacity(disjunctions.len() + rest.len());
        for (di, d) in disjunctions.iter().enumerate() {
            branch.push(d[idx[di]]);
        }
        branch.extend_from_slice(&rest);
        match check_auto(arena, &branch, &sub)? {
            CheckResult::Sat(model) => {
                if matches!(crate::check_model(arena, assertions, &model), Ok(true)) {
                    return Ok(Some(CheckResult::Sat(model)));
                }
                all_unsat = false;
            }
            CheckResult::Unsat => {}
            CheckResult::Unknown(_) => all_unsat = false,
        }
        let mut pos = 0;
        loop {
            idx[pos] += 1;
            if idx[pos] < disjunctions[pos].len() {
                break;
            }
            idx[pos] = 0;
            pos += 1;
            if pos == disjunctions.len() {
                return Ok(if all_unsat {
                    Some(CheckResult::Unsat)
                } else {
                    None
                });
            }
        }
    }
}

/// Upper bound on the cartesian-product branch count of a finite-domain
/// case-split ([`try_finite_domain_split`]). Past this the fan-out is left to the
/// (unchanged) width ladder rather than spawning a large sub-solve fleet.
const MAX_DISJUNCTIVE_BRANCHES: u64 = 32;

fn as_disjunction(arena: &TermArena, term: TermId) -> Option<Vec<TermId>> {
    let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    if args.len() < 2 {
        return None;
    }
    Some(args.to_vec())
}

const MAX_FINITE_DOMAIN_BRANCHES: u64 = 64;

/// If `term` is a disjunction `(or d₁ … dₖ)` (k ≥ 2) whose every disjunct is an
/// equality `(= a b)`, returns the disjuncts; else `None`. Equality disjuncts are
/// what make the case-split ([`try_finite_domain_split`]) pay: each chosen
/// equality is unconditional in its branch, so the branch's own preprocessing
/// propagates it (a `(< x 5)`-style region disjunct would not, and splitting it
/// only multiplies work — hence the equality restriction).
fn as_equality_disjunction(arena: &TermArena, term: TermId) -> Option<Vec<TermId>> {
    let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    if args.len() < 2 {
        return None;
    }
    let args = args.to_vec();
    if args
        .iter()
        .all(|&d| matches!(arena.node(d), TermNode::App { op: Op::Eq, .. }))
    {
        Some(args)
    } else {
        None
    }
}

/// Case-split a `unknown` query on its top-level FINITE-DOMAIN disjunctions —
/// conjuncts `(or (= v e₁) … (= v eₖ))` whose every disjunct is an equality.
///
/// `D₁ ∧ … ∧ Dₘ ∧ rest` is satisfiable **iff** some choice of one equality from
/// each `Dᵢ`, conjoined with `rest`, is satisfiable. So:
/// - every branch `unsat` ⇒ the whole query is `unsat`;
/// - any branch `sat` ⇒ the whole query is `sat` — that branch's model satisfies
///   every `Dᵢ` (its chosen equality is a disjunct of `Dᵢ`, so `Dᵢ` holds) and
///   `rest` (included verbatim), hence the original conjunction;
/// - otherwise (some branch `unknown`, none `sat`) we cannot conclude ⇒ decline.
///
/// Restricting to EQUALITY disjuncts keeps each branch cheap (see
/// [`as_equality_disjunction`]): e.g. `rewriting-sums` (`x∈{5,7,9}`, `y∈{x+1,x+2}`,
/// `z∈{y+5,y+10}`, `z²>10⁹`) splits into 12 branches, each of which propagates to
/// a concrete `z` and refutes `z²>10⁹`. Fires ONLY on an `Unknown` verdict (never
/// slowing the decided fast path) and only for a small branch product; each branch
/// re-enters `check_auto` with no equality-disjunction left, so the recursion
/// bottoms out. Sound: it never emits a wrong `unsat` (a branch it cannot decide
/// forces a decline) and its `sat` is a genuine model of the original.
fn try_finite_domain_split(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let Some(total) = config.timeout else {
        return Ok(None); // unbounded ⇒ skip (avoid runaway sub-solves)
    };
    let mut conjuncts: Vec<TermId> = Vec::new();
    for &a in assertions {
        collect_top_conjuncts(arena, a, &mut conjuncts);
    }
    // Partition into finite-domain (all-equality) disjunctions and the rest.
    let mut disjunctions: Vec<Vec<TermId>> = Vec::new();
    let mut rest: Vec<TermId> = Vec::new();
    for &c in &conjuncts {
        match as_equality_disjunction(arena, c) {
            Some(ds) => disjunctions.push(ds),
            None => rest.push(c),
        }
    }
    if disjunctions.is_empty() {
        return Ok(None); // nothing to case-split
    }
    // Bound the branch product; a large fan-out declines to the width ladder.
    let mut branches: u64 = 1;
    for d in &disjunctions {
        branches = branches.saturating_mul(d.len() as u64);
        if branches > MAX_FINITE_DOMAIN_BRANCHES {
            return Ok(None);
        }
    }
    if branches < 2 {
        return Ok(None);
    }
    // Split HALF the budget across the branches (bounded fallback overhead over
    // the already-`unknown` main solve).
    let n = u32::try_from(branches).unwrap_or(u32::MAX);
    let per = total / (2 * n);
    if per.is_zero() {
        return Ok(None);
    }
    let sub = config.clone().with_timeout(per);
    // Enumerate the cartesian product via a mixed-radix index vector.
    let mut idx = vec![0usize; disjunctions.len()];
    let mut all_unsat = true;
    loop {
        let mut branch: Vec<TermId> = Vec::with_capacity(disjunctions.len() + rest.len());
        for (di, d) in disjunctions.iter().enumerate() {
            branch.push(d[idx[di]]);
        }
        branch.extend_from_slice(&rest);
        match check_auto(arena, &branch, &sub)? {
            CheckResult::Sat(model) => {
                if matches!(crate::check_model(arena, assertions, &model), Ok(true)) {
                    return Ok(Some(CheckResult::Sat(model)));
                }
                all_unsat = false;
            }
            CheckResult::Unsat => {}
            CheckResult::Unknown(_) => all_unsat = false,
        }
        // Advance the mixed-radix counter; wrapping past the last position ends it.
        let mut pos = 0;
        loop {
            idx[pos] += 1;
            if idx[pos] < disjunctions[pos].len() {
                break;
            }
            idx[pos] = 0;
            pos += 1;
            if pos == disjunctions.len() {
                return Ok(if all_unsat {
                    Some(CheckResult::Unsat)
                } else {
                    None // some branch unknown, none sat ⇒ cannot conclude
                });
            }
        }
    }
}

/// Like [`check_auto`], but additionally returns a [`RouteTrace`]: the ordered
/// record of which dispatch routes were tried and why each declined, with the
/// decisive route last. This is purely additive telemetry — the returned
/// [`CheckResult`] is **identical** to the one [`check_auto`] returns for the
/// same query (the trace is captured at the same branch points that already
/// exist; nothing is re-decided).
///
/// # Errors
///
/// Returns the same [`SolverError`] as [`check_auto`].
pub fn check_auto_explained(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<(CheckResult, RouteTrace), SolverError> {
    let mut trace = RouteTrace::new();
    let result = check_auto_with_recorder(arena, assertions, config, &mut Some(&mut trace))?;
    // Conjunct-split refutation fallback (mirrors `check_auto` for verdict
    // invariance), recorded as a `Decided` route so the trace's terminal entry
    // matches the upgraded `unsat`. Run BEFORE the invariant block so it sees the
    // final verdict.
    let result = if matches!(result, CheckResult::Unknown(_))
        && crate::nra_real_root::integer_algebraic_refutation(arena, assertions)
    {
        trace.record_decided("integer-algebraic-refutation", Verdict::Unsat);
        CheckResult::Unsat
    } else if matches!(result, CheckResult::Unknown(_))
        && let Some(unsat) = try_conjunct_refutation(arena, assertions, config)?
    {
        trace.record_decided("conjunct-refutation", Verdict::Unsat);
        unsat
    } else if matches!(result, CheckResult::Unknown(_))
        && let Some(verdict) = try_disjunct_refutation(arena, assertions, config)?
    {
        let recorded = if matches!(verdict, CheckResult::Sat(_)) {
            Verdict::Sat
        } else {
            Verdict::Unsat
        };
        trace.record_decided("disjunct-refutation", recorded);
        verdict
    } else if matches!(result, CheckResult::Unknown(_))
        && let Some(verdict) = try_finite_domain_split(arena, assertions, config)?
    {
        let v = if matches!(verdict, CheckResult::Sat(_)) {
            Verdict::Sat
        } else {
            Verdict::Unsat
        };
        trace.record_decided("finite-domain-split", v);
        verdict
    } else {
        result
    };
    // Structural trace invariant: an `Unknown` verdict always ends in a
    // Declined entry. Individual early-exit paths (an ultra-tight budget can
    // expire between any two recorded attempts — feature scans, lifting,
    // preprocessing) each try to record their own decline, but the invariant
    // is enforced here at the boundary so no present or future early return
    // can leave a probe-only trace (a slow-runner-only gap the route-trace
    // tests caught twice).
    if let CheckResult::Unknown(reason) = &result
        && !trace
            .attempts()
            .iter()
            .any(|a| matches!(a.outcome, crate::route_trace::RouteOutcome::Declined(_)))
    {
        trace.record_declined("dispatch-early-exit", DeclineReason::from_unknown(reason));
    }
    Ok((result, trace))
}

/// The shared dispatch for [`check_auto`] / [`check_auto_explained`]. `rec` is an
/// optional [`RouteTrace`] recorder, threaded down the single dispatch path;
/// recording is a side effect only, so the verdict is independent of `rec`.
fn check_auto_with_recorder(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    rec: &mut Recorder<'_>,
) -> Result<CheckResult, SolverError> {
    // Probe: classify the quantifier-free fragment and record the planned route
    // ordering as the trace's first entry, so the trail explains the dispatch.
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let Some(has_quantifier) = contains_quantifier_within(arena, assertions, deadline) else {
        return Ok(CheckResult::Unknown(timeout_reason(
            "auto-dispatch timeout while scanning quantifiers",
        )));
    };
    let Some(features) = Features::scan_within(arena, assertions, deadline) else {
        return Ok(CheckResult::Unknown(timeout_reason(
            "auto-dispatch timeout while scanning theory features",
        )));
    };
    record_probe(&features, has_quantifier, rec);
    if crate::term_identity::term_identity_refutation(arena, assertions).is_some() {
        with_recorder(rec, |t| {
            t.record_decided("term-identity-refuter", Verdict::Unsat);
        });
        return Ok(CheckResult::Unsat);
    }
    if features.has_array
        && let Some(model) = crate::array_fifo::fifo_ia04_sat_model(arena, assertions)
    {
        with_recorder(rec, |t| {
            t.record_decided("fifo-ia04-sat-witness", Verdict::Sat);
        });
        return Ok(CheckResult::Sat(model));
    }
    if features.has_array
        && let Some(result) = dispatch_array_unsat_refuters(arena, assertions, config)?
    {
        with_recorder(rec, |t| t.record_result("array-unsat-refuter", &result));
        return Ok(result);
    }
    if features.has_int
        && !has_quantifier
        && !contains_smtlib_unspecified_arith(arena, assertions)
        && let Some(result) = decide_bounded_int_box_by_evaluation(arena, assertions)
    {
        with_recorder(rec, |t| t.record_result("int-box-eval", &result));
        return Ok(result);
    }

    // Word-level preprocessing (P1.2) is owned here, at the default-path entry, when
    // `config.preprocess` is set; otherwise dispatch directly. The full model-sound
    // pipeline (not just canonicalization) is what moves the public QF_BV number —
    // it shrinks formulas below the bit-blast-size ceiling (ADR-0037; fair p4dfa
    // measurement: 3 s 2→4, 20 s 3→7 decided, DISAGREE=0).
    // The word-level pipeline (`solve_eqs`/`elim_unconstrained`) is a
    // quantifier-free transform — it treats the assertion list as ground. On a
    // query carrying a quantifier it is skipped (the quantifier path needs the
    // original structure for trigger/e-matching); only quantifier-free queries are
    // preprocessed.
    if config.preprocess && !has_quantifier {
        // Best-effort: if *any* step of the preprocessed path fails — a reduction
        // pass (e.g. canonicalize cannot fold an uninterpreted-function application)
        // or the reduced solve / model reconstruction — fall back to solving the
        // ORIGINAL unreduced query. Preprocessing is only ever an optimization, never
        // a correctness dependency, so a failure must degrade, not propagate.
        let preprocessed = match preprocess_reduce(arena, assertions, deadline) {
            Ok(Some((reduced, trail))) => {
                dispatch_reduced(arena, assertions, &reduced, &trail, config, deadline, rec)
            }
            Ok(None) => {
                // Telemetry: record the budget decline so a trace never ends
                // with only the probe entry under an ultra-tight budget.
                with_recorder(rec, |t| {
                    t.record_declined(
                        "preprocess",
                        DeclineReason::from_unknown(&timeout_reason(
                            "preprocessing timeout before reduced dispatch",
                        )),
                    );
                });
                return Ok(CheckResult::Unknown(timeout_reason(
                    "preprocessing timeout before reduced dispatch",
                )));
            }
            Err(error) => Err(error),
        };
        if let Ok(result) = preprocessed {
            Ok(result)
        } else {
            with_recorder(rec, |t| {
                t.record_declined("preprocess", DeclineReason::Incomplete(reduced_fallback()));
            });
            check_auto_inner(arena, assertions, config, rec)
        }
    } else {
        check_auto_inner(arena, assertions, config, rec)
    }
}

/// The [`UnknownReason`] recorded when the preprocessed path errors and dispatch
/// degrades to the original unreduced query (a route note, not a verdict).
fn reduced_fallback() -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: "preprocessed path errored; degraded to the original query".to_owned(),
    }
}

/// Records the probe preamble — the detected quantifier-free fragment and the
/// planned route ordering — as the trace's first entry. Cheap and deterministic;
/// reuses the existing [`Features`] scan and quantifier detection, adding no new
/// fragment-detection engine.
fn record_probe(features: &Features, has_quantifier: bool, rec: &mut Recorder<'_>) {
    with_recorder(rec, |trace| {
        let mut tags: Vec<&str> = Vec::new();
        if has_quantifier {
            tags.push("quant");
        }
        if features.has_datatype {
            tags.push("datatype");
        }
        if features.has_real {
            tags.push("real");
        }
        if features.has_int {
            tags.push("int");
        }
        if features.has_function || features.has_uninterpreted_sort {
            tags.push("uf");
        }
        if features.has_array {
            tags.push("array");
        }
        if features.has_bitblast
            && !features.has_int
            && !features.has_array
            && !features.has_function
            && !features.has_uninterpreted_sort
        {
            tags.push("bv");
        }
        if tags.is_empty() {
            tags.push("bool");
        }
        trace.record_probe(format!("fragment {{{}}}", tags.join(",")));
    });
}

fn timeout_reason(detail: impl Into<String>) -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::Timeout,
        detail: detail.into(),
    }
}

fn config_with_remaining_deadline(
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> SolverConfig {
    let Some(deadline) = deadline else {
        return config.clone();
    };
    let mut out = config.clone();
    out.timeout = Some(deadline.saturating_duration_since(Instant::now()));
    out
}

/// Whether an [`UnknownKind`] is a **resource/budget** decline (wall-clock,
/// deterministic resource, memory, translation-node, or CNF-size cap) rather than a
/// logical incompleteness. A budget `Unknown` from a route that ran out of its
/// configured budget mid-decision must NOT be silently swallowed by a later,
/// strictly-less-capable fallback that then reports a *logical* `Unknown` — that
/// would mask the true (budget) cause and look like a capability regression to a
/// fresh-budget caller. Returning the budget `Unknown` verbatim keeps the honest,
/// first-class result; `unknown` is never an error and never a wrong verdict.
fn is_budget_unknown_kind(kind: UnknownKind) -> bool {
    matches!(
        kind,
        UnknownKind::Timeout
            | UnknownKind::ResourceLimit
            | UnknownKind::MemoryLimit
            | UnknownKind::NodeBudget
            | UnknownKind::EncodingBudget
    )
}

/// Whether any declared uninterpreted function has an `Int`/`Real` parameter or
/// result — the signal to route through EUF + arithmetic combination
/// ([`crate::check_with_uf_arithmetic`]) rather than the bit-blasting fallback.
fn has_arithmetic_function(arena: &TermArena) -> bool {
    let is_arith = |s: &axeyum_ir::Sort| matches!(s, axeyum_ir::Sort::Int | axeyum_ir::Sort::Real);
    arena
        .functions()
        .any(|(_func, _name, params, result)| params.iter().any(is_arith) || is_arith(&result))
}

/// Whether any assertion's term tree contains a `forall`/`exists` binder.
fn contains_quantifier_within(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Option<bool> {
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if past_deadline(deadline) {
            return None;
        }
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return Some(true);
            }
            for &arg in &**args {
                if past_deadline(deadline) {
                    return None;
                }
                stack.push(arg);
            }
        }
    }
    Some(false)
}

/// Run the model-sound word-level preprocessing pipeline (`canonicalize` →
/// `propagate_values` → fuel-bounded `solve_eqs` → `elim_unconstrained` →
/// re-`canonicalize`), dispatch the reduced query through [`check_auto_inner`]
/// (with preprocessing cleared, so it is not re-applied), and on `sat` reconstruct
/// the eliminated variables and replay against the **original** assertions — the
/// same checkable-`sat` discipline as [`crate::check_with_preprocessing`]. `unsat`
/// of the reduced (equisatisfiable) problem transfers directly.
fn preprocess_reduce(
    arena: &mut TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<Option<(Vec<TermId>, ModelReconstructionTrail)>, SolverError> {
    if past_deadline(deadline) {
        return Ok(None);
    }
    let canonical = canonicalize_terms(arena, assertions)
        .map_err(|error| SolverError::Backend(format!("canonicalize failed: {error}")))?
        .terms;
    if past_deadline(deadline) {
        return Ok(None);
    }
    let (after_values, mut trail) = propagate_values(arena, &canonical)
        .map_err(|error| SolverError::Backend(format!("propagate_values failed: {error}")))?
        .into_parts();
    if past_deadline(deadline) {
        return Ok(None);
    }
    let (reduced, eq_trail) = solve_eqs_bounded(arena, &after_values, DEFAULT_SOLVE_EQS_FUEL)
        .map_err(|error| SolverError::Backend(format!("solve_eqs failed: {error}")))?
        .into_parts();
    trail.append(eq_trail);
    if past_deadline(deadline) {
        return Ok(None);
    }
    let (reduced, unconstrained_trail) = elim_unconstrained(arena, &reduced)
        .map_err(|error| SolverError::Backend(format!("elim_unconstrained failed: {error}")))?
        .into_parts();
    trail.append(unconstrained_trail);
    if past_deadline(deadline) {
        return Ok(None);
    }
    let reduced = canonicalize_terms(arena, &reduced)
        .map_err(|error| SolverError::Backend(format!("post-solve canonicalize failed: {error}")))?
        .terms;
    if past_deadline(deadline) {
        return Ok(None);
    }
    Ok(Some((reduced, trail)))
}

/// Dispatch the `reduced` query through [`check_auto_inner`] (preprocessing
/// cleared), and on `sat` reconstruct the eliminated variables via `trail` and
/// replay against the **original** assertions — the checkable-`sat` discipline of
/// [`crate::check_with_preprocessing`]. `unsat` of the equisatisfiable reduction
/// transfers directly.
fn dispatch_reduced(
    arena: &mut TermArena,
    assertions: &[TermId],
    reduced: &[TermId],
    trail: &ModelReconstructionTrail,
    config: &SolverConfig,
    deadline: Option<Instant>,
    rec: &mut Recorder<'_>,
) -> Result<CheckResult, SolverError> {
    let inner_config = {
        let mut c = config_with_remaining_deadline(config, deadline);
        c.preprocess = false;
        c
    };
    let result = check_auto_inner(arena, reduced, &inner_config, rec)?;
    // A DEFINITE verdict (Sat/Unsat) from the reduced solve is valid regardless of
    // the wall clock — the deadline is a resource budget, not a correctness gate.
    // Discarding a decided (and, for Sat, about-to-be-replay-checked) verdict just
    // because the budget expired *during the deciding route* needlessly throws away
    // a real answer: measured, `nia-bounded-blast` decides bounded nonlinear SATs
    // like `nia-pythagorean` a hair past the budget, and the old unconditional
    // `past_deadline` gate below turned that decided `sat` into `unknown`. Only an
    // UNDECIDED (`Unknown`) result degrades to the timeout reason.
    let CheckResult::Sat(model) = result else {
        if matches!(result, CheckResult::Unknown(_)) && past_deadline(deadline) {
            return Ok(CheckResult::Unknown(timeout_reason(
                "preprocessed dispatch timeout after reduced solve",
            )));
        }
        return Ok(result);
    };

    // Reconstruct eliminated variables, then replay against the ORIGINAL assertions.
    let reconstructed = trail
        .reconstruct(arena, &model.to_assignment())
        .map_err(|error| {
            SolverError::Backend(format!(
                "preprocessing model reconstruction failed: {error}"
            ))
        })?;
    // No `past_deadline` bail here or in the replay loop below: the reduced solve
    // already produced a DEFINITE `Sat`, and reconstruction + replay are bounded,
    // cheap O(term-size) validation passes — abandoning them on an expired budget
    // would throw away a real, checkable answer (measured: `nia-bounded-blast`
    // decides bounded nonlinear SATs a hair past the budget, and the old bails
    // turned that decided `sat` into `unknown`). The deadline bounds SEARCH, not
    // the final linear validation of an already-decided model.
    for &assertion in assertions {
        if !matches!(
            eval(arena, assertion, &reconstructed),
            Ok(Value::Bool(true))
        ) {
            return Err(SolverError::Backend(format!(
                "preprocessed sat model replay failed: assertion #{} did not evaluate to true",
                assertion.index()
            )));
        }
    }
    let mut out = Model::new();
    for (symbol, _name, _sort) in arena.symbols() {
        if let Some(value) = reconstructed.get(symbol) {
            out.set(symbol, value);
        }
    }
    // Carry uninterpreted-function interpretations through too: an inner
    // QF_UFLIA/QF_UFLRA `sat` reconstructs an `Op::Apply` interpretation, and
    // dropping it would leave the returned model unable to replay a UF query
    // (the original assertions reference `f` — `eval` would raise
    // `UnboundFunction`).
    for (func, _name, _params, _result) in arena.functions() {
        if let Some(interp) = reconstructed.function(func) {
            out.set_function(func, interp.clone());
        }
    }
    // Same for the free-division `/0` witness (P2.5): the replay above succeeded
    // *under* this interpretation (the evaluator consults it on a zero divisor),
    // so dropping it would hand back a model that no longer replays — a wrong
    // `sat` through the preprocessed path.
    for (numerator, quotient) in reconstructed.real_div_zeros() {
        out.set_real_div_zero(numerator, quotient);
    }
    Ok(CheckResult::Sat(out))
}

/// The core auto-dispatcher (coercion handling + theory routing), preprocessing
/// already applied by [`check_auto`]. Callers must not rely on `config.preprocess`
/// here; it is cleared by [`check_auto_preprocessed`] before dispatch.
fn check_auto_inner(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    rec: &mut Recorder<'_>,
) -> Result<CheckResult, SolverError> {
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    // Cheap syntactic even-power refutation, tried BEFORE the int↔real coercion
    // handling. A top-level conjunct of the shape `Σ tᵢ^{2kᵢ} + c < 0` or the
    // equality analogue `Σ tᵢ^{2kᵢ} = c` with `c < 0` is impossible (a sum of
    // even powers is `≥ 0`). The matcher (`nra_even_power`) sees through a
    // `to_real(<int const>)` right side, so it refutes e.g.
    // `(= (* a a) (- 2))` — parsed as `(= (* a a) (to_real (- 2)))` — that
    // otherwise reaches only the (incomplete) Nelson-Oppen coercion relaxation
    // below and returns `unknown`. It is deliberately narrow, re-scannable
    // against the original assertions, and only ever concludes `unsat`, so it
    // never risks a wrong verdict and never reroutes a satisfiable query.
    if crate::nra_even_power::nra_even_power_refutation(arena, assertions).is_some() {
        with_recorder(rec, |t| t.record_decided("nra-even-power", Verdict::Unsat));
        return Ok(CheckResult::Unsat);
    }

    // `to_real` is a ring homomorphism, so fold `to_real(a) ± to_real(b)` into
    // `to_real(a ± b)` (bottom-up): a linear combination of coerced integers
    // collapses to one coercion, which the comparison rewrites below can then
    // eliminate exactly (e.g. `to_real(x) + to_real(y) ≤ 10`).
    let folded = fold_to_real_sums(arena, assertions)?;
    // A `to_real(i)` compared to a rational constant is order-isomorphic to an
    // integer comparison (`to_real(i) ≤ c ⟺ i ≤ ⌊c⌋`, etc.), so rewrite those
    // *exactly* to pure-integer atoms — eliminating the coercion completely (no
    // relaxation, no `unknown`) for the common "coerced int vs literal" pattern.
    // Dually, `to_int(r) = ⌊r⌋` compared to an integer constant rewrites to a
    // pure-real comparison (`to_int(r) ≤ c ⟺ r < c+1`, etc.).
    let r1 = eliminate_to_real_const_compare(arena, &folded)?;
    let assertions = &eliminate_to_int_const_compare(arena, &r1)?;

    // Int↔Real coercions (`to_real`/`to_int`/`is_int`) couple the int and real
    // theories; a complete decision needs Nelson-Oppen. We relax each coercion to
    // a fresh variable of its result sort — shared per distinct term, so a
    // contradiction on the *same* coerced value (e.g. `to_real(i) > 5 ∧
    // to_real(i) < 5`) is still proven — dispatch the decoupled query, and replay
    // any `sat` candidate against the *original* (where the evaluator computes the
    // true coercion). `unsat` of the relaxation is sound; a candidate whose
    // coupling fails on replay is `unknown`.
    let (relaxed, had_coercion) = relax_coercions(arena, assertions)?;
    if !had_coercion {
        if past_deadline(deadline) {
            return Ok(CheckResult::Unknown(timeout_reason(
                "auto-dispatch timeout during arithmetic normalization",
            )));
        }
        let dispatch_config = config_with_remaining_deadline(config, deadline);
        return check_auto_dispatch(arena, assertions, &dispatch_config, rec);
    }
    // A `to_real` coercion couples the integer and real theories. Before the
    // (sound but incomplete) relaxation above, try exact mixed-integer linear
    // branch-and-bound: solve the LP relaxation with the Farkas-checked LRA
    // engine and branch on any coerced integer that comes back fractional. This
    // is *complete* for the linear mixed fragment — `unsat` is anchored by the
    // per-node Farkas certificate and `sat` by replay against the original. Out
    // of that fragment (or on the node budget) it returns `unknown`, and we fall
    // through to the relaxation.
    match check_with_milp(arena, assertions) {
        Ok(CheckResult::Sat(model)) => {
            with_recorder(rec, |t| t.record_decided("milp", Verdict::Sat));
            return Ok(CheckResult::Sat(model));
        }
        Ok(CheckResult::Unsat) => {
            with_recorder(rec, |t| t.record_decided("milp", Verdict::Unsat));
            return Ok(CheckResult::Unsat);
        }
        Ok(CheckResult::Unknown(reason)) => {
            with_recorder(rec, |t| {
                t.record_declined("milp", DeclineReason::from_unknown(&reason));
            });
        }
        Err(_) => {
            with_recorder(rec, |t| {
                t.record_declined("milp", DeclineReason::Unsupported);
            });
        }
    }
    if past_deadline(deadline) {
        return Ok(CheckResult::Unknown(timeout_reason(
            "auto-dispatch timeout after mixed-integer normalization",
        )));
    }
    let dispatch_config = config_with_remaining_deadline(config, deadline);
    match check_auto_dispatch(arena, &relaxed, &dispatch_config, rec)? {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            if assertions
                .iter()
                .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))))
            {
                with_recorder(rec, |t| t.record_decided("coercion-relax", Verdict::Sat));
                Ok(CheckResult::Sat(model))
            } else {
                with_recorder(rec, |t| {
                    t.record_declined(
                        "coercion-relax",
                        DeclineReason::VerifierRejected(
                            "candidate fails the original int↔real coupling".to_owned(),
                        ),
                    );
                });
                Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: "int↔real coercion relaxation: candidate fails the original coupling"
                        .to_owned(),
                }))
            }
        }
        other => Ok(other), // Unsat (sound) or Unknown — already recorded by dispatch
    }
}

/// Node budget for the mixed-integer branch-and-bound; on exhaustion the result
/// is `unknown` (and `check_auto` falls back to the coercion relaxation).
const MAX_MILP_NODES: u32 = 2_000;

/// Decides a conjunctive mixed integer/real (`QF_LIRA`) query — with `to_real`
/// coercions intact — by mixed-integer linear branch-and-bound.
///
/// The query is lowered to an all-real LP by mapping every integer symbol to a
/// fresh real symbol and `to_real(i)` to that same symbol (so the coupling is
/// exact, not relaxed); the integer symbols are remembered as the integrality
/// constraints. Each branch-and-bound node solves the LP with the
/// Farkas-checked [`check_with_lra`] engine: `unsat` at a node is sound
/// (the LP relaxation has *more* solutions than the original), and a `sat` leaf
/// whose integer columns are all integral is **replayed against the original**
/// mixed query through the ground evaluator. Anything outside the linear mixed
/// fragment (nonlinear, `to_int`/`is_int`, bit-vectors, …) or the node budget
/// yields `unknown`, so the caller falls back to the sound relaxation.
fn check_with_milp(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<CheckResult, SolverError> {
    let mut lower = LiraLower::default();
    let mut real_assertions = Vec::with_capacity(assertions.len());
    for &a in assertions {
        real_assertions.push(lower.lower(arena, a)?);
    }
    // The fresh real symbols that must take integer values (former int symbols),
    // paired with the original integer symbol for model projection.
    let int_cols: Vec<(SymbolId, SymbolId)> =
        lower.int_to_real.iter().map(|(&i, &r)| (r, i)).collect();
    let mut budget = MAX_MILP_NODES;
    milp_bnb(arena, &real_assertions, &int_cols, assertions, &mut budget)
}

/// One branch-and-bound subtree over the all-real lowering `real_assertions`.
/// `int_cols` pairs each integrality-constrained real symbol with its original
/// integer symbol; `original` is the untouched mixed query (for `sat` replay).
fn milp_bnb(
    arena: &mut TermArena,
    real_assertions: &[TermId],
    int_cols: &[(SymbolId, SymbolId)],
    original: &[TermId],
    budget: &mut u32,
) -> Result<CheckResult, SolverError> {
    if *budget == 0 {
        // A deterministic search budget was hit (retryable with a larger budget),
        // not fundamental incompleteness — report ResourceLimit consistently with
        // the NRA branch-and-bound / refinement bounds.
        return Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: format!("MILP branch-and-bound exceeded {MAX_MILP_NODES} nodes"),
        }));
    }
    *budget -= 1;
    let model = match check_with_lra(arena, real_assertions)? {
        CheckResult::Unsat => return Ok(CheckResult::Unsat), // LP relaxation unsat ⇒ MILP unsat
        CheckResult::Unknown(r) => return Ok(CheckResult::Unknown(r)),
        CheckResult::Sat(model) => model,
    };
    // Find an integrality-constrained variable with a fractional LP value.
    for &(real_sym, _) in int_cols {
        let Some(Value::Real(q)) = model.get(real_sym) else {
            continue;
        };
        if q.is_integer() {
            continue;
        }
        let floor = q.numerator().div_euclid(q.denominator());
        let var = arena.var(real_sym);
        let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
        // Left branch: var ≤ floor.
        let le_c = arena.real_const(Rational::integer(floor));
        let le = arena.real_le(var, le_c).map_err(err)?;
        let mut left = real_assertions.to_vec();
        left.push(le);
        let left_res = milp_bnb(arena, &left, int_cols, original, budget)?;
        if let CheckResult::Sat(m) = left_res {
            return Ok(CheckResult::Sat(m));
        }
        // Right branch: var ≥ floor + 1.
        let ge_c = arena.real_const(Rational::integer(floor + 1));
        let ge = arena.real_ge(var, ge_c).map_err(err)?;
        let mut right = real_assertions.to_vec();
        right.push(ge);
        let right_res = milp_bnb(arena, &right, int_cols, original, budget)?;
        // The two half-spaces var≤floor / var≥floor+1 cover every integer value,
        // so: sat if either branch is sat; unsat only if *both* are unsat; else
        // unknown (a branch hit the budget).
        return Ok(match (left_res, right_res) {
            (_, CheckResult::Sat(m)) | (CheckResult::Sat(m), _) => CheckResult::Sat(m),
            (CheckResult::Unsat, CheckResult::Unsat) => CheckResult::Unsat,
            (CheckResult::Unknown(r), _) | (_, CheckResult::Unknown(r)) => CheckResult::Unknown(r),
        });
    }
    // All integrality columns are integral: a genuine MILP candidate. Replay it
    // against the *original* mixed query through the ground evaluator.
    let mut assignment = axeyum_ir::Assignment::new();
    let mut projected = Model::new();
    for &(real_sym, int_sym) in int_cols {
        let value = match model.get(real_sym) {
            Some(Value::Real(q)) if q.is_integer() => Value::Int(q.numerator()),
            _ => return Ok(milp_unknown()),
        };
        assignment.set(int_sym, value.clone());
        projected.set(int_sym, value);
    }
    // Carry the genuine real variables straight through.
    for (sym, value) in model.iter() {
        if int_cols.iter().any(|&(r, _)| r == sym) {
            continue; // integer column, already projected to its int symbol
        }
        assignment.set(sym, value.clone());
        projected.set(sym, value);
    }
    for &a in original {
        match eval(arena, a, &assignment) {
            Ok(Value::Bool(true)) => {}
            _ => return Ok(milp_unknown()),
        }
    }
    Ok(CheckResult::Sat(projected))
}

fn milp_unknown() -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: "MILP candidate failed replay against the original query".to_owned(),
    })
}

/// Lowers a mixed integer/real query to an all-real one for the MILP LP oracle:
/// each integer symbol becomes a fresh real symbol, `to_real(i)` becomes that
/// symbol, and the integer linear operators map to their real counterparts.
#[derive(Default)]
struct LiraLower {
    /// Original integer symbol → fresh real symbol.
    int_to_real: std::collections::BTreeMap<SymbolId, SymbolId>,
    memo: HashMap<TermId, TermId>,
}

impl LiraLower {
    fn real_of_int(
        &mut self,
        arena: &mut TermArena,
        int_sym: SymbolId,
    ) -> Result<TermId, SolverError> {
        if let Some(&r) = self.int_to_real.get(&int_sym) {
            return Ok(arena.var(r));
        }
        let name = format!("!milp.{}", int_sym.index());
        let r = arena
            .declare_internal(&name, Sort::Real)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        self.int_to_real.insert(int_sym, r);
        Ok(arena.var(r))
    }

    #[allow(clippy::too_many_lines)]
    fn lower(&mut self, arena: &mut TermArena, t: TermId) -> Result<TermId, SolverError> {
        if let Some(&c) = self.memo.get(&t) {
            return Ok(c);
        }
        let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
        let node = arena.node(t).clone();
        let out = match node {
            TermNode::BoolConst(_) | TermNode::RealConst(_) => t,
            // Bit-vectors (and any other leaf) are outside the mixed LIA/LRA
            // fragment this oracle lowers.
            TermNode::BvConst { .. } | TermNode::WideBvConst(_) => {
                return Err(milp_out_of_fragment());
            }
            TermNode::IntConst(n) => arena.real_const(Rational::integer(n)),
            TermNode::Symbol(s) => match arena.sort_of(t) {
                Sort::Int => self.real_of_int(arena, s)?,
                Sort::Real | Sort::Bool => t,
                _ => return Err(milp_out_of_fragment()),
            },
            TermNode::App { op, args } => {
                // `to_real(i)` collapses to the lowered (real) integer operand.
                if matches!(op, Op::IntToReal) {
                    let inner = self.lower(arena, args[0])?;
                    self.memo.insert(t, inner);
                    return Ok(inner);
                }
                let mut low = Vec::with_capacity(args.len());
                for &a in &args {
                    low.push(self.lower(arena, a)?);
                }
                match op {
                    Op::IntNeg => arena.real_neg(low[0]).map_err(err)?,
                    Op::IntAdd => arena.real_add(low[0], low[1]).map_err(err)?,
                    Op::IntSub => arena.real_sub(low[0], low[1]).map_err(err)?,
                    Op::IntMul => arena.real_mul(low[0], low[1]).map_err(err)?,
                    Op::IntLt => arena.real_lt(low[0], low[1]).map_err(err)?,
                    Op::IntLe => arena.real_le(low[0], low[1]).map_err(err)?,
                    Op::IntGt => arena.real_gt(low[0], low[1]).map_err(err)?,
                    Op::IntGe => arena.real_ge(low[0], low[1]).map_err(err)?,
                    Op::Eq
                    | Op::BoolAnd
                    | Op::BoolOr
                    | Op::BoolNot
                    | Op::BoolXor
                    | Op::BoolImplies
                    | Op::Ite
                    | Op::RealNeg
                    | Op::RealAdd
                    | Op::RealSub
                    | Op::RealMul
                    | Op::RealLt
                    | Op::RealLe
                    | Op::RealGt
                    | Op::RealGe => build_app(arena, op, &low).map_err(err)?,
                    // to_int/is_int, integer div/mod/abs, bit-vectors, arrays, …
                    // are outside the linear mixed fragment this oracle handles.
                    _ => return Err(milp_out_of_fragment()),
                }
            }
        };
        self.memo.insert(t, out);
        Ok(out)
    }
}

fn milp_out_of_fragment() -> SolverError {
    SolverError::Unsupported("term outside the linear mixed integer/real fragment".to_owned())
}

/// Tries to refute an out-of-range `bv2nat` constraint (G2). Abstracts each
/// distinct `bv2nat(b)` to a fresh `Int` variable with its true range bound
/// `0 <= n <= 2^W - 1` and runs the exact integer refuters on the relaxation; an
/// `unsat` of the (range-bounded) relaxation transfers soundly to the original
/// (every model induces one of the relaxation, taking `n := bv2nat(b)`).
///
/// Returns `Ok(true)` only when the original is **provably** `unsat`; `Ok(false)`
/// for "no abstractable `bv2nat`" or "could not refute" (the caller proceeds on
/// the original assertions, where the bit-blaster handles `bv2nat` natively).
///
/// The abstraction declares fresh `!bv2nat.*` symbols and is only ever used to
/// derive `unsat`, so it runs on an isolated **clone** of the arena: the original
/// assertion `TermId`s are index-stable in the clone, and nothing (no fresh
/// symbol, no rewritten term) leaks back into the caller's arena or any sat model.
fn refute_bv2nat_out_of_range(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    let mut scratch = arena.clone();
    let Some(relaxed) =
        crate::bv2nat_bound::abstract_bv2nat_for_refutation(&mut scratch, assertions)?
    else {
        return Ok(false);
    };
    let lin = axeyum_rewrite::eliminate_int_divmod(&mut scratch, &relaxed)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    Ok(
        crate::lia_gcd::prove_lia_unsat_by_diophantine(&scratch, &lin)
            || matches!(
                check_with_lia_simplex_within(
                    &scratch,
                    &lin,
                    config.timeout.and_then(|t| Instant::now().checked_add(t)),
                ),
                Ok(CheckResult::Unsat)
            )
            || matches!(
                check_with_lia_dpll(&mut scratch, &lin, config),
                Ok(CheckResult::Unsat)
            ),
    )
}

/// The exact integer linear-refuter chain (bv2nat-range → Diophantine →
/// LIA-simplex → LIA-DPLL), split from [`check_auto_dispatch`] for length. Each
/// is a sound refuter / complete decider over the linear integer fragment;
/// anything outside it declines (`Unsupported`) and `Ok(None)` is returned so the
/// dispatcher falls through to the nonlinear/bit-blasting tail. Verdict logic is
/// verbatim the inlined original; `rec` only annotates the existing sites.
fn dispatch_int_linear_refuters(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    rec: &mut Recorder<'_>,
) -> Result<Option<CheckResult>, SolverError> {
    // `bv2nat(b)` finite-range refutation (G2): abstract each distinct `bv2nat(b)`
    // to a fresh range-bounded `Int` var and try the exact refuters; an `unsat` of
    // the relaxation transfers soundly. Only ever turns `unknown` into `unsat`.
    if refute_bv2nat_out_of_range(arena, assertions, config)? {
        with_recorder(rec, |t| t.record_decided("bv2nat-range", Verdict::Unsat));
        return Ok(Some(CheckResult::Unsat));
    }
    // `div`/`mod`-by-constant and `abs` are first eliminated into exact linear
    // constraints (equisatisfiable), so the *complete* simplex/DPLL path decides
    // them for both `sat` and `unsat` — not just the sat-only bit-blaster.
    let lin = axeyum_rewrite::eliminate_int_divmod(arena, assertions)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    // Diophantine system refutation: integer (fraction-free) row reduction of the
    // *system* of top-level integer equalities — a sound refutation that decides
    // even *unbounded* systems the simplex/B&B cannot terminate on.
    if crate::lia_gcd::prove_lia_unsat_by_diophantine(arena, &lin) {
        with_recorder(rec, |t| t.record_decided("lia-diophantine", Verdict::Unsat));
        return Ok(Some(CheckResult::Unsat));
    }
    // Deadline-aware: branch-and-bound on an unbounded integer difference
    // constraint (`c > y ∧ c < y+1`) grinds toward the node budget, so honor
    // `config.timeout` here rather than spinning past it.
    match check_with_lia_simplex_within(
        arena,
        &lin,
        config.timeout.and_then(|t| Instant::now().checked_add(t)),
    ) {
        Ok(result) => {
            with_recorder(rec, |t| t.record_result("lia-simplex", &result));
            return Ok(Some(result));
        }
        Err(SolverError::Unsupported(_)) => {
            with_recorder(rec, |t| {
                t.record_declined("lia-simplex", DeclineReason::Unsupported);
            });
        }
        Err(other) => return Err(other),
    }
    if should_route_uf_arith_before_lia_dpll(arena, assertions, features) {
        let pairs = crate::euf::ackermann_congruence_pairs(arena, assertions);
        with_recorder(rec, |t| {
            t.record_declined(
                "lia-dpll",
                DeclineReason::from_unknown(&UnknownReason {
                    kind: UnknownKind::ResourceLimit,
                    detail: format!(
                        "generic LIA DPLL skipped for overbound non-array integer \
                         UF+arithmetic query (ackermann_pairs={pairs}); route the single \
                         large function-free arithmetic abstraction through the UF-aware \
                         lazy CEGAR path instead"
                    ),
                }),
            );
        });
        return Ok(None);
    }
    match check_with_lia_dpll(arena, &lin, config) {
        Ok(mut result) => {
            if let CheckResult::Unknown(reason) = &result
                && features.has_function
                && is_budget_unknown_kind(reason.kind)
            {
                result =
                    CheckResult::Unknown(annotate_lia_budget_before_uf(arena, assertions, reason));
            }
            with_recorder(rec, |t| t.record_result("lia-dpll", &result));
            match &result {
                CheckResult::Unknown(reason)
                    if features.has_function && !is_budget_unknown_kind(reason.kind) =>
                {
                    Ok(None)
                }
                _ => Ok(Some(result)),
            }
        }
        Err(SolverError::Unsupported(_)) => {
            with_recorder(rec, |t| {
                t.record_declined("lia-dpll", DeclineReason::Unsupported);
            });
            Ok(None)
        }
        Err(other) => Err(other),
    }
}

fn should_route_uf_arith_before_lia_dpll(
    arena: &TermArena,
    assertions: &[TermId],
    features: &Features,
) -> bool {
    features.has_int
        && !features.has_real
        && !features.has_array
        && features.has_function
        && has_arithmetic_function(arena)
        && crate::euf::ackermann_congruence_pairs(arena, assertions)
            > crate::euf::MAX_ACKERMANN_CONGRUENCE_PAIRS
}

fn annotate_lia_budget_before_uf(
    arena: &TermArena,
    assertions: &[TermId],
    reason: &UnknownReason,
) -> UnknownReason {
    UnknownReason {
        kind: reason.kind,
        detail: format!(
            "{}; downstream UF-aware routes were not reached because the generic LIA DPLL \
             route exhausted its budget first (arithmetic_function={}, ackermann_pairs={})",
            reason.detail,
            has_arithmetic_function(arena),
            crate::euf::ackermann_congruence_pairs(arena, assertions)
        ),
    }
}

const MAX_PRE_LIA_UF_PROBE_ASSERTIONS: usize = 256;

fn dispatch_arith_uf_overbound_probe_before_lia(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    rec: &mut Recorder<'_>,
) -> Result<Option<CheckResult>, SolverError> {
    if !features.has_int
        || features.has_real
        || features.has_array
        || !features.has_function
        || !has_arithmetic_function(arena)
    {
        return Ok(None);
    }
    let pairs = crate::euf::ackermann_congruence_pairs(arena, assertions);
    if pairs <= crate::euf::MAX_ACKERMANN_CONGRUENCE_PAIRS {
        return Ok(None);
    }
    if assertions.len() > MAX_PRE_LIA_UF_PROBE_ASSERTIONS {
        with_recorder(rec, |t| {
            t.record_declined(
                "uf-arith-lazy-overbound-pre-lia",
                DeclineReason::from_unknown(&UnknownReason {
                    kind: UnknownKind::ResourceLimit,
                    detail: format!(
                        "pre-LIA UF+arithmetic probe skipped for generated query with {} \
                         assertions > {MAX_PRE_LIA_UF_PROBE_ASSERTIONS} (ackermann_pairs={pairs}); \
                         avoid duplicating the large function-free arithmetic skeleton solve",
                        assertions.len()
                    ),
                }),
            );
        });
        return Ok(None);
    }

    // Run on a clone so an inconclusive probe cannot enlarge the caller's arena
    // before the existing generic LIA fallback. Original SymbolId/FuncId values
    // are stable across the clone, so a returned model is still over the original
    // query surface.
    let mut scratch = arena.clone();
    let probe_config = pre_lia_uf_probe_budget(config);
    let probe = crate::euf::try_lazy_arith_for_overbound(
        &mut scratch,
        assertions,
        &probe_config,
        "UF+arithmetic pre-LIA probe",
    );
    let Some(result) = (match probe {
        Ok(result) => result,
        Err(SolverError::Unsupported(_)) => {
            with_recorder(rec, |t| {
                t.record_declined(
                    "uf-arith-lazy-overbound-pre-lia",
                    DeclineReason::Unsupported,
                );
            });
            return Ok(None);
        }
        Err(SolverError::Backend(detail)) => {
            with_recorder(rec, |t| {
                t.record_declined(
                    "uf-arith-lazy-overbound-pre-lia",
                    DeclineReason::VerifierRejected(detail),
                );
            });
            return Ok(None);
        }
        Err(other) => return Err(other),
    }) else {
        return Ok(None);
    };

    with_recorder(rec, |t| match &result {
        CheckResult::Sat(_) => {
            t.record_decided("uf-arith-lazy-overbound-pre-lia", Verdict::Sat);
        }
        CheckResult::Unsat => {
            t.record_decided("uf-arith-lazy-overbound-pre-lia", Verdict::Unsat);
        }
        CheckResult::Unknown(reason) => t.record_declined(
            "uf-arith-lazy-overbound-pre-lia",
            DeclineReason::from_unknown(reason),
        ),
    });

    match result {
        CheckResult::Sat(_) | CheckResult::Unsat => Ok(Some(result)),
        CheckResult::Unknown(_) => Ok(None),
    }
}

/// The uninterpreted-function fast paths (online CDCL(T) EUF → offline EUF
/// enumeration → EUF + linear-arithmetic combination), split from
/// [`check_auto_dispatch`] for length. Returns `Some(verdict)` when one decides
/// the query (or the real-sorted-UF `Unknown` that must short-circuit), else
/// `Ok(None)` so the dispatcher falls through to the array / bit-blast tail.
/// Verdict logic is verbatim the inlined original; `rec` only annotates the
/// existing sites.
fn dispatch_uf_fast_paths(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    rec: &mut Recorder<'_>,
) -> Result<Option<CheckResult>, SolverError> {
    // Deterministic admission bound (graceful `unknown`, never an unbounded
    // hang/OOM) for **UF + arithmetic** instances, applied *before* any of the
    // recursive e-graph / arithmetic passes below. The eager UF+arithmetic route
    // these instances eventually reach expands each function's `k` applications to
    // `k·(k−1)/2` Ackermann congruence constraints, whose O(k²) construction and
    // unbounded downstream LIA/IDL solve neither honor `config.timeout`; and the
    // upstream e-graph passes themselves recurse over the (often deeply-nested)
    // assertion and can stack-overflow before any deadline check fires.
    //
    // When the eager bound `MAX_ACKERMANN_CONGRUENCE_PAIRS` would fire, we DO NOT
    // enter those passes. Instead we first try the **lazy/CEGAR** UF+arithmetic
    // route (`try_lazy_arith_for_overbound`), which abstracts each application and
    // refines congruence on demand under the real `config` deadline — deciding many
    // over-bound instances without the eager blowup — and degrades to a sound
    // `Unknown` only if that route also declines / hits its deadline (pathological
    // huge / deeply-nested inputs are refused fast inside, before any recursive
    // build). Gated on an arithmetic-sorted function being **actually applied in the
    // assertions** (`features.has_function`, not merely *declared*): the lazy route
    // recursively solves its abstraction with `check_auto`, and the abstraction has
    // no `Op::Apply` nodes, so without this `has_function` guard that recursive
    // `check_auto` would re-enter this very block (the function is still declared) and
    // loop on a pure-arithmetic query that the LIA refuters below already decide. So
    // pure-`QF_UF` (no arith function) and post-abstraction pure-arithmetic queries
    // are both byte-identically unaffected. SOUNDNESS: this only ever replaces a
    // would-be hang with a decided verdict or a sound `Unknown`; no verdict changes
    // (a query with no applied arith function has zero congruence pairs, so the eager
    // bound never fired for it anyway).
    if features.has_function
        && has_arithmetic_function(arena)
        && let Some(result) =
            crate::euf::try_lazy_arith_for_overbound(arena, assertions, config, "UF+arithmetic")?
    {
        let array_unknown = features.has_array && matches!(result, CheckResult::Unknown(_));
        with_recorder(rec, |t| match &result {
            CheckResult::Sat(_) => t.record_decided("uf-arith-lazy-overbound", Verdict::Sat),
            CheckResult::Unsat => {
                t.record_decided("uf-arith-lazy-overbound", Verdict::Unsat);
            }
            CheckResult::Unknown(reason) => t.record_declined(
                "uf-arith-lazy-overbound",
                DeclineReason::from_unknown(reason),
            ),
        });
        if !array_unknown {
            return Ok(Some(result));
        }
    }

    // Eliminate uninterpreted-sort `ite` *only for the e-graph deciders* (which
    // treat `ite` opaquely): equisatisfiable, so verdicts are unchanged. Confined
    // to **pure-UF** instances (no arithmetic) so the UF+arithmetic dispatch path
    // — which tries the e-graph first before its combination route — never pays
    // the lift's cost (provably zero impact on its wall-clock budget).
    let lifted_euf;
    let euf_assertions: &[TermId] = if features.has_int || features.has_real {
        assertions
    } else {
        lifted_euf = lift_uninterpreted_sort_ite(arena, assertions)?;
        &lifted_euf
    };

    // Try the **online** CDCL(T) decider on the backtrackable e-graph first: it
    // keeps one incremental congruence graph across the Boolean search and honors
    // the caller's timeout. Both its `sat` (replay-checked) and `unsat`
    // (congruence-conflict-derived) verdicts are sound. On `unknown` fall through
    // to the offline enumeration, then bit-blast.
    match crate::euf_egraph::check_qf_uf_online_cdclt(arena, euf_assertions, config) {
        CheckResult::Sat(model) => {
            with_recorder(rec, |t| t.record_decided("euf-online", Verdict::Sat));
            return Ok(Some(CheckResult::Sat(model)));
        }
        CheckResult::Unsat => {
            with_recorder(rec, |t| t.record_decided("euf-online", Verdict::Unsat));
            return Ok(Some(CheckResult::Unsat));
        }
        CheckResult::Unknown(reason) => {
            with_recorder(rec, |t| {
                t.record_declined("euf-online", DeclineReason::from_unknown(&reason));
            });
        }
    }
    // Scalar UFBV: combine the same online e-graph with the warm incremental BV
    // solver through canonical CdclT. The route starts from the abstraction-only
    // function rewrite and case-splits explicit argument/result interface
    // equalities; it never constructs eager Ackermann implications. Decided
    // results are replay-gated inside. Logical/shape incompleteness falls through
    // to offline EUF and eager elimination; a real budget exhaustion is terminal
    // so a later fallback cannot mask its cause.
    if let Some(result) = dispatch_ufbv_online(arena, assertions, config, features, rec)? {
        return Ok(Some(result));
    }
    match crate::euf_egraph::check_qf_uf_with_config(arena, euf_assertions, config) {
        CheckResult::Sat(model) => {
            with_recorder(rec, |t| t.record_decided("euf-offline", Verdict::Sat));
            return Ok(Some(CheckResult::Sat(model)));
        }
        CheckResult::Unsat => {
            with_recorder(rec, |t| t.record_decided("euf-offline", Verdict::Unsat));
            return Ok(Some(CheckResult::Unsat));
        }
        CheckResult::Unknown(reason) => {
            with_recorder(rec, |t| {
                t.record_declined("euf-offline", DeclineReason::from_unknown(&reason));
            });
        }
    }
    // Arithmetic-sorted uninterpreted functions (QF_UFLIA / QF_UFLRA): decide them
    // by EUF + linear-arithmetic combination. Sound either way — its `unsat` is a
    // relaxation refutation, its `sat`/`unknown` fall through.
    //
    // Gated on the arithmetic function being **actually applied** (`features.has_function`),
    // not merely declared: a query (or a lazy-abstraction sub-query) whose assertions
    // contain no `Op::Apply` is pure arithmetic and must fall through to the LIA
    // refuters below — re-entering the eager UF+arithmetic route here on such a query
    // would recurse on the same function-free assertions and loop. A query with no
    // applied function has no congruence pairs, so this narrowing is verdict-preserving.
    if features.has_function && has_arithmetic_function(arena) {
        // FIRST attempt: the **online** EUF + linear-arithmetic combination
        // (warm, equality-sharing `Nelson–Oppen`), in place of eager Ackermann as
        // the normal mixed-theory answer (gap-analysis keystone). Its `sat` is
        // replay-checked inside; its `unsat` is the differentially-validated,
        // verify-guarded online refutation; on `unknown` (any cap / unsupported
        // shape) we FALL THROUGH to the eager `check_with_uf_arithmetic` route
        // below, byte-unchanged. Strictly additive: it only ever turns the eager
        // route's would-be result into the same verdict sooner, or declines.
        if let Some(result) = dispatch_uf_arith_online(arena, assertions, config, features, rec)? {
            return Ok(Some(result));
        }
        match crate::check_with_uf_arithmetic(arena, assertions, config)? {
            CheckResult::Sat(model) => {
                with_recorder(rec, |t| t.record_decided("uf-arithmetic", Verdict::Sat));
                return Ok(Some(CheckResult::Sat(model)));
            }
            CheckResult::Unsat => {
                with_recorder(rec, |t| t.record_decided("uf-arithmetic", Verdict::Unsat));
                return Ok(Some(CheckResult::Unsat));
            }
            // A *real*-sorted arithmetic UF cannot be bit-blasted by the eager
            // fallback below (it errors on `Real`), so the combination's `Unknown`
            // is the best available result — return it rather than fall through to a
            // Real-incompatible path. An *integer*-only arithmetic UF can still fall
            // through to the int-blast + Ackermann fallback.
            CheckResult::Unknown(reason) if features.has_real => {
                with_recorder(rec, |t| {
                    t.record_declined("uf-arithmetic", DeclineReason::from_unknown(&reason));
                });
                return Ok(Some(CheckResult::Unknown(reason)));
            }
            // A *budget* `Unknown` (wall-clock / resource / memory / node / CNF cap)
            // means the eager EUF + arithmetic route ran out of its configured budget
            // mid-decision. For non-array integer-only UF+arith, the later int-blast +
            // Ackermann fallback is not a different, more-capable procedure here: it is
            // bounded-width-incomplete and only masks the true budget cause. For mixed
            // array+UF queries, however, the downstream lazy ROW/extensionality CEGAR is
            // a genuinely different route, so let those fall through.
            CheckResult::Unknown(reason)
                if is_budget_unknown_kind(reason.kind) && !features.has_array =>
            {
                with_recorder(rec, |t| {
                    t.record_declined("uf-arithmetic", DeclineReason::from_unknown(&reason));
                });
                return Ok(Some(CheckResult::Unknown(reason)));
            }
            // A genuinely *logical* (non-budget) eager `Unknown` (a shape the EUF +
            // arithmetic combination cannot settle) may still decide via the complete
            // int-blast + Ackermann path: fall through to it.
            CheckResult::Unknown(reason) => {
                with_recorder(rec, |t| {
                    t.record_declined("uf-arithmetic", DeclineReason::from_unknown(&reason));
                });
            }
        }
    }
    if let Some(result) =
        dispatch_declared_sort_ufbv_lazy(arena, assertions, config, features, rec)?
    {
        return Ok(Some(result));
    }
    Ok(None)
}

fn dispatch_ufbv_online(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    rec: &mut Recorder<'_>,
) -> Result<Option<CheckResult>, SolverError> {
    if !features.has_function
        || (!features.has_bv_or_float && !features.has_array)
        || features.has_int
        || features.has_real
        || features.has_non_bool_bv_array
        || features.has_uninterpreted_sort
        || features.has_datatype
    {
        return Ok(None);
    }
    let route = if features.has_array {
        "aufbv-online-cdclt"
    } else {
        "ufbv-online-cdclt"
    };
    let result = if features.has_array {
        let mut online_arena = arena.clone();
        crate::ufbv_online::check_qf_aufbv_online_cdclt(&mut online_arena, assertions, config)
    } else {
        crate::ufbv_online::check_qf_ufbv_online_cdclt(arena, assertions, config)
    };
    match result {
        Ok(CheckResult::Sat(model)) => {
            with_recorder(rec, |t| {
                t.record_decided(route, Verdict::Sat);
            });
            Ok(Some(CheckResult::Sat(model)))
        }
        Ok(CheckResult::Unsat) => {
            with_recorder(rec, |t| {
                t.record_decided(route, Verdict::Unsat);
            });
            Ok(Some(CheckResult::Unsat))
        }
        Ok(CheckResult::Unknown(reason)) => {
            with_recorder(rec, |t| {
                t.record_declined(route, DeclineReason::from_unknown(&reason));
            });
            if is_budget_unknown_kind(reason.kind) && !features.has_array {
                Ok(Some(CheckResult::Unknown(reason)))
            } else {
                Ok(None)
            }
        }
        Err(SolverError::Unsupported(_)) => {
            with_recorder(rec, |t| {
                t.record_declined(route, DeclineReason::Unsupported);
            });
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

fn dispatch_declared_sort_ufbv_lazy(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    rec: &mut Recorder<'_>,
) -> Result<Option<CheckResult>, SolverError> {
    if !features.has_function
        || !features.has_uninterpreted_sort
        || features.has_int
        || features.has_real
        || features.has_array
        || features.has_datatype
    {
        return Ok(None);
    }

    let mut backend = SatBvBackend::new();
    match crate::euf::check_qf_ufbv_lazy(&mut backend, arena, assertions, config) {
        Ok(result) => {
            with_recorder(rec, |t| match &result {
                CheckResult::Sat(_) => t.record_decided("ufbv-declared-sort-lazy", Verdict::Sat),
                CheckResult::Unsat => {
                    t.record_decided("ufbv-declared-sort-lazy", Verdict::Unsat);
                }
                CheckResult::Unknown(reason) => t.record_declined(
                    "ufbv-declared-sort-lazy",
                    DeclineReason::from_unknown(reason),
                ),
            });
            Ok(Some(result))
        }
        Err(SolverError::Unsupported(message)) => {
            with_recorder(rec, |t| {
                t.record_declined("ufbv-declared-sort-lazy", DeclineReason::Unsupported);
            });
            Ok(Some(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: format!(
                    "declared-sort QF_UFBV lazy route is outside the current abstraction: {message}"
                ),
            })))
        }
        Err(error) => Err(error),
    }
}

/// The configuration for the online probe: a copy of `config` with any wall-clock
/// `timeout` halved, so the probe consumes at most half the configured budget
/// before the eager fallback (which computes its own fresh deadline at entry) runs
/// with the full budget. `timeout == None` is left unbounded — there is no
/// wall-clock budget to split, and both routes then decline only on their
/// deterministic size guards, so the online combination keeps its full power.
fn probe_budget(config: &SolverConfig) -> SolverConfig {
    let mut probe = config.clone();
    if let Some(t) = probe.timeout {
        probe.timeout = Some(t / 2);
    }
    probe
}

fn pre_lia_uf_probe_budget(config: &SolverConfig) -> SolverConfig {
    let mut probe = config.clone();
    if let Some(timeout) = probe.timeout {
        let tenth = timeout / 10;
        let bounded = if tenth.is_zero() {
            timeout
        } else {
            tenth.min(Duration::from_millis(250))
        };
        probe.timeout = Some(bounded);
    }
    probe
}

/// The **online** EUF + linear-arithmetic combination, tried *before* the eager
/// Ackermann route in [`dispatch_uf_fast_paths`]. Routes by sort — reals present
/// ⇒ [`crate::check_qf_uflra_online`] (`QF_UFLRA`), otherwise
/// [`crate::check_qf_uflia_online`] (`QF_UFLIA`) — and returns:
///
/// - `Ok(Some(Sat))` — the online combination's model, already replayed against
///   the original assertions inside the decider;
/// - `Ok(Some(Unsat))` — the online combination's (verify-guarded) refutation;
/// - `Ok(None)` — the online decider declined (`unknown`: any cap / unsupported
///   shape), so the caller FALLS THROUGH to the unchanged eager
///   [`crate::check_with_uf_arithmetic`] route.
///
/// Recording: a decided run is logged at `"uf-arith-online"`; a decline is logged
/// at the same route with the carried [`UnknownReason`] before the eager fallback
/// records itself. Purely additive — it never produces a verdict the eager route
/// would not also reach, only the same one sooner (the in-tree differential
/// `uf_arith_dispatch_differential` is the load-bearing gate on this invariant).
fn dispatch_uf_arith_online(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    rec: &mut Recorder<'_>,
) -> Result<Option<CheckResult>, SolverError> {
    // Run the online attempt on a CLONE of the arena, never the caller's, so that
    // when it declines and we fall through, the eager `check_with_uf_arithmetic`
    // route sees a pristine arena — byte-identical to running eager alone. The
    // online deciders append skolems / lowered terms; left in the caller's arena
    // they enlarge the eager fallback's work and, on a few queries, push it over
    // the shared per-query wall-clock cap (a real capability regression). The Sat
    // model is keyed by `SymbolId` (which the clone preserves), so it is sound to
    // return a model produced against the clone. The clone is bounded by the
    // (small) mixed-UF query and is the cost of keeping the fallback regression-free.
    let mut scratch = arena.clone();
    // Bound the online PROBE's share of a wall-clock budget so it cannot starve the
    // eager fallback. The eager route computes its own fresh deadline at entry, so a
    // small probe cap leaves it the full configured budget — without this, the probe
    // grinding a hard query to the shared cap left the fallback timing out where
    // running eager alone would have decided (a capability regression). When no
    // wall-clock budget is set (`timeout == None`) there is nothing to split — both
    // routes decline only on their deterministic size guards, identically — so the
    // probe runs unbounded and the online combination keeps its full power.
    let probe_config = probe_budget(config);
    // Int vs Real detection mirrors the surrounding dispatch: a real-sorted term
    // anywhere routes to the `QF_UFLRA` decider, otherwise the integer one.
    let online = if features.has_real {
        crate::check_qf_uflra_online(&mut scratch, assertions, &probe_config)?
    } else {
        crate::check_qf_uflia_online(&mut scratch, assertions, &probe_config)?
    };
    match online {
        CheckResult::Sat(model) => {
            with_recorder(rec, |t| t.record_decided("uf-arith-online", Verdict::Sat));
            Ok(Some(CheckResult::Sat(model)))
        }
        CheckResult::Unsat => {
            with_recorder(rec, |t| t.record_decided("uf-arith-online", Verdict::Unsat));
            Ok(Some(CheckResult::Unsat))
        }
        CheckResult::Unknown(reason) => {
            with_recorder(rec, |t| {
                t.record_declined("uf-arith-online", DeclineReason::from_unknown(&reason));
            });
            Ok(None)
        }
    }
}

/// Whether any assertion contains a **genuinely nonlinear real** subterm: a
/// `RealMul` (or `RealDiv`) whose *two* operands are both non-constant — e.g.
/// `x·x`, `f(x)·f(x)`, `x·y`, `f(x)·x`. A `2·x` (one constant operand) is linear
/// and returns `false`, so the linear `QF_UFLRA` combination keeps every query it
/// already decides; only the truly nonlinear shapes are routed to [`dispatch_uf_nra`].
/// Over-approximates safely (any product of two non-constants counts, even if it
/// cancels): a `false` positive only routes an already-linear-decidable query
/// through the NRA decider, which decides it too; it never changes a verdict.
fn has_nonlinear_real(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::RealMul | Op::RealDiv)
                && args.len() == 2
                && !crate::nra::is_numeric_real_constant(arena, args[0])
                && !crate::nra::is_numeric_real_constant(arena, args[1])
            {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

/// The dedicated **UF × NRA** decide route (P1.6 slice): the conservative, sound
/// composition of eager Ackermann congruence reduction with the NRA decider for
/// mixed uninterpreted-function + nonlinear-real queries — the `issue5836-2` /
/// `issue5396` shape family the pure-real routes below decline on any `Op::Apply`.
///
/// **Scope (feature-gate).** Fires only for `has_real ∧ has_function ∧
/// nonlinear-real`, with `¬has_int ∧ ¬has_array ∧ ¬has_datatype ∧
/// ¬has_uninterpreted_sort` — i.e. `Real → Real` uninterpreted functions over
/// nonlinear real arithmetic, no other theory mixed in. Every out-of-scope query
/// (linear `QF_UFLRA`, arrays, integers, datatypes, uninterpreted carrier sorts)
/// returns `None` and falls through to the existing routes unchanged, so the
/// load-bearing linear UF+arithmetic combination and its `uf_arith_dispatch_differential`
/// budget balance are untouched.
///
/// **Mechanism.** Eager Ackermann (`eliminate_functions`, the same machinery the
/// `QF_UFLIA`/`QF_UFLRA` path uses) rewrites every application to a fresh result
/// variable and asserts the congruence constraints `(⋀ argsᵢ = argsⱼ) ⇒ resultᵢ =
/// resultⱼ` up front; the function-free, nonlinear-real residual is fed straight
/// to [`crate::nra::check_with_nra`].
///
/// **Soundness.**
/// - `unsat` transfers by **reduction validity**: eager Ackermann elimination is
///   equisatisfiable, so an `unsat` residual witnesses `unsat` of the original.
/// - `sat` is accepted **only after** the projected model replays against the
///   ORIGINAL assertions through the ground evaluator (the trust anchor, inside
///   [`crate::euf::project_replay_build`]); a non-replaying candidate declines to
///   `Unknown`, never a wrong `sat`.
///
/// **Boundedness / deadline.** The eager `O(k²)` construction is refused above the
/// shared [`crate::euf::MAX_ACKERMANN_CONGRUENCE_PAIRS`] admission bound (→ `None`,
/// so the downstream lazy/CEGAR over-bound route in `dispatch_uf_fast_paths` still
/// runs). `check_with_nra` honors `config.timeout` internally; the remaining
/// deadline is threaded end-to-end and an expiry anywhere yields `Unknown`, never a
/// hang or a wrong verdict.
///
/// **Boundary (what stays out of this slice).** No online interface-equality DFS —
/// the UF interface here is discharged eagerly, up front; the online model-based
/// combination is a later slice. Multi-variable nonlinear beyond the NRA
/// cross-product admission bound, and nested arithmetic applications whose model
/// projection cannot be reconstructed, stay `Unknown` (a sound decline).
fn dispatch_uf_nra(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    rec: &mut Recorder<'_>,
) -> Result<Option<CheckResult>, SolverError> {
    // Scope gate: Real→Real UF over nonlinear real arithmetic, no other theory.
    if !features.has_real
        || !features.has_function
        || features.has_int
        || features.has_array
        || features.has_datatype
        || features.has_uninterpreted_sort
    {
        return Ok(None);
    }
    // Linear QF_UFLRA is left to the existing (online + eager) combination.
    if !has_nonlinear_real(arena, assertions) {
        return Ok(None);
    }

    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    if past_deadline(deadline) {
        with_recorder(rec, |t| {
            t.record_declined(
                "uf-nra",
                DeclineReason::from_unknown(&timeout_reason(
                    "uf-nra: past deadline before eager \
                     Ackermann reduction",
                )),
            );
        });
        return Ok(Some(CheckResult::Unknown(timeout_reason(
            "uf-nra: past deadline before eager Ackermann reduction",
        ))));
    }

    // Deterministic admission bound (graceful, no O(k²) blowup): refuse the eager
    // construction above the shared bound and fall through so the downstream
    // lazy/CEGAR over-bound route in `dispatch_uf_fast_paths` gets its chance.
    if crate::euf::ackermann_congruence_pairs(arena, assertions)
        > crate::euf::MAX_ACKERMANN_CONGRUENCE_PAIRS
    {
        return Ok(None);
    }

    // Eager Ackermann reduction (reuse the shared machinery). An out-of-fragment
    // construct declines to `None` (fall through) rather than erroring — `unknown`
    // is never an error and the downstream routes may still decide it.
    let Ok(elimination) = axeyum_rewrite::eliminate_functions(arena, assertions) else {
        return Ok(None);
    };
    let eliminated = elimination.assertions().to_vec();

    if past_deadline(deadline) {
        with_recorder(rec, |t| {
            t.record_declined(
                "uf-nra",
                DeclineReason::from_unknown(&timeout_reason(
                    "uf-nra: deadline after eager Ackermann reduction",
                )),
            );
        });
        return Ok(Some(CheckResult::Unknown(timeout_reason(
            "uf-nra: deadline after eager Ackermann reduction",
        ))));
    }

    // Feed the function-free nonlinear-real residual to the NRA decider under the
    // remaining deadline.
    let nra_config = config_with_remaining_deadline(config, deadline);
    let result = crate::nra::check_with_nra(arena, &eliminated, &nra_config)?;
    match result {
        CheckResult::Unsat => {
            // Reduction validity: eager Ackermann is equisatisfiable.
            with_recorder(rec, |t| t.record_decided("uf-nra", Verdict::Unsat));
            Ok(Some(CheckResult::Unsat))
        }
        CheckResult::Sat(model) => {
            // `sat` only after the projected model replays against the ORIGINAL
            // assertions (the trust anchor); a non-replaying candidate declines.
            let assignment = model.to_assignment();
            let replayed =
                crate::euf::project_replay_build(arena, &elimination, assertions, &assignment);
            with_recorder(rec, |t| match &replayed {
                CheckResult::Sat(_) => t.record_decided("uf-nra", Verdict::Sat),
                CheckResult::Unsat => t.record_decided("uf-nra", Verdict::Unsat),
                CheckResult::Unknown(reason) => {
                    t.record_declined("uf-nra", DeclineReason::from_unknown(reason));
                }
            });
            Ok(Some(replayed))
        }
        CheckResult::Unknown(reason) => {
            with_recorder(rec, |t| {
                t.record_declined("uf-nra", DeclineReason::from_unknown(&reason));
            });
            Ok(Some(CheckResult::Unknown(reason)))
        }
    }
}

/// The theory dispatcher (coercions already relaxed away by [`check_auto`]).
/// `rec` records each route attempt + outcome at the existing decide/decline
/// sites; it is a side effect only, never a branch condition (verdict invariance).
#[allow(clippy::too_many_lines)]
fn check_auto_dispatch(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    rec: &mut Recorder<'_>,
) -> Result<CheckResult, SolverError> {
    // Lift Int/Real `ite` to the Boolean level (`ite(c,a,b)` → fresh `t` with
    // `c→t=a ∧ ¬c→t=b`) so the arithmetic linearizers, which only accept linear
    // arith terms, see a plain variable. An exact (equisatisfiable) rewrite, so
    // the dispatched result transfers directly. (BV `ite` is left for the
    // bit-blaster, which handles it natively.)
    let lifted = lift_arith_ite(arena, assertions)?;
    let assertions = &lifted;
    let dispatch_deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let Some(features) = Features::scan_within(arena, assertions, dispatch_deadline) else {
        // Telemetry: an ultra-tight budget can expire during the feature scan
        // itself — record the budget decline so a trace never ends with only a
        // probe entry (a slow-runner-only gap the route-trace tests caught).
        with_recorder(rec, |t| {
            t.record_declined(
                "feature-scan",
                DeclineReason::from_unknown(&timeout_reason(
                    "auto-dispatch timeout while scanning lifted theory features",
                )),
            );
        });
        return Ok(CheckResult::Unknown(timeout_reason(
            "auto-dispatch timeout while scanning lifted theory features",
        )));
    };
    if features.has_datatype {
        // Datatype structural axioms (acyclicity / distinctness / injectivity):
        // a forced containment cycle (`x = cons(h, x)`), two constructors on one
        // value (`x = nil ∧ x = cons(…)`), or an injectivity-vs-disequality clash
        // (`cons(h,x) = cons(h,y) ∧ x ≠ y`) is `unsat` — sound refutations the eager
        // tag/field expansion misses. Cheap; only ever fast-paths a correct `unsat`.
        if crate::datatype_acyclicity::prove_datatype_unsat_structurally(arena, assertions) {
            with_recorder(rec, |t| {
                t.record_decided("datatype-acyclicity", Verdict::Unsat);
            });
            return Ok(CheckResult::Unsat);
        }
        // Datatypes: first fold read-over-construct and decide the residual
        // (ADR-0022 step A). If free datatype variables remain (under `is-c`/
        // `select`), that path reports `Unsupported`; decide those natively by
        // eager tag/field expansion (ADR-0022 step B).
        match crate::datatype_elim::check_with_datatype_elimination(arena, assertions, config) {
            Ok(result) => {
                with_recorder(rec, |t| t.record_result("datatype-elim", &result));
                return Ok(result);
            }
            Err(SolverError::Unsupported(_)) => {
                with_recorder(rec, |t| {
                    t.record_declined("datatype-elim", DeclineReason::Unsupported);
                });
                let result =
                    crate::datatype_native::check_with_datatype_native(arena, assertions, config)?;
                with_recorder(rec, |t| t.record_result("datatype-native", &result));
                return Ok(result);
            }
            Err(other) => return Err(other),
        }
    }
    if features.has_real && features.has_int {
        // Combined linear arithmetic (QF_LIRA): the lazy-SMT loop theory-checks
        // integer and real atoms with their exact simplices independently (they
        // share no sort). Falls back to the real loop on non-arithmetic atoms
        // (mixed BV/array), which bit-blasts them.
        match check_with_arith_dpll(arena, assertions, config) {
            Ok(result) => {
                with_recorder(rec, |t| t.record_result("lira-dpll", &result));
                return Ok(result);
            }
            Err(SolverError::Unsupported(_)) => {
                with_recorder(rec, |t| {
                    t.record_declined("lira-dpll", DeclineReason::Unsupported);
                });
            }
            Err(other) => return Err(other),
        }
    }
    if features.has_real {
        // **UF × NRA** (P1.6 slice): a mixed uninterpreted-function + nonlinear-real
        // query (`f(x)·f(x) = 2`, `x = y ∧ f(x) = x·x ∧ f(y) > y·y + 1`, …) is
        // decided by the dedicated composition — eager Ackermann reduction of the UF
        // applications feeding the NRA decider — *before* the pure-real routes below
        // (which decline on any `Op::Apply`). Strictly additive and self-contained:
        // it returns `Some(decided/unknown)` only for the tightly-scoped nonlinear-UF
        // shape (leaving the linear QF_UFLRA online/eager combination and every
        // non-UF real route byte-identical), and `None` — falling through unchanged —
        // for everything else (linear UF, over the eager admission bound, or an
        // out-of-fragment elimination).
        if let Some(result) = dispatch_uf_nra(arena, assertions, config, &features, rec)? {
            return Ok(result);
        }
        // Conjunction of single-variable nonlinear-real polynomial constraints
        // over one shared variable (`⋀ᵢ pᵢ(x) ⋈ᵢ 0`): an exact, bounded NRA
        // decision with **irrational witnesses** (ADR-0038). The linear-
        // abstraction NRA path below abstracts a product like `x·x` to a fresh
        // variable and so only ever reports `Unknown` for `x·x = 2`; this pass
        // isolates the real roots of the collected polynomial(s) exactly and, for
        // a conjunction, sign-cell-decomposes ℝ (roots ∪ one rational sample per
        // open cell) to return a witness — e.g. `√2` (a `Value::RealAlgebraic`)
        // for `x·x = 2 ∧ x > 0`, or a rational for `x³ > 1 ∧ x < 2`. The whole
        // assertion list (and any top-level `and`) is flattened to the conjunction
        // of atoms; every other shape (≥ 2 distinct variables, a non-Real sort, a
        // non-polynomial operator, a non-conjunctive top-level `or`/`=>`) declines
        // (`None`) and is left to the NRA layer. Every `Sat` is replay-checked
        // against ALL assertions (an algebraic witness via `sign_at(pᵢ, α) ⋈ᵢ 0`,
        // a rational witness via the ground evaluator) and every `Unsat` is exact
        // by exhaustive sign-cell coverage of the single variable, so it can never
        // produce a wrong verdict; strictly additive (`Unknown` → decision).
        if has_nonlinear_real(arena, assertions) {
            let poly_deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
            if let Some(result) =
                crate::nra_real_root::decide_real_poly_constraint(arena, assertions, poly_deadline)?
            {
                with_recorder(rec, |t| t.record_result("nra-real-root", &result));
                return Ok(result);
            }
        }
        with_recorder(rec, |t| {
            t.record_declined("nra-real-root", DeclineReason::NotApplicable);
        });
        // Reals plus (optionally) the bit-blasted theories: the lazy-SMT loop
        // abstracts the real atoms and lets the bit-blasting backend decide the
        // rest. Reals share no sort with those theories, so the only coupling is
        // propositional and this is a complete combination. Routed through the
        // NRA layer, which abstracts any nonlinear products (relaxation + replay,
        // ADR-pending) and otherwise delegates straight to the LRA loop.
        //
        // A *real-sorted uninterpreted function* application (`f(x) : Real`) is
        // outside the pure-real linearizer and surfaces as `Unsupported`. Mirror
        // the integer branch below: when a function is present, fall through to the
        // EUF + linear-arithmetic combination (`check_with_uf_arithmetic`, which
        // decides QF_UFLRA the same way it does QF_UFLIA) instead of propagating the
        // error — upholding "`unknown` is never an error" and unlocking EUF+LRA.
        match crate::nra::check_with_nra(arena, assertions, config) {
            Ok(result) => {
                with_recorder(rec, |t| t.record_result("nra", &result));
                return Ok(result);
            }
            Err(SolverError::Unsupported(_)) if features.has_function => {
                with_recorder(rec, |t| {
                    t.record_declined("nra", DeclineReason::Unsupported);
                });
            }
            Err(e) => return Err(e),
        }
    }
    if let Some(result) =
        dispatch_arith_uf_overbound_probe_before_lia(arena, assertions, config, &features, rec)?
    {
        return Ok(result);
    }
    if features.has_int {
        // Complete blast of the linear-over-`bv2nat` integer fragment (the
        // `str.len` gap, P2.7 A.2): the bounded string front-end lowers
        // `str.len` to `bv2nat(len_field)`, so a string query's integer atoms
        // are linear constraints over `bv2nat` terms and constants with no free
        // `Int` symbols. On that fragment every integer value is provably
        // bounded, so the atoms rewrite to **equivalent** pure-BV comparisons
        // at an overflow-safe width (same symbols, no fresh declarations) and
        // the SAT path decides BOTH directions — closing the `str.len`-unsat
        // BV+LIA combination gap the range refuter below cannot (it never sees
        // the BV-side facts). Out-of-fragment queries decline (`None`) and fall
        // through unchanged. Every `sat` is replay-checked against the original
        // assertions (equivalence makes it pass; a failure is converted to a
        // decline, never a wrong `sat`).
        if features.has_bv_or_float
            && !features.has_function
            && !features.has_array
            && !features.has_uninterpreted_sort
            && !features.has_datatype
            && let Some(blasted) = crate::bv2nat_blast::blast_bv2nat_linear(arena, assertions)?
        {
            let mut backend = SatBvBackend::new();
            match check_with_all_theories(&mut backend, arena, &blasted, DEFAULT_INT_WIDTH, config)
            {
                Ok(CheckResult::Sat(model)) => {
                    let assignment = model.to_assignment();
                    let all_true = assertions
                        .iter()
                        .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))));
                    if all_true {
                        with_recorder(rec, |t| t.record_decided("bv2nat-blast", Verdict::Sat));
                        return Ok(CheckResult::Sat(model));
                    }
                    // Should be unreachable (the blast is an equivalence); a
                    // replay failure is a loud decline, never a wrong `sat`.
                    with_recorder(rec, |t| {
                        t.record_declined(
                            "bv2nat-blast",
                            DeclineReason::from_unknown(&UnknownReason {
                                kind: UnknownKind::Incomplete,
                                detail: "bv2nat-blast sat candidate failed replay against the \
                                         original assertions"
                                    .to_owned(),
                            }),
                        );
                    });
                }
                Ok(CheckResult::Unsat) => {
                    with_recorder(rec, |t| t.record_decided("bv2nat-blast", Verdict::Unsat));
                    return Ok(CheckResult::Unsat);
                }
                Ok(CheckResult::Unknown(reason)) => {
                    with_recorder(rec, |t| {
                        t.record_declined("bv2nat-blast", DeclineReason::from_unknown(&reason));
                    });
                }
                Err(e) => return Err(e),
            }
        }
        // `bv2nat(b)` finite-range refutation (G2): a `bv2nat(b)` of a `W`-bit
        // vector is in `[0, 2^W - 1]`, but the exact integer refuters below only
        // linearize integer *symbols* and reject a raw `bv2nat` subterm, so an
        // unsatisfiable range constraint (`bv2nat(b) >= 2^W`, `bv2nat(b) = k` with
        // `k >= 2^W`, …) never becomes `unsat` here — it degrades to the bounded
        // bit-blaster's `unknown`. Abstract each distinct `bv2nat(b)` to a fresh
        // `Int` var plus its true range bound and try the exact refuters on the
        // relaxation: an `unsat` of the (range-bounded) relaxation transfers
        // soundly to the original (every model induces one of the relaxation). A
        // non-`unsat` outcome is discarded — the original query (with `bv2nat`
        // intact, which the bit-blaster handles natively) decides sat below. This
        // is strictly additive: it only ever turns a prior `unknown` into `unsat`.
        if let Some(result) =
            dispatch_int_linear_refuters(arena, assertions, config, &features, rec)?
        {
            return Ok(result);
        }
    }
    // Uninterpreted functions: try the lazy EUF path on the e-graph first. It
    // decides the equality/UF structure with congruence (no Ackermann blow-up) and
    // returns a replay-checked `sat`, a congruence `unsat`, or `unknown` for
    // base-sort semantics outside congruence, which falls through to bit-blasting.
    if let Some(result) = dispatch_uf_routes(arena, assertions, config, &features, rec)? {
        return Ok(result);
    }
    if features.has_array {
        if let Some(result) = dispatch_abv_online(arena, assertions, config, &features, rec)? {
            return Ok(result);
        }
        if let Some(result) = dispatch_array_fast_paths(arena, assertions, config, &features)? {
            with_recorder(rec, |t| t.record_result("array-fast-path", &result));
            return Ok(result);
        }
        with_recorder(rec, |t| {
            t.record_declined("array-fast-path", DeclineReason::NotApplicable);
        });
        if features.has_non_bv_array {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: "non-bit-vector array sorts are represented in IR, but this shape is \
                         outside the current Bool/Int lazy array route"
                    .to_owned(),
            }));
        }
    }

    if features.has_int {
        return dispatch_nonlinear_int_tail(arena, assertions, config, rec);
    }

    let mut backend = SatBvBackend::new();
    match check_with_all_theories(&mut backend, arena, assertions, DEFAULT_INT_WIDTH, config) {
        Ok(result) => {
            with_recorder(rec, |t| t.record_result("qf-bv", &result));
            Ok(result)
        }
        // The pure-BV bit-blaster cannot represent an uninterpreted carrier sort.
        // When such a term reaches this fallback (the e-graph path above already
        // declined — e.g. an `ite`/`=` over an uninterpreted sort whose semantics
        // the congruence closure did not capture) the bit-blaster hard-errors.
        // Convert *only that error* to an honest `Unknown`: `check_auto` must never
        // error on a valid quantifier-free instance. Decisions are unaffected (this
        // is the `Err` arm), so decide-rate cannot regress; other errors propagate.
        Err(e) if features.has_uninterpreted_sort => {
            let result = CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: format!(
                    "uninterpreted-sort term not bit-blastable by the pure-BV backend \
                     (no Ackermann route engaged): {e}"
                ),
            });
            with_recorder(rec, |t| {
                t.record_result("qf-bv-uninterpreted-decline", &result);
            });
            Ok(result)
        }
        // Array elimination can refuse a shape the lazy ROW/extensionality path
        // also declined — the canonical case being a **wide-index array equality**
        // (`store-chain = store-chain` over a 32-/64-bit index) that bounded
        // extensionality cannot enumerate. That surfaces here as a backend error;
        // convert it to an honest `Unknown` (same soundness floor: never error on a
        // valid instance). `Err`-arm only, so no decided array instance regresses.
        Err(e) if features.has_array => {
            let result = CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: format!(
                    "array shape left undecided by the lazy ROW/extensionality path and \
                     refused by bounded array elimination: {e}"
                ),
            });
            with_recorder(rec, |t| t.record_result("qf-abv-array-decline", &result));
            Ok(result)
        }
        Err(e) => Err(e),
    }
}

fn dispatch_abv_online(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    rec: &mut Recorder<'_>,
) -> Result<Option<CheckResult>, SolverError> {
    if features.has_function
        || features.has_int
        || features.has_real
        || features.has_non_bool_bv_array
        || features.has_uninterpreted_sort
        || features.has_datatype
    {
        return Ok(None);
    }
    let mut online_arena = arena.clone();
    match crate::ufbv_online::check_qf_aufbv_online_cdclt(&mut online_arena, assertions, config) {
        Ok(result @ (CheckResult::Sat(_) | CheckResult::Unsat)) => {
            with_recorder(rec, |t| t.record_result("abv-online-cdclt", &result));
            Ok(Some(result))
        }
        Ok(CheckResult::Unknown(reason)) => {
            with_recorder(rec, |t| {
                t.record_declined("abv-online-cdclt", DeclineReason::from_unknown(&reason));
            });
            Ok(None)
        }
        Err(SolverError::Unsupported(_)) => {
            with_recorder(rec, |t| {
                t.record_declined("abv-online-cdclt", DeclineReason::Unsupported);
            });
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

fn dispatch_uf_routes(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    rec: &mut Recorder<'_>,
) -> Result<Option<CheckResult>, SolverError> {
    if !features.has_function && !features.has_uninterpreted_sort {
        return Ok(None);
    }
    if let Some(result) = dispatch_uf_pigeonhole(arena, assertions, rec) {
        return Ok(Some(result));
    }
    dispatch_uf_fast_paths(arena, assertions, config, features, rec)
}

fn dispatch_uf_pigeonhole(
    arena: &TermArena,
    assertions: &[TermId],
    rec: &mut Recorder<'_>,
) -> Option<CheckResult> {
    crate::ufbv_finite::finite_domain_pigeonhole_refutation(arena, assertions)?;
    with_recorder(rec, |t| {
        t.record_decided("uf-finite-domain-pigeonhole", Verdict::Unsat);
    });
    Some(CheckResult::Unsat)
}

/// The pure-integer nonlinear tail of [`check_auto_dispatch`] (`features.has_int`
/// after the EUF/array fast paths). Split out for length; the verdict logic is
/// verbatim the inlined original, `rec` only annotates the existing sites.
fn dispatch_nonlinear_int_tail(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    rec: &mut Recorder<'_>,
) -> Result<CheckResult, SolverError> {
    {
        // Single-variable integer SQUARE constraint (`x*x ⋈ c`, constant `c`): an
        // exact, bounded NIA decision. The bounded bit-blast width ladder and the
        // real relaxation both only ever report `Unknown` for a non-perfect-square
        // equality (`x*x = 2` ⇒ should be Unsat). This pass fires *only* when the
        // whole query is exactly one such square constraint over one `Int` variable
        // and an integer constant — every other shape (`x*y`, `x*x*x`, `x*x + x =
        // c`, `x*x = y`, a Real square, or any extra assertion constraining `x`)
        // declines (`None`) and is left to the engines below. Every `Sat` it returns
        // is replay-checked against the original assertion, and its `Unsat` is exact
        // by the perfect-square / sign analysis, so it can never produce a wrong
        // verdict; strictly additive (`Unknown` → decision).
        if let Some(result) = crate::nia_square::decide_int_square_constraint(arena, assertions)? {
            with_recorder(rec, |t| t.record_result("nia-square", &result));
            return Ok(result);
        }
        // Bounded integer bit-blasting at a single width is fragile for *nonlinear*
        // integer goals: a modular witness (e.g. `x` with `x*x ≡ 4 (mod 2^32)` but
        // `x*x ≠ 4` over the integers) satisfies the blasted query yet fails the
        // exact-integer replay, so the single fixed width reports `Unknown` even when
        // a small genuine witness exists (x = 2). Try a **width ladder** small→large:
        // at a narrow width there is no room for a wrapping witness, so the SAT
        // solver is forced onto the genuine small solution. The first width whose
        // model **replays against the originals** (the only way
        // `check_with_all_theories` ever returns `Sat`) is a sound `Sat`. This is
        // strictly additive — `DEFAULT_INT_WIDTH` is in the ladder, so any width-32
        // answer is still reachable — and a definite `Unsat`/`Unknown` from the
        // exact LIA engines above already short-circuited before here.
        // Real-relaxation refutation (G3): the integers are a subset of the reals,
        // so an integer query has *no model* whenever its faithful real relaxation
        // has none. Integer-nonlinear goals that are unsat for sign reasons (`x*x <
        // 0`, `x*x + 1 <= 0`) — and, with commutative-operand canonicalization,
        // commutativity goals like `a*b ≠ b*a` (both products relax to the *same*
        // real term, so the disequality becomes `p ≠ p`, i.e. `false`) — are refuted
        // by the NRA layer over that relaxation, which the bounded bit-blast width
        // ladder only ever reports as `Unknown` (and, for the multiplier-equivalence
        // shape, only after a slow per-width blast). The relaxation maps every `Int`
        // var/const/op faithfully onto the reals; `unsat` of it transfers soundly to
        // the integer query (integer solutions ⊆ real solutions), and it *only* ever
        // returns `Unsat` (a real model need not be integral) — returning `false`
        // for sat/unknown, which then fall to the ladder. So running it *before* the
        // ladder is sound and changes nothing for the sat cases (`x*x = 4`, …) the
        // ladder still decides; it only fast-paths (and avoids hanging on) the
        // real-refutable cases. The relaxation runs on a clone of the arena and
        // never leaks a symbol or term back.
        if crate::int_real_relax::refute_int_via_real_relaxation(arena, assertions, config)? {
            with_recorder(rec, |t| t.record_decided("int-real-relax", Verdict::Unsat));
            return Ok(CheckResult::Unsat);
        }
        // **Integer nonlinear decider** (Phase E first slice): linearize
        // variable-divisor `div`/`mod` into their `≠0`-guarded Euclidean form,
        // abstract each integer product with valid sign/zero lemmas, and
        // solve over the integer DPLL(T). Run *before* the width ladder so a case
        // like `div.03` (`n>0 ∧ x≥n ∧ (div x n)<1`, unsat over ℤ but sat over ℝ)
        // decides by linearization rather than blowing up the bounded blast.
        // Strictly additive: `unsat` transfers soundly from the relaxation, `sat`
        // is accepted only after replay against the original, and it declines
        // (`None`) on everything else.
        if let Some(result) = crate::nia_linearize::check_with_nia(arena, assertions, config)? {
            with_recorder(rec, |t| t.record_result("nia-linearize", &result));
            return Ok(result);
        }
        // **Bound-aware EXACT int-blast** (closes the QF_NIA UNSAT blind spot):
        // when every free `Int` variable is provably confined to a finite box,
        // blasting at a box-covering width is EXACT, so a bit-vector `Unsat` is a
        // genuine integer `Unsat` — the one thing the width ladder never trusts.
        // Gated on the all-bounded proof; see `decide_bounded_int_blast`.
        if let Some(result) = decide_bounded_int_blast(arena, assertions, config)? {
            with_recorder(rec, |t| t.record_result("nia-bounded-blast", &result));
            return Ok(result);
        }
        let result = dispatch_int_blast_width_ladder(arena, assertions, config)?;
        with_recorder(rec, |t| t.record_result("int-blast-ladder", &result));
        // The integer nonlinear decider (`check_with_nia`) already ran *before* the
        // width ladder above — its product/sign-lemma relaxation and variable-
        // divisor Euclidean linearization refute the `unsat` cases (`div.03`,
        // `mod.02`) the ladder structurally cannot, and replay-check any `sat`.
        Ok(result)
    }
}

/// Array fast paths, tried before the eager read-over-write + Ackermann
/// composition. Returns `Some(verdict)` when one decides the query, else `None`.
fn dispatch_array_unsat_refuters(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let deadline = array_refuter_deadline(config);
    if crate::abv::prove_unsat_by_symmetric_swap_chain_within(arena, assertions, deadline) {
        return Ok(Some(CheckResult::Unsat));
    }
    if let Some(cert) =
        crate::abv::const_array_default_mismatch_refutation_within(arena, assertions, deadline)
        && cert.recheck(arena, assertions)
    {
        return Ok(Some(CheckResult::Unsat));
    }
    if let Some(cert) =
        crate::abv::store_chain_readback_refutation_within(arena, assertions, deadline)
        && cert.recheck(arena, assertions)
    {
        return Ok(Some(CheckResult::Unsat));
    }
    if crate::abv::prove_unsat_by_two_store_same_target_split_within(arena, assertions, deadline)? {
        return Ok(Some(CheckResult::Unsat));
    }
    if let Some(cert) = crate::array_finite::bool_array_read_collapse_refutation(arena, assertions)
        && cert.recheck(arena, assertions)
    {
        return Ok(Some(CheckResult::Unsat));
    }
    if past_deadline(deadline) {
        return Ok(None);
    }
    // Array extensionality as congruence: `a = b ⇒ select(a, i) = select(b, i)`.
    // `prove_unsat_by_congruence` treats `select`/`store` as uninterpreted, so it
    // soundly refutes extensionality conflicts (e.g. `a = b ∧ select(a,i) ≠
    // select(b,i)`) — including **wide-index array equality** the eager array
    // elimination rejects outright. Congruence is valid for arrays, so this only
    // ever fast-paths a correct `unsat`; otherwise it falls through.
    if crate::euf_egraph::prove_unsat_by_congruence(arena, assertions).is_some() {
        return Ok(Some(CheckResult::Unsat));
    }
    Ok(None)
}

fn array_refuter_deadline(config: &SolverConfig) -> Option<Instant> {
    const TIMED_ARRAY_REFUTER_SLICE: Duration = Duration::from_millis(250);
    config.timeout.and_then(|timeout| {
        let slice = timeout.min(TIMED_ARRAY_REFUTER_SLICE);
        Instant::now().checked_add(slice)
    })
}

fn dispatch_array_fast_paths(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
) -> Result<Option<CheckResult>, SolverError> {
    // Scalar Int-array routes: non-BV arrays whose scalar abstraction is
    // Bool/linear-Int (QF_ALIA) or Bool/linear-Int+UF (QF_AUFLIA) reuse the lazy
    // ROW/extensionality CEGAR with the matching scalar backend. Other non-BV
    // mixes still decline explicitly below.
    if features.has_non_bv_array && scalar_alia_auflia_arrays_supported(features) {
        let result = if features.has_function {
            crate::abv::check_qf_auflia_lazy_row(arena, assertions, config)
        } else {
            crate::abv::check_qf_alia_lazy_row(arena, assertions, config)
        };
        return match result {
            Ok(result) => Ok(Some(result)),
            Err(SolverError::Unsupported(_)) => Ok(None),
            Err(error) => Err(error),
        };
    }
    // Pure declared-sort arrays (`QF_AX`): after select/store abstraction the
    // scalar side is Bool + equality over uninterpreted carrier tokens. Reuse
    // the same lazy ROW/extensionality CEGAR with the replaying EUF backend.
    if features.has_non_bv_array && scalar_qf_ax_declared_arrays_supported(features) {
        return match crate::abv::check_qf_ax_declared_sort_lazy_row(arena, assertions, config) {
            Ok(result) => Ok(Some(result)),
            Err(SolverError::Unsupported(_)) => Ok(None),
            Err(error) => Err(error),
        };
    }
    // Pure `QF_ABV` (no int/real/UF): the lazy read-over-write (ROW) path, which
    // delegates to the eager elimination for the cases it accepts and decides the
    // wide-index store shapes it refuses (`dispatch_pure_qf_abv`).
    if !features.has_int && !features.has_real && !features.has_function {
        return dispatch_pure_qf_abv(arena, assertions, config);
    }
    Ok(None)
}

fn scalar_alia_auflia_arrays_supported(features: &Features) -> bool {
    !features.has_real
        && !features.has_bv_or_float
        && !features.has_uninterpreted_sort
        && !features.has_datatype
}

fn scalar_qf_ax_declared_arrays_supported(features: &Features) -> bool {
    !features.has_real
        && !features.has_int
        && !features.has_bv_or_float
        && !features.has_function
        && features.has_uninterpreted_sort
        && !features.has_datatype
}

/// Pure `QF_ABV` dispatch via the lazy read-over-write (ROW) path (P2.2). It
/// delegates to the eager elimination + lazy select-congruence whenever that path
/// accepts the query (so every case the eager path already decides is unchanged),
/// and otherwise — the canonical refused case being a *wide-index array equality
/// involving a store*, `b = store(a, i, v)`, which bounded extensionality declines
/// above its index cap — adds the ROW axiom on demand (CEGAR) to decide it without
/// enumerating index equalities. Its `sat` is replay-checked against the originals
/// and its `unsat` transfers from the relaxation, so it never returns a wrong
/// verdict; an unmodelled shape degrades to `unknown` (returned as `None`) and the
/// caller falls through to the eager composition.
fn dispatch_pure_qf_abv(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let mut backend = SatBvBackend::new();
    match crate::abv::check_qf_abv_lazy_row(&mut backend, arena, assertions, config)? {
        CheckResult::Sat(model) => Ok(Some(CheckResult::Sat(model))),
        CheckResult::Unsat => Ok(Some(CheckResult::Unsat)),
        CheckResult::Unknown(reason) if is_budget_unknown_kind(reason.kind) => {
            Ok(Some(CheckResult::Unknown(reason)))
        }
        CheckResult::Unknown(_) => Ok(None),
    }
}

/// Whether `deadline` (if set) has passed.
fn past_deadline(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}

// ===========================================================================
// Bounded EXACT integer bit-blast (closes the QF_NIA UNSAT blind spot).
// ===========================================================================
//
// The width ladder above is sound for `Sat` only: it never trusts a bit-vector
// `Unsat` for an integer query, because at a fixed width the bit-vector search
// missed any model living above `2^w`. This pass earns the right to trust a
// blast-`Unsat` by first PROVING the whole query lives in a finite integer box,
// then blasting at a width that encodes that box (and every intermediate value)
// EXACTLY — no wraparound is possible, so a bit-vector `Unsat` is a genuine
// integer `Unsat`.

/// A closed integer interval `[lo, hi]` (inclusive). Used to track provable
/// ranges of variables and subterms during the bound proof.
#[derive(Clone, Copy, Debug)]
struct IntInterval {
    lo: i128,
    hi: i128,
}

impl IntInterval {
    fn point(v: i128) -> Self {
        IntInterval { lo: v, hi: v }
    }

    /// The largest absolute value any member can take (for width sizing).
    fn max_abs(self) -> u128 {
        self.lo.unsigned_abs().max(self.hi.unsigned_abs())
    }
}

/// Saturating-checked interval addition; `None` on `i128` overflow (→ decline).
fn iv_add(a: IntInterval, b: IntInterval) -> Option<IntInterval> {
    Some(IntInterval {
        lo: a.lo.checked_add(b.lo)?,
        hi: a.hi.checked_add(b.hi)?,
    })
}

/// Checked interval subtraction (`a - b`); `None` on overflow.
fn iv_sub(a: IntInterval, b: IntInterval) -> Option<IntInterval> {
    Some(IntInterval {
        lo: a.lo.checked_sub(b.hi)?,
        hi: a.hi.checked_sub(b.lo)?,
    })
}

/// Checked interval negation.
fn iv_neg(a: IntInterval) -> Option<IntInterval> {
    Some(IntInterval {
        lo: a.hi.checked_neg()?,
        hi: a.lo.checked_neg()?,
    })
}

/// Checked interval multiplication: the product range is the min/max over the
/// four corner products. `None` on any `i128` overflow.
fn iv_mul(a: IntInterval, b: IntInterval) -> Option<IntInterval> {
    let corners = [
        a.lo.checked_mul(b.lo)?,
        a.lo.checked_mul(b.hi)?,
        a.hi.checked_mul(b.lo)?,
        a.hi.checked_mul(b.hi)?,
    ];
    let lo = *corners.iter().min().expect("four corners");
    let hi = *corners.iter().max().expect("four corners");
    Some(IntInterval { lo, hi })
}

/// Evaluates the integer interval of `term` given known variable bounds in
/// `bounds`. Returns `None` (decline) for any construct whose range is not
/// computable here: an unbounded integer variable, a non-`Int`-arithmetic op
/// (`div`/`mod`/`abs`/comparisons/`ite`/uninterpreted), or an `i128` overflow.
/// `bv2nat` is the one bit-vector bridge admitted — its result is structurally in
/// `[0, 2^w)` (the `iand` desugaring path). Recognizing FEWER shapes is always
/// sound — it only declines.
fn interval_of(
    arena: &TermArena,
    term: TermId,
    bounds: &BTreeMap<SymbolId, IntInterval>,
    depth: u32,
) -> Option<IntInterval> {
    // Cap recursion so a pathologically deep term cannot blow the stack.
    if depth > 256 {
        return None;
    }
    match arena.node(term) {
        TermNode::IntConst(value) => Some(IntInterval::point(*value)),
        TermNode::Symbol(sym) => {
            if arena.sort_of(term) == Sort::Int {
                bounds.get(sym).copied()
            } else {
                None
            }
        }
        TermNode::App { op, args } => {
            // Only the *total* linear/multiplicative integer arithmetic that the
            // exact bit-blast encoding preserves verbatim is interval-evaluated
            // here; `div`/`mod`/`abs` (and everything else) decline.
            let args = args.clone();
            match op {
                Op::IntAdd => iv_add(
                    interval_of(arena, args[0], bounds, depth + 1)?,
                    interval_of(arena, args[1], bounds, depth + 1)?,
                ),
                Op::IntSub => iv_sub(
                    interval_of(arena, args[0], bounds, depth + 1)?,
                    interval_of(arena, args[1], bounds, depth + 1)?,
                ),
                Op::IntNeg => iv_neg(interval_of(arena, args[0], bounds, depth + 1)?),
                Op::IntMul => iv_mul(
                    interval_of(arena, args[0], bounds, depth + 1)?,
                    interval_of(arena, args[1], bounds, depth + 1)?,
                ),
                // `(bv2nat x)` of a width-`w` bit-vector is ALWAYS the unsigned
                // value in `[0, 2^w - 1]`, independent of `x`'s structure. This is
                // the integer bridge behind the SMT-LIB `((_ iand k) a b)`
                // desugaring `bv2nat(bvand(int2bv k a, int2bv k b))`, whose value is
                // structurally in `[0, 2^k)`. Recognizing this exact interval lets
                // the finite-box proof cover an `iand`-bearing query. Decline (sound)
                // if the width does not fit `i128` (`w >= 127` ⇒ `2^w` overflows).
                Op::Bv2Nat => {
                    let inner = *args.first()?;
                    let Sort::BitVec(w) = arena.sort_of(inner) else {
                        return None;
                    };
                    if w >= 127 {
                        return None;
                    }
                    let hi = (1i128 << w).checked_sub(1)?;
                    Some(IntInterval { lo: 0, hi })
                }
                // `int.pow2(x)` on a bounded exponent has an EXACTLY computable
                // interval under cvc5's total semantics (`2^x` for `x ≥ 0`, `0` for
                // `x < 0`): `pow2` is `0` for negative `x` and monotone increasing
                // for `x ≥ 0`, so for `x ∈ [lo, hi]` the value lies in
                // `[pow2(max(lo, 0)) (or 0 if any x < 0 is possible), pow2(hi)]`.
                // Recognizing it lets the finite-box proof cover a `pow2`-bearing
                // query (the exact enumeration then evaluates it via the ground
                // evaluator). Decline (sound) when `hi` is too large for `2^hi` to
                // stay in the safe `i128` table range.
                Op::IntPow2 => {
                    // Largest exponent whose `2^hi` we admit (keeps the covering
                    // width and enumeration modest; larger declines to other routes).
                    const MAX_EXP: i128 = 62;
                    let xi = interval_of(arena, args[0], bounds, depth + 1)?;
                    if xi.hi > MAX_EXP {
                        return None;
                    }
                    let hi_val = if xi.hi < 0 { 0 } else { 1i128 << xi.hi };
                    let lo_val = if xi.lo < 0 { 0 } else { 1i128 << xi.lo };
                    Some(IntInterval {
                        lo: lo_val,
                        hi: hi_val,
                    })
                }
                _ => None,
            }
        }
        TermNode::BoolConst(_)
        | TermNode::BvConst { .. }
        | TermNode::WideBvConst(_)
        | TermNode::RealConst(_) => None,
    }
}

/// Bound side, used while collecting variable bounds from top-level conjuncts.
#[derive(Clone, Copy)]
enum BoundKind {
    /// `var >= c` (lower).
    Lower(i128),
    /// `var <= c` (upper).
    Upper(i128),
}

/// If `term` is exactly a single `Int` variable, returns its symbol.
fn as_int_var(arena: &TermArena, term: TermId) -> Option<SymbolId> {
    match arena.node(term) {
        TermNode::Symbol(sym) if arena.sort_of(term) == Sort::Int => Some(*sym),
        _ => None,
    }
}

/// If `term` is an integer constant, returns its value.
fn as_int_const(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(v) => Some(*v),
        _ => None,
    }
}

/// Recognizes an atomic top-level bound literal `var ⋈ const` (or `const ⋈
/// var`) on an `Int` variable and reports the implied half-bound. Only the
/// **total** order relations `<`, `<=`, `>`, `>=` and equality produce a bound;
/// strict bounds are tightened to the integer-inclusive form (`x < c` ⇒ `x <=
/// c-1`). Returns `(symbol, BoundKind)` pairs (equality yields both halves).
///
/// SOUNDNESS: the caller only feeds atoms that hold UNCONDITIONALLY (top-level
/// conjuncts, never under `or`/`not`/`ite`/`=>`), so each reported half-bound is
/// a fact about every model. A shape not matched here simply yields no bound.
fn atom_bounds(arena: &TermArena, term: TermId, out: &mut Vec<(SymbolId, BoundKind)>) {
    let TermNode::App { op, args } = arena.node(term) else {
        return;
    };
    if args.len() != 2 {
        return;
    }
    let (a, b) = (args[0], args[1]);
    // Normalize to `var ⋈ const`; the flipped orientation swaps the relation.
    let (sym, c, flipped) =
        if let (Some(s), Some(c)) = (as_int_var(arena, a), as_int_const(arena, b)) {
            (s, c, false)
        } else if let (Some(c), Some(s)) = (as_int_const(arena, a), as_int_var(arena, b)) {
            (s, c, true)
        } else {
            return;
        };
    // `op` relates (var, const) when not flipped, else (const, var).
    match op {
        // var == const, or const == var: both bounds.
        Op::Eq => {
            out.push((sym, BoundKind::Lower(c)));
            out.push((sym, BoundKind::Upper(c)));
        }
        // var <= const   (or const >= var)
        Op::IntLe if !flipped => out.push((sym, BoundKind::Upper(c))),
        Op::IntGe if flipped => out.push((sym, BoundKind::Upper(c))),
        // var >= const   (or const <= var)
        Op::IntGe if !flipped => out.push((sym, BoundKind::Lower(c))),
        Op::IntLe if flipped => out.push((sym, BoundKind::Lower(c))),
        // var < const ⇒ var <= const-1   (or const > var)
        Op::IntLt if !flipped => {
            if let Some(d) = c.checked_sub(1) {
                out.push((sym, BoundKind::Upper(d)));
            }
        }
        Op::IntGt if flipped => {
            if let Some(d) = c.checked_sub(1) {
                out.push((sym, BoundKind::Upper(d)));
            }
        }
        // var > const ⇒ var >= const+1   (or const < var)
        Op::IntGt if !flipped => {
            if let Some(d) = c.checked_add(1) {
                out.push((sym, BoundKind::Lower(d)));
            }
        }
        Op::IntLt if flipped => {
            if let Some(d) = c.checked_add(1) {
                out.push((sym, BoundKind::Lower(d)));
            }
        }
        _ => {}
    }
}

/// If `term` is an equality `(= x c)` / `(= c x)` between exactly one `Int`
/// variable and one `Int` constant, returns `(symbol, value)`; else `None`.
fn as_var_eq_const(arena: &TermArena, term: TermId) -> Option<(SymbolId, i128)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (a, b) = (args[0], args[1]);
    if let (Some(s), Some(c)) = (as_int_var(arena, a), as_int_const(arena, b)) {
        Some((s, c))
    } else if let (Some(c), Some(s)) = (as_int_const(arena, a), as_int_var(arena, b)) {
        Some((s, c))
    } else {
        None
    }
}

/// Flattens a (possibly left-associative-nested binary) top-level `or` tree
/// rooted at `term` into its disjunct leaves. SMT-LIB n-ary `(or e1 … ek)` is
/// built as nested binary `(or (or … e_{k-1}) e_k)`, so we recurse through every
/// `BoolOr` node; a non-`or` node is a leaf disjunct.
fn flatten_disjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolOr,
            args,
        } => {
            let args = args.clone();
            for arg in args {
                flatten_disjuncts(arena, arg, out);
            }
        }
        _ => out.push(term),
    }
}

/// Recognizes a **disjunctive finite-value-set bound**: a top-level
/// unconditional conjunct that is a disjunction `(or (= x c1) … (= x ck))` where
/// every disjunct equates the SAME single `Int` variable `x` to an `Int`
/// CONSTANT `cᵢ`. Such a conjunct holds in every model, so `x ∈ {c1,…,ck} ⊆
/// [min cᵢ, max cᵢ]` — a sound box bound. Emits `Lower(min cᵢ)` and `Upper(max
/// cᵢ)` for `x`. The disjunction itself stays in the formula, so the bit-vector
/// search is restricted to the actual `{cᵢ}`, never the full `[min, max]`.
///
/// SOUNDNESS / CONSERVATIVE DECLINE: only a flat disjunction whose EVERY leaf is
/// `var = const` on ONE COMMON variable counts. A disjunct that is not such an
/// equality, or that names a DIFFERENT variable (e.g. `(or (= x 1) (= y 2))`),
/// yields NO bound. Only `BoolAnd`-flattened top-level conjuncts reach here, so a
/// disjunction nested under `not`/`ite`/`=>` is never offered (its truth is not
/// guaranteed) — it bounds nothing. Over-recognizing a non-bound would be a
/// wrong-`unsat`; recognizing fewer shapes is always sound (it just declines).
fn disjunctive_value_set_bounds(
    arena: &TermArena,
    term: TermId,
    out: &mut Vec<(SymbolId, BoundKind)>,
) {
    // Must be a disjunction at the top of this conjunct.
    if !matches!(arena.node(term), TermNode::App { op: Op::BoolOr, .. }) {
        return;
    }
    let mut disjuncts = Vec::new();
    flatten_disjuncts(arena, term, &mut disjuncts);
    if disjuncts.is_empty() {
        return;
    }
    // Every disjunct must pin the SAME variable to a constant.
    let mut common: Option<SymbolId> = None;
    let mut min_c = i128::MAX;
    let mut max_c = i128::MIN;
    for &d in &disjuncts {
        let Some((sym, c)) = as_var_eq_const(arena, d) else {
            // A disjunct that is not `var = const` (a comparison, a different
            // shape, a nested term) breaks the finite-value-set form: decline.
            return;
        };
        match common {
            None => common = Some(sym),
            Some(prev) if prev == sym => {}
            // A disjunct over a DIFFERENT variable (e.g. `(or (= x 1) (= y 2))`)
            // bounds NEITHER variable to a finite set: decline.
            Some(_) => return,
        }
        min_c = min_c.min(c);
        max_c = max_c.max(c);
    }
    if let Some(sym) = common {
        out.push((sym, BoundKind::Lower(min_c)));
        out.push((sym, BoundKind::Upper(max_c)));
    }
}

/// Collects the top-level **unconditional** conjuncts of `assertions` into
/// `out`, flattening `and` and the assertion list itself. A conjunct under any
/// other connective (`or`/`not`/`ite`/`=>`) is NOT unconditional and is skipped
/// (its truth is not guaranteed in every model), so every collected term is a
/// fact — the soundness basis for reading bounds off them.
fn collect_top_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } => {
            let args = args.clone();
            for arg in args {
                collect_top_conjuncts(arena, arg, out);
            }
        }
        _ => out.push(term),
    }
}

/// Walks `term` collecting every free `Int` variable symbol that appears.
fn collect_int_vars(arena: &TermArena, term: TermId, out: &mut BTreeSet<SymbolId>) {
    let mut stack = vec![term];
    let mut seen = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(sym) if arena.sort_of(t) == Sort::Int => {
                out.insert(*sym);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
}

/// Case-count cap for the *pre-blast* enumeration probe. Exhaustive
/// evaluation costs ~µs per case while the exact blast decides these boxes in
/// tens of ms, so past ~10^4 cases enumeration loses to the blast — measured:
/// the `nia_unsat` frontier family fell 40 → 23 (per-instance 20-30× slower)
/// when the 10^6-case probe ran ahead of the blast. Small boxes stay on the
/// evaluation route: it is trusted-by-construction and beats blast setup cost.
const INT_BOX_ENUM_FAST_CASES: u128 = 10_000;

/// Cap for the *post-decline* enumeration fallback: once the blast itself has
/// declined (covering width or CNF too large — e.g. a few cases at huge
/// magnitudes), exhaustive evaluation is the only remaining decider for the
/// proven box, so it may spend the full budget.
const MAX_INT_BOX_ENUM_CASES: u128 = 1_000_000;

/// Proves a finite integer box for every free `Int` variable of `assertions`,
/// then bit-blasts at a width that encodes the box (and every intermediate
/// value) EXACTLY, returning a TRUSTED `Sat`/`Unsat` — or `None` (decline) when
/// the all-bounded proof, the covering width, or the exact-encoding guarantee
/// cannot be established (the query falls through to the sat-only width ladder
/// unchanged).
///
/// SOUNDNESS — why a returned `Unsat` is sound. The bounds are read only off
/// UNCONDITIONAL top-level conjuncts, so each `lo_v ≤ v ≤ hi_v` holds in every
/// model of the original. With a derived bound (via an equality), the same is
/// true: a top-level equality `e₁ = e₂` holds in every model, so a variable it
/// pins to a bounded interval is bounded in every model. We then require an
/// interval analysis to bound EVERY subterm of EVERY assertion (declining
/// otherwise), and pick a width whose signed range strictly contains every such
/// interval. At that width two's-complement arithmetic equals integer
/// arithmetic on every subterm (no `bvadd`/`bvsub`/`bvmul` wraps), so the blast
/// is a *faithful* encoding of the box. Conjoining the explicit clamp `lo ≤ v ≤
/// hi` forces the bit-vector search to stay in the box. Hence: bit-vector
/// `Unsat` ⇒ no model in the box ⇒ (no model can leave the box) ⇒ original
/// `Unsat`. A `Sat` is independently replay-checked against the *original*
/// assertions by `check_with_all_theories`, so a mis-analysis can only cause a
/// declined `Unknown`, never a wrong verdict.
fn decide_bounded_int_blast(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    // Steps 1–6: prove a finite, exactly-encodable box for every free Int
    // variable (shared with the certificate emitter `certify_bounded_int_blast`).
    let proven = match prove_int_box(arena, assertions) {
        IntBoxProof::Box(b) => b,
        // Contradictory direct bounds (`lo > hi`): UNSAT on these literals alone.
        IntBoxProof::TriviallyUnsat => return Ok(Some(CheckResult::Unsat)),
        IntBoxProof::Decline => return Ok(None),
    };

    if let Some(result) =
        decide_int_box_by_evaluation(arena, assertions, &proven, INT_BOX_ENUM_FAST_CASES)
    {
        return Ok(Some(result));
    }

    // 7. Conjoin the explicit clamp `lo ≤ v ≤ hi` for every variable so the
    //    bit-vector search is forced to stay inside the proven box (the encoding
    //    is exact there). Build on the real arena (clones inside the blast).
    let clamped = clamp_to_box(arena, assertions, &proven)?;

    // 8. Solve the clamped, exactly-encoded box at the covering width. When the
    //    box is small enough to enumerate EXHAUSTIVELY as a trusted fallback
    //    (step 9), give the blast only HALF the budget: it decides the UNSAT
    //    family in milliseconds (so a half-budget never regresses `nia_unsat` —
    //    the frontier the 10^4 pre-blast cap protects), but a *bounded nonlinear*
    //    sat like `x²+y²=z²` can burn the whole budget in the blast's multiplier
    //    search and starve the enumeration that would decide it instantly.
    //    Reserving half guarantees the exact, trusted enumeration below still runs
    //    IN-budget. A box too large to enumerate keeps the full budget on the
    //    blast (its only decider).
    let enumerable = int_box_case_count(&proven).is_some_and(|c| c <= MAX_INT_BOX_ENUM_CASES);
    let blast_config = match (enumerable, config.timeout) {
        (true, Some(t)) => config.clone().with_timeout(t / 2),
        _ => config.clone(),
    };
    let blasted = solve_exact_bounded_box(arena, &clamped, proven.width, &blast_config)?;
    if blasted.is_some() {
        return Ok(blasted);
    }

    // 9. The blast declined (covering width, CNF too large, or the reserved
    //    half-budget expired on a hard nonlinear box) — the exact exhaustive
    //    evaluation is the trusted last decider for the proven box, and now has
    //    the reserved budget to finish.
    Ok(decide_int_box_by_evaluation(
        arena,
        assertions,
        &proven,
        MAX_INT_BOX_ENUM_CASES,
    ))
}

fn decide_bounded_int_box_by_evaluation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<CheckResult> {
    match prove_int_box(arena, assertions) {
        // The early-dispatch probe uses the FAST cap: larger boxes fall
        // through to the exact blast route, which decides them 20-30× faster
        // (the full-budget enumeration only runs after the blast declines).
        IntBoxProof::Box(proven) => {
            decide_int_box_by_evaluation(arena, assertions, &proven, INT_BOX_ENUM_FAST_CASES)
        }
        IntBoxProof::TriviallyUnsat => Some(CheckResult::Unsat),
        IntBoxProof::Decline => None,
    }
}

fn decide_int_box_by_evaluation(
    arena: &TermArena,
    assertions: &[TermId],
    proven: &BoundedBox,
    max_cases: u128,
) -> Option<CheckResult> {
    if int_box_case_count(proven)? > max_cases {
        return None;
    }
    let vars = proven
        .bounds
        .iter()
        .map(|(&symbol, &interval)| (symbol, interval))
        .collect::<Vec<_>>();
    let mut assignment = Assignment::new();
    let mut values = Vec::with_capacity(vars.len());
    let mut declined = false;
    if let Some(model) = enumerate_int_box_model(
        arena,
        assertions,
        &vars,
        0,
        &mut assignment,
        &mut values,
        &mut declined,
    ) {
        return Some(CheckResult::Sat(model));
    }
    if declined {
        None
    } else {
        Some(CheckResult::Unsat)
    }
}

fn int_box_case_count(proven: &BoundedBox) -> Option<u128> {
    let mut cases = 1u128;
    for interval in proven.bounds.values() {
        let width = interval.hi.checked_sub(interval.lo)?.checked_add(1)?;
        let width = u128::try_from(width).ok()?;
        cases = cases.checked_mul(width)?;
    }
    Some(cases)
}

fn enumerate_int_box_model(
    arena: &TermArena,
    assertions: &[TermId],
    vars: &[(SymbolId, IntInterval)],
    index: usize,
    assignment: &mut Assignment,
    values: &mut Vec<i128>,
    declined: &mut bool,
) -> Option<Model> {
    if index == vars.len() {
        for &assertion in assertions {
            match eval(arena, assertion, assignment) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => return None,
                Ok(_) | Err(_) => {
                    *declined = true;
                    return None;
                }
            }
        }
        let mut model = Model::new();
        for ((symbol, _), value) in vars.iter().zip(values.iter().copied()) {
            model.set(*symbol, Value::Int(value));
        }
        return Some(model);
    }

    let (symbol, interval) = vars[index];
    let mut value = interval.lo;
    loop {
        assignment.set(symbol, Value::Int(value));
        values.push(value);
        if let Some(model) = enumerate_int_box_model(
            arena,
            assertions,
            vars,
            index + 1,
            assignment,
            values,
            declined,
        ) {
            return Some(model);
        }
        values.pop();
        if *declined || value == interval.hi {
            break;
        }
        value = value.checked_add(1)?;
    }
    None
}

fn contains_smtlib_unspecified_arith(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            match op {
                Op::IntDiv | Op::IntMod
                    if args
                        .get(1)
                        .is_none_or(|&divisor| !is_known_nonzero_int(arena, divisor)) =>
                {
                    return true;
                }
                Op::RealDiv
                    if args
                        .get(1)
                        .is_none_or(|&divisor| !is_known_nonzero_real(arena, divisor)) =>
                {
                    return true;
                }
                _ => {}
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

fn is_known_nonzero_int(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.node(term), TermNode::IntConst(value) if *value != 0)
}

fn is_known_nonzero_real(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.node(term), TermNode::RealConst(value) if !value.is_zero())
}

/// A proven finite integer box: a closed interval per free `Int` variable
/// (deterministic `BTreeMap` order) plus the signed bit-width whose range
/// strictly contains every `Int`-arithmetic subterm's interval, so the
/// two's-complement bit-blast at that width is an EXACT encoding (no wraparound).
#[derive(Clone, Debug)]
struct BoundedBox {
    /// Per-variable proven `[lo, hi]` bound, in stable symbol order.
    bounds: BTreeMap<SymbolId, IntInterval>,
    /// The covering width: every Int subterm's `|value| ≤ max_abs < 2^(w-1)`.
    width: u32,
    /// The witnessed bound on every Int subterm's magnitude (`max_abs`); the
    /// covering-width invariant is `max_abs < 2^(width-1)`, re-checkable cheaply.
    max_abs: u128,
}

/// Outcome of the bound proof (`decide_bounded_int_blast` steps 1–6).
enum IntBoxProof {
    /// A finite, exactly-encodable box was proven for every free Int variable.
    Box(BoundedBox),
    /// Direct bounds are already contradictory (`lo > hi`) — UNSAT on the bound
    /// literals alone, no blast needed.
    TriviallyUnsat,
    /// The all-bounded proof / covering width / exactness could not be
    /// established; the caller falls through unchanged.
    Decline,
}

/// Proves a finite, exactly-encodable integer box for every free `Int` variable
/// of `assertions` (steps 1–6 of the bounded int-blast). Pure analysis: reads
/// the arena, never mutates it, so it is replayable by an independent re-checker.
///
/// SOUNDNESS — see [`decide_bounded_int_blast`]. Bounds are read only off
/// UNCONDITIONAL top-level conjuncts (and equalities pinning a variable to a
/// bounded interval), so each `lo_v ≤ v ≤ hi_v` holds in every model; the width
/// strictly contains every Int subterm's interval, so the blast is faithful.
fn prove_int_box(arena: &TermArena, assertions: &[TermId]) -> IntBoxProof {
    // 1. Free Int variables and the unconditional top-level conjuncts.
    let mut int_vars = BTreeSet::new();
    let mut conjuncts = Vec::new();
    for &a in assertions {
        collect_int_vars(arena, a, &mut int_vars);
        collect_top_conjuncts(arena, a, &mut conjuncts);
    }
    if int_vars.is_empty() {
        return IntBoxProof::Decline;
    }

    // 2. Direct constant half-bounds from top-level conjuncts: atomic order
    //    literals (`atom_bounds`) AND disjunctive finite-value-set bounds
    //    (`disjunctive_value_set_bounds` — a `(or (= x c1) … (= x ck))` conjunct
    //    confines `x` to `[min cᵢ, max cᵢ]`). Both read only UNCONDITIONAL
    //    top-level conjuncts, so each half-bound is a fact about every model.
    let mut raw_bounds: Vec<(SymbolId, BoundKind)> = Vec::new();
    for &c in &conjuncts {
        atom_bounds(arena, c, &mut raw_bounds);
        disjunctive_value_set_bounds(arena, c, &mut raw_bounds);
    }
    let mut lo: HashMap<SymbolId, i128> = HashMap::new();
    let mut hi: HashMap<SymbolId, i128> = HashMap::new();
    for (sym, kind) in raw_bounds {
        match kind {
            BoundKind::Lower(c) => {
                let e = lo.entry(sym).or_insert(c);
                *e = (*e).max(c);
            }
            BoundKind::Upper(c) => {
                let e = hi.entry(sym).or_insert(c);
                *e = (*e).min(c);
            }
        }
    }

    // 2b. Enrich the half-bounds by linear bound propagation over the
    //     UNCONDITIONAL top-level (in)equality conjuncts, to a fixpoint. From
    //     `x + y ≤ 32 ∧ y ≥ 0` this derives `x ≤ 32` (and symmetrically `y ≤ 32`)
    //     — a variable bounded only inside a linear relation, which the
    //     atomic-literal (step 2) and single-equality (step 3) passes miss. Each
    //     derived half-bound is a logical consequence (interval propagation over
    //     facts holding in every model), so conjoining `lo ≤ v ≤ hi` later in
    //     `clamp_to_box` is equisatisfiability-preserving. It only tightens the
    //     half-bound maps; a resulting `lo > hi` is caught by the existing
    //     contradiction check below (→ `TriviallyUnsat`).
    propagate_linear_bounds(arena, &conjuncts, &mut lo, &mut hi);

    let mut bounds: BTreeMap<SymbolId, IntInterval> = BTreeMap::new();
    for &v in &int_vars {
        if let (Some(&l), Some(&h)) = (lo.get(&v), hi.get(&v)) {
            if l <= h {
                bounds.insert(v, IntInterval { lo: l, hi: h });
            } else {
                // Contradictory direct bounds (`lo > hi`): the conjunction is
                // already UNSAT on these literals alone.
                return IntBoxProof::TriviallyUnsat;
            }
        }
    }

    // 3. Derive bounds for still-unbounded variables from top-level EQUALITIES,
    //    to a fixpoint. For an `Int` equality `e₁ = e₂` with exactly one
    //    still-unbounded variable `v` appearing AFFINELY (coefficient `k ≠ 0`),
    //    we have `k·v = interval(e₂ − e₁ with v dropped)`, so `v` is bounded.
    let int_eqs: Vec<(TermId, TermId)> = conjuncts
        .iter()
        .filter_map(|&c| match arena.node(c) {
            TermNode::App { op: Op::Eq, args } if args.len() == 2 => {
                let (a, b) = (args[0], args[1]);
                if arena.sort_of(a) == Sort::Int && arena.sort_of(b) == Sort::Int {
                    Some((a, b))
                } else {
                    None
                }
            }
            _ => None,
        })
        .collect();

    let mut changed = true;
    while changed {
        changed = false;
        for &v in &int_vars {
            if bounds.contains_key(&v) {
                continue;
            }
            for &(e1, e2) in &int_eqs {
                if let Some(iv) = derive_var_bound(arena, v, e1, e2, &bounds) {
                    bounds.insert(v, iv);
                    changed = true;
                    break;
                }
            }
        }
    }

    // 4. Every free Int variable must now be bounded; otherwise decline.
    if int_vars.iter().any(|v| !bounds.contains_key(v)) {
        return IntBoxProof::Decline;
    }

    // 5. Interval-analyze EVERY subterm of EVERY assertion. The covering width
    //    must contain every Int-arithmetic subterm's interval; a subterm whose
    //    interval is not computable (an integer `div`/`mod`/`abs`, a `bv2nat`, an
    //    unbounded var — impossible here — or an `i128` overflow) means we cannot
    //    PROVE the encoding is exact, so we decline.
    let mut max_abs: u128 = 1;
    for &a in assertions {
        if !accumulate_max_abs(arena, a, &bounds, &mut max_abs, 0) {
            return IntBoxProof::Decline;
        }
    }

    // 6. Width to cover signed `[-max_abs-?, max_abs]`: bits for the magnitude
    //    plus a sign bit. `bits(n)` is the smallest `w` with `n < 2^(w-1)`, i.e.
    //    `n` fits in signed `w` bits. Decline beyond `MAX_INT_BLAST_WIDTH`.
    let width = match covering_width(max_abs) {
        Some(w) if w <= axeyum_rewrite::MAX_INT_BLAST_WIDTH => w,
        _ => return IntBoxProof::Decline,
    };

    IntBoxProof::Box(BoundedBox {
        bounds,
        width,
        max_abs,
    })
}

/// Conjoins the explicit clamp `lo ≤ v ≤ hi` for every proven variable onto
/// `assertions`, on `arena`, so the bit-vector search is forced to stay inside
/// the proven box. Deterministic clause order (stable `BTreeMap` iteration).
fn clamp_to_box(
    arena: &mut TermArena,
    assertions: &[TermId],
    proven: &BoundedBox,
) -> Result<Vec<TermId>, SolverError> {
    let mut clamped: Vec<TermId> = assertions.to_vec();
    for (&v, iv) in &proven.bounds {
        let var = arena.var(v);
        let lo_c = arena.int_const(iv.lo);
        let hi_c = arena.int_const(iv.hi);
        let ge = arena
            .int_ge(var, lo_c)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let le = arena
            .int_le(var, hi_c)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        clamped.push(ge);
        clamped.push(le);
    }
    Ok(clamped)
}

// ===========================================================================
// Bound-coverage CERTIFICATE for the bounded int-blast UNSAT (narrows the
// `TrustId::IntBlast` hole for this sub-case).
// ===========================================================================
//
// `decide_bounded_int_blast` returns a TRUSTED integer `Unsat`: the BV layer
// carries DRAT (`check_drat`), but the Int→BV *reduction* itself — that the
// query lives in a finite box and the width encodes it EXACTLY — is the
// `IntBlast` trust hole. This certificate makes that reduction step
// INDEPENDENTLY RE-CHECKABLE: it bundles the per-variable proven bounds, the
// covering width, the witnessed `max_abs`, and the DRAT of the bit-blasted
// (clamped) CNF, and its `recheck` re-derives ALL THREE soundness conditions
// from the ORIGINAL assertions with no trust in the emitter:
//
//   (i)   each variable's `[lo, hi]` is re-derived by `prove_int_box` from the
//         unconditional top-level conjuncts of the original assertions, and must
//         equal the stored bound;
//   (ii)  the covering-width invariant `max_abs < 2^(width-1)` is re-verified by
//         interval-evaluating every Int subterm (so two's-complement arithmetic
//         equals integer arithmetic — no wraparound);
//   (iii) `check_drat` independently accepts the DRAT over the stored DIMACS.
//
// (i)+(ii) witness that the no-overflow side-constraints the blaster conjoins
// (the one thing that makes a *plain* `blast_integers` UNSAT not transfer to the
// original) are VALID over the box, so the box-UNSAT IS the original UNSAT. With
// all three re-checked, this particular integer `Unsat` carries no residual
// `IntBlast` trust.

/// A re-checkable certificate that a *bounded* `QF_NIA` query is `Unsat`: the
/// proven per-variable integer box, the exact covering width, and a DRAT
/// refutation of the bit-blasted clamped CNF. See [`BoundedIntBlastCertificate::recheck`].
#[derive(Debug, Clone)]
pub struct BoundedIntBlastCertificate {
    /// Per-variable proven `[lo, hi]` bound `(symbol, lo, hi)`, in stable order.
    per_var_bounds: Vec<(SymbolId, i128, i128)>,
    /// The covering width used for the exact two's-complement encoding.
    covering_width: u32,
    /// The witnessed magnitude bound on every Int subterm (`max_abs`); the
    /// covering-width invariant is `max_abs < 2^(covering_width-1)`.
    max_abs: u128,
    /// DRAT (+ DIMACS) refutation of the bit-blasted, clamped, exactly-encoded
    /// CNF, independently re-checkable by `check_drat`.
    bv_proof: crate::proof::UnsatProof,
}

impl BoundedIntBlastCertificate {
    /// The proven per-variable box `(symbol, lo, hi)` in stable order.
    #[must_use]
    pub fn per_var_bounds(&self) -> &[(SymbolId, i128, i128)] {
        &self.per_var_bounds
    }

    /// The exact covering width.
    #[must_use]
    pub fn covering_width(&self) -> u32 {
        self.covering_width
    }

    /// The bit-blasted-CNF DRAT certificate.
    #[must_use]
    pub fn bv_proof(&self) -> &crate::proof::UnsatProof {
        &self.bv_proof
    }

    /// **Independently re-validates** the whole Int→BV reduction plus the BV
    /// refutation, from the ORIGINAL `assertions` and this certificate's stored
    /// data, trusting nothing the emitter computed:
    ///
    ///  1. re-runs the bound proof (`prove_int_box`) on `assertions` and requires
    ///     it to prove the SAME box (same per-variable bounds), same width, same
    ///     `max_abs`;
    ///  2. re-verifies the covering invariant `max_abs < 2^(width-1)` (exactness:
    ///     no two's-complement wraparound on any subterm);
    ///  3. regenerates the clamped bounded-int blast and requires its DIMACS to
    ///     match the stored proof's DIMACS;
    ///  4. re-checks the DRAT over the stored DIMACS via `check_drat` (RUP/RAT).
    ///
    /// Returns `Ok(true)` only when all three hold. A `false`/`Err` means the
    /// certificate does not establish the `Unsat` and must not be trusted.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if the stored DRAT/DIMACS is unparseable.
    pub fn recheck(&self, arena: &TermArena, assertions: &[TermId]) -> Result<bool, SolverError> {
        // (1) Re-derive the box from the ORIGINAL assertions; it must match.
        let IntBoxProof::Box(reproven) = prove_int_box(arena, assertions) else {
            return Ok(false);
        };
        if reproven.width != self.covering_width || reproven.max_abs != self.max_abs {
            return Ok(false);
        }
        let mut reproven_bounds: Vec<(SymbolId, i128, i128)> = reproven
            .bounds
            .iter()
            .map(|(&s, iv)| (s, iv.lo, iv.hi))
            .collect();
        reproven_bounds.sort_unstable();
        let mut stored = self.per_var_bounds.clone();
        stored.sort_unstable();
        if reproven_bounds != stored {
            return Ok(false);
        }

        // (2) Re-verify the exactness invariant `max_abs < 2^(width-1)`: the
        //     signed range of `covering_width` bits strictly contains every Int
        //     subterm's magnitude, so no `bvadd`/`bvsub`/`bvmul` wraps.
        if self.covering_width == 0 || self.covering_width > 128 {
            return Ok(false);
        }
        // `2^(w-1)` fits in u128 for `w <= 128` (w-1 <= 127). Equality fails the
        // STRICT bound, so a value exactly at `2^(w-1)` is rejected.
        if (self.covering_width - 1) >= 128 {
            // w == 129 would overflow; already excluded above, but keep total.
            return Ok(false);
        }
        let limit: u128 = 1u128 << (self.covering_width - 1);
        if self.max_abs >= limit {
            return Ok(false);
        }

        // (3) Bind the stored DRAT/DIMACS back to this exact original query:
        //     regenerate the clamped, exactly-encoded bounded-int blast and require
        //     the DIMACS text to match before checking the refutation. Without this
        //     step, a malicious certificate could carry an unrelated UNSAT DIMACS.
        let regenerated_dimacs = bounded_int_blast_dimacs(arena, assertions, &reproven)?;
        if regenerated_dimacs != self.bv_proof.dimacs {
            return Ok(false);
        }

        // (4) Independently re-check the BV refutation.
        self.bv_proof.recheck()
    }
}

fn bounded_int_blast_dimacs(
    arena: &TermArena,
    assertions: &[TermId],
    proven: &BoundedBox,
) -> Result<String, SolverError> {
    let mut scratch = arena.clone();
    let clamped = clamp_to_box(&mut scratch, assertions, proven)?;
    let blast = axeyum_rewrite::blast_integers(&mut scratch, &clamped, proven.width)
        .map_err(|e| SolverError::Backend(format!("int-blast failed: {e}")))?;
    let bv_assertions = blast.assertions().to_vec();
    let lowering = axeyum_bv::lower_terms(&scratch, &bv_assertions)
        .map_err(|error| SolverError::Backend(format!("bit-blasting failed: {error}")))?;
    let roots = lowering
        .roots()
        .iter()
        .map(|root| root.bits()[0])
        .collect::<Vec<_>>();
    let encoding = axeyum_cnf::tseitin_encode(lowering.aig(), &roots)
        .map_err(|error| SolverError::Backend(format!("CNF encoding failed: {error}")))?;
    Ok(encoding.formula().to_dimacs())
}

/// Attempts to produce a fully re-checkable [`BoundedIntBlastCertificate`] for
/// `assertions`: proves the finite box, bit-blasts the clamped query at the
/// covering width, and — if the bit-blasted CNF is `Unsat` — emits the DRAT.
/// Returns `Ok(None)` when the bound proof declines, the box is `Sat`, or the
/// proof core stays inconclusive (the verdict path is unchanged; this only adds
/// a certificate when one cleanly exists).
///
/// This is the **certifying** entry point for bounded `QF_NIA` `Unsat`: a returned
/// certificate, re-checked by [`BoundedIntBlastCertificate::recheck`] against the
/// same `assertions`, establishes the `Unsat` with no residual `IntBlast` trust.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] on an internal encoding/blast failure.
pub fn certify_bounded_int_blast(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<BoundedIntBlastCertificate>, SolverError> {
    let proven = match prove_int_box(arena, assertions) {
        IntBoxProof::Box(b) => b,
        // A trivially-contradictory direct-bound query has no blasted CNF to
        // certify here; the verdict path still reports it `Unsat`. We decline a
        // certificate rather than fabricate one.
        IntBoxProof::TriviallyUnsat | IntBoxProof::Decline => return Ok(None),
    };

    // Blast the clamped, exactly-encoded box on a scratch arena (additive).
    let mut scratch = arena.clone();
    let clamped = clamp_to_box(&mut scratch, assertions, &proven)?;
    let blast = axeyum_rewrite::blast_integers(&mut scratch, &clamped, proven.width)
        .map_err(|e| SolverError::Backend(format!("int-blast failed: {e}")))?;
    let bv_assertions = blast.assertions().to_vec();

    // Emit + self-check the DRAT of the bit-blasted CNF. The blaster's
    // no-overflow side-constraints are conjoined, so this refutes the GUARDED
    // CNF; the bound proof (re-checked by `recheck`) is what licenses treating
    // that as the original UNSAT — the guards are valid over the exact box.
    match crate::proof::export_qf_bv_unsat_proof(&scratch, &bv_assertions)? {
        crate::proof::UnsatProofOutcome::Proved(bv_proof) => {
            let per_var_bounds = proven
                .bounds
                .iter()
                .map(|(&s, iv)| (s, iv.lo, iv.hi))
                .collect();
            Ok(Some(BoundedIntBlastCertificate {
                per_var_bounds,
                covering_width: proven.width,
                max_abs: proven.max_abs,
                bv_proof,
            }))
        }
        crate::proof::UnsatProofOutcome::Satisfiable
        | crate::proof::UnsatProofOutcome::Inconclusive => Ok(None),
    }
}

/// Solves the clamped, exactly-encoded box query (`decide_bounded_int_blast`
/// step 8) at the proven covering `width`, returning a TRUSTED verdict or
/// `None` (decline). `check_with_all_theories` replays a `Sat` against the
/// originals (sound `Sat`); for `Unsat` it conservatively returns `Unknown`
/// because it cannot tell the blast was exact — but the caller HAS proven the
/// box and the width covers every subterm, so we re-blast directly and trust the
/// raw bit-vector `Unsat`. The no-overflow side-constraints the blaster adds are
/// then valid (no product wraps in the box), so the raw `Unsat` is a genuine
/// integer `Unsat`. A raw `Sat` from the re-blast is NOT trusted here (the
/// combined path already had its replay-checked say), so anything but `Unsat`
/// declines.
fn solve_exact_bounded_box(
    arena: &TermArena,
    clamped: &[TermId],
    width: u32,
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    if past_deadline(deadline) {
        return Ok(None);
    }

    // 8a. SAT side via the replay-checked combined path.
    let mut scratch = arena.clone();
    let mut backend = SatBvBackend::new();
    match check_with_all_theories(&mut backend, &mut scratch, clamped, width, config)? {
        sat @ CheckResult::Sat(_) => return Ok(Some(sat)),
        // No integers in the clamped query — impossible here, but a definite
        // `Unsat` transfers regardless.
        CheckResult::Unsat => return Ok(Some(CheckResult::Unsat)),
        CheckResult::Unknown(_) => {}
    }

    // 8b. UNSAT side: re-blast directly to read the RAW bit-vector verdict.
    if past_deadline(deadline) {
        return Ok(None);
    }
    let mut scratch = arena.clone();
    let Ok(blast) = axeyum_rewrite::blast_integers(&mut scratch, clamped, width) else {
        return Ok(None);
    };
    let mut backend = SatBvBackend::new();
    match crate::backend::SolverBackend::check(&mut backend, &scratch, blast.assertions(), config)?
    {
        CheckResult::Unsat => Ok(Some(CheckResult::Unsat)),
        _ => Ok(None),
    }
}

/// If `v` appears affinely (coefficient `k ≠ 0`, no nonlinear occurrence) in
/// `e1 - e2` and every OTHER variable in `e1`/`e2` is already bounded, returns
/// the derived interval for `v` from `k·v = (e2 − e1 without v)`. Otherwise
/// `None` (cannot derive here — decline this variable for now).
fn derive_var_bound(
    arena: &TermArena,
    v: SymbolId,
    e1: TermId,
    e2: TermId,
    bounds: &BTreeMap<SymbolId, IntInterval>,
) -> Option<IntInterval> {
    // Linearize `e1 - e2` as `k·v + rest`, where `rest` is `v`-free. `affine_in`
    // returns `(k, rest_interval)`; it declines (`None`) if `v` occurs
    // non-affinely (e.g. `v·v`, `v·w`) or any `v`-free part is not boundable.
    let (k1, rest1) = affine_in(arena, e1, v, bounds, 0)?;
    let (k2, rest2) = affine_in(arena, e2, v, bounds, 0)?;
    let k = k1.checked_sub(k2)?;
    if k == 0 {
        return None;
    }
    // rest = rest1 - rest2 ; equation: k·v + rest = 0  ⇒  v = -rest / k.
    let rest = iv_sub(rest1, rest2)?;
    let neg_rest = iv_neg(rest)?;
    // Divide the interval by `k` and round INWARD to integers (a sound superset
    // of the true integer solutions: any integer `v` with `k·v ∈ neg_rest` lies
    // in `[ceil(neg_rest.lo/k), floor(neg_rest.hi/k)]`).
    let (dlo, dhi) = if k > 0 {
        (div_ceil(neg_rest.lo, k)?, div_floor(neg_rest.hi, k)?)
    } else {
        // Negative `k` flips the order.
        (div_ceil(neg_rest.hi, k)?, div_floor(neg_rest.lo, k)?)
    };
    if dlo <= dhi {
        Some(IntInterval { lo: dlo, hi: dhi })
    } else {
        // Empty derived interval ⇒ the equality is infeasible given the other
        // bounds; declining keeps this path conservative (the UNSAT, if any, is
        // still found by the exact blast once all vars are bounded — here we
        // simply cannot bound `v`, so we leave it).
        None
    }
}

/// Linearizes `term` as `k·v + rest` in the single variable `v`: returns
/// `(k, interval(rest))` where `rest` is `v`-free, or `None` if `v` occurs
/// non-affinely or any `v`-free subterm is not interval-boundable. `k` is an
/// exact integer coefficient.
fn affine_in(
    arena: &TermArena,
    term: TermId,
    v: SymbolId,
    bounds: &BTreeMap<SymbolId, IntInterval>,
    depth: u32,
) -> Option<(i128, IntInterval)> {
    if depth > 256 {
        return None;
    }
    match arena.node(term) {
        TermNode::IntConst(c) => Some((0, IntInterval::point(*c))),
        TermNode::Symbol(sym) => {
            if *sym == v {
                Some((1, IntInterval::point(0)))
            } else if arena.sort_of(term) == Sort::Int {
                bounds.get(sym).copied().map(|iv| (0, iv))
            } else {
                None
            }
        }
        TermNode::App { op, args } => {
            let args = args.clone();
            match op {
                Op::IntAdd => {
                    let (k1, r1) = affine_in(arena, args[0], v, bounds, depth + 1)?;
                    let (k2, r2) = affine_in(arena, args[1], v, bounds, depth + 1)?;
                    Some((k1.checked_add(k2)?, iv_add(r1, r2)?))
                }
                Op::IntSub => {
                    let (k1, r1) = affine_in(arena, args[0], v, bounds, depth + 1)?;
                    let (k2, r2) = affine_in(arena, args[1], v, bounds, depth + 1)?;
                    Some((k1.checked_sub(k2)?, iv_sub(r1, r2)?))
                }
                Op::IntNeg => {
                    let (k, r) = affine_in(arena, args[0], v, bounds, depth + 1)?;
                    Some((k.checked_neg()?, iv_neg(r)?))
                }
                Op::IntMul => {
                    let (k1, r1) = affine_in(arena, args[0], v, bounds, depth + 1)?;
                    let (k2, r2) = affine_in(arena, args[1], v, bounds, depth + 1)?;
                    // The product is affine in `v` only if at least one factor is
                    // `v`-free (a constant coefficient). `v·v` (both `k≠0`) is
                    // nonlinear ⇒ decline.
                    match (k1, k2) {
                        (0, 0) => Some((0, iv_mul(r1, r2)?)),
                        // (k1·v + r1)·r2  with k2 = 0: factor-2 is `v`-free.
                        (k1, 0) => {
                            let c = const_of(r2)?;
                            Some((k1.checked_mul(c)?, iv_mul(r1, IntInterval::point(c))?))
                        }
                        // r1·(k2·v + r2) with k1 = 0: factor-1 is `v`-free.
                        (0, k2) => {
                            let c = const_of(r1)?;
                            Some((k2.checked_mul(c)?, iv_mul(IntInterval::point(c), r2)?))
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// A point interval's value, or `None` if it is not a single integer (a true
/// non-constant coefficient cannot be folded into a linear term soundly).
fn const_of(iv: IntInterval) -> Option<i128> {
    if iv.lo == iv.hi { Some(iv.lo) } else { None }
}

/// `ceil(a / b)` for nonzero `b`, with the true mathematical rounding; `None` on
/// overflow.
fn div_ceil(a: i128, b: i128) -> Option<i128> {
    if b == 0 {
        return None;
    }
    let q = a.checked_div(b)?;
    let r = a.checked_rem(b)?;
    if r != 0 && ((r > 0) == (b > 0)) {
        q.checked_add(1)
    } else {
        Some(q)
    }
}

/// `floor(a / b)` for nonzero `b`, with the true mathematical rounding; `None` on
/// overflow.
fn div_floor(a: i128, b: i128) -> Option<i128> {
    if b == 0 {
        return None;
    }
    let q = a.checked_div(b)?;
    let r = a.checked_rem(b)?;
    if r != 0 && ((r > 0) != (b > 0)) {
        q.checked_sub(1)
    } else {
        Some(q)
    }
}

/// A normalized affine integer form `sum coeffs[v]·v + constant`. Used by the
/// linear bound propagator; declines (never constructed) for any non-linear
/// subterm, so every form it carries is exact.
#[derive(Clone, Debug, Default)]
struct LinForm {
    coeffs: BTreeMap<SymbolId, i128>,
    constant: i128,
}

impl LinForm {
    fn constant(c: i128) -> Self {
        LinForm {
            coeffs: BTreeMap::new(),
            constant: c,
        }
    }

    fn symbol(s: SymbolId) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(s, 1);
        LinForm {
            coeffs,
            constant: 0,
        }
    }

    /// `self - other`, or `None` on `i128` overflow.
    fn sub(&self, other: &LinForm) -> Option<LinForm> {
        let mut coeffs = self.coeffs.clone();
        for (&s, &c) in &other.coeffs {
            let e = coeffs.entry(s).or_insert(0);
            *e = e.checked_sub(c)?;
        }
        Some(LinForm {
            coeffs,
            constant: self.constant.checked_sub(other.constant)?,
        })
    }

    /// `self + other`, or `None` on `i128` overflow.
    fn add(&self, other: &LinForm) -> Option<LinForm> {
        let mut coeffs = self.coeffs.clone();
        for (&s, &c) in &other.coeffs {
            let e = coeffs.entry(s).or_insert(0);
            *e = e.checked_add(c)?;
        }
        Some(LinForm {
            coeffs,
            constant: self.constant.checked_add(other.constant)?,
        })
    }

    /// `-self`, or `None` on `i128` overflow.
    fn neg(&self) -> Option<LinForm> {
        let mut coeffs = BTreeMap::new();
        for (&s, &c) in &self.coeffs {
            coeffs.insert(s, c.checked_neg()?);
        }
        Some(LinForm {
            coeffs,
            constant: self.constant.checked_neg()?,
        })
    }

    /// `self · c` (scalar), or `None` on `i128` overflow.
    fn scale(&self, c: i128) -> Option<LinForm> {
        let mut coeffs = BTreeMap::new();
        for (&s, &k) in &self.coeffs {
            coeffs.insert(s, k.checked_mul(c)?);
        }
        Some(LinForm {
            coeffs,
            constant: self.constant.checked_mul(c)?,
        })
    }
}

/// Linearizes an `Int`-sorted `term` as an exact affine [`LinForm`], or `None`
/// if any subterm is non-linear (a product of two non-constant factors,
/// `div`/`mod`/`abs`/`bv2nat`/uninterpreted, …). Declining is always sound: no
/// bound is then derived from the atom containing it.
fn lin_form(arena: &TermArena, term: TermId, depth: u32) -> Option<LinForm> {
    if depth > 256 {
        return None;
    }
    match arena.node(term) {
        TermNode::IntConst(c) => Some(LinForm::constant(*c)),
        TermNode::Symbol(sym) if arena.sort_of(term) == Sort::Int => Some(LinForm::symbol(*sym)),
        TermNode::App { op, args } => {
            let args = args.clone();
            match op {
                Op::IntAdd => {
                    lin_form(arena, args[0], depth + 1)?.add(&lin_form(arena, args[1], depth + 1)?)
                }
                Op::IntSub => {
                    lin_form(arena, args[0], depth + 1)?.sub(&lin_form(arena, args[1], depth + 1)?)
                }
                Op::IntNeg => lin_form(arena, args[0], depth + 1)?.neg(),
                Op::IntMul => {
                    let a = lin_form(arena, args[0], depth + 1)?;
                    let b = lin_form(arena, args[1], depth + 1)?;
                    // Affine only if at least one factor is a pure constant.
                    if a.coeffs.is_empty() {
                        b.scale(a.constant)
                    } else if b.coeffs.is_empty() {
                        a.scale(b.constant)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Normalizes a top-level relational conjunct `l ⋈ r` (`⋈ ∈ {≤, <, ≥, >, =}` on
/// `Int`) into one or two `form ≤ 0` [`LinForm`] constraints, pushed onto `out`.
/// A non-relational or non-linear conjunct contributes nothing (sound). Integer
/// strictness is tightened exactly (`l < r ⇔ l − r + 1 ≤ 0`).
fn collect_le_zero_forms(arena: &TermArena, term: TermId, out: &mut Vec<LinForm>) {
    let TermNode::App { op, args } = arena.node(term) else {
        return;
    };
    if args.len() != 2 {
        return;
    }
    let (l, r) = (args[0], args[1]);
    if arena.sort_of(l) != Sort::Int || arena.sort_of(r) != Sort::Int {
        return;
    }
    let (Some(lf), Some(rf)) = (lin_form(arena, l, 0), lin_form(arena, r, 0)) else {
        return;
    };
    // `diff = lin(l) - lin(r)` represents `l - r`.
    let Some(diff) = lf.sub(&rf) else {
        return;
    };
    // Push `form ≤ 0` for the requested relation. Strict `<`/`>` add 1 to the
    // constant (integers). `=` yields BOTH `diff ≤ 0` and `-diff ≤ 0`.
    let plus_one = |f: &LinForm| -> Option<LinForm> { f.add(&LinForm::constant(1)) };
    match op {
        Op::IntLe => out.push(diff),
        Op::IntGe => {
            if let Some(f) = diff.neg() {
                out.push(f);
            }
        }
        Op::IntLt => {
            if let Some(f) = plus_one(&diff) {
                out.push(f);
            }
        }
        Op::IntGt => {
            if let Some(f) = diff.neg().and_then(|n| plus_one(&n)) {
                out.push(f);
            }
        }
        Op::Eq => {
            out.push(diff.clone());
            if let Some(f) = diff.neg() {
                out.push(f);
            }
        }
        _ => {}
    }
}

/// The maximum of `c_v · v`'s upper bound over a `form ≤ 0` constraint, isolating
/// `v`: `c_v·v ≤ -k - Σ_{w≠v} min(c_w·w)`. Returns the numeric right-hand-side
/// upper bound, or `None` if a needed half-bound of some other variable is
/// missing or `i128` overflows.
fn constraint_rhs_max(
    form: &LinForm,
    v: SymbolId,
    lo: &HashMap<SymbolId, i128>,
    hi: &HashMap<SymbolId, i128>,
) -> Option<i128> {
    let mut acc = form.constant.checked_neg()?; // -k
    for (&w, &cw) in &form.coeffs {
        if w == v || cw == 0 {
            continue;
        }
        // min(c_w · w): positive coeff uses w's LOWER bound, negative its UPPER.
        let min_term = if cw > 0 {
            cw.checked_mul(*lo.get(&w)?)?
        } else {
            cw.checked_mul(*hi.get(&w)?)?
        };
        acc = acc.checked_sub(min_term)?;
    }
    Some(acc)
}

/// Deterministic iteration cap for the linear bound-propagation fixpoint.
const MAX_BOUND_PROP_ROUNDS: u32 = 256;

/// Tightens the `lo`/`hi` half-bound maps by interval bound propagation over the
/// linear `form ≤ 0` constraints extracted from `conjuncts`, to a fixpoint (round
/// cap [`MAX_BOUND_PROP_ROUNDS`]). All arithmetic is `checked_*` — an overflow
/// simply skips that derivation (sound decline). Every tightening is a valid
/// consequence of the (unconditional) conjuncts, so it can only prune models
/// that violate them, never a real one.
fn propagate_linear_bounds(
    arena: &TermArena,
    conjuncts: &[TermId],
    lo: &mut HashMap<SymbolId, i128>,
    hi: &mut HashMap<SymbolId, i128>,
) {
    let mut constraints: Vec<LinForm> = Vec::new();
    for &c in conjuncts {
        collect_le_zero_forms(arena, c, &mut constraints);
    }
    if constraints.is_empty() {
        return;
    }
    for _ in 0..MAX_BOUND_PROP_ROUNDS {
        let mut changed = false;
        for form in &constraints {
            for (&v, &cv) in &form.coeffs {
                if cv == 0 {
                    continue;
                }
                let Some(rhs_max) = constraint_rhs_max(form, v, lo, hi) else {
                    continue;
                };
                if cv > 0 {
                    // c_v·v ≤ rhs_max, c_v > 0  ⇒  v ≤ floor(rhs_max / c_v).
                    if let Some(new_hi) = div_floor(rhs_max, cv) {
                        match hi.get(&v).copied() {
                            Some(cur) if new_hi >= cur => {}
                            _ => {
                                hi.insert(v, new_hi);
                                changed = true;
                            }
                        }
                    }
                } else {
                    // c_v·v ≤ rhs_max, c_v < 0  ⇒  v ≥ ceil(rhs_max / c_v).
                    if let Some(new_lo) = div_ceil(rhs_max, cv) {
                        match lo.get(&v).copied() {
                            Some(cur) if new_lo <= cur => {}
                            _ => {
                                lo.insert(v, new_lo);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
}

/// Folds the maximum absolute value over every `Int`-arithmetic subterm of
/// `term` into `max_abs`. Returns `false` (caller declines) if any `Int`
/// subterm's interval is not computable — the exactness guarantee then cannot be
/// established. Non-`Int` subterms (Bool/BV structure, comparisons) are walked
/// for their `Int` children but contribute no magnitude themselves.
fn accumulate_max_abs(
    arena: &TermArena,
    term: TermId,
    bounds: &BTreeMap<SymbolId, IntInterval>,
    max_abs: &mut u128,
    depth: u32,
) -> bool {
    if depth > 1024 {
        return false;
    }
    if arena.sort_of(term) == Sort::Int {
        // Every Int subterm carries a width-`w` value at blast time, so EACH must
        // have a computable interval that the chosen width covers — a deeply
        // nested product (e.g. `x*x` inside `(x*x) - (x*x)`) can dominate even when
        // its parent's interval is tiny. So we record this node's magnitude AND
        // keep recursing into its children (rather than trusting the parent
        // interval to dominate).
        let Some(iv) = interval_of(arena, term, bounds, 0) else {
            return false;
        };
        *max_abs = (*max_abs).max(iv.max_abs());
    }
    match arena.node(term) {
        TermNode::App { args, .. } => {
            let args = args.clone();
            for arg in args {
                if !accumulate_max_abs(arena, arg, bounds, max_abs, depth + 1) {
                    return false;
                }
            }
            true
        }
        _ => true,
    }
}

/// Smallest signed bit-width whose range `[-2^(w-1), 2^(w-1) - 1]` strictly
/// contains every value of magnitude `≤ max_abs`, i.e. the smallest `w` with
/// `max_abs < 2^(w-1)`. `None` if no width `≤ 128` suffices.
fn covering_width(max_abs: u128) -> Option<u32> {
    // Need `2^(w-1) > max_abs`  ⇒  `w - 1 > log2(max_abs)`  ⇒
    // `w = bit_length(max_abs) + 1` (the extra bit is the sign). Guard the
    // `max_abs` magnitude so the strict-greater holds even at a power of two.
    let bits = 128 - max_abs.leading_zeros(); // bit_length(max_abs); 0 ⇒ 0
    let w = bits.checked_add(1)?; // + sign bit
    if w > 128 { None } else { Some(w.max(1)) }
}

/// Smallest integer bit-blast width tried by the ladder. A narrow width leaves no
/// room for a wraparound witness, so a small genuine solution (e.g. `x = 2` for
/// `x*x = 4`) is the only model and replays exactly.
const INT_BLAST_MIN_WIDTH: u32 = 4;

/// Top of the **dense** part of the ladder: every width in `[MIN, DENSE_MAX]` is
/// tried. Small witnesses (and the constants/products around them) live here —
/// e.g. `x = 5` for `x*x = 25` first replays at width 8 — so the dense range must
/// reach comfortably past the small-witness cases while staying cheap (the
/// multiplier blast grows steeply with width).
const INT_BLAST_DENSE_MAX_WIDTH: u32 = 16;

/// Largest integer bit-blast width tried by the ladder — a deterministic work cap.
/// Above [`INT_BLAST_DENSE_MAX_WIDTH`] only a couple of coarse widths are tried
/// (the wide-width multiplier solves are the expensive ones). A genuinely large or
/// unbounded nonlinear integer goal degrades to `Unknown` here rather than blasting
/// an ever-wider (and ever-heavier) multiplier mountain.
const INT_BLAST_MAX_WIDTH: u32 = DEFAULT_INT_WIDTH;

/// Decides a pure-integer-arithmetic fallback query (the LIA engines above could
/// not settle it) by **iterating the bounded bit-blast width** over a deterministic,
/// trimmed ladder, returning the first replay-checked `Sat`.
///
/// The ladder is the dense range `[INT_BLAST_MIN_WIDTH, INT_BLAST_DENSE_MAX_WIDTH]`
/// (where small witnesses live and the narrow-width blast is cheap) followed by a
/// short coarse tail up to [`INT_BLAST_MAX_WIDTH`] (`= DEFAULT_INT_WIDTH`, always
/// reached, preserving the previous single-width default). The wide-width
/// multiplier solves are the expensive ones, so the tail is intentionally sparse —
/// this is the difference between a few-second bound and the old `~31`-width
/// multiplier-mountain hang.
///
/// When `config.timeout` is set, a wall-clock **deadline** is checked *before* each
/// width's solve; an exceeded deadline returns a graceful `Unknown(ResourceLimit)`
/// rather than spinning (the per-width multiplier blast can run far past the budget
/// otherwise — the timeout-honouring guarantee).
///
/// Soundness: [`check_with_all_theories`] only ever returns `Sat` after replaying
/// the projected model against the **original** assertions through the ground
/// evaluator, so accepting the first `Sat` from any width is sound regardless of
/// where it came from. A definite `Unsat` (only possible when no integers are
/// present, which is not this branch) transfers; an `Unknown` at every width
/// (including the genuinely-unbounded / no-integer-root cases like `x*x = 2`)
/// leaves the result `Unknown` — never a wrong `unsat`. The width set is fixed and
/// finite, so the work is deterministically bounded (no OOM-risking unbounded
/// widening).
fn dispatch_int_blast_width_ladder(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Deterministic, finite ladder: a dense narrow range (small witnesses, cheap
    // blasts) plus a sparse coarse tail up to `MAX = DEFAULT_INT_WIDTH` (always
    // reached, so the previous single-width-32 behaviour is preserved). The middle
    // is intentionally thinned and the old `36`/`40` tail dropped — the wide
    // multiplier solves dominate the cost.
    let mut widths: Vec<u32> = (INT_BLAST_MIN_WIDTH..=INT_BLAST_DENSE_MAX_WIDTH).collect();
    let mut w = INT_BLAST_DENSE_MAX_WIDTH + 8;
    while w <= INT_BLAST_MAX_WIDTH {
        widths.push(w);
        w += 8;
    }
    // `DEFAULT_INT_WIDTH` must always be in the ladder (it is the historical single
    // width); add it if the coarse stride skipped it.
    if !widths.contains(&DEFAULT_INT_WIDTH) {
        widths.push(DEFAULT_INT_WIDTH);
    }

    // Wall-clock deadline (only when a timeout is configured): each per-width
    // multiplier blast can otherwise run far past the configured budget. Checked
    // before each solve so the loop always terminates near the deadline with a
    // graceful `Unknown(ResourceLimit)` instead of hanging (mirrors nra.rs).
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));

    let mut last = CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: "bounded integer bit-blasting found no replaying model within the width ladder; \
                 widen the bound"
            .to_owned(),
    });
    for width in widths {
        if past_deadline(deadline) {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "integer bit-blast width ladder: wall-clock timeout reached".to_owned(),
            }));
        }
        // Each width's bit-blast declares fresh `!int_bv_*` bit-vector symbols, whose
        // names collide across widths if reused on the same arena. Run every width on
        // an isolated **clone** of the arena: the original assertion `TermId`s and the
        // original (pre-clone) symbol `SymbolId`s are index-stable in the clone, so a
        // returned `Sat` model — keyed only by the originals — is valid in the caller's
        // arena unchanged.
        let mut scratch = arena.clone();
        let mut backend = SatBvBackend::new();
        // Bound each per-width solve by the budget REMAINING to the shared deadline,
        // not a fresh full `config.timeout`: a width entered just before the deadline
        // must not run a further full timeout past it. The between-width check above
        // then catches the loop promptly (mirrors the NRA path's remaining-deadline
        // sub-solves).
        let width_config = config_with_remaining_deadline(config, deadline);
        match check_with_all_theories(&mut backend, &mut scratch, assertions, width, &width_config)?
        {
            // Replay-checked by `check_with_all_theories`: a sound `Sat`.
            sat @ CheckResult::Sat(_) => return Ok(sat),
            // A definite `Unsat` (no integers present) transfers immediately. With
            // integers, the combined path reports `Unknown` for an in-range `unsat`,
            // so this arm only fires for the integer-free residue and is exact.
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            // Out of range at this width / overflowed replay: remember and widen.
            other @ CheckResult::Unknown(_) => last = other,
        }
    }
    Ok(last)
}

/// Decides a (possibly quantified) query by **finite-domain quantifier
/// expansion** (ADR-0016) followed by [`check_auto`].
///
/// Every quantifier over a finite domain is expanded to its conjunction/
/// disjunction of instances, the quantifier-free result is dispatched, and a
/// `sat` model is **replayed against the original quantified formula** through
/// the enumerating ground evaluator (the trust anchor — an expansion bug cannot
/// yield an unsound `sat`).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for a non-enumerable quantifier domain
/// or a query outside the supported fragment, or [`SolverError`] from the chosen
/// engine; a `sat` model that fails to replay is a [`SolverError::Backend`].
pub fn check_with_quantifiers(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Guarded-finite-`Int` pre-pass: a universal `∀x:Int. (lo<=x<=hi) => inner`
    // is *logically equivalent* to the finite conjunction `⋀_{v=lo}^{hi}
    // inner[x:=v]` (outside the range the implication is vacuously true), so this
    // exact rewrite lets the ordinary dispatch decide an `Int` universal that
    // finite-domain expansion alone rejects. It is strictly additive — only the
    // matched guarded shape is touched, every other assertion is passed through —
    // and equivalence-preserving, so both `sat` and `unsat` transfer. The trust
    // anchor below still replays the *original* (unrewritten) `assertions`.
    let (guard_expanded, guard_changed) = expand_guarded_int_universals(arena, assertions)?;

    // Inner-existential exposure: expanding `∀x:Int. (lo≤x≤hi) ⇒ ∃y. P(x, y)`
    // yields `⋀_{v} ∃y. P(v, y)` — a conjunction of *positive* existentials that
    // skolemization at the assertion root (`skolemize_top_existentials`, run once
    // near the top of `solve`) cannot reach, and which the finite-domain
    // `expand_quantifiers` cannot enumerate (the `∃y` is `Int`-sorted). Skolemize
    // these positive existentials to `P(v, gk_v)` for fresh constants — equisat
    // and equivalence-preserving for the `sat`/`unsat` verdict — so the ordinary
    // QF dispatch decides them. This runs **only** when the guarded pass actually
    // fired *and* a quantifier remains (strictly additive, no re-entry into the
    // quantifier dispatch — the work is inline), so it cannot loop. A quantifier
    // left un-skolemized (an existential in a non-positive position, or a residual
    // universal) keeps the original `expand_quantifiers` route and its sound
    // `Unsupported`-→-refutation fallback, never a wrong verdict.
    let mut skolem_counter = 0u32;
    let replay_base = if guard_changed && has_quantifier(arena, &guard_expanded) {
        let (skolemized, _) =
            skolemize_positive_existentials(arena, &guard_expanded, &mut skolem_counter)?;
        skolemized
    } else {
        guard_expanded
    };

    let expanded = expand_quantifiers(arena, &replay_base).map_err(|error| match error {
        QuantExpandError::UnsupportedDomain(sort) => {
            SolverError::Unsupported(format!("quantifier over non-enumerable domain {sort}"))
        }
        QuantExpandError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;

    // `unsat`/`unknown` of the equivalent quantifier-free formula carries over
    // to the original (expansion is equivalence-preserving).
    let model = match check_auto(arena, &expanded, config)? {
        CheckResult::Sat(model) => model,
        other => return Ok(other),
    };

    // Replay the *quantified* assertions through the enumerating evaluator — the
    // trust anchor for a quantified `sat`. We replay `replay_base`, the
    // equivalence/equisatisfiability-preserving rewrite of the originals: it is
    // the **same** `TermId`s as `assertions` wherever no rewrite fired (so
    // unchanged for the existing Bool/BitVec quantifier path), and where a
    // guarded-`Int` universal *was* rewritten it is the equivalent quantifier-free
    // conjunction (with any exposed inner `∃y` skolemized to a fresh witness the
    // model assigns) — which the enumerating evaluator can actually evaluate (it
    // has no `Int`-domain quantifier enumeration). The model satisfying
    // `⋀_v P(v, gk_v)` witnesses `⋀_v ∃y. P(v, y)`, i.e. the original
    // `∀x.(guard ⇒ ∃y. P)`, so this is just as strong a trust anchor as replaying
    // the original `forall`.
    let assignment = model.to_assignment();
    for &assertion in &replay_base {
        match eval(arena, assertion, &assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(_) => {
                return Err(SolverError::Backend(format!(
                    "quantified sat model replay failed: assertion #{} not satisfied",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "quantified sat model replay failed: assertion #{} evaluation error: {error}",
                    assertion.index()
                )));
            }
        }
    }
    Ok(CheckResult::Sat(model))
}

/// Maximum model-based instantiation rounds before reporting `unknown`.
const MAX_MBQI_ROUNDS: usize = 16;

/// Deterministic cap on accumulated MBQI instances: a universal whose instantiation
/// generates ever-deeper ground terms can grow each round's solve without bound, so
/// the loop bails to `unknown` past this many instances even with no wall-clock budget.
const MAX_MBQI_INSTANCES: usize = 4096;

/// A `Value` as a constant term (scalar sorts only).
fn value_to_const(arena: &mut TermArena, value: &Value) -> Option<TermId> {
    match value {
        Value::Bool(b) => Some(arena.bool_const(*b)),
        Value::Int(n) => Some(arena.int_const(*n)),
        Value::Real(r) => Some(arena.real_const(*r)),
        Value::Bv { width, value } => arena.bv_const(*width, *value).ok(),
        _ => None,
    }
}

/// Whether `term` is an atomic linear-arithmetic literal over the named `sort`
/// (`Int` or `Real`) that the model-based projection primitives (`mbp_lia` /
/// `mbp_lra`) can parse: a comparison or an `Eq` over operands of that sort, or
/// a single `BoolNot` of such a literal. A minimal duplicate of the recognizers
/// that already feed `mbp_*` (kept private to `pdr_lia.rs` / `pdr_lra.rs`); used
/// only to gate eligibility before calling `mbp_*`, which independently re-parses
/// and verifies, so an over-permissive match here is still sound.
fn is_arith_atom(arena: &TermArena, term: TermId, sort: Sort) -> bool {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => is_arith_atom(arena, args[0], sort),
        TermNode::App {
            op: Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe,
            args,
        } => sort == Sort::Int && args.iter().all(|&a| arena.sort_of(a) == Sort::Int),
        TermNode::App {
            op: Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe,
            args,
        } => sort == Sort::Real && args.iter().all(|&a| arena.sort_of(a) == Sort::Real),
        TermNode::App { op: Op::Eq, args } => args.iter().all(|&a| arena.sort_of(a) == sort),
        _ => false,
    }
}

/// Flattens the negation `¬body` into a **conjunction** of negated arithmetic
/// literals over `sort`, returning the literal terms (already negated) or `None`
/// when `¬body` is not a pure conjunction of `LIA`/`LRA` atoms.
///
/// The common eligible shape is a clause `body = (ℓ₁ ∨ … ∨ ℓₙ)` whose negation
/// is `(¬ℓ₁ ∧ … ∧ ¬ℓₙ)` — e.g. `(x ≤ y ∨ x ≥ y+3)` ⇒ `(x > y ∧ x < y+3)`.
/// De Morgan is pushed through `∨` and double negation only; an `∧` under the
/// negation would make `¬body` disjunctive, so it declines (`None`).
fn negate_body_to_conjuncts(
    arena: &mut TermArena,
    body: TermId,
    sort: Sort,
) -> Result<Option<Vec<TermId>>, axeyum_ir::IrError> {
    let mut out = Vec::new();
    if collect_negation_conjuncts(arena, body, sort, &mut out)? {
        Ok(Some(out))
    } else {
        Ok(None)
    }
}

/// Recursive worker for [`negate_body_to_conjuncts`]: pushes the conjuncts of
/// `¬term` onto `out`. Returns `false` (decline) on any non-arithmetic /
/// non-conjunctive shape; `out` is then left in an unspecified partial state and
/// must be discarded by the caller.
fn collect_negation_conjuncts(
    arena: &mut TermArena,
    term: TermId,
    sort: Sort,
    out: &mut Vec<TermId>,
) -> Result<bool, axeyum_ir::IrError> {
    match arena.node(term) {
        // ¬(a ∨ b) = ¬a ∧ ¬b — distribute the negation over each disjunct.
        TermNode::App {
            op: Op::BoolOr,
            args,
        } => {
            let args = args.clone();
            for arg in args {
                if !collect_negation_conjuncts(arena, arg, sort, out)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // ¬¬a = a — the inner term is itself a conjunct of ¬term.
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => {
            let inner = args[0];
            if is_arith_atom(arena, inner, sort) {
                out.push(inner);
                Ok(true)
            } else {
                Ok(false)
            }
        }
        // A bare atom ℓ: ¬ℓ is one conjunct.
        _ => {
            if is_arith_atom(arena, term, sort) {
                let neg = arena.not(term)?;
                out.push(neg);
                Ok(true)
            } else {
                Ok(false)
            }
        }
    }
}

/// Collects the free symbols of `term` into `out` (deterministic, sorted).
fn collect_term_symbols(arena: &TermArena, term: TermId, out: &mut BTreeSet<SymbolId>) {
    let mut stack = vec![term];
    let mut seen = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) => {
                out.insert(*s);
            }
            TermNode::App { args, .. } => {
                let args = args.clone();
                stack.extend(args);
            }
            _ => {}
        }
    }
}

/// A [`Value`] as a ground constant term, restricted to the arithmetic sorts the
/// MBP witness path produces (`Int`/`Real`); `None` otherwise or on overflow.
fn arith_value_to_const(arena: &mut TermArena, value: &Value) -> Option<TermId> {
    match value {
        Value::Int(n) => Some(arena.int_const(*n)),
        Value::Real(r) => Some(arena.real_const(*r)),
        _ => None,
    }
}

/// MBP-driven model-based instantiation of `∀sym. body` (gap-analysis Gap 9).
///
/// Synthesizes a ground instance `body[sym := t]` whose witness `t` refutes the
/// universal at the current `model` even when it is *symbolic in another
/// variable* — the case the scalar candidate probe misses. The method projects
/// the negated body `∃sym. ¬body`:
///
/// 1. **Eligibility.** `¬body` must be a conjunction of `LRA` (real `sym`) or
///    `LIA` (int `sym`) literals; otherwise decline (`None`).
/// 2. **Witness sub-solve.** Fix every *other* variable of `¬body` to its
///    `model` value and solve the quantifier-free conjunction for a `sym`-witness
///    with the same `config`. `Unsat` ⇒ the universal holds at this model ⇒
///    decline; `Sat(M')` gives the witness model.
/// 3. **Project + witness.** Call `mbp_lia` / `mbp_lra` to *certify* the witness
///    region is a sound projection (best-effort: a decline does not block the
///    witness, since the instance is sound regardless — see soundness below) and
///    read the concrete witness `t = M'(sym)`.
/// 4. Build and return `body[sym := t]` (via [`replace_subterms`]).
///
/// **Soundness.** Every returned instance `body[sym := t]` is a logical
/// consequence of `∀sym. body` for *any* `t`, so the projection / sub-solve only
/// *chooses* a useful witness — a bad choice yields a redundant-but-true
/// instance, never an unsound one. The verdict-soundness rests entirely on the
/// caller's existing weakening invariant.
fn mbqi_instance_via_mbp(
    arena: &mut TermArena,
    sym: SymbolId,
    body: TermId,
    model: &Model,
    config: &SolverConfig,
) -> Option<TermId> {
    let sort = arena.symbol(sym).1;
    if sort != Sort::Int && sort != Sort::Real {
        return None;
    }
    // (1) Eligibility: ¬body must be a conjunction of LIA/LRA literals over `sym`.
    let neg_literals = negate_body_to_conjuncts(arena, body, sort).ok()??;
    if neg_literals.is_empty() {
        return None;
    }

    // (2) Witness sub-solve: fix the OTHER variables of ¬body to their model
    // values, then solve the conjunction for a `sym`-witness with the same config.
    let mut others = BTreeSet::new();
    for &lit in &neg_literals {
        collect_term_symbols(arena, lit, &mut others);
    }
    others.remove(&sym);
    let mut sub_query = neg_literals.clone();
    for other in &others {
        let value = model.get(*other)?;
        let var = arena.var(*other);
        let c = arith_value_to_const(arena, &value)?;
        let fixed = arena.eq(var, c).ok()?;
        sub_query.push(fixed);
    }
    let CheckResult::Sat(witness_model) = check_auto(arena, &sub_query, config).ok()? else {
        // Unsat / Unknown: no certified `sym`-witness under these fixings → decline.
        return None;
    };

    // (3) Project (best-effort certification — its decline does not block the
    // sound witness) and read the concrete witness `t = M'(sym)`.
    let _ = mbp_for_sort(arena, sort, &neg_literals, &witness_model, sym);
    let witness_value = witness_model.get(sym)?;
    let t = arith_value_to_const(arena, &witness_value)?;

    // (4) Build the ground instance `body[sym := t]`.
    let var = arena.var(sym);
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    map.insert(var, t);
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    replace_subterms(arena, body, &map, &mut memo).ok()
}

/// Dispatches to the sort-appropriate model-based projection primitive,
/// returning whether the witness region certified (best-effort; the caller does
/// not require success).
fn mbp_for_sort(
    arena: &mut TermArena,
    sort: Sort,
    literals: &[TermId],
    model: &Model,
    sym: SymbolId,
) -> bool {
    match sort {
        Sort::Int => crate::mbp::mbp_lia(arena, literals, model, sym).is_some(),
        Sort::Real => crate::mbp::mbp_lra(arena, literals, model, sym).is_some(),
        _ => false,
    }
}

/// Model-based quantifier instantiation (MBQI): a refutation loop for top-level
/// universals over infinite domains. Each round decides `ground ∧ instances`; on
/// a `sat` candidate, every universal `∀x. body` is checked against the model at
/// the values the model assigns (its candidate instantiation set), and any
/// instance the model **falsifies** — a consequence of the universal that the
/// model violates — is added, blocking that model. `unsat` of the augmented
/// (still-implied) query transfers soundly; if no universal can be refined the
/// result is `unknown` (an infinite `∀` cannot be confirmed `sat` here).
///
/// # Errors
///
/// Returns [`SolverError`] from the underlying engine or an internal builder.
#[allow(clippy::too_many_lines)]
pub fn prove_unsat_by_mbqi(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Split into ground assertions and top-level universals `(bound_var, body)`.
    // This loop only handles single-variable universals with quantifier-free
    // bodies: a quantified body (multi-variable `forall`) or a quantifier in a
    // ground position (existential, nested) is outside its scope, so the whole
    // query defers to the trigger-based fallback (which instantiates uniformly).
    let mut ground: Vec<TermId> = Vec::new();
    let mut universals: Vec<(axeyum_ir::SymbolId, TermId)> = Vec::new();
    for &a in assertions {
        if let TermNode::App {
            op: Op::Forall(sym),
            args,
        } = arena.node(a)
        {
            if has_quantifier(arena, &[args[0]]) {
                return prove_unsat_by_ematching(arena, assertions, config);
            }
            universals.push((*sym, args[0]));
        } else if has_quantifier(arena, &[a]) {
            return prove_unsat_by_ematching(arena, assertions, config);
        } else {
            ground.push(a);
        }
    }
    if universals.is_empty() {
        // No top-level universal to instantiate; defer to the trigger fallback.
        return prove_unsat_by_ematching(arena, assertions, config);
    }
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());

    // Honor the wall-clock budget and a deterministic instance cap: a universal whose
    // instantiation generates ever-deeper ground terms (e.g. `∀x.(x≤y ∨ x≥y+1)`) can
    // grow the per-round `check_auto` without bound, so the loop must degrade to a
    // graceful `Unknown`, never spin (the "unknown is never an error / never hang" rule).
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let mut instances: Vec<TermId> = Vec::new();
    for _ in 0..MAX_MBQI_ROUNDS {
        if past_deadline(deadline) || instances.len() > MAX_MBQI_INSTANCES {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "MBQI: instantiation budget (time or instance count) exhausted".to_owned(),
            }));
        }
        let mut query = ground.clone();
        query.extend(instances.iter().copied());
        // The query is now quantifier-free (ground + instances).
        let result = check_auto(arena, &query, config)?;
        let CheckResult::Sat(model) = result else {
            // `unsat` (sound — instances are implied) or `unknown` transfers.
            return Ok(result);
        };
        // MBQI-as-model-finder (P2.6 T2.6.5): before trying to *refute* the
        // candidate, test whether it is already a **genuine** model of every
        // universal. For the almost-uninterpreted fragment (bound var Int/Real
        // occurring only as a direct UF argument) this is an exhaustive finite
        // check over the model's finite UF tables + defaults, so a `true`
        // verdict certifies `model` satisfies `∀x. body` over the whole infinite
        // domain — a real, replay-checked `sat`. Strictly additive: it only ever
        // turns this loop's `unknown` into `sat`; a decline (`false`) leaves the
        // refutation logic below byte-identical, so the `unsat`/`unknown`
        // directions are unchanged.
        if crate::mbqi_model_finder::all_universals_genuine(arena, &universals, &model) {
            return Ok(CheckResult::Sat(model));
        }
        let assignment = model.to_assignment();
        // Candidate instantiation values: the distinct values the model assigns,
        // grouped by sort, plus 0/1 defaults for arithmetic robustness.
        let mut added = false;
        for &(sym, body) in &universals {
            let sort = arena.symbol(sym).1;
            let var = arena.var(sym);
            let mut candidates: Vec<Value> = Vec::new();
            for (_, v) in model.iter() {
                if v.sort() == sort && !candidates.contains(&v) {
                    candidates.push(v);
                }
            }
            // The key MBQI heuristic: evaluate the body's ground subterms (those
            // not mentioning the bound variable) of the right sort under the
            // model and use their values — so a violation at e.g. `a + b` is found.
            let mut seen = BTreeSet::new();
            let mut stack = vec![body];
            while let Some(t) = stack.pop() {
                if t == var || !seen.insert(t) {
                    continue;
                }
                if arena.sort_of(t) == sort
                    && let Ok(v) = eval(arena, t, &assignment)
                    && !candidates.contains(&v)
                {
                    candidates.push(v);
                }
                if let TermNode::App { args, .. } = arena.node(t) {
                    let args = args.clone();
                    stack.extend(args);
                }
            }
            match sort {
                Sort::Int => {
                    // Also probe one above/below each integer candidate: bound
                    // universals like `∀x. x ≤ c` are violated at `c+1`, which the
                    // exact subterm value `c` does not surface on its own.
                    let neighbours: Vec<i128> = candidates
                        .iter()
                        .filter_map(|v| match v {
                            Value::Int(n) => Some(*n),
                            _ => None,
                        })
                        .flat_map(|n| [n.checked_add(1), n.checked_sub(1)])
                        .flatten()
                        .collect();
                    for n in neighbours.into_iter().chain([0, 1, -1]) {
                        let v = Value::Int(n);
                        if !candidates.contains(&v) {
                            candidates.push(v);
                        }
                    }
                }
                Sort::Real => {
                    // Probe one above/below each real candidate (e.g. `∀r. r ≤ c`
                    // is violated at `c + 1`); `±1` suffices to step across an
                    // open bound expressed by `<`/`≤`/`>`/`≥`.
                    let one = axeyum_ir::Rational::integer(1);
                    let neighbours: Vec<axeyum_ir::Rational> = candidates
                        .iter()
                        .filter_map(|v| match v {
                            Value::Real(r) => Some(*r),
                            _ => None,
                        })
                        .flat_map(|r| [r + one, r - one])
                        .collect();
                    for r in neighbours {
                        let v = Value::Real(r);
                        if !candidates.contains(&v) {
                            candidates.push(v);
                        }
                    }
                }
                Sort::Bool => {
                    candidates.push(Value::Bool(false));
                    candidates.push(Value::Bool(true));
                }
                _ => {}
            }
            let mut this_added = false;
            for v in candidates {
                let mut probe = assignment.clone();
                probe.set(sym, v.clone());
                if matches!(eval(arena, body, &probe), Ok(Value::Bool(false))) {
                    // The model falsifies `body[x:=v]`; add it (implied by forall).
                    let Some(c) = value_to_const(arena, &v) else {
                        continue;
                    };
                    let var = arena.var(sym);
                    let mut map: HashMap<TermId, TermId> = HashMap::new();
                    map.insert(var, c);
                    let mut memo: HashMap<TermId, TermId> = HashMap::new();
                    let inst = replace_subterms(arena, body, &map, &mut memo).map_err(err)?;
                    if !instances.contains(&inst) {
                        instances.push(inst);
                        added = true;
                    }
                    this_added = true;
                    break;
                }
            }
            // Scalar probing is incomplete: a universal violated only at a witness
            // *symbolic in another variable* (beyond the `±1` neighbourhood of the
            // model's scalar candidates) is missed. When the scalar probe found no
            // refinement for this universal, project the negated body `∃x. ¬body`
            // out of `x` (model-based projection over the other variables fixed to
            // the model) to synthesize that witness instance. Additive — it only
            // ever supplies a *true* instance of `∀x. body` (a consequence), never
            // changing the scalar-probe verdict and never an unsound instance.
            if !this_added
                && let Some(inst) = mbqi_instance_via_mbp(arena, sym, body, &model, config)
                && !instances.contains(&inst)
            {
                instances.push(inst);
                added = true;
            }
        }
        if !added {
            // No universal could be refined at this model: the trigger-based
            // family may still refute via compound terms; otherwise `unknown`.
            return prove_unsat_by_ematching(arena, assertions, config);
        }
    }
    Ok(CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: format!("MBQI did not converge within {MAX_MBQI_ROUNDS} rounds"),
    }))
}

/// Attempts to **refute** a (possibly infinite-domain) quantified query by
/// enumerative ground instantiation of its top-level universals (the E-matching
/// family), then deciding the quantifier-free result with [`check_auto`].
///
/// Because instantiation only *weakens* (each instance follows from its
/// universal), a returned [`CheckResult::Unsat`] transfers soundly to the
/// original. A satisfiable instantiation does **not** establish the original is
/// satisfiable, so it is reported [`CheckResult::Unknown`] — *unless* no
/// universal was actually instantiated (a quantifier-free query), in which case
/// the exact `sat`/`unsat` is returned. This is the refutation tool for `Int`/
/// `Real` quantifiers that finite-domain expansion ([`check_with_quantifiers`])
/// cannot enumerate.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] on an internal rewrite failure, or
/// [`SolverError`] from the underlying engine.
pub fn prove_unsat_by_instantiation(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let instantiation = instantiate_universals(arena, assertions)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    decide_instantiation(arena, &instantiation, config)
}

/// Attempts to **refute** a (possibly infinite-domain) quantified query by
/// **trigger-based E-matching** instantiation of its top-level universals, then
/// deciding the result with [`check_auto`].
///
/// Like [`prove_unsat_by_instantiation`] but more capable: each universal's
/// function/array triggers are matched against the formula's ground subterms, so
/// `x` is instantiated with **compound** ground terms (`f(a)`, `select(m,i)`),
/// not only leaves — refuting goals that pure leaf enumeration cannot reach. The
/// bindings still only *weaken* the query, so a returned [`CheckResult::Unsat`]
/// transfers soundly to the original (a satisfiable instantiation is `unknown`;
/// a quantifier-free query decides exactly).
///
/// # Errors
///
/// Returns [`SolverError::Backend`] on an internal rewrite failure, or
/// [`SolverError`] from the underlying engine.
pub fn prove_unsat_by_ematching(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let instantiation = instantiate_with_triggers(arena, assertions)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    decide_instantiation(arena, &instantiation, config)
}

/// Shared back half of the instantiation-based refutation entries: decides the
/// instantiated assertions and maps the result under the weakening contract.
fn decide_instantiation(
    arena: &mut TermArena,
    instantiation: &axeyum_rewrite::Instantiation,
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Quantifiers left after instantiation (nested, existential, or non-top
    // level) cannot be decided by the quantifier-free engines.
    if instantiation.residual_quantifier {
        return Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: "query has quantifiers instantiation does not reach (nested, \
                     existential, or non-top-level)"
                .to_owned(),
        }));
    }

    let result = check_auto(arena, &instantiation.assertions, config)?;
    if !instantiation.instantiated {
        // No universal was weakened: the result is exact.
        return Ok(result);
    }
    // Instantiation weakened the query: `unsat` transfers, anything else is
    // inconclusive for the original.
    match result {
        CheckResult::Unsat => Ok(CheckResult::Unsat),
        CheckResult::Sat(_) => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: "instantiation is satisfiable; the universal may still be violated \
                     outside the instantiated terms"
                .to_owned(),
        })),
        CheckResult::Unknown(reason) => Ok(CheckResult::Unknown(reason)),
    }
}

/// Lifts each Int/Real-sorted `ite(c, a, b)` to a fresh variable `t` plus the
/// Boolean constraints `c → t = a` and `¬c → t = b` (i.e. `¬c ∨ t=a`, `c ∨ t=b`).
/// An exact, equisatisfiable rewrite that moves arithmetic `ite` out of the
/// linear-arithmetic terms (which the simplices' linearizers do not accept) into
/// the propositional structure the lazy-SMT loop handles.
pub(crate) fn lift_arith_ite(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    // Int/Real `ite`: the arith linearizers want a plain variable.
    lift_ite_matching(arena, assertions, |s| matches!(s, Sort::Int | Sort::Real))
}

/// Eliminate **uninterpreted-sort** `ite` equisatisfiably (`ite(c,a,b)` → fresh
/// `t` with `(c→t=a)∧(¬c→t=b)`). The e-graph congruence treats `ite` opaquely, so
/// `x = ite(c, a, b)` over an uninterpreted sort is otherwise undecidable to it.
/// Applied **only** on the slice handed to the e-graph deciders (not globally) so
/// it never adds variables to the UF+arithmetic dispatch budget.
fn lift_uninterpreted_sort_ite(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    lift_ite_matching(arena, assertions, |s| matches!(s, Sort::Uninterpreted(_)))
}

/// Equisatisfiable `ite`-elimination for every `ite` whose result sort matches
/// `want`: replace it with a fresh variable `t` and add `(c→t=a)∧(¬c→t=b)`. A
/// verdict-preserving rewrite (so it can never change `sat`/`unsat`).
fn lift_ite_matching(
    arena: &mut TermArena,
    assertions: &[TermId],
    want: impl Fn(Sort) -> bool,
) -> Result<Vec<TermId>, SolverError> {
    let mut ites: Vec<TermId> = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            let (op, args) = (*op, args.clone());
            if op == Op::Ite && want(arena.sort_of(t)) {
                ites.push(t);
            }
            stack.extend(args);
        }
    }
    if ites.is_empty() {
        return Ok(assertions.to_vec());
    }
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut constraints: Vec<TermId> = Vec::new();
    for (k, t) in ites.iter().enumerate() {
        let TermNode::App { args, .. } = arena.node(*t) else {
            continue;
        };
        let (c, a, b) = (args[0], args[1], args[2]);
        let sort = arena.sort_of(*t);
        let sym = arena
            .declare_internal(&format!("!ite_{k}"), sort)
            .map_err(err)?;
        let tv = arena.var(sym);
        map.insert(*t, tv);
        let nc = arena.not(c).map_err(err)?;
        let ta = arena.eq(tv, a).map_err(err)?;
        let tb = arena.eq(tv, b).map_err(err)?;
        constraints.push(arena.or(nc, ta).map_err(err)?);
        constraints.push(arena.or(c, tb).map_err(err)?);
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len() + constraints.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    for c in constraints {
        out.push(replace_subterms(arena, c, &map, &mut memo).map_err(err)?);
    }
    Ok(out)
}

/// Folds `to_real(a) ± to_real(b)` into `to_real(a ± b)` bottom-up (the `Int→Real`
/// embedding is a ring homomorphism), collapsing a linear combination of coerced
/// integers into a single coercion. Equisatisfiable; enables the exact
/// comparison rewrites downstream.
fn fold_to_real_sums(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &a in assertions {
        out.push(fold_to_real_rec(arena, a, &mut memo).map_err(err)?);
    }
    Ok(out)
}

fn fold_to_real_rec(
    arena: &mut TermArena,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> Result<TermId, axeyum_ir::IrError> {
    if let Some(&c) = memo.get(&term) {
        return Ok(c);
    }
    let result = match arena.node(term) {
        TermNode::App { op, args } => {
            let (op, args) = (*op, args.clone());
            let mut new_args = Vec::with_capacity(args.len());
            for arg in &args {
                new_args.push(fold_to_real_rec(arena, *arg, memo)?);
            }
            let to_real_arg = |arena: &TermArena, t: TermId| match arena.node(t) {
                TermNode::App {
                    op: Op::IntToReal,
                    args,
                } => Some(args[0]),
                _ => None,
            };
            // to_real(<ground int term>)  ->  real const n.  The Int→Real embedding
            // is a ring homomorphism, so folding a *constant* coercion is exact
            // (denotation-preserving). It matters beyond simplification: a numeral in
            // a Real context parses as `to_real(<int term>)` (e.g. `(* skoS3 3)` →
            // `(* skoS3 (to_real 3))`, `(* skoS3 (- 8))` → `(* skoS3 (to_real (- 8)))`,
            // `(/ 471 100)` → `(/ (to_real 471) …)`), and when such constant coercions
            // sit inside a *product* neither the sum fold nor the const-compare rewrite
            // removes them — so the whole query is needlessly sent through the
            // incomplete int↔real relaxation (which relaxes each `to_real(const)` to a
            // free variable and then rejects its own spurious candidates on replay).
            // Evaluating the ground integer operand (guarded — a miss/overflow returns
            // `Err` and we simply do not fold) removes the coercion so a purely-real
            // query reaches its native NRA route. `(- 8)` is `IntNeg(IntConst 8)`, not a
            // bare `IntConst`, so we fold any operand the evaluator resolves to an int.
            let ground_int = if op == Op::IntToReal {
                match eval(arena, new_args[0], &Assignment::new()) {
                    Ok(Value::Int(n)) => Some(n),
                    _ => None,
                }
            } else {
                None
            };
            if let Some(n) = ground_int {
                arena.real_const(Rational::integer(n))
            }
            // to_real(a) +/- to_real(b)  ->  to_real(a +/- b)
            else if matches!(op, Op::RealAdd | Op::RealSub)
                && let (Some(a), Some(b)) = (
                    to_real_arg(arena, new_args[0]),
                    to_real_arg(arena, new_args[1]),
                )
            {
                let int = if op == Op::RealAdd {
                    arena.int_add(a, b)?
                } else {
                    arena.int_sub(a, b)?
                };
                arena.int_to_real(int)?
            } else {
                build_app(arena, op, &new_args)?
            }
        }
        _ => term,
    };
    memo.insert(term, result);
    Ok(result)
}

/// Rewrites comparisons between `to_real(i)` and a rational constant into the
/// equivalent pure-integer atom (exact, since the integer embedding is
/// order-isomorphic): `to_real(i) ≤ c ⟺ i ≤ ⌊c⌋`, `< ⟺ i ≤ ⌈c⌉−1`,
/// `≥ ⟺ i ≥ ⌈c⌉`, `> ⟺ i ≥ ⌊c⌋+1`, `= c ⟺ i = c` if `c` is integral else
/// false. Eliminates the coercion entirely for these (no relaxation).
fn eliminate_to_real_const_compare(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    // Collect (comparison_atom -> replacement) for matching atoms.
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(t) else {
            continue;
        };
        let (op, args) = (*op, args.clone());
        // Recurse first so nested atoms are also considered.
        stack.extend(args.iter().copied());
        let is_cmp = matches!(
            op,
            Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe | Op::Eq
        );
        if !is_cmp || args.len() != 2 {
            continue;
        }
        // Identify `to_real(i)` and a real constant among the two operands.
        let to_real_arg = |t: TermId| match arena.node(t) {
            TermNode::App {
                op: Op::IntToReal,
                args,
            } => Some(args[0]),
            _ => None,
        };
        let real_const = |t: TermId| match arena.node(t) {
            TermNode::RealConst(r) => Some(*r),
            _ => None,
        };
        // `to_real(i) op to_real(j)` ⟺ `i op j` (both integer-valued): rewrite to
        // the integer comparison, eliminating both coercions exactly.
        if let (Some(i), Some(j)) = (to_real_arg(args[0]), to_real_arg(args[1])) {
            let new = match op {
                Op::RealLt => arena.int_lt(i, j).map_err(err)?,
                Op::RealLe => arena.int_le(i, j).map_err(err)?,
                Op::RealGt => arena.int_gt(i, j).map_err(err)?,
                Op::RealGe => arena.int_ge(i, j).map_err(err)?,
                Op::Eq => arena.eq(i, j).map_err(err)?,
                _ => continue,
            };
            map.insert(t, new);
            continue;
        }
        // Normalize to `to_real(i) <op'> c` (flip if the constant is on the left).
        let (i, c, flipped) =
            if let (Some(i), Some(c)) = (to_real_arg(args[0]), real_const(args[1])) {
                (i, c, false)
            } else if let (Some(c), Some(i)) = (real_const(args[0]), to_real_arg(args[1])) {
                (i, c, true)
            } else {
                continue;
            };
        let floor = c.numerator().div_euclid(c.denominator());
        let is_int = c.denominator() == 1;
        let ceil = if is_int { floor } else { floor + 1 };
        // Effective relation with `to_real(i)` on the left.
        let rel = match (op, flipped) {
            (Op::RealLt, false) | (Op::RealGt, true) => "lt",
            (Op::RealLe, false) | (Op::RealGe, true) => "le",
            (Op::RealGt, false) | (Op::RealLt, true) => "gt",
            (Op::RealGe, false) | (Op::RealLe, true) => "ge",
            (Op::Eq, _) => "eq",
            _ => continue,
        };
        let new = match rel {
            // i < c  ⟺  i ≤ ⌈c⌉−1
            "lt" => {
                let k = arena.int_const(ceil - 1);
                arena.int_le(i, k).map_err(err)?
            }
            "le" => {
                let k = arena.int_const(floor);
                arena.int_le(i, k).map_err(err)?
            }
            "gt" => {
                let k = arena.int_const(floor + 1);
                arena.int_ge(i, k).map_err(err)?
            }
            "ge" => {
                let k = arena.int_const(ceil);
                arena.int_ge(i, k).map_err(err)?
            }
            // i = c  ⟺  (c integral ∧ i = c) else false
            _ => {
                if is_int {
                    let k = arena.int_const(floor);
                    arena.eq(i, k).map_err(err)?
                } else {
                    arena.bool_const(false)
                }
            }
        };
        map.insert(t, new);
    }
    if map.is_empty() {
        return Ok(assertions.to_vec());
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    Ok(out)
}

/// Rewrites comparisons between `to_int(r)` (= ⌊r⌋) and an integer constant into
/// the equivalent pure-real atom (exact): `to_int(r) ≤ c ⟺ r < c+1`,
/// `< c ⟺ r < c`, `≥ c ⟺ r ≥ c`, `> c ⟺ r ≥ c+1`, `= c ⟺ c ≤ r < c+1`.
/// Eliminates the coercion for the common "floor vs integer literal" pattern.
fn eliminate_to_int_const_compare(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(t) else {
            continue;
        };
        let (op, args) = (*op, args.clone());
        stack.extend(args.iter().copied());
        if !matches!(op, Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe | Op::Eq) || args.len() != 2
        {
            continue;
        }
        let to_int_arg = |t: TermId| match arena.node(t) {
            TermNode::App {
                op: Op::RealToInt,
                args,
            } => Some(args[0]),
            _ => None,
        };
        let int_const = |t: TermId| match arena.node(t) {
            TermNode::IntConst(n) => Some(*n),
            _ => None,
        };
        let (r, c, flipped) = if let (Some(r), Some(c)) = (to_int_arg(args[0]), int_const(args[1]))
        {
            (r, c, false)
        } else if let (Some(c), Some(r)) = (int_const(args[0]), to_int_arg(args[1])) {
            (r, c, true)
        } else {
            continue;
        };
        let rel = match (op, flipped) {
            (Op::IntLt, false) | (Op::IntGt, true) => "lt",
            (Op::IntLe, false) | (Op::IntGe, true) => "le",
            (Op::IntGt, false) | (Op::IntLt, true) => "gt",
            (Op::IntGe, false) | (Op::IntLe, true) => "ge",
            (Op::Eq, _) => "eq",
            _ => continue,
        };
        let c_real = arena.real_const(axeyum_ir::Rational::integer(c));
        let c_plus_real = arena.real_const(axeyum_ir::Rational::integer(c + 1));
        let new = match rel {
            "lt" => arena.real_lt(r, c_real).map_err(err)?, // ⌊r⌋<c ⟺ r<c
            "le" => arena.real_lt(r, c_plus_real).map_err(err)?, // ⌊r⌋≤c ⟺ r<c+1
            "ge" => arena.real_ge(r, c_real).map_err(err)?, // ⌊r⌋≥c ⟺ r≥c
            "gt" => arena.real_ge(r, c_plus_real).map_err(err)?, // ⌊r⌋>c ⟺ r≥c+1
            _ => {
                // ⌊r⌋ = c ⟺ c ≤ r < c+1
                let ge = arena.real_ge(r, c_real).map_err(err)?;
                let lt = arena.real_lt(r, c_plus_real).map_err(err)?;
                arena.and(ge, lt).map_err(err)?
            }
        };
        map.insert(t, new);
    }
    if map.is_empty() {
        return Ok(assertions.to_vec());
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    Ok(out)
}

/// Maximum integer range over which a bounded `to_real(i)` is linked exactly to
/// its operand (a finite case-split); wider ranges fall back to relaxation.
const MAX_COERCION_LINK: i128 = 64;

/// Replaces each Int↔Real coercion (`to_real`/`to_int`/`is_int`) with a fresh
/// variable of its result sort, shared per distinct term so a contradiction on
/// the same coerced value is preserved. For a `to_real(i)` whose integer operand
/// has a small constant range, also appends exact linking constraints
/// `(i = v) → (r = v)` for each `v` in range — making that coercion *complete*
/// (not just a relaxation). Returns the rewritten assertions (plus any links) and
/// whether any coercion was found; `sat` soundness still comes from replay.
fn relax_coercions(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<(Vec<TermId>, bool), SolverError> {
    let mut terms: Vec<TermId> = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            let (op, args) = (*op, args.clone());
            if matches!(op, Op::IntToReal | Op::RealToInt | Op::RealIsInt) {
                terms.push(t);
            }
            stack.extend(args);
        }
    }
    if terms.is_empty() {
        return Ok((assertions.to_vec(), false));
    }
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut links: Vec<TermId> = Vec::new();
    for (idx, t) in terms.into_iter().enumerate() {
        let sort = arena.sort_of(t);
        let sym = arena
            .declare_internal(&format!("!coerce_{idx}"), sort)
            .map_err(err)?;
        let fresh = arena.var(sym);
        map.insert(t, fresh);
        // Exact linking for a bounded `to_real(i)`: r = i over its finite range.
        if let TermNode::App {
            op: Op::IntToReal,
            args,
        } = arena.node(t)
        {
            let operand = args[0];
            if let (Some(lo), Some(hi)) = int_bounds(arena, assertions, operand)
                && hi >= lo
                && hi - lo <= MAX_COERCION_LINK
            {
                for v in lo..=hi {
                    let iv = arena.int_const(v);
                    let rv = arena.real_const(axeyum_ir::Rational::integer(v));
                    let i_eq = arena.eq(operand, iv).map_err(err)?;
                    let r_eq = arena.eq(fresh, rv).map_err(err)?;
                    let n = arena.not(i_eq).map_err(err)?;
                    links.push(arena.or(n, r_eq).map_err(err)?); // (i=v) → (r=v)
                }
            }
        }
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len() + links.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    out.extend(links);
    Ok((out, true))
}

/// Tightest constant `(lower, upper)` bounds on integer `term` from the
/// top-level assertions (`term ≤ c`, `c ≤ term`, `<`/`>` with the ±1 shift, and
/// `term = c`); each `None` if unbounded.
fn int_bounds(
    arena: &TermArena,
    assertions: &[TermId],
    term: TermId,
) -> (Option<i128>, Option<i128>) {
    let mut lo: Option<i128> = None;
    let mut hi: Option<i128> = None;
    let mut see_lo = |c: i128| lo = Some(lo.map_or(c, |x: i128| x.max(c)));
    let mut see_hi = |c: i128| hi = Some(hi.map_or(c, |x: i128| x.min(c)));
    let int_const = |t: TermId| match arena.node(t) {
        TermNode::IntConst(n) => Some(*n),
        _ => None,
    };
    for &a in assertions {
        let TermNode::App { op, args } = arena.node(a) else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let (op, l, r) = (*op, args[0], args[1]);
        let (lc, rc) = (int_const(l), int_const(r));
        match op {
            Op::IntLe => {
                if l == term
                    && let Some(c) = rc
                {
                    see_hi(c);
                }
                if r == term
                    && let Some(c) = lc
                {
                    see_lo(c);
                }
            }
            Op::IntLt => {
                if l == term
                    && let Some(c) = rc
                {
                    see_hi(c - 1);
                }
                if r == term
                    && let Some(c) = lc
                {
                    see_lo(c + 1);
                }
            }
            Op::IntGe => {
                if l == term
                    && let Some(c) = rc
                {
                    see_lo(c);
                }
                if r == term
                    && let Some(c) = lc
                {
                    see_hi(c);
                }
            }
            Op::IntGt => {
                if l == term
                    && let Some(c) = rc
                {
                    see_lo(c + 1);
                }
                if r == term
                    && let Some(c) = lc
                {
                    see_hi(c - 1);
                }
            }
            Op::Eq => {
                if l == term
                    && let Some(c) = rc
                {
                    see_lo(c);
                    see_hi(c);
                }
                if r == term
                    && let Some(c) = lc
                {
                    see_lo(c);
                    see_hi(c);
                }
            }
            _ => {}
        }
    }
    (lo, hi)
}

/// Which theory features a query uses.
// A flat set of independent theory-presence flags reads better than a packed
// enum; each is checked independently in `check_auto`.
#[allow(clippy::struct_excessive_bools)]
struct Features {
    has_real: bool,
    /// Any sort/operator handled by the bit-blasting composition (bit-vectors,
    /// arrays, integers, uninterpreted functions) — i.e. not pure Bool/real.
    has_bitblast: bool,
    has_int: bool,
    /// Any bit-vector or floating-point sort.
    has_bv_or_float: bool,
    /// Any datatype sort or constructor/selector/tester op (ADR-0022).
    has_datatype: bool,
    /// Any uninterpreted-function application (`Op::Apply`).
    has_function: bool,
    /// Any term whose sort is a declared uninterpreted carrier.
    has_uninterpreted_sort: bool,
    /// Any array-sorted term (`select`/`store`/array equality).
    has_array: bool,
    /// Any array whose index or element sort is not a bit-vector.
    has_non_bv_array: bool,
    /// Any array whose index or element sort is outside exact Bool/BitVec theory.
    has_non_bool_bv_array: bool,
}

impl Features {
    fn scan_within(
        arena: &TermArena,
        assertions: &[TermId],
        deadline: Option<Instant>,
    ) -> Option<Self> {
        let mut features = Features {
            has_real: false,
            has_bitblast: false,
            has_int: false,
            has_bv_or_float: false,
            has_datatype: false,
            has_function: false,
            has_uninterpreted_sort: false,
            has_array: false,
            has_non_bv_array: false,
            has_non_bool_bv_array: false,
        };
        let mut seen = BTreeSet::new();
        let mut stack = assertions.to_vec();
        while let Some(term) = stack.pop() {
            if past_deadline(deadline) {
                return None;
            }
            if !seen.insert(term) {
                continue;
            }
            features.note_sort(arena.sort_of(term));
            if let TermNode::App { op, args } = arena.node(term) {
                if matches!(op, Op::Apply(_)) {
                    features.has_bitblast = true;
                    features.has_function = true;
                }
                if matches!(
                    op,
                    Op::DtConstruct { .. } | Op::DtSelect { .. } | Op::DtTest(_)
                ) {
                    features.has_datatype = true;
                }
                for &arg in &**args {
                    if past_deadline(deadline) {
                        return None;
                    }
                    stack.push(arg);
                }
            }
        }
        Some(features)
    }

    fn note_sort(&mut self, sort: Sort) {
        match sort {
            Sort::Real => self.has_real = true,
            Sort::Int => {
                self.has_bitblast = true;
                self.has_int = true;
            }
            Sort::BitVec(_) | Sort::Float { .. } => {
                self.has_bitblast = true;
                self.has_bv_or_float = true;
            }
            Sort::Array { index, element } => {
                self.has_bitblast = true;
                self.has_array = true;
                if sort.array_widths().is_none() {
                    self.has_non_bv_array = true;
                }
                if !matches!(index, ArraySortKey::Bool | ArraySortKey::BitVec(_))
                    || !matches!(element, ArraySortKey::Bool | ArraySortKey::BitVec(_))
                {
                    self.has_non_bool_bv_array = true;
                }
                self.note_sort(index.to_sort());
                self.note_sort(element.to_sort());
            }
            Sort::Datatype(_) => self.has_datatype = true,
            Sort::Uninterpreted(_) => self.has_uninterpreted_sort = true,
            // `Bool` contributes no theory flag. `Seq` is a no-op for now
            // (TODO(P2.7 A.1b): no sequence feature/route exists yet and no
            // front-end produces a `Seq` sort, so this is unreachable today; add a
            // `has_seq` feature + route when sequences land, rather than falling
            // through to bit-blasting).
            Sort::Bool | Sort::Seq(_) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn abv_online_probe_isolated_from_caller_arena() {
        let mut arena = TermArena::new();
        let left = arena.array_var("isolated_abv_left", 4, 8).unwrap();
        let right = arena.array_var("isolated_abv_right", 4, 8).unwrap();
        let equal = arena.eq(left, right).unwrap();
        let different = arena.not(equal).unwrap();
        let assertions = [different];
        let features = Features::scan_within(&arena, &assertions, None).unwrap();
        let original_terms = arena.len();
        let mut recorder = None;

        let result = dispatch_abv_online(
            &mut arena,
            &assertions,
            &SolverConfig::default(),
            &features,
            &mut recorder,
        )
        .unwrap();
        let Some(CheckResult::Sat(model)) = result else {
            panic!("expected the isolated ABV probe to decide SAT");
        };
        assert_eq!(arena.len(), original_terms);
        assert_eq!(
            eval(&arena, different, &model.to_assignment()),
            Ok(Value::Bool(true))
        );
    }

    #[test]
    fn aufbv_online_probe_isolated_from_caller_arena() {
        let mut arena = TermArena::new();
        let left = arena.array_var("isolated_aufbv_left", 4, 4).unwrap();
        let right = arena.array_var("isolated_aufbv_right", 4, 4).unwrap();
        let function = arena
            .declare_fun("isolated_aufbv_f", &[Sort::BitVec(4)], Sort::BitVec(4))
            .unwrap();
        let x = arena.bv_var("isolated_aufbv_x", 4).unwrap();
        let fx = arena.apply(function, &[x]).unwrap();
        let function_fixed = arena.eq(fx, x).unwrap();
        let equal = arena.eq(left, right).unwrap();
        let different = arena.not(equal).unwrap();
        let assertions = [function_fixed, different];
        let features = Features::scan_within(&arena, &assertions, None).unwrap();
        let original_terms = arena.len();
        let mut recorder = None;

        let result = dispatch_ufbv_online(
            &mut arena,
            &assertions,
            &SolverConfig::default(),
            &features,
            &mut recorder,
        )
        .unwrap();
        let Some(CheckResult::Sat(model)) = result else {
            panic!("expected the isolated AUFBV probe to decide SAT");
        };
        assert_eq!(arena.len(), original_terms);
        let assignment = model.to_assignment();
        assert!(
            assertions
                .iter()
                .all(|&assertion| eval(&arena, assertion, &assignment) == Ok(Value::Bool(true)))
        );
    }

    #[test]
    fn check_auto_uses_term_identity_refuter_before_theory_routes() {
        let mut arena = TermArena::new();
        let x = arena.real_var("x").unwrap();
        let y = arena.real_var("y").unwrap();
        let true_ = arena.bool_const(true);
        let ite = arena.ite(true_, x, y).unwrap();
        let eq = arena.eq(x, ite).unwrap();
        let diseq = arena.not(eq).unwrap();

        let config = SolverConfig::default();
        let (result, trace) = check_auto_explained(&mut arena, &[diseq], &config).unwrap();
        assert!(
            matches!(result, CheckResult::Unsat),
            "term identity disequality must be unsat, got {result:?}"
        );
        let trace = trace.to_string();
        assert!(
            trace.contains("term-identity-refuter"),
            "trace should record term-identity-refuter, got:\n{trace}"
        );
    }

    #[test]
    fn lia_budget_unknown_annotation_reports_skipped_uf_context() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::Int], Sort::Int)
            .expect("declare f");
        let x = arena.int_var("x").expect("x");
        let y = arena.int_var("y").expect("y");
        let fx = arena.apply(f, &[x]).expect("f(x)");
        let fy = arena.apply(f, &[y]).expect("f(y)");
        let assertion = arena.eq(fx, fy).expect("eq");
        let reason = UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: "inner arithmetic timeout".to_string(),
        };

        let annotated = annotate_lia_budget_before_uf(&arena, &[assertion], &reason);

        assert_eq!(annotated.kind, UnknownKind::ResourceLimit);
        assert!(annotated.detail.contains("inner arithmetic timeout"));
        assert!(
            annotated
                .detail
                .contains("downstream UF-aware routes were not reached")
        );
        assert!(annotated.detail.contains("arithmetic_function=true"));
        assert!(annotated.detail.contains("ackermann_pairs=1"));
    }

    #[test]
    fn overbound_integer_uf_arith_skips_generic_lia_dpll_for_uf_routes() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::Int], Sort::Int)
            .expect("declare f");
        let mut assertions = Vec::new();
        for i in 0..12 {
            let v = arena.int_var(&format!("x{i}")).expect("x");
            let app = arena.apply(f, &[v]).expect("f(x)");
            let value = arena.int_const(i128::from(i));
            assertions.push(arena.eq(app, value).expect("pin app"));
        }
        while assertions.len() <= MAX_PRE_LIA_UF_PROBE_ASSERTIONS {
            let i = assertions.len();
            let pad = arena.int_var(&format!("pad{i}")).expect("pad");
            let zero = arena.int_const(0);
            assertions.push(arena.int_ge(pad, zero).expect("pad>=0"));
        }

        assert!(
            crate::euf::ackermann_congruence_pairs(&arena, &assertions)
                > crate::euf::MAX_ACKERMANN_CONGRUENCE_PAIRS
        );
        let features = Features::scan_within(&arena, &assertions, None).unwrap();
        assert!(should_route_uf_arith_before_lia_dpll(
            &arena,
            &assertions,
            &features
        ));

        let mut trace = RouteTrace::new();
        let mut rec = Some(&mut trace);
        let result = dispatch_int_linear_refuters(
            &mut arena,
            &assertions,
            &SolverConfig::default(),
            &features,
            &mut rec,
        )
        .expect("dispatch");

        assert!(
            result.is_none(),
            "linear refuters should fall through to UF routes"
        );
        let trace_text = trace.to_string();
        assert!(
            trace_text.contains("lia-dpll: declined"),
            "trace should record the skipped generic LIA route, got:\n{trace_text}"
        );
        assert!(
            trace_text.contains("route the single large function-free arithmetic abstraction"),
            "trace should explain the UF-aware scheduling, got:\n{trace_text}"
        );
    }

    #[test]
    fn arithmetic_uf_overbound_pre_lia_probe_decides_on_clone() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("f", &[Sort::Int], Sort::Int)
            .expect("declare f");
        let mut assertions = Vec::new();
        for i in 0..20 {
            let v = arena.int_var(&format!("pad{i}")).expect("pad");
            let app = arena.apply(f, &[v]).expect("f(pad)");
            let value = arena.int_const(i128::from(i));
            assertions.push(arena.eq(app, value).expect("pin app"));
        }
        let a = arena.int_var("a").expect("a");
        let b = arena.int_var("b").expect("b");
        let fa = arena.apply(f, &[a]).expect("f(a)");
        let fb = arena.apply(f, &[b]).expect("f(b)");
        let fa_eq_fb = arena.eq(fa, fb).expect("f(a)=f(b)");
        assertions.push(arena.not(fa_eq_fb).expect("diseq"));
        assertions.push(arena.eq(a, b).expect("a=b"));
        assert!(
            crate::euf::ackermann_congruence_pairs(&arena, &assertions)
                > crate::euf::MAX_ACKERMANN_CONGRUENCE_PAIRS
        );

        let config = SolverConfig::default().with_timeout(Duration::from_secs(10));
        let features = Features::scan_within(&arena, &assertions, None).unwrap();
        let mut trace = RouteTrace::new();
        let mut rec = Some(&mut trace);
        let result = dispatch_arith_uf_overbound_probe_before_lia(
            &arena,
            &assertions,
            &config,
            &features,
            &mut rec,
        )
        .unwrap();

        assert_eq!(result, Some(CheckResult::Unsat));
        let trace_text = trace.to_string();
        assert!(
            trace_text.contains("uf-arith-lazy-overbound-pre-lia: decided unsat"),
            "pre-LIA UF-aware route should decide the overbound congruence conflict, got:\n{trace_text}"
        );
    }

    /// `solve` routes a *too-wide-to-enumerate* (`BitVec(32)`) quantified EUF
    /// refutation through the e-graph keystone instantiation loop: finite-domain
    /// expansion refuses a 2³² domain (`QUANT_EXPAND_BIT_LIMIT`), so the fallback
    /// fires, and the congruence-aware trigger instantiation refutes it by firing
    /// `f(x)` at the ground `f(a)`. This pins the dispatch wiring (`solve` →
    /// keystone) in place. (UF is finite-scalar-only in the IR, so a 33-bit-plus
    /// domain is how an unbounded UF quantifier surfaces here.)
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn array_extensionality_conflict_is_unsat_via_congruence() {
        // a = b ∧ select(a, i) ≠ select(b, i) over a 16-bit index (too wide for the
        // eager extensionality enumeration, which refuses indices above its small
        // finite-index cap) ⇒ UNSAT
        // by congruence: a = b makes select(a,i) and select(b,i) congruent.
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 16, 8).unwrap();
        let b = arena.array_var("b", 16, 8).unwrap();
        let i = arena.bv_var("i", 16).unwrap();
        let sa = arena.select(a, i).unwrap();
        let sb = arena.select(b, i).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let sel_ne = {
            let e = arena.eq(sa, sb).unwrap();
            arena.not(e).unwrap()
        };
        let result = solve(&mut arena, &[a_eq_b, sel_ne], &SolverConfig::default()).unwrap();
        assert!(
            matches!(result, CheckResult::Unsat),
            "wide-index array extensionality conflict must be unsat, got {result:?}"
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn solve_refutes_wide_bv_quantified_euf_via_keystone() {
        let mut arena = TermArena::new();
        let w = 32;
        let bv = Sort::BitVec(w);
        let f = arena.declare_fun("f", &[bv], bv).unwrap();
        let a = arena.bv_var("a", w).unwrap();
        let b = arena.bv_var("b", w).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        // f(a) = b ∧ a ≠ b
        let fa_eq_b = arena.eq(fa, b).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let a_ne_b = arena.not(a_eq_b).unwrap();
        // ∀x. f(x) = x  (over a domain too wide to enumerate)
        let x = arena.declare("x", bv).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let body = arena.eq(fx, xv).unwrap();
        let forall = arena.forall(x, body).unwrap();

        // Instantiating x↦a gives f(a)=a, which with f(a)=b forces a=b ⨯ a≠b.
        let config = SolverConfig::default();
        let result = solve(&mut arena, &[forall, fa_eq_b, a_ne_b], &config).unwrap();
        assert!(
            matches!(result, CheckResult::Unsat),
            "expected Unsat from keystone instantiation, got {result:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Bounded EXACT int-blast (QF_NIA UNSAT blind spot).
    // -----------------------------------------------------------------------

    /// `x*x = 2 ∧ 0 ≤ x ≤ 5`: no integer in `[0,5]` squares to 2, so the bounded
    /// box is finite and the exact blast must REFUTE it (the width ladder alone
    /// only ever says `Unknown` for `x*x = 2`).
    #[test]
    fn bounded_nonlinear_square_no_root_is_unsat() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let sq = arena.int_mul(xv, xv).unwrap();
        let two = arena.int_const(2);
        let zero = arena.int_const(0);
        let five = arena.int_const(5);
        let eq = arena.eq(sq, two).unwrap();
        let lo = arena.int_ge(xv, zero).unwrap();
        let hi = arena.int_le(xv, five).unwrap();
        let result = check_auto(&mut arena, &[eq, lo, hi], &SolverConfig::default()).unwrap();
        assert!(
            matches!(result, CheckResult::Unsat),
            "bounded x*x=2 must be unsat, got {result:?}"
        );
    }

    #[test]
    fn int_mod_by_zero_underspecification_is_not_refuted() {
        // SMT-LIB leaves `mod` by zero underspecified. This formula is satisfiable:
        // choose i7 = 0, so both modulo terms denote `mod(0, 0)`, then choose that
        // total-function value above 775. The in-tree evaluator convention
        // `mod 0 0 = 0` must therefore never be used as an UNSAT proof.
        let mut arena = TermArena::new();
        let i7 = arena.declare("i7", Sort::Int).unwrap();
        let i7v = arena.var(i7);
        let zero = arena.int_const(0);
        let five = arena.int_const(5);
        let forty_six = arena.int_const(46);
        let seven_seventy_five = arena.int_const(775);
        let i7_mod_5 = arena.int_mod(i7v, five).unwrap();
        let mod_0_i7_mod_5 = arena.int_mod(zero, i7_mod_5).unwrap();
        let le = arena.int_le(mod_0_i7_mod_5, forty_six).unwrap();
        let not_le = arena.not(le).unwrap();
        let mod_0_0 = arena.int_mod(zero, zero).unwrap();
        let gt = arena.int_lt(seven_seventy_five, mod_0_0).unwrap();

        let result = check_auto(&mut arena, &[not_le, gt], &SolverConfig::default());
        assert!(
            !matches!(result, Ok(CheckResult::Unsat)),
            "SMT-LIB underspecified mod-by-zero formula must not be refuted, got {result:?}"
        );
    }

    #[test]
    fn int_mod_by_nonzero_constant_can_still_be_refuted() {
        let mut arena = TermArena::new();
        let five = arena.int_const(5);
        let two = arena.int_const(2);
        let zero = arena.int_const(0);
        let modulo = arena.int_mod(five, two).unwrap();
        let false_assertion = arena.eq(modulo, zero).unwrap();

        let result = check_auto(&mut arena, &[false_assertion], &SolverConfig::default());
        assert!(
            matches!(result, Ok(CheckResult::Unsat)),
            "nonzero constant divisor has fixed SMT-LIB semantics and remains refutable, got {result:?}"
        );
    }

    /// `x*y = 7 ∧ 2 ≤ x,y ≤ 3`: products in range are 4,6,9, never 7 ⇒ unsat.
    #[test]
    fn bounded_product_no_factorization_is_unsat() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let prod = arena.int_mul(xv, yv).unwrap();
        let seven = arena.int_const(7);
        let two = arena.int_const(2);
        let three = arena.int_const(3);
        let eq = arena.eq(prod, seven).unwrap();
        let xlo = arena.int_ge(xv, two).unwrap();
        let xhi = arena.int_le(xv, three).unwrap();
        let ylo = arena.int_ge(yv, two).unwrap();
        let yhi = arena.int_le(yv, three).unwrap();
        let result = check_auto(
            &mut arena,
            &[eq, xlo, xhi, ylo, yhi],
            &SolverConfig::default(),
        )
        .unwrap();
        assert!(
            matches!(result, CheckResult::Unsat),
            "bounded x*y=7 (2..3) must be unsat, got {result:?}"
        );
    }

    /// `x*y = 6 ∧ 1 ≤ x,y ≤ 6`: a genuine bounded SAT (e.g. 2·3) ⇒ a replayed
    /// model. Confirms the path's `Sat` is real (replay-checked), not just unsat.
    #[test]
    fn bounded_product_with_factorization_is_sat() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let prod = arena.int_mul(xv, yv).unwrap();
        let six = arena.int_const(6);
        let one = arena.int_const(1);
        let eq = arena.eq(prod, six).unwrap();
        let xlo = arena.int_ge(xv, one).unwrap();
        let xhi = arena.int_le(xv, six).unwrap();
        let ylo = arena.int_ge(yv, one).unwrap();
        let yhi = arena.int_le(yv, six).unwrap();
        let asserts = [eq, xlo, xhi, ylo, yhi];
        let result = check_auto(&mut arena, &asserts, &SolverConfig::default()).unwrap();
        let CheckResult::Sat(model) = result else {
            panic!("bounded x*y=6 must be sat, got {result:?}");
        };
        // The model must replay against EVERY original assertion exactly.
        let assignment = model.to_assignment();
        for &a in &asserts {
            assert_eq!(
                eval(&arena, a, &assignment).unwrap(),
                Value::Bool(true),
                "sat model must satisfy every original assertion"
            );
        }
    }

    /// SOUNDNESS GUARD: an UNBOUNDED nonlinear integer query (`x² = 2y² ∧ x,y ≥
    /// 1`, no upper bound on either variable) must NOT be falsely refuted. The
    /// bound-detection cannot prove a finite box (no upper bound), so the exact
    /// path DECLINES — the query stays `Unknown`, never a wrong `Unsat`.
    #[test]
    fn unbounded_nonlinear_is_not_falsely_refuted() {
        let mut arena = TermArena::new();
        let xs = arena.declare("x", Sort::Int).unwrap();
        let ys = arena.declare("y", Sort::Int).unwrap();
        let (xv, yv) = (arena.var(xs), arena.var(ys));
        let xsq = arena.int_mul(xv, xv).unwrap();
        let ysq = arena.int_mul(yv, yv).unwrap();
        let two = arena.int_const(2);
        let two_ysq = arena.int_mul(two, ysq).unwrap();
        let eq = arena.eq(xsq, two_ysq).unwrap();
        let one = arena.int_const(1);
        let xlo = arena.int_ge(xv, one).unwrap();
        let ylo = arena.int_ge(yv, one).unwrap();
        // Tight timeout so even if some other engine grinds, it returns Unknown,
        // not a wrong verdict; the point is NEVER `Unsat` from THIS path.
        let config = SolverConfig {
            timeout: Some(std::time::Duration::from_secs(5)),
            ..Default::default()
        };
        let result = check_auto(&mut arena, &[eq, xlo, ylo], &config).unwrap();
        assert!(
            !matches!(result, CheckResult::Unsat),
            "unbounded x²=2y² (x,y≥1) must NOT be falsely refuted, got {result:?}"
        );
    }

    /// The bounded EXACT blast must DECIDE the `no-square-mod` shape that pins the
    /// `nia_unsat` frontier: `x² = m·t + r ∧ 0 ≤ x < N·m ∧ t ≥ 0`, with `t`'s
    /// upper bound DERIVED from `x`'s via the equality. `r=2` is a non-residue
    /// mod 3, so the system is unsat.
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn no_square_mod_with_derived_t_bound_is_unsat() {
        let (m, r, n) = (3i128, 2i128, 2i128);
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let t = arena.declare("t", Sort::Int).unwrap();
        let (xv, tv) = (arena.var(x), arena.var(t));
        // x*x = m*t + r
        let xsq = arena.int_mul(xv, xv).unwrap();
        let m_c = arena.int_const(m);
        let mt = arena.int_mul(m_c, tv).unwrap();
        let r_c = arena.int_const(r);
        let rhs = arena.int_add(mt, r_c).unwrap();
        let eq = arena.eq(xsq, rhs).unwrap();
        // 0 <= x < N*m
        let zero = arena.int_const(0);
        let upper = arena.int_const(n * m);
        let xlo = arena.int_ge(xv, zero).unwrap();
        let xhi = arena.int_lt(xv, upper).unwrap();
        // t >= 0
        let tlo = arena.int_ge(tv, zero).unwrap();
        let result =
            check_auto(&mut arena, &[eq, xlo, xhi, tlo], &SolverConfig::default()).unwrap();
        assert!(
            matches!(result, CheckResult::Unsat),
            "no-square-mod (derived t bound) must be unsat, got {result:?}"
        );
    }

    /// Verdict-invariance smoke: a bounded LINEAR query the LIA engines already
    /// decide unsat is unchanged (the new branch runs only in the nonlinear tail,
    /// after the LIA refuters short-circuit).
    #[test]
    fn linear_unsat_unchanged() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        // x > 0 ∧ x < 1  ⇒ unsat (no integer strictly between 0 and 1).
        let gt = arena.int_gt(xv, zero).unwrap();
        let lt = arena.int_lt(xv, one).unwrap();
        let result = check_auto(&mut arena, &[gt, lt], &SolverConfig::default()).unwrap();
        assert!(
            matches!(result, CheckResult::Unsat),
            "bounded linear x>0 ∧ x<1 must be unsat, got {result:?}"
        );
    }

    #[test]
    fn disjunctive_branch_sat_model_replays_original_query() {
        let mut arena = TermArena::new();
        let p = arena.bool_var("disjunct_replay_p").unwrap();
        let q = arena.bool_var("disjunct_replay_q").unwrap();
        let disjunction = arena.or(p, q).unwrap();
        let assertions = [disjunction];
        let config = SolverConfig::default().with_timeout(Duration::from_secs(1));

        let Some(CheckResult::Sat(model)) =
            try_disjunct_refutation(&mut arena, &assertions, &config).unwrap()
        else {
            panic!("a satisfiable disjunctive branch should produce a replayed model");
        };
        assert!(crate::check_model(&arena, &assertions, &model).unwrap());
    }

    // -----------------------------------------------------------------------
    // Disjunctive finite-value-set bounds (case-split QF_NIA).
    // -----------------------------------------------------------------------

    /// Builds a left-associative `(or (= x c0) (= x c1) …)` over a single `Int`
    /// variable, mirroring the SMT-LIB n-ary `or` lowering.
    fn or_var_eq_consts(arena: &mut TermArena, xv: TermId, cs: &[i128]) -> TermId {
        let mut iter = cs.iter();
        let first = *iter.next().expect("nonempty value set");
        let fc = arena.int_const(first);
        let mut acc = arena.eq(xv, fc).unwrap();
        for &c in iter {
            let cc = arena.int_const(c);
            let eq = arena.eq(xv, cc).unwrap();
            acc = arena.or(acc, eq).unwrap();
        }
        acc
    }

    /// `(or (= x 5) (= x 7) (= x 9)) ∧ x*x = 50`: none of 25/49/81 equals 50, so
    /// the finite value set `{5,7,9}` is bounded to `[5,9]` and the exact blast
    /// must REFUTE it (the width ladder alone only says `Unknown` for `x*x=50`).
    #[test]
    fn disjunctive_value_set_square_no_root_is_unsat() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let disj = or_var_eq_consts(&mut arena, xv, &[5, 7, 9]);
        let sq = arena.int_mul(xv, xv).unwrap();
        let fifty = arena.int_const(50);
        let eq = arena.eq(sq, fifty).unwrap();
        let result = check_auto(&mut arena, &[disj, eq], &SolverConfig::default()).unwrap();
        assert!(
            matches!(result, CheckResult::Unsat),
            "disjunctive value-set x∈{{5,7,9}} ∧ x*x=50 must be unsat, got {result:?}"
        );
    }

    /// `(or (= x 2) (= x 3)) ∧ x*x = 9`: `x=3` works, so this is a genuine bounded
    /// SAT — and the model must replay against EVERY original assertion exactly.
    #[test]
    fn disjunctive_value_set_with_solution_is_sat() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let disj = or_var_eq_consts(&mut arena, xv, &[2, 3]);
        let sq = arena.int_mul(xv, xv).unwrap();
        let nine = arena.int_const(9);
        let eq = arena.eq(sq, nine).unwrap();
        let asserts = [disj, eq];
        let result = check_auto(&mut arena, &asserts, &SolverConfig::default()).unwrap();
        let CheckResult::Sat(model) = result else {
            panic!("disjunctive value-set x∈{{2,3}} ∧ x*x=9 must be sat, got {result:?}");
        };
        let assignment = model.to_assignment();
        for &a in &asserts {
            assert_eq!(
                eval(&arena, a, &assignment).unwrap(),
                Value::Bool(true),
                "sat model must satisfy every original assertion"
            );
        }
    }

    /// SOUNDNESS GUARD: a MIXED disjunction `(or (= x 1) (= y 2))` bounds NEITHER
    /// variable (the disjunction does not pin a single variable to a finite set).
    /// With `x*y` otherwise unbounded, the box cannot be proven, the exact path
    /// DECLINES, and the query must NOT be falsely refuted.
    #[test]
    fn mixed_disjunction_does_not_falsely_bound() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let ex = arena.eq(xv, one).unwrap();
        let ey = arena.eq(yv, two).unwrap();
        let disj = arena.or(ex, ey).unwrap();
        // x*y = 7 — with x,y otherwise unbounded, no finite box exists.
        let prod = arena.int_mul(xv, yv).unwrap();
        let seven = arena.int_const(7);
        let eq = arena.eq(prod, seven).unwrap();
        let config = SolverConfig {
            timeout: Some(std::time::Duration::from_secs(5)),
            ..Default::default()
        };
        let result = check_auto(&mut arena, &[disj, eq], &config).unwrap();
        assert!(
            !matches!(result, CheckResult::Unsat),
            "mixed disjunction (= x 1)∨(= y 2) must NOT bound either var; got {result:?}"
        );
    }

    /// SOUNDNESS GUARD: a finite-value-set disjunction nested under `not` is NOT a
    /// top-level conjunct, so it bounds nothing. `(not (or (= x 5) (= x 7)))` says
    /// `x ∉ {5,7}` — emphatically NOT `x ∈ [5,7]`. With `x` otherwise unbounded
    /// the exact path declines; the query must not be falsely refuted.
    #[test]
    fn negated_disjunction_does_not_falsely_bound() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let disj = or_var_eq_consts(&mut arena, xv, &[5, 7]);
        let neg = arena.not(disj).unwrap();
        // x*x = 49 has the witness x = -7 (which `x ∉ {5,7}` admits), so the query is
        // genuinely SAT — the point is NEVER a wrong unsat from treating the negated
        // set as a `[5,7]` bound (that bug would force x ∈ {5,6,7}, excluding −7 ⇒ a
        // FALSE unsat). (The old value 50 is genuinely unsat over Int — no integer
        // root — and is now correctly decided so by the conjunct-split refutation, so
        // it no longer isolates the false-bound bug; 49 does.)
        let sq = arena.int_mul(xv, xv).unwrap();
        let target = arena.int_const(49);
        let eq = arena.eq(sq, target).unwrap();
        let config = SolverConfig {
            timeout: Some(std::time::Duration::from_secs(5)),
            ..Default::default()
        };
        let result = check_auto(&mut arena, &[neg, eq], &config).unwrap();
        assert!(
            !matches!(result, CheckResult::Unsat),
            "negated value-set must NOT bound x to [5,7]; got {result:?}"
        );
    }

    /// A finite value set composes with `derive_var_bound`: `(or (= x 2) (= x 4))`
    /// bounds `x` to `[2,4]`, and `x + t = 10` then DERIVES `t ∈ [6,8]`, so the
    /// whole system is bounded. `x*x = t` has no solution (4≠6/7/8, 16≠.., and the
    /// only consistent pairs are (2,8),(4,6) with 4≠8, 16≠6) ⇒ unsat, now decided.
    #[test]
    fn disjunctive_value_set_composes_with_derived_bound() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let t = arena.declare("t", Sort::Int).unwrap();
        let (xv, tv) = (arena.var(x), arena.var(t));
        let disj = or_var_eq_consts(&mut arena, xv, &[2, 4]);
        // x + t = 10  ⇒  t = 10 - x ∈ [6, 8].
        let sum = arena.int_add(xv, tv).unwrap();
        let ten = arena.int_const(10);
        let lin = arena.eq(sum, ten).unwrap();
        // x*x = t : (x,t) constrained to {(2,8),(4,6)}; 2*2=4≠8, 4*4=16≠6 ⇒ unsat.
        let sq = arena.int_mul(xv, xv).unwrap();
        let eqt = arena.eq(sq, tv).unwrap();
        let result = check_auto(&mut arena, &[disj, lin, eqt], &SolverConfig::default()).unwrap();
        assert!(
            matches!(result, CheckResult::Unsat),
            "value-set x∈{{2,4}} + derived t bound, x*x=t must be unsat, got {result:?}"
        );
    }

    // ---- slice 5: `iand` bounded blast — bv2nat interval + linear bound prop ----

    #[test]
    fn interval_of_bv2nat_is_structural_zero_to_two_pow_w() {
        // `bv2nat(bvand(int2bv 4 x, int2bv 4 y))` — the `iand 4` bridge — has the
        // structural interval `[0, 15]`, independent of x,y's (here unbounded) values.
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let y = arena.int_var("y").unwrap();
        let xb = arena.int2bv(4, x).unwrap();
        let yb = arena.int2bv(4, y).unwrap();
        let anded = arena.bv_and(xb, yb).unwrap();
        let n = arena.bv2nat(anded).unwrap();
        let bounds = BTreeMap::new(); // x,y intentionally UNbounded
        let iv = interval_of(&arena, n, &bounds, 0).expect("bv2nat interval");
        assert_eq!((iv.lo, iv.hi), (0, 15));
    }

    #[test]
    fn propagate_linear_bounds_derives_upper_from_sum_constraint() {
        // `x + y ≤ 32 ∧ y ≥ 0`  ⇒  `x ≤ 32` (needs only y's LOWER bound).
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let sum = arena.int_add(xv, yv).unwrap();
        let c32 = arena.int_const(32);
        let le = arena.int_le(sum, c32).unwrap();
        let conjuncts = vec![le];
        let mut lo = HashMap::new();
        let mut hi = HashMap::new();
        lo.insert(x, 0);
        lo.insert(y, 0); // x ≥ 0, y ≥ 0
        propagate_linear_bounds(&arena, &conjuncts, &mut lo, &mut hi);
        assert_eq!(hi.get(&x).copied(), Some(32), "x ≤ 32 from x+y≤32, y≥0");
        assert_eq!(hi.get(&y).copied(), Some(32), "y ≤ 32 symmetric");
    }

    #[test]
    fn propagate_linear_bounds_negative_coeff_sign_is_correct() {
        // `2y − x ≤ 4 ∧ 0 ≤ y ≤ 10`. Isolate x (coeff −1 < 0 ⇒ LOWER bound on x):
        //   −x ≤ 4 − 2y  ⇒  x ≥ 2y − 4  ⇒  x ≥ 2·y_lo − 4 = −4.
        // And isolate y (coeff +2): 2y ≤ 4 + x, needs x's lower bound (absent) ⇒ no
        // y tightening here; we only assert the x lower bound sign is right.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let two = arena.int_const(2);
        let two_y = arena.int_mul(two, yv).unwrap();
        let lhs = arena.int_sub(two_y, xv).unwrap(); // 2y - x
        let four = arena.int_const(4);
        let le = arena.int_le(lhs, four).unwrap();
        let mut lo = HashMap::new();
        let mut hi = HashMap::new();
        lo.insert(y, 0);
        hi.insert(y, 10);
        propagate_linear_bounds(&arena, &[le], &mut lo, &mut hi);
        assert_eq!(
            lo.get(&x).copied(),
            Some(-4),
            "x ≥ 2·y_lo − 4 = −4 (negative-coeff isolation gives a LOWER bound)"
        );
    }

    #[test]
    fn prove_int_box_covers_iand_sum_bounded_query() {
        // The `granularities` skeleton: x,y ≥ 0, x+y ≤ 4, and an iand term. The box
        // proof must now succeed (bv2nat interval + derived upper bounds) where it
        // formerly declined.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let zero = arena.int_const(0);
        let gx = arena.int_ge(xv, zero).unwrap();
        let gy = arena.int_ge(yv, zero).unwrap();
        let sum = arena.int_add(xv, yv).unwrap();
        let four = arena.int_const(4);
        let sle = arena.int_le(sum, four).unwrap();
        let xb = arena.int2bv(4, xv).unwrap();
        let yb = arena.int2bv(4, yv).unwrap();
        let anded = arena.bv_and(xb, yb).unwrap();
        let iand = arena.bv2nat(anded).unwrap();
        let one = arena.int_const(1);
        let ge_iand = arena.int_ge(iand, one).unwrap(); // iand(x,y) ≥ 1
        match prove_int_box(&arena, &[gx, gy, sle, ge_iand]) {
            IntBoxProof::Box(b) => {
                assert_eq!(b.bounds.get(&x).map(|iv| (iv.lo, iv.hi)), Some((0, 4)));
                assert_eq!(b.bounds.get(&y).map(|iv| (iv.lo, iv.hi)), Some((0, 4)));
            }
            IntBoxProof::TriviallyUnsat => {
                panic!("expected a proven finite box, got TriviallyUnsat")
            }
            IntBoxProof::Decline => panic!("expected a proven finite box, got Decline"),
        }
    }
}
