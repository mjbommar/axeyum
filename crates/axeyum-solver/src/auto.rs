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
    ArraySortKey, Assignment, FuncId, Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode,
    Value, eval,
};
use axeyum_rewrite::{
    DEFAULT_SOLVE_EQS_FUEL, ModelReconstructionTrail, QuantExpandError, build_app,
    canonicalize_terms, elim_unconstrained, expand_quantifiers, instantiate_universals,
    instantiate_with_triggers, propagate_values, replace_subterms, solve_eqs_bounded,
};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::cas_poly::CasOutcome;
use crate::combined::check_with_all_theories;
use crate::dpll_lia::{check_with_arith_dpll, check_with_lia_dpll};
use crate::lia::DEFAULT_INT_WIDTH;
use crate::lra::{check_with_lia_simplex_within, check_with_lra};
use crate::model::Model;
use crate::qinst_egraph::prove_quantified_unsat_via_egraph;
use crate::quant_guarded_int::{expand_guarded_int_universals, skolemize_positive_existentials};
use crate::route_trace;
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
    is_quantified: bool,
) -> Result<Option<CheckResult>, SolverError> {
    if !is_quantified {
        return Ok(None);
    }
    if canonicalization_discharges_quantifiers(arena, assertions, config)? {
        return Ok(Some(CheckResult::Unsat));
    }
    if let Some(result) =
        crate::quant_guard_vacuity_search::decide_quantified_guard_vacuity_sat(arena, assertions)
    {
        return Ok(Some(result));
    }
    if let Some(result) =
        crate::quant_bv_model_sat_search::decide_quantified_bv_model_sat(arena, assertions, config)?
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
        || crate::quant_vacuous_exists_counterexample_search::find_vacuous_exists_universal_counterexample(
            arena, assertions, config,
        )?
        .is_some()
        || crate::quant_bv_paired_exists_search::find_bv_paired_existential_transfer(
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

/// Whether denotation-preserving canonicalization alone discharges every
/// quantifier in the query **and** refutes what is left.
///
/// The word-level preprocessing pipeline is skipped on quantified queries
/// (`solve_eqs`/`elim_unconstrained` treat the assertion list as ground, and the
/// trigger/e-matching routes need the original structure). Canonicalization is
/// the one member of that pipeline that is *structurally* quantifier-aware: it
/// rebuilds `forall`/`exists` nodes with the same binder around a rewritten body
/// and never substitutes a symbol, so it cannot capture. Running it here recovers
/// the family of queries that are propositional tautologies **over** quantified
/// atoms — the quantifier-duality identities `not (forall x. P) = exists x. not
/// P` among them — which no instantiation heuristic can reach because there is
/// nothing to instantiate.
///
/// Two deliberate restrictions keep this from disturbing anything else:
///
/// * The canonicalized form is adopted **only when it is quantifier-free**. A
///   partial simplification is discarded, so every query the existing quantifier
///   portfolio handles reaches it byte-identical.
/// * Only `unsat` is propagated. Canonicalization is denotation-preserving, so
///   `sat` would transfer too, but a folded query can drop symbols the original
///   model must still bind; rather than grow a reconstruction trail for a probe,
///   a non-`unsat` outcome simply falls through to the ordinary quantified path.
///   The result is a refutation-side-only addition: it can turn `unknown` into
///   `unsat` and can turn nothing into anything else.
fn canonicalization_discharges_quantifiers(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    if !config.preprocess {
        return Ok(false);
    }
    // A canonicalization failure is not an error here: this is a probe, and
    // declining leaves the ordinary quantified path in charge.
    let Ok(canonical) = canonicalize_terms(arena, assertions) else {
        return Ok(false);
    };
    let canonical = canonical.terms;
    if has_quantifier(arena, &canonical) {
        return Ok(false);
    }
    Ok(matches!(
        check_auto(arena, &canonical, config)?,
        CheckResult::Unsat
    ))
}

/// Tries a strict quantifier-free subset of a quantified conjunction before the
/// more expensive quantifier portfolio. If the unconditional ground conjuncts
/// are already inconsistent, that refutes the complete query; every other
/// outcome is ignored. The probe receives only one tenth of a finite query
/// budget, so it cannot starve the quantified routes it is meant to precede.
// dispatch-family fn: keeps `Result` for uniformity with sibling routes, and the
// const-after-statements placement is intentional (co-located with its use).
#[allow(clippy::unnecessary_wraps, clippy::items_after_statements)]
fn ground_subset_refutes_quantified_query(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    let Some(total) = config.timeout else {
        return Ok(false);
    };
    let probe_budget = total / 10;
    if probe_budget.is_zero() {
        return Ok(false);
    }

    let probe_deadline = Instant::now().checked_add(probe_budget);
    let mut conjuncts = Vec::new();
    for &assertion in assertions {
        collect_top_conjuncts(arena, assertion, &mut conjuncts);
    }
    let mut ground = Vec::new();
    let mut quantified_conjuncts = 0usize;
    for conjunct in conjuncts {
        match contains_quantifier_within(arena, &[conjunct], probe_deadline) {
            Some(true) => quantified_conjuncts += 1,
            Some(false) => ground.push(conjunct),
            None => return Ok(false),
        }
    }
    // On small quantified conjunctions the established portfolio is cheap and
    // can already finish close to its deadline. Reserve this probe for large
    // axiom sets, where repeatedly scanning all quantified conjuncts dominates
    // and a strict ground core is a materially smaller problem.
    const MIN_QUANTIFIED_CONJUNCTS: usize = 32;
    if quantified_conjuncts < MIN_QUANTIFIED_CONJUNCTS || ground.is_empty() {
        return Ok(false);
    }

    let Some(probe) = config_with_remaining_timeout(config, probe_deadline) else {
        return Ok(false);
    };
    match check_auto(arena, &ground, &probe) {
        Ok(CheckResult::Unsat) => Ok(true),
        Ok(CheckResult::Sat(_) | CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {
            Ok(false)
        }
        // This is an optional accelerator. It must never turn a query the
        // established portfolio can handle into an operational error.
        Err(_) => Ok(false),
    }
}

/// Clones a query configuration with only the wall-clock time remaining before
/// `deadline`. `None` means the shared query budget has already expired.
pub(crate) fn config_with_remaining_timeout(
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Option<SolverConfig> {
    let mut remaining = config.clone();
    if let Some(deadline) = deadline {
        let duration = deadline.checked_duration_since(Instant::now())?;
        if duration.is_zero() {
            return None;
        }
        remaining.timeout = Some(duration);
    }
    Some(remaining)
}

/// Env-gated stage tracing for the quantified portfolio (`AXEYUM_QTRACE=1`):
/// prints each dispatch stage with its wall-clock cost to stderr. Diagnostic
/// only — never alters routing, budgets, or verdicts. The flag is read once,
/// so disabled tracing costs a single cached load per call site.
pub(crate) fn qtrace(stage: &str, since: Instant, note: &str) {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *ENABLED.get_or_init(|| std::env::var_os("AXEYUM_QTRACE").is_some()) {
        eprintln!(
            "[qtrace] {stage} +{:.3}s {note}",
            since.elapsed().as_secs_f64()
        );
    }
}

fn quantified_timeout(stage: &str) -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::ResourceLimit,
        detail: format!("quantified solve time budget exhausted after {stage}"),
    })
}

/// Retains an already-classified finite-expansion `unknown` so narrower
/// quantified fallbacks cannot replace it with an operational shape error.
/// A genuinely unsupported finite front door remains an error unless a later
/// route decides the query.
fn retained_finite_unknown(result: Result<CheckResult, SolverError>) -> Option<CheckResult> {
    match result {
        Ok(result @ CheckResult::Unknown(_)) => Some(result),
        Err(SolverError::Unsupported(_)) => None,
        _ => unreachable!("finite-result pattern admits only unknown or unsupported"),
    }
}

fn run_egraph_quantified_fallback(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
    finite_unknown: Option<CheckResult>,
    started: Instant,
) -> Result<Option<CheckResult>, SolverError> {
    let Some(egraph_config) = config_with_remaining_timeout(config, deadline) else {
        return Ok(Some(quantified_timeout("finite quantifier expansion")));
    };
    match prove_quantified_unsat_via_egraph(arena, assertions, &egraph_config) {
        Ok(CheckResult::Unsat) => {
            qtrace("egraph", started, "unsat");
            Ok(Some(CheckResult::Unsat))
        }
        Ok(CheckResult::Sat(_) | CheckResult::Unknown(_)) => {
            qtrace("egraph", started, "declined");
            Ok(None)
        }
        Err(error @ SolverError::Unsupported(_)) => {
            if mbqi_source_shape_supported(arena, assertions) {
                qtrace("egraph", started, "unsupported->mbqi");
                Ok(None)
            } else if let Some(result) = finite_unknown {
                qtrace("egraph", started, "unsupported->finite-unknown");
                Ok(Some(result))
            } else {
                Err(error)
            }
        }
        Err(error) => Err(error),
    }
}

fn finish_quantified_solve(
    arena: &mut TermArena,
    assertions: &[TermId],
    original_assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    let t0 = Instant::now();
    let Some(witness_config) = config_with_remaining_timeout(config, deadline) else {
        return Ok(quantified_timeout("quantifier normalization"));
    };
    if let Some(result) = crate::quant_exists_witness::decide_forall_exists_by_witness(
        arena,
        assertions,
        &witness_config,
    )? {
        qtrace("forall-exists-witness", t0, "decided");
        return Ok(result);
    }
    qtrace("forall-exists-witness", t0, "declined");

    let Some(finite_config) = config_with_remaining_timeout(config, deadline) else {
        return Ok(quantified_timeout("forall-exists witness search"));
    };
    match check_with_quantifiers(arena, assertions, &finite_config) {
        finite_result @ (Ok(CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_))) => {
            let finite_unknown = retained_finite_unknown(finite_result);
            qtrace("finite-expansion", t0, "declined");
            // Pure-UF finite model finding, probed BEFORE the refutation
            // family on half the remaining budget (the `probe_budget`
            // pattern): the refutation loops below reliably consume their
            // entire budget on satisfiable pure-UF queries, so a post-only
            // placement would starve. The finder applies only to the pure-UF
            // fragment (everything else declines in one cheap scan), returns
            // only an independently certified model, and is re-gated by the
            // standard `check_model` — it can only turn an eventual `unknown`
            // into a checked `sat`, never `unsat`. The certificates bind to
            // the ORIGINAL assertions, which is why it runs on those. The
            // probe-sized instance cap keeps this call from ever building a
            // ground round big enough to starve the refutation family below
            // (a measured failure mode: a 3 s ground refutation of a large
            // declared-unsat file became a wall-clock kill when the probe
            // was allowed full-sized rounds).
            // The finder runs on a THROWAWAY CLONE of the arena: its bounded
            // expansions intern thousands of encoding symbols and selector
            // terms, and letting those leak into the shared arena measurably
            // derailed the e-graph refutation downstream (a 3 s ground
            // refutation of a large declared-unsat file became `unknown`
            // with the polluted arena, and refuted again the moment the
            // probe was skipped). Term/symbol IDs coincide between the clone
            // and the original, so the returned model and its certificates
            // bind to the original assertions, and `check_model` re-gates
            // against the ORIGINAL arena.
            if let Some(probe_config) = config_with_remaining_timeout(config, deadline)
                && let Some(model) = crate::uf_fmf::find_uf_finite_model(
                    &mut arena.clone(),
                    original_assertions,
                    &probe_budget(&probe_config),
                    crate::uf_fmf::UF_FMF_PROBE_SOLVE_ASSERTIONS,
                )?
                && crate::check_model(arena, original_assertions, &model)?
            {
                qtrace("uf-fmf-probe", t0, "sat");
                return Ok(CheckResult::Sat(model));
            }
            qtrace("uf-fmf-probe", t0, "declined");
            // Effort ladder (budget-monotone dispatch, after cvc5's
            // QuantifiersEngine effort passes): the model-based refuter is a
            // few *milliseconds* when its first ground candidate already
            // violates a universal, while the e-graph instantiation loop
            // reliably consumes every second it is given. Handing the e-graph
            // the full remaining budget therefore made mid-range budgets
            // strictly worse than small ones (measured: the same UF file is
            // `unsat` in 0.5 s at a 500 ms budget and `unsat` at 24 s, but
            // `unknown` at 2/5/10 s — the e-graph ate the whole window,
            // whether the 13 ms MBQI refutation ever ran depended on the
            // e-graph's own round-forecast quirks, and at 2-10 s it never did).
            // The fix is a bounded **first-refusal MBQI rung on 1/8 of the
            // remaining budget** before the e-graph pass. The e-graph then
            // keeps its established full-remaining-budget slice, so every
            // verdict it finds today it still finds; the quick rung only
            // spends a bounded fraction. The slice is a *fraction of the
            // remaining budget*, so a larger total budget gives the rung at
            // least as much time — a verdict found at budget B is not lost at
            // B' > B by rung starvation.
            if let Some(result) =
                mbqi_first_refusal(arena, assertions, original_assertions, config, deadline)?
            {
                return Ok(result);
            }
            if let Some(result) = run_egraph_quantified_fallback(
                arena,
                assertions,
                config,
                deadline,
                finite_unknown,
                t0,
            )? {
                return Ok(result);
            }
            let Some(mbqi_config) = config_with_remaining_timeout(config, deadline) else {
                return Ok(quantified_timeout("e-matching"));
            };
            let mbqi_result = prove_unsat_by_mbqi(arena, assertions, &mbqi_config)?;
            qtrace("mbqi", t0, "returned");
            match mbqi_result {
                CheckResult::Sat(model)
                    if crate::check_model(arena, original_assertions, &model)? =>
                {
                    Ok(CheckResult::Sat(model))
                }
                CheckResult::Sat(_) => Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail:
                        "MBQI candidate lacks a checked model for the original assertion sequence"
                            .to_owned(),
                })),
                other => {
                    // Pure-UF finite model finding, the SAT-side complement of
                    // the refutation family above. Every route so far —
                    // finite expansion, the e-graph refuter, MBQI, and its
                    // terminal E-matching/instantiation fallbacks (including
                    // the "instantiation is satisfiable" decline) — has ended
                    // in `unknown`. The finder runs on the ORIGINAL
                    // assertions (so its closure axioms see every free
                    // symbol, and its certificates bind to the exact source
                    // terms), returns only an independently certified model
                    // or nothing, and the standard `check_model` gate
                    // re-validates before the verdict is emitted. It can only
                    // turn this `unknown` into a checked `sat` — never
                    // `unsat`, never an unchecked model.
                    // Same throwaway-clone isolation as the probe above: the
                    // arena outlives this solve, so the caller's next queries
                    // must not inherit the expansion junk either.
                    if matches!(other, CheckResult::Unknown(_))
                        && let Some(fmf_config) = config_with_remaining_timeout(config, deadline)
                        && let Some(model) = crate::uf_fmf::find_uf_finite_model(
                            &mut arena.clone(),
                            original_assertions,
                            &fmf_config,
                            crate::uf_fmf::UF_FMF_FULL_SOLVE_ASSERTIONS,
                        )?
                        && crate::check_model(arena, original_assertions, &model)?
                    {
                        qtrace("uf-fmf-full", t0, "sat");
                        return Ok(CheckResult::Sat(model));
                    }
                    qtrace("uf-fmf-full", t0, "declined");
                    Ok(other)
                }
            }
        }
        other => {
            qtrace("finite-expansion", t0, "decided");
            other
        }
    }
}

/// `memory_limit_mb` at a front door, or `None` when it is not set or not
/// exceeded.
///
/// `SatBvBackend` probes its own three phase boundaries, but these front doors
/// reach routes that never bit-blast (simplex, strings, e-matching, the
/// quantified ladder), and those would otherwise ignore the field entirely. One
/// probe (~9.4 us) bounds every one of them to "did not arrive already over".
///
/// What happens *inside* a rung is **not** bounded by this, and
/// [`crate::memory_budget`] says so rather than implying otherwise: a faithful
/// bound needs a global allocator hook, which is an ADR-sized decision.
fn memory_budget_decline(config: &SolverConfig, phase: &str) -> Option<CheckResult> {
    crate::memory_budget::MemoryBudget::from_config(config)
        .and_then(|budget| budget.exceeded(phase))
        .map(CheckResult::Unknown)
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
// The memory-budget probe put this at 103 lines against a 100 limit. It was at
// exactly 100 before, so the honest options were an `allow` or a refactor of a
// front door for three lines' worth of budget; five other functions in this
// module already carry the same `allow`.
#[allow(clippy::too_many_lines)]
pub fn solve(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    if let Some(decline) = memory_budget_decline(config, "solve entry") {
        return Ok(decline);
    }
    // Arms the sampling watchdog for the whole call. The entry probe above only
    // answers "did this query ARRIVE over budget"; the watchdog is what makes
    // the field bind while a route allocates. Nested `solve`/`check_auto` calls
    // see a nonzero install depth and leave the outermost budget alone.
    let _memory_watchdog = crate::memory_budget::MemoryWatchdog::install(config);
    let is_quantified = has_quantifier(arena, assertions);
    if is_quantified && ground_subset_refutes_quantified_query(arena, assertions, config)? {
        return Ok(CheckResult::Unsat);
    }
    if let Some(result) = checked_quantified_fast_path(arena, assertions, config, is_quantified)? {
        return Ok(result);
    }
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return Ok(quantified_timeout("checked fast paths"));
    }
    let original_assertions = assertions.to_vec();

    // Expose the exact counterexample form `not (A => B)` as `A` plus `not B`,
    // and push that negation through a leading quantifier prefix. This turns a
    // theorem-negation benchmark into the ordinary conjunction of source
    // universals and existential counterexample witnesses that the established
    // skolemization/e-matching pipeline handles. The rewrite is logical
    // equivalence; all other assertion shapes remain byte-identical.
    let normalized = normalize_top_level_quantified_counterexamples(arena, assertions)?;

    // Skolemize top-level existential assertions: `∃x. body` is equisatisfiable
    // with `body[x := fresh]` (the solver picks the witness), so this is exact and
    // — unlike finite expansion — decides infinite-domain existentials too.
    let skolemized = skolemize_top_existentials(arena, &normalized)?;
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
        let Some(remaining) = config_with_remaining_timeout(config, deadline) else {
            return Ok(quantified_timeout("existential skolemization"));
        };
        let result = check_auto(arena, assertions, &remaining)?;
        return Ok(certify_skolemized_negated_universals(
            arena,
            &original_assertions,
            result,
            &remaining,
        ));
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
    let Some(valid_config) = config_with_remaining_timeout(config, deadline) else {
        return Ok(quantified_timeout("existential skolemization"));
    };
    let eliminated =
        crate::quant_valid_universal::eliminate_valid_universals(arena, assertions, &valid_config)?;
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        return Ok(quantified_timeout("valid-universal elimination"));
    }
    let assertions: &[TermId] = &eliminated.0;
    // If every universal was eliminated, the residual is quantifier-free and the
    // ordinary QF dispatch decides it directly.
    if eliminated.1 && !has_quantifier(arena, assertions) {
        let Some(remaining) = config_with_remaining_timeout(config, deadline) else {
            return Ok(quantified_timeout("valid-universal elimination"));
        };
        return check_auto(arena, assertions, &remaining);
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
        let Some(remaining) = config_with_remaining_timeout(config, deadline) else {
            return Ok(quantified_timeout("vacuous-universal elimination"));
        };
        return check_auto(arena, assertions, &remaining);
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
        let Some(remaining) = config_with_remaining_timeout(config, deadline) else {
            return Ok(quantified_timeout("Fourier-Motzkin elimination"));
        };
        return check_auto(arena, fm_assertions, &remaining);
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
    finish_quantified_solve_or_induct(arena, assertions, &original_assertions, config, deadline)
}

/// [`finish_quantified_solve`], then the last rung of the quantified ladder:
/// ℕ-induction over a guarded negated universal
/// ([`crate::nat_induction::prove_by_nat_induction`]).
///
/// Placed last because it is the most expensive thing here that is not a search
/// loop — it discharges two whole sub-queries through [`check_auto`] — and
/// because everything above it decides strictly more shapes. It is also the only
/// route in `solve` that can reach a goal pinned *only* by recursion equations:
/// `f(0) = 0` plus `∀k ≥ 0. f(k+1) = f(k) + 2` does not entail `∀n ≥ 0. f(n) = 2n`
/// by any finite instantiation, so the finite-expansion / e-graph / MBQI family
/// above cannot refute its negation and reports `unknown` — which is exactly the
/// input this rung consumes.
///
/// # Why `original_assertions`
///
/// **Not** the `assertions` the caller has been threading through the pipeline.
/// By this point `normalize_top_level_quantified_counterexamples` has turned
/// every `¬∀n. body` into `∃n. ¬body` and `skolemize_top_existentials` has turned
/// *that* into a ground `¬body[n := !sk_0]`. The negated universal the recogniser
/// matches on no longer exists in `assertions`; handed those, the route finds
/// nothing and declines on every input. The raw assertion sequence still carries
/// the shape, and the route's own soundness argument is stated against it.
///
/// # One direction only
///
/// `Unknown` → `Unsat`, and nothing else. A `sat` or an `unsat` already formed
/// upstream is returned untouched, so no verdict this function sees can change.
/// A backend error from the sub-queries is swallowed rather than propagated: the
/// caller already has a well-formed `unknown`, and losing it to an error raised
/// by a speculative rung would be a regression, not a report.
fn finish_quantified_solve_or_induct(
    arena: &mut TermArena,
    assertions: &[TermId],
    original_assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    let result = finish_quantified_solve(arena, assertions, original_assertions, config, deadline)?;
    if !matches!(result, CheckResult::Unknown(_)) {
        return Ok(result);
    }
    let Some(induction_config) = config_with_remaining_timeout(config, deadline) else {
        return Ok(result);
    };
    let t0 = Instant::now();
    // The route's only verdict is `unsat`, and it is spelled out here rather
    // than passed through, so a future widening of its return type cannot start
    // emitting `sat` from this rung without this line changing too.
    if let Ok(Some(CheckResult::Unsat)) = crate::nat_induction::prove_by_nat_induction(
        arena,
        original_assertions,
        &induction_config,
        check_auto,
    ) {
        qtrace("nat-induction", t0, "unsat");
        return Ok(CheckResult::Unsat);
    }
    qtrace("nat-induction", t0, "declined");
    Ok(result)
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
/// Attaches a checked witness certificate to a `sat` that top-level
/// skolemization decided.
///
/// `∃x. B` is replaced by `B[x := s]` for a fresh constant, which is
/// equisatisfiable and lets the quantifier-free dispatch decide it. The model
/// that comes back interprets `s`, so it *is* the existential witness — but it
/// is a model of the **skolemized** query, and `check_model` replays against the
/// **original**. For a directly negated universal `¬∀x. B` (the normalized form
/// of a counterexample query) that replay has to enumerate `x`'s whole domain,
/// which is fine at 8 or 16 bits and impossible at 32. The verdict and the model
/// were both correct; only the evidence was missing, so a caller could not tell
/// an unverifiable `sat` from a verified one.
///
/// This re-derives the witness through the same checked route the certified
/// search uses, so the returned `sat` carries evidence `check_model` accepts at
/// every width. It is strictly additive: a shape that does not match, or a
/// witness that fails its own check, leaves the result exactly as it was.
fn certify_skolemized_negated_universals(
    arena: &TermArena,
    original_assertions: &[TermId],
    result: CheckResult,
    config: &SolverConfig,
) -> CheckResult {
    let CheckResult::Sat(mut model) = result else {
        return result;
    };
    let assignment = model.to_assignment();
    for &assertion in original_assertions {
        if model
            .quantified_bv_model_sat_certificate(assertion)
            .is_some()
            || crate::quant_bv_model_sat_cert::direct_negated_universal(arena, assertion).is_none()
        {
            continue;
        }
        let Some(free) = crate::quant_bv_model_sat_cert::admitted_free_bv_symbols(arena, assertion)
        else {
            continue;
        };
        let Some(free_values) = free
            .iter()
            .map(|&symbol| assignment.get(symbol).map(|value| (symbol, value)))
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        // The witness search pins exactly these free values, so `all_values` and
        // `free_values` coincide here; the certified search passes a wider
        // candidate assignment.
        // A declined or failed witness search is not a soundness event: the
        // verdict stands on skolemization, which is trusted. Leave the model as
        // it was rather than weakening a correct answer.
        if let Ok(Some(certificate)) =
            crate::quant_bv_model_sat_search::find_negated_universal_witness(
                arena,
                assertion,
                free_values.clone(),
                &free_values,
                config,
            )
        {
            model.set_quantified_bv_model_sat_certificate(certificate);
        }
    }
    CheckResult::Sat(model)
}

/// What a top-level existential elimination did, recorded **without any
/// `TermId` of its own product**.
///
/// A certificate for a refutation of the *skolemized* query has to explain the
/// difference between that query and the caller's, and it cannot do so with
/// ids: the skolemized assertions and the witness terms are created during the
/// producing solve, so their ids name nothing in a checker's arena (which is a
/// fresh parse of the same file, deliberately — see
/// [`crate::quant_instance_set_cert`]). What *is* portable is the shape of the
/// elimination: assertion `i` lost `witnesses[i].len()` existential binders,
/// outermost first. A checker re-runs [`eliminate_top_existentials`] on the
/// caller's assertions, obtains its **own** `assertions` and its **own**
/// witnesses at the same positions, and reads the certificate's positional
/// references against those.
///
/// Freshness — the soundness condition for eliminating `∃` — needs no recording
/// for the same reason: whoever runs this function introduces the witnesses
/// itself, into its own arena, through the unused-name probe below.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SkolemElimination {
    /// The skolemized assertions, positionally parallel to the input.
    pub(crate) assertions: Vec<TermId>,
    /// Witness symbols introduced for each input assertion, outermost binder
    /// first. Empty for an assertion with no top-level existential, which is
    /// the overwhelmingly common case and leaves that assertion untouched.
    pub(crate) witnesses: Vec<Vec<axeyum_ir::SymbolId>>,
}

fn skolemize_top_existentials(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    Ok(eliminate_top_existentials(arena, assertions)?.assertions)
}

/// As `skolemize_top_existentials`, additionally reporting the witness symbols
/// it introduced per assertion — see [`SkolemElimination`].
pub(crate) fn eliminate_top_existentials(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<SkolemElimination, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut out = Vec::with_capacity(assertions.len());
    let mut witnesses = Vec::with_capacity(assertions.len());
    let mut k = 0u32;
    for &a in assertions {
        let mut current = a;
        let mut introduced = Vec::new();
        #[allow(clippy::while_let_loop)] // explicit loop reads clearer with the let-else below
        loop {
            let TermNode::App {
                op: Op::Exists(sym),
                args,
            } = arena.node(current)
            else {
                break;
            };
            let (sym, body) = (*sym, args[0]);
            let sort = arena.symbol(sym).1;
            // `k` restarts on every call while `declare_internal` persists for the
            // life of the arena, so a second call over the same arena would reuse
            // `!sk_3` — hard-erroring when the sorts differ, and silently making
            // two unrelated existentials share one witness when they match. Probe
            // for an unused name instead; this stays deterministic because it
            // depends only on the arena contents and the traversal order. The
            // probe must be `find_internal_symbol` -- `find_symbol` only sees
            // user-declared names, so it is blind to everything declared here.
            let skolem = loop {
                let candidate = format!("!sk_{k}");
                k += 1;
                if arena.find_internal_symbol(&candidate).is_none() {
                    break arena.declare_internal(&candidate, sort).map_err(err)?;
                }
            };
            let bound = arena.var(sym);
            let fresh = arena.var(skolem);
            introduced.push(skolem);
            let mut map: HashMap<TermId, TermId> = HashMap::new();
            map.insert(bound, fresh);
            let mut memo: HashMap<TermId, TermId> = HashMap::new();
            current = replace_subterms(arena, body, &map, &mut memo).map_err(err)?;
        }
        out.push(current);
        witnesses.push(introduced);
    }
    Ok(SkolemElimination {
        assertions: out,
        witnesses,
    })
}

fn normalize_top_level_quantified_counterexamples(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut out = Vec::with_capacity(assertions.len() + 1);
    for &assertion in assertions {
        let implication = match arena.node(assertion) {
            TermNode::App {
                op: Op::BoolNot,
                args,
            } => Some(args[0]),
            _ => None,
        };
        let Some(implication) = implication else {
            out.push(assertion);
            continue;
        };
        let sides = match arena.node(implication) {
            TermNode::App {
                op: Op::BoolImplies,
                args,
            } if args.len() == 2 => Some((args[0], args[1])),
            _ => None,
        };
        let Some((antecedent, consequent)) = sides else {
            if matches!(
                arena.node(implication),
                TermNode::App {
                    op: Op::Forall(_) | Op::Exists(_),
                    ..
                }
            ) {
                out.push(negate_quantifier_prefix(arena, implication).map_err(err)?);
            } else {
                out.push(assertion);
            }
            continue;
        };
        out.push(antecedent);
        out.push(negate_quantifier_prefix(arena, consequent).map_err(err)?);
    }
    Ok(out)
}

fn negate_quantifier_prefix(
    arena: &mut TermArena,
    mut term: TermId,
) -> Result<TermId, axeyum_ir::IrError> {
    let mut prefix = Vec::new();
    loop {
        match arena.node(term) {
            TermNode::App {
                op: Op::Forall(symbol),
                args,
            } => {
                prefix.push((true, *symbol));
                term = args[0];
            }
            TermNode::App {
                op: Op::Exists(symbol),
                args,
            } => {
                prefix.push((false, *symbol));
                term = args[0];
            }
            _ => break,
        }
    }
    let mut negated = arena.not(term)?;
    for (was_forall, symbol) in prefix.into_iter().rev() {
        negated = if was_forall {
            arena.exists(symbol, negated)?
        } else {
            arena.forall(symbol, negated)?
        };
    }
    Ok(negated)
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
    // Front-door route attribution (ADR-1760), opt-in and OFF by default. When a
    // `RouteAttributionGuard` is live on this thread, the OUTERMOST `check_auto`
    // takes its result from `check_auto_explained` and publishes that call's
    // trace into the thread-local attribution, so the shipped front door
    // (`solve_smtlib`, as `smtcomp_cli` runs it) can say which route decided the
    // file. It does NOT change the answer: `check_auto_explained` returning the
    // same verdict as `check_auto` for every query is exactly the invariant
    // `route_trace` exists to uphold and `tests/route_trace.rs` pins.
    //
    // Nested `check_auto` calls (a route solving a sub-query — IMC, PDR,
    // quantifier instantiation, the refuters) take the plain path unchanged;
    // their dispatch is internal detail of the route that made them, and
    // publishing them would bury the top-level decision under whichever route
    // recursed the most.
    //
    // With the guard off this is one thread-local `Cell<bool>` read.
    //
    // MEASURED DIVERGENCE, repaired here rather than inherited.
    // `check_auto_explained` does NOT run `memory_budget_decline` at entry; only
    // `check_auto` does. So a query under a memory budget that `check_auto`
    // declines at the door would, if delegated naively, run the whole dispatch
    // instead — a real verdict change, on exactly the axis `smtcomp_cli`'s
    // `--memory-limit-mb` exercises. The entry guard therefore runs BEFORE the
    // delegation and both paths return the same decline.
    //
    // This is a pre-existing gap in the two functions' contract, not one this
    // lane introduced: the differential corpus in `tests/route_trace.rs` never
    // sets `memory_limit_mb`, so it passes vacuously on this axis.
    // `route_attribution_is_verdict_identical_under_a_memory_budget` in
    // `tests/route_attribution.rs` pins the repaired behaviour.
    if let Some(decline) = memory_budget_decline(config, "check_auto entry") {
        return Ok(decline);
    }
    // Same reason as in `solve`, and it has to be here TOO rather than only
    // there: `check_auto` is a front door in its own right (the SMT-LIB path,
    // every `-p axeyum-solver` consumer that skips the quantifier ladder), so a
    // watchdog armed only in `solve` would leave those callers exactly as
    // unbounded as before.
    let _memory_watchdog = crate::memory_budget::MemoryWatchdog::install(config);
    if let Some(attributed) = route_trace::with_outermost_dispatch(|outermost| {
        if !outermost {
            return None;
        }
        Some(
            check_auto_explained(arena, assertions, config).inspect(|(_, trace)| {
                route_trace::absorb_dispatch_trace(trace);
            }),
        )
    }) {
        return attributed.map(|(result, _)| result);
    }
    // Thin wrapper: the *same* dispatch as `check_auto_explained`, with no trace
    // recorder. The recorder is a pure side effect at the existing decide/decline
    // sites — it never participates in a branch condition — so this returns
    // byte-for-byte the verdict `check_auto_explained` does (verdict invariance,
    // pinned by `tests/route_trace.rs`).
    // The caller's budget is a WALL-CLOCK deadline for the whole call, not a fresh
    // allowance per fallback rung (see `fallback_deadline`).
    // (The `memory_budget_decline` entry guard that used to sit here now runs
    // ABOVE the attribution branch, so BOTH paths are gated by it rather than
    // only this one — see the comment there.)
    let deadline = fallback_deadline(config);
    let result = check_auto_with_recorder(arena, assertions, config, &mut None)?;
    if matches!(result, CheckResult::Unknown(_)) {
        // Integer-algebraic identity refutation (QF_NIA): cheap, exact, unsat-only.
        if crate::nra_real_root::integer_algebraic_refutation(arena, assertions) {
            return Ok(CheckResult::Unsat);
        }
        if let Some(unsat) = try_conjunct_refutation(arena, assertions, config, deadline)? {
            return Ok(unsat);
        }
        if let Some(verdict) = try_disjunct_refutation(arena, assertions, config, deadline)? {
            return Ok(verdict);
        }
        if let Some(verdict) = try_finite_domain_split(arena, assertions, config, deadline)? {
            return Ok(verdict);
        }
    }
    Ok(result)
}

/// The wall-clock deadline the post-dispatch fallback chain
/// ([`try_conjunct_refutation`], [`try_disjunct_refutation`],
/// [`try_finite_domain_split`]) must respect, taken at ENTRY so it covers the main
/// dispatch too.
///
/// Each rung used to read `config.timeout` directly, i.e. to award itself a FRESH
/// full budget after the main solve had already spent one — and the rungs recurse
/// into `check_auto`, which re-enters the chain. Measured, a caller asking for 24 s
/// could burn well over 60 s (one file took 400 s) while a sibling front end that
/// enforced its own limit finished on time. `check_auto`/`check_auto_explained` are
/// public API, so every consumer inherited the overrun. This is the same defect
/// class as a phase ignoring the caller's parse deadline, and the fix is the same:
/// one deadline, taken once, threaded down.
///
/// The per-rung SHARE is still sized from the caller's original budget (so a rung
/// reached with plenty of time left behaves exactly as before), but every
/// individual sub-solve is additionally clamped to what remains before the
/// deadline, and the chain stops the moment it passes. Bounding the total instead
/// of shrinking the share is what keeps the rungs' existing solving power.
///
/// `None` (an unbounded query) keeps the existing behaviour: the rungs decline
/// outright rather than launch unbounded sub-solves.
fn fallback_deadline(config: &SolverConfig) -> Option<Instant> {
    config.timeout.and_then(|t| Instant::now().checked_add(t))
}

/// The budget still available before `deadline`, or `None` when it has passed (or
/// was never set). Every fallback sub-solve is clamped to this, so the chain as a
/// whole cannot outlive the caller's request.
fn remaining_before(deadline: Option<Instant>) -> Option<Duration> {
    let remaining = deadline?.checked_duration_since(Instant::now())?;
    if remaining.is_zero() {
        None
    } else {
        Some(remaining)
    }
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
    deadline: Option<Instant>,
) -> Result<Option<CheckResult>, SolverError> {
    let Some(total) = config.timeout else {
        return Ok(None); // unbounded ⇒ skip (avoid runaway sub-solves)
    };
    if remaining_before(deadline).is_none() {
        return Ok(None); // the caller's budget (plus grace) is already gone
    }
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
    for &c in &conjuncts {
        // Each sub-solve keeps its per-conjunct share, additionally clamped to what
        // is left of the caller's deadline — so the CHAIN is bounded even though the
        // share itself is sized from the original budget.
        let Some(left) = remaining_before(deadline) else {
            return Ok(None); // out of the caller's budget ⇒ stop, never overrun
        };
        let sub = config.clone().with_timeout(per.min(left));
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
    deadline: Option<Instant>,
) -> Result<Option<CheckResult>, SolverError> {
    let Some(total) = config.timeout else {
        return Ok(None); // unbounded ⇒ skip (avoid runaway sub-solves)
    };
    if remaining_before(deadline).is_none() {
        return Ok(None); // the caller's budget is already gone
    }
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
    let mut idx = vec![0usize; disjunctions.len()];
    let mut all_unsat = true;
    loop {
        let mut branch: Vec<TermId> = Vec::with_capacity(disjunctions.len() + rest.len());
        for (di, d) in disjunctions.iter().enumerate() {
            branch.push(d[idx[di]]);
        }
        branch.extend_from_slice(&rest);
        // Out of the caller's budget with branches unexplored: those branches are
        // UNDECIDED, so `all_unsat` is not established — decline.
        let Some(left) = remaining_before(deadline) else {
            return Ok(None);
        };
        let sub = config.clone().with_timeout(per.min(left));
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
/// a concrete `z` and refutes `z²>10⁹`. The bounded route runs before nonlinear
/// dispatch so an honestly enforced shared deadline cannot starve it, and remains
/// available as a post-dispatch fallback for callers that reach it with budget
/// left. It fires only for a small branch product; each branch re-enters
/// `check_auto` with no equality-disjunction left, so the recursion bottoms out.
/// Sound: it never emits a wrong `unsat` (a branch it cannot decide forces a
/// decline) and its `sat` is a genuine model of the original.
fn try_finite_domain_split(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<Option<CheckResult>, SolverError> {
    let Some(total) = config.timeout else {
        return Ok(None); // unbounded ⇒ skip (avoid runaway sub-solves)
    };
    if remaining_before(deadline).is_none() {
        return Ok(None); // the caller's budget is already gone
    }
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
    // Enumerate the cartesian product via a mixed-radix index vector.
    let mut idx = vec![0usize; disjunctions.len()];
    let mut all_unsat = true;
    loop {
        let mut branch: Vec<TermId> = Vec::with_capacity(disjunctions.len() + rest.len());
        for (di, d) in disjunctions.iter().enumerate() {
            branch.push(d[idx[di]]);
        }
        branch.extend_from_slice(&rest);
        // Out of the caller's budget with branches unexplored: those branches are
        // UNDECIDED, so `all_unsat` is not established — decline.
        let Some(left) = remaining_before(deadline) else {
            return Ok(None);
        };
        let sub = config.clone().with_timeout(per.min(left));
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
    // One deadline for the whole call, taken at entry — see `fallback_deadline`.
    let deadline = fallback_deadline(config);
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
        && let Some(unsat) = try_conjunct_refutation(arena, assertions, config, deadline)?
    {
        trace.record_decided("conjunct-refutation", Verdict::Unsat);
        unsat
    } else if matches!(result, CheckResult::Unknown(_))
        && let Some(verdict) = try_disjunct_refutation(arena, assertions, config, deadline)?
    {
        let recorded = if matches!(verdict, CheckResult::Sat(_)) {
            Verdict::Sat
        } else {
            Verdict::Unsat
        };
        trace.record_decided("disjunct-refutation", recorded);
        verdict
    } else if matches!(result, CheckResult::Unknown(_))
        && let Some(verdict) = try_finite_domain_split(arena, assertions, config, deadline)?
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
/// The route-boundary admission check for integer constants outside `i128`
/// (ADR-1702 slice 2). `None` admits; `Some(reason)` is a first-class
/// `unknown` naming why.
///
/// **Why a check and not just per-route decline.** Every route already fails
/// closed on a `WideIntConst` — the LIA/LRA linearizers' wildcard arm returns
/// `Unsupported`, `int_blast` returns `WideConstantOutOfRange`, the certificate
/// emitters decline — so this guard changes no verdict. What it changes is the
/// COST and the EXPLANATION. Without it a 15 MB Certora file walks the whole
/// dispatch ladder before every rung declines for the same reason: measured on
/// `3106_1c933134166dbad31f79_38_QF_UFLIA.smt2`, that is the full 24 s budget
/// instead of a fast, named `unknown`. And a trace that ends in a dozen
/// unrelated declines does not tell the next reader that ONE thing was missing.
///
/// **Why it is not permanent.** This is ADR-1702's opt-in-per-route discipline,
/// transplanted from `Rational` to the literal: promotion is a route's decision,
/// not a property of the type. A route that gains an exact wide path — the
/// exact-rational simplex is the obvious first candidate, since its tableau is
/// already `Rational` and `Rational` already has `wide_*` — is named here and
/// then runs. Nothing is opted in today, and ADR-0376's ablation (re-measured
/// 2026-09-06: 6/6 still `unknown` with every wide literal *removed*) says why
/// opting one in would decide nothing on the `QF_UFLIA` population: the binding
/// constraint there is the decision procedure, not the literal type.
fn wide_int_admission(features: &Features) -> Option<UnknownReason> {
    if !features.has_wide_int {
        return None;
    }
    Some(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: "query contains an integer literal outside the i128 reference range; \
                 no route has opted into wide integer constants (ADR-1702 slice 2)"
            .to_owned(),
    })
}

/// [`wide_int_admission`] plus the trace entry, so the dispatcher spends three
/// lines on it rather than six.
fn wide_int_decline(features: &Features, rec: &mut Recorder<'_>) -> Option<CheckResult> {
    let reason = wide_int_admission(features)?;
    with_recorder(rec, |t| {
        t.record_declined("wide-int-admission", DeclineReason::from_unknown(&reason));
    });
    Some(CheckResult::Unknown(reason))
}

// 102 lines, three of them the ADR-1702 wide-integer admission guard added on
// 2026-09-06; the function was at 99 before it. Splitting a dispatch ladder to
// satisfy a line count would scatter the ordering that IS the logic, so the
// lint is allowed here as it already is at six other sites in this file.
#[allow(clippy::too_many_lines)]
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
    if let Some(result) = wide_int_decline(&features, rec) {
        return Ok(result);
    }
    if crate::term_identity::term_identity_refutation(arena, assertions).is_some() {
        with_recorder(rec, |t| {
            t.record_decided("term-identity-refuter", Verdict::Unsat);
        });
        return Ok(CheckResult::Unsat);
    }
    if let Some(result) = dispatch_cas_refuters(arena, assertions, &features, rec) {
        return Ok(result);
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

    // A finite-domain fallback placed only *after* nonlinear dispatch is
    // unreachable when that dispatch honestly consumes the caller's shared
    // absolute deadline. Run this already-bounded route first for genuinely
    // nonlinear integer products only. The restriction avoids intercepting
    // partially modeled mixed-theory front ends (notably word/Int coupling),
    // while covering the starvation case this placement repairs. It spends at
    // most half of the original budget across a capped branch product; following
    // work receives only the time left before this entry's deadline.
    if features.has_int
        && !has_quantifier
        && crate::nia_linearize::has_nonlinear_int_product(arena, assertions)
        && let Some(verdict) = try_finite_domain_split(arena, assertions, config, deadline)?
    {
        let recorded = if matches!(verdict, CheckResult::Sat(_)) {
            Verdict::Sat
        } else {
            Verdict::Unsat
        };
        with_recorder(rec, |t| {
            t.record_decided("finite-domain-split", recorded);
        });
        return Ok(verdict);
    }

    // The early finite-domain probe is part of this call's wall-clock budget.
    // Clamp preprocessing and ordinary dispatch to what remains rather than
    // silently handing either path a fresh copy of `config.timeout`.
    let remaining_config = config_with_remaining_deadline(config, deadline);
    let config = &remaining_config;

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
            Ok(Some((reduced, trail)))
                if reduction_shrinks_encoding(arena, assertions, &reduced, deadline) =>
            {
                dispatch_reduced(arena, assertions, &reduced, &trail, config, deadline, rec)
            }
            // The reduction made the *encoding* bigger, so solve the original
            // instead. See `reduction_shrinks_encoding`.
            Ok(Some(_)) => check_auto_dispatch(
                arena,
                assertions,
                &config_with_remaining_deadline(config, deadline),
                rec,
            ),
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

// ---------------------------------------------------------------------------
// One ladder, one clock: how much of it each route may spend
// ---------------------------------------------------------------------------

/// The floor on any route's slice of a ladder's clock, capped at **half** the
/// remaining budget by [`LadderSlice::slice_of`].
///
/// It replaces a branch that handed the route the WHOLE budget when its share
/// rounded to zero, in the two places that divided rather than reserved:
/// `int_real_relax_budget` returned `config` unchanged when `timeout / 6` was
/// zero, and `pre_lia_uf_probe_budget` returned the full `timeout` when
/// `timeout / 10` was. The first is recorded as a FINDING against
/// `INT_REAL_RELAX_BUDGET_SHARE` in [`crate::config_registry`]; the second was
/// found by this lane looking for more of the same shape.
///
/// **How reachable that was, corrected.** The FINDING says the policy is
/// bypassed "at exactly the small-budget end where starvation matters most",
/// and this lane repeated that before measuring it. `Duration` division is in
/// NANOSECONDS: `Duration::from_millis(5) / 6` is 833 µs, not zero. `is_zero()`
/// there needs a budget under **six nanoseconds**, so the band the old branch
/// actually inverted on is six nanoseconds wide and no caller has ever been in
/// it. The defect was structural, not behavioural, and saying otherwise is the
/// kind of claim this file's own rules exist to stop. Removing the special case
/// is still right — a branch that returns the unshared budget is one edit away
/// from being reachable — but it bought no measured behaviour.
///
/// A millisecond is chosen because it is the smallest slice any route in this
/// tree can act on, and because the alternative — skipping the route entirely
/// when its share underflows — is a *different* policy that changes which routes
/// run, not just how long they run for. The **half** cap is the load-bearing
/// half: without it this constant recreates the very inversion it replaced on
/// every budget under a millisecond, which is a band a hundred thousand times
/// wider than the one it closed. That is not hypothetical — it is what the first
/// version of this code did, and the mutation that restores the old branch is
/// what found it, by making no test fail at all.
const MIN_LADDER_SLICE: Duration = Duration::from_millis(1);

/// The shape of one route's claim on a ladder's remaining wall clock.
///
/// The tree grew three hand-rolled versions of this arithmetic before it grew a
/// name for it (`dl_probe_budget`, `cegar_probe_budget`, `int_real_relax_budget`),
/// and a fourth was needed for `abv-online-cdclt` — the route that took
/// `config.timeout` in FULL on every array query, declined, and left the array
/// ladder underneath it nothing. Measured on the committed 50-file `QF_ABV`
/// span-log sweep: on four files it spent 24.009 s of a 24 s budget and
/// `array-fast-path` then decided the file in 0.007–0.174 s.
///
/// The distinction the two variants draw is the one the `QF_UFLIA` measurement
/// paid four files to learn (see [`UF_ARITH_LADDER_RESERVE_SHARE`]): a route
/// that decides most of what it is given needs a **reserve** (it keeps
/// everything but a slice), while a route that is speculative insurance takes a
/// **fraction** (it keeps only a slice). Halving a budget is the worst of both
/// — it starves the deciding route without buying the ladder anything it
/// needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SliceShape {
    /// The route keeps everything except `1/reserve_share` of what is left,
    /// with that reserve itself capped at `reserve_ceiling` when present.
    AllButReserve {
        /// Divisor of the remaining budget that is held back for the ladder.
        reserve_share: u32,
        /// Ceiling on the held-back slice, for budgets large enough that a flat
        /// reserve is cheaper insurance than a proportional one.
        reserve_ceiling: Option<Duration>,
    },
    /// The route may spend `1/share` of what is left; the ladder keeps the rest.
    Fraction {
        /// Divisor of the remaining budget granted to the route.
        share: u32,
        /// Ceiling on the granted slice, when the route is a quick screen whose
        /// usefulness does not scale with the clock.
        ceiling: Option<Duration>,
    },
}

/// One route's slice of a ladder's clock, as a named policy rather than a
/// divisor written at the call site.
///
/// **A route that runs before others must leave them something.** Every field
/// here is a policy statement about one route, and every constructed value in
/// this file is a `const` with a dated justification in
/// [`crate::config_registry`], so "why does this route get 18 s of a 24 s
/// budget" is answerable from the registry rather than from a literal in an
/// expression.
///
/// The type deliberately does **not** own a clock. It converts a *remaining*
/// budget the caller measured into a slice, so a caller that has a dispatch
/// deadline passes what is left of it (one clock for the whole ladder) and a
/// caller that only has `config.timeout` passes that. Which one a call site
/// uses is a property of that ladder, not of this policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LadderSlice {
    /// The route this policy governs, spelled as it appears in the route trail.
    /// Carried so a reader of the constant can find the attribution rows it
    /// explains; nothing branches on it.
    pub(crate) route: &'static str,
    /// How much of what is left this route may spend.
    pub(crate) shape: SliceShape,
}

impl LadderSlice {
    /// The route keeps everything but `1/reserve_share` of the remaining budget.
    pub(crate) const fn all_but_reserve(route: &'static str, reserve_share: u32) -> Self {
        Self {
            route,
            shape: SliceShape::AllButReserve {
                reserve_share,
                reserve_ceiling: None,
            },
        }
    }

    /// As [`Self::all_but_reserve`], with the reserve capped at a flat ceiling.
    pub(crate) const fn all_but_capped_reserve(
        route: &'static str,
        reserve_share: u32,
        reserve_ceiling: Duration,
    ) -> Self {
        Self {
            route,
            shape: SliceShape::AllButReserve {
                reserve_share,
                reserve_ceiling: Some(reserve_ceiling),
            },
        }
    }

    /// The route may spend `1/share` of the remaining budget.
    pub(crate) const fn fraction(route: &'static str, share: u32) -> Self {
        Self {
            route,
            shape: SliceShape::Fraction {
                share,
                ceiling: None,
            },
        }
    }

    /// As [`Self::fraction`], with the granted slice capped at a flat ceiling.
    pub(crate) const fn capped_fraction(
        route: &'static str,
        share: u32,
        ceiling: Duration,
    ) -> Self {
        Self {
            route,
            shape: SliceShape::Fraction {
                share,
                ceiling: Some(ceiling),
            },
        }
    }

    /// The slice this policy grants out of `remaining`.
    ///
    /// Never zero unless `remaining` is (see [`MIN_LADDER_SLICE`]), and never
    /// more than `remaining`: a policy that hands a route more clock than the
    /// ladder has is the bug this type exists to make unwritable.
    pub(crate) fn slice_of(self, remaining: Duration) -> Duration {
        let want = match self.shape {
            SliceShape::AllButReserve {
                reserve_share,
                reserve_ceiling,
            } => {
                let mut reserve = remaining / reserve_share.max(1);
                if let Some(ceiling) = reserve_ceiling {
                    reserve = reserve.min(ceiling);
                }
                remaining.saturating_sub(reserve)
            }
            SliceShape::Fraction { share, ceiling } => {
                let mut slice = remaining / share.max(1);
                if let Some(ceiling) = ceiling {
                    slice = slice.min(ceiling);
                }
                slice
            }
        };
        // The floor is capped at HALF the remaining budget, not at the whole of
        // it. `MIN_LADDER_SLICE.min(remaining)` was written first and is wrong
        // in the direction this whole type exists to prevent: on any budget
        // under a millisecond it resolves to `remaining`, so the clamp hands
        // the route the entire clock and the ladder nothing — the same
        // inversion as the code it replaced, with a band a hundred thousand
        // times wider. Caught by the mutation that restores the old
        // `share.is_zero()` branch and found it made NO test fail.
        want.clamp(MIN_LADDER_SLICE.min(remaining / 2), remaining)
    }

    /// What the ladder below this route keeps out of `remaining`.
    ///
    /// Exposed so a test can assert the reserve directly rather than by
    /// subtracting two numbers it also computed.
    #[cfg(test)]
    pub(crate) fn reserved_from(self, remaining: Duration) -> Duration {
        remaining.saturating_sub(self.slice_of(remaining))
    }

    /// `config` with this route's slice of `remaining` as its timeout.
    ///
    /// `remaining == None` (an unbounded caller budget) stays unbounded: there
    /// is no clock to share, and both the route and the ladder below it then
    /// decline only on their deterministic size guards. This only ever divides
    /// an existing budget, never invents one.
    pub(crate) fn apply(self, config: &SolverConfig, remaining: Option<Duration>) -> SolverConfig {
        let Some(remaining) = remaining else {
            return config.clone();
        };
        let mut sliced = config.clone();
        sliced.timeout = Some(self.slice_of(remaining));
        sliced
    }
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
/// Whether the reduced query is worth dispatching, judged by the size it
/// **bit-blasts to** rather than by its term count.
///
/// `solve_eqs` and `elim_unconstrained` substitute terms, and substitution
/// duplicates structure the term DAG was *sharing*. The bit-blaster then pays for
/// every copy, so a reduction that looks free at the term level can hand the SAT
/// backend a much larger circuit.
///
/// Measured on three files the raw `SatBvBackend` path decides and the reduced
/// dispatch does not:
///
/// | benchmark | term DAG | AIG nodes |
/// |---|---|---|
/// | `021-bench_11651` | 148 → 179 | 2 939 → 3 563 (+21 %) |
/// | `062-bench_2195` | 1 375 → **1 215** | 35 329 → 51 724 (+46 %) |
/// | `058-bench_165` | — | 1 223 291 → 1 887 781 (+54 %) |
///
/// Note `062`: the term DAG **shrank** while the AIG grew 46 %. The term count is
/// not merely a weak proxy, it points the wrong way — which is why this compares
/// lowered sizes and nothing else.
///
/// Cost is one extra lowering (0.36 ms for `021`) against a 24 s timeout on the
/// files this rescues. When either side cannot be lowered (not a pure bit-vector
/// query) the reduction is kept, preserving the previous behaviour: the
/// reduction genuinely helps some queries — `025-bench_250` is decided by the
/// reduced path and *not* by the raw backend — so this only declines to use it
/// when it demonstrably inflates the circuit.
fn reduction_shrinks_encoding(
    arena: &mut TermArena,
    original: &[TermId],
    reduced: &[TermId],
    deadline: Option<Instant>,
) -> bool {
    // `lower_terms` does not return an error for a non-bit-vector query — it
    // PANICS (`unreachable!("integer terms are rejected before bit lowering
    // (ADR-0014)")`, axeyum-bv/src/lib.rs:1890). So the query has to be screened
    // for bit-blastability first; a `let Ok(..) else` guard is not protection.
    // Five arithmetic tests died on exactly that.
    let bit_blastable = |terms: &[TermId]| {
        Features::scan_within(arena, terms, deadline).is_some_and(|f| {
            !f.has_int
                && !f.has_real
                && !f.has_datatype
                && !f.has_function
                && !f.has_uninterpreted_sort
                && !f.has_array
        })
    };
    if !bit_blastable(original) || !bit_blastable(reduced) {
        return true;
    }
    let Ok(reduced_lowering) = axeyum_bv::lower_terms(arena, reduced) else {
        return true;
    };
    let Ok(original_lowering) = axeyum_bv::lower_terms(arena, original) else {
        return true;
    };
    reduced_lowering.aig().node_count() <= original_lowering.aig().node_count()
}

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
            // An integer constant outside `i128` has no `Rational::integer`
            // image (ADR-1702 keeps promotion opt-in), so it leaves this
            // fragment rather than being narrowed.
            TermNode::WideIntConst(_) => return Err(milp_out_of_fragment()),
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
    // Only `unsat` is taken from this route, and every mode of the elimination is a
    // relaxation, so `unsat` transfers at any zero-divisor group count (ADR-1730).
    let lin = axeyum_rewrite::eliminate_int_divmod(&mut scratch, &relaxed)
        .map_err(|e| SolverError::Backend(e.to_string()))?
        .into_assertions();
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

/// Declines a `sat` that came out of a zero-divisor relaxation the elimination did
/// not congruence-close (ADR-1730).
///
/// `eliminate_int_divmod` maps each `div a 0` / `mod a 0` group to a fresh
/// unconstrained variable — SMT-LIB leaves the value underspecified — and ties the
/// groups together with pairwise congruence lemmas so that a satisfying assignment
/// induces a genuine total `div(·, 0)`. Above `MAX_CONGRUENCE_GROUPS` those lemmas
/// are skipped. Dropping conjuncts only ENLARGES the model set, so `unsat` and
/// `unknown` pass through untouched at every group count; a `sat`, however, may
/// give two provably-equal dividends different free values, which no total function
/// can produce. That is a wrong `sat`, so it becomes a first-class `unknown` whose
/// detail names the group count and the bound.
fn guard_zero_divisor_sat(
    result: CheckResult,
    congruence: axeyum_rewrite::ZeroDivisorCongruence,
) -> CheckResult {
    if congruence.sat_transfers() {
        return result;
    }
    match result {
        CheckResult::Sat(_) => CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: format!(
                "int div/mod-by-zero relaxation was not congruence-closed \
                 ({} distinct zero-divisor dividends exceeds the {} bound), so a \
                 `sat` of the relaxation need not be a model of the original",
                congruence.groups(),
                axeyum_rewrite::MAX_CONGRUENCE_GROUPS,
            ),
        }),
        other => other,
    }
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
    dispatch_deadline: Option<Instant>,
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
    let elim = axeyum_rewrite::eliminate_int_divmod(arena, assertions)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    // ADR-1730. Above `MAX_CONGRUENCE_GROUPS` the zero-divisor Ackermann lemmas are
    // NOT emitted, and the mode used to be invisible here. It is a relaxation, so
    // `unsat` transfers at every group count — but this route does not only refute:
    // the simplex and DPLL verdicts below are returned as the answer for the
    // ORIGINAL query, `Sat` included, and a `sat` of a relaxation that is not
    // congruence-closed need not be a model of the original. `guard_zero_divisor_sat`
    // turns exactly that case into a first-class `unknown` naming the group count.
    // A decline is a legal discharge (ADR-1721); a silent `sat` is not.
    let congruence = elim.congruence();
    let lin = elim.into_assertions();
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
            let result = guard_zero_divisor_sat(result, congruence);
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
    let mut group: Option<IntLinearGroup> = None;
    // The integer-linear ladder's fused group (`crate::portfolio`). At one
    // worker this branch is not taken at all: the call below is the same call
    // this function has always made, on the caller's arena, with the caller's
    // config. That is the strongest available form of the degeneracy property --
    // the sequential path is not merely equivalent to a one-worker group, it
    // does not construct one.
    if int_linear_portfolio_workers() > 1 {
        // The group's clock is what is LEFT of the dispatcher's entry deadline,
        // not a fresh `config.timeout`. Measured 2026-09-09, and it is the
        // difference between a portfolio and a budget overrun: on
        // `QF_IDL/.../super_queen83-1.smt2` the difference-logic probe above
        // spends 21 s of the 24 s budget, so an unclamped group would run its
        // arms for a further 24 s and answer at 45 s -- past a wall the
        // competition harness enforces by killing the process, which scores as
        // a loss whatever the arms found.
        //
        // The sequential call below is deliberately NOT clamped: it takes
        // `config` exactly as it always has. Clamping it would be a behaviour
        // change to the shipped path, which is the one thing this wiring must
        // not do -- and `lia-dpll` does not have the same exposure, because it
        // is the route the ladder was going to run either way.
        let group_config = config_with_remaining_deadline(config, dispatch_deadline);
        group = Some(run_int_linear_group(
            arena,
            &lin,
            &group_config,
            congruence,
            rec,
        )?);
        if let Some(group) = &mut group
            && let Some(decided) = group.decided_by_a_later_arm.take()
        {
            return Ok(Some(decided));
        }
    }
    // `lia-dpll` is the group's FIRST arm, so when the group ran it has already
    // been run -- on the group's clock, on its own arena clone, and recorded.
    // Calling it again here would run the ladder's main integer route TWICE per
    // query and put two `lia-dpll` rows in the trail. Taking the group's result
    // is not an optimisation; it is the difference between one dispatch and two.
    let already_recorded = group.is_some();
    let lia_result = match group {
        Some(group) => group.first_arm,
        None => check_with_lia_dpll(arena, &lin, config),
    };
    match lia_result {
        Ok(mut result) => {
            result = guard_zero_divisor_sat(result, congruence);
            if let CheckResult::Unknown(reason) = &result
                && features.has_function
                && is_budget_unknown_kind(reason.kind)
            {
                result =
                    CheckResult::Unknown(annotate_lia_budget_before_uf(arena, assertions, reason));
            }
            if !already_recorded {
                with_recorder(rec, |t| t.record_result("lia-dpll", &result));
            }
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
            if !already_recorded {
                with_recorder(rec, |t| {
                    t.record_declined("lia-dpll", DeclineReason::Unsupported);
                });
            }
            Ok(None)
        }
        Err(other) => Err(other),
    }
}

/// The default worker count for the integer-linear fused group.
///
/// `1` is the sequential ladder: [`dispatch_int_linear_refuters`] does not even
/// construct a group at this setting, so the single-threaded path is the
/// pre-portfolio path unchanged rather than a re-derivation of it.
const DEFAULT_INT_LINEAR_PORTFOLIO_WORKERS: usize = 1;

/// How many workers the integer-linear fused group may use.
///
/// Read once per process from `AXEYUM_PORTFOLIO_WORKERS`. A resource decision
/// belongs to the operator, not to the query: the arms of this group each want
/// a whole core for most of a competition budget, and how many cores exist is
/// not something the dispatcher can read off the formula.
fn int_linear_portfolio_workers() -> usize {
    static RESOLVED: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    if let Some(workers) = INT_LINEAR_PORTFOLIO_WORKERS_OVERRIDE.with(std::cell::Cell::get) {
        return workers;
    }
    *RESOLVED.get_or_init(|| {
        std::env::var("AXEYUM_PORTFOLIO_WORKERS")
            .ok()
            .and_then(|value| value.trim().parse::<usize>().ok())
            .unwrap_or(DEFAULT_INT_LINEAR_PORTFOLIO_WORKERS)
    })
}

std::thread_local! {
    /// Per-thread override of [`int_linear_portfolio_workers`].
    ///
    /// The env-var reading is a process-wide `OnceLock`, which makes an
    /// in-process A/B between one worker and two impossible -- and that A/B is
    /// the only way to test a scheduling change against the schedule it
    /// replaced. Thread-local rather than global for the same reason lane
    /// identity is: a test binary runs its cases in parallel, and a global
    /// would let one case decide another case's policy.
    static INT_LINEAR_PORTFOLIO_WORKERS_OVERRIDE: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

/// Sets the integer-linear group's worker count on this thread until dropped.
///
/// Restores the previous value rather than clearing it, so nesting is safe.
#[derive(Debug)]
pub struct IntLinearPortfolioWorkersGuard(Option<usize>);

impl IntLinearPortfolioWorkersGuard {
    /// Overrides the worker count on this thread.
    #[must_use]
    pub fn set(workers: usize) -> Self {
        Self(INT_LINEAR_PORTFOLIO_WORKERS_OVERRIDE.with(|cell| cell.replace(Some(workers))))
    }
}

impl Drop for IntLinearPortfolioWorkersGuard {
    fn drop(&mut self) {
        INT_LINEAR_PORTFOLIO_WORKERS_OVERRIDE.with(|cell| cell.set(self.0));
    }
}

/// The arms of the integer-linear fused group, in priority order.
///
/// **Why these two.** On the committed loss population, four files are decided
/// alone at the competition budget by the bounded integer blast -- 8.5 s to
/// 17.3 s -- while the ladder spends the same clock inside `lia-dpll` (or
/// arrives with 2.6 s left, having spent 21 s in `dl-online`). No reservation
/// collects them: on `QF_LIA/.../182-incremental_scheduling-17280-0` the whole
/// 24 s is *inside* `lia-dpll`, so any slice large enough for the blast is a
/// slice taken from the route that decides the rest of the division. Two arms,
/// two cores, both get the whole budget.
///
/// `lia-dpll` is first because it is the ladder's own next route and decides
/// the overwhelming majority of this fragment; the declared order is also the
/// tie-break, so the group's verdict on a query both arms decide is
/// `lia-dpll`'s -- the verdict the sequential ladder would have returned.
///
/// The blast arm is the tree's existing width ladder, not a fresh call to
/// `check_with_all_theories`: with integers present the combined path reports
/// `Unknown` for an in-range `unsat`, so only the width ladder's
/// replay-checked `Sat` and integer-free `Unsat` are sound here, and a second
/// hand-rolled copy of that reasoning is how a wrong `unsat` gets shipped.
const INT_LINEAR_PORTFOLIO_ARMS: [crate::portfolio::Arm; 2] = [
    crate::portfolio::Arm {
        route: "lia-dpll",
        weight: 3,
        run: check_with_lia_dpll,
    },
    crate::portfolio::Arm {
        route: "int-blast-ladder",
        weight: 1,
        run: dispatch_int_blast_width_ladder,
    },
];

/// What the integer-linear fused group produced.
///
/// Split into the first arm and the rest because the caller's handling of
/// `lia-dpll`'s own result is established behaviour -- the `has_function`
/// fall-through, the budget annotation, the zero-divisor guard -- and belongs to
/// that route, not to the group.
struct IntLinearGroup {
    /// `lia-dpll`'s result, for the caller's established handling.
    first_arm: Result<CheckResult, SolverError>,
    /// A verdict from an arm AFTER `lia-dpll`, when one decided.
    decided_by_a_later_arm: Option<CheckResult>,
}

/// Runs the integer-linear fused group over `lin` (the div/mod-eliminated
/// assertions -- **one query**, which is what makes the group's cross-arm
/// disagreement gate meaningful).
///
/// Records every arm it ran, in **declared** order: the trail's contents depend
/// on the race but its shape must not.
///
/// # Errors
///
/// Propagates a cross-arm disagreement from
/// [`crate::portfolio::FusedGroup::run`] as a [`SolverError`]: two routes
/// contradicting each other on one query is a soundness defect and must not be
/// resolved into a verdict.
fn run_int_linear_group(
    arena: &TermArena,
    lin: &[TermId],
    config: &SolverConfig,
    congruence: axeyum_rewrite::ZeroDivisorCongruence,
    rec: &mut Recorder<'_>,
) -> Result<IntLinearGroup, SolverError> {
    let group = crate::portfolio::FusedGroup::new(
        &INT_LINEAR_PORTFOLIO_ARMS,
        int_linear_portfolio_workers(),
    );
    let outcome = group.run(arena, lin, config)?;
    let winner = outcome.winner;
    let mut first_arm = Ok(CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Other,
        detail: String::from("portfolio first arm produced no outcome"),
    }));
    let mut decided_by_a_later_arm = None;
    for (index, arm) in outcome.arms.into_iter().enumerate() {
        match arm.result {
            Ok(result) => {
                let result = guard_zero_divisor_sat(result, congruence);
                with_recorder(rec, |t| t.record_result(arm.route, &result));
                if index == 0 {
                    first_arm = Ok(result);
                } else if winner == Some(index) {
                    decided_by_a_later_arm = Some(result);
                }
            }
            Err(SolverError::Unsupported(message)) => {
                with_recorder(rec, |t| {
                    t.record_declined(arm.route, DeclineReason::Unsupported);
                });
                if index == 0 {
                    first_arm = Err(SolverError::Unsupported(message));
                }
            }
            Err(other) => return Err(other),
        }
    }
    Ok(IntLinearGroup {
        first_arm,
        decided_by_a_later_arm,
    })
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

/// How the dispatcher spends its budget when the eager Ackermann admission
/// bound (`crate::euf::MAX_ACKERMANN_CONGRUENCE_PAIRS`, `64`) fires on a
/// UF+arithmetic query.
///
/// # Why this is a policy and not a constant
///
/// `try_lazy_arith_for_overbound` returns `Some(..)` **exactly when** the eager
/// bound would have fired, and `dispatch_uf_fast_paths` used to return that
/// result unconditionally — *including its `Unknown`*. So on any non-array
/// UF+arithmetic query with more than 64 congruence pairs, every route below it
/// in the ladder was unreachable: `euf-online`, `euf-offline`, and
/// `dispatch_uf_arith_online` — the online model-based EUF+LIA combination,
/// which is the architecture Z3 (`setup_QF_UFLIA` registers `theory_lra` over
/// native congruence closure) and cvc5 (`--ackermann` is expert-only, default
/// false, and force-disabled when UF is present) actually use for this logic.
/// Neither reference solver Ackermannizes UFLIA at all.
///
/// Selected by `AXEYUM_UF_ARITH_OVERBOUND` (`terminal` / `probe` / `skip`) so
/// the three arms can be A/B-ed on one binary; the default is
/// [`Self::CegarProbe`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UfArithOverboundPolicy {
    /// The lazy CEGAR receives the whole wall-clock budget and its result —
    /// `Unknown` included — is the dispatcher's final answer. This is the
    /// behaviour that made the routes below unreachable; kept as a named arm so
    /// the change can be measured against it rather than only remembered.
    CegarTerminal,
    /// The lazy CEGAR receives the remaining budget **less the ladder's
    /// reserve** (`1/``UF_ARITH_LADDER_RESERVE_SHARE`) as a probe; a decided
    /// verdict is returned, and an `Unknown` declines the route so the ladder
    /// below runs on the reserve. Default.
    CegarProbe,
    /// The lazy CEGAR does not run at all. A measurement arm: it reports what
    /// the routes underneath decide on their own, with no budget split to
    /// confound the comparison.
    SkipCegar,
}

/// The fraction of the remaining wall-clock budget held back from the lazy
/// CEGAR for the ladder underneath it, under
/// [`UfArithOverboundPolicy::CegarProbe`]. The CEGAR gets everything else, and
/// the ladder runs against the dispatcher's *entry* deadline, so the two
/// together stay inside the caller's budget rather than re-spending it.
///
/// **A RESERVE, not a split, and the difference is measured.** The first
/// version of this constant halved the budget, copying [`probe_budget`]'s
/// precedent. On the committed 200-file `QF_UFLIA` list that cost **four** files
/// we previously decided, all of them files the CEGAR needs more than half the
/// budget for: `hash_sat_05_14` (12.7 s), `xs_23_33` (13.3 s),
/// `hash_uns_05_17` (15.5 s), `hash_uns_05_20` (23.7 s). It bought nothing for
/// that, because the routes the change unblocks do not need half the clock: on
/// the nine files it wins, the ladder decides in **307–625 ms** (the `skip`
/// arm's wall clock, where no CEGAR runs at all). A half-budget split spent
/// twelve seconds to buy four hundred milliseconds of work.
///
/// `4` is chosen against **both** bounds the measurement gives, which is why it
/// is neither the largest nor the smallest defensible value:
///
/// - it leaves the CEGAR 18 s of a 24 s budget, above **three of the four**
///   regressing files' requirements (12.7 / 13.3 / 15.5 s);
/// - it gives the ladder 6 s, about **ten times** the largest ladder time
///   observed (625 ms).
///
/// The fourth, `hash_uns_05_20` at 23.7 s of a 24 s budget, is not recoverable
/// by any reserve at all: a route that needs 99% of the clock cannot share it.
/// That file is the honest, named cost of making the ladder reachable, not an
/// oversight.
///
/// A bigger reserve starves the CEGAR on files it still decides; a smaller one
/// leaves the ladder's 0.4 s of work sitting behind 21 s of CEGAR on a 24 s
/// budget, where contention alone can eat the difference. Neither failure is
/// hypothetical: the half-budget version cost four files, and the 1/8-reserve
/// version was rejected before it shipped for the second reason.
/// Measurement: `docs/research/12-performance/uf-arith-overbound-2026-09-08.md`.
///
/// An unbounded configuration (`timeout == None`) is left unbounded: there is
/// no clock to share, and both arms then decline only on their deterministic
/// size guards.
const UF_ARITH_LADDER_RESERVE_SHARE: u32 = 4;

impl UfArithOverboundPolicy {
    /// The short name this policy is selected by and reported as.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::CegarTerminal => "terminal",
            Self::CegarProbe => "probe",
            Self::SkipCegar => "skip",
        }
    }
}

std::thread_local! {
    /// A per-thread override of the process policy, set by
    /// [`UfArithOverboundPolicyGuard`]. It exists because the process policy is
    /// read once from the environment: without it, the three arms could only be
    /// A/B-ed across separate processes, and no test could exercise more than
    /// one of them.
    static UF_ARITH_OVERBOUND_OVERRIDE: std::cell::Cell<Option<UfArithOverboundPolicy>> =
        const { std::cell::Cell::new(None) };
}

/// Forces `policy` on this thread for the lifetime of the guard, restoring the
/// previous setting on drop.
pub struct UfArithOverboundPolicyGuard(Option<UfArithOverboundPolicy>);

impl UfArithOverboundPolicyGuard {
    /// Overrides the process policy on this thread.
    #[must_use]
    pub fn set(policy: UfArithOverboundPolicy) -> Self {
        UfArithOverboundPolicyGuard(UF_ARITH_OVERBOUND_OVERRIDE.with(|c| c.replace(Some(policy))))
    }
}

impl Drop for UfArithOverboundPolicyGuard {
    fn drop(&mut self) {
        UF_ARITH_OVERBOUND_OVERRIDE.with(|c| c.set(self.0));
    }
}

/// The [`UfArithOverboundPolicy`] in force on this thread: a live
/// [`UfArithOverboundPolicyGuard`]'s choice, else the process policy resolved
/// once from `AXEYUM_UF_ARITH_OVERBOUND`. An unset or unrecognised environment
/// value is the default, so a typo degrades to the shipped behaviour rather
/// than to an arm nobody chose.
fn uf_arith_overbound_policy() -> UfArithOverboundPolicy {
    static RESOLVED: std::sync::OnceLock<UfArithOverboundPolicy> = std::sync::OnceLock::new();
    if let Some(policy) = UF_ARITH_OVERBOUND_OVERRIDE.with(std::cell::Cell::get) {
        return policy;
    }
    *RESOLVED.get_or_init(
        || match std::env::var("AXEYUM_UF_ARITH_OVERBOUND").as_deref() {
            Ok("terminal") => UfArithOverboundPolicy::CegarTerminal,
            Ok("skip") => UfArithOverboundPolicy::SkipCegar,
            _ => UfArithOverboundPolicy::CegarProbe,
        },
    )
}

std::thread_local! {
    /// Whether over-bound UF+arithmetic dispatch counters are being collected on
    /// this thread. See [`UfArithOverboundStatsGuard`].
    static COLLECT_UF_ARITH_OVERBOUND_STATS: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    /// The counters accumulated since the active guard was created.
    static UF_ARITH_OVERBOUND_STATS: std::cell::Cell<UfArithOverboundStats> =
        const { std::cell::Cell::new(UfArithOverboundStats::ZERO) };
}

/// Clock-free counters for the over-bound UF+arithmetic decision point: how
/// often the eager Ackermann bound fired, what the lazy CEGAR did with the
/// query, and whether the ladder below it got to run.
///
/// Every field is a count, never a duration — timing for this decision point is
/// already carried by [`crate::RouteTrace`]'s per-attempt `bound_by`/`bound_ms`,
/// and a second clock here would only give a reader two numbers to reconcile.
/// What the route trail cannot say is *why* the route stopped: `cegar_unknown`
/// split from `cegar_decided`, and `fell_through` split from `terminal_unknown`,
/// is the difference between "the CEGAR could not decide this" and "the CEGAR
/// could not decide this **and nothing else was allowed to try**".
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct UfArithOverboundStats {
    /// Queries on which the eager Ackermann bound fired, so this decision point
    /// was reached at all.
    pub engaged: u32,
    /// Of those, the ones on which the lazy CEGAR was skipped entirely
    /// ([`UfArithOverboundPolicy::SkipCegar`]).
    pub cegar_skipped: u32,
    /// Of those, the ones the lazy CEGAR decided (`sat` or `unsat`).
    pub cegar_decided: u32,
    /// Of those, the ones on which the lazy CEGAR returned `Unknown`.
    pub cegar_unknown: u32,
    /// `Unknown`s returned as the dispatcher's final answer, with the ladder
    /// below never entered. A nonzero count here on a division we lose is the
    /// signal this counter exists for.
    pub terminal_unknown: u32,
    /// `Unknown`s after which the ladder below (`euf-online`, `euf-offline`,
    /// `uf-arith-online`, eager `uf-arithmetic`) was allowed to run.
    pub fell_through: u32,
    /// Queries refused **before** the CEGAR by the secondary (pathological)
    /// lazy bounds — pair count above `MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS`,
    /// DAG above `MAX_LAZY_DAG_NODES`, or depth above `MAX_LAZY_DEPTH`. These
    /// stay terminal under every policy: they are the inputs on which the
    /// routes below would blow up exactly as the eager route would, which is
    /// what the bound exists for. Counted separately so "we refused" is never
    /// read as "the CEGAR tried and failed".
    pub pathological_refusals: u32,
}

impl UfArithOverboundStats {
    /// The all-zero counters, so the thread-local can be a `const` initializer.
    const ZERO: Self = Self {
        engaged: 0,
        cegar_skipped: 0,
        cegar_decided: 0,
        cegar_unknown: 0,
        terminal_unknown: 0,
        fell_through: 0,
        pathological_refusals: 0,
    };

    /// One `;`-prefixed `--trace` line, in the `key=value` shape every other
    /// instrument in this tree prints.
    #[must_use]
    pub fn trace_line(&self) -> String {
        format!(
            "; uf-overbound policy={} engaged={} cegar_skipped={} cegar_decided={} \
             cegar_unknown={} terminal_unknown={} fell_through={} pathological_refusals={}",
            uf_arith_overbound_policy().name(),
            self.engaged,
            self.cegar_skipped,
            self.cegar_decided,
            self.cegar_unknown,
            self.terminal_unknown,
            self.fell_through,
            self.pathological_refusals
        )
    }
}

/// Enables over-bound UF+arithmetic counter collection on this thread for the
/// lifetime of the guard, resetting the counters on construction and restoring
/// the previous setting on drop. Same opt-in, off-by-default convention as
/// [`crate::FrontDoorStatsGuard`] and [`crate::BvLayerStatsGuard`]: with no
/// guard live, the recording path reads one thread-local `Cell<bool>` and
/// returns.
pub struct UfArithOverboundStatsGuard(bool);

impl UfArithOverboundStatsGuard {
    /// Enables collection for the lifetime of the returned guard.
    #[must_use]
    pub fn enable() -> Self {
        let previous = COLLECT_UF_ARITH_OVERBOUND_STATS.with(|c| c.replace(true));
        UF_ARITH_OVERBOUND_STATS.with(|c| c.set(UfArithOverboundStats::ZERO));
        UfArithOverboundStatsGuard(previous)
    }
}

impl Drop for UfArithOverboundStatsGuard {
    /// Restores the previous setting and publishes the finished counters.
    ///
    /// The only COMPLETE publish point this instrument has: like
    /// [`crate::LiaCounters`], its fields accumulate across the whole solve
    /// rather than being lifted at a stage boundary, so the guard's drop is the
    /// only moment at which they stop moving.
    fn drop(&mut self) {
        COLLECT_UF_ARITH_OVERBOUND_STATS.with(|c| c.set(self.0));
        crate::live_instruments::publish_live(
            crate::live_instruments::instrument::UF_OVERBOUND,
            UF_ARITH_OVERBOUND_STATS.with(std::cell::Cell::get),
            crate::live_instruments::Sampled::Complete,
        );
    }
}

/// The counters accumulated on this thread since the active
/// [`UfArithOverboundStatsGuard`] (or the most recently dropped one) was
/// created. All-zero means either "collection was never enabled" or "the eager
/// Ackermann bound never fired on this thread" — the caller knows which, because
/// it decides whether to construct the guard.
#[must_use]
pub fn last_uf_arith_overbound_stats() -> UfArithOverboundStats {
    UF_ARITH_OVERBOUND_STATS.with(std::cell::Cell::get)
}

/// Applies `f` to this thread's counters when collection is enabled; otherwise
/// reads one `Cell<bool>` and returns.
fn note_uf_arith_overbound(f: impl FnOnce(&mut UfArithOverboundStats)) {
    if !COLLECT_UF_ARITH_OVERBOUND_STATS.with(std::cell::Cell::get) {
        return;
    }
    let stats = UF_ARITH_OVERBOUND_STATS.with(|c| {
        let mut stats = c.get();
        f(&mut stats);
        c.set(stats);
        stats
    });
    // Mirrored on EVERY recording rather than through a handle on a cadence,
    // because this decision point is reached a handful of times per query and
    // never inside a loop: there is no cadence to amortize, and republishing a
    // 28-byte `Copy` snapshot is cheaper than the `Arc` and `Mutex` a handle
    // would need. Reached only when collection is already on, so a default run
    // never gets here.
    crate::live_instruments::publish_live(
        crate::live_instruments::instrument::UF_OVERBOUND,
        stats,
        // Partial: the query has not returned, so the ladder below this
        // decision point may still run and change every field but `engaged`.
        crate::live_instruments::Sampled::InFlight,
    );
}

/// What the over-bound UF+arithmetic decision point concluded for one query.
enum OverboundOutcome {
    /// The eager Ackermann bound did not fire (or this query is not
    /// UF+arithmetic): in-bound dispatch, unchanged.
    NotEngaged,
    /// This is the dispatcher's answer.
    Answer(CheckResult),
    /// The ladder below this decision point should run.
    FallThrough,
}

/// The lazy CEGAR's probe configuration: the *remaining* budget at `deadline`,
/// less the ladder's reserve of `1/``UF_ARITH_LADDER_RESERVE_SHARE` of it.
/// Falls back to `config.timeout` when the caller set no deadline; an unbounded
/// configuration stays unbounded.
fn cegar_probe_budget(config: &SolverConfig, deadline: Option<Instant>) -> SolverConfig {
    let remaining = deadline
        .map(|d| d.saturating_duration_since(Instant::now()))
        .or(config.timeout);
    UF_ARITH_CEGAR_SLICE.apply(config, remaining)
}

/// The lazy CEGAR's slice: everything but the ladder's quarter.
const UF_ARITH_CEGAR_SLICE: LadderSlice =
    LadderSlice::all_but_reserve("uf-arith-lazy-overbound", UF_ARITH_LADDER_RESERVE_SHARE);

/// Runs the over-bound UF+arithmetic decision point under the resolved
/// [`UfArithOverboundPolicy`], recording both the route attempt and the
/// clock-free counters.
///
/// `deadline` is the dispatcher's **entry** deadline, so the probe arm's budget
/// and the ladder's remaining budget come out of one clock rather than two.
///
/// # Soundness
///
/// Every arm returns either a verdict the lazy CEGAR produced (its `sat` is
/// replayed against the original assertions inside
/// `check_with_function_consistency`, its `unsat` is a relaxation refutation) or
/// declines. Falling through cannot produce a wrong verdict: the routes below
/// re-derive their own answers, and the eager `check_with_uf_arithmetic` route
/// re-applies `refuse_oversized_ackermann` at its own entry (`combined.rs:86`),
/// so the O(k²) blow-up the bound exists to prevent is still refused.
///
/// # Errors
///
/// Propagates [`SolverError`] from the lazy route's IR builders / dispatcher.
fn dispatch_uf_arith_overbound(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    deadline: Option<Instant>,
    rec: &mut Recorder<'_>,
) -> Result<OverboundOutcome, SolverError> {
    if !(features.has_function && has_arithmetic_function(arena)) {
        return Ok(OverboundOutcome::NotEngaged);
    }
    if crate::euf::refuse_oversized_ackermann(arena, assertions, "UF+arithmetic").is_none() {
        // In-bound: unchanged dispatch, and the decision point is not "engaged"
        // so no counter moves.
        return Ok(OverboundOutcome::NotEngaged);
    }
    // The secondary (pathological-input) bounds are TERMINAL under every policy.
    // They are the case the eager bound exists for — a pair count above two
    // million, a DAG above two million nodes, or a term deeper than 65 536 — and
    // the ladder below recurses over the same assertion, so letting these fall
    // through would reintroduce exactly the blow-up the guard prevents. Falling
    // through is for the CEGAR's own inconclusive `Unknown`, not for a refusal
    // taken before it ran.
    if let Some(refusal) =
        crate::euf::refuse_pathological_for_lazy(arena, assertions, "UF+arithmetic")
    {
        note_uf_arith_overbound(|s| {
            s.engaged += 1;
            s.pathological_refusals += 1;
            s.terminal_unknown += 1;
        });
        with_recorder(rec, |t| match &refusal {
            CheckResult::Unknown(reason) => t.record_declined(
                "uf-arith-lazy-overbound",
                DeclineReason::from_unknown(reason),
            ),
            _ => unreachable!("refuse_pathological_for_lazy only ever refuses"),
        });
        return Ok(OverboundOutcome::Answer(refusal));
    }
    let policy = uf_arith_overbound_policy();
    if policy == UfArithOverboundPolicy::SkipCegar {
        note_uf_arith_overbound(|s| {
            s.engaged += 1;
            s.cegar_skipped += 1;
            s.fell_through += 1;
        });
        with_recorder(rec, |t| {
            t.record_declined("uf-arith-lazy-overbound", DeclineReason::NotApplicable);
        });
        return Ok(OverboundOutcome::FallThrough);
    }

    // `CegarTerminal` keeps the caller's arena (byte-identical to the behaviour
    // that arm names). `CegarProbe` runs on a CLONE, for the same reason
    // `dispatch_uf_arith_online` does: the CEGAR appends abstraction symbols and
    // congruence lemmas, and leaving them in the caller's arena would enlarge
    // every route the fall-through then runs. A `sat` model is keyed by
    // `SymbolId`, which the clone preserves, so returning it is sound.
    let terminal = policy == UfArithOverboundPolicy::CegarTerminal;
    let cegar_config = if terminal {
        config.clone()
    } else {
        cegar_probe_budget(config, deadline)
    };
    let mut scratch;
    let cegar_arena: &mut TermArena = if terminal {
        arena
    } else {
        scratch = arena.clone();
        &mut scratch
    };
    let Some(result) = crate::euf::try_lazy_arith_for_overbound(
        cegar_arena,
        assertions,
        &cegar_config,
        "UF+arithmetic",
    )?
    else {
        return Ok(OverboundOutcome::NotEngaged);
    };
    note_uf_arith_overbound(|s| s.engaged += 1);
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
    if !matches!(result, CheckResult::Unknown(_)) {
        note_uf_arith_overbound(|s| s.cegar_decided += 1);
        return Ok(OverboundOutcome::Answer(result));
    }
    note_uf_arith_overbound(|s| s.cegar_unknown += 1);
    // An array query already fell through before this change; keep that, and add
    // the probe arm's fall-through for everything else.
    if features.has_array || !terminal {
        note_uf_arith_overbound(|s| s.fell_through += 1);
        return Ok(OverboundOutcome::FallThrough);
    }
    note_uf_arith_overbound(|s| s.terminal_unknown += 1);
    Ok(OverboundOutcome::Answer(result))
}

/// The uninterpreted-function fast paths (online CDCL(T) EUF → offline EUF
/// enumeration → EUF + linear-arithmetic combination), split from
/// [`check_auto_dispatch`] for length. Returns `Some(verdict)` when one decides
/// the query (or the real-sorted-UF `Unknown` that must short-circuit), else
/// `Ok(None)` so the dispatcher falls through to the array / bit-blast tail.
/// Verdict logic is verbatim the inlined original; `rec` only annotates the
/// existing sites.
// 107/100 lines: a cohesive verbatim-inlined UF fast-path dispatcher; splitting
// it would obscure the fall-through verdict logic. (solver lane: refactor if desired.)
#[allow(clippy::too_many_lines)]
fn dispatch_uf_fast_paths(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    rec: &mut Recorder<'_>,
) -> Result<Option<CheckResult>, SolverError> {
    // ONE deadline for this whole dispatcher, taken at entry. The over-bound
    // UF+arithmetic probe below and the ladder after it both derive their
    // remaining budget from it, so a probe that spends half the budget leaves the
    // ladder the other half instead of restarting the clock (which is what
    // computing this after the probe would do).
    let entry_deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));

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
    //
    // WHAT HAPPENS TO ITS `Unknown` IS NOW A POLICY, NOT A CONSTANT
    // ([`UfArithOverboundPolicy`]). Returning it unconditionally — the historical
    // behaviour, kept as [`UfArithOverboundPolicy::CegarTerminal`] — made every
    // route below this point unreachable on any non-array UF+arithmetic query
    // with more than 64 congruence pairs, `dispatch_uf_arith_online` (our online
    // model-based EUF+LIA combination) included. See that enum's docs for the
    // measurement.
    match dispatch_uf_arith_overbound(arena, assertions, config, features, entry_deadline, rec)? {
        OverboundOutcome::NotEngaged | OverboundOutcome::FallThrough => {}
        OverboundOutcome::Answer(result) => return Ok(Some(result)),
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

    // One shared deadline for this UF ladder: each route below derives its own
    // internal deadline from its config's `timeout`, so passing the entry
    // config to consecutive routes re-spends the same wall-clock budget once
    // per route (measured at 2-3x the intended budget on large predicate
    // skeletons). Re-deriving the remaining timeout before each heavy route
    // keeps the whole ladder inside the caller's budget. It is the dispatcher's
    // ENTRY deadline, so an over-bound probe that already ran comes out of the
    // same budget rather than restarting the clock.
    let ladder_deadline = entry_deadline;

    // Try the **online** CDCL(T) decider on the backtrackable e-graph first: it
    // keeps one incremental congruence graph across the Boolean search and honors
    // the caller's timeout. Both its `sat` (replay-checked) and `unsat`
    // (congruence-conflict-derived) verdicts are sound. On `unknown` fall through
    // to the offline enumeration, then bit-blast.
    let Some(euf_online_config) = config_with_remaining_timeout(config, ladder_deadline) else {
        return Ok(None);
    };
    match crate::euf_egraph::check_qf_uf_online_cdclt(arena, euf_assertions, &euf_online_config) {
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
    let Some(euf_offline_config) = config_with_remaining_timeout(config, ladder_deadline) else {
        return Ok(None);
    };
    match crate::euf_egraph::check_qf_uf_with_config(arena, euf_assertions, &euf_offline_config) {
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
    // Ackermann elimination removes every `Apply` node but can leave a genuinely
    // mixed carrier-equality + LIA formula: its congruence implications relate
    // declared-sort argument equalities to integer result equalities. That is
    // still QF_UFLIA and the online combination handles it directly. Requiring
    // an applied arithmetic function here made the reduced query fall through to
    // an impossible carrier bit-blast. SAT remains replay-checked inside the
    // combination.
    if features.has_int
        && features.has_uninterpreted_sort
        && !features.has_function
        && let Some(result) =
            dispatch_uf_arith_online(arena, assertions, config, features, ladder_deadline, rec)?
    {
        return Ok(Some(result));
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
        if let Some(result) =
            dispatch_uf_arith_online(arena, assertions, config, features, ladder_deadline, rec)?
        {
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
    // This dispatcher is the TERMINAL rung of `dispatch_uf_fast_paths` for a
    // declared-sort, function-carrying, arithmetic-free query: `euf-online`,
    // `dispatch_ufbv_online` and `euf-offline` have all declined above it, and
    // nothing runs after it. So the congruence-pair bound whose whole purpose is
    // to stop this route stealing an enclosing search's budget has no enclosing
    // search to protect here, and the wall-clock budget it refuses to spend is
    // discarded rather than handed on (measured: 214 ms of 24 s on the QF_UF
    // parity losses). Pass the terminal-rung bound; the loop's own shared
    // deadline is what bounds its time.
    match crate::euf::check_qf_ufbv_lazy_with_pair_bound(
        &mut backend,
        arena,
        assertions,
        config,
        crate::euf::DECLARED_SORT_CEGAR_PAIRS_TERMINAL_RUNG,
    ) {
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
    UFBV_ONLINE_PROBE_SLICE.apply(config, config.timeout)
}

/// Divisor of the caller's budget the declared-sort `QF_UFBV` online probe may
/// spend. A HALF, not a reserve, and deliberately left as one: the eager
/// fallback below it computes a fresh deadline at entry, so this is a split
/// across two clocks rather than a share of one. The `QF_UFLIA` measurement
/// behind [`UF_ARITH_LADDER_RESERVE_SHARE`] says a half-budget split is the
/// wrong shape when the two routes share ONE clock; whether it is wrong here is
/// unmeasured, and this lane did not retune it.
const UFBV_ONLINE_PROBE_SHARE: u32 = 2;

/// The declared-sort `QF_UFBV` online probe's slice: half the caller's clock.
const UFBV_ONLINE_PROBE_SLICE: LadderSlice =
    LadderSlice::fraction("ufbv-online-probe", UFBV_ONLINE_PROBE_SHARE);

/// The first-refusal MBQI rung of the quantified effort ladder: 1/8 of the
/// remaining wall budget. Returns `None` for unbounded configurations — with no
/// clock to share there is no starvation to prevent, and the established
/// engine order (e-graph loop first) keeps byte-identical behavior.
fn mbqi_first_refusal_budget(config: &SolverConfig) -> Option<SolverConfig> {
    let timeout = config.timeout?;
    Some(MBQI_FIRST_REFUSAL_SLICE.apply(config, Some(timeout)))
}

/// Divisor of the remaining budget the first-refusal MBQI rung may spend.
const MBQI_FIRST_REFUSAL_SHARE: u32 = 8;

/// The first-refusal MBQI rung's slice: an eighth of what is left.
const MBQI_FIRST_REFUSAL_SLICE: LadderSlice =
    LadderSlice::fraction("mbqi-quick", MBQI_FIRST_REFUSAL_SHARE);

/// Divisor of the remaining budget the incremental e-graph quantifier retry may
/// spend, so the callers' later SAT-only stages are not starved.
const QINST_EGRAPH_RETRY_SHARE: u32 = 2;

/// The incremental e-graph quantifier retry's slice: half of what is left.
const QINST_EGRAPH_RETRY_SLICE: LadderSlice =
    LadderSlice::fraction("qinst-egraph-retry", QINST_EGRAPH_RETRY_SHARE);

/// Runs the bounded first-refusal MBQI rung. `Ok(Some(_))` carries only a
/// fully anchored verdict (a replay-checked `sat` or the refuter's `unsat`);
/// every other outcome — including an unsupported shape — declines with
/// `Ok(None)` so the established rungs below run unchanged.
fn mbqi_first_refusal(
    arena: &mut TermArena,
    assertions: &[TermId],
    original_assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<Option<CheckResult>, SolverError> {
    let t0 = Instant::now();
    let Some(quick_config) = config_with_remaining_timeout(config, deadline) else {
        return Ok(None);
    };
    let Some(quick_config) = mbqi_first_refusal_budget(&quick_config) else {
        return Ok(None);
    };
    // THROWAWAY CLONE isolation (same rationale as the uf_fmf probe above):
    // MBQI interns skolems and instantiation terms, and letting that traffic
    // leak into the shared arena measurably derails the e-graph refutation
    // downstream (measured: a 3.5 s e-graph `unsat` on a scored UF file became
    // a 24 s `unknown` with the polluted arena). Term/symbol IDs coincide
    // between the clone and the original, so an `unsat` on the clone refutes
    // the same assertion set, and a `sat` model is re-checked against the
    // ORIGINAL arena before it is accepted.
    match prove_unsat_by_mbqi(&mut arena.clone(), assertions, &quick_config) {
        Ok(CheckResult::Sat(model)) if crate::check_model(arena, original_assertions, &model)? => {
            qtrace("mbqi-quick", t0, "sat");
            Ok(Some(CheckResult::Sat(model)))
        }
        Ok(CheckResult::Unsat) => {
            qtrace("mbqi-quick", t0, "unsat");
            Ok(Some(CheckResult::Unsat))
        }
        // A first-refusal pass must not fail the whole solve: an unsupported
        // shape or an unchecked candidate falls through to the established
        // rungs.
        Ok(CheckResult::Sat(_) | CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {
            qtrace("mbqi-quick", t0, "declined");
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

/// Ceiling on the pre-LIA UF probe's slice: it is a quick screen, so its
/// usefulness does not scale with the clock.
const PRE_LIA_UF_PROBE_CEILING: Duration = Duration::from_millis(250);

/// Divisor of the caller's budget the pre-LIA UF probe may spend, before
/// [`PRE_LIA_UF_PROBE_CEILING`] caps it.
const PRE_LIA_UF_PROBE_SHARE: u32 = 10;

/// The pre-LIA UF probe's slice: `min(t/10, 250 ms)`.
const PRE_LIA_UF_PROBE_SLICE: LadderSlice = LadderSlice::capped_fraction(
    "uf-arith-overbound-pre-lia",
    PRE_LIA_UF_PROBE_SHARE,
    PRE_LIA_UF_PROBE_CEILING,
);

/// **Behaviour change, 2026-09-08**, the same one [`int_real_relax_budget`]
/// carries: a `timeout / 10` that rounded to zero used to hand this probe the
/// FULL timeout, which is the sharing policy inverted. It now clamps to
/// [`MIN_LADDER_SLICE`], differing from the old behaviour only under 10 ms.
fn pre_lia_uf_probe_budget(config: &SolverConfig) -> SolverConfig {
    PRE_LIA_UF_PROBE_SLICE.apply(config, config.timeout)
}

/// The **online** EUF + linear-arithmetic combination, tried *before* the eager
/// Ackermann route in `dispatch_uf_fast_paths`. Routes by sort — reals present
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
    ladder_deadline: Option<Instant>,
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
    //
    // The share is taken out of what is LEFT at `ladder_deadline`, not out of the
    // caller's original timeout: an over-bound query may already have spent half
    // its budget in the lazy-CEGAR probe above, and halving the original timeout
    // again there would let this route run past the caller's deadline.
    let probe_config = probe_budget(
        &config_with_remaining_timeout(config, ladder_deadline).unwrap_or_else(|| config.clone()),
    );
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

/// The **difference-logic** probe (`QF_IDL` / `QF_RDL`): when every relational
/// atom is a difference constraint `x - y ⋈ c` the query is decidable in
/// polynomial time by negative-cycle detection, and a negative cycle is a
/// *minimal* explanation — exactly what the generic linear-arithmetic cores do
/// badly here (measured: thousands of blocking rounds with cores in the
/// hundreds of literals on the `QF_IDL` residuals). It runs ahead of the
/// LIRA / NRA / LIA-DPLL chain because on its own fragment it dominates them.
///
/// **Conservative by construction.** [`crate::dl_online::try_check_qf_dl`]
/// returns `None` — leaving every route below to run byte-identically — unless
/// the *whole* query is single-sorted numeric plus a propositional skeleton the
/// encoder covers and every atom normalizes to `x - y ⋈ c` with unit
/// coefficients. A non-unit coefficient, a product, a `div`/`mod`, a mixed
/// `Int`/`Real` query, an uninterpreted application, a connective outside the
/// skeleton encoder, or any normalization overflow all decline. Every `sat` it
/// returns is replayed against the ORIGINAL assertions, and every theory
/// conflict is re-checked by `FarkasCertificate::verify` before it can become a
/// lemma.
///
/// Returns `Some(verdict)` only for a decision; a budget-exhausted or
/// non-replaying run returns `None` so the established routes still get their
/// reserved slice of the budget (see [`dl_probe_budget`]).
fn dispatch_difference_logic(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    rec: &mut Recorder<'_>,
) -> Option<CheckResult> {
    // Stage timing for the `--trace` `; dl-online …` line (opt-in — see
    // `crate::dl_online::DlOnlineStatsGuard`): the whole call is timed from
    // this single choke point rather than inside `try_check_qf_dl` itself,
    // so every one of its several early-return paths (a `?` on `scan_dl`, a
    // budget-exhausted `Some(timeout_result(..))`, …) is covered without
    // touching them individually. `QF_IDL`/`QF_RDL` route here as their
    // dominant engine and never enter the generic CDCL(T) driver at all
    // (docs/research/12-performance/bench-divisions-2026-09-07.md,
    // "First finding"), so this is currently their only stage instrument.
    let dl_start = crate::dl_online::dl_online_stats_collecting().then(Instant::now);
    let dl_result = crate::dl_online::try_check_qf_dl(
        arena,
        assertions,
        &dl_probe_budget(config),
        extended_dl_probe_timeout(config),
    );
    if let Some(start) = dl_start {
        crate::dl_online::record_dl_online_time(start.elapsed());
    }
    match dl_result {
        Some(result) => {
            with_recorder(rec, |t| t.record_result("dl-online", &result));
            match &result {
                CheckResult::Sat(_) | CheckResult::Unsat => return Some(result),
                // A budget-exhausted or non-replaying difference-logic run still
                // falls through to the established routes: the probe only ever
                // adds decisions.
                CheckResult::Unknown(_) => {}
            }
        }
        None => {
            with_recorder(rec, |t| {
                t.record_declined("dl-online", DeclineReason::NotApplicable);
            });
        }
    }
    None
}

/// The budget handed to the difference-logic probe: the caller's, minus a
/// reserved slice, so a probe that runs out of time still leaves the routes
/// *below* it enough budget to decide the query.
///
/// Without this reservation the probe is not a probe — it is a commitment. It
/// runs ahead of the whole linear-arithmetic chain, and a query that is
/// difference-shaped but hard for negative-cycle search would burn the entire
/// budget and hand the established routes zero milliseconds. That is measured,
/// not hypothetical: `QF_IDL/sal/lpsat/lpsat-goal-18` is decided `unsat` by
/// `lia-dpll` in 4.2 s, and an unreserved probe turned it into `unknown`.
///
/// The default reserve is `min(timeout / 4, 6 s)`: a quarter on tight budgets,
/// and a flat 6 s once the budget is large enough that a fixed slice is the
/// cheaper insurance. [`crate::dl_online::try_check_qf_dl`] may shorten that
/// maximum probe budget for a preregistered equality-heavy shape, but it may
/// never exceed it. The dispatcher therefore stays *strictly additive*.
pub(crate) fn dl_probe_budget(config: &SolverConfig) -> SolverConfig {
    DL_PROBE_SLICE.apply(config, config.timeout)
}

/// Ceiling on the slice held back for the routes below the difference-logic
/// probe.
const DL_FALLBACK_RESERVE: Duration = Duration::from_secs(6);

/// Divisor of the caller's budget held back for the routes below the
/// difference-logic probe, before [`DL_FALLBACK_RESERVE`] caps it. Named rather
/// than written as a `/ 4` at the call site so the registry can key an entry on
/// it: it is the same policy number as [`UF_ARITH_LADDER_RESERVE_SHARE`] and
/// `ABV_ONLINE_LADDER_RESERVE_SHARE`, and three copies of a quarter that
/// cannot be found by name is how a fourth gets hand-rolled.
const DL_LADDER_RESERVE_SHARE: u32 = 4;

/// The difference-logic probe's slice: everything but `min(t/4, 6 s)`.
const DL_PROBE_SLICE: LadderSlice =
    LadderSlice::all_but_capped_reserve("dl-online", DL_LADDER_RESERVE_SHARE, DL_FALLBACK_RESERVE);

/// Larger DL slice available only after the route's standard-budget scan
/// proves the query is in the preregistered large equality-heavy class.
pub(crate) fn extended_dl_probe_timeout(config: &SolverConfig) -> Option<Duration> {
    config.timeout.map(|t| DL_EXTENDED_PROBE_SLICE.slice_of(t))
}

/// Ceiling on the slice held back from the *extended* difference-logic probe.
const DL_EXTENDED_FALLBACK_RESERVE: Duration = Duration::from_secs(3);

/// Divisor of the caller's budget held back from the extended difference-logic
/// probe, before [`DL_EXTENDED_FALLBACK_RESERVE`] caps it.
const DL_EXTENDED_LADDER_RESERVE_SHARE: u32 = 8;

/// The extended difference-logic probe's slice: everything but `min(t/8, 3 s)`.
const DL_EXTENDED_PROBE_SLICE: LadderSlice = LadderSlice::all_but_capped_reserve(
    "dl-online-extended",
    DL_EXTENDED_LADDER_RESERVE_SHARE,
    DL_EXTENDED_FALLBACK_RESERVE,
);

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
    if let Some(result) = dispatch_difference_logic(arena, assertions, config, rec) {
        return Ok(result);
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
        let real_config = config_with_remaining_deadline(config, dispatch_deadline);
        if let Some(result) = dispatch_uf_nra(arena, assertions, &real_config, &features, rec)? {
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
        if has_nonlinear_real(arena, assertions)
            && let Some(result) = crate::nra_real_root::decide_real_poly_constraint(
                arena,
                assertions,
                dispatch_deadline,
            )?
        {
            // A `Some(Unknown)` from the exact real-root decider ends this branch
            // — `nra` below is never reached. That is deliberate (the decider has
            // already spent the work), but it also means an `unknown` it reports
            // is terminal for the real branch, so the ideal combination gets its
            // turn here rather than never. Strictly additive: only an `unknown`
            // is ever replaced, and only by a certificate-checked `unsat`.
            if matches!(result, CheckResult::Unknown(_))
                && let Some(decided) = dispatch_cas_ideal(arena, assertions, rec)
            {
                return Ok(decided);
            }
            with_recorder(rec, |t| t.record_result("nra-real-root", &result));
            return Ok(result);
        }
        with_recorder(rec, |t| {
            t.record_declined("nra-real-root", DeclineReason::NotApplicable);
        });
        // The exact real-root decider handles one shared variable exactly and a
        // two-variable component by resultants; a system of coupled multivariate
        // equations is past it. Try the ideal combination before handing the
        // query to the linear-abstraction relaxation, whose own decline text says
        // "this needs a nlsat/CAD engine".
        if let Some(result) = dispatch_cas_ideal(arena, assertions, rec) {
            return Ok(result);
        }
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
        if past_deadline(dispatch_deadline) {
            return Ok(CheckResult::Unknown(timeout_reason(
                "auto-dispatch timeout after exact real-polynomial route",
            )));
        }
        let nra_config = config_with_remaining_deadline(config, dispatch_deadline);
        match crate::nra::check_with_nra(arena, assertions, &nra_config) {
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
        if let Some(result) = dispatch_int_linear_refuters(
            arena,
            assertions,
            config,
            &features,
            dispatch_deadline,
            rec,
        )? {
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
        if let Some(result) =
            dispatch_abv_online(arena, assertions, config, &features, dispatch_deadline, rec)?
        {
            return Ok(result);
        }
        // ONE CLOCK for the array ladder. `abv-online-cdclt` above now keeps
        // all but a reserve of the dispatcher's entry deadline, and this route
        // runs on what is left of that same deadline rather than on a fresh
        // copy of the caller's full timeout. Handing it `config` unchanged is
        // what made the four measured `QF_ABV` files finish only inside the
        // harness watchdog's grace period: 24 s spent above plus a fresh 24 s
        // budget here is 48 s of a 24 s promise, and a hard external limit
        // would have taken all four.
        //
        // The `off` arm keeps the ORIGINAL config here, not the remaining
        // deadline, because it exists to reproduce the historical behaviour
        // exactly. An arm that gave the online route the whole budget AND then
        // handed this route what was left of it would leave the ladder zero
        // milliseconds — strictly worse than the code it is meant to be a
        // control for, and a mislabelled arm is a measurement of nothing.
        let ladder_config = match abv_online_reserve_policy() {
            AbvOnlineReservePolicy::WholeBudget => config.clone(),
            AbvOnlineReservePolicy::LadderReserve => {
                config_with_remaining_deadline(config, dispatch_deadline)
            }
        };
        if let Some(result) =
            dispatch_array_fast_paths(arena, assertions, &ladder_config, &features)?
        {
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
        return dispatch_nonlinear_int_tail(arena, assertions, config, dispatch_deadline, rec);
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

/// The fraction of the remaining wall-clock budget held back from
/// `abv-online-cdclt` for the array ladder underneath it.
///
/// **The route it governs used to take `config.timeout` in FULL.** It is the
/// first route every array query tries, and `array-fast-path` — the route
/// immediately below it — never saw a millisecond on any file the online search
/// could not decide. Measured 2026-09-08 over the committed 50-file `QF_ABV`
/// span-log sweep (`docs/research/12-performance/span-log-sweep-2026-09-08.md`,
/// shard `QF_ABV.json`), 24 s per file:
///
/// - on **four** files `abv-online-cdclt` spent 24.001–24.011 s of a 24 s budget,
///   declined, and `array-fast-path` then decided the file `sat` in
///   **0.007–0.174 s**. Those four are decided today only because the harness
///   watchdog's grace period outlasts the budget; under a hard external limit
///   they are losses;
/// - the ladder below never needed more than **2.898 s** on any file in the
///   sweep (the slowest `array-fast-path` decision), and its median decision
///   took 168 ms;
/// - `abv-online-cdclt` itself decided 24 of 47 files it entered, and its
///   **slowest decision was 5.723 s** — 8 of the 24 took over one second.
///
/// `4` is chosen against both of those bounds, the method
/// [`UF_ARITH_LADDER_RESERVE_SHARE`] paid four files to establish:
///
/// - it leaves the online route 18 s of a 24 s budget, **above every decision it
///   made** in the sweep (5.7 s, the slowest);
/// - it gives the ladder 6 s, about **twice** the slowest ladder decision
///   observed (2.9 s) and thirty-five times the median.
///
/// A reserve cannot recover a route that needs 99% of the clock, and nothing in
/// this population does — unlike `QF_UFLIA`, where `hash_uns_05_20` at 23.7 s of
/// 24 s was the named cost of the same change. If such a file exists outside
/// this sample it is the cost here too, and
/// [`AbvOnlineReservePolicy::WholeBudget`] is the arm that measures it.
const ABV_ONLINE_LADDER_RESERVE_SHARE: u32 = 4;

/// `abv-online-cdclt`'s slice: everything but the array ladder's quarter.
const ABV_ONLINE_SLICE: LadderSlice =
    LadderSlice::all_but_reserve("abv-online-cdclt", ABV_ONLINE_LADDER_RESERVE_SHARE);

/// What `abv-online-cdclt` is allowed to spend before the array ladder runs.
///
/// Selected by `AXEYUM_ABV_ONLINE_RESERVE` (`off` / `on`) so both arms are
/// runnable from one binary — the A/B protocol
/// `docs/research/12-performance/uf-arith-overbound-2026-09-08.md` had to
/// establish after an unpinned baseline mixed two binaries in one sweep.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbvOnlineReservePolicy {
    /// The historical behaviour: the online route receives the caller's whole
    /// wall-clock budget and the array ladder below it runs on whatever the
    /// harness's grace period leaves. Kept as a named arm so the change can be
    /// measured against it rather than only remembered.
    WholeBudget,
    /// The online route receives the remaining budget less the ladder's reserve
    /// (`1/``ABV_ONLINE_LADDER_RESERVE_SHARE`), and the ladder below runs on
    /// the reserve, out of the same clock. Default.
    LadderReserve,
}

impl AbvOnlineReservePolicy {
    /// The short name this policy is selected by and reported as.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::WholeBudget => "off",
            Self::LadderReserve => "on",
        }
    }
}

std::thread_local! {
    /// A per-thread override of the process policy, set by
    /// [`AbvOnlineReservePolicyGuard`]. The process policy is read once from the
    /// environment, so without this no test could exercise more than one arm.
    static ABV_ONLINE_RESERVE_OVERRIDE: std::cell::Cell<Option<AbvOnlineReservePolicy>> =
        const { std::cell::Cell::new(None) };
}

/// Forces `policy` on this thread for the lifetime of the guard, restoring the
/// previous setting on drop.
pub struct AbvOnlineReservePolicyGuard(Option<AbvOnlineReservePolicy>);

impl AbvOnlineReservePolicyGuard {
    /// Overrides the process policy on this thread.
    #[must_use]
    pub fn set(policy: AbvOnlineReservePolicy) -> Self {
        AbvOnlineReservePolicyGuard(ABV_ONLINE_RESERVE_OVERRIDE.with(|c| c.replace(Some(policy))))
    }
}

impl Drop for AbvOnlineReservePolicyGuard {
    fn drop(&mut self) {
        ABV_ONLINE_RESERVE_OVERRIDE.with(|c| c.set(self.0));
    }
}

/// The [`AbvOnlineReservePolicy`] in force on this thread: a live
/// [`AbvOnlineReservePolicyGuard`]'s choice, else the process policy resolved
/// once from `AXEYUM_ABV_ONLINE_RESERVE`. An unset or unrecognised value is the
/// default, so a typo degrades to the shipped behaviour rather than to an arm
/// nobody chose.
fn abv_online_reserve_policy() -> AbvOnlineReservePolicy {
    static RESOLVED: std::sync::OnceLock<AbvOnlineReservePolicy> = std::sync::OnceLock::new();
    if let Some(policy) = ABV_ONLINE_RESERVE_OVERRIDE.with(std::cell::Cell::get) {
        return policy;
    }
    *RESOLVED.get_or_init(
        || match std::env::var("AXEYUM_ABV_ONLINE_RESERVE").as_deref() {
            Ok("off") => AbvOnlineReservePolicy::WholeBudget,
            _ => AbvOnlineReservePolicy::LadderReserve,
        },
    )
}

/// The budget handed to `abv-online-cdclt`: the remaining clock at `deadline`
/// less the array ladder's reserve, or the caller's whole budget under
/// [`AbvOnlineReservePolicy::WholeBudget`].
///
/// `deadline` is the dispatcher's **entry** deadline, so this route's slice and
/// the ladder's remainder come out of one clock rather than two — the same
/// property `cegar_probe_budget` keeps, and the reason a route that spends its
/// share cannot also spend the ladder's.
fn abv_online_probe_budget(config: &SolverConfig, deadline: Option<Instant>) -> SolverConfig {
    if abv_online_reserve_policy() == AbvOnlineReservePolicy::WholeBudget {
        return config.clone();
    }
    let remaining = deadline
        .map(|d| d.saturating_duration_since(Instant::now()))
        .or(config.timeout);
    ABV_ONLINE_SLICE.apply(config, remaining)
}

fn dispatch_abv_online(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    features: &Features,
    deadline: Option<Instant>,
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
    let online_config = abv_online_probe_budget(config, deadline);
    let mut online_arena = arena.clone();
    match crate::ufbv_online::check_qf_aufbv_online_cdclt(
        &mut online_arena,
        assertions,
        &online_config,
    ) {
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

/// The two CAS refutation routes (ADR-0386), tried immediately after
/// `term-identity-refuter` and before any theory engine runs.
///
/// Both are exact, deterministic, and bounded by node/monomial ceilings rather
/// than a clock, and both hand their certificate to the independent checker in
/// [`crate::cas_certificate`] before returning — so they are cheap enough to sit
/// on the fast path and cannot return an unchecked `unsat`.
///
/// Declines are recorded, not silent, but **only when the route actually had a
/// candidate shape to work on** ([`CasOutcome::NoCandidate`] records nothing).
/// That keeps the trail diagnosable exactly where diagnosis is wanted — the past
/// bug this discipline comes from is the one documented on
/// [`record_nia_decline`], where an undecided `QF_NIA` query's trace showed only
/// `int-blast-ladder` — without appending two entries to the trace of every
/// unrelated query.
fn dispatch_cas_refuters(
    arena: &TermArena,
    assertions: &[TermId],
    features: &Features,
    rec: &mut Recorder<'_>,
) -> Option<CheckResult> {
    // Polynomial normalization only has purchase on integer/real arithmetic; a
    // pure Bool/BV/string query never enters, so the fast path pays one check.
    if !(features.has_int || features.has_real) {
        return None;
    }
    match crate::cas_poly::cas_identity_refutation(arena, assertions) {
        CasOutcome::Refuted(_) => {
            with_recorder(rec, |t| {
                t.record_decided("cas-identity-refuter", Verdict::Unsat);
            });
            return Some(CheckResult::Unsat);
        }
        CasOutcome::NoCandidate => {}
        CasOutcome::NotRefuted(why) => {
            record_cas_decline(
                rec,
                "cas-identity-refuter",
                DeclineReason::Incomplete(incomplete_reason(why)),
            );
        }
        CasOutcome::VerifierRejected => {
            record_cas_decline(
                rec,
                "cas-identity-refuter",
                DeclineReason::VerifierRejected(
                    "polynomial normal form disagreed with the independent expansion".to_owned(),
                ),
            );
        }
    }
    match crate::cas_poly::cas_int_units_refutation(arena, assertions) {
        CasOutcome::Refuted(_) => {
            with_recorder(rec, |t| {
                t.record_decided("cas-int-units", Verdict::Unsat);
            });
            Some(CheckResult::Unsat)
        }
        CasOutcome::NoCandidate => None,
        CasOutcome::NotRefuted(why) => {
            record_cas_decline(
                rec,
                "cas-int-units",
                DeclineReason::Incomplete(incomplete_reason(why)),
            );
            None
        }
        CasOutcome::VerifierRejected => {
            record_cas_decline(
                rec,
                "cas-int-units",
                DeclineReason::VerifierRejected(
                    "divisibility certificate failed its independent re-check".to_owned(),
                ),
            );
            None
        }
    }
}

/// The multivariate ideal / positivity refuter (ADR-0387).
///
/// Unlike the two ADR-0386 routes this one does **not** sit on the fast
/// pre-theory path. It computes a Gröbner basis, which costs milliseconds where
/// those routes cost microseconds, and it was measured taking over queries that
/// `nra-real-root` and `int-real-relax` already decide **faster** — `x + y = 3
/// ∧ x·y = 5` over `Real` was 0.96 ms via `nra-real-root` and 3.96 ms through
/// this route. So it is placed where those engines have already declined: after
/// `nra-real-root` on the real branch, and after `nia-bounded-blast` on the
/// nonlinear-integer tail, immediately before the width ladder whose answer on
/// these shapes is "no model within the bounded integer width", i.e. `unknown`.
///
/// The placement is the whole of the performance story: a query the existing
/// engines decide never reaches this route, and a query that reaches it was
/// going to be `unknown`.
fn dispatch_cas_ideal(
    arena: &TermArena,
    assertions: &[TermId],
    rec: &mut Recorder<'_>,
) -> Option<CheckResult> {
    match crate::cas_poly::cas_ideal_refutation(arena, assertions) {
        CasOutcome::Refuted(_) => {
            with_recorder(rec, |t| {
                t.record_decided("cas-ideal-refuter", Verdict::Unsat);
            });
            Some(CheckResult::Unsat)
        }
        CasOutcome::NoCandidate => None,
        CasOutcome::NotRefuted(why) => {
            record_cas_decline(
                rec,
                "cas-ideal-refuter",
                DeclineReason::Incomplete(incomplete_reason(why)),
            );
            None
        }
        CasOutcome::VerifierRejected => {
            record_cas_decline(
                rec,
                "cas-ideal-refuter",
                DeclineReason::VerifierRejected(
                    "ideal combination failed its independent re-check".to_owned(),
                ),
            );
            None
        }
    }
}

/// An [`UnknownReason`] carrying a CAS route's decline text.
fn incomplete_reason(detail: &str) -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: detail.to_owned(),
    }
}

/// Records a CAS route decline. Telemetry only — `rec` never participates in a
/// branch, so the verdict is independent of it.
fn record_cas_decline(rec: &mut Recorder<'_>, route: &'static str, reason: DeclineReason) {
    with_recorder(rec, |t| t.record_declined(route, reason));
}

/// Records that a `QF_NIA` route declined, with the reason the route reported.
///
/// Before this hook existed the three nonlinear-integer routes (`nia-square`,
/// `nia-linearize`, `nia-bounded-blast`) declined **silently**: a route trace on
/// an undecided `QF_NIA` query showed only `int-blast-ladder`, so diagnosing why the
/// query was never refuted took a dedicated route-tracing pass. Telemetry only —
/// `rec` never participates in a branch, so the verdict is unchanged.
fn record_nia_decline(rec: &mut Recorder<'_>, route: &'static str, why: Option<DeclineReason>) {
    let reason = why.unwrap_or(DeclineReason::NotApplicable);
    with_recorder(rec, |t| t.record_declined(route, reason));
}

/// The share of the caller's wall clock the real-relaxation refuter
/// (`int_real_relax::refute_int_via_real_relaxation`) is asked to stay inside:
/// **one sixth**, leaving the remaining five sixths for the nonlinear routes that
/// follow it. `None` (an unbounded caller budget) stays `None` — this only ever
/// divides an existing budget, never invents one.
const INT_REAL_RELAX_BUDGET_SHARE: u32 = 6;

/// The real-relaxation refuter's slice: one sixth of the caller's clock.
const INT_REAL_RELAX_SLICE: LadderSlice =
    LadderSlice::fraction("int-real-relax", INT_REAL_RELAX_BUDGET_SHARE);

/// `config` with the real-relaxation refuter's budget share applied.
///
/// **Behaviour change, 2026-09-08.** This used to return the caller's config
/// UNCHANGED — the full, unshrunk timeout — whenever `timeout / 6` rounded to
/// zero, so the sharing policy inverted itself at exactly the small-budget end
/// where starvation matters most (recorded as a FINDING against
/// `INT_REAL_RELAX_BUDGET_SHARE` in [`crate::config_registry`]). It now clamps
/// to [`MIN_LADDER_SLICE`], which differs from the old behaviour only for
/// budgets under 6 ms.
fn int_real_relax_budget(config: &SolverConfig) -> SolverConfig {
    INT_REAL_RELAX_SLICE.apply(config, config.timeout)
}

/// The pure-integer nonlinear tail of [`check_auto_dispatch`] (`features.has_int`
/// after the EUF/array fast paths). Split out for length; the verdict logic is
/// verbatim the inlined original, `rec` only annotates the existing sites.
fn dispatch_nonlinear_int_tail(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
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
        let mut why = None;
        if let Some(result) =
            crate::nia_square::decide_int_square_constraint_explained(arena, assertions, &mut why)?
        {
            with_recorder(rec, |t| t.record_result("nia-square", &result));
            return Ok(result);
        }
        record_nia_decline(rec, "nia-square", why);
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
        //
        // BUDGET SHARE. This refuter is a *fast path*, not the decider of record —
        // when it declines, `check_with_nia` below is the route that can actually
        // decide the query, and it needs wall clock to do it. Handing the refuter
        // the caller's whole `config.timeout` means a declining file spends 100% of
        // its budget here and `check_with_nia` is never entered at all; that is what
        // it did on 9 of the 12 `QF_NIA` parity files measured at the standard 24 s
        // budget. One sixth is what the probe lane measured as the point where the
        // refuter still lands its `unsat`s and the tail gets a usable remainder.
        //
        // ADR-0377 makes this a share of the caller's REMAINING absolute deadline,
        // not a fresh allowance. The NRA/CAD inner loops poll the same deadline;
        // after a decline the boundary check below prevents a subsequent route from
        // resetting the clock.
        let remaining_config = config_with_remaining_deadline(config, deadline);
        let relax_config = int_real_relax_budget(&remaining_config);
        let mut relax_why = None;
        if crate::int_real_relax::refute_int_via_real_relaxation(
            arena,
            assertions,
            &relax_config,
            &mut relax_why,
        )? {
            with_recorder(rec, |t| t.record_decided("int-real-relax", Verdict::Unsat));
            return Ok(CheckResult::Unsat);
        }
        // Recorded on the DECLINE too. A trace attempt's `elapsed` runs from the
        // previous recorded attempt, so without this row every second this route
        // spends is charged to `nia-linearize` below — measured at 4.04 s of the
        // 10.73 s that route was credited with on `QF_NIA` file 34, 2026-09-08.
        record_nia_decline(rec, "int-real-relax", relax_why);
        if past_deadline(deadline) {
            return Ok(CheckResult::Unknown(timeout_reason(
                "auto-dispatch timeout after nonlinear integer real relaxation",
            )));
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
        let mut why = None;
        let nia_config = config_with_remaining_deadline(config, deadline);
        if let Some(result) =
            crate::nia_linearize::check_with_nia(arena, assertions, &nia_config, &mut why)?
        {
            with_recorder(rec, |t| t.record_result("nia-linearize", &result));
            return Ok(result);
        }
        record_nia_decline(rec, "nia-linearize", why);
        if past_deadline(deadline) {
            return Ok(CheckResult::Unknown(timeout_reason(
                "auto-dispatch timeout after nonlinear integer linearization",
            )));
        }
        // **Bound-aware EXACT int-blast** (closes the QF_NIA UNSAT blind spot):
        // when every free `Int` variable is provably confined to a finite box,
        // blasting at a box-covering width is EXACT, so a bit-vector `Unsat` is a
        // genuine integer `Unsat` — the one thing the width ladder never trusts.
        // Gated on the all-bounded proof; see `decide_bounded_int_blast`.
        let mut why = None;
        let bounded_config = config_with_remaining_deadline(config, deadline);
        if let Some(result) =
            decide_bounded_int_blast_explained(arena, assertions, &bounded_config, &mut why)?
        {
            with_recorder(rec, |t| t.record_result("nia-bounded-blast", &result));
            return Ok(result);
        }
        record_nia_decline(rec, "nia-bounded-blast", why);
        // Last exact route before the width ladder, whose answer on an unbounded
        // nonlinear system is "no model within the bounded integer width 32",
        // i.e. `unknown`. The ideal combination needs no box at all.
        if let Some(result) = dispatch_cas_ideal(arena, assertions, rec) {
            return Ok(result);
        }
        if past_deadline(deadline) {
            return Ok(CheckResult::Unknown(timeout_reason(
                "auto-dispatch timeout after exact bounded integer blast",
            )));
        }
        let ladder_config = config_with_remaining_deadline(config, deadline);
        let result = dispatch_int_blast_width_ladder(arena, assertions, &ladder_config)?;
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
    crate::portfolio::stop_or_past_deadline(deadline)
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
    // A `WideIntConst` falls through to the `None` arm below: `IntInterval` is
    // an `i128` pair, a wider bound has no point in it, and saturating one would
    // be a WRONG bound rather than a coarse one (ADR-1702 slice 2).
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
        | TermNode::WideIntConst(_)
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
    // N-ary and unconditional, so this is a straight delegation; the shared
    // walker also drops the per-node `args.clone()` the recursive form needed to
    // release the arena borrow before recursing.
    crate::term_walk::flatten_op_spine(arena, term, out, Op::BoolOr);
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
///
/// # Why this is an explicit worklist and not native recursion
///
/// The `and` spine's depth is the source's: an SMT-LIB assertion written
/// `(and (and (and …) p) q)` nests once per conjunct, and the front door
/// reproduces that verbatim. A recursive flattener therefore **aborted** the
/// process with a stack overflow, which is strictly worse than an `unknown` —
/// the solver cannot report a first-class `unknown` and a harness reads the exit
/// as a crash (the failure mode fixed in `fcc8760d`). `work` is a stack, so
/// conjuncts are still collected left to right.
fn collect_top_conjuncts(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    let mut work = vec![term];
    while let Some(t) = work.pop() {
        match arena.node(t) {
            TermNode::App {
                op: Op::BoolAnd,
                args,
            } => work.extend(args.iter().rev().copied()),
            _ => out.push(t),
        }
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
fn decide_bounded_int_blast_explained(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    why: &mut Option<DeclineReason>,
) -> Result<Option<CheckResult>, SolverError> {
    // Steps 1–6: prove a finite, exactly-encodable box for every free Int
    // variable (shared with the certificate emitter `certify_bounded_int_blast`).
    let proven = match prove_int_box(arena, assertions) {
        IntBoxProof::Box(b) => b,
        // Contradictory direct bounds (`lo > hi`): UNSAT on these literals alone.
        IntBoxProof::TriviallyUnsat => return Ok(Some(CheckResult::Unsat)),
        IntBoxProof::Decline => {
            *why = Some(DeclineReason::NotApplicable);
            return Ok(None);
        }
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
    let enumerated =
        decide_int_box_by_evaluation(arena, assertions, &proven, MAX_INT_BOX_ENUM_CASES);
    if enumerated.is_none() {
        *why = Some(DeclineReason::Budget(
            "exact box blast declined and the proven int box exceeds the exhaustive-enumeration cap"
                .into(),
        ));
    }
    Ok(enumerated)
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
    let blast = match axeyum_rewrite::blast_integers(&mut scratch, &clamped, proven.width) {
        Ok(blast) => blast,
        // A DECLINE, not a failure — the same distinction the `IntBoxProof` match
        // above already draws. `int_blast` rejects an operator it has no faithful
        // finite encoding for (`int.pow2`, whose value is exponential in its
        // operand) *precisely so* the query falls through to a route that does
        // handle it, and it says so at the rejection site.
        //
        // Mapping every `IntBlastError` to a backend error turned that
        // fall-through into a hard stop. Measured on
        // `QF_NIA/cvc5-regress-clean/cli__regress0__nl__pow2-native-{2,7}.smt2`,
        // both declared `unsat` and both decided `unsat` by `check_auto` in
        // 0.13ms via `int-box-eval`: `produce_evidence` returned
        // `backend failure: int-blast failed: ... does not support operator IntPow2`.
        // The dominance audit recorded that as `solver-error` and
        // `smtcomp_cli --evidence` rendered it `unknown` — so a missing
        // CERTIFICATE was costing a verdict the solver already had.
        //
        // Other `IntBlastError`s stay errors: a constant that does not fit the
        // chosen width, or an invalid width, are wrong-configuration bugs here,
        // not statements that this route does not apply.
        Err(axeyum_rewrite::IntBlastError::UnsupportedOp(_)) => return Ok(None),
        Err(error) => {
            return Err(SolverError::Backend(format!("int-blast failed: {error}")));
        }
    };
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
/// Returns [`CheckResult::Unknown`] when a mathematically finite quantifier
/// domain exceeds the eager expansion budget. Returns
/// [`SolverError::Unsupported`] for a genuinely non-enumerable quantifier domain
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

    let expanded = match expand_quantifiers(arena, &replay_base) {
        Ok(expanded) => expanded,
        Err(QuantExpandError::UnsupportedDomain(
            sort @ (Sort::Bool | Sort::BitVec(_) | Sort::Float { .. }),
        )) => {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: format!(
                    "finite quantifier domain {sort} exceeds the eager expansion budget"
                ),
            }));
        }
        Err(QuantExpandError::UnsupportedDomain(sort)) => {
            return Err(SolverError::Unsupported(format!(
                "quantifier over non-enumerable domain {sort}"
            )));
        }
        Err(QuantExpandError::Ir(inner)) => {
            return Err(SolverError::Backend(inner.to_string()));
        }
    };

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

/// Maximum free integer symbols whose ground values the quantified-UF model
/// finder may complete before ordinary MBQI refinement (ADR-0360).
const MAX_MBQI_FREE_INT_SYMBOLS: usize = 2;

/// Maximum complete value pool used for each ADR-0360 free integer symbol.
const MAX_MBQI_FREE_INT_VALUES: usize = 16;

/// Maximum complete Cartesian product searched by ADR-0360.
const MAX_MBQI_FREE_INT_TUPLES: usize = 256;

/// Maximum candidate solves in ADR-0364's SAT-only finite-profile completion.
const MAX_MBQI_PROFILE_COMPLETION_ROUNDS: usize = 32;

/// Maximum exact source instances accumulated by ADR-0364.
const MAX_MBQI_PROFILE_COMPLETION_INSTANCES: usize = 32;

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

fn certify_mbqi_candidate(
    arena: &TermArena,
    assertions: &[TermId],
    universal_assertions: &[TermId],
    model: &Model,
) -> Result<Option<Model>, SolverError> {
    let (mut certified_model, certificates) = if let Some(certificates) =
        crate::mbqi_model_finder::certify_all_universals(arena, universal_assertions, model)
    {
        (model.clone(), certificates)
    } else if let Some(repaired) = crate::mbqi_model_finder::repair_and_certify_all_universals(
        arena,
        universal_assertions,
        model,
    ) {
        repaired
    } else {
        return Ok(None);
    };
    for certificate in certificates {
        certified_model.set_quantified_uf_model_sat_certificate(certificate);
    }
    crate::check_model(arena, assertions, &certified_model)
        .map(|accepted| accepted.then_some(certified_model))
}

/// Collects the one or two free `Int` symbols that occur in the exact assertion
/// sequence. Every leading universal binder is excluded; a non-`Int` free
/// scalar, no free scalar, or a wider symbol set makes ADR-0360 decline without
/// changing the ordinary MBQI path.
fn mbqi_free_int_symbols(
    arena: &TermArena,
    assertions: &[TermId],
    universal_assertions: &[TermId],
) -> Option<Vec<SymbolId>> {
    let mut binders = BTreeSet::new();
    for &assertion in universal_assertions {
        let mut matrix = assertion;
        let mut saw_binder = false;
        while let TermNode::App {
            op: Op::Forall(binder),
            args,
        } = arena.node(matrix)
        {
            let [body] = &**args else {
                return None;
            };
            saw_binder = true;
            binders.insert(*binder);
            matrix = *body;
        }
        if !saw_binder || has_quantifier(arena, &[matrix]) {
            return None;
        }
    }

    let mut symbols = BTreeSet::new();
    for &assertion in assertions {
        collect_term_symbols(arena, assertion, &mut symbols);
    }
    symbols.retain(|symbol| !binders.contains(symbol));
    if symbols.is_empty() || symbols.len() > MAX_MBQI_FREE_INT_SYMBOLS {
        return None;
    }
    if symbols
        .iter()
        .any(|symbol| arena.symbol(*symbol).1 != Sort::Int)
    {
        return None;
    }
    Some(symbols.into_iter().collect())
}

fn mbqi_free_int_base_values(
    arena: &TermArena,
    assertions: &[TermId],
    initial_model: &Model,
) -> BTreeSet<i128> {
    let mut values = BTreeSet::from([0]);
    for (_, value) in initial_model.iter() {
        if let Value::Int(integer) = value {
            values.insert(integer);
        }
    }

    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::IntConst(integer) => {
                values.insert(*integer);
            }
            TermNode::App { args, .. } => {
                stack.extend(args.iter().rev().copied());
            }
            _ => {}
        }
    }
    values
}

fn mbqi_close_free_int_value_pool(mut values: BTreeSet<i128>) -> Option<Vec<i128>> {
    let bases: Vec<i128> = values.iter().copied().collect();
    for base in bases {
        if let Some(predecessor) = base.checked_sub(1) {
            values.insert(predecessor);
        }
        if let Some(successor) = base.checked_add(1) {
            values.insert(successor);
        }
    }
    (values.len() <= MAX_MBQI_FREE_INT_VALUES).then(|| values.into_iter().collect())
}

/// Builds ADR-0360's complete, deterministic free-Int value pool. Overflow is
/// a decline, never truncation: truncating would make the measured Cartesian
/// search depend on insertion order rather than the preregistered policy.
fn mbqi_free_int_value_pool(
    arena: &TermArena,
    assertions: &[TermId],
    initial_model: &Model,
) -> Option<Vec<i128>> {
    mbqi_close_free_int_value_pool(mbqi_free_int_base_values(arena, assertions, initial_model))
}

/// Extends ADR-0360's raw scalar pool with ADR-0361's untrusted values from the
/// initial candidate: integer UF results and exact-source integer subterms that
/// evaluate without any quantified binder. The same neighbour closure and cap
/// apply once to the combined raw pool.
fn mbqi_evaluated_free_int_value_pool(
    arena: &TermArena,
    assertions: &[TermId],
    initial_model: &Model,
) -> Option<Vec<i128>> {
    let mut values = mbqi_free_int_base_values(arena, assertions, initial_model);
    for (_, function) in initial_model.functions() {
        if let Value::Int(integer) = function.default_value() {
            values.insert(integer);
        }
        for (_, value) in function.value_entries() {
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
        if let TermNode::App { op, args } = arena.node(term) {
            if let Op::Forall(symbol) | Op::Exists(symbol) = op {
                binders.insert(*symbol);
            }
            stack.extend(args.iter().rev().copied());
        }
    }

    let assignment = initial_model.to_assignment();
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

    mbqi_close_free_int_value_pool(values)
}

/// Clones `config` with only the time remaining under the caller-owned MBQI
/// deadline. `None` means the shared deadline has already expired.
fn mbqi_config_with_deadline(
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Option<SolverConfig> {
    let mut candidate = config.clone();
    if let Some(deadline) = deadline {
        let remaining = deadline.checked_duration_since(Instant::now())?;
        if remaining.is_zero() {
            return None;
        }
        candidate.timeout = Some(remaining);
    }
    Some(candidate)
}

#[derive(Default)]
struct MbqiGroundComponent {
    assertions: Vec<TermId>,
    symbols: BTreeSet<SymbolId>,
    functions: BTreeSet<FuncId>,
}

fn mbqi_ground_dependencies(
    arena: &TermArena,
    assertion: TermId,
) -> (BTreeSet<SymbolId>, BTreeSet<FuncId>) {
    let mut symbols = BTreeSet::new();
    let mut functions = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![assertion];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(symbol) => {
                symbols.insert(*symbol);
            }
            TermNode::App { op, args } => {
                if let Op::Apply(function) = op {
                    functions.insert(*function);
                }
                stack.extend(args.iter().copied());
            }
            _ => {}
        }
    }
    (symbols, functions)
}

fn mbqi_disjoint_ground_components(
    arena: &TermArena,
    assertions: &[TermId],
) -> Vec<MbqiGroundComponent> {
    let mut components: Vec<MbqiGroundComponent> = Vec::new();
    for &assertion in assertions {
        let (mut symbols, mut functions) = mbqi_ground_dependencies(arena, assertion);
        let mut component_assertions = vec![assertion];
        let mut index = 0;
        while index < components.len() {
            if symbols.is_disjoint(&components[index].symbols)
                && functions.is_disjoint(&components[index].functions)
            {
                index += 1;
                continue;
            }
            let component = components.remove(index);
            component_assertions.extend(component.assertions);
            symbols.extend(component.symbols);
            functions.extend(component.functions);
            index = 0;
        }
        component_assertions.sort_unstable();
        components.push(MbqiGroundComponent {
            assertions: component_assertions,
            symbols,
            functions,
        });
    }
    components
}

/// Gives MBQI a ground seed when a conjunction contains independent theory
/// components that the monolithic dispatcher cannot yet combine. Each connected
/// component is decided normally; `unsat` transfers from any conjunct, while
/// `sat` is returned only after the merged source model replays every exact
/// ground assertion. This is candidate generation, not quantified evidence.
fn check_mbqi_ground_seed(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    let original = check_auto(arena, assertions, config);
    if matches!(&original, Ok(CheckResult::Sat(_) | CheckResult::Unsat)) {
        return original;
    }

    let components = mbqi_disjoint_ground_components(arena, assertions);
    if components.len() < 2 {
        return original;
    }
    let mut combined = Model::new();
    for component in components {
        let Some(component_config) = mbqi_config_with_deadline(config, deadline) else {
            return original;
        };
        match check_auto(arena, &component.assertions, &component_config) {
            Ok(CheckResult::Unsat) => return Ok(CheckResult::Unsat),
            Ok(CheckResult::Sat(model)) => {
                for symbol in component.symbols {
                    if let Some(value) = model.get(symbol) {
                        combined.set(symbol, value);
                    }
                }
                for function in component.functions {
                    if let Some(value) = model.function(function) {
                        combined.set_function(function, value.clone());
                    }
                }
                for (numerator, quotient) in model.real_div_zeros() {
                    combined.set_real_div_zero(numerator, quotient);
                }
            }
            Ok(CheckResult::Unknown(_)) | Err(_) => return original,
        }
    }
    if matches!(crate::check_model(arena, assertions, &combined), Ok(true)) {
        Ok(CheckResult::Sat(combined))
    } else {
        original
    }
}

fn mbqi_source_shape_supported(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut saw_universal = false;
    for &assertion in assertions {
        if matches!(
            arena.node(assertion),
            TermNode::App {
                op: Op::Forall(_),
                ..
            }
        ) {
            saw_universal = true;
            if crate::quant_uf_model_sat_cert::quantified_uf_model_functions(arena, assertion)
                .is_none()
            {
                return false;
            }
        } else if has_quantifier(arena, &[assertion]) {
            return false;
        }
    }
    saw_universal
}

/// ADR-0360's SAT-only free-Int candidate completion. Temporary equalities are
/// submitted only to the untrusted quantifier-free model generator. Any result
/// other than a candidate that independently certifies and replays against the
/// exact original assertion sequence is ignored.
fn complete_mbqi_free_int_candidate(
    arena: &mut TermArena,
    assertions: &[TermId],
    universal_assertions: &[TermId],
    ground: &[TermId],
    initial_model: &Model,
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Option<Model> {
    let symbols = mbqi_free_int_symbols(arena, assertions, universal_assertions)?;
    let values = mbqi_free_int_value_pool(arena, assertions, initial_model)?;
    complete_mbqi_free_int_candidate_for_values(
        arena,
        assertions,
        universal_assertions,
        ground,
        &symbols,
        &values,
        config,
        deadline,
    )
}

#[allow(clippy::too_many_arguments)]
fn complete_mbqi_free_int_candidate_for_values(
    arena: &mut TermArena,
    assertions: &[TermId],
    universal_assertions: &[TermId],
    ground: &[TermId],
    symbols: &[SymbolId],
    values: &[i128],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Option<Model> {
    let tuple_count = values
        .len()
        .checked_pow(u32::try_from(symbols.len()).ok()?)?;
    if tuple_count > MAX_MBQI_FREE_INT_TUPLES {
        return None;
    }

    for tuple_index in 0..tuple_count {
        let candidate_config = mbqi_config_with_deadline(config, deadline)?;
        let mut remaining_index = tuple_index;
        let mut chosen = vec![0; symbols.len()];
        for slot in (0..symbols.len()).rev() {
            chosen[slot] = values[remaining_index % values.len()];
            remaining_index /= values.len();
        }

        let mut candidate_query = ground.to_vec();
        for (&symbol, &value) in symbols.iter().zip(&chosen) {
            let variable = arena.var(symbol);
            let constant = arena.int_const(value);
            let fixing = arena.eq(variable, constant).ok()?;
            candidate_query.push(fixing);
        }
        let Ok(CheckResult::Sat(candidate_model)) =
            check_auto(arena, &candidate_query, &candidate_config)
        else {
            continue;
        };
        if past_deadline(deadline) {
            return None;
        }
        if let Ok(Some(certified)) =
            certify_mbqi_candidate(arena, assertions, universal_assertions, &candidate_model)
        {
            return Some(certified);
        }
    }
    None
}

/// ADR-0361's additive evaluated-value retry. The ADR-0360 pool has already
/// been exhausted before this is called, so an identical or overflowing pool
/// declines without repeating work.
fn complete_mbqi_evaluated_free_int_candidate(
    arena: &mut TermArena,
    assertions: &[TermId],
    universal_assertions: &[TermId],
    ground: &[TermId],
    initial_model: &Model,
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Option<Model> {
    let symbols = mbqi_free_int_symbols(arena, assertions, universal_assertions)?;
    let baseline_values = mbqi_free_int_value_pool(arena, assertions, initial_model)?;
    let values = mbqi_evaluated_free_int_value_pool(arena, assertions, initial_model)?;
    if values == baseline_values {
        return None;
    }
    complete_mbqi_free_int_candidate_for_values(
        arena,
        assertions,
        universal_assertions,
        ground,
        &symbols,
        &values,
        config,
        deadline,
    )
}

/// Accepts only a fixed-query SAT candidate that independently replays against
/// the exact unfixed assertion sequence. In particular, fixed-query UNSAT does
/// not transfer: the temporary scalar equality strengthened that query.
fn replay_one_level_fixed_mbqi_candidate(
    arena: &TermArena,
    assertions: &[TermId],
    result: CheckResult,
) -> Result<Option<Model>, SolverError> {
    let CheckResult::Sat(model) = result else {
        return Ok(None);
    };
    crate::check_model(arena, assertions, &model).map(|accepted| accepted.then_some(model))
}

/// ADR-0363's additive source-guided default repair. Candidate values and
/// defaults remain untrusted; every universal receives an independent
/// finite-profile certificate and the exact full source is replayed here.
fn complete_mbqi_source_guided_default_candidate(
    arena: &TermArena,
    assertions: &[TermId],
    universal_assertions: &[TermId],
    initial_model: &Model,
    deadline: Option<Instant>,
) -> Result<Option<Model>, SolverError> {
    let Some((mut repaired, certificates)) =
        crate::mbqi_model_finder::repair_and_certify_all_universals_with_source_int_values(
            arena,
            assertions,
            universal_assertions,
            initial_model,
            deadline,
        )
    else {
        return Ok(None);
    };
    for certificate in certificates {
        repaired.set_quantified_uf_model_sat_certificate(certificate);
    }
    crate::check_model(arena, assertions, &repaired).map(|accepted| accepted.then_some(repaired))
}

/// ADR-0364's post-decline SAT-only finite-profile completion loop. Every QF
/// solve and source-definition rewrite is untrusted candidate generation; only
/// the independent finite-profile certificates plus exact full replay can
/// return a model.
fn complete_mbqi_profile_guided_candidate(
    arena: &mut TermArena,
    assertions: &[TermId],
    universal_assertions: &[TermId],
    ground: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Option<Model> {
    let [universal] = universal_assertions else {
        return None;
    };
    let TermNode::App {
        op: Op::Forall(binder),
        args,
    } = arena.node(*universal)
    else {
        return None;
    };
    let [body] = &**args else {
        return None;
    };
    if arena.symbol(*binder).1 != Sort::Int {
        return None;
    }
    let binder = *binder;
    let body = *body;
    let universal = *universal;
    let mut instances = Vec::new();

    for _ in 0..MAX_MBQI_PROFILE_COMPLETION_ROUNDS {
        let candidate_config = mbqi_config_with_deadline(config, deadline)?;
        let mut query = ground.to_vec();
        query.extend(instances.iter().copied());
        let Ok(CheckResult::Sat(candidate)) = check_auto(arena, &query, &candidate_config) else {
            return None;
        };
        if past_deadline(deadline) {
            return None;
        }
        let candidate = crate::mbqi_model_finder::complete_profile_guided_int_candidate(
            arena, universal, &candidate,
        )?;

        if let Some(certificates) = crate::mbqi_model_finder::certify_all_universals(
            arena,
            universal_assertions,
            &candidate,
        ) {
            let mut certified = candidate.clone();
            for certificate in certificates {
                certified.set_quantified_uf_model_sat_certificate(certificate);
            }
            if !past_deadline(deadline)
                && matches!(crate::check_model(arena, assertions, &certified), Ok(true))
            {
                return Some(certified);
            }
        }

        let falsifier = crate::quant_uf_model_sat_cert::first_quantified_uf_model_falsifier(
            arena, universal, &candidate,
        )?;
        let constant = value_to_const(arena, &falsifier)?;
        let variable = arena.var(binder);
        let replacements = HashMap::from([(variable, constant)]);
        let instance = replace_subterms(arena, body, &replacements, &mut HashMap::new()).ok()?;
        if !push_mbqi_profile_completion_instance(&mut instances, instance) {
            return None;
        }
    }
    None
}

fn push_mbqi_profile_completion_instance(instances: &mut Vec<TermId>, instance: TermId) -> bool {
    if instances.len() >= MAX_MBQI_PROFILE_COMPLETION_INSTANCES || instances.contains(&instance) {
        return false;
    }
    instances.push(instance);
    true
}

/// ADR-0362's structurally one-level, first-candidate fixed-query retry. The
/// inner MBQI entry is invoked with this retry disabled, so the shared deadline
/// is not the only recursion bound. Only one exact-source free `Int` and the
/// first ordered evaluated value are admitted; broader scalar search remains a
/// one-shot ADR-0360/0361 mechanism.
#[allow(clippy::too_many_arguments)]
fn complete_mbqi_one_level_fixed_candidate(
    arena: &mut TermArena,
    assertions: &[TermId],
    universal_assertions: &[TermId],
    initial_model: &Model,
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<Option<Model>, SolverError> {
    let Some(symbols) = mbqi_free_int_symbols(arena, assertions, universal_assertions) else {
        return Ok(None);
    };
    let [symbol] = symbols.as_slice() else {
        return Ok(None);
    };
    let Some(value) = mbqi_evaluated_free_int_value_pool(arena, assertions, initial_model)
        .and_then(|values| values.into_iter().next())
    else {
        return Ok(None);
    };

    let Some(candidate_config) = mbqi_config_with_deadline(config, deadline) else {
        return Ok(None);
    };
    let variable = arena.var(*symbol);
    let constant = arena.int_const(value);
    let fixing = arena.eq(variable, constant)?;
    let mut fixed_assertions = assertions.to_vec();
    fixed_assertions.push(fixing);
    let result = prove_unsat_by_mbqi_inner(arena, &fixed_assertions, &candidate_config, false)?;
    replay_one_level_fixed_mbqi_candidate(arena, assertions, result)
}

/// Model-based quantifier instantiation (MBQI): a refutation loop for top-level
/// universals over infinite domains. Each round decides `ground ∧ instances`; on
/// a `sat` candidate, every single-binder universal `∀x. body` is checked against
/// the model at the values the model assigns (its candidate instantiation set), and any
/// instance the model **falsifies** — a consequence of the universal that the
/// model violates — is added, blocking that model. `unsat` of the augmented
/// (still-implied) query transfers soundly; if no universal can be refined the
/// result is `unknown`. A leading multi-binder block gets one SAT-only finite-
/// profile candidate attempt before this loop and otherwise falls back to
/// E-matching.
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
    prove_unsat_by_mbqi_inner(arena, assertions, config, true)
}

#[allow(clippy::too_many_lines)]
fn prove_unsat_by_mbqi_inner(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    allow_outer_candidate_retries: bool,
) -> Result<CheckResult, SolverError> {
    // Split into ground assertions and top-level universal prefixes. The
    // refutation loop below remains single-binder. Multi-binder prefixes get a
    // separately checked SAT-only candidate attempt, then defer to E-matching.
    let mut ground: Vec<TermId> = Vec::new();
    let mut universals: Vec<(axeyum_ir::SymbolId, TermId)> = Vec::new();
    let mut universal_assertions: Vec<TermId> = Vec::new();
    let mut has_multi_binder_prefix = false;
    for &a in assertions {
        if matches!(
            arena.node(a),
            TermNode::App {
                op: Op::Forall(_),
                ..
            }
        ) {
            let mut prefix = Vec::new();
            let mut matrix = a;
            while let TermNode::App {
                op: Op::Forall(sym),
                args,
            } = arena.node(matrix)
            {
                let [body] = &**args else {
                    return prove_unsat_by_ematching(arena, assertions, config);
                };
                prefix.push(*sym);
                matrix = *body;
            }
            if has_quantifier(arena, &[matrix]) {
                return prove_unsat_by_ematching(arena, assertions, config);
            }
            if prefix.len() == 1 {
                universals.push((prefix[0], matrix));
            } else {
                has_multi_binder_prefix = true;
            }
            universal_assertions.push(a);
        } else if has_quantifier(arena, &[a]) {
            return prove_unsat_by_ematching(arena, assertions, config);
        } else {
            ground.push(a);
        }
    }
    if universal_assertions.is_empty() {
        // No top-level universal to instantiate; defer to the trigger fallback.
        return prove_unsat_by_ematching(arena, assertions, config);
    }

    if has_multi_binder_prefix {
        match check_auto(arena, &ground, config)? {
            CheckResult::Sat(model) => {
                if let Some(model) =
                    certify_mbqi_candidate(arena, assertions, &universal_assertions, &model)?
                {
                    return Ok(CheckResult::Sat(model));
                }
            }
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(_) => {}
        }
        return prove_unsat_by_ematching(arena, assertions, config);
    }
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());

    // Honor the wall-clock budget and a deterministic instance cap: a universal whose
    // instantiation generates ever-deeper ground terms (e.g. `∀x.(x≤y ∨ x≥y+1)`) can
    // grow the per-round `check_auto` without bound, so the loop must degrade to a
    // graceful `Unknown`, never spin (the "unknown is never an error / never hang" rule).
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let mut instances: Vec<TermId> = Vec::new();
    let mut initial_ground_model = None;
    for round in 0..MAX_MBQI_ROUNDS {
        if past_deadline(deadline) || instances.len() > MAX_MBQI_INSTANCES {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "MBQI: instantiation budget (time or instance count) exhausted".to_owned(),
            }));
        }
        let mut query = ground.clone();
        query.extend(instances.iter().copied());
        // The query is now quantifier-free (ground + instances).
        let result = check_mbqi_ground_seed(arena, &query, config, deadline)?;
        let CheckResult::Sat(model) = result else {
            // `unsat` (sound — instances are implied) or `unknown` transfers.
            return Ok(result);
        };
        if round == 0 {
            initial_ground_model = Some(model.clone());
        }
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
        if let Some(model) =
            certify_mbqi_candidate(arena, assertions, &universal_assertions, &model)?
        {
            return Ok(CheckResult::Sat(model));
        }
        // ADR-0362: after the initial candidate itself fails certification,
        // deepen only the first ordered evaluated value for one source Int. The
        // inner entry disables this retry, and a decline continues into the
        // complete ADR-0360 search and every established refutation route.
        if round == 0
            && allow_outer_candidate_retries
            && let Some(model) = complete_mbqi_one_level_fixed_candidate(
                arena,
                assertions,
                &universal_assertions,
                &model,
                config,
                deadline,
            )?
        {
            return Ok(CheckResult::Sat(model));
        }
        // ADR-0360: on the initial ground candidate only, search the complete
        // bounded product of one/two relevant free-Int assignments. The fixing
        // equalities guide only QF model generation; every accepted result is
        // certified and replayed against `assertions` without those fixings.
        if round == 0
            && let Some(model) = complete_mbqi_free_int_candidate(
                arena,
                assertions,
                &universal_assertions,
                &ground,
                &model,
                config,
                deadline,
            )
        {
            return Ok(CheckResult::Sat(model));
        }
        // ADR-0363: only after ADR-0362 and ADR-0360 decline, augment the
        // established default-only repair with exact-source integer values.
        // This runs once on the outer initial candidate; the inner fixed-query
        // invocation disables it together with the recursive retry.
        if round == 0
            && allow_outer_candidate_retries
            && let Some(model) = complete_mbqi_source_guided_default_candidate(
                arena,
                assertions,
                &universal_assertions,
                &model,
                deadline,
            )?
        {
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
            // family may still refute via compound terms. Only after that
            // established route also declines does ADR-0361 spend the remaining
            // shared deadline on its evaluated-value SAT-only retry. This keeps
            // the new search from delaying any pre-existing MBQI/E-matching
            // decision.
            let ematching = prove_unsat_by_ematching(arena, assertions, config)?;
            if matches!(ematching, CheckResult::Unknown(_))
                && let Some(initial_model) = &initial_ground_model
                && let Some(model) = complete_mbqi_evaluated_free_int_candidate(
                    arena,
                    assertions,
                    &universal_assertions,
                    &ground,
                    initial_model,
                    config,
                    deadline,
                )
            {
                return Ok(CheckResult::Sat(model));
            }
            // ADR-0364: only after ordinary MBQI, E-matching, and ADR-0361
            // decline, spend the original deadline's remaining time on exact
            // finite-profile counterexamples. The helper is SAT-only and is
            // disabled in ADR-0362's inner invocation so prior retry behavior
            // and recursion depth remain unchanged.
            if matches!(ematching, CheckResult::Unknown(_))
                && allow_outer_candidate_retries
                && let Some(model) = complete_mbqi_profile_guided_candidate(
                    arena,
                    assertions,
                    &universal_assertions,
                    &ground,
                    config,
                    deadline,
                )
            {
                return Ok(CheckResult::Sat(model));
            }
            return Ok(ematching);
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
    let deadline = config
        .timeout
        .and_then(|timeout| Instant::now().checked_add(timeout));
    let instantiation = instantiate_with_triggers(arena, assertions)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    if !instantiation.residual_quantifier {
        return decide_instantiation(arena, &instantiation, config);
    }
    // A residual quantifier used to end the attempt here. Rewriting to NNF,
    // Skolemizing the existential-in-force quantifiers, and hoisting the
    // surviving universals to the front puts them where trigger instantiation can
    // see them. This is the largest measured gap in UF: 126 of the 159
    // declared-status files in the 300-file slice declined exactly here.
    // `AXEYUM_NESTED_QUANT` (default off) swaps the flat prefix for the nesting-
    // preserving layout, which keeps each surviving universal where it occurred
    // so the instantiation driver can give it its own body-derived triggers.
    let skolemized = crate::quant_skolemize::skolemize_assertions_with_layout(
        arena,
        assertions,
        crate::quant_skolemize::configured_layout(),
    )?;
    if !skolemized.changed {
        if std::env::var_os("AXEYUM_QPROBE").is_some() {
            eprintln!("QPROBE ematch skolemize-unchanged (residual before skolemize)");
        }
        return decide_instantiation(arena, &instantiation, config);
    }
    let retried = instantiate_with_triggers(arena, &skolemized.assertions)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    if std::env::var_os("AXEYUM_QPROBE").is_some() {
        eprintln!(
            "QPROBE ematch retried residual={} instantiated={}",
            retried.residual_quantifier, retried.instantiated
        );
    }
    // Measured shape (the whole residual bucket on the scored UF corpus): the
    // skolemizer succeeds on every assertion, and the retry is blocked ONLY by
    // prenex chains whose hoisted variable count makes the cartesian instance
    // product exceed `CHAIN_INSTANCE_CAP` — those chains are left as `forall`s,
    // `residual_quantifier` comes back true, and the whole query was declined
    // even though every other assertion instantiated fine. The one-shot
    // cartesian retry is the wrong tool for those chains (a measured 366-
    // conjunct instantiation blob also just times out in dispatch); the
    // incremental e-graph loop is the machinery built for them — multi-pattern
    // joins instead of cartesian products, interleaved quantifier-free ground
    // refutation checks, round/deadline discipline. It never saw these files
    // usefully before because it ran only on the ORIGINAL non-prenex
    // assertions, whose nested quantifiers reduce its instances to junk the
    // QF-subset filter drops. Unsat-only: the loop's refutation of the
    // skolemized set transfers back through skolemization; any other outcome
    // falls through to the established decline. Half the remaining budget, so
    // the callers' later SAT-only stages are not starved.
    // What the e-matching loop said when it gave up, kept so the caller is told
    // the OPERATIVE stop rather than a shape message. Measured 2026-09-09 on
    // `bench-results/parity-losses-20260908/UF.txt`: on 26 of the 32 files the
    // loop stops at its accumulated-ground ceiling
    // (`e-matching: ground-term count budget exhausted`) or at its final
    // refutation check, and the reason the CLI then printed was
    // `decide_instantiation`'s "query has quantifiers instantiation does not
    // reach (nested, existential, or non-top-level)" -- which is a claim about
    // the query's SHAPE, and the shape is not what stopped these runs. The
    // skolemizer reached every one of them (`AXEYUM_QPROBE` reports zero
    // `skolem-bail`), so the printed reason sent every reader looking at the
    // wrong subsystem. It costs one `Option` to say what actually happened.
    let mut loop_decline: Option<UnknownReason> = None;
    if retried.residual_quantifier
        && let Some(remaining_config) = config_with_remaining_timeout(config, deadline)
    {
        let loop_config =
            QINST_EGRAPH_RETRY_SLICE.apply(&remaining_config, remaining_config.timeout);
        let probe = std::env::var_os("AXEYUM_QPROBE").is_some();
        let started = Instant::now();
        // The skolemized set alone, NOT its union with the originals: the
        // union was measured strictly worse (doubling the universal partition
        // with the originals' junk-instance chains drove ground to its cap by
        // round 10 and LOST a refutation the skolemized-only run finds).
        let loop_result = crate::qinst_egraph::prove_quantified_unsat_via_egraph(
            arena,
            &skolemized.assertions,
            &loop_config,
        )?;
        if probe {
            eprintln!(
                "QPROBE skolemized-egraph budget={:?} elapsed={:?} result={}",
                loop_config.timeout,
                started.elapsed(),
                match &loop_result {
                    CheckResult::Unsat => "unsat",
                    CheckResult::Sat(_) => "sat",
                    CheckResult::Unknown(r) => &r.detail,
                }
            );
        }
        match loop_result {
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => loop_decline = Some(reason),
            CheckResult::Sat(_) => {}
        }
    }
    // Skolemization preserves satisfiability, not equivalence, so only `unsat`
    // transfers back to the original query. In particular the "no universal was
    // weakened, so the result is exact" shortcut inside `decide_instantiation`
    // must NOT be allowed to hand back a `sat` here: that model interprets Skolem
    // symbols the original does not contain, so it could not replay against it.
    match decide_instantiation(arena, &retried, config)? {
        CheckResult::Unsat => Ok(CheckResult::Unsat),
        CheckResult::Sat(_) => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: "skolemized query is satisfiable; satisfiability does not transfer \
                     back through skolemization"
                .to_owned(),
        })),
        // The loop's own decline wins over the residual-shape message: it ran,
        // and it is the thing that gave up. `decide_instantiation`'s shape
        // decline is kept for the case where the loop never ran at all (no
        // remaining budget, or no residual quantifier to hand it), because
        // there the shape IS the reason.
        CheckResult::Unknown(reason) => Ok(CheckResult::Unknown(loop_decline.unwrap_or(reason))),
    }
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
    for t in &ites {
        let TermNode::App { args, .. } = arena.node(*t) else {
            continue;
        };
        let (c, a, b) = (args[0], args[1], args[2]);
        let sort = arena.sort_of(*t);
        let sym = arena
            // `check_auto` can be called repeatedly on the same arena while a
            // quantified search checks different ground slices. A call-local
            // ordinal (`!ite_0`, `!ite_1`, ...) aliases unrelated ITEs from
            // different slices and becomes a sort conflict when their result
            // sorts differ. The arena term id is stable and globally unique
            // within that arena, while repeated lifting of the same ITE still
            // reuses the same helper.
            .declare_internal(&format!("!ite_{}", t.index()), sort)
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

/// One frame of the explicit post-order walk in [`fold_to_real_rec`].
enum FoldToRealStep {
    /// Visit `t`: memo-hit, or schedule its children then its own rebuild.
    Enter(TermId),
    /// Rebuild `t` from children that are guaranteed to be in the memo already.
    Build(TermId),
}

/// Bottom-up `to_real` fold over one assertion.
///
/// # Why this is an explicit worklist and not native recursion
///
/// [`fold_to_real_sums`] runs on **every** query the auto-dispatcher sees — a
/// pure `QF_BV` query included, where the fold is the identity — and the walk's
/// recursion depth is the term DAG's *depth*, not its size. Native recursion
/// therefore aborted the whole process with a stack overflow on deep BV
/// operand chains: nine scored `QF_BV/sage/app7` benchmarks in
/// `bench-results/parity-lists/QF_BV.txt` died in `fold_to_real_rec` (confirmed
/// by backtrace) before any BV route was ever reached, and all nine decide
/// `unsat` in 8-16 s of the 24 s budget once the depth limit is gone.
///
/// A stack overflow is strictly worse than an `unknown`: it is an abort, so the
/// solver cannot report a first-class `unknown` and a harness reads it as a
/// crash. The memo keeps the walk linear in DAG size regardless.
fn fold_to_real_rec(
    arena: &mut TermArena,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> Result<TermId, axeyum_ir::IrError> {
    let mut work = vec![FoldToRealStep::Enter(term)];
    while let Some(step) = work.pop() {
        let t = match step {
            FoldToRealStep::Enter(t) => {
                if memo.contains_key(&t) {
                    continue;
                }
                let TermNode::App { args, .. } = arena.node(t) else {
                    // Leaves (constants, variables) fold to themselves.
                    memo.insert(t, t);
                    continue;
                };
                let args = args.clone();
                // `Build(t)` sits *below* its children, so every descendant is
                // in the memo by the time it pops.
                work.push(FoldToRealStep::Build(t));
                work.extend(args.iter().rev().map(|a| FoldToRealStep::Enter(*a)));
                continue;
            }
            FoldToRealStep::Build(t) => t,
        };
        // A shared subterm can be scheduled by several parents; the first
        // rebuild wins and the rest are memo hits.
        if memo.contains_key(&t) {
            continue;
        }
        let result = {
            let TermNode::App { op, args } = arena.node(t) else {
                unreachable!("Build is only pushed for App nodes")
            };
            let (op, args) = (*op, args.clone());
            let mut new_args = Vec::with_capacity(args.len());
            for arg in &args {
                new_args.push(memo[arg]);
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
        };
        memo.insert(t, result);
    }
    Ok(memo[&term])
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
            {
                // Split out of the let-chain so the *refusal* has a body. Above
                // the link width the coercion is left unlinked and the query is
                // handed on with a weaker encoding — a mode change with no
                // branch a caller can observe, which is exactly the population
                // `note_crossed` exists for.
                if hi - lo > MAX_COERCION_LINK {
                    crate::config_registry::note_crossed(
                        "crates/axeyum-solver/src/auto.rs::MAX_COERCION_LINK",
                        u64::try_from(hi - lo).unwrap_or(u64::MAX),
                        u64::try_from(MAX_COERCION_LINK).unwrap_or(u64::MAX),
                    );
                } else {
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
    /// Any integer constant outside the `i128` reference range
    /// (`TermNode::WideIntConst`, ADR-1702 slice 2).
    ///
    /// This is the OPT-IN POINT. ADR-1702 made arbitrary-precision arithmetic a
    /// per-route decision rather than a property of the type, because `i128`
    /// exhaustion is load-bearing for one population of consumers and a
    /// liability for another. The same discipline applies to a wide integer
    /// *literal*: no route claims it today, so `wide_int_admission` declines
    /// with a named reason. A route that opts in is named there.
    has_wide_int: bool,
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
            has_wide_int: false,
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
            if matches!(arena.node(term), TermNode::WideIntConst(_)) {
                features.has_wide_int = true;
            }
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
            Sort::BitVec(_) | Sort::RoundingMode | Sort::Float { .. } => {
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

/// The cross-thread half of the over-bound UF+arithmetic instrument.
///
/// Kept beside the recording site rather than in an integration suite because
/// the property under test is exactly that `note_uf_arith_overbound` publishes:
/// reaching this decision point from a real query needs a `QF_UFLIA` file that
/// trips the eager Ackermann bound, which would test the dispatcher's admission
/// arithmetic rather than the mirror.
#[cfg(test)]
mod uf_overbound_live_tests {
    use super::{UfArithOverboundStats, UfArithOverboundStatsGuard, note_uf_arith_overbound};
    use crate::live_instruments::{LiveInstruments, Sampled, install, instrument};

    /// The property: a counter recorded by a query that has NOT returned is
    /// readable from another thread, and is labelled partial.
    ///
    /// Before the mirror this instrument published nowhere until its guard
    /// dropped, so a watchdog kill lost it entirely — and a nonzero
    /// `terminal_unknown` on a division we lose is precisely the signal the
    /// counter exists for.
    #[test]
    fn a_recording_reaches_the_board_before_the_guard_drops() {
        let board = LiveInstruments::new();
        let _live = install(&board);
        let guard = UfArithOverboundStatsGuard::enable();
        assert!(
            board
                .sample::<UfArithOverboundStats>(instrument::UF_OVERBOUND)
                .is_none(),
            "arming collection publishes nothing: an absent reading has to stay \
             distinguishable from a recorded zero"
        );

        note_uf_arith_overbound(|stats| {
            stats.engaged += 1;
            stats.terminal_unknown += 1;
        });

        let sample = board
            .sample::<UfArithOverboundStats>(instrument::UF_OVERBOUND)
            .expect("the recording site mirrors onto the board");
        assert_eq!(sample.value.engaged, 1);
        assert_eq!(sample.value.terminal_unknown, 1);
        assert_eq!(
            sample.sampled,
            Sampled::InFlight,
            "the query has not returned, so the ladder below this decision point \
             may still run and change every field but `engaged`"
        );

        // Dropping the guard is this instrument's only COMPLETE publish point:
        // its fields accumulate across the whole solve rather than being lifted
        // at a stage boundary, so that is the one moment they stop moving.
        drop(guard);
        let done = board
            .sample::<UfArithOverboundStats>(instrument::UF_OVERBOUND)
            .expect("the guard publishes on drop");
        assert_eq!(done.sampled, Sampled::Complete);
        assert!(
            done.sequence > sample.sequence,
            "the complete reading is published after the partial one, which is \
             how a reader orders them: {done:?} vs {sample:?}"
        );
    }

    /// Off by default: with no board installed, the recording site publishes
    /// nothing and costs one thread-local read. A test that only ever ran WITH
    /// a board could not tell a mirror from an unconditional publish.
    #[test]
    fn recording_without_a_board_publishes_nothing() {
        let board = LiveInstruments::new();
        let _guard = UfArithOverboundStatsGuard::enable();
        note_uf_arith_overbound(|stats| stats.engaged += 1);
        assert!(
            board
                .sample::<UfArithOverboundStats>(instrument::UF_OVERBOUND)
                .is_none(),
            "a board nobody installed receives nothing"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn difference_logic_probe_preserves_the_fallback_slice() {
        let cases = [
            (Duration::ZERO, Duration::ZERO),
            (Duration::from_secs(3), Duration::from_millis(2_250)),
            (Duration::from_secs(12), Duration::from_secs(9)),
            (Duration::from_secs(24), Duration::from_secs(18)),
            (Duration::from_secs(60), Duration::from_secs(54)),
        ];
        for (timeout, expected_probe) in cases {
            let config = SolverConfig::new().with_timeout(timeout);
            assert_eq!(dl_probe_budget(&config).timeout, Some(expected_probe));
        }
        assert_eq!(dl_probe_budget(&SolverConfig::new()).timeout, None);
    }

    #[test]
    fn extended_difference_logic_probe_retains_a_nonzero_fallback_slice() {
        let cases = [
            (Duration::ZERO, Duration::ZERO),
            (Duration::from_secs(3), Duration::from_millis(2_625)),
            (Duration::from_secs(12), Duration::from_millis(10_500)),
            (Duration::from_secs(24), Duration::from_secs(21)),
            (Duration::from_secs(60), Duration::from_secs(57)),
        ];
        for (timeout, expected_probe) in cases {
            let config = SolverConfig::new().with_timeout(timeout);
            assert_eq!(extended_dl_probe_timeout(&config), Some(expected_probe));
        }
        assert_eq!(extended_dl_probe_timeout(&SolverConfig::new()), None);
    }

    /// A deep `and` spine must not blow the stack in the top-conjunct scan.
    ///
    /// `collect_top_conjuncts` reads the unconditional facts off an assertion on
    /// the dispatch path, and its walk depth is the conjunction's nesting depth
    /// — which an SMT-LIB source controls directly. A natively recursive walk
    /// aborted the process on a 20k-conjunct source spine (found by backtrace),
    /// so a regression aborts the test binary rather than failing quietly.
    #[test]
    fn collect_top_conjuncts_survives_a_deep_and_spine() {
        const DEPTH: usize = 100_000;
        let mut arena = TermArena::new();
        let p = arena.declare("deep_conj_p", Sort::Bool).unwrap();
        let leaf = arena.var(p);
        let mut acc = leaf;
        for _ in 0..DEPTH {
            acc = arena.and(acc, leaf).unwrap();
        }

        let mut out = Vec::new();
        collect_top_conjuncts(&arena, acc, &mut out);
        assert_eq!(out.len(), DEPTH + 1);
        assert!(out.iter().all(|&c| c == leaf));
    }

    /// A deep BV operand chain must not blow the stack in the `to_real` fold.
    ///
    /// `fold_to_real_sums` runs on **every** query the auto-dispatcher sees,
    /// so a native-recursion walk made the process abort with a stack overflow
    /// on deep pure-BV terms — before any BV route was reached. Nine scored
    /// `QF_BV/sage/app7` parity benchmarks died exactly here; each decides
    /// `unsat` well inside the 24 s budget once the depth limit is gone.
    ///
    /// The chain depth is far past what any recursive frame survives on the
    /// test harness's default thread stack, so a regression aborts the test
    /// binary rather than failing quietly.
    #[test]
    fn fold_to_real_survives_a_deep_bv_chain() {
        const DEPTH: usize = 100_000;
        let mut arena = TermArena::new();
        let x = arena.declare("deep_x", Sort::BitVec(8)).unwrap();
        let mut acc = arena.var(x);
        for i in 0..DEPTH {
            let k = arena.bv_const(8, (i % 251) as u128).unwrap();
            acc = arena.bv_add(acc, k).unwrap();
        }
        let zero = arena.bv_const(8, 0).unwrap();
        let assertion = arena.eq(acc, zero).unwrap();

        // Pure BV carries no `to_real`, so the fold is the identity — the point
        // is that it *terminates* rather than aborting the process.
        let folded = fold_to_real_sums(&mut arena, &[assertion]).unwrap();
        assert_eq!(folded, vec![assertion]);
    }

    /// The iterative walk must still perform the folds it exists for:
    /// `to_real(a) + to_real(b)` collapses to one coercion, and a coercion of
    /// a ground integer folds to a real constant.
    #[test]
    fn fold_to_real_still_collapses_coerced_sums() {
        let mut arena = TermArena::new();
        let i = arena.declare("fold_i", Sort::Int).unwrap();
        let j = arena.declare("fold_j", Sort::Int).unwrap();
        let (iv, jv) = (arena.var(i), arena.var(j));
        let (ri, rj) = (
            arena.int_to_real(iv).unwrap(),
            arena.int_to_real(jv).unwrap(),
        );
        let sum = arena.real_add(ri, rj).unwrap();

        // `to_real(3)` is a coercion of a ground integer: it folds to `3.0`.
        let three = arena.int_const(3);
        let r_three = arena.int_to_real(three).unwrap();
        let cmp = arena.real_le(sum, r_three).unwrap();

        let folded = fold_to_real_sums(&mut arena, &[cmp]).unwrap();
        assert_eq!(folded.len(), 1);
        let TermNode::App { op, args } = arena.node(folded[0]) else {
            panic!("expected an application");
        };
        assert_eq!(*op, Op::RealLe);
        let (lhs, rhs) = (args[0], args[1]);
        // Left: one `to_real` over an integer sum, not a sum of two coercions.
        assert!(matches!(
            arena.node(lhs),
            TermNode::App {
                op: Op::IntToReal,
                ..
            }
        ));
        // Right: the ground coercion became a real constant.
        assert!(matches!(arena.node(rhs), TermNode::RealConst(_)));
    }

    #[test]
    fn negated_quantified_implication_exposes_counterexample_witness() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("counterexample_f", &[Sort::Int], Sort::Int)
            .unwrap();

        let x = arena.declare("counterexample_x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let f_x = arena.apply(function, &[xv]).unwrap();
        let antecedent_body = arena.int_gt(f_x, xv).unwrap();
        let antecedent = arena.forall(x, antecedent_body).unwrap();

        let y = arena.declare("counterexample_y", Sort::Int).unwrap();
        let yv = arena.var(y);
        let minus_y = arena.int_neg(yv).unwrap();
        let f_minus_y = arena.apply(function, &[minus_y]).unwrap();
        let minus_f_minus_y = arena.int_neg(f_minus_y).unwrap();
        let f_y = arena.apply(function, &[yv]).unwrap();
        let consequent_body = arena.int_lt(minus_f_minus_y, f_y).unwrap();
        let consequent = arena.forall(y, consequent_body).unwrap();
        let implication = arena.implies(antecedent, consequent).unwrap();
        let theorem_counterexample = arena.not(implication).unwrap();

        let normalized =
            normalize_top_level_quantified_counterexamples(&mut arena, &[theorem_counterexample])
                .unwrap();
        assert_eq!(normalized.len(), 2);
        assert!(matches!(
            arena.node(normalized[0]),
            TermNode::App {
                op: Op::Forall(_),
                ..
            }
        ));
        assert!(matches!(
            arena.node(normalized[1]),
            TermNode::App {
                op: Op::Exists(_),
                ..
            }
        ));

        let config = SolverConfig::new().with_timeout(Duration::from_secs(1));
        assert_eq!(
            solve(&mut arena, &[theorem_counterexample], &config).unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    fn negated_quantified_implication_near_miss_is_not_refuted() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("counterexample_near_miss_f", &[Sort::Int], Sort::Int)
            .unwrap();

        let x = arena
            .declare("counterexample_near_miss_x", Sort::Int)
            .unwrap();
        let xv = arena.var(x);
        let f_x = arena.apply(function, &[xv]).unwrap();
        let antecedent_body = arena.int_gt(f_x, xv).unwrap();
        let antecedent = arena.forall(x, antecedent_body).unwrap();

        let y = arena
            .declare("counterexample_near_miss_y", Sort::Int)
            .unwrap();
        let yv = arena.var(y);
        let f_y = arena.apply(function, &[yv]).unwrap();
        let one = arena.int_const(1);
        let y_plus_one = arena.int_add(yv, one).unwrap();
        let stronger_body = arena.int_gt(f_y, y_plus_one).unwrap();
        let stronger = arena.forall(y, stronger_body).unwrap();
        let implication = arena.implies(antecedent, stronger).unwrap();
        let counterexample = arena.not(implication).unwrap();

        let normalized =
            normalize_top_level_quantified_counterexamples(&mut arena, &[counterexample]).unwrap();
        let skolemized = skolemize_top_existentials(&mut arena, &normalized).unwrap();
        let config = SolverConfig::new().with_timeout(Duration::from_secs(1));
        assert!(matches!(
            prove_quantified_unsat_via_egraph(&mut arena, &skolemized, &config).unwrap(),
            CheckResult::Unknown(_)
        ));
    }

    #[test]
    fn top_level_negated_universal_exposes_counterexample_witness() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("negated_universal_f", &[Sort::Int], Sort::Int)
            .unwrap();
        let x = arena.declare("negated_universal_x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let f_x = arena.apply(function, &[xv]).unwrap();
        let axiom_body = arena.eq(f_x, xv).unwrap();
        let axiom = arena.forall(x, axiom_body).unwrap();

        let y = arena.declare("negated_universal_y", Sort::Int).unwrap();
        let yv = arena.var(y);
        let f_y = arena.apply(function, &[yv]).unwrap();
        let goal_body = arena.eq(f_y, yv).unwrap();
        let goal = arena.forall(y, goal_body).unwrap();
        let counterexample = arena.not(goal).unwrap();

        let config = SolverConfig::new().with_timeout(Duration::from_secs(1));
        assert_eq!(
            solve(&mut arena, &[axiom, counterexample], &config).unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    fn ite_lifting_is_collision_free_across_repeated_mixed_sort_slices() {
        let mut arena = TermArena::new();
        let condition = arena.bool_var("ite_slice_condition").unwrap();
        let first_sort = Sort::Uninterpreted(arena.declare_uninterpreted_sort("IteSliceFirst"));
        let second_sort = Sort::Uninterpreted(arena.declare_uninterpreted_sort("IteSliceSecond"));

        let first_then = arena.declare("first_then", first_sort).unwrap();
        let first_else = arena.declare("first_else", first_sort).unwrap();
        let first_then = arena.var(first_then);
        let first_else = arena.var(first_else);
        let first_ite = arena.ite(condition, first_then, first_else).unwrap();
        let first_assertion = arena.eq(first_ite, first_then).unwrap();

        let second_then = arena.declare("second_then", second_sort).unwrap();
        let second_else = arena.declare("second_else", second_sort).unwrap();
        let second_then = arena.var(second_then);
        let second_else = arena.var(second_else);
        let second_ite = arena.ite(condition, second_then, second_else).unwrap();
        let second_assertion = arena.eq(second_ite, second_then).unwrap();

        lift_uninterpreted_sort_ite(&mut arena, &[first_assertion]).expect("first slice must lift");
        lift_uninterpreted_sort_ite(&mut arena, &[second_assertion])
            .expect("a later mixed-sort slice must mint a distinct helper");

        // Re-lifting an identical slice remains stable and reuses its helper.
        lift_uninterpreted_sort_ite(&mut arena, &[first_assertion])
            .expect("the same ITE must remain reusable");
    }

    #[test]
    fn quantified_ground_subset_refutation_ignores_only_quantified_conjuncts() {
        let mut arena = TermArena::new();
        let x = arena.int_var("ground_subset_x").unwrap();
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let x_is_zero = arena.eq(x, zero).unwrap();
        let x_is_one = arena.eq(x, one).unwrap();

        let binder = arena.declare("ground_subset_binder", Sort::Int).unwrap();
        let binder_variable = arena.var(binder);
        let quantified_body = arena.eq(binder_variable, binder_variable).unwrap();
        let quantified = arena.forall(binder, quantified_body).unwrap();
        let mut assertions = vec![x_is_zero, x_is_one];
        assertions.extend(std::iter::repeat_n(quantified, 32));
        let config = SolverConfig::new().with_timeout(Duration::from_secs(1));

        assert!(
            ground_subset_refutes_quantified_query(&mut arena, &assertions, &config).unwrap(),
            "the contradictory unconditional ground subset refutes the full query"
        );

        let mut satisfiable = vec![x_is_zero];
        satisfiable.extend(std::iter::repeat_n(quantified, 32));
        assert!(
            !ground_subset_refutes_quantified_query(&mut arena, &satisfiable, &config).unwrap(),
            "a satisfiable ground subset says nothing about the quantified query"
        );
    }

    #[test]
    fn mbqi_free_int_symbol_policy_uses_exact_source_and_excludes_binders() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("scalar_policy_f", &[Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("scalar_policy_x", Sort::Int).unwrap();
        let first = arena.declare("scalar_policy_first", Sort::Int).unwrap();
        let second = arena.declare("scalar_policy_second", Sort::Int).unwrap();
        let binder_variable = arena.var(binder);
        let first_variable = arena.var(first);
        let second_variable = arena.var(second);
        let application = arena.apply(function, &[binder_variable]).unwrap();
        let sum = arena.int_add(first_variable, second_variable).unwrap();
        let body = arena.eq(application, sum).unwrap();
        let universal = arena.forall(binder, body).unwrap();
        assert_eq!(
            mbqi_free_int_symbols(&arena, &[universal], &[universal]),
            Some(vec![first, second])
        );

        let third = arena.declare("scalar_policy_third", Sort::Int).unwrap();
        let zero = arena.int_const(0);
        let third_variable = arena.var(third);
        let third_ground = arena.int_ge(third_variable, zero).unwrap();
        assert!(
            mbqi_free_int_symbols(&arena, &[universal, third_ground], &[universal]).is_none(),
            "more than two exact-source free Int symbols must decline"
        );

        let real = arena.declare("scalar_policy_real", Sort::Real).unwrap();
        let real_zero = arena.real_const(Rational::zero());
        let real_variable = arena.var(real);
        let real_ground = arena.real_ge(real_variable, real_zero).unwrap();
        assert!(
            mbqi_free_int_symbols(&arena, &[universal, real_ground], &[universal]).is_none(),
            "a free non-Int source symbol must decline"
        );
    }

    #[test]
    fn mbqi_free_int_value_pool_is_complete_neighbor_closed_or_declines() {
        let mut arena = TermArena::new();
        let symbol = arena.declare("scalar_pool_y", Sort::Int).unwrap();
        let variable = arena.var(symbol);
        let seven = arena.int_const(7);
        let assertion = arena.int_le(variable, seven).unwrap();
        let mut model = Model::new();
        model.set(symbol, Value::Int(5));
        assert_eq!(
            mbqi_free_int_value_pool(&arena, &[assertion], &model),
            Some(vec![-1, 0, 1, 4, 5, 6, 7, 8])
        );

        let mut overflow_assertions = Vec::new();
        for value in (0_i128..=18).step_by(3) {
            let constant = arena.int_const(value);
            overflow_assertions.push(arena.int_le(variable, constant).unwrap());
        }
        assert!(
            mbqi_free_int_value_pool(&arena, &overflow_assertions, &Model::new()).is_none(),
            "the neighbor-closed pool must decline instead of truncating"
        );
    }

    #[test]
    fn mbqi_evaluated_value_pool_uses_uf_results_and_ground_source_only() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("evaluated_pool_f", &[Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("evaluated_pool_x", Sort::Int).unwrap();
        let scalar = arena.declare("evaluated_pool_y", Sort::Int).unwrap();
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

        let interpretation =
            axeyum_ir::FuncValue::constant_value(vec![Sort::Int], Sort::Int, Value::Int(5))
                .define_value(&[Value::Int(2)], Value::Int(9));
        let mut model = Model::new();
        model.set(binder, Value::Int(100));
        model.set(scalar, Value::Int(2));
        model.set_function(function, interpretation);

        assert_eq!(
            mbqi_evaluated_free_int_value_pool(&arena, &[universal, ground], &model),
            Some(vec![-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 99, 100, 101])
        );
        assert!(
            !mbqi_evaluated_free_int_value_pool(&arena, &[universal, ground], &model)
                .unwrap()
                .contains(&300),
            "the evaluable-looking binder product must not enter the ground pool"
        );
    }

    #[test]
    fn mbqi_candidate_config_honors_expired_shared_deadline() {
        assert!(mbqi_config_with_deadline(&SolverConfig::new(), Some(Instant::now())).is_none());
    }

    #[test]
    fn mbqi_one_level_fixed_retry_is_guarded_and_replays_unfixed_seed_111_shape() {
        let mut arena = TermArena::new();
        let f = arena
            .declare_fun("one_level_f", &[Sort::Int], Sort::Int)
            .unwrap();
        let g = arena
            .declare_fun("one_level_g", &[Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("one_level_x", Sort::Int).unwrap();
        let scalar = arena.declare("one_level_y", Sort::Int).unwrap();

        let binder_variable = arena.var(binder);
        let minus_two = arena.int_const(-2);
        let f_at_binder = arena.apply(f, &[binder_variable]).unwrap();
        let universal_body = arena.eq(f_at_binder, minus_two).unwrap();
        let universal = arena.forall(binder, universal_body).unwrap();

        let four = arena.int_const(4);
        let minus_four = arena.int_const(-4);
        let one = arena.int_const(1);
        let scalar_variable = arena.var(scalar);
        let f_minus_four = arena.apply(f, &[minus_four]).unwrap();
        let scalar_plus_f = arena.int_add(scalar_variable, f_minus_four).unwrap();
        let lower_bound = arena.int_add(scalar_plus_f, one).unwrap();
        let g_four = arena.apply(g, &[four]).unwrap();
        let ground_bound = arena.int_ge(g_four, lower_bound).unwrap();

        let g_f_minus_four = arena.apply(g, &[f_minus_four]).unwrap();
        let g_one = arena.apply(g, &[one]).unwrap();
        let f_g_one = arena.apply(f, &[g_one]).unwrap();
        let ground_equality = arena.eq(g_f_minus_four, f_g_one).unwrap();
        let assertions = vec![universal, ground_bound, ground_equality];
        // This asserts a deterministic semantic invariant. The fixed MBQI
        // round/instance caps bound the search; a wall-clock budget would make
        // the expected SAT depend on host speed and load.
        let config = SolverConfig::new();

        assert!(matches!(
            prove_unsat_by_mbqi_inner(&mut arena, &assertions, &config, false).unwrap(),
            CheckResult::Unknown(_)
        ));

        let minus_five = arena.int_const(-5);
        let fixing = arena.eq(scalar_variable, minus_five).unwrap();
        let mut fixed_assertions = assertions.clone();
        fixed_assertions.push(fixing);
        let fixed_result =
            prove_unsat_by_mbqi_inner(&mut arena, &fixed_assertions, &config, false).unwrap();
        assert!(
            matches!(fixed_result, CheckResult::Sat(_)),
            "fixed query must be satisfiable, got {fixed_result:?}"
        );

        let CheckResult::Sat(model) =
            prove_unsat_by_mbqi(&mut arena, &assertions, &config).unwrap()
        else {
            panic!("one guarded fixed-query level must recover the measured model");
        };
        assert!(crate::check_model(&arena, &assertions, &model).unwrap());
        assert_eq!(model.get(scalar), Some(Value::Int(-5)));
    }

    #[test]
    fn mbqi_one_level_fixed_retry_never_transfers_non_sat_result() {
        let arena = TermArena::new();
        assert!(
            replay_one_level_fixed_mbqi_candidate(&arena, &[], CheckResult::Unsat)
                .unwrap()
                .is_none()
        );
        assert!(
            replay_one_level_fixed_mbqi_candidate(
                &arena,
                &[],
                CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: "fixed-query control".to_owned(),
                }),
            )
            .unwrap()
            .is_none()
        );
    }

    #[test]
    fn mbqi_profile_completion_is_outer_only_and_deadline_bound() {
        let mut arena = TermArena::new();
        let function = arena
            .declare_fun("profile_outer_f", &[Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("profile_outer_x", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let application = arena.apply(function, &[variable]).unwrap();
        let nested = arena.apply(function, &[application]).unwrap();
        let minus_one = arena.int_const(-1);
        let at_minus_one = arena.apply(function, &[minus_one]).unwrap();
        let zero = arena.int_const(0);
        let nonnegative = arena.int_ge(application, zero).unwrap();
        let increasing = arena.int_gt(nested, at_minus_one).unwrap();
        let body = arena.and(nonnegative, increasing).unwrap();
        let universal = arena.forall(binder, body).unwrap();
        let assertions = vec![universal];
        let config = SolverConfig::new().with_timeout(Duration::from_secs(2));

        assert!(matches!(
            prove_unsat_by_mbqi_inner(&mut arena, &assertions, &config, false).unwrap(),
            CheckResult::Unknown(_)
        ));
        let CheckResult::Sat(model) =
            prove_unsat_by_mbqi_inner(&mut arena, &assertions, &config, true).unwrap()
        else {
            panic!("the outer profile completion must recover the checked model");
        };
        assert!(crate::check_model(&arena, &assertions, &model).unwrap());

        assert!(
            complete_mbqi_profile_guided_candidate(
                &mut arena,
                &assertions,
                &[universal],
                &[],
                &config,
                Some(Instant::now()),
            )
            .is_none(),
            "an expired shared deadline must decline before QF search"
        );
    }

    #[test]
    fn mbqi_profile_completion_caps_instances_and_never_transfers_unsat() {
        let mut arena = TermArena::new();
        let mut instances = Vec::new();
        for value in 0..MAX_MBQI_PROFILE_COMPLETION_INSTANCES {
            let instance = arena.int_const(i128::try_from(value).unwrap());
            assert!(push_mbqi_profile_completion_instance(
                &mut instances,
                instance
            ));
        }
        assert_eq!(instances.len(), MAX_MBQI_PROFILE_COMPLETION_INSTANCES);
        let duplicate = instances[0];
        assert!(!push_mbqi_profile_completion_instance(
            &mut instances,
            duplicate
        ));
        let one_over = arena.int_const(1000);
        assert!(!push_mbqi_profile_completion_instance(
            &mut instances,
            one_over
        ));
        assert_eq!(MAX_MBQI_PROFILE_COMPLETION_ROUNDS, 32);

        let function = arena
            .declare_fun("profile_unsat_f", &[Sort::Int], Sort::Int)
            .unwrap();
        let binder = arena.declare("profile_unsat_x", Sort::Int).unwrap();
        let variable = arena.var(binder);
        let application = arena.apply(function, &[variable]).unwrap();
        let zero = arena.int_const(0);
        let body = arena.int_ge(application, zero).unwrap();
        let universal = arena.forall(binder, body).unwrap();
        let contradiction = arena.bool_const(false);
        let assertions = vec![universal, contradiction];
        let config = SolverConfig::new().with_timeout(Duration::from_secs(1));
        let deadline = Instant::now().checked_add(Duration::from_secs(1));
        assert!(
            complete_mbqi_profile_guided_candidate(
                &mut arena,
                &assertions,
                &[universal],
                &[contradiction],
                &config,
                deadline,
            )
            .is_none(),
            "inner QF UNSAT must decline instead of transferring"
        );
        assert!(
            complete_mbqi_profile_guided_candidate(
                &mut arena,
                &assertions,
                &[universal, universal],
                &[contradiction],
                &config,
                deadline,
            )
            .is_none(),
            "multiple universals are outside ADR-0364"
        );
    }

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
            None,
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
            None,
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

    /// S2 dispatch-overrun fix regression
    /// (`docs/plan/smt-parity-plan-2026-09-05.md` row S2,
    /// `crate::dpll_lia::arith_dpll_admission_preflight`). Before the fix,
    /// `lia-dpll` always spent `online_lia_probe_config`'s share of the
    /// caller's reserve (a fixed fraction of the timeout, ~8 s on the
    /// standard 24 s budget) on the online CDCL(T) probe BEFORE checking
    /// whether the query's own Boolean-arithmetic skeleton already exceeds
    /// the joint size admission boundary
    /// (`dpll_lia::exceeds_pre_sat_skeleton_boundary`) — a constant the
    /// abstraction's own atom/CNF-variable counts already answer. This builds
    /// a disjunction that crosses the boundary, combined disjunctively so
    /// `lia-simplex` above it declines as `Unsupported` rather than deciding
    /// the conjunctive system directly, and asserts the decline stays far
    /// below the reserve it used to spend unconditionally.
    ///
    /// **The fixture moved on 2026-09-08 and it had to.** It used to cross on
    /// the ATOM dimension (1,300 integer atoms past a 1,280-atom envelope). The
    /// envelope was re-derived against the native CDCL core and is now 10,240
    /// atoms / 16,384 CNF variables, so this query became admissible and the
    /// test failed with `Sat` — correctly: it is a satisfiable disjunction, and
    /// the solver now decides it. Crossing on ATOMS instead would need >10,240
    /// distinct arithmetic atoms, and `ArithAbstractor::abstract_term` dedups
    /// each new atom against every prior one with a linear scan, so that is
    /// over 100M comparisons in a debug build. So the fixture now crosses on the
    /// CNF-VARIABLE dimension, which the envelope's `||` makes sufficient and
    /// which plain Boolean padding reaches linearly.
    #[test]
    fn oversized_lia_dpll_admission_declines_before_spending_the_online_probe_reserve() {
        // Two SEPARATE dimensions, deliberately kept SMALL on the expensive one:
        // `ArithAbstractor::abstract_term` dedups each new theory atom against
        // every prior one with a linear scan (`dpll_lia.rs`'s
        // `self.atoms.iter().any(...)`, pre-existing), so N distinct arithmetic
        // atoms cost O(N²) to build. `INT_ATOMS` is therefore only just past
        // `MAX_PRE_SAT_ARITH_ATOMS` (1,024) — enough for the base trigger's
        // atom half, and ~1.7M comparisons rather than the >100M that clearing
        // the 10,240-atom envelope on this dimension would cost. `BOOL_PAD`
        // does the rest: plain Boolean skeleton variables carry none of that
        // dedup cost (see the 20,000-variable
        // `abstractor_scales_linearly_on_a_wide_boolean_disjunction` test
        // above) and push the CNF-variable count past
        // `MAX_MODERATE_PRE_SAT_CNF_VARS` (16,384), which the envelope's `||`
        // makes sufficient on its own.
        const INT_ATOMS: usize = 1_300;
        const BOOL_PAD: usize = 12_000;
        let mut arena = TermArena::new();
        let zero = arena.int_const(0);
        let mut atoms = Vec::with_capacity(INT_ATOMS + BOOL_PAD);
        for index in 0..INT_ATOMS {
            let var = arena
                .int_var(&format!("wide_int_{index}"))
                .expect("fresh int var");
            atoms.push(arena.int_le(var, zero).expect("atom"));
        }
        for index in 0..BOOL_PAD {
            let symbol = arena
                .declare(&format!("wide_bool_{index}"), Sort::Bool)
                .expect("fresh Boolean symbol");
            atoms.push(arena.var(symbol));
        }
        let mut disjunction = atoms[0];
        for &atom in &atoms[1..] {
            disjunction = arena.or(disjunction, atom).expect("disjunction");
        }
        let assertions = [disjunction];

        let features = Features::scan_within(&arena, &assertions, None).expect("scan");

        // Reference-frame calibration (this codebase's own convention for a
        // wall-clock assertion that must survive a loaded, shared host — see
        // `docs/research/08-planning/frontier-ratchet-reference-frame.md`):
        // time the SAME abstraction build the preflight (and, on the
        // admissible path, `run_arith_dpll`) does directly, on a scratch
        // clone, right before the timed call below. Both measurements pay
        // whatever the host's current contention costs, so their RATIO stays
        // meaningful even when the absolute numbers are inflated by a busy
        // box or a debug build's unoptimized `O(n)`-per-atom dedup scan
        // (`ArithAbstractor::abstract_term`, pre-existing, not part of this
        // fix).
        let calibration_started = Instant::now();
        let mut calibration_arena = arena.clone();
        let _calibration =
            crate::dpll_lia::IncrementalArithDpll::new(&mut calibration_arena, &assertions)
                .expect("calibration build");
        let calibration_elapsed = calibration_started.elapsed();

        let mut trace = RouteTrace::new();
        let mut rec = Some(&mut trace);
        let config = SolverConfig {
            timeout: Some(Duration::from_secs(24)),
            ..SolverConfig::default()
        };
        let result = dispatch_int_linear_refuters(
            &mut arena,
            &assertions,
            &config,
            &features,
            None,
            &mut rec,
        )
        .expect("dispatch")
        .expect(
            "lia-dpll decides Unknown (an admission decline is still a decision \
                         `dispatch_int_linear_refuters` returns as `Some`, not a fallthrough \
                         `None` — only an `Unsupported` error falls through)",
        );
        let CheckResult::Unknown(reason) = result else {
            panic!("expected an Unknown admission decline, got {result:?}");
        };
        assert_eq!(reason.kind, UnknownKind::ResourceLimit);
        assert!(
            reason
                .detail
                .contains("pre-SAT skeleton exceeds the joint resource boundary"),
            "got: {}",
            reason.detail
        );
        let trace_text = trace.to_string();
        assert!(
            trace_text.contains("lia-dpll: declined"),
            "expected a recorded lia-dpll decline, got:\n{trace_text}"
        );
        assert!(
            trace_text.contains("pre-SAT skeleton exceeds the joint resource boundary"),
            "expected the size-admission message (not a budget/timeout message), got:\n{trace_text}"
        );

        let attempts = trace.attempts();
        let idx = attempts
            .iter()
            .position(|a| a.route == "lia-dpll")
            .expect("lia-dpll attempt recorded");
        let elapsed = trace.elapsed()[idx];
        // Bound the RATIO to the calibration, not an absolute constant: the
        // whole dispatch (bv2nat-range probe, Diophantine, `lia-simplex`'s
        // decline, and lia-dpll's preflight) should cost a small multiple of
        // ONE abstraction build, because that preflight build is the only
        // expensive step this path takes — it must NOT also pay for a real
        // online CDCL(T) probe (`check_qf_lia_online_cdclt`), which is what
        // the pre-fix code always did first (a FIXED ~8s on the standard
        // 24s budget, `online_lia_probe_config`, measured on the real corpus
        // files:
        // `docs/research/11-design-review/2026-09-05-arith-timeout-profiles.md`).
        // A flat +50ms floor keeps this from being flaky when both
        // measurements round to sub-millisecond on a fast, idle host.
        let budget = calibration_elapsed
            .saturating_mul(10)
            .saturating_add(Duration::from_millis(50));
        assert!(
            elapsed < budget,
            "lia-dpll's size-admission decline must cost close to ONE abstraction build \
             ({calibration_elapsed:?}), not also spend the online probe's reserve on an \
             already-inadmissible query; got {elapsed:?} against a budget of {budget:?}"
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
            try_disjunct_refutation(&mut arena, &assertions, &config, fallback_deadline(&config))
                .unwrap()
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

    /// Builds the measured UF residual shape: a nested assertion whose NNF +
    /// skolemization yields a 6-variable prenex chain over an uninterpreted
    /// sort with enough ground leaves that the one-shot cartesian retry
    /// overflows `CHAIN_INSTANCE_CAP` and leaves a residual quantifier. When
    /// `contradict` is set, the ground facts refute the chain's instance at
    /// `x := c1` (unsat); otherwise the query is satisfiable.
    fn cap_overflow_chain_query(contradict: bool) -> (TermArena, Vec<TermId>) {
        let mut arena = TermArena::new();
        let sort = Sort::Uninterpreted(arena.declare_uninterpreted_sort("QChainS"));
        let consts: Vec<TermId> = (1..=6)
            .map(|i| {
                let sym = arena.declare(&format!("qchain_c{i}"), sort).unwrap();
                arena.var(sym)
            })
            .collect();
        let d_const = {
            let sym = arena.declare("qchain_d", sort).unwrap();
            arena.var(sym)
        };
        let func_f = arena.declare_fun("qchain_f", &[sort], sort).unwrap();
        let func_p = arena.declare_fun("qchain_p", &[sort], Sort::Bool).unwrap();
        let func_g = arena
            .declare_fun("qchain_g", &[sort, sort, sort, sort, sort], sort)
            .unwrap();

        // Ground facts: p(f(c1)) is false (or true), and g(c2..c6) = d.
        let f_c1 = arena.apply(func_f, &[consts[0]]).unwrap();
        let p_f_c1 = arena.apply(func_p, &[f_c1]).unwrap();
        let fact = if contradict {
            arena.not(p_f_c1).unwrap()
        } else {
            p_f_c1
        };
        let g_ground = arena
            .apply(
                func_g,
                &[consts[1], consts[2], consts[3], consts[4], consts[5]],
            )
            .unwrap();
        let g_eq_d = arena.eq(g_ground, d_const).unwrap();

        // not (exists x. not (forall y1..y5. g(y1..y5) = d => p(f(x)))):
        // NNF-skolemizes to the prenex chain forall x, y1..y5 over 7 ground
        // leaves of the sort (7^6 cartesian instances >> the 4096 chain cap).
        let x_sym = arena.declare("qchain_x", sort).unwrap();
        let ys: Vec<_> = (1..=5)
            .map(|i| arena.declare(&format!("qchain_y{i}"), sort).unwrap())
            .collect();
        let y_vars: Vec<TermId> = ys.iter().map(|&y| arena.var(y)).collect();
        let g_y = arena.apply(func_g, &y_vars).unwrap();
        let g_y_eq_d = arena.eq(g_y, d_const).unwrap();
        let xv = arena.var(x_sym);
        let f_x = arena.apply(func_f, &[xv]).unwrap();
        let p_f_x = arena.apply(func_p, &[f_x]).unwrap();
        let body = arena.implies(g_y_eq_d, p_f_x).unwrap();
        let mut chain = body;
        for &y in ys.iter().rev() {
            chain = arena.forall(y, chain).unwrap();
        }
        let not_chain = arena.not(chain).unwrap();
        let exists = arena.exists(x_sym, not_chain).unwrap();
        let nested = arena.not(exists).unwrap();

        (arena, vec![fact, g_eq_d, nested])
    }

    #[test]
    fn cap_overflowing_skolemized_chain_is_refuted_via_the_egraph_loop() {
        // Before the loop retry, this exact shape (the whole measured UF
        // residual bucket) declined as "query has quantifiers instantiation
        // does not reach": the skolemized retry's only blocker is the chain
        // cap, and one overflowing chain declined the whole query.
        let (mut arena, assertions) = cap_overflow_chain_query(true);
        let config = SolverConfig::new().with_timeout(Duration::from_secs(10));
        assert_eq!(
            prove_unsat_by_ematching(&mut arena, &assertions, &config).unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    fn cap_overflowing_skolemized_chain_never_reports_sat() {
        // The satisfiable variant must stay `unknown`: the retry ran on the
        // SKOLEMIZED query, so neither the loop nor the decider may hand back
        // a `sat` that could not replay against the original assertions.
        let (mut arena, assertions) = cap_overflow_chain_query(false);
        let config = SolverConfig::new().with_timeout(Duration::from_secs(10));
        assert!(matches!(
            prove_unsat_by_ematching(&mut arena, &assertions, &config).unwrap(),
            CheckResult::Unknown(_)
        ));
    }

    // ----- wide integer literals (ADR-1702 slice 2) ---------------------

    /// `2^256`, the EVM `uint256` magnitude the Certora `QF_UFLIA` family carries.
    /// Built by repeated exact doubling rather than from a decimal constant, so
    /// the fixture cannot be a typo that happens to parse.
    fn wide_pow2(n: u32) -> axeyum_ir::WideInt {
        let mut value = axeyum_ir::WideInt::from_i128(1);
        let two = axeyum_ir::WideInt::from_i128(2);
        for _ in 0..n {
            value = value.mul(&two);
        }
        assert!(!value.fits_i128(), "the fixture must be outside i128");
        value
    }

    /// The admission check fires on a wide literal and NOT on anything else.
    /// The negative half is the load-bearing one: a guard that declines every
    /// query would also "pass" the positive half.
    #[test]
    fn wide_int_admission_fires_only_on_a_wide_integer_constant() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let narrow = arena.int_const(i128::MAX);
        let narrow_atom = arena.int_gt(x, narrow).unwrap();
        let features = Features::scan_within(&arena, &[narrow_atom], None).unwrap();
        assert!(!features.has_wide_int);
        assert!(wide_int_admission(&features).is_none());

        let wide = arena.int_const_big(wide_pow2(256));
        let wide_atom = arena.int_gt(x, wide).unwrap();
        let features = Features::scan_within(&arena, &[wide_atom], None).unwrap();
        assert!(features.has_wide_int);
        let reason = wide_int_admission(&features).expect("a wide literal is not admitted");
        assert_eq!(reason.kind, UnknownKind::Incomplete);
        assert!(
            reason.detail.contains("i128"),
            "the decline must name the reason: {}",
            reason.detail
        );
    }

    /// End to end through the front door: a query carrying a `2^256` bound is
    /// ATTEMPTED and returns a first-class `unknown` — never a panic, and never
    /// a verdict. Before ADR-1702 slice 2 it never got past the parser.
    #[test]
    fn a_query_with_a_wide_literal_declines_rather_than_panicking() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let wide = arena.int_const_big(wide_pow2(256));
        let assertion = arena.int_gt(x, wide).unwrap();
        let result = check_auto(&mut arena, &[assertion], &SolverConfig::new()).unwrap();
        match result {
            CheckResult::Unknown(reason) => assert!(reason.detail.contains("i128")),
            other => panic!("a wide literal must decline, got {other:?}"),
        }
    }

    /// Soundness-negative: the guard must not cost us a query we could decide.
    /// The same shapes without a wide literal still get real verdicts, so the
    /// decline above is about the literal and not about the query shape.
    #[test]
    fn the_admission_check_does_not_touch_narrow_queries() {
        let mut arena = TermArena::new();
        let x = arena.int_var("x").unwrap();
        let five = arena.int_const(5);
        let three = arena.int_const(3);
        let lower = arena.int_gt(x, five).unwrap();
        let upper = arena.int_lt(x, three).unwrap();
        assert!(matches!(
            check_auto(&mut arena, &[lower, upper], &SolverConfig::new()).unwrap(),
            CheckResult::Unsat
        ));
        let satisfiable = arena.int_gt(x, three).unwrap();
        assert!(matches!(
            check_auto(&mut arena, &[satisfiable], &SolverConfig::new()).unwrap(),
            CheckResult::Sat(_)
        ));
    }

    // ---------------------------------------------------------------------
    // The over-bound UF+arithmetic decision point (`UfArithOverboundPolicy`).
    // ---------------------------------------------------------------------

    /// Padding applications in the over-bound fixture below.
    ///
    /// It must exceed [`MAX_PRE_LIA_UF_PROBE_ASSERTIONS`] (`256`), or the
    /// pre-LIA probe (`dispatch_arith_uf_overbound_probe_before_lia`) decides
    /// the query on its own clone and `dispatch_uf_fast_paths` is never
    /// reached — which is exactly how the first version of these tests failed,
    /// reporting `engaged == 0` on a query that is unambiguously over the eager
    /// bound. The fixture emits `n + 2` assertions, so `260` clears it.
    const PADDING_APPS: usize = 260;

    /// An UNSAT `QF_UFLIA` query with `n` padding applications of one `Int -> Int`
    /// function, so it carries `C(n+2, 2)` Ackermann congruence pairs: over the
    /// eager bound of 64 for `n >= 8`, and far under the secondary (pathological)
    /// bound of two million. The refutation itself is pure congruence:
    /// `a = b` with `f(a) != f(b)`.
    fn overbound_uflia_unsat(arena: &mut TermArena, n: usize) -> Vec<TermId> {
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let mut assertions = Vec::new();
        for i in 0..n {
            let v = arena.int_var(&format!("pad{i}")).unwrap();
            let app = arena.apply(f, &[v]).unwrap();
            let value = arena.int_const(i128::try_from(i).unwrap());
            assertions.push(arena.eq(app, value).unwrap());
        }
        let a = arena.int_var("a").unwrap();
        let b = arena.int_var("b").unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let eq = arena.eq(fa, fb).unwrap();
        assertions.push(arena.not(eq).unwrap());
        assertions.push(arena.eq(a, b).unwrap());
        assertions
    }

    #[test]
    fn overbound_policy_defaults_to_the_probe_arm() {
        // No guard, no environment variable set in this test: the shipped default
        // must be the arm that lets the ladder run. A future edit that flips the
        // default back to `CegarTerminal` makes every route below the CEGAR
        // unreachable again, silently — this test is what says so.
        assert_eq!(
            uf_arith_overbound_policy(),
            UfArithOverboundPolicy::CegarProbe
        );
    }

    #[test]
    fn overbound_policy_guard_overrides_and_restores() {
        let outer = uf_arith_overbound_policy();
        {
            let _g = UfArithOverboundPolicyGuard::set(UfArithOverboundPolicy::CegarTerminal);
            assert_eq!(
                uf_arith_overbound_policy(),
                UfArithOverboundPolicy::CegarTerminal
            );
            {
                let _inner = UfArithOverboundPolicyGuard::set(UfArithOverboundPolicy::SkipCegar);
                assert_eq!(
                    uf_arith_overbound_policy(),
                    UfArithOverboundPolicy::SkipCegar
                );
            }
            assert_eq!(
                uf_arith_overbound_policy(),
                UfArithOverboundPolicy::CegarTerminal
            );
        }
        assert_eq!(uf_arith_overbound_policy(), outer);
    }

    #[test]
    fn ladder_slice_arithmetic_matches_the_policy_each_route_declares() {
        let day = Duration::from_secs(86_400);
        // A reserve: the route keeps everything but 1/N.
        let quarter = LadderSlice::all_but_reserve("test", 4);
        assert_eq!(
            quarter.slice_of(Duration::from_secs(24)),
            Duration::from_secs(18)
        );
        assert_eq!(
            quarter.reserved_from(Duration::from_secs(24)),
            Duration::from_secs(6)
        );
        // A capped reserve: proportional on tight budgets, flat once the cap
        // binds. Both sides of the `min` are exercised, because a ceiling that
        // never binds and a ceiling that always binds are different policies
        // and one test hitting only one of them cannot tell them apart.
        assert_eq!(
            DL_PROBE_SLICE.reserved_from(Duration::from_secs(8)),
            Duration::from_secs(2),
            "under the cap the reserve is proportional"
        );
        assert_eq!(
            DL_PROBE_SLICE.reserved_from(day),
            DL_FALLBACK_RESERVE,
            "over the cap the reserve is flat"
        );
        assert_eq!(
            DL_EXTENDED_PROBE_SLICE.reserved_from(day),
            DL_EXTENDED_FALLBACK_RESERVE
        );
        // A fraction: the route takes 1/N and the ladder keeps the rest, which
        // is the opposite division and the one `int-real-relax` uses.
        assert_eq!(
            INT_REAL_RELAX_SLICE.slice_of(Duration::from_secs(24)),
            Duration::from_secs(4)
        );
        // A capped fraction.
        assert_eq!(
            PRE_LIA_UF_PROBE_SLICE.slice_of(Duration::from_secs(1)),
            Duration::from_millis(100)
        );
        assert_eq!(
            PRE_LIA_UF_PROBE_SLICE.slice_of(day),
            PRE_LIA_UF_PROBE_CEILING
        );
        // No policy may hand a route more clock than the ladder has.
        for slice in [
            quarter,
            DL_PROBE_SLICE,
            DL_EXTENDED_PROBE_SLICE,
            UF_ARITH_CEGAR_SLICE,
            ABV_ONLINE_SLICE,
            INT_REAL_RELAX_SLICE,
            PRE_LIA_UF_PROBE_SLICE,
            UFBV_ONLINE_PROBE_SLICE,
            MBQI_FIRST_REFUSAL_SLICE,
            QINST_EGRAPH_RETRY_SLICE,
        ] {
            for remaining in [
                Duration::ZERO,
                Duration::from_millis(1),
                Duration::from_millis(7),
                Duration::from_secs(24),
                day,
            ] {
                assert!(
                    slice.slice_of(remaining) <= remaining,
                    "{} granted more than the ladder had at {remaining:?}",
                    slice.route
                );
            }
        }
    }

    #[test]
    fn a_slice_that_rounds_to_zero_is_never_the_whole_budget() {
        // THE INVERSION GUARD. Two helpers used to return the caller's config
        // UNCHANGED when their share underflowed -- `int_real_relax_budget` at
        // `timeout / 6 == 0` and `pre_lia_uf_probe_budget` at `timeout / 10 ==
        // 0` -- so a route asked for a sixth of the clock got all of it. The
        // first is recorded as a FINDING in `crate::config_registry`; the
        // second was found looking for more of the same shape.
        //
        // THE BUDGETS BELOW ARE IN NANOSECONDS, and that is the whole point of
        // this test. `Duration` division is nanosecond-based, so
        // `from_millis(5) / 6` is 833 us, NOT zero: the old branch could only
        // fire under SIX NANOSECONDS. A first version of this test used 5 ms
        // and 9 ms, believing the FINDING's "small-budget end" was milliseconds
        // -- and the mutation that restores the old branch made no test fail at
        // all. A guard for a band six nanoseconds wide has to be written in
        // nanoseconds.
        for tight in [
            Duration::from_nanos(1),
            Duration::from_nanos(5),
            Duration::from_nanos(9),
            Duration::from_nanos(100),
            Duration::from_micros(1),
            Duration::from_millis(1),
            Duration::from_millis(5),
        ] {
            let config = SolverConfig::new().with_timeout(tight);
            let relax = int_real_relax_budget(&config).timeout.unwrap();
            assert!(
                relax < tight,
                "a sixth of {tight:?} became {relax:?} -- the whole clock"
            );
            let pre_lia = pre_lia_uf_probe_budget(&config).timeout.unwrap();
            assert!(
                pre_lia < tight,
                "a tenth of {tight:?} became {pre_lia:?} -- the whole clock"
            );
            // ...and it must not become ZERO either: a route handed no clock at
            // all is a route deleted, which is a different policy from a route
            // shared. Below 2 ns there is no nonzero slice smaller than the
            // budget, so that is where the promise stops.
            if tight >= Duration::from_nanos(2) {
                assert!(!relax.is_zero(), "a sixth of {tight:?} became nothing");
                assert!(!pre_lia.is_zero(), "a tenth of {tight:?} became nothing");
            }
        }
        // An unbounded caller stays unbounded: this divides a budget, it never
        // invents one.
        assert_eq!(int_real_relax_budget(&SolverConfig::new()).timeout, None);
        assert_eq!(pre_lia_uf_probe_budget(&SolverConfig::new()).timeout, None);
    }

    #[test]
    fn abv_online_probe_keeps_all_but_the_array_ladder_reserve() {
        // Measured 2026-09-08 (span-log sweep, `QF_ABV.json`): on four files
        // `abv-online-cdclt` spent 24.009 s of a 24 s budget, declined, and
        // `array-fast-path` decided the file in 0.007-0.174 s. This asserts the
        // ladder now gets a reserve out of the SAME clock, and that the arm
        // which reproduces the old behaviour still exists to measure against.
        let timeout = Duration::from_secs(24);
        let config = SolverConfig::new().with_timeout(timeout);
        let deadline = Instant::now().checked_add(timeout);

        let reserved = {
            let _policy = AbvOnlineReservePolicyGuard::set(AbvOnlineReservePolicy::LadderReserve);
            abv_online_probe_budget(&config, deadline).timeout.unwrap()
        };
        // Bounded from both sides: the clock moves while the test runs, and an
        // upper bound alone is satisfied by a probe of zero.
        assert!(
            reserved <= Duration::from_secs(18) && reserved >= Duration::from_secs(17),
            "abv-online probe budget {reserved:?} is not 3/4 of a 24 s clock"
        );
        assert!(
            timeout.saturating_sub(reserved) >= Duration::from_millis(2900),
            "the array ladder's reserve must exceed the 2.898 s slowest \
             array-fast-path decision in the measured sweep"
        );

        let whole = {
            let _policy = AbvOnlineReservePolicyGuard::set(AbvOnlineReservePolicy::WholeBudget);
            abv_online_probe_budget(&config, deadline).timeout.unwrap()
        };
        assert_eq!(
            whole, timeout,
            "the `off` arm must reproduce the old budget"
        );

        // An unbounded configuration stays unbounded under both arms.
        for policy in [
            AbvOnlineReservePolicy::LadderReserve,
            AbvOnlineReservePolicy::WholeBudget,
        ] {
            let _policy = AbvOnlineReservePolicyGuard::set(policy);
            assert_eq!(
                abv_online_probe_budget(&SolverConfig::new(), None).timeout,
                None,
                "{}: no clock to share means no clock to divide",
                policy.name()
            );
        }
    }

    #[test]
    fn every_route_budget_in_this_file_goes_through_the_slice_policy() {
        // THE RATCHET. The pattern this policy exists for -- a route that runs
        // before others and takes the whole clock -- was hand-rolled four times
        // in this file before it had a name, and each copy had to be found by
        // measuring a division. So the population here is derived from the
        // SOURCE, not from a list: every site that sets a route's `timeout` is
        // read out of `auto.rs` and must be one of the three helpers that
        // narrow a config to the REMAINING clock, or `LadderSlice::apply`.
        //
        // A fifth hand-rolled divisor fails this test at the moment it is
        // written, which is the only moment it is cheap to notice.
        const NARROWS_TO_REMAINING: &[&str] = &[
            "config_with_remaining_timeout",
            "config_with_remaining_deadline",
            "mbqi_config_with_deadline",
            "apply",
        ];
        let source = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/auto.rs"),
        )
        .expect("read this file's own source");
        let non_test = source
            .split_once("\nmod tests {")
            .map_or(source.as_str(), |(before, _)| before);
        let mut enclosing = String::new();
        let mut sites: Vec<(String, String)> = Vec::new();
        for line in non_test.lines() {
            let trimmed = line.trim_start();
            if let Some(rest) = trimmed
                .strip_prefix("pub(crate) fn ")
                .or_else(|| trimmed.strip_prefix("pub fn "))
                .or_else(|| trimmed.strip_prefix("fn "))
            {
                enclosing = rest
                    .split(['(', '<'])
                    .next()
                    .unwrap_or_default()
                    .trim()
                    .to_owned();
            }
            if trimmed.contains(".timeout = Some(") {
                sites.push((enclosing.clone(), trimmed.to_owned()));
            }
        }
        // A scan that found nothing would pass every assertion below, so the
        // count is checked first: this is the control, not decoration.
        assert!(
            sites.len() >= 4,
            "the scan found only {} timeout assignments in auto.rs -- it stopped \
             matching the source rather than the source getting cleaner",
            sites.len()
        );
        assert!(
            sites.iter().any(|(f, _)| f == "apply"),
            "LadderSlice::apply must be one of the sites the scan sees"
        );
        let hand_rolled: Vec<&(String, String)> = sites
            .iter()
            .filter(|(f, _)| !NARROWS_TO_REMAINING.contains(&f.as_str()))
            .collect();
        assert!(
            hand_rolled.is_empty(),
            "route budgets computed outside the ladder-slice policy: {hand_rolled:#?}\n\
             Express the share as a named `LadderSlice` constant with a registry \
             entry instead, so the next reader can find it by name."
        );
    }

    #[test]
    fn overbound_cegar_probe_keeps_all_but_the_ladder_reserve() {
        // The CEGAR keeps everything left at the dispatcher's entry deadline
        // EXCEPT the ladder's reserve. This is the assertion that fails if
        // anyone turns the reserve back into a half-budget split: on the
        // committed 200-file list that split cost `hash_sat_05_14`, a file that
        // decides at 12.7 s and cannot decide in 12.
        for (timeout, ceiling, floor) in [
            (Duration::ZERO, Duration::ZERO, Duration::ZERO),
            (
                Duration::from_secs(24),
                Duration::from_secs(18),
                Duration::from_secs(17),
            ),
            (
                Duration::from_secs(8),
                Duration::from_secs(6),
                Duration::from_secs(5),
            ),
        ] {
            let config = SolverConfig::new().with_timeout(timeout);
            let deadline = Instant::now().checked_add(timeout);
            let probe = cegar_probe_budget(&config, deadline).timeout.unwrap();
            // The remaining budget shrinks by the time this loop takes, so bound
            // it from both sides rather than asserting an exact clock reading.
            // The FLOOR is the load-bearing half: an upper bound alone is
            // satisfied by a probe of zero, which is the failure this guards.
            assert!(
                probe <= ceiling && probe >= floor,
                "probe budget {probe:?} outside [{floor:?}, {ceiling:?}] for {timeout:?}"
            );
        }
        // An unbounded configuration stays unbounded: there is no clock to share.
        assert_eq!(cegar_probe_budget(&SolverConfig::new(), None).timeout, None);
    }

    #[test]
    fn overbound_ladder_is_reachable_when_the_cegar_is_skipped() {
        // THE REACHABILITY TEST. Above 64 congruence pairs the lazy CEGAR used to
        // answer for the whole dispatcher: `euf-online`, `euf-offline` and
        // `uf-arith-online` never ran, whatever they would have decided. With the
        // CEGAR removed entirely, the routes underneath must still decide this
        // query — which is the fact the old structure made unobservable.
        let mut arena = TermArena::new();
        let assertions = overbound_uflia_unsat(&mut arena, PADDING_APPS);
        assert!(
            crate::euf::ackermann_congruence_pairs(&arena, &assertions)
                > crate::euf::MAX_ACKERMANN_CONGRUENCE_PAIRS,
            "fixture must be over the eager Ackermann bound"
        );

        let config = SolverConfig::new().with_timeout(Duration::from_secs(20));
        let _policy = UfArithOverboundPolicyGuard::set(UfArithOverboundPolicy::SkipCegar);
        let _stats = crate::UfArithOverboundStatsGuard::enable();
        let _routes = crate::RouteAttributionGuard::enable();

        let verdict = check_auto(&mut arena, &assertions, &config).unwrap();
        assert_eq!(
            verdict,
            CheckResult::Unsat,
            "with the CEGAR skipped, the ladder below it must still refute this"
        );

        let stats = crate::last_uf_arith_overbound_stats();
        assert_eq!(stats.engaged, 1, "the eager bound must have fired once");
        assert_eq!(stats.cegar_skipped, 1);
        assert_eq!(stats.fell_through, 1);
        assert_eq!(stats.terminal_unknown, 0);

        let trace = crate::last_route_attribution();
        let attempts = trace.attempts();
        let overbound = attempts
            .iter()
            .position(|a| a.route == "uf-arith-lazy-overbound")
            .expect("the over-bound decision point must be recorded");
        assert!(
            overbound + 1 < attempts.len(),
            "no route ran after the over-bound decision point; trail: {:?}",
            attempts.iter().map(|a| a.route).collect::<Vec<_>>()
        );
    }

    #[test]
    fn overbound_terminal_policy_still_answers_for_the_whole_dispatcher() {
        // The negative control for the test above, on the same fixture: under the
        // policy that names the old behaviour, the CEGAR's answer IS the
        // dispatcher's answer. If this ever stops holding, `CegarTerminal` no
        // longer describes what it claims to and the A/B is meaningless.
        let mut arena = TermArena::new();
        let assertions = overbound_uflia_unsat(&mut arena, PADDING_APPS);
        let config = SolverConfig::new().with_timeout(Duration::from_secs(20));
        let _policy = UfArithOverboundPolicyGuard::set(UfArithOverboundPolicy::CegarTerminal);
        let _stats = crate::UfArithOverboundStatsGuard::enable();
        let _routes = crate::RouteAttributionGuard::enable();

        let verdict = check_auto(&mut arena, &assertions, &config).unwrap();
        assert_eq!(verdict, CheckResult::Unsat);

        let stats = crate::last_uf_arith_overbound_stats();
        assert_eq!(stats.engaged, 1);
        assert_eq!(stats.cegar_decided, 1, "the CEGAR decides this fixture");
        assert_eq!(stats.fell_through, 0, "nothing may run after it here");

        let trace = crate::last_route_attribution();
        let decided = trace.decided_by().expect("a decided file names its route");
        assert_eq!(
            decided.1.route, "uf-arith-lazy-overbound",
            "the terminal arm must be answered by the CEGAR itself"
        );
    }

    #[test]
    fn every_policy_gives_the_same_verdict_on_an_overbound_query() {
        // The soundness bar for making this a policy at all: three arms, one
        // query, one verdict. A policy that can change a `sat`/`unsat` is not a
        // policy, it is a bug with a name.
        for policy in [
            UfArithOverboundPolicy::CegarTerminal,
            UfArithOverboundPolicy::CegarProbe,
            UfArithOverboundPolicy::SkipCegar,
        ] {
            let mut arena = TermArena::new();
            let assertions = overbound_uflia_unsat(&mut arena, PADDING_APPS);
            let config = SolverConfig::new().with_timeout(Duration::from_secs(20));
            let _policy = UfArithOverboundPolicyGuard::set(policy);
            assert_eq!(
                check_auto(&mut arena, &assertions, &config).unwrap(),
                CheckResult::Unsat,
                "policy {} changed the verdict",
                policy.name()
            );
        }
    }

    #[test]
    fn pathological_overbound_stays_terminal_under_every_policy() {
        // The secondary (pathological-input) bounds are NOT relaxed by this
        // change. A query above `MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS` is the case
        // the eager bound exists for: the ladder below recurses over the same
        // assertion, so it must be refused before anything runs, under every arm.
        // Smallest `k` with C(k,2) strictly above the two-million secondary bound.
        let mut k = 2usize;
        while k * (k - 1) / 2 <= crate::euf::MAX_LAZY_ACKERMANN_CONGRUENCE_PAIRS {
            k += 1;
        }
        for policy in [
            UfArithOverboundPolicy::CegarTerminal,
            UfArithOverboundPolicy::CegarProbe,
            UfArithOverboundPolicy::SkipCegar,
        ] {
            let mut arena = TermArena::new();
            let assertions = overbound_uflia_unsat(&mut arena, k);
            let config = SolverConfig::new().with_timeout(Duration::from_secs(5));
            let _policy = UfArithOverboundPolicyGuard::set(policy);
            let _stats = crate::UfArithOverboundStatsGuard::enable();
            let started = Instant::now();
            let verdict = check_auto(&mut arena, &assertions, &config).unwrap();
            let elapsed = started.elapsed();
            assert!(
                matches!(verdict, CheckResult::Unknown(_)),
                "policy {} admitted a pathological query: {verdict:?}",
                policy.name()
            );
            let stats = crate::last_uf_arith_overbound_stats();
            assert_eq!(
                stats.pathological_refusals,
                1,
                "policy {} did not take the pathological refusal",
                policy.name()
            );
            assert_eq!(stats.terminal_unknown, 1);
            assert_eq!(stats.fell_through, 0);
            assert!(
                elapsed < Duration::from_secs(5),
                "the pathological refusal must be taken before the budget, took {elapsed:?}"
            );
        }
    }

    #[test]
    fn overbound_counters_are_silent_without_a_guard() {
        // The opt-in half of the instrumentation contract: with no guard live, the
        // recording path must not accumulate anything. A counter that keeps
        // counting after its guard drops reports another query's work.
        let mut arena = TermArena::new();
        let assertions = overbound_uflia_unsat(&mut arena, PADDING_APPS);
        let config = SolverConfig::new().with_timeout(Duration::from_secs(20));
        {
            let _stats = crate::UfArithOverboundStatsGuard::enable();
            let mut probe_arena = arena.clone();
            let _ = check_auto(&mut probe_arena, &assertions, &config).unwrap();
            assert_eq!(crate::last_uf_arith_overbound_stats().engaged, 1);
        }
        // Guard dropped: a second solve must not move the counters.
        let before = crate::last_uf_arith_overbound_stats();
        let _ = check_auto(&mut arena, &assertions, &config).unwrap();
        assert_eq!(
            crate::last_uf_arith_overbound_stats(),
            before,
            "counters moved after the guard was dropped"
        );
    }
}
