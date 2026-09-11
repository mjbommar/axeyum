//! Pure Rust SAT-backed bit-vector backend.
//!
//! This backend is the first Phase 5 composition slice: Axeyum query terms are
//! lowered to AIG, encoded to CNF, solved through the native proof-producing
//! CDCL core, lifted back into an Axeyum model, and replayed against the
//! original terms before a `sat` result is accepted. Z3 is not used and
//! unsupported lowering remains explicit rather than falling through to an
//! oracle.
//!
//! This paragraph said "the pure-Rust `BatSat` adapter" until ADR-1910. That was
//! false from 2026-09-05 (ADR-1703), when `primary_sat_search` became an
//! unconditional `solve_with_native_cdcl` call — a module doc describing a route
//! the module had stopped taking.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::time::Duration;

// Monotonic clock: on wasm32 the browser has no `std` clock, so use `web-time`'s
// drop-in `Instant` (ADR-0017). Native targets use the std clock.
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use axeyum_aig::{AigLit, AigNode};
#[cfg(feature = "full")]
use axeyum_bv::lower_terms;
use axeyum_bv::{
    BitLowerError, BitLowering, first_unsupported_op, first_unsupported_sort,
    lower_terms_demanded_with_deadline, lower_terms_range_demanded_with_deadline,
    lower_terms_with_deadline, lower_terms_with_deadline_profiled,
};
// The seven pass-sequencing names -- `simplify_within_recorded`,
// `simplify_with_options`, `vivify_within`, `eliminate_variables_within`,
// `eliminate_variables_within_recorded`, `compact` and `xor_propagate` -- are
// deliberately absent from this list. Since ADR-1810 this file is a call site of
// `inprocess_scheduled`, not a second scheduler over the same passes, and the
// import list is the mechanical statement of that.
use axeyum_cnf::{
    CnfAssignment, CnfConstructionProfile, CnfDuplicateOriginProfile, CnfEncoding, CnfError,
    CnfFormula, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, EncodedLit, InprocessObserver, InprocessSchedule,
    OccurrencePass, ProofCoverage, ProofSolveOutcome, ReducedReason, ReductionLink, SatProofStatus,
    SatResult, SatUnknownReason, SatUnsatEvidence, ScheduledInprocess, VivifyOptions,
    XorCdclResult, check_drat, extract_xors, inprocess_scheduled, solve_with_drat_proof,
    solve_with_drat_proof_with_limits, solve_with_xor_cdcl, tseitin_encode,
    tseitin_encode_profiled_with_origins, write_drat, xor_gauss_drat_refutation,
};
use axeyum_ir::budget::{EffortAccount, EffortPolicy, Grant, WorkMeter};
use axeyum_ir::{
    Assignment, IrError, Op, Sort, SortId, TermArena, TermId, TermNode, TermStats, Value, eval,
    well_founded_default,
};
use axeyum_query::{Query, QueryPlan, QueryReplayFailure};

use crate::backend::{
    BitLoweringMode, Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig,
    SolverError, UnknownKind, UnknownReason,
};
use crate::memory_budget::MemoryBudget;
use crate::model::Model;
use crate::proof::UnsatProof;

/// Pure Rust `QF_BV` backend for the currently supported bit-blasting subset.
///
/// The supported subset is exactly the subset accepted by `axeyum-bv` lowering,
/// which now covers the full scalar `QF_BV` operator set: Bool/BV constants and
/// symbols, Boolean connectives, BV bitwise operators, equality, `ite`,
/// `bvcomp`, concat/extract, zero/sign extension, neg/add/sub/mul, unsigned and
/// signed division and remainder (`bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/`bvsmod`),
/// comparisons, shifts, and constant rotates. Constructs outside the scalar
/// `QF_BV` fragment (for example arrays) would return
/// [`SolverError::Unsupported`] with no oracle fallback.
#[derive(Debug, Default)]
pub struct SatBvBackend {
    stats: Option<SolveStats>,
}

impl SatBvBackend {
    /// Creates a new pure Rust SAT-backed BV backend.
    pub fn new() -> Self {
        Self::default()
    }

    #[allow(clippy::too_many_lines)]
    fn check_with_replay(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        replay_plan: Option<&QueryPlan>,
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        self.check_with_replay_internal(arena, assertions, replay_plan, config, true)
    }

    #[allow(clippy::too_many_lines)]
    fn check_with_replay_internal(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        replay_plan: Option<&QueryPlan>,
        config: &SolverConfig,
        allow_shared_guard_split: bool,
    ) -> Result<CheckResult, SolverError> {
        self.stats = None;
        let deadline = config
            .timeout
            .and_then(|timeout| Instant::now().checked_add(timeout));
        for &term in assertions {
            if arena.sort_of(term) != Sort::Bool {
                return Err(SolverError::NonBooleanAssertion(term));
            }
        }
        if let Some((term, op)) = first_unsupported_op(arena, assertions) {
            return Err(SolverError::Unsupported(format!(
                "term #{} uses unsupported pure-Rust BV operator {op:?}",
                term.index()
            )));
        }
        if let Some((term, sort)) = first_unsupported_sort(arena, assertions) {
            return Err(SolverError::Unsupported(format!(
                "term #{} has sort {sort} that the pure-Rust BV backend cannot bit-blast",
                term.index()
            )));
        }

        let shape = TermStats::compute(arena, assertions);
        if let Some(budget) = config.node_budget
            && shape.dag_nodes > budget
        {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::NodeBudget,
                detail: format!("query has {} DAG nodes, budget {budget}", shape.dag_nodes),
            }));
        }

        // Phase boundary 1 of 3 for the memory budget (`memory_budget`): a caller
        // that arrives already over its limit gets `unknown` before this check
        // allocates anything at all. ~9.4 us; see that module for why a probe
        // may only sit at a phase boundary.
        let memory = MemoryBudget::from_config(config);
        if let Some(budget) = memory
            && let Some(reason) = budget.exceeded("backend entry")
        {
            return Ok(CheckResult::Unknown(reason));
        }

        if let Some(result) = oversized_encoding_refusal(arena, assertions, config) {
            return Ok(result);
        }

        if allow_shared_guard_split
            && replay_plan.is_none()
            && let Some(deadline) = deadline
            && let Some(branches) = shared_guard_split_branches(arena, assertions, shape.dag_nodes)
        {
            return self.check_shared_guard_split(arena, assertions, &branches, config, deadline);
        }

        let mut stats = SolveStats {
            assertion_count: assertions.len() as u64,
            terms_translated: shape.dag_nodes,
            ..SolveStats::default()
        };

        // The cross-thread stage mirror (`crate::layers::BvStageMirror`).
        // `publish_bv_layer_stats` fires only when this check RETURNS, so
        // without this a check killed by a wall-clock watchdog published
        // nothing at all — and a `sat-bv` file we lose is by definition a check
        // that did not return. Both decisions are taken HERE, once: with
        // collection off (the default) or no board installed (every run without
        // `--trace`) this is two thread-local `bool` reads and no allocation,
        // and every `enter_stage!` below is a `None` test.
        let stage_mirror = (crate::layers::bv_layer_stats_enabled()
            && crate::live_instruments::installed())
        .then(|| {
            let mirror = Arc::new(crate::layers::BvStageMirror::default());
            crate::live_instruments::publish_live(
                crate::live_instruments::instrument::BV_LAYER_MIRROR,
                Arc::clone(&mirror),
                // A handle, never a snapshot: this check writes through it at
                // every stage boundary for as long as it runs.
                crate::live_instruments::Sampled::InFlight,
            );
            mirror
        });
        macro_rules! enter_stage {
            ($stage:expr) => {
                if let Some(mirror) = &stage_mirror {
                    mirror.enter($stage, &stats);
                }
            };
        }

        enter_stage!(crate::layers::BvStage::BitBlast);
        let bit_blast_start = Instant::now();
        let lowering_result = match config.bit_lowering_mode {
            BitLoweringMode::RangeSliced(policy) => {
                lower_terms_range_demanded_with_deadline(arena, assertions, policy, deadline)
            }
            BitLoweringMode::DemandSliced => {
                lower_terms_demanded_with_deadline(arena, assertions, deadline)
            }
            BitLoweringMode::Eager if config.profile_bit_demand => {
                lower_terms_with_deadline_profiled(arena, assertions, deadline)
            }
            BitLoweringMode::Eager => lower_terms_with_deadline(arena, assertions, deadline),
        };
        let lowering = match lowering_result {
            Ok(lowering) => lowering,
            Err(BitLowerError::DeadlineExceeded) => {
                let bit_blast = bit_blast_start.elapsed();
                stats.translate = bit_blast;
                push_duration_ms(&mut stats, "bit_blast_ms", bit_blast);
                self.stats = Some(stats);
                return Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Timeout,
                    detail:
                        "pure-Rust BV backend exhausted its deadline during bit-vector lowering"
                            .to_owned(),
                }));
            }
            Err(error) => return Err(map_lower_error(error)),
        };
        let bit_blast = bit_blast_start.elapsed();

        // Phase boundary 2 of 3: lowering is where the AIG is built, and the
        // projected-clause ceiling above is an ESTIMATE. This is the first point
        // at which the real cost is observable.
        if let Some(budget) = memory
            && let Some(reason) = budget.exceeded("after bit-vector lowering")
        {
            stats.translate = bit_blast;
            push_duration_ms(&mut stats, "bit_blast_ms", bit_blast);
            self.stats = Some(stats);
            return Ok(CheckResult::Unknown(reason));
        }

        let roots = lowering
            .roots()
            .iter()
            .map(|root| root.bits()[0])
            .collect::<Vec<_>>();
        // No stage timings are attached to this boundary on purpose.
        // `BvLayerStats` is identified as `sat-bv`-shaped by `aig_nodes` /
        // `cnf_variables`, which `record_encoding_stats` publishes only AFTER
        // the CNF encoding — so a reading taken at or before here lifts to
        // `None` whatever is in `stats`, and the STAGE is the entire answer.
        // That is the honest reading: "killed while encoding", with no numbers,
        // rather than a row of zeros a consumer would read as measured stage
        // costs.
        enter_stage!(crate::layers::BvStage::CnfEncode);
        let cnf_start = Instant::now();
        let (encoding, duplicate_origins) = if config.profile_cnf_construction {
            let (encoding, origins) = tseitin_encode_profiled_with_origins(lowering.aig(), &roots)
                .map_err(|error| map_cnf_error(&error))?;
            (encoding, Some(origins))
        } else {
            (
                tseitin_encode(lowering.aig(), &roots).map_err(|error| map_cnf_error(&error))?,
                None,
            )
        };
        if config.profile_cnf_construction
            && (!encoding.stats().construction_profile_invariants_hold()
                || duplicate_origins.as_ref().is_none_or(|origins| {
                    !origins.invariants_hold()
                        || origins.duplicate_clauses != encoding.stats().duplicate_clauses_skipped
                }))
        {
            return Err(SolverError::Backend(
                "cold CNF construction/origin profile violated an accounting invariant".to_owned(),
            ));
        }
        let cnf_encode = cnf_start.elapsed();
        stats.translate = bit_blast + cnf_encode;
        push_duration_ms(&mut stats, "bit_blast_ms", bit_blast);
        push_duration_ms(&mut stats, "cnf_encode_ms", cnf_encode);
        record_encoding_stats(&mut stats, &lowering, &encoding);
        if let Some(origins) = &duplicate_origins {
            record_duplicate_origin_profile(&mut stats, origins);
        }

        // Optional CNF inprocessing (subsumption + bounded variable elimination)
        // on the Tseitin formula. Subsumption is model-preserving and BVE is
        // equisatisfiable — a reduced `sat` model is lifted back to the original
        // CNF variables through the reconstruction stack before the AIG/model
        // lift, and every `sat` result still replays against the original terms.
        // The `cnf_variables`/`cnf_clauses` stats above describe the
        // un-inprocessed encoding (baseline comparability); the formula actually
        // submitted to the SAT adapter is `solve_formula`. Inprocessing is bounded
        // to a fraction of the remaining solve budget (an admission size cap aside),
        // so on a formula it cannot usefully reduce it spends only that slice and
        // never starves the SAT solve — capping the downside while still capturing
        // the big reductions it does find.
        // From here on `stats` carries `aig_nodes` / `cnf_variables`, so a
        // reading taken at this boundary or later lifts to a real
        // `BvLayerStats` whose reached-stage fields are measurements.
        enter_stage!(crate::layers::BvStage::CnfInprocess);
        let inprocessed = maybe_inprocess(config, encoding.formula(), deadline, &mut stats);
        let solve_formula: &CnfFormula = inprocessed
            .as_ref()
            .map_or_else(|| encoding.formula(), |out| &out.formula);

        if let Some(result) = check_cnf_budgets(config, solve_formula, &mut stats) {
            self.stats = Some(stats);
            return Ok(result);
        }

        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            stats.solve = Duration::ZERO;
            self.stats = Some(stats);
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Timeout,
                detail: "pure-Rust BV backend timeout before SAT solve".to_owned(),
            }));
        }

        enter_stage!(crate::layers::BvStage::SatSearch);
        let solve_start = Instant::now();
        // Primary SAT search: the deadline-bounded native CDCL core, on every
        // path (ADR-1703). Its result feeds the reconstruction + replay below
        // (see `solve_with_native_cdcl`).
        // The reduction, handed to the search so its `unsat` proof is checked
        // against `encoding.formula()` — the formula this backend built — and
        // not merely against the reduced one it happened to search.
        let reduction = inprocessed
            .as_ref()
            .map(|out| (encoding.formula(), &out.link));
        let mut sat_result =
            primary_sat_search(config, solve_formula, deadline, &mut stats, reduction);
        stats.solve = solve_start.elapsed();
        // A DEFINITE verdict is kept regardless of the wall clock: the deadline is
        // a resource budget, not a correctness gate (ADR-1906). Only an UNDECIDED
        // result degrades to the timeout reason, so every `SatResult::Unknown`
        // sub-case keeps the exact `kind` and `detail` it had before.
        //
        // This gate used to be unconditional, and it discarded answers we had
        // already computed *and* already paid for: nine instances -- two of them
        // real SMT-LIB files through the shipping front door -- returned `unknown`
        // at a 10 s budget after spending 29-43 s, and `sat` at 300 s after
        // spending the same time. Re-reading the clock after the search cannot
        // refund the overrun; it only converts an answer into a non-answer. The
        // per-route safety argument (`sat` replay, the inline `unsat` DRAT check,
        // the incremental facade, the portfolio, and determinism) is in
        // `docs/research/03-measurements/late-result-keep-safety-2026-09-10.md`;
        // the measurement it answers is `why-43-satisfiable-qfbv-miss-2026-09-10.md`.
        //
        // Keeping the verdict does mean the model lift and the replay below run
        // past the deadline. That is bounded, size-proportional work (~164 ms
        // measured on `pspace/ndist.b.20000`) and it is not skippable in any case:
        // `handle_sat_result` cannot construct a `Sat` without replaying the model
        // against the ORIGINAL terms, which is what makes a late `sat` exactly as
        // checked as a timely one.
        if matches!(sat_result, SatResult::Unknown(_))
            && deadline.is_some_and(|deadline| Instant::now() >= deadline)
        {
            self.stats = Some(stats);
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Timeout,
                detail: "pure-Rust BV backend timeout after SAT search".to_owned(),
            }));
        }

        // CDCL(XOR) search fallback (ADR-0035): only on an `unknown` primary
        // verdict (timeout/budget), only when opted in, and only on a formula
        // carrying recognized XOR structure within the conservative clause cap.
        // Its `unsat` is the trusted `XorGaussian` ledger hole (no DRAT — XOR
        // reasoning is not RUP); its `sat` carries no trust cost (it threads the
        // same reconstruction + AIG/model/term replay the primary path uses and
        // is discarded on replay failure). This never weakens an existing definite
        // verdict — it can only *upgrade* an `unknown`.
        let mut xor_cdcl_unsat = false;
        if matches!(sat_result, SatResult::Unknown(_)) && config.xor_cdcl_fallback {
            let fallback = maybe_xor_cdcl_fallback(solve_formula, sat_result, &mut stats);
            sat_result = fallback.result;
            xor_cdcl_unsat = fallback.unsat_from_xor;
        }

        // The xor-derived `unsat` is the trusted `XorGaussian` hole and is NOT
        // RUP, so it cannot be DRAT-verified (the checker would correctly reject a
        // synthesized proof). Skip the proof route for it; only the native core's
        // `unsat` is DRAT-checked here.
        let prove = config.prove_unsat && !xor_cdcl_unsat;
        if let Some(reason) = ensure_unsat_proof_checked(
            prove,
            &sat_result,
            solve_formula,
            &mut stats,
            inprocessed.is_some(),
        )? {
            self.stats = Some(stats);
            return Ok(CheckResult::Unknown(reason));
        }

        // Lift a compacted `sat` model back to the original CNF variables (no-op
        // without inprocessing) so the AIG/model lift uses the original encoding:
        // `compaction.expand` (→ BVE-reduced width) then `reconstruction.extend`.
        let sat_result = reconstruct_sat_result(sat_result, inprocessed.as_ref());

        // One boundary for both remaining stages: `handle_sat_result` lifts the
        // model and replays it inside a single call, and splitting the mirror
        // finer would need either a callback into it or a second lock on the
        // replay path. `ModelLift` is therefore the last stage this mirror can
        // name, and a kill during the replay reads as one during the lift —
        // stated here rather than left for a reader to infer from a stage
        // stream that never mentions `model_replay`.
        enter_stage!(crate::layers::BvStage::ModelLift);
        let result = handle_sat_result(
            arena,
            assertions,
            replay_plan,
            &lowering,
            &encoding,
            sat_result,
            &mut stats,
        );
        self.stats = Some(stats);
        result
    }

    fn check_shared_guard_split(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        branches: &[TermId],
        config: &SolverConfig,
        deadline: Instant,
    ) -> Result<CheckResult, SolverError> {
        let mut combined = SolveStats {
            assertion_count: assertions.len() as u64,
            ..SolveStats::default()
        };
        let total_branches = branches.len();

        for (index, &branch) in branches.iter().enumerate() {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                record_split_progress(&mut combined, total_branches, index);
                self.stats = Some(combined);
                return Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Timeout,
                    detail: "shared-guard disjunction split exhausted its deadline".to_owned(),
                }));
            }
            let remaining_branches = total_branches - index;
            let fair_share = remaining / u32::try_from(remaining_branches).unwrap_or(u32::MAX);
            let branch_timeout = remaining.min(fair_share.max(Duration::from_secs(1)));
            let branch_config = config.clone().with_timeout(branch_timeout);
            let mut backend = Self::new();
            let result = backend.check_with_replay_internal(
                arena,
                &[branch],
                None,
                &branch_config,
                false,
            )?;
            if let Some(stats) = backend.last_stats() {
                merge_split_stats(&mut combined, stats);
            }

            match result {
                CheckResult::Unsat => {}
                CheckResult::Sat(mut model) => {
                    for (symbol, _name, sort) in arena.symbols() {
                        if model.get(symbol).is_none() {
                            let Some(value) = well_founded_default(arena, sort) else {
                                record_split_progress(&mut combined, total_branches, index + 1);
                                self.stats = Some(combined);
                                return Ok(CheckResult::Unknown(UnknownReason {
                                    kind: UnknownKind::Incomplete,
                                    detail: "shared-guard split SAT branch could not complete an \
                                             uninhabited symbol sort"
                                        .to_owned(),
                                }));
                            };
                            model.set(symbol, value);
                        }
                    }
                    let assignment = model.to_assignment();
                    if assertions.iter().all(|&assertion| {
                        matches!(eval(arena, assertion, &assignment), Ok(Value::Bool(true)))
                    }) {
                        record_split_progress(&mut combined, total_branches, index + 1);
                        push_count(&mut combined, "shared_guard_split_sat", 1);
                        self.stats = Some(combined);
                        return Ok(CheckResult::Sat(model));
                    }
                    record_split_progress(&mut combined, total_branches, index + 1);
                    self.stats = Some(combined);
                    return Ok(CheckResult::Unknown(UnknownReason {
                        kind: UnknownKind::Incomplete,
                        detail: "shared-guard split SAT model did not replay against the original \
                                 disjunction"
                            .to_owned(),
                    }));
                }
                CheckResult::Unknown(reason) => {
                    record_split_progress(&mut combined, total_branches, index + 1);
                    self.stats = Some(combined);
                    return Ok(CheckResult::Unknown(reason));
                }
            }
        }

        record_split_progress(&mut combined, total_branches, total_branches);
        push_count(&mut combined, "shared_guard_split_unsat", 1);
        self.stats = Some(combined);
        Ok(CheckResult::Unsat)
    }
}

const MIN_SHARED_GUARD_SPLIT_DAG_NODES: u64 = 5_000;
const MIN_SHARED_GUARD_SPLIT_BRANCHES: usize = 4;
const MAX_SHARED_GUARD_SPLIT_BRANCHES: usize = 16;

/// Recognizes one large disjunction of negated obligations with an identical
/// implication antecedent. Splitting this exact shape is denotation-preserving:
/// `or(not(A => C_i))` is satisfiable iff at least one branch is satisfiable,
/// and it is unsatisfiable iff every branch is unsatisfiable.
fn shared_guard_split_branches(
    arena: &TermArena,
    assertions: &[TermId],
    dag_nodes: u64,
) -> Option<Vec<TermId>> {
    if assertions.len() != 1 || dag_nodes < MIN_SHARED_GUARD_SPLIT_DAG_NODES {
        return None;
    }

    let mut stack = vec![assertions[0]];
    let mut branches = BTreeSet::new();
    while let Some(term) = stack.pop() {
        match arena.node(term) {
            TermNode::App {
                op: Op::BoolOr,
                args,
            } if args.len() == 2 => {
                stack.push(args[1]);
                stack.push(args[0]);
            }
            TermNode::BoolConst(false) => {}
            _ => {
                branches.insert(term);
            }
        }
    }
    if !(MIN_SHARED_GUARD_SPLIT_BRANCHES..=MAX_SHARED_GUARD_SPLIT_BRANCHES)
        .contains(&branches.len())
    {
        return None;
    }

    let mut common_antecedent = None;
    for &branch in &branches {
        let TermNode::App {
            op: Op::BoolNot,
            args: not_args,
        } = arena.node(branch)
        else {
            return None;
        };
        if not_args.len() != 1 {
            return None;
        }
        let TermNode::App {
            op: Op::BoolImplies,
            args: implies_args,
        } = arena.node(not_args[0])
        else {
            return None;
        };
        if implies_args.len() != 2 {
            return None;
        }
        match common_antecedent {
            None => common_antecedent = Some(implies_args[0]),
            Some(antecedent) if antecedent == implies_args[0] => {}
            Some(_) => return None,
        }
    }

    Some(branches.into_iter().collect())
}

fn merge_split_stats(combined: &mut SolveStats, branch: &SolveStats) {
    combined.translate += branch.translate;
    combined.solve += branch.solve;
    combined.model_lift += branch.model_lift;
    combined.terms_translated = combined
        .terms_translated
        .saturating_add(branch.terms_translated);
    for (name, value) in &branch.backend {
        if let Some((_, total)) = combined.backend.iter_mut().find(|(key, _)| key == name) {
            *total += value;
        } else {
            combined.backend.push((name.clone(), *value));
        }
    }
}

fn record_split_progress(stats: &mut SolveStats, branches: usize, completed: usize) {
    push_count(
        stats,
        "shared_guard_split_branches",
        u64::try_from(branches).expect("shared-guard branch cap fits u64"),
    );
    push_count(
        stats,
        "shared_guard_split_completed",
        u64::try_from(completed).expect("shared-guard branch cap fits u64"),
    );
}

impl SolverBackend for SatBvBackend {
    /// The pure-Rust SAT-BV path IS what `IncrementalBvSolver` runs warmly:
    /// the same lowering, the same CNF encoder, the same CDCL core. This is the
    /// only `true` in the workspace (roadmap item 1.1b).
    fn warm_bv_engine_equivalent(&self) -> bool {
        true
    }

    fn capabilities(&self) -> Capabilities {
        Capabilities {
            name: "axeyum-sat-bv native-cdcl".to_owned(),
            produces_models: true,
            complete: true,
        }
    }

    fn check(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        let result = self.check_with_replay(arena, assertions, None, config);
        // Single publish point for `BvLayerStats` collection (see
        // `crate::layers::publish_bv_layer_stats`): a no-op unless a
        // `BvLayerStatsGuard` is active on this thread, and reads only the
        // `SolveStats` this check already computed — no new work on the
        // default (uncollected) path.
        if let Some(stats) = &self.stats {
            crate::layers::publish_bv_layer_stats(stats);
        }
        result
    }

    fn check_query(
        &mut self,
        arena: &TermArena,
        query: &Query,
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        let plan = query.plan_full(arena);
        let assertions = plan.solver_terms().collect::<Vec<_>>();
        let result = self.check_with_replay(arena, &assertions, Some(&plan), config);
        if let Some(stats) = &self.stats {
            crate::layers::publish_bv_layer_stats(stats);
        }
        result
    }

    fn last_stats(&self) -> Option<&SolveStats> {
        self.stats.as_ref()
    }
}

/// Records the AIG and (un-inprocessed) CNF size counters for the most recent
/// encoding into `stats.backend`.
fn record_encoding_stats(stats: &mut SolveStats, lowering: &BitLowering, encoding: &CnfEncoding) {
    let formula = encoding.formula();
    stats.backend.push((
        "aig_nodes".to_owned(),
        usize_to_f64(lowering.aig().node_count()),
    ));
    stats.backend.push((
        "aig_inputs".to_owned(),
        usize_to_f64(lowering.aig().input_count()),
    ));
    stats.backend.push((
        "cnf_variables".to_owned(),
        usize_to_f64(formula.variable_count()),
    ));
    stats.backend.push((
        "cnf_clauses".to_owned(),
        usize_to_f64(formula.clauses().len()),
    ));
    let aig = lowering.aig().construction_stats();
    push_count(stats, "aig_and_requests", aig.and_requests);
    push_count(
        stats,
        "aig_and_trivial_simplifications",
        aig.and_trivial_simplifications,
    );
    push_count(
        stats,
        "aig_and_absorption_simplifications",
        aig.and_absorption_simplifications,
    );
    push_count(
        stats,
        "aig_and_structural_hash_hits",
        aig.and_structural_hash_hits,
    );
    push_count(stats, "aig_and_nodes_created", aig.and_nodes_created);

    record_bit_demand_stats(stats, lowering);
    record_bit_lowering_memo_stats(stats, lowering, encoding);

    let cnf = encoding.stats();
    push_duration_ms(stats, "cnf_plan_ms", cnf.planning);
    push_duration_ms(stats, "cnf_allocate_ms", cnf.variable_allocation);
    push_duration_ms(stats, "cnf_gate_encode_ms", cnf.gate_encoding);
    push_duration_ms(stats, "cnf_root_encode_ms", cnf.root_encoding);
    push_count(stats, "cnf_reachable_nodes", cnf.reachable_nodes);
    push_count(stats, "cnf_skipped_helper_nodes", cnf.skipped_helper_nodes);
    push_count(stats, "cnf_direct_root_nodes", cnf.direct_root_nodes);
    push_count(stats, "cnf_xor_gates", cnf.xor_gates);
    push_count(stats, "cnf_not_ite_gates", cnf.not_ite_gates);
    push_count(stats, "cnf_not_and_gates", cnf.not_and_gates);
    push_count(stats, "cnf_and_tree_gates", cnf.and_tree_gates);
    push_count(stats, "cnf_binary_and_gates", cnf.binary_and_gates);
    push_count(stats, "cnf_clause_attempts", cnf.clause_attempts);
    push_count(
        stats,
        "cnf_tautological_clauses_skipped",
        cnf.tautological_clauses_skipped,
    );
    push_count(
        stats,
        "cnf_duplicate_clauses_skipped",
        cnf.duplicate_clauses_skipped,
    );
    push_count(stats, "cnf_clauses_emitted", cnf.clauses_emitted);
    record_cnf_construction_profile(stats, cnf.construction_profile);
}

fn record_bit_demand_stats(stats: &mut SolveStats, lowering: &BitLowering) {
    let demand = lowering.demand_stats();
    push_count(
        stats,
        "bit_demand_profile_complete",
        u64::from(demand.profile_complete),
    );
    push_count(
        stats,
        "bit_demand_lowering_applied",
        u64::from(demand.lowering_applied),
    );
    push_count(
        stats,
        "range_demand_decision",
        u64::from(demand.range_decision.code()),
    );
    push_duration_ms(stats, "range_demand_admission_ms", demand.admission);
    push_count(
        stats,
        "range_demand_estimated_bits_avoided",
        demand.estimated_bits_avoided,
    );
    push_count(
        stats,
        "range_demand_analysis_work_budget",
        demand.analysis_work_budget,
    );
    push_count(stats, "range_demand_analysis_work", demand.analysis_work);
    push_count(stats, "range_demand_merges", demand.range_merges);
    push_count(stats, "range_demand_promotions", demand.range_promotions);
    push_duration_ms(stats, "bit_demand_analysis_ms", demand.analysis);
    push_count(stats, "term_bit_requests", demand.term_bit_requests);
    push_count(stats, "term_bits_available", demand.term_bits_available);
    push_count(stats, "term_bits_demanded", demand.term_bits_demanded);
    push_count(stats, "term_bits_lowered", demand.term_bits_lowered);
    push_count(stats, "symbol_bit_requests", demand.symbol_bit_requests);
    push_count(stats, "symbol_bits_available", demand.symbol_bits_available);
    push_count(stats, "symbol_bits_demanded", demand.symbol_bits_demanded);
    push_count(stats, "symbol_bits_lowered", demand.symbol_bits_lowered);
}

fn record_bit_lowering_memo_stats(
    stats: &mut SolveStats,
    lowering: &BitLowering,
    encoding: &CnfEncoding,
) {
    let memo = lowering.memo_stats();
    push_count(
        stats,
        "bit_lowering_memo_profile_complete",
        u64::from(memo.profile_complete),
    );
    push_count(
        stats,
        "bit_lowering_memo_representation",
        u64::from(memo.representation.code()),
    );
    push_count(stats, "bit_lowering_memo_source_terms", memo.source_terms);
    push_count(stats, "bit_lowering_memo_slots", memo.slots);
    push_count(stats, "bit_lowering_memo_occupied", memo.occupied);
    push_count(stats, "bit_lowering_memo_lookups", memo.lookups);
    push_count(stats, "bit_lowering_memo_hits", memo.hits);
    push_count(stats, "bit_lowering_memo_writes", memo.writes);
    push_count(
        stats,
        "bit_lowering_memo_payload_literals",
        memo.payload_literals,
    );
    push_count(
        stats,
        "bit_lowering_memo_payload_capacity_literals",
        memo.payload_capacity_literals,
    );
    push_count(
        stats,
        "bit_lowering_memo_logical_header_bytes",
        memo.logical_header_bytes,
    );
    push_count(
        stats,
        "bit_lowering_memo_logical_payload_bytes",
        memo.logical_payload_bytes,
    );
    push_count(
        stats,
        "bit_lowering_memo_logical_total_bytes",
        memo.logical_total_bytes,
    );
    push_count(
        stats,
        "bit_lowering_memo_payload_capacity_bytes",
        memo.payload_capacity_bytes,
    );
    push_count(stats, "bit_lowering_memo_root_bits", memo.root_bits);
    push_count(
        stats,
        "bit_lowering_memo_expected_root_bits",
        memo.expected_root_bits,
    );
    push_count(
        stats,
        "bit_lowering_memo_invariants_hold",
        u64::from(memo.invariants_hold),
    );
    if memo.profile_complete {
        push_digest(
            stats,
            "bit_lowering_structure_digest",
            lowering_structure_digest(lowering),
        );
        push_digest(
            stats,
            "cnf_structure_digest",
            cnf_structure_digest(encoding),
        );
    }
}

const PROFILE_FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const PROFILE_FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

fn digest_u64(digest: &mut u64, value: u64) {
    for byte in value.to_le_bytes() {
        *digest ^= u64::from(byte);
        *digest = digest.wrapping_mul(PROFILE_FNV_PRIME);
    }
}

fn digest_bytes(digest: &mut u64, bytes: &[u8]) {
    digest_u64(digest, usize_to_u64(bytes.len()));
    for &byte in bytes {
        *digest ^= u64::from(byte);
        *digest = digest.wrapping_mul(PROFILE_FNV_PRIME);
    }
}

fn digest_aig_lit(digest: &mut u64, literal: AigLit) {
    digest_u64(digest, usize_to_u64(literal.node().index()));
    digest_u64(digest, u64::from(literal.is_inverted()));
}

fn lowering_structure_digest(lowering: &BitLowering) -> u64 {
    let mut digest = PROFILE_FNV_OFFSET;
    digest_u64(&mut digest, usize_to_u64(lowering.aig().node_count()));
    for (_, node) in lowering.aig().nodes() {
        match node {
            AigNode::ConstFalse => digest_u64(&mut digest, 0),
            AigNode::Input(input) => {
                digest_u64(&mut digest, 1);
                digest_u64(&mut digest, usize_to_u64(input.index()));
            }
            AigNode::And(left, right) => {
                digest_u64(&mut digest, 2);
                digest_aig_lit(&mut digest, left);
                digest_aig_lit(&mut digest, right);
            }
        }
    }
    for input in lowering.aig().inputs() {
        digest_u64(&mut digest, usize_to_u64(input.id.index()));
        digest_u64(&mut digest, usize_to_u64(input.node.index()));
        digest_bytes(&mut digest, input.label.as_bytes());
    }
    for root in lowering.roots() {
        digest_u64(&mut digest, usize_to_u64(root.term().index()));
        digest_u64(&mut digest, usize_to_u64(root.bits().len()));
        for &literal in root.bits() {
            digest_aig_lit(&mut digest, literal);
        }
    }
    for binding in lowering.term_bits() {
        digest_u64(&mut digest, usize_to_u64(binding.term.index()));
        digest_u64(&mut digest, u64::from(binding.bit_index));
        digest_aig_lit(&mut digest, binding.literal);
    }
    for input in lowering.symbol_inputs() {
        digest_u64(&mut digest, usize_to_u64(input.symbol.index()));
        digest_u64(&mut digest, u64::from(input.bit_index));
        digest_u64(&mut digest, usize_to_u64(input.input.index()));
        digest_aig_lit(&mut digest, input.literal);
        digest_bytes(&mut digest, input.symbol_name.as_bytes());
    }
    digest
}

fn cnf_structure_digest(encoding: &CnfEncoding) -> u64 {
    let mut digest = PROFILE_FNV_OFFSET;
    digest_u64(
        &mut digest,
        usize_to_u64(encoding.formula().variable_count()),
    );
    for clause in encoding.formula().clauses() {
        digest_u64(&mut digest, usize_to_u64(clause.lits().len()));
        for &literal in clause.lits() {
            digest_u64(&mut digest, usize_to_u64(literal.var().index()));
            digest_u64(&mut digest, u64::from(literal.is_negated()));
        }
    }
    for root in encoding.roots() {
        digest_aig_lit(&mut digest, root.aig_literal);
        match root.cnf_lit {
            EncodedLit::Const(value) => {
                digest_u64(&mut digest, 0);
                digest_u64(&mut digest, u64::from(value));
            }
            EncodedLit::Lit(literal) => {
                digest_u64(&mut digest, 1);
                digest_u64(&mut digest, usize_to_u64(literal.var().index()));
                digest_u64(&mut digest, u64::from(literal.is_negated()));
            }
        }
    }
    for binding in encoding.variable_bindings() {
        digest_u64(&mut digest, usize_to_u64(binding.variable.index()));
        digest_aig_lit(&mut digest, binding.aig_literal);
    }
    digest
}

fn push_digest(stats: &mut SolveStats, key: &str, digest: u64) {
    push_count(stats, &format!("{key}_hi"), digest >> 32);
    push_count(stats, &format!("{key}_lo"), digest & u64::from(u32::MAX));
}

fn record_cnf_construction_profile(stats: &mut SolveStats, profile: CnfConstructionProfile) {
    push_count(
        stats,
        "cnf_construction_profile_complete",
        u64::from(profile.profile_complete),
    );
    push_count(
        stats,
        "cnf_declared_clause_literals",
        profile.declared_clause_literals,
    );
    push_count(
        stats,
        "cnf_visited_clause_literals",
        profile.visited_clause_literals,
    );
    push_count(
        stats,
        "cnf_false_constants_dropped",
        profile.false_constants_dropped,
    );
    push_count(
        stats,
        "cnf_repeated_literals_dropped",
        profile.repeated_literals_dropped,
    );
    push_count(
        stats,
        "cnf_true_constant_tautologies",
        profile.true_constant_tautologies,
    );
    push_count(
        stats,
        "cnf_complementary_literal_tautologies",
        profile.complementary_literal_tautologies,
    );
    push_count(stats, "cnf_canonical_literals", profile.canonical_literals);
    push_count(
        stats,
        "cnf_canonical_empty_clauses",
        profile.canonical_empty_clauses,
    );
    push_count(
        stats,
        "cnf_canonical_unit_clauses",
        profile.canonical_unit_clauses,
    );
    push_count(
        stats,
        "cnf_canonical_binary_clauses",
        profile.canonical_binary_clauses,
    );
    push_count(
        stats,
        "cnf_canonical_ternary_clauses",
        profile.canonical_ternary_clauses,
    );
    push_count(
        stats,
        "cnf_canonical_larger_clauses",
        profile.canonical_larger_clauses,
    );
    push_count(
        stats,
        "cnf_primary_vacant_probes",
        profile.primary_vacant_probes,
    );
    push_count(
        stats,
        "cnf_primary_occupied_probes",
        profile.primary_occupied_probes,
    );
    push_count(
        stats,
        "cnf_primary_exact_duplicates",
        profile.primary_exact_duplicates,
    );
    push_count(
        stats,
        "cnf_collision_bucket_comparisons",
        profile.collision_bucket_comparisons,
    );
    push_count(
        stats,
        "cnf_collision_exact_duplicates",
        profile.collision_exact_duplicates,
    );
    push_count(stats, "cnf_collision_inserts", profile.collision_inserts);
}

fn record_duplicate_origin_profile(stats: &mut SolveStats, profile: &CnfDuplicateOriginProfile) {
    push_count(
        stats,
        "cnf_duplicate_origin_profile_complete",
        u64::from(profile.profile_complete),
    );
    push_count(
        stats,
        "cnf_duplicate_origin_clauses",
        profile.duplicate_clauses,
    );
    push_count(
        stats,
        "cnf_duplicate_origin_canonical_literals",
        profile.duplicate_canonical_literals,
    );
    for row in &profile.rows {
        let relation = if row.same_owner { "same" } else { "cross" };
        let prefix = format!(
            "cnf_duplicate_origin|{}|{}|{relation}|",
            row.first_origin.stable_key(),
            row.duplicate_origin.stable_key(),
        );
        for (metric, value) in [
            ("clauses", row.duplicate_clauses),
            ("canonical_literals", row.duplicate_canonical_literals),
            ("empty_clauses", row.empty_clauses),
            ("empty_literals", row.empty_literals),
            ("unit_clauses", row.unit_clauses),
            ("unit_literals", row.unit_literals),
            ("binary_clauses", row.binary_clauses),
            ("binary_literals", row.binary_literals),
            ("ternary_clauses", row.ternary_clauses),
            ("ternary_literals", row.ternary_literals),
            ("larger_clauses", row.larger_clauses),
            ("larger_literals", row.larger_literals),
        ] {
            push_count(stats, &format!("{prefix}{metric}"), value);
        }
    }
    let overlap = &profile.parity_overlap;
    push_count(
        stats,
        "cnf_parity_overlap_profile_complete",
        u64::from(overlap.profile_complete),
    );
    push_count(
        stats,
        "cnf_parity_overlap_clauses",
        overlap.duplicate_clauses,
    );
    push_count(
        stats,
        "cnf_parity_overlap_canonical_literals",
        overlap.duplicate_canonical_literals,
    );
    for row in &overlap.rows {
        let prefix = format!(
            "cnf_parity_overlap|{}|{}|{}|",
            row.relation.as_str(),
            row.first_shape.stable_key(),
            row.duplicate_shape.stable_key(),
        );
        for (metric, value) in [
            ("clauses", row.duplicate_clauses),
            ("canonical_literals", row.duplicate_canonical_literals),
            ("empty_clauses", row.empty_clauses),
            ("empty_literals", row.empty_literals),
            ("unit_clauses", row.unit_clauses),
            ("unit_literals", row.unit_literals),
            ("binary_clauses", row.binary_clauses),
            ("binary_literals", row.binary_literals),
            ("ternary_clauses", row.ternary_clauses),
            ("ternary_literals", row.ternary_literals),
            ("larger_clauses", row.larger_clauses),
            ("larger_literals", row.larger_literals),
        ] {
            push_count(stats, &format!("{prefix}{metric}"), value);
        }
    }
}

/// A Tseitin formula after CNF inprocessing, plus the maps that lift a model of
/// the reduced formula back to the original CNF variables and a refutation of
/// it back to the formula this backend encoded.
///
/// One name for one thing: since ADR-1810 the sequencing that produces it lives
/// in `axeyum_cnf::inprocess`, so this is that module's own outcome type rather
/// than a parallel copy of it. The lift is a two-step composition. BVE removes
/// clauses/variables but does not renumber, so its reduced formula keeps the
/// original (wide) variable count; `compact` then densely renumbers the live
/// variables, lowering [`CnfFormula::variable_count`] so the variable-bound
/// admission gate admits cases that eliminated millions of variables. The
/// `formula` field is the *compacted* formula (the one submitted to the SAT
/// solver); a `sat` model of it is lifted by `compaction.expand` (-> original-
/// width, BVE-reduced model) and then `reconstruction.extend` (-> full original
/// model), in that order, and an `unsat` proof of it is lifted the other way by
/// `link`.
type Inprocessed = ScheduledInprocess;

/// Inprocessing admission bound. Since T1.1.4 both passes are occurrence-list
/// indexed and near-linear with internal work budgets (`axeyum_cnf::simplify`
/// forward one-watch subsumption, `axeyum_cnf::bve` full occurrence lists + a
/// touched queue), so they no longer blow a solve budget on the wide bit-blasted
/// CNFs that the old `O(clauses²)`/`O(variables·clauses)` versions hung on (the
/// earlier 5k-var/20k-clause cap saw 13–22 s passes; the indexed versions run in
/// milliseconds on the curated slice).
///
/// The ceiling is deliberately set above the public-corpus `EncodingBudget` band
/// (`QF_BV` p4dfa instances reach ~2.1 M variables / ~8 M clauses) so inprocessing
/// is actually attempted on the cases it can convert: BVE measured a consistent
/// ~28 % clause reduction there, which clears their CNF-budget overshoot. This is
/// safe because [`maybe_inprocess`] time-bounds the passes to half the remaining
/// solve budget (`eliminate_variables_within`/`simplify_within` truncate between
/// variables/clauses and the partial result stays sound) — the *budget*, not this
/// cap, is the hang-preventer. The cap only excludes pathological encodings whose
/// occurrence lists would not fit a single pass even to start.
const INPROCESS_MAX_VARIABLES: usize = 4_000_000;
const INPROCESS_MAX_CLAUSES: usize = 16_000_000;

/// Ceiling on the concatenated `DRAT` proof (reduction prefix + search steps)
/// this backend will hold in RAM to check against the original formula.
///
/// It exists because the prefix is proportional to the FORMULA, not to the
/// search: ADR-1750 measured BVE's at **37.7 M steps** on a 3.1 M-variable
/// `p4dfa` instance against the search's ~36 k, three orders of magnitude
/// apart. A `Vec<DratStep>` of that size is several gigabytes before the
/// checker allocates anything of its own, so an unbounded in-RAM
/// concatenation would turn a checked `unsat` into an OOM on exactly the
/// instances where inprocessing pays.
///
/// Exceeding it is **not** a silent downgrade: the check falls back to the
/// reduced formula and says so through
/// `unsat_proof_checked_against_reduced` + `unsat_proof_reduced_reason = 2`,
/// with the step count that would have been needed.
///
/// **The headroom is thin and the number is measured, not assumed.** Over the
/// 200-file `QF_BV` parity list on 2026-09-08 (117 `unsat`, every one checked
/// against the original) the prefix was a median of 658 steps, p90 71,881, and
/// a **maximum of 1,971,102** — so the cap clears the worst observed instance
/// by only **4.06x**, not by the orders of magnitude a reader might assume from
/// its size. Two things follow. A larger corpus can be expected to cross it,
/// which is the intended signal to wire the streaming route
/// (`ReductionLink::lifting_sink` into a `TextProofSink`, checked by
/// `check_drat_backward_reader`) rather than to raise the constant. And the
/// peak is about **twice** what the step count suggests, because
/// `check_unsat` clones the stored prefix into the concatenation — the cap is
/// on steps, and the allocation it is standing in for is roughly
/// `2 x steps x (32 + 8 x literals-per-clause)` bytes.
///
/// See `docs/research/03-measurements/inprocessed-unsat-proof-coverage-2026-09-08.md`.
const MAX_LINKED_PROOF_STEPS: usize = 8_000_000;

/// XOR-propagation admission bound. Unlike subsumption/BVE, `xor_propagate` runs
/// Gaussian elimination over the recovered XOR system, which is `O(gates²·vars)`
/// and currently carries no internal deadline — so it gets a conservative,
/// separate clause cap so the first measured wiring cannot hang on the big
/// multiplier CNFs (the very instances whose dense parity structure only an
/// *in-search* Gaussian, not preprocessing, can collapse). Raised once the pass
/// is deadline-bounded.
const XOR_PROPAGATE_MAX_CLAUSES: usize = 20_000;

/// CDCL(XOR) search-fallback admission bound (ADR-0035). `solve_with_xor_cdcl`
/// is conflict-budgeted but carries **no wall-clock budget**, so the fallback is
/// gated by a conservative clause cap to keep it from running unbounded on very
/// large CNFs. The cap is generous enough to cover the curated multiplier
/// instances it is meant to crack (a few thousand clauses) while excluding the
/// pathologically large encodings. A size skip is recorded as a stat.
const XOR_CDCL_FALLBACK_MAX_CLAUSES: usize = 50_000;

/// Outcome of [`maybe_xor_cdcl_fallback`]: the (possibly upgraded) SAT result and
/// whether the `unsat` verdict came from the **trusted** (uncertified) CDCL(XOR)
/// core, so the caller can skip the standard DRAT proof route, which cannot
/// certify a non-RUP XOR refutation, and surface the `XorGaussian` trust hole.
///
/// `unsat_from_xor` is `true` only for an XOR-derived `unsat` that was *not*
/// independently certified. The pure-Gaussian-level-0 sub-case (the extracted XOR
/// system is inconsistent by Gaussian elimination alone, no branching) is checked
/// here via a per-query DRAT certificate ([`xor_gauss_drat_refutation`] +
/// [`check_drat`]); when that certificate validates the `unsat` is stamped
/// [`SatProofStatus::Checked`] and `unsat_from_xor` is `false`, so it flows
/// through the same checked-by-construction path the batsat/native `unsat` uses
/// (no trust cost). The harder interleaved CDCL(XOR) `unsat` (branching was
/// needed) stays `unsat_from_xor = true` — still the trusted `XorGaussian` hole.
struct XorCdclFallback {
    result: SatResult,
    unsat_from_xor: bool,
}

/// Runs CNF inprocessing when it is enabled and the formula is within the
/// admission bound. Records `inprocess_ms` and folds it into `stats.translate`; a
/// size skip is recorded too. Inprocessing is time-bounded to (at most) half the
/// remaining solve budget so the SAT solve always keeps the other half.
fn maybe_inprocess(
    config: &SolverConfig,
    formula: &CnfFormula,
    deadline: Option<Instant>,
    stats: &mut SolveStats,
) -> Option<Inprocessed> {
    if !config.cnf_inprocessing {
        return None;
    }
    if formula.variable_count() > INPROCESS_MAX_VARIABLES
        || formula.clauses().len() > INPROCESS_MAX_CLAUSES
    {
        stats
            .backend
            .push(("cnf_inprocessing_skipped_size".to_owned(), 1.0));
        return None;
    }
    // Spend at most half the remaining solve budget on inprocessing; the partial
    // result of an interrupted pass is still sound (subsumption is model-preserving,
    // BVE equisatisfiable with a valid reconstruction). Unbounded if there is no
    // solve deadline.
    let start = Instant::now();
    let inprocess_deadline = deadline.map(|dl| start + dl.saturating_duration_since(start) / 2);
    // Record the SLICE the passes were granted, not just what they spent. Without
    // it, a pass that took 3.0 s is indistinguishable between "that is what the
    // pass costs" and "that is where the clock cut it off" — the two call for
    // opposite work, and only the pair (spend, budget) separates them. Absent
    // when there is no solve deadline, so the key's presence also says whether a
    // truncation was even possible.
    if let Some(dl) = inprocess_deadline {
        push_duration_ms(
            stats,
            "inprocess_budget_ms",
            dl.saturating_duration_since(start),
        );
    }
    let out = inprocess(config, formula, inprocess_deadline, stats);
    let elapsed = start.elapsed();
    stats.translate += elapsed;
    push_duration_ms(stats, "inprocess_ms", elapsed);
    Some(out)
}

/// BVE's budget as a multiple of its own setup cost, in occurrence-list steps.
///
/// The pass builds occurrence lists over the whole formula before it can
/// consider a single variable, so `literals + 2 x variables` is the floor it
/// pays for existing. This multiple is what it may spend **on top of** that.
///
/// The value is measured, not inherited, and the measurement is unusual enough
/// to state. Over the pinned 200-file `QF_BV` parity list
/// (`bench-results/parity-lists/QF_BV.txt`), with the budget disabled so
/// nothing truncates, the work BVE spends spans **five orders of magnitude in
/// units of its own setup cost**: the point of its last elimination sits at 474
/// x setup at the median, 12,723 x at p90 and 39,654 x at the maximum. So there
/// is no multiple that is simultaneously generous to every file and frugal with
/// any of them, and picking one is a trade priced in seconds against
/// eliminations rather than a threshold that separates good runs from bad.
///
/// At `2000` that trade is: 51 of 143 files are cut, 200 s of the corpus's
/// 307 s of BVE time is not spent (115 s of it on the 20 files the clock was
/// cutting off anyway), and 98 of 143 files still reach their last elimination
/// inside the budget. The population being cut is the one worth cutting — 17 of
/// those 20 truncated files are decided by the *baseline* in under 4.3 s, seven
/// of them in under 120 ms.
/// See `docs/research/03-measurements/inprocessing-admission-2026-09-08.md`.
const BVE_BUDGET_SETUP_MULTIPLE: u64 = 2_000;

/// The smallest budget worth starting the pass for, as a multiple of setup.
///
/// This arms the accumulate-and-delay gate
/// (`axeyum_ir::budget::EffortPolicy::with_init_cost`), and it is `CaDiCaL`'s
/// rule stated for a single pre-search round: *do not start a pass whose fixed
/// setup cost the available budget cannot recover*
/// (`references/cadical/src/probe.cpp:902-907`, transcribed in
/// `docs/research/02-ecosystems/inprocessing-scheduling-2026-09/cadical-kissat-budget-model.md`
/// §2A.2). At `2` the pass must be able to afford its occurrence lists twice
/// over — once to build them, once to use them — or it does not start.
///
/// **When it can fire.** With no solve deadline the reference window is purely
/// size-proportional, so the ratio is [`BVE_BUDGET_SETUP_MULTIPLE`] by
/// construction and this gate is structurally unable to fire — that is a
/// property of a one-shot pre-search round, not an oversight, and it is why
/// the reference is *also* capped by what the granted slice can buy. The gate
/// fires on the population it was written for: a large formula meeting a small
/// remaining budget.
const BVE_MIN_RECOVERY_MULTIPLE: u64 = 2;

/// Occurrence-list steps this host expects to retire per millisecond, used only
/// to convert the granted wall slice into the budget primitive's unit.
///
/// This is the one host-dependent number in the decision, and it is confined to
/// the branch that already depends on the host: converting a wall-clock slice.
/// With no deadline it is not read at all and the budget is fully
/// deterministic.
///
/// Measured as `bve_work_spent / bve_ms` over the 97 parity files whose BVE ran
/// at least 20 ms: p10 170,671, **median 460,365**, p90 1,326,285. `400_000`
/// sits just under the median. Getting it wrong is not dangerous in either
/// direction — too high and the wall deadline truncates as it does today, too
/// low and the pass stops early with a still-equisatisfiable partial result —
/// which is why the size term, not this one, is the real brake.
const BVE_STEPS_PER_MILLISECOND: u64 = 400_000;

/// Subsumption's budget as a multiple of its own setup cost, in the same
/// occurrence-list-step unit BVE is budgeted in.
///
/// # This constant is a different KIND of decision from BVE's
///
/// BVE's `2000` was nearly free: 22.9 % of its work came after its last useful
/// action, so most of what the budget declined was waste. Subsumption's is
/// **1.5–2.2 %**, and its total spend sits between 131 x and 193 x setup across
/// the whole 200-file parity list — a factor of 1.5, against BVE's factor of 84.
/// The pass does work proportional to the formula and then stops.
///
/// So there is no free component here: every second this saves is bought by
/// giving up subsumptions, and the constant is chosen against a solved count
/// rather than against a waste figure. Measured 2026-09-08 over the pinned list
/// at 24 s, all arms concurrent and pinned to distinct physical P-cores:
///
/// | arm | decided | PAR-2 | subsume s | bve s |
/// |---|---:|---:|---:|---:|
/// | inprocessing off | 184 | 926.8 | — | — |
/// | subsumption unbudgeted | 185 | 1003.7 | 74.4 | 79.1 |
/// | `K = 100` | 184 | 1020.5 | 37.4 | 77.8 |
/// | **`K = 50`** | **186** | **960.5** | **29.9** | 111.1 |
///
/// `K = 50` is the shipped value: the best inprocessing arm measured on both
/// counts, 44.5 s of subsumption not spent, and it **recovers `div3.c.50`** —
/// the one file the 2026-09-08 admission lane's gated arm lost, where
/// subsumption ate a 10.8 s slice by itself. Under this budget that file's
/// subsumption stops at exactly `50 x setup` = 452,526,023 steps, 4.2 s, and the
/// whole solve returns `sat` in 22.4 s.
///
/// **Read `K = 100` before trusting the ranking.** It is worse than doing
/// nothing on PAR-2, which is not a monotone story, and the identical-arm
/// spread measured between two `off` runs on this host was 1 file and 17.6
/// PAR-2 points. The 43-point gap from unbudgeted to `K = 50` exceeds that; the
/// one-file difference in decided counts does not. Treat the seconds as
/// measured and the ordering of adjacent arms as provisional.
///
/// See `docs/research/03-measurements/subsumption-work-meter-2026-09-08.md`.
const SUBSUME_BUDGET_SETUP_MULTIPLE: u64 = 50;

/// Occurrence-list steps subsumption retires per millisecond on this host, used
/// only to convert a remaining wall slice into the budget's unit.
///
/// Separate from [`BVE_STEPS_PER_MILLISECOND`] because the two passes do
/// different things per step — subsumption's inner loop is a signature test and
/// a marked-literal walk, BVE's is a resolvent merge — so one number for both
/// would be a guess dressed as a shared constant, and the measurement says they
/// differ by 3.6x.
///
/// Measured 2026-09-08 as `subsume_work_spent / subsume_ms` over the parity
/// files whose subsumption ran at least 20 ms, on two runs at different host
/// load: p10 86,042 / 85,471, **median 127,599 / 172,489**, p90 154,908 /
/// 220,577. The shipped value is the lower median, which is the conservative
/// end. Against BVE's median of 460,365 — a subsumption step is the more
/// expensive one, which is the opposite of what a shared constant would have
/// assumed, and the reason there are two constants.
///
/// The spread between the two runs is the point of the caveat: this is the one
/// quantity here that moves with host load, which is why it governs only the
/// deadline branch.
///
/// Getting it wrong is not dangerous in either direction — too high and the
/// wall deadline truncates as it does today, too low and the pass stops early
/// with a still model-preserving partial result — but it is the one
/// host-dependent number in the decision, and it is confined to the branch that
/// already depends on the host. With no deadline it is not read at all.
const SUBSUME_STEPS_PER_MILLISECOND: u64 = 128_000;

/// Whether BVE drops lazily-removed clause ids from its occurrence lists.
///
/// BVE's lists live for the whole pass and an elimination kills clauses that sit
/// in many of them, so the dead-id constant is real here and
/// `bve_dead_occurrence_entries` measures it.
const BVE_COMPACT_OCCURRENCES: bool = false;

/// Reads a measurement lever overriding one pass's budget multiple.
///
/// **This exists to make the A/B arms of a corpus sweep runnable against one
/// binary, and for nothing else.** The shipped default is the constant; the
/// variable is how a sweep asks for "the same build with this pass unbudgeted"
/// without a second build whose differences it would then have to argue are
/// irrelevant. `off` (or `0`) means unbudgeted, which is why the multiple is
/// clamped at 1 rather than allowed to be a silent zero.
///
/// An unparseable value is ignored rather than defaulted to something else: a
/// typo must not quietly measure a different arm than the one named.
fn env_override_multiple(name: &str, default: u64) -> u64 {
    parse_multiple_lever(std::env::var(name).ok().as_deref(), default)
}

/// The lever's parsing rules, separated from the environment read so they are
/// testable at all.
///
/// A test that sets a process-wide environment variable is a gate on one shell
/// and races every other test in a threaded suite, so the decision lives here
/// and `env_override_multiple` is the thin read. `None` (absent) and an
/// unparseable value both keep `default`: a typo must not quietly measure a
/// different arm than the one named.
fn parse_multiple_lever(value: Option<&str>, default: u64) -> u64 {
    match value {
        None => default,
        Some(v) if v.eq_ignore_ascii_case("off") || v == "0" => u64::MAX,
        Some(v) => v.parse::<u64>().map_or(default, |n| n.max(1)),
    }
}

/// Whether occurrence-list compaction is enabled for the inprocessing passes.
///
/// A measurement lever like [`env_override_multiple`], and the default is the
/// answer this lane measured — see
/// `docs/research/03-measurements/subsumption-work-meter-2026-09-08.md`.
fn env_compact_occurrences(default: bool) -> bool {
    parse_compact_lever(std::env::var("AXEYUM_OCC_COMPACT").ok().as_deref(), default)
}

/// The compaction lever's parsing rules, separated from the environment read
/// for the same reason as [`parse_multiple_lever`].
fn parse_compact_lever(value: Option<&str>, default: bool) -> bool {
    match value {
        Some(v) if v == "1" || v.eq_ignore_ascii_case("on") => true,
        Some(v) if v == "0" || v.eq_ignore_ascii_case("off") => false,
        // Absent and unparseable both keep the shipped value: a typo must not
        // quietly measure a different arm than the one named.
        None | Some(_) => default,
    }
}

/// The constants one occurrence-list pass is admitted and budgeted by.
///
/// BVE and subsumption are budgeted by the *same* policy with *different*
/// numbers, so the policy is written once here and the numbers are named per
/// pass. Copying it would let the two drift into different shapes, and then
/// "BVE was granted 2000 x setup and subsumption 400 x" would stop being a
/// comparison — which is the whole reason both meters charge in the same unit.
#[derive(Debug, Clone, Copy)]
struct PassAdmission {
    /// Stat-key prefix (`bve` / `subsume`), so a reader can tell whose decision
    /// a counter describes.
    name: &'static str,
    /// What the pass may spend on top of its setup cost, as a multiple of it.
    budget_setup_multiple: u64,
    /// The smallest budget worth starting the pass for, as a multiple of setup.
    /// Arms the accumulate-and-delay gate; see [`BVE_MIN_RECOVERY_MULTIPLE`].
    min_recovery_multiple: u64,
    /// Occurrence-list steps this host retires per millisecond, used only to
    /// convert a remaining wall slice into the budget's unit.
    steps_per_millisecond: u64,
}

/// Decides whether one occurrence-list pass runs at all, and under what
/// deterministic work budget. `None` means it must not start.
///
/// # Why this is not a wall-clock decision
///
/// Measured 2026-09-08 over the pinned parity list, 16 of 195 files spent their
/// **entire** granted inprocessing slice inside a BVE that was then cut off
/// unfinished — 189 s of the corpus's 342 s, i.e. 55 % of all inprocessing cost
/// on 8 % of the files, and on five of them the baseline decides the query in
/// 88–116 ms. Halving or doubling the slice moves that number and fixes
/// nothing, because the slice was never the quantity that should have governed:
/// a pass should be bounded by the work it is worth, and "worth" is measured
/// against the formula, not against the clock.
///
/// So the reference window is `budget_setup_multiple x setup`, capped by what
/// the remaining slice can buy, and the standard accumulate-and-delay gate
/// refuses the round when that cannot recover setup `min_recovery_multiple`
/// times over. Both halves come from [`axeyum_ir::budget`] rather than being
/// re-derived here — this function chooses nothing but the arithmetic that
/// feeds them.
///
/// # Setup is exact, not an estimate
///
/// `literal_occurrences + 2 x variable_count` is what the passes' meters start
/// at (`axeyum_cnf::pass_work`): one step per literal occurrence connected plus
/// one per occurrence-list slot. Both passes charge in that unit, so one
/// admission function serves both. Subsumption's first round is at most this,
/// and below it only when clauses past its size limit go unconnected.
fn admit_occurrence_pass(
    admission: PassAdmission,
    formula: &CnfFormula,
    deadline: Option<Instant>,
    stats: &mut SolveStats,
) -> Option<u64> {
    let setup = (literal_occurrences(formula) + 2 * formula.variable_count()) as u64;
    let size_allowance = setup.saturating_mul(admission.budget_setup_multiple);
    let reference = match deadline {
        Some(dl) => {
            let remaining_ms =
                u64::try_from(dl.saturating_duration_since(Instant::now()).as_millis())
                    .unwrap_or(u64::MAX);
            size_allowance.min(remaining_ms.saturating_mul(admission.steps_per_millisecond))
        }
        None => size_allowance,
    };

    // The whole reference window: there is no other consumer to share it with at
    // the moment this pass is offered, so its share is 1000 per mille of it. The
    // window itself is already the fraction — `EffortPolicy::per_mille` would be
    // double-counting.
    let policy = EffortPolicy::new(1000)
        .with_min_reference(reference)
        .with_init_cost(admission.min_recovery_multiple);
    let mut account = EffortAccount::new(policy);
    // No search has run yet, so the numeraire reads zero and `min_reference`
    // supplies the whole window. This is the case `with_min_reference` exists
    // for; a pre-search round is the same code path as an in-search one, with a
    // bootstrap reference instead of an accrued one.
    let search = WorkMeter::new();
    let own = WorkMeter::new();

    push_count(stats, &format!("{}_setup_work", admission.name), setup);
    match account.request(&search, &own, setup) {
        Grant::Granted(budget) => {
            push_count(
                stats,
                &format!("{}_work_budget", admission.name),
                budget.limit(),
            );
            stats
                .backend
                .push((format!("{}_admitted", admission.name), 1.0));
            Some(budget.limit())
        }
        Grant::Delayed { accrued, threshold } => {
            push_count(
                stats,
                &format!("{}_admission_accrued", admission.name),
                accrued,
            );
            push_count(
                stats,
                &format!("{}_admission_threshold", admission.name),
                threshold,
            );
            stats
                .backend
                .push((format!("{}_admitted", admission.name), 0.0));
            None
        }
        // Unreachable with a fresh account (the backoff needs a recorded
        // failure), but a `_` arm here would silently absorb a future policy
        // change into "run anyway", which is the wrong default for a gate.
        Grant::BackedOff { .. } => {
            stats
                .backend
                .push((format!("{}_admitted", admission.name), 0.0));
            None
        }
    }
}

/// BVE's admission constants.
const BVE_ADMISSION: PassAdmission = PassAdmission {
    name: "bve",
    budget_setup_multiple: BVE_BUDGET_SETUP_MULTIPLE,
    min_recovery_multiple: BVE_MIN_RECOVERY_MULTIPLE,
    steps_per_millisecond: BVE_STEPS_PER_MILLISECOND,
};

/// Subsumption's admission constants. See [`SUBSUME_BUDGET_SETUP_MULTIPLE`].
const SUBSUME_ADMISSION: PassAdmission = PassAdmission {
    name: "subsume",
    budget_setup_multiple: SUBSUME_BUDGET_SETUP_MULTIPLE,
    min_recovery_multiple: BVE_MIN_RECOVERY_MULTIPLE,
    steps_per_millisecond: SUBSUME_STEPS_PER_MILLISECOND,
};

/// Decides whether BVE runs, and under what budget. See
/// [`admit_occurrence_pass`]; this names the constants and nothing else.
fn bve_admission(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    stats: &mut SolveStats,
) -> Option<u64> {
    admit_occurrence_pass(
        PassAdmission {
            budget_setup_multiple: env_override_multiple(
                "AXEYUM_BVE_BUDGET_MULTIPLE",
                BVE_BUDGET_SETUP_MULTIPLE,
            ),
            ..BVE_ADMISSION
        },
        formula,
        deadline,
        stats,
    )
}

/// Decides whether subsumption runs, and under what budget.
fn subsume_admission(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    stats: &mut SolveStats,
) -> Option<u64> {
    admit_occurrence_pass(
        PassAdmission {
            budget_setup_multiple: env_override_multiple(
                "AXEYUM_SUBSUME_BUDGET_MULTIPLE",
                SUBSUME_BUDGET_SETUP_MULTIPLE,
            ),
            ..SUBSUME_ADMISSION
        },
        formula,
        deadline,
        stats,
    )
}

/// The solver's [`InprocessObserver`]: the two things
/// [`axeyum_cnf::inprocess_scheduled`] cannot decide for itself.
///
/// The schedule moved into `axeyum-cnf` with ADR-1810; the *admission policy*
/// deliberately did not. A grant is derived from the solve deadline and from
/// host-measured throughput constants ([`BVE_STEPS_PER_MILLISECOND`],
/// [`SUBSUME_STEPS_PER_MILLISECOND`]) -- neither of which `axeyum-cnf` can see
/// -- and it pushes its own admission counters into the same [`SolveStats`] the
/// stage telemetry lands in. So the schedule asks, and this answers.
///
/// It asks at the moment each pass is offered rather than up front, which is
/// load-bearing: BVE's grant is computed over the post-subsume, post-vivify
/// formula, and that formula does not exist until the schedule is half-run.
struct BackendInprocessObserver<'a> {
    /// The inprocessing slice's deadline, the input the grants are derived from.
    deadline: Option<Instant>,
    /// Where both the admission counters and the schedule's stage telemetry go.
    stats: &'a mut SolveStats,
}

impl InprocessObserver for BackendInprocessObserver<'_> {
    fn grant(&mut self, pass: OccurrencePass, formula: &CnfFormula) -> Option<u64> {
        match pass {
            OccurrencePass::Subsume => subsume_admission(formula, self.deadline, self.stats),
            OccurrencePass::Bve => bve_admission(formula, self.deadline, self.stats),
        }
    }

    fn count(&mut self, name: &str, value: f64) {
        self.stats.backend.push((name.to_owned(), value));
    }
}

/// Runs subsumption, optional clause vivification, then bounded variable
/// elimination and compaction on `formula`, recording what each pass did in
/// `stats`.
///
/// Since ADR-1810 this is a call site and not a scheduler: the sequencing is
/// [`axeyum_cnf::inprocess_scheduled`], which is where the passes, `compact` and
/// [`ReductionLink`] already lived. What stays here is what depends on things
/// `axeyum-cnf` cannot see -- [`SolverConfig`], [`SolveStats`], and the
/// deadline-derived work grants -- and it reaches the schedule through
/// [`BackendInprocessObserver`].
///
/// The arms are built from [`SolverConfig`] **field by field** rather than by
/// naming a preset. `InprocessOptions::preprocess()` has `vivify: false` while
/// this path's `cnf_vivify` default is `true`, so a merge that reached for a
/// preset by name would have changed the shipping default silently.
fn inprocess(
    config: &SolverConfig,
    formula: &CnfFormula,
    deadline: Option<Instant>,
    stats: &mut SolveStats,
) -> Inprocessed {
    let schedule = InprocessSchedule {
        // Gaussian carries no internal deadline yet, hence a cap of its own; the
        // schedule itself declines to APPLY the units under `recording`, since a
        // Gaussian-implied unit is not RUP in general.
        xor_propagate: true,
        xor_propagate_max_clauses: XOR_PROPAGATE_MAX_CLAUSES,
        vivify: config.cnf_vivify,
        vivify_options: VivifyOptions::default(),
        // The step-guard is a `prove_unsat`-only alarm: it costs a `check_drat`
        // over the pass's own derivation, and it is only worth paying where a
        // certificate is being built.
        vivify_step_guard: config.prove_unsat,
        bve_compact_occurrences: env_compact_occurrences(BVE_COMPACT_OCCURRENCES),
        // Recording a prefix costs a `Vec<DratStep>` proportional to the FORMULA
        // (ADR-1750 measured BVE's at 37.7 M steps on a 3.1 M-variable
        // instance), which is not something to pay for on a path that will never
        // look at it.
        recording: config.prove_unsat,
    };
    let mut observer = BackendInprocessObserver { deadline, stats };
    inprocess_scheduled(formula, schedule, deadline, &mut observer)
}

/// Lifts a compacted `sat` assignment back to the original CNF variable space.
///
/// The lift composes the two inprocessing maps in order: `compaction.expand`
/// raises a compacted model up to the BVE-reduced (original-width) variable space
/// (placing live values and `false` placeholders for never-occurring indices),
/// then `reconstruction.extend` replays the BVE-eliminated variables to produce a
/// model of the pre-inprocessing formula. A no-op (identity) when inprocessing was
/// off or for non-`sat` results.
fn reconstruct_sat_result(result: SatResult, inprocessed: Option<&Inprocessed>) -> SatResult {
    match (result, inprocessed) {
        (SatResult::Sat(assignment), Some(inprocessed)) => {
            let reduced = inprocessed.compaction.expand(assignment.values());
            SatResult::Sat(CnfAssignment::new(
                inprocessed.reconstruction.extend(&reduced),
            ))
        }
        (result, _) => result,
    }
}

/// Runs the CDCL(XOR) search core on `formula` as a fallback for an `unknown`
/// batsat verdict (ADR-0035), gated by recognized XOR structure and a clause cap.
///
/// Called only when the caller has already confirmed the verdict is `unknown`
/// and the `xor_cdcl_fallback` flag is set. Records what fired in `stats.backend`.
/// The returned `result` keeps the original `unknown` unless the core reaches a
/// definite verdict:
///
/// - `Unsat` upgrades to `SatResult::Unsat`. The pure-Gaussian-level-0 sub-case
///   (the extracted XOR system is inconsistent by Gaussian elimination alone) is
///   `check_drat`-certified here via [`certify_pure_gauss_xor_unsat`]; on success
///   it is stamped `SatProofStatus::Checked` with `unsat_from_xor = false`.
///   Otherwise it is the trusted `XorGaussian` hole (`unsat_from_xor = true`, no
///   DRAT proof) — the interleaved CDCL(XOR) case is not certifiable here yet.
/// - `Sat(values)` upgrades to `SatResult::Sat` over `formula`'s variable space;
///   it then flows through the same reconstruction + AIG/model/term replay the
///   batsat path uses, so a wrong model is rejected at replay (never a wrong sat).
/// - `Unknown` keeps the original batsat `unknown`.
fn maybe_xor_cdcl_fallback(
    formula: &CnfFormula,
    original: SatResult,
    stats: &mut SolveStats,
) -> XorCdclFallback {
    // Clause cap: the search core has no wall-clock budget, so a huge CNF could
    // run unbounded. Skip (and record) above the cap.
    if formula.clauses().len() > XOR_CDCL_FALLBACK_MAX_CLAUSES {
        stats
            .backend
            .push(("xor_cdcl_fallback_skipped_size".to_owned(), 1.0));
        return XorCdclFallback {
            result: original,
            unsat_from_xor: false,
        };
    }
    // Only worth running where XOR structure was actually recognized (the parity
    // structure the multiplier wall hides behind); otherwise it is just a slower
    // resolution search with no algebraic edge.
    if extract_xors(formula).num_recognized == 0 {
        stats
            .backend
            .push(("xor_cdcl_fallback_no_xor".to_owned(), 1.0));
        return XorCdclFallback {
            result: original,
            unsat_from_xor: false,
        };
    }

    stats
        .backend
        .push(("xor_cdcl_fallback_fired".to_owned(), 1.0));
    match solve_with_xor_cdcl(formula) {
        XorCdclResult::Unsat => {
            stats
                .backend
                .push(("xor_cdcl_fallback_unsat".to_owned(), 1.0));
            // Pure-Gaussian-level-0 sub-case: if the extracted XOR system is
            // inconsistent by Gaussian elimination *alone* (no branching), emit a
            // per-query DRAT certificate of the conflict subset and validate it
            // with the independent `check_drat`. A validated certificate makes
            // this `unsat` checked-by-construction (stamped `Checked`,
            // `unsat_from_xor = false`); it then rides the same accepted-as-checked
            // path the batsat/native `unsat` uses. If the system is not pure-Gauss
            // UNSAT (the conflict needed interleaved CDCL branching) or the
            // certificate fails to validate, keep the prior trusted behavior.
            if certify_pure_gauss_xor_unsat(formula) {
                stats
                    .backend
                    .push(("xor_cdcl_fallback_unsat_drat_checked".to_owned(), 1.0));
                XorCdclFallback {
                    result: SatResult::Unsat(SatUnsatEvidence {
                        proof: SatProofStatus::Checked,
                        failed_assumptions: Vec::new(),
                    }),
                    unsat_from_xor: false,
                }
            } else {
                XorCdclFallback {
                    result: SatResult::Unsat(SatUnsatEvidence {
                        proof: SatProofStatus::Unchecked,
                        failed_assumptions: Vec::new(),
                    }),
                    unsat_from_xor: true,
                }
            }
        }
        XorCdclResult::Sat(values) => {
            stats
                .backend
                .push(("xor_cdcl_fallback_sat".to_owned(), 1.0));
            XorCdclFallback {
                result: SatResult::Sat(CnfAssignment::new(values)),
                unsat_from_xor: false,
            }
        }
        XorCdclResult::Unknown => {
            stats
                .backend
                .push(("xor_cdcl_fallback_unknown".to_owned(), 1.0));
            XorCdclFallback {
                result: original,
                unsat_from_xor: false,
            }
        }
    }
}

/// Whether the formula's `unsat` is certified by a `check_drat`-validated DRAT
/// refutation of the **pure-Gaussian-level-0** XOR sub-case.
///
/// The clean, independently-decidable sub-case: the XOR system recovered from
/// `formula` ([`extract_xors`]) is inconsistent by Gaussian elimination *alone*
/// (no CDCL branching). When so, [`axeyum_cnf::Gf2System::unsat_reason_subset`] surfaces the
/// subset `S` of original XOR constraints whose GF(2)-sum is `0 = 1`, and
/// [`xor_gauss_drat_refutation`] builds a DRAT refutation of `CNF(S)`. The proof
/// is then re-validated end to end by the independent [`check_drat`] (a different
/// implementation than the producer): only `Ok(true)` — the proof genuinely
/// derives the empty clause from `CNF(S)` — returns `true`.
///
/// Soundness link to the original query: each recovered XOR gate is logically
/// entailed by a clause-subset of `formula` (the same entailment the XOR
/// inprocessing path relies on), so an inconsistent subset of those XORs makes
/// the formula UNSAT, and `CNF(S)`'s `check_drat`-accepted refutation certifies
/// that subset is contradictory. Soundness rides entirely on `check_drat`
/// accepting: a wrong subset, a non-refuting proof, or a width over
/// [`axeyum_cnf::MAX_XOR_WIDTH`] all make this return `false` (declining is sound
/// — the caller then keeps the prior trusted XOR-UNSAT behavior, never a false
/// certificate).
///
/// Returns `false` when the conflict is *not* pure-Gauss (interleaved CDCL(XOR)
/// branching was needed — the combined-proof case, still uncertified) — that is
/// exactly when [`axeyum_cnf::Gf2System::unsat_reason_subset`] is `None`.
fn certify_pure_gauss_xor_unsat(formula: &CnfFormula) -> bool {
    pure_gauss_xor_unsat_certificate(formula).is_some()
}

/// Builds the `check_drat`-validated DRAT certificate of the pure-Gaussian-level-0
/// XOR sub-case for `formula`, or `None` when the sub-case does not apply.
///
/// The returned [`UnsatProof`] carries the DIMACS of `CNF(S)` (the conflict
/// subset `S` of original XOR constraints summing to `0 = 1`) and its DRAT
/// refutation, both as text, re-checkable from the text alone via
/// [`UnsatProof::recheck`] / [`crate::Evidence::check`]. See
/// [`certify_pure_gauss_xor_unsat`] for the soundness argument; the certificate
/// is returned only after [`check_drat`] accepts it here, so a `Some` is always a
/// genuine, independently-validated refutation of `CNF(S)`.
pub(crate) fn pure_gauss_xor_unsat_certificate(formula: &CnfFormula) -> Option<UnsatProof> {
    let system = extract_xors(formula).system;
    let subset = system.unsat_reason_subset()?;
    let constraints = system.constraints();
    let refutation = xor_gauss_drat_refutation(&constraints, &subset, system.num_vars())?;
    // The certificate is accepted only if the independent checker derives the
    // empty clause from CNF(S) (`Ok(true)`). Any other outcome (`Ok(false)` — a
    // proof that does not refute — or an `Err`) declines: no false certificate.
    if !matches!(
        check_drat(refutation.formula(), refutation.proof()),
        Ok(true)
    ) {
        return None;
    }
    Some(UnsatProof {
        dimacs: refutation.formula().to_dimacs(),
        drat: write_drat(refutation.proof()),
        lrat: None,
    })
}

/// Builds the pure-Gaussian-level-0 XOR certificate for a `QF_BV` query by
/// bit-blasting `assertions` to CNF and certifying the recovered XOR system, or
/// `None` when the sub-case does not apply (or the query is outside the
/// bit-blastable subset).
///
/// This independently re-derives the certificate from the query terms — it does
/// not reuse any backend state — so the evidence layer can attach a freshly
/// re-validated certificate. The CNF is the un-inprocessed Tseitin encoding; the
/// pure-Gauss inconsistency of the recovered XOR system is a property of that
/// formula, and the certificate is `check_drat`-validated before being returned.
#[cfg(feature = "full")]
pub(crate) fn pure_gauss_xor_unsat_certificate_for_query(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<UnsatProof> {
    if first_unsupported_op(arena, assertions).is_some()
        || first_unsupported_sort(arena, assertions).is_some()
    {
        return None;
    }
    let lowering = lower_terms(arena, assertions).ok()?;
    let roots = lowering
        .roots()
        .iter()
        .map(|root| root.bits()[0])
        .collect::<Vec<_>>();
    let encoding = tseitin_encode(lowering.aig(), &roots).ok()?;
    pure_gauss_xor_unsat_certificate(encoding.formula())
}

fn complete_model(arena: &TermArena, assignment: &Assignment) -> Model {
    let mut model = Model::new();
    let mut used_uninterpreted_tokens = used_uninterpreted_tokens(arena, assignment);
    for (symbol, _name, sort) in arena.symbols() {
        // A symbol unconstrained by the query gets its sort's well-founded
        // default (false/0/empty-array/base-constructor). Datatype symbols left
        // over from an eliminated datatype query are handled here too; an
        // uninhabited datatype simply gets no model entry.
        let value = assignment
            .get(symbol)
            .or_else(|| completion_default_value(arena, sort, &mut used_uninterpreted_tokens));
        if let Some(value) = value {
            model.set(symbol, value);
        }
    }
    model
}

fn used_uninterpreted_tokens(
    arena: &TermArena,
    assignment: &Assignment,
) -> BTreeMap<SortId, BTreeSet<u128>> {
    let mut used: BTreeMap<SortId, BTreeSet<u128>> = BTreeMap::new();
    for (symbol, _name, sort) in arena.symbols() {
        let Sort::Uninterpreted(sort_id) = sort else {
            continue;
        };
        if let Some(Value::Uninterpreted { value, .. }) = assignment.get(symbol) {
            used.entry(sort_id).or_default().insert(value);
        }
    }
    used
}

fn completion_default_value(
    arena: &TermArena,
    sort: Sort,
    used_uninterpreted_tokens: &mut BTreeMap<SortId, BTreeSet<u128>>,
) -> Option<Value> {
    if let Sort::Uninterpreted(sort_id) = sort {
        let used = used_uninterpreted_tokens.entry(sort_id).or_default();
        let mut token = 0u128;
        while used.contains(&token) {
            token = token.checked_add(1)?;
        }
        used.insert(token);
        return Some(Value::Uninterpreted {
            sort: sort_id,
            value: token,
        });
    }
    well_founded_default(arena, sort)
}

fn handle_sat_result(
    arena: &TermArena,
    assertions: &[TermId],
    replay_plan: Option<&QueryPlan>,
    lowering: &BitLowering,
    encoding: &CnfEncoding,
    sat_result: SatResult,
    stats: &mut SolveStats,
) -> Result<CheckResult, SolverError> {
    match sat_result {
        SatResult::Sat(cnf_assignment) => {
            // Two separately-timed sub-stages, split from one `lift_start`
            // measurement that used to cover both (found while wiring
            // `BvLayerStats` to a CLI flag, docs/research/12-performance/
            // instrument-coverage-2026-09-07.md: `stats.model_lift` was
            // stamped AFTER `replay_model` returned, so the field named "lift"
            // silently included the replay-check cost too). `lift_elapsed`
            // covers only assignment extraction/completion (AIG values ->
            // lowering assignment -> `complete_model`); `replay_elapsed`
            // covers only the soundness-gate replay below. Neither is
            // recorded on the unverifiable-replay early return (unchanged
            // from the pre-split behaviour: `stats.model_lift` stayed
            // `Duration::ZERO` on that path too), so this is a pure
            // additional-measurement change with no effect on control flow
            // or the returned `CheckResult`.
            let lift_start = Instant::now();
            let aig_values = encoding
                .aig_node_values_from_assignment(lowering.aig(), &cnf_assignment)
                .map_err(|error| map_cnf_error(&error))?;
            let assignment = lowering
                .assignment_from_aig_values(&aig_values)
                .map_err(map_lower_error)?;
            let model = complete_model(arena, &assignment);
            let lift_elapsed = lift_start.elapsed();
            // Replay is the soundness gate: a sat model is accepted only if it
            // satisfies the original query. If replay can't *evaluate* (e.g. an
            // arithmetic overflow in the trust-anchor evaluator), we cannot
            // confirm the model — the sound answer is a graceful `Unknown`, never
            // an accepted (unverified) sat and never a crash.
            let replay_start = Instant::now();
            let replay_outcome = replay_model(arena, assertions, replay_plan, &model)?;
            let replay_elapsed = replay_start.elapsed();
            if let Some(reason) = replay_outcome {
                return Ok(CheckResult::Unknown(reason));
            }
            stats.model_lift = lift_elapsed;
            push_duration_ms(stats, "model_replay_ms", replay_elapsed);
            Ok(CheckResult::Sat(model))
        }
        SatResult::Unsat(_) => Ok(CheckResult::Unsat),
        SatResult::Unknown(reason) => {
            let kind = if reason.detail.contains("timeout") {
                UnknownKind::Timeout
            } else if reason.detail.contains("resource") || reason.detail.contains("budget") {
                UnknownKind::ResourceLimit
            } else {
                UnknownKind::Other
            };
            Ok(CheckResult::Unknown(UnknownReason {
                kind,
                detail: reason.detail,
            }))
        }
    }
}

/// Replays the candidate `model` against the original query.
///
/// Returns:
/// - `Ok(None)` when the model is verified (every original term is `true`).
/// - `Ok(Some(reason))` when the model cannot be *evaluated* (the trust-anchor
///   evaluator returned an [`IrError`], e.g. an arithmetic overflow): the model
///   is conservatively *not* accepted and the caller degrades to a graceful
///   `Unknown` — never a crash, never an unverified sat.
/// - `Err(..)` only for a genuine soundness violation: an original Boolean term
///   evaluated to `false` (the model is wrong) or to a non-Boolean value (an
///   internal invariant breach). These must surface, not be swallowed.
fn replay_model(
    arena: &TermArena,
    assertions: &[TermId],
    replay_plan: Option<&QueryPlan>,
    model: &Model,
) -> Result<Option<UnknownReason>, SolverError> {
    let assignment = model.to_assignment();
    if let Some(plan) = replay_plan {
        return match plan.replay_original(arena, &assignment) {
            Ok(()) => Ok(None),
            // Could not evaluate the original term (e.g. overflow): graceful Unknown.
            Err(QueryReplayFailure::Evaluation { term, error, .. }) => {
                Ok(Some(eval_unverifiable_unknown(term, &error)))
            }
            // A genuine wrong/ill-typed model: must surface as an error.
            Err(failure) => Err(SolverError::Backend(format!(
                "sat model replay failed: {failure}"
            ))),
        };
    }
    for &term in assertions {
        match eval(arena, term, &assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Err(SolverError::Backend(format!(
                    "sat model replay failed: assertion #{} evaluated to false",
                    term.index()
                )));
            }
            Ok(value) => {
                return Err(SolverError::Backend(format!(
                    "sat model replay failed: assertion #{} evaluated to non-Boolean {value}",
                    term.index()
                )));
            }
            // Could not evaluate (e.g. arithmetic overflow in the evaluator): the
            // model is unverifiable, so degrade to a graceful `Unknown` rather
            // than accepting it or crashing.
            Err(error) => {
                return Ok(Some(eval_unverifiable_unknown(term, &error)));
            }
        }
    }
    Ok(None)
}

/// The `Unknown` reason for a sat model whose replay could not be evaluated.
fn eval_unverifiable_unknown(term: TermId, error: &IrError) -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::Other,
        detail: format!(
            "sat model could not be verified: assertion #{} failed evaluation: {error} \
             (model conservatively not accepted)",
            term.index()
        ),
    }
}

/// Pre-lowering oversized-encoding refusal: a small DAG can bit-blast to a
/// gigantic AIG/CNF (a single wide multiply is ~width² gates), and the
/// `check_cnf_budgets` gate only fires *after* `lower_terms` has already
/// allocated it. Estimate the blasted clause count up front and return a graceful
/// `Unknown` BEFORE lowering, so an oversized query degrades cleanly instead of
/// aborting the process out of memory. The estimate is a conservative
/// over-approximation; an absolute ceiling guards the no-explicit-budget case so
/// a runaway can never OOM the host. Returns `None` when the query is within
/// budget and lowering should proceed.
fn oversized_encoding_refusal(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Option<CheckResult> {
    let estimated_clauses = estimate_blast_clauses(arena, assertions);

    // `memory_limit_mb`, mechanism 1: megabytes converted into this gate's own
    // currency. Kept as a SEPARATE refusal rather than folded into `clause_cap`
    // so the reason a consumer reads names the budget that actually bound —
    // `MemoryLimit` and `EncodingBudget` are different findings and lead to
    // different fixes (give it more memory / re-scope the query).
    if let Some(budget) = MemoryBudget::from_config(config)
        && estimated_clauses > budget.clause_ceiling()
    {
        return Some(CheckResult::Unknown(
            budget.encoding_refusal(estimated_clauses, "projected"),
        ));
    }

    let clause_cap = config.cnf_clause_budget.unwrap_or(ABSOLUTE_CLAUSE_CEILING);
    if estimated_clauses > clause_cap {
        return Some(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::EncodingBudget,
            detail: format!(
                "estimated {estimated_clauses} CNF clauses before lowering exceeds budget \
                 {clause_cap} (oversized encoding refused gracefully)"
            ),
        }));
    }
    None
}

/// Default projected clause ceiling when the caller did not set an explicit
/// encoding budget.
pub(crate) const ABSOLUTE_CLAUSE_CEILING: u64 = 64_000_000;

/// A cheap, pre-lowering **over-estimate** of the bit-blasted CNF clause count,
/// used to refuse oversized encodings before `lower_terms` allocates them
/// (graceful `unknown` instead of an out-of-memory abort). Walks the shared term
/// DAG once; each node contributes a per-operator cost in its result width —
/// multiplies are ~`8w²`, divides/remainders ~`10w²`, shifts ~`w·log w`, and
/// everything else linear in `w` — then `~3×` the gate total approximates the
/// Tseitin clause count.
pub(crate) fn estimate_blast_clauses(arena: &TermArena, assertions: &[TermId]) -> u64 {
    use std::collections::HashSet;

    use axeyum_ir::{Op, TermNode};

    let width = |t: TermId| -> u64 {
        match arena.sort_of(t) {
            Sort::Bool => 1,
            Sort::BitVec(w) => u64::from(w),
            _ => 0,
        }
    };
    let mut visited: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut gates: u64 = 0;
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            let w = width(t);
            let cost = match op {
                // A shift-and-add multiplier is `w²` partial-product AND gates PLUS a
                // carry-save adder tree (~`w` ripple-carry adds of `w`-bit numbers,
                // ~7 AIG nodes per full adder) ≈ 8·w² gates total. Charging only `w²`
                // under-estimated by ~8×, so e.g. a 4096-bit `bvmul` slipped *just*
                // under the clause ceiling and then OOM-trapped during lowering
                // instead of degrading to `unknown`. Use the conservative ~8·w² so
                // genuinely-too-large multipliers are refused before allocation.
                Op::BvMul => w.saturating_mul(w).saturating_mul(8),
                // Restoring division/remainder is a per-bit subtract+compare circuit,
                // heavier than multiplication; conservatively ~10·w².
                Op::BvUdiv | Op::BvUrem | Op::BvSdiv | Op::BvSrem | Op::BvSmod => {
                    w.saturating_mul(w).saturating_mul(10)
                }
                Op::BvShl | Op::BvLshr | Op::BvAshr => {
                    let log_w = 64u64 - u64::from(w.leading_zeros());
                    w.saturating_mul(log_w.max(1))
                }
                _ => w.max(1),
            };
            gates = gates.saturating_add(cost);
            for &a in &**args {
                stack.push(a);
            }
        } else {
            gates = gates.saturating_add(width(t).max(1));
        }
    }
    gates.saturating_mul(3)
}

fn check_cnf_budgets(
    config: &SolverConfig,
    formula: &axeyum_cnf::CnfFormula,
    stats: &mut SolveStats,
) -> Option<CheckResult> {
    let variables = usize_to_u64(formula.variable_count());
    if let Some(budget) = config.cnf_variable_budget
        && variables > budget
    {
        stats.solve = Duration::ZERO;
        return Some(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::EncodingBudget,
            detail: format!("CNF has {variables} variables, budget {budget}"),
        }));
    }

    let clauses = usize_to_u64(formula.clauses().len());
    if let Some(budget) = config.cnf_clause_budget
        && clauses > budget
    {
        stats.solve = Duration::ZERO;
        return Some(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::EncodingBudget,
            detail: format!("CNF has {clauses} clauses, budget {budget}"),
        }));
    }

    // `memory_limit_mb` against the REAL clause count. The pre-lowering gate ran
    // on `estimate_blast_clauses`, which over-approximates by ~8x on multipliers;
    // an encoding can clear that estimate and still be the one that does not fit,
    // or (more often) be refused there and fit here. This is the exact one.
    if let Some(budget) = MemoryBudget::from_config(config)
        && clauses > budget.clause_ceiling()
    {
        stats.solve = Duration::ZERO;
        return Some(CheckResult::Unknown(
            budget.encoding_refusal(clauses, "encoded"),
        ));
    }

    // Phase boundary 3 of 3: everything the encoding allocates is now live, and
    // the SAT search is about to start on top of it.
    if let Some(budget) = MemoryBudget::from_config(config)
        && let Some(reason) = budget.exceeded("before SAT search")
    {
        stats.solve = Duration::ZERO;
        return Some(CheckResult::Unknown(reason));
    }

    None
}

fn map_lower_error(error: BitLowerError) -> SolverError {
    match error {
        BitLowerError::UnsupportedOp { term, op } => SolverError::Unsupported(format!(
            "term #{} uses unsupported pure-Rust BV operator {op:?}",
            term.index()
        )),
        BitLowerError::Ir(IrError::InvalidWidth(width)) => SolverError::Unsupported(format!(
            "unsupported bit-vector width {width} in pure-Rust BV backend"
        )),
        other => SolverError::Backend(other.to_string()),
    }
}

fn map_cnf_error(error: &CnfError) -> SolverError {
    SolverError::Backend(error.to_string())
}

/// Dispatches the primary SAT search: the deadline-bounded native CDCL core,
/// unconditionally (ADR-1703).
///
/// `config.native_cdcl` is a retired no-op — the native core is the engine
/// whether it is set or not — and the `rustsat-batsat` adapter it used to select
/// against is gone from the default build entirely.
///
/// When `config.prove_unsat` is set, `check_proof` is passed so any `unsat` is
/// verified inline (`SatProofStatus::Checked`) and the downstream re-derivation
/// is skipped (see the call site in [`SatBvBackend::check_with_replay`]).
/// Without it the core still *derives* a proof — it simply is not spent on
/// checking, which is why the result is stamped `Unchecked` rather than being
/// proofless.
fn primary_sat_search(
    config: &SolverConfig,
    formula: &CnfFormula,
    deadline: Option<Instant>,
    stats: &mut SolveStats,
    reduction: Option<(&CnfFormula, &ReductionLink)>,
) -> SatResult {
    let outcome = solve_with_native_cdcl(
        formula,
        deadline,
        config.resource_limit,
        config.prove_unsat,
        reduction,
    );
    if let Some(duration) = outcome.proof_replay {
        push_duration_ms(stats, "unsat_proof_replay_ms", duration);
    }
    if let Some(coverage) = &outcome.coverage {
        record_proof_coverage(stats, coverage, outcome.prefix_steps, outcome.search_steps);
    }
    outcome.result
}

/// Records WHICH formula an `unsat` proof was checked against, and why when it
/// was not the caller's.
///
/// Exactly one of `unsat_proof_checked_against_original` /
/// `unsat_proof_checked_against_reduced` is emitted per checked `unsat`, so a
/// consumer that reads only one of the two keys still cannot mistake a missing
/// key for a passing one — the pair is a partition, not a flag and its absence.
/// The `reason` key names the cause as a small integer so a sweep can group by
/// it without parsing prose.
fn record_proof_coverage(
    stats: &mut SolveStats,
    coverage: &ProofCoverage,
    prefix_steps: usize,
    search_steps: usize,
) {
    push_count(stats, "unsat_proof_prefix_steps", prefix_steps as u64);
    push_count(stats, "unsat_proof_search_steps", search_steps as u64);
    match coverage {
        ProofCoverage::Original => {
            stats
                .backend
                .push(("unsat_proof_checked_against_original".to_owned(), 1.0));
        }
        ProofCoverage::Reduced(reason) => {
            stats
                .backend
                .push(("unsat_proof_checked_against_reduced".to_owned(), 1.0));
            let (code, detail) = match reason {
                ReducedReason::Unjustified(_) => (1.0, None),
                ReducedReason::OverBudget { steps, .. } => (2.0, Some(*steps)),
                ReducedReason::RenamingOutOfRange(_) => (3.0, None),
            };
            stats
                .backend
                .push(("unsat_proof_reduced_reason".to_owned(), code));
            if let Some(steps) = detail {
                push_count(stats, "unsat_proof_steps_over_budget", steps as u64);
            }
        }
    }
}

/// Runs the in-tree proof-producing CDCL core as the primary SAT search,
/// mapping its [`ProofSolveOutcome`] onto the [`SatResult`] the rest of the
/// pipeline consumes.
///
/// - `Sat` → [`SatResult::Sat`]; the model then flows through the standard
///   reconstruction + AIG/model/term replay (a wrong model is rejected there).
/// - `Unsat` → [`SatResult::Unsat`]. The native core already produced a DRAT
///   proof inline; when `check_proof` is set we verify it **here, in place**
///   (one solve) and stamp the result `Checked` so a downstream re-derivation is
///   unnecessary. A proof that fails to check — or fails to derive the empty
///   clause — is a should-never-happen native-core bug: we conservatively
///   **downgrade to `Unknown`** rather than accept an unverified `unsat`. When
///   `check_proof` is unset we stamp `Unchecked` (no verification cost), matching
///   the prior behaviour.
/// - `ResourceOut`/`Interrupted` → [`SatResult::Unknown`]; an undecided verdict
///   is never reported as `sat`/`unsat`.
struct NativeCdclOutcome {
    result: SatResult,
    /// Time spent independently checking the emitted DRAT proof. This is nested
    /// within SAT search time, not an additional sequential pipeline stage.
    proof_replay: Option<Duration>,
    /// Which formula the proof was checked against, when one was checked.
    ///
    /// Produced by the same call that chose the formula
    /// ([`ReductionLink::check_unsat`]), never asserted alongside it — a
    /// coverage flag a caller sets by hand is the shape that lets a checker
    /// report "original" for a check it did not make.
    coverage: Option<ProofCoverage>,
    /// Steps of the reduction prefix that were part of the checked proof.
    prefix_steps: usize,
    /// Steps the search itself emitted.
    search_steps: usize,
}

fn solve_with_native_cdcl(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    resource_limit: Option<u64>,
    check_proof: bool,
    reduction: Option<(&CnfFormula, &ReductionLink)>,
) -> NativeCdclOutcome {
    let max_conflicts = resource_limit.map_or(DEFAULT_PROOF_SAT_CONFLICT_LIMIT, |limit| {
        usize::try_from(limit).unwrap_or(usize::MAX)
    });
    match solve_with_drat_proof_with_limits(formula, deadline, max_conflicts) {
        ProofSolveOutcome::Sat(assignment) => NativeCdclOutcome {
            result: SatResult::Sat(assignment),
            proof_replay: None,
            coverage: None,
            prefix_steps: 0,
            search_steps: 0,
        },
        ProofSolveOutcome::Unsat(proof) => {
            if !check_proof {
                return NativeCdclOutcome {
                    result: SatResult::Unsat(SatUnsatEvidence {
                        proof: SatProofStatus::Unchecked,
                        failed_assumptions: Vec::new(),
                    }),
                    proof_replay: None,
                    coverage: None,
                    prefix_steps: 0,
                    search_steps: proof.len(),
                };
            }
            // Verify the inline proof in place. Only a checked proof yields an
            // accepted `unsat`; anything else is a conservative downgrade — we
            // never pass off an unverified `unsat` as checked.
            //
            // WHICH formula it is checked against is the whole question here.
            // Without a reduction the two are the same formula and the
            // identity link says so. With one, the link concatenates the
            // passes' derivation with the search's steps lifted out of the
            // compacted variable space, and the check runs against the
            // ENCODED formula — so the reduction is inside the certificate
            // instead of underneath it.
            let identity = ReductionLink::identity();
            let (original, link) = reduction.map_or((formula, &identity), |(f, l)| (f, l));
            let check = link.check_unsat(original, formula, &proof, MAX_LINKED_PROOF_STEPS);
            let result = if check.verified {
                SatResult::Unsat(SatUnsatEvidence {
                    proof: SatProofStatus::Checked,
                    failed_assumptions: Vec::new(),
                })
            } else {
                let against = if check.coverage.is_original() {
                    "the original formula"
                } else {
                    "the reduced formula"
                };
                let detail = match &check.error {
                    Some(error) => {
                        format!("native unsat proof failed to check against {against}: {error}")
                    }
                    None => format!(
                        "native unsat proof failed to check against {against}: did not derive \
                         the empty clause"
                    ),
                };
                SatResult::Unknown(SatUnknownReason { detail })
            };
            NativeCdclOutcome {
                result,
                proof_replay: Some(check.check_duration),
                coverage: Some(check.coverage),
                prefix_steps: check.prefix_steps,
                search_steps: check.search_steps,
            }
        }
        ProofSolveOutcome::ResourceOut => NativeCdclOutcome {
            result: SatResult::Unknown(SatUnknownReason {
                detail: "native CDCL core exhausted its conflict budget".to_owned(),
            }),
            proof_replay: None,
            coverage: None,
            prefix_steps: 0,
            search_steps: 0,
        },
        ProofSolveOutcome::Interrupted => NativeCdclOutcome {
            result: SatResult::Unknown(SatUnknownReason {
                detail: "native CDCL core timeout".to_owned(),
            }),
            proof_replay: None,
            coverage: None,
            prefix_steps: 0,
            search_steps: 0,
        },
    }
}

/// Ensures the `unsat` in `sat_result` is backed by a checked DRAT proof,
/// returning `Ok(None)` when it is (so the caller may accept the `unsat`) and
/// `Ok(Some(reason))` when it must fail closed to `unknown`. A no-op (`Ok(None)`)
/// unless `prove` is set and `sat_result` is `Unsat`.
///
/// Two routes reach here, both yielding the same guarantee:
/// - The native proof-producing core (used for `prove_unsat`) already produced
///   and verified its DRAT proof inline; its `Checked` status means the `unsat`
///   is backed by a checked proof BY CONSTRUCTION, so no re-derivation runs.
///   This is the single-solve path.
/// - The batsat fallback (or any config still routing to batsat) lands here
///   `Unchecked`; re-derive and verify with the proof core, failing closed if no
///   checkable proof can be produced within budget.
fn ensure_unsat_proof_checked(
    prove: bool,
    sat_result: &SatResult,
    formula: &CnfFormula,
    stats: &mut SolveStats,
    reduced: bool,
) -> Result<Option<UnknownReason>, SolverError> {
    if !prove || !matches!(sat_result, SatResult::Unsat(_)) {
        return Ok(None);
    }
    let already_checked = matches!(
        sat_result,
        SatResult::Unsat(evidence) if evidence.proof == SatProofStatus::Checked
    );
    if already_checked {
        stats
            .backend
            .push(("unsat_proof_checked_inline".to_owned(), 1.0));
        return Ok(None);
    }
    // The re-derivation route. It re-solves `formula`, which is whatever the
    // search ran over, so when a reduction happened this certifies the REDUCED
    // formula and the link to the original is trusted — the exact state the
    // primary path no longer has. Say so rather than leave the coverage keys
    // unset: a missing key reads as "not applicable" and this is a real
    // narrowing.
    //
    // The reduced formula is equisatisfiable with the original, so the verdict
    // is still sound. Fail CLOSED when no checkable proof can be produced.
    if reduced {
        record_proof_coverage(
            stats,
            &ProofCoverage::Reduced(ReducedReason::Unjustified(
                "re-derivation route re-solves the reduced formula".to_owned(),
            )),
            0,
            0,
        );
    }
    verify_unsat_proof(formula, stats)
}

/// Independently re-derives `unsat` with the proof-producing SAT core and
/// verifies its DRAT proof (ADR-0011/0012).
///
/// Returns `Ok(None)` when the `unsat` was independently re-derived and its DRAT
/// proof checked (certified). Returns `Ok(Some(reason))` when the proof core
/// exhausted its conflict budget (or was interrupted) before deriving the empty
/// clause: no checkable proof exists, so the caller must **fail closed** —
/// downgrade to `unknown` rather than pass off an unverified `unsat` as a checked
/// one. A disagreement (the proof core finds a model) or a failed proof is a
/// soundness alarm (`Err`).
fn verify_unsat_proof(
    formula: &CnfFormula,
    stats: &mut SolveStats,
) -> Result<Option<UnknownReason>, SolverError> {
    match solve_with_drat_proof(formula) {
        ProofSolveOutcome::Unsat(proof) => match check_drat(formula, &proof) {
            Ok(true) => {
                stats.backend.push(("unsat_proof_checked".to_owned(), 1.0));
                Ok(None)
            }
            Ok(false) => Err(SolverError::Backend(
                "unsat proof did not derive the empty clause".to_owned(),
            )),
            Err(error) => Err(SolverError::Backend(format!(
                "unsat proof failed to check: {error}"
            ))),
        },
        ProofSolveOutcome::Sat(_) => Err(SolverError::Backend(
            "soundness alarm: adapter reported unsat but the proof core found a model".to_owned(),
        )),
        // Budget exhausted before the empty clause: the adapter's `unsat` stands
        // as a best-effort verdict but is NOT proof-checked. Fail closed.
        ProofSolveOutcome::ResourceOut | ProofSolveOutcome::Interrupted => {
            stats
                .backend
                .push(("unsat_proof_unavailable".to_owned(), 1.0));
            Ok(Some(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "unsat found but the proof core exhausted its budget before producing a \
                         checkable proof; prove_unsat requested a checked unsat"
                    .to_owned(),
            }))
        }
    }
}

fn push_duration_ms(stats: &mut SolveStats, name: &str, duration: Duration) {
    stats
        .backend
        .push((name.to_owned(), duration.as_secs_f64() * 1000.0));
}

/// Total literal occurrences in `formula` — the size the SAT core's propagation
/// actually walks, which clause and variable counts do not capture. BVE removes
/// clauses while *adding* literal occurrences (resolvents are longer than the
/// clauses they replace), so a reduction reported only in clauses can hide a
/// growth in the quantity that costs propagation time.
fn literal_occurrences(formula: &CnfFormula) -> usize {
    formula.clauses().iter().map(|c| c.lits().len()).sum()
}

#[allow(clippy::cast_precision_loss)]
fn push_count(stats: &mut SolveStats, name: &str, value: u64) {
    stats.backend.push((name.to_owned(), value as f64));
}

#[allow(clippy::cast_precision_loss)]
fn usize_to_f64(value: usize) -> f64 {
    value as f64
}

fn usize_to_u64(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_cnf::{CnfClause, CnfLit, CnfVar, SatUnknownReason};

    // --- `memory_limit_mb`, one test per guard -----------------------------
    //
    // These are here rather than in `crate::memory_budget` because two of the
    // five guards are only reachable through this module's private gates
    // (`estimate_blast_clauses`, `check_cnf_budgets`), and because the FIRST
    // mutation run of this feature reported all five SURVIVED: each guard was
    // shadowed by another that rejected the same query. Each test below is
    // constructed so that exactly one guard can be the one that fires, and the
    // construction is asserted rather than assumed.
    //
    // The names start `memory_budget_` so `--lib memory_budget` collects them
    // alongside the module's own tests.

    use crate::memory_budget::{PROBE_LOCK, script_resident_bytes};

    /// A small query, decided in microseconds, that still reaches all three
    /// probe sites.
    fn tiny_bv_query() -> (TermArena, Vec<TermId>) {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 16).unwrap();
        let y = arena.bv_var("y", 16).unwrap();
        let product = arena.bv_mul(x, y).unwrap();
        let target = arena.bv_const(16, 0x5a5a).unwrap();
        let assertion = arena.eq(product, target).unwrap();
        (arena, vec![assertion])
    }

    /// Runs `tiny_bv_query` under a 1 GiB budget with `readings` scripted into
    /// the resident-set probe, and returns the verdict.
    ///
    /// 1 GiB buys ~2.8 M clauses, and the query encodes a few thousand, so
    /// neither clause ceiling can fire: whatever declines here is a probe.
    fn probe_run(readings: &[u64]) -> CheckResult {
        let (arena, assertions) = tiny_bv_query();
        let config = SolverConfig::default().with_memory_limit_mb(1024);
        script_resident_bytes(readings);
        let result = SatBvBackend::new()
            .check(&arena, &assertions, &config)
            .expect("check");
        script_resident_bytes(&[]);
        result
    }

    fn expect_memory_decline(result: &CheckResult, phase: &str) {
        let CheckResult::Unknown(reason) = result else {
            panic!("expected a memory decline at {phase}, got {result:?}");
        };
        assert_eq!(reason.kind, UnknownKind::MemoryLimit);
        assert!(
            reason.detail.contains(phase),
            "the decline must name the boundary that fired (wanted {phase}): {}",
            reason.detail
        );
    }

    const OVER_1GIB: u64 = 2 * 1024 * 1024 * 1024;

    #[test]
    fn memory_budget_entry_probe_declines() {
        let _guard = PROBE_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        expect_memory_decline(&probe_run(&[OVER_1GIB]), "backend entry");
    }

    /// Under budget on arrival, over it after lowering. The scripted second
    /// reading is the only way to reach this boundary deterministically: with
    /// real readings the entry probe would have to be under and the lowering
    /// growth over, in a process whose resident set is mostly other tests.
    #[test]
    fn memory_budget_probe_after_lowering_declines() {
        let _guard = PROBE_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        expect_memory_decline(&probe_run(&[0, OVER_1GIB]), "after bit-vector lowering");
    }

    #[test]
    fn memory_budget_probe_before_sat_search_declines() {
        let _guard = PROBE_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        expect_memory_decline(&probe_run(&[0, 0, OVER_1GIB]), "before SAT search");
    }

    /// The PROJECTED ceiling, isolated from the encoded one.
    ///
    /// `estimate_blast_clauses` over-approximates a multiplier by ~3x, so a
    /// budget set halfway between the real clause count and the estimate is
    /// refused before lowering and would NOT be refused after it. The test
    /// asserts that gap rather than trusting it: if the estimate ever tightens
    /// to the real count, this stops isolating anything and says so.
    #[test]
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // a clause count
    fn memory_budget_projected_ceiling_refuses_before_lowering() {
        let _guard = PROBE_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 64).unwrap();
        let y = arena.bv_var("y", 64).unwrap();
        let left = arena.bv_mul(x, y).unwrap();
        let right = arena.bv_mul(y, x).unwrap();
        let equal = arena.eq(left, right).unwrap();
        let assertion = arena.not(equal).unwrap();
        let assertions = vec![assertion];

        // What the query really encodes to. `resource_limit` 0 stops the search
        // the moment it starts, so this is the encoding and nothing else.
        let mut backend = SatBvBackend::new();
        let _ = backend
            .check(
                &arena,
                &assertions,
                &SolverConfig::default().with_resource_limit(0),
            )
            .expect("check");
        let encoded = backend
            .last_stats()
            .expect("stats")
            .backend
            .iter()
            .find(|(name, _)| name == "cnf_clauses")
            .map_or(0.0, |(_, value)| *value) as u64;
        let projected = estimate_blast_clauses(&arena, &assertions);
        assert!(
            projected > encoded * 2,
            "this test needs the estimate to over-approximate (projected \
             {projected}, encoded {encoded}); with the two close together it \
             cannot separate the two ceilings and is not testing what it says"
        );

        // A ceiling strictly between the two: the projected gate must refuse,
        // and the encoded gate must not have been able to.
        let ceiling = u64::midpoint(projected, encoded);
        let limit_mb = ceiling * crate::memory_budget::ENCODING_BYTES_PER_CLAUSE / (1024 * 1024);
        assert!(encoded < ceiling && ceiling < projected);

        // Scripted zero: the probes must not be what declines this.
        script_resident_bytes(&[0, 0, 0]);
        let result = SatBvBackend::new()
            .check(
                &arena,
                &assertions,
                &SolverConfig::default()
                    .with_memory_limit_mb(limit_mb)
                    .with_resource_limit(0),
            )
            .expect("check");
        script_resident_bytes(&[]);

        let CheckResult::Unknown(reason) = result else {
            panic!("a budget below the projected encoding must decline: {result:?}");
        };
        assert_eq!(reason.kind, UnknownKind::MemoryLimit);
        assert!(
            reason.detail.contains("projected"),
            "the pre-lowering gate must say it projected: {}",
            reason.detail
        );
    }

    /// The ENCODED ceiling, isolated by calling its gate directly.
    ///
    /// It cannot be isolated through `check`, because `estimate_blast_clauses`
    /// over-approximates: any encoding over the ceiling was projected over it
    /// too, so the pre-lowering gate always fires first. That makes this a
    /// backstop for an estimate that is a heuristic, not a proof — and a
    /// backstop nothing can reach is still a backstop nothing tests, so the
    /// test reaches the gate rather than the route.
    #[test]
    fn memory_budget_encoded_ceiling_refuses_the_real_clause_count() {
        // Probes here too (the generous case reaches the third boundary), so
        // this must not run inside the probe-count test's window.
        let _guard = PROBE_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // One unit clause per variable: `add_clause` dedups, so repeating a
        // clause 1000 times builds 4 of them, not 1000 (it did, first run).
        let mut formula = axeyum_cnf::CnfFormula::new(1000);
        for i in 1..=1000usize {
            let var = CnfVar::new(i).expect("a variable index");
            let _ = formula.add_clause(CnfClause::new(vec![CnfLit::positive(var)]));
        }
        let clauses = formula.clauses().len() as u64;
        assert!(
            clauses > 100,
            "the fixture must be big enough to exceed a zero ceiling: {clauses}"
        );

        // A 0 MiB budget is a zero clause ceiling, so this is the encoded gate
        // and nothing else: no probe can fire (scripted 0) and there is no
        // pre-lowering estimate on this path at all.
        let config = SolverConfig::default().with_memory_limit_mb(0);
        let mut stats = SolveStats::default();
        script_resident_bytes(&[0, 0, 0]);
        let refusal = check_cnf_budgets(&config, &formula, &mut stats);
        script_resident_bytes(&[]);
        let Some(CheckResult::Unknown(reason)) = refusal else {
            panic!("a zero-clause ceiling must refuse 1000 clauses: {refusal:?}");
        };
        assert_eq!(reason.kind, UnknownKind::MemoryLimit);
        assert!(
            reason.detail.contains(&format!("encoded {clauses}")),
            "the post-encoding gate must quote the REAL clause count, not a \
             projection: {}",
            reason.detail
        );

        // ...and a budget that fits leaves the gate silent.
        let generous = SolverConfig::default().with_memory_limit_mb(1024);
        script_resident_bytes(&[0, 0, 0]);
        assert!(check_cnf_budgets(&generous, &formula, &mut stats).is_none());
        script_resident_bytes(&[]);
    }

    /// A synthetic `unknown` batsat verdict, the only state the fallback acts on.
    fn unknown() -> SatResult {
        SatResult::Unknown(SatUnknownReason {
            detail: "test: forced unknown".to_owned(),
        })
    }

    fn lit(var: usize, negated: bool) -> CnfLit {
        let base = CnfLit::positive(CnfVar::new(var).expect("var fits"));
        if negated { base.negated() } else { base }
    }

    fn formula(num_vars: usize, clauses: &[&[(usize, bool)]]) -> CnfFormula {
        let mut f = CnfFormula::new(num_vars);
        for clause in clauses {
            let lits = clause.iter().map(|&(v, n)| lit(v, n)).collect();
            f.add_clause(CnfClause::new(lits)).expect("valid clause");
        }
        f
    }

    /// Complete clause encoding of `(⊕ vars) = p`, exactly as `extract_xors`
    /// recognizes it (the forbidden assignments have parity `1 - p`).
    fn xor_clauses(vars: &[usize], p: bool) -> Vec<Vec<(usize, bool)>> {
        let k = vars.len();
        let forbidden_parity = !p;
        (0u32..(1u32 << k))
            .filter(|assign| ((assign.count_ones() & 1) == 1) == forbidden_parity)
            .map(|assign| {
                vars.iter()
                    .enumerate()
                    .map(|(j, &v)| (v, (assign >> j) & 1 == 1))
                    .collect()
            })
            .collect()
    }

    /// `x0 == x1 == … == x_{n-1}` with `x0 != x_{n-1}`: a purely XOR-structured
    /// UNSAT (`extract_xors` fires, batsat decides it too — so it is a clean
    /// fixture for the fallback's UNSAT path).
    fn parity_chain_unsat(n: usize) -> CnfFormula {
        let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();
        for i in 0..n - 1 {
            clauses.extend(xor_clauses(&[i, i + 1], false));
        }
        clauses.extend(xor_clauses(&[0, n - 1], true));
        let refs: Vec<&[(usize, bool)]> = clauses.iter().map(Vec::as_slice).collect();
        formula(n, &refs)
    }

    /// `push_count` stores work totals as `f64`, so a test comparing against
    /// one has to make the same conversion. Named rather than an inline `as`
    /// so the lossy cast is admitted once, next to the reason it is harmless:
    /// these values are well under 2^53.
    #[allow(clippy::cast_precision_loss)]
    fn u64_as_f64(value: u64) -> f64 {
        value as f64
    }

    fn stat(stats: &SolveStats, name: &str) -> Option<f64> {
        stats
            .backend
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| *v)
    }

    fn guarded_counterexample(arena: &mut TermArena, guard: TermId, consequent: TermId) -> TermId {
        let implication = arena.implies(guard, consequent).unwrap();
        arena.not(implication).unwrap()
    }

    fn or_all(arena: &mut TermArena, terms: &[TermId]) -> TermId {
        terms
            .iter()
            .copied()
            .reduce(|left, right| arena.or(left, right).unwrap())
            .unwrap()
    }

    #[test]
    fn shared_guard_split_requires_one_common_antecedent() {
        let mut arena = TermArena::new();
        let guard = arena.bool_var("guard").unwrap();
        let other_guard = arena.bool_var("other_guard").unwrap();
        let consequents = (0..4)
            .map(|index| arena.bool_var(&format!("c{index}")).unwrap())
            .collect::<Vec<_>>();
        let branches = consequents
            .iter()
            .map(|&consequent| guarded_counterexample(&mut arena, guard, consequent))
            .collect::<Vec<_>>();
        let root = or_all(&mut arena, &branches);

        assert_eq!(
            shared_guard_split_branches(&arena, &[root], MIN_SHARED_GUARD_SPLIT_DAG_NODES),
            Some(branches.clone())
        );
        assert!(
            shared_guard_split_branches(&arena, &[root], MIN_SHARED_GUARD_SPLIT_DAG_NODES - 1)
                .is_none()
        );

        let mismatched = guarded_counterexample(&mut arena, other_guard, consequents[0]);
        let mut mixed = branches;
        mixed[0] = mismatched;
        let mixed_root = or_all(&mut arena, &mixed);
        assert!(
            shared_guard_split_branches(&arena, &[mixed_root], MIN_SHARED_GUARD_SPLIT_DAG_NODES)
                .is_none()
        );
    }

    #[test]
    fn shared_guard_split_transfers_unsat_and_replays_sat() {
        let mut arena = TermArena::new();
        let guard = arena.bool_var("guard").unwrap();
        let extras = (0..4)
            .map(|index| arena.bool_var(&format!("extra{index}")).unwrap())
            .collect::<Vec<_>>();

        let unsat_branches = extras
            .iter()
            .map(|&extra| {
                let consequent = arena.or(guard, extra).unwrap();
                guarded_counterexample(&mut arena, guard, consequent)
            })
            .collect::<Vec<_>>();
        let unsat_root = or_all(&mut arena, &unsat_branches);
        let config = SolverConfig::new().with_timeout(Duration::from_secs(1));
        let mut backend = SatBvBackend::new();
        let unsat = backend
            .check_shared_guard_split(
                &arena,
                &[unsat_root],
                &unsat_branches,
                &config,
                Instant::now() + Duration::from_secs(1),
            )
            .unwrap();
        assert_eq!(unsat, CheckResult::Unsat);
        assert_eq!(
            stat(backend.last_stats().unwrap(), "shared_guard_split_unsat"),
            Some(1.0)
        );

        let false_term = arena.bool_const(false);
        let sat_branch = guarded_counterexample(&mut arena, guard, false_term);
        let mut sat_branches = unsat_branches;
        sat_branches.push(sat_branch);
        let sat_root = or_all(&mut arena, &sat_branches);
        let mut backend = SatBvBackend::new();
        let sat = backend
            .check_shared_guard_split(
                &arena,
                &[sat_root],
                &sat_branches,
                &config,
                Instant::now() + Duration::from_secs(1),
            )
            .unwrap();
        let CheckResult::Sat(model) = sat else {
            panic!("one satisfiable branch must produce a replayed SAT model");
        };
        assert_eq!(
            eval(&arena, sat_root, &model.to_assignment()).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            stat(backend.last_stats().unwrap(), "shared_guard_split_sat"),
            Some(1.0)
        );
    }

    /// An unsatisfiable `QF_BV` goal big enough that inprocessing has something
    /// to do: a 6-bit multiplier's Tseitin encoding is hundreds of clauses of
    /// gate definitions, which is exactly what BVE eats, and commutativity is
    /// refutable without the search having to redo the multiplier.
    fn unsat_bv_goal() -> (TermArena, Vec<TermId>) {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 6).unwrap();
        let y = arena.bv_var("y", 6).unwrap();
        let xy = arena.bv_mul(x, y).unwrap();
        let yx = arena.bv_mul(y, x).unwrap();
        let same = arena.eq(xy, yx).unwrap();
        let assertion = arena.not(same).unwrap();
        (arena, vec![assertion])
    }

    /// THE test this lane exists for. With inprocessing on and `prove_unsat`
    /// set, the `unsat` must be backed by a proof checked against the formula
    /// this backend ENCODED, not against the reduced formula the search
    /// happened to run over.
    ///
    /// Every assertion below is load-bearing, and three of them exist to stop
    /// the headline one from passing vacuously:
    ///
    /// * `inprocess_proof_steps > 0` — the passes actually derived clauses. A
    ///   reduction that changed nothing makes "checked against the original"
    ///   true and meaningless.
    /// * `cnf_compaction_variables_dropped > 0` — the compaction actually
    ///   renumbered, so the search's steps really were in a different variable
    ///   space and the lift really had to run. This is the half ADR-1750 left
    ///   open; without it the test would pass for a build with no renaming at
    ///   all.
    /// * `unsat_proof_search_steps > 0` — the search contributed a refutation
    ///   rather than the prefix having refuted the formula on its own, which
    ///   ADR-1750 measured as a real vacuity trap on small pigeonholes.
    #[test]
    fn inprocessed_unsat_is_checked_against_the_original_formula() {
        let (arena, assertions) = unsat_bv_goal();
        let config = SolverConfig::default()
            .with_prove_unsat(true)
            .with_cnf_inprocessing(true)
            .with_cnf_vivify(true)
            .with_timeout(Duration::from_secs(60));
        let mut backend = SatBvBackend::new();
        let result = backend.check(&arena, &assertions, &config).expect("check");
        assert_eq!(result, CheckResult::Unsat);

        let stats = backend.last_stats().expect("stats");
        assert_eq!(
            stat(stats, "cnf_inprocessing"),
            Some(1.0),
            "inprocessing must have run, or this test is about the wrong path"
        );
        assert_eq!(
            stat(stats, "unsat_proof_checked_against_original"),
            Some(1.0),
            "the unsat must be checked against the ORIGINAL formula; stats: {:?}",
            stats.backend
        );
        assert_eq!(
            stat(stats, "unsat_proof_checked_against_reduced"),
            None,
            "the two coverage keys are a partition — never both, never neither"
        );
        assert!(
            stat(stats, "inprocess_proof_steps").is_some_and(|v| v > 0.0),
            "the passes must have derived something: {:?}",
            stats.backend
        );
        assert!(
            stat(stats, "cnf_compaction_variables_dropped").is_some_and(|v| v > 0.0),
            "compaction must actually renumber, or the lift is untested: {:?}",
            stats.backend
        );
        assert!(
            stat(stats, "unsat_proof_search_steps").is_some_and(|v| v > 0.0),
            "the search must contribute steps, or the prefix refuted alone"
        );
        assert_eq!(
            stat(stats, "unsat_proof_prefix_steps"),
            stat(stats, "inprocess_proof_steps"),
            "every step the passes recorded must be part of the checked proof"
        );
    }

    /// Without inprocessing the searched formula IS the encoded one, so the
    /// same coverage key must read `original` — and it must do so through the
    /// identity link rather than through a special case, which is what makes
    /// the flag one mechanism instead of two.
    #[test]
    fn an_unreduced_unsat_is_also_covered_and_carries_no_prefix() {
        let (arena, assertions) = unsat_bv_goal();
        let config = SolverConfig::default()
            .with_prove_unsat(true)
            .with_timeout(Duration::from_secs(60));
        let mut backend = SatBvBackend::new();
        let result = backend.check(&arena, &assertions, &config).expect("check");
        assert_eq!(result, CheckResult::Unsat);
        let stats = backend.last_stats().expect("stats");
        assert_eq!(stat(stats, "cnf_inprocessing"), None);
        assert_eq!(
            stat(stats, "unsat_proof_checked_against_original"),
            Some(1.0)
        );
        assert_eq!(stat(stats, "unsat_proof_prefix_steps"), Some(0.0));
    }

    /// The XOR-propagation stage adds units derived by GAUSSIAN elimination,
    /// which are entailed but not `RUP`, so under `prove_unsat` they are not
    /// applied — otherwise they would be the one link no `DRAT` step can
    /// justify, and the coverage flag would have to read `reduced` for a reason
    /// nobody chose.
    ///
    /// This asserts the arrangement rather than the frequency: whether or not
    /// the skip fires on this instance, no pass may leave the link
    /// unjustifiable.
    #[test]
    fn xor_units_never_break_the_link_silently() {
        let (arena, assertions) = unsat_bv_goal();
        let config = SolverConfig::default()
            .with_prove_unsat(true)
            .with_cnf_inprocessing(true)
            .with_timeout(Duration::from_secs(60));
        let mut backend = SatBvBackend::new();
        let result = backend.check(&arena, &assertions, &config).expect("check");
        assert_eq!(result, CheckResult::Unsat);
        let stats = backend.last_stats().expect("stats");
        assert_eq!(
            stat(stats, "inprocess_link_checkable"),
            Some(1.0),
            "no pass may leave the link unjustifiable: {:?}",
            stats.backend
        );
        assert_eq!(
            stat(stats, "unsat_proof_checked_against_original"),
            Some(1.0)
        );
    }

    #[test]
    fn cold_cnf_construction_profile_is_opt_in_and_partitioned() {
        let mut arena = TermArena::new();
        let p = arena.bool_var("p").unwrap();

        let mut ordinary_backend = SatBvBackend::new();
        let ordinary = ordinary_backend
            .check(&arena, &[p, p], &SolverConfig::default())
            .unwrap();
        assert!(matches!(ordinary, CheckResult::Sat(_)));
        let ordinary_layers =
            crate::layers::BvLayerStats::from_solve_stats(ordinary_backend.last_stats().unwrap())
                .unwrap();
        assert!(!ordinary_layers.cnf_construction_profile_complete);
        assert_eq!(ordinary_layers.cnf_declared_clause_literals, 0);
        assert_eq!(ordinary_layers.cnf_primary_vacant_probes, 0);
        assert_eq!(
            stat(
                ordinary_backend.last_stats().unwrap(),
                "cnf_duplicate_origin_profile_complete"
            ),
            None
        );
        assert_eq!(
            stat(
                ordinary_backend.last_stats().unwrap(),
                "cnf_parity_overlap_profile_complete"
            ),
            None
        );

        let mut profiled_backend = SatBvBackend::new();
        let profiled = profiled_backend
            .check(
                &arena,
                &[p, p],
                &SolverConfig::default().with_cnf_construction_profile(true),
            )
            .unwrap();
        assert!(matches!(profiled, CheckResult::Sat(_)));
        let layers =
            crate::layers::BvLayerStats::from_solve_stats(profiled_backend.last_stats().unwrap())
                .unwrap();
        assert!(layers.cnf_construction_profile_complete);
        assert_eq!(layers.cnf_declared_clause_literals, 2);
        assert_eq!(layers.cnf_visited_clause_literals, 2);
        let profiled_stats = profiled_backend.last_stats().unwrap();
        assert_eq!(
            stat(profiled_stats, "cnf_duplicate_origin_profile_complete"),
            Some(1.0)
        );
        assert_eq!(
            stat(profiled_stats, "cnf_duplicate_origin_clauses"),
            Some(1.0)
        );
        assert_eq!(
            stat(profiled_stats, "cnf_parity_overlap_profile_complete"),
            Some(1.0)
        );
        assert_eq!(
            stat(profiled_stats, "cnf_parity_overlap_clauses"),
            Some(0.0)
        );
        assert_eq!(
            stat(
                profiled_stats,
                "cnf_duplicate_origin|root/root/assertion/unit|root/root/assertion/unit|same|clauses"
            ),
            Some(1.0)
        );
        assert_eq!(
            layers.cnf_clause_attempts - layers.cnf_tautological_clauses_skipped,
            layers.cnf_canonical_empty_clauses
                + layers.cnf_canonical_unit_clauses
                + layers.cnf_canonical_binary_clauses
                + layers.cnf_canonical_ternary_clauses
                + layers.cnf_canonical_larger_clauses
        );
        assert_eq!(
            layers.cnf_clauses,
            layers.cnf_primary_vacant_probes + layers.cnf_collision_inserts
        );
    }

    #[test]
    fn fallback_decides_xor_unsat_with_certificate() {
        // An XOR-structured UNSAT decidable by pure Gaussian elimination (the
        // parity chain telescopes to 0 = 1, no branching): the fallback upgrades
        // `unknown` to `unsat` AND certifies it via a check_drat-validated DRAT
        // certificate, so it is stamped `Checked` and `unsat_from_xor` is false
        // (it then rides the standard checked-by-construction path, not the trust
        // hole). The verdict is `unsat` either way — only the trust signal changed.
        let f = parity_chain_unsat(6);
        assert!(
            extract_xors(&f).num_recognized > 0,
            "fixture must carry XORs"
        );
        let mut stats = SolveStats::default();
        let out = maybe_xor_cdcl_fallback(&f, unknown(), &mut stats);
        let SatResult::Unsat(evidence) = &out.result else {
            panic!("expected unsat");
        };
        assert_eq!(
            evidence.proof,
            SatProofStatus::Checked,
            "pure-Gauss XOR unsat must carry a checked certificate"
        );
        assert!(
            !out.unsat_from_xor,
            "a certified pure-Gauss unsat is not the trusted hole"
        );
        assert_eq!(stat(&stats, "xor_cdcl_fallback_fired"), Some(1.0));
        assert_eq!(stat(&stats, "xor_cdcl_fallback_unsat"), Some(1.0));
        assert_eq!(
            stat(&stats, "xor_cdcl_fallback_unsat_drat_checked"),
            Some(1.0)
        );
        // The certificate the gate validated must independently re-check.
        let proof = pure_gauss_xor_unsat_certificate(&f).expect("certificate");
        assert!(proof.recheck().expect("recheck parses"));
    }

    /// A BV "parity chain" query: `v0 ^ v1 = 0`, …, `v_{n-2} ^ v_{n-1} = 0`, and
    /// `v0 ^ v_{n-1} = 1` over 1-bit vectors. Each `bvxor(a,b) == 0` bit-blasts to
    /// a width-2 XOR gate `extract_xors` recognizes, and the chain telescopes to
    /// the pure-Gaussian inconsistency `0 = 1` (no branching). UNSAT.
    #[cfg(feature = "full")]
    fn bv_parity_chain_query(n: usize) -> (TermArena, Vec<TermId>) {
        let mut arena = TermArena::new();
        let xs: Vec<TermId> = (0..n)
            .map(|i| arena.bv_var(&format!("v{i}"), 1).unwrap())
            .collect();
        let zero = arena.bv_const(1, 0).unwrap();
        let one = arena.bv_const(1, 1).unwrap();
        let mut eqs = Vec::new();
        for i in 0..n - 1 {
            let xr = arena.bv_xor(xs[i], xs[i + 1]).unwrap();
            eqs.push(arena.eq(xr, zero).unwrap());
        }
        let head = arena.bv_xor(xs[0], xs[n - 1]).unwrap();
        eqs.push(arena.eq(head, one).unwrap());
        (arena, eqs)
    }

    #[cfg(feature = "full")]
    #[test]
    fn query_certificate_for_bv_parity_chain_rechecks() {
        // A real BV query whose bit-blasted CNF carries a pure-Gauss-UNSAT XOR
        // system: the query-level builder returns a certificate that re-checks
        // independently (the end-to-end soundness link from query terms to a
        // check_drat-validated artifact).
        let (arena, eqs) = bv_parity_chain_query(5);
        let cert = pure_gauss_xor_unsat_certificate_for_query(&arena, &eqs)
            .expect("pure-Gauss certificate for the BV parity chain");
        assert!(cert.recheck().expect("recheck parses"));
    }

    #[cfg(feature = "full")]
    #[test]
    fn query_certificate_declines_for_satisfiable_query() {
        // A satisfiable BV query never yields a pure-Gauss XOR refutation: the
        // query-level certificate builder must return None (no false certificate).
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 2).unwrap();
        let y = arena.bv_var("y", 2).unwrap();
        let xor = arena.bv_xor(x, y).unwrap();
        let three = arena.bv_const(2, 3).unwrap();
        let eq = arena.eq(xor, three).unwrap();
        assert!(pure_gauss_xor_unsat_certificate_for_query(&arena, &[eq]).is_none());
    }

    #[test]
    fn certify_pure_gauss_declines_for_sat_xor_system() {
        // A satisfiable XOR system is NOT pure-Gauss unsat: no false certificate.
        let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();
        clauses.extend(xor_clauses(&[0, 1], true));
        clauses.extend(xor_clauses(&[1, 2], false));
        let refs: Vec<&[(usize, bool)]> = clauses.iter().map(Vec::as_slice).collect();
        let f = formula(3, &refs);
        assert!(!certify_pure_gauss_xor_unsat(&f));
        assert!(pure_gauss_xor_unsat_certificate(&f).is_none());
    }

    #[test]
    fn certify_pure_gauss_declines_when_no_xor_structure() {
        // No recognized XOR gate ⇒ the extracted system is empty ⇒ no pure-Gauss
        // refutation (it would have to come from CNF clauses, the interleaved
        // case, which this sub-case does not certify).
        let f = formula(2, &[&[(0, false), (1, false)]]); // plain (x0 ∨ x1)
        assert_eq!(extract_xors(&f).num_recognized, 0);
        assert!(!certify_pure_gauss_xor_unsat(&f));
    }

    #[test]
    fn interleaved_xor_unsat_stays_trusted_not_certified() {
        // The recovered XOR system alone is SAT (`x0 ⊕ x1 = 0`), but the formula
        // is UNSAT because two NON-XOR unit clauses (`x0`, `¬x1`) force the XOR's
        // operands apart. The unsatisfiability therefore needs clause/XOR
        // interleaving — it is NOT pure-Gauss — so it must stay the trusted
        // `XorGaussian` hole: `unsat_from_xor` true, `Unchecked`, and the certified
        // stat absent. (Soundness boundary: never a false certificate here.)
        let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();
        clauses.extend(xor_clauses(&[0, 1], false)); // x0 ⊕ x1 = 0 (recognized, SAT)
        clauses.push(vec![(0, false)]); // unit x0 (not an XOR gate)
        clauses.push(vec![(1, true)]); // unit ¬x1 (not an XOR gate)
        let refs: Vec<&[(usize, bool)]> = clauses.iter().map(Vec::as_slice).collect();
        let f = formula(2, &refs);
        assert_eq!(
            extract_xors(&f).num_recognized,
            1,
            "only the width-2 XOR is recognized; the units are not"
        );
        // The XOR subsystem alone is satisfiable ⇒ no pure-Gauss refutation.
        assert!(extract_xors(&f).system.unsat_reason_subset().is_none());
        assert!(!certify_pure_gauss_xor_unsat(&f));

        let mut stats = SolveStats::default();
        let out = maybe_xor_cdcl_fallback(&f, unknown(), &mut stats);
        // Still decided UNSAT — the interleaved path is not regressed.
        let SatResult::Unsat(evidence) = &out.result else {
            panic!("expected unsat");
        };
        assert_eq!(evidence.proof, SatProofStatus::Unchecked);
        assert!(
            out.unsat_from_xor,
            "interleaved XOR unsat stays the trusted hole"
        );
        assert!(stat(&stats, "xor_cdcl_fallback_unsat_drat_checked").is_none());
    }

    #[test]
    fn fallback_decides_xor_sat_without_trust_cost() {
        // A satisfiable XOR system: the fallback upgrades `unknown` to a `sat`
        // CnfAssignment (which then flows through the standard replay gate), and
        // it carries no trust signal (`unsat_from_xor` is false).
        // x0 ⊕ x1 = 1 and x1 ⊕ x2 = 0: satisfiable (e.g. 1,0,0).
        let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();
        clauses.extend(xor_clauses(&[0, 1], true));
        clauses.extend(xor_clauses(&[1, 2], false));
        let refs: Vec<&[(usize, bool)]> = clauses.iter().map(Vec::as_slice).collect();
        let f = formula(3, &refs);
        assert!(extract_xors(&f).num_recognized > 0);

        let mut stats = SolveStats::default();
        let out = maybe_xor_cdcl_fallback(&f, unknown(), &mut stats);
        let SatResult::Sat(assignment) = out.result else {
            panic!("expected sat");
        };
        assert!(!out.unsat_from_xor, "sat carries no trust cost");
        assert!(f.evaluate(assignment.values()).expect("len matches"));
        assert_eq!(stat(&stats, "xor_cdcl_fallback_sat"), Some(1.0));
    }

    #[test]
    fn fallback_skips_formula_without_xor_structure() {
        // No recognized XOR gate ⇒ the fallback does not run; the original
        // `unknown` is preserved and a skip stat is recorded.
        let f = formula(2, &[&[(0, false), (1, false)]]); // plain (x0 ∨ x1)
        assert_eq!(extract_xors(&f).num_recognized, 0);
        let mut stats = SolveStats::default();
        let out = maybe_xor_cdcl_fallback(&f, unknown(), &mut stats);
        assert!(matches!(out.result, SatResult::Unknown(_)));
        assert!(!out.unsat_from_xor);
        assert_eq!(stat(&stats, "xor_cdcl_fallback_no_xor"), Some(1.0));
        assert!(stat(&stats, "xor_cdcl_fallback_fired").is_none());
    }

    #[test]
    fn fallback_skips_formula_over_clause_cap() {
        // Above the clause cap the fallback never runs (it is wall-clock
        // unbounded); the original `unknown` is preserved with a size-skip stat.
        // Pad an XOR-structured formula past the cap with trivial unit clauses on
        // a fresh padding variable (kept satisfiability-irrelevant).
        let f = parity_chain_unsat(4);
        let pad_start = f.variable_count();
        let mut padded = CnfFormula::new(pad_start + 1);
        for clause in f.clauses() {
            padded.add_clause(clause.clone()).expect("re-add clause");
        }
        let pad_var = pad_start;
        for _ in 0..=XOR_CDCL_FALLBACK_MAX_CLAUSES {
            padded
                .add_clause(CnfClause::new(vec![lit(pad_var, false)]))
                .expect("unit clause");
        }
        assert!(padded.clauses().len() > XOR_CDCL_FALLBACK_MAX_CLAUSES);

        let mut stats = SolveStats::default();
        let out = maybe_xor_cdcl_fallback(&padded, unknown(), &mut stats);
        assert!(matches!(out.result, SatResult::Unknown(_)));
        assert!(!out.unsat_from_xor);
        assert_eq!(stat(&stats, "xor_cdcl_fallback_skipped_size"), Some(1.0));
        assert!(stat(&stats, "xor_cdcl_fallback_fired").is_none());
    }

    /// A sat model whose replay cannot be *evaluated* (an arithmetic overflow in
    /// the trust-anchor evaluator) must degrade to a graceful `Unknown` reason —
    /// never a panic, never an accepted (unverified) sat, never a hard error. The
    /// sound stance: if we can't confirm the model, we don't accept it.
    #[test]
    fn replay_eval_overflow_yields_graceful_unknown_not_panic_or_accept() {
        let mut arena = TermArena::new();
        // x : Int, model-bound to i128::MAX. The assertion `(x * 2) >= 0` is
        // Bool-sorted but its evaluation overflows (`i128::MAX * 2`), so the
        // model is unverifiable.
        let x = arena.int_var("x").expect("declare x");
        let two = arena.int_const(2);
        let prod = arena.int_mul(x, two).expect("x*2");
        let zero = arena.int_const(0);
        let assertion = arena.int_ge(prod, zero).expect("x*2 >= 0");

        let mut model = Model::new();
        let x_sym = match arena.node(x) {
            axeyum_ir::TermNode::Symbol(s) => *s,
            _ => unreachable!("int_var builds a Symbol node"),
        };
        model.set(x_sym, Value::Int(i128::MAX));

        // Sanity: eval of the assertion really does overflow.
        assert_eq!(
            eval(&arena, assertion, &model.to_assignment()),
            Err(IrError::ArithmeticOverflow { op: "int_mul" })
        );

        // The replay boundary must map that to `Ok(Some(Unknown))`: not an Err
        // (which would surface as a hard error), not Ok(None) (which would accept
        // an unverified sat).
        let reason = replay_model(&arena, &[assertion], None, &model)
            .expect("replay must not return a hard error on an overflow");
        let reason = reason.expect("overflow must yield an Unknown reason, not an accepted model");
        assert!(
            reason.detail.contains("could not be verified"),
            "unexpected reason: {}",
            reason.detail
        );
    }

    /// The native core, when asked to check its proof, returns an `unsat`
    /// stamped `Checked` for a genuinely unsatisfiable formula — the checked
    /// proof falls out of a SINGLE solve.
    #[test]
    fn native_cdcl_checks_inline_proof_for_unsat() {
        // `x ∧ ¬x` is unsat.
        let f = formula(1, &[&[(0, false)], &[(0, true)]]);
        let result = solve_with_native_cdcl(&f, None, None, true, None);
        assert_eq!(
            result.result,
            SatResult::Unsat(SatUnsatEvidence {
                proof: SatProofStatus::Checked,
                failed_assumptions: Vec::new(),
            }),
            "native unsat with check_proof must be Checked"
        );
        assert!(result.proof_replay.is_some());
    }

    /// Without `check_proof`, the native core stamps `Unchecked` (no verification
    /// cost) — the prior behaviour, now opt-in.
    #[test]
    fn native_cdcl_skips_inline_check_when_not_requested() {
        let f = formula(1, &[&[(0, false)], &[(0, true)]]);
        let result = solve_with_native_cdcl(&f, None, None, false, None);
        assert_eq!(
            result.result,
            SatResult::Unsat(SatUnsatEvidence {
                proof: SatProofStatus::Unchecked,
                failed_assumptions: Vec::new(),
            })
        );
        assert_eq!(result.proof_replay, None);
    }

    /// A `Checked` unsat is accepted with no re-derivation: `ensure_unsat_proof_checked`
    /// returns `Ok(None)` and records only the inline stat, never the
    /// re-derivation stat.
    #[test]
    fn ensure_proof_accepts_checked_without_rederivation() {
        let f = formula(1, &[&[(0, false)], &[(0, true)]]);
        let checked = SatResult::Unsat(SatUnsatEvidence {
            proof: SatProofStatus::Checked,
            failed_assumptions: Vec::new(),
        });
        let mut stats = SolveStats::default();
        let outcome = ensure_unsat_proof_checked(true, &checked, &f, &mut stats, false)
            .expect("checked proof must not error");
        assert!(outcome.is_none(), "a Checked unsat must be accepted");
        assert!(
            stats
                .backend
                .iter()
                .any(|(n, _)| n == "unsat_proof_checked_inline"),
            "the inline stat must be recorded"
        );
        assert!(
            !stats
                .backend
                .iter()
                .any(|(n, _)| n == "unsat_proof_checked"),
            "a Checked unsat must NOT re-derive the proof"
        );
    }

    /// The batsat fallback (`Unchecked`) route still fails closed / certifies via
    /// re-derivation: on a genuinely unsat formula `ensure_unsat_proof_checked`
    /// re-derives, checks, and accepts (`Ok(None)`) recording the re-derivation
    /// stat — never accepting an unsat without a checked proof.
    #[test]
    fn ensure_proof_rederives_for_unchecked_batsat_path() {
        let f = formula(1, &[&[(0, false)], &[(0, true)]]);
        let unchecked = SatResult::Unsat(SatUnsatEvidence {
            proof: SatProofStatus::Unchecked,
            failed_assumptions: Vec::new(),
        });
        let mut stats = SolveStats::default();
        let outcome = ensure_unsat_proof_checked(true, &unchecked, &f, &mut stats, false)
            .expect("re-derivation of a genuine unsat must certify");
        assert!(
            outcome.is_none(),
            "a re-derived + checked unsat must be accepted"
        );
        assert!(
            stats
                .backend
                .iter()
                .any(|(n, _)| n == "unsat_proof_checked"),
            "the batsat fallback must re-derive + check the proof"
        );
    }
    // --- BVE admission: the gate, the budget, and the case each one exists for ---

    /// A formula whose setup cost is large enough that the two branches of the
    /// admission decision are distinguishable: `n` three-literal clauses over
    /// `n` variables.
    fn wide_formula(n: usize) -> CnfFormula {
        let mut f = CnfFormula::new(n);
        for i in 0..n {
            f.add_clause(CnfClause::new(vec![
                lit(i, false),
                lit((i + 1) % n, true),
                lit((i + 2) % n, false),
            ]))
            .expect("valid clause");
        }
        f
    }

    /// With no deadline the decision is size-proportional and fully
    /// deterministic: the budget is `BVE_BUDGET_SETUP_MULTIPLE` x setup, and
    /// the pass is admitted.
    ///
    /// This is also the statement that the shipped constants are consistent
    /// with each other: a `BVE_BUDGET_SETUP_MULTIPLE` below
    /// `BVE_MIN_RECOVERY_MULTIPLE` would delay *every* formula in the
    /// no-deadline case and silently switch BVE off, which no other test in
    /// this crate would notice.
    #[test]
    fn without_a_deadline_bve_is_admitted_with_a_size_proportional_budget() {
        let f = wide_formula(500);
        let mut stats = SolveStats::default();
        let budget = bve_admission(&f, None, &mut stats).expect("no deadline must admit");
        let setup = (literal_occurrences(&f) + 2 * f.variable_count()) as u64;
        assert_eq!(budget, setup * BVE_BUDGET_SETUP_MULTIPLE);
        const { assert!(BVE_BUDGET_SETUP_MULTIPLE >= BVE_MIN_RECOVERY_MULTIPLE) };
        assert_eq!(stat(&stats, "bve_admitted"), Some(1.0));
        assert_eq!(stat(&stats, "bve_setup_work"), Some(u64_as_f64(setup)));
    }

    /// The gate fires when the remaining slice cannot recover the setup cost.
    ///
    /// This is the population `BVE_MIN_RECOVERY_MULTIPLE` exists for and the
    /// only test that reaches the `Grant::Delayed` arm, so without it that arm
    /// is unexecuted code claiming to be a safety mechanism. The deadline is in
    /// the **past**, which is the limiting case of "no time left" and is exact
    /// rather than racy — a deadline a few milliseconds ahead would make this
    /// test a stopwatch.
    #[test]
    fn a_spent_slice_delays_bve_instead_of_paying_for_setup_it_cannot_use() {
        let f = wide_formula(500);
        let already_gone = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("the process has been up for at least a second");
        let mut stats = SolveStats::default();
        assert!(
            bve_admission(&f, Some(already_gone), &mut stats).is_none(),
            "a slice with nothing left in it must not start the pass"
        );
        assert_eq!(stat(&stats, "bve_admitted"), Some(0.0));
        let setup = (literal_occurrences(&f) + 2 * f.variable_count()) as u64;
        assert_eq!(
            stat(&stats, "bve_admission_threshold"),
            Some(u64_as_f64(setup * BVE_MIN_RECOVERY_MULTIPLE))
        );
        assert_eq!(stat(&stats, "bve_admission_accrued"), Some(0.0));
    }

    /// A generous deadline leaves the size term binding, so the two branches
    /// agree. Without this the previous test could be passing because the
    /// deadline branch always delays, which is a different bug with the same
    /// symptom.
    #[test]
    fn a_generous_deadline_does_not_change_the_budget() {
        let f = wide_formula(500);
        let mut with_dl = SolveStats::default();
        let mut without_dl = SolveStats::default();
        let far = Instant::now() + Duration::from_secs(600);
        assert_eq!(
            bve_admission(&f, Some(far), &mut with_dl),
            bve_admission(&f, None, &mut without_dl),
            "600 s buys far more than the size term allows, so the size term binds"
        );
    }

    /// A test [`InprocessObserver`] that offers a budget to exactly ONE pass and
    /// declines the other, and keeps every counter the schedule emitted.
    ///
    /// One pass at a time because the passes compose: subsumption changes the
    /// formula BVE is then offered, so an observer that grants both cannot
    /// attribute a change in `bve_work_spent` to BVE's own grant.
    struct OnePassObserver {
        pass: OccurrencePass,
        budget: Option<u64>,
        counts: Vec<(String, f64)>,
    }

    impl OnePassObserver {
        fn new(pass: OccurrencePass, budget: Option<u64>) -> Self {
            Self {
                pass,
                budget,
                counts: Vec::new(),
            }
        }

        fn get(&self, name: &str) -> Option<f64> {
            self.counts
                .iter()
                .find(|(key, _)| key == name)
                .map(|(_, value)| *value)
        }
    }

    impl InprocessObserver for OnePassObserver {
        fn grant(&mut self, pass: OccurrencePass, _formula: &CnfFormula) -> Option<u64> {
            if pass == self.pass { self.budget } else { None }
        }
        fn count(&mut self, name: &str, value: f64) {
            self.counts.push((name.to_owned(), value));
        }
    }

    /// Runs the SHIPPING schedule over `f` with only `pass` granted `budget`,
    /// and returns what the schedule recorded.
    fn schedule_one_pass(
        f: &CnfFormula,
        pass: OccurrencePass,
        budget: Option<u64>,
    ) -> OnePassObserver {
        let mut observer = OnePassObserver::new(pass, budget);
        let _ = inprocess_scheduled(f, InprocessSchedule::OFF, None, &mut observer);
        observer
    }

    /// The granted budget must reach BVE, not merely be computed.
    ///
    /// This exists because the obvious mutation — compute the budget, then call
    /// `eliminate_variables_within` with `BveOptions::DEFAULT` — **survived the
    /// whole `--lib --features full` sweep** when the decision was inline at the
    /// call site. The fixture is a formula whose unbudgeted BVE spends far more
    /// than the budget under test, so "budget applied" and "budget ignored"
    /// produce different `work_spent`, and the assertion is on the difference
    /// rather than on an invariant that holds either way.
    ///
    /// Since ADR-1810 it runs through [`inprocess_scheduled`] — the shipping
    /// route — rather than through a solver-local wrapper, and it reads the
    /// schedule's own `bve_work_spent` counter rather than re-deriving one. The
    /// wiring under test is therefore the wiring that ships.
    #[test]
    fn the_granted_budget_reaches_the_pass() {
        let f = wide_formula(4000);
        let unbudgeted = schedule_one_pass(&f, OccurrencePass::Bve, Some(u64::MAX));
        let spent_unbudgeted = unbudgeted.get("bve_work_spent").expect("bve_work_spent");
        let setup = u64_as_f64((literal_occurrences(&f) + 2 * f.variable_count()) as u64);
        assert!(
            spent_unbudgeted > setup,
            "fixture must spend past setup unbudgeted: {spent_unbudgeted} vs {setup}"
        );

        // Half way between the setup floor and what the pass spends when nothing
        // stops it. Derived from this run rather than written as a literal, so
        // the test cannot quietly become vacuous when the fixture or the
        // charging rules change.
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let tight = (setup + (spent_unbudgeted - setup) / 2.0) as u64;
        let budgeted = schedule_one_pass(&f, OccurrencePass::Bve, Some(tight));
        assert_eq!(
            budgeted.get("bve_work_exhausted"),
            Some(1.0),
            "the budget must be the reason the pass stopped"
        );
        let spent_budgeted = budgeted.get("bve_work_spent").expect("bve_work_spent");
        assert!(
            spent_budgeted < spent_unbudgeted,
            "a budget that is ignored spends exactly what no budget spends: \
             {spent_budgeted} vs {spent_unbudgeted}"
        );

        // And the `None` arm really declines rather than running cheaply.
        let declined = schedule_one_pass(&f, OccurrencePass::Bve, None);
        assert_eq!(declined.get("bve_work_spent"), Some(0.0));
        assert_eq!(
            declined.get("bve_variables_eliminated"),
            Some(0.0),
            "a declined pass eliminates nothing"
        );
    }

    /// A `None` grant must mean the pass did not run — not that it ran with a
    /// budget of zero. The two differ by the whole `O(|F|)` occurrence-list
    /// build, which is the cost being declined.
    ///
    /// Both arms go through the shipping schedule, so this is a statement about
    /// what `inprocess_scheduled` does with a `None` from the admission test and
    /// not about a pass called directly.
    #[test]
    fn skipped_is_not_the_same_as_a_zero_budget() {
        let f = wide_formula(500);

        let skipped = schedule_one_pass(&f, OccurrencePass::Bve, None);
        assert_eq!(skipped.get("bve_work_spent"), Some(0.0));
        assert_eq!(skipped.get("bve_variables_eliminated"), Some(0.0));
        assert_eq!(
            skipped.get("cnf_clauses_solved"),
            Some(usize_to_f64(f.clauses().len())),
            "a declined pass leaves the clause set alone"
        );

        let zero_budget = schedule_one_pass(&f, OccurrencePass::Bve, Some(0));
        assert!(
            zero_budget
                .get("bve_work_spent")
                .is_some_and(|spent| spent > 0.0),
            "a zero-budget call still pays for setup; that is why declining exists"
        );
    }

    // --- Subsumption admission: the same gate, its own constants ---

    /// With no deadline subsumption's budget is size-proportional and
    /// deterministic, exactly as BVE's is.
    ///
    /// The `const` assertion is the statement that the shipped constants are
    /// consistent: a `SUBSUME_BUDGET_SETUP_MULTIPLE` below the recovery
    /// multiple would delay *every* formula in the no-deadline case and switch
    /// subsumption off entirely, which no other test here would notice.
    #[test]
    fn without_a_deadline_subsumption_is_admitted_with_a_size_proportional_budget() {
        let f = wide_formula(500);
        let mut stats = SolveStats::default();
        let budget = subsume_admission(&f, None, &mut stats).expect("no deadline must admit");
        let setup = (literal_occurrences(&f) + 2 * f.variable_count()) as u64;
        assert_eq!(budget, setup * SUBSUME_BUDGET_SETUP_MULTIPLE);
        const { assert!(SUBSUME_BUDGET_SETUP_MULTIPLE >= BVE_MIN_RECOVERY_MULTIPLE) };
        assert_eq!(stat(&stats, "subsume_admitted"), Some(1.0));
        assert_eq!(stat(&stats, "subsume_setup_work"), Some(u64_as_f64(setup)));
    }

    /// The delay arm, reached for subsumption too. Without this the shared
    /// `admit_occurrence_pass` would be exercised on one pass only, and the
    /// second caller would be untested code claiming to reuse a tested
    /// mechanism.
    #[test]
    fn a_spent_slice_delays_subsumption_as_well() {
        let f = wide_formula(500);
        let already_gone = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("the process has been up for at least a second");
        let mut stats = SolveStats::default();
        assert!(
            subsume_admission(&f, Some(already_gone), &mut stats).is_none(),
            "a slice with nothing left in it must not start the pass"
        );
        assert_eq!(stat(&stats, "subsume_admitted"), Some(0.0));
        let setup = (literal_occurrences(&f) + 2 * f.variable_count()) as u64;
        assert_eq!(
            stat(&stats, "subsume_admission_threshold"),
            Some(u64_as_f64(setup * BVE_MIN_RECOVERY_MULTIPLE))
        );
    }

    /// The two passes are admitted by ONE policy with different constants, so
    /// their budgets must be in the same ratio as their multiples on the same
    /// formula. If they ever stop being, the shared function has been forked.
    #[test]
    fn both_passes_are_budgeted_by_the_same_policy() {
        let f = wide_formula(500);
        let mut a = SolveStats::default();
        let mut b = SolveStats::default();
        let bve = bve_admission(&f, None, &mut a).expect("admitted");
        let subsume = subsume_admission(&f, None, &mut b).expect("admitted");
        assert_eq!(
            bve * SUBSUME_BUDGET_SETUP_MULTIPLE,
            subsume * BVE_BUDGET_SETUP_MULTIPLE,
            "one policy, two constants: {bve} and {subsume} must scale together"
        );
    }

    /// The granted budget must reach subsumption, not merely be computed.
    ///
    /// The same wiring gap `the_granted_budget_reaches_the_pass` documents for
    /// BVE, and it is a real gap rather than a hypothetical one: the mutation
    /// is "compute the budget, then pass `SubsumeOptions::DEFAULT`", it
    /// compiles, it produces identical verdicts, and nothing else in this crate
    /// looks at `subsume_work_spent`. The budget under test is derived from the
    /// unbudgeted run so the fixture cannot quietly go vacuous when the
    /// charging rules change.
    ///
    /// Runs through the shipping schedule since ADR-1810, for the same reason
    /// its BVE twin does.
    #[test]
    fn the_granted_subsume_budget_reaches_the_pass() {
        let f = wide_formula(4000);
        let unbudgeted = schedule_one_pass(&f, OccurrencePass::Subsume, Some(u64::MAX));
        let spent_unbudgeted = unbudgeted
            .get("subsume_work_spent")
            .expect("subsume_work_spent");
        let setup = u64_as_f64((literal_occurrences(&f) + 2 * f.variable_count()) as u64);
        assert!(
            spent_unbudgeted > setup,
            "fixture must spend past setup unbudgeted: {spent_unbudgeted} vs {setup}"
        );

        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let tight = (setup + (spent_unbudgeted - setup) / 2.0) as u64;
        let budgeted = schedule_one_pass(&f, OccurrencePass::Subsume, Some(tight));
        assert_eq!(
            budgeted.get("subsume_work_exhausted"),
            Some(1.0),
            "the budget must be the reason the pass stopped"
        );
        let spent_budgeted = budgeted
            .get("subsume_work_spent")
            .expect("subsume_work_spent");
        assert!(
            spent_budgeted < spent_unbudgeted,
            "a budget that is ignored spends exactly what no budget spends: \
             {spent_budgeted} vs {spent_unbudgeted}"
        );

        // And the `None` arm declines rather than running cheaply: no
        // normalization, no occurrence lists, the clause set returned verbatim.
        let declined = schedule_one_pass(&f, OccurrencePass::Subsume, None);
        assert_eq!(declined.get("subsume_work_spent"), Some(0.0));
        assert_eq!(
            declined.get("cnf_clauses_solved"),
            Some(usize_to_f64(f.clauses().len()))
        );
    }

    /// The measurement lever is a lever, not a default.
    ///
    /// The parsing rules are read from the shipped function rather than
    /// re-derived here: a test that recomputes the decision inline passes while
    /// the artifact is wrong, which is the failure mode this repository has
    /// measured most often.
    #[test]
    fn the_measurement_levers_default_to_the_shipped_constants() {
        assert_eq!(parse_multiple_lever(None, 1234), 1234, "absent = shipped");
        assert_eq!(parse_multiple_lever(Some("off"), 1234), u64::MAX);
        assert_eq!(parse_multiple_lever(Some("OFF"), 1234), u64::MAX);
        assert_eq!(parse_multiple_lever(Some("0"), 1234), u64::MAX);
        assert_eq!(parse_multiple_lever(Some("7"), 1234), 7);
        assert_eq!(
            parse_multiple_lever(Some("nonsense"), 1234),
            1234,
            "a typo must keep the shipped arm, not invent one"
        );

        assert!(parse_compact_lever(None, true), "absent = shipped");
        assert!(!parse_compact_lever(None, false));
        assert!(parse_compact_lever(Some("1"), false));
        assert!(parse_compact_lever(Some("on"), false));
        assert!(!parse_compact_lever(Some("0"), true));
        assert!(!parse_compact_lever(Some("off"), true));
        assert!(parse_compact_lever(Some("maybe"), true), "typo = shipped");
    }
}
