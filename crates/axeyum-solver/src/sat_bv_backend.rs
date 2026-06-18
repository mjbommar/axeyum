//! Pure Rust SAT-backed bit-vector backend.
//!
//! This backend is the first Phase 5 composition slice: Axeyum query terms are
//! lowered to AIG, encoded to CNF, solved through the pure-Rust `BatSat` adapter,
//! lifted back into an Axeyum model, and replayed against the original terms
//! before a `sat` result is accepted. Z3 is not used and unsupported lowering
//! remains explicit rather than falling through to an oracle.

use std::time::Duration;

// Monotonic clock: on wasm32 the browser has no `std` clock, so use `web-time`'s
// drop-in `Instant` (ADR-0017). Native targets use the std clock.
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use axeyum_bv::{
    BitLowerError, BitLowering, first_unsupported_op, first_unsupported_sort, lower_terms,
};
use axeyum_cnf::{
    BveOptions, CnfAssignment, CnfEncoding, CnfError, CnfFormula, ProofSolveOutcome,
    Reconstruction, SatError, SatProofStatus, SatResult, SatUnsatEvidence, XorCdclResult,
    XorPropagation, check_drat, eliminate_variables_within, extract_xors, simplify_within,
    solve_with_drat_proof, solve_with_rustsat_batsat_timeout, solve_with_xor_cdcl, tseitin_encode,
    xor_propagate,
};
use axeyum_ir::{
    Assignment, IrError, Sort, TermArena, TermId, TermStats, Value, eval, well_founded_default,
};
use axeyum_query::{Query, QueryPlan};

use crate::backend::{
    Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig, SolverError, UnknownKind,
    UnknownReason,
};
use crate::model::Model;

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

    fn check_with_replay(
        &mut self,
        arena: &TermArena,
        assertions: &[TermId],
        replay_plan: Option<&QueryPlan>,
        config: &SolverConfig,
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

        if let Some(result) = oversized_encoding_refusal(arena, assertions, config) {
            return Ok(result);
        }

        let mut stats = SolveStats {
            assertion_count: assertions.len() as u64,
            terms_translated: shape.dag_nodes,
            ..SolveStats::default()
        };

        let bit_blast_start = Instant::now();
        let lowering = lower_terms(arena, assertions).map_err(map_lower_error)?;
        let bit_blast = bit_blast_start.elapsed();

        let roots = lowering
            .roots()
            .iter()
            .map(|root| root.bits()[0])
            .collect::<Vec<_>>();
        let cnf_start = Instant::now();
        let encoding =
            tseitin_encode(lowering.aig(), &roots).map_err(|error| map_cnf_error(&error))?;
        let cnf_encode = cnf_start.elapsed();
        stats.translate = bit_blast + cnf_encode;
        push_duration_ms(&mut stats, "bit_blast_ms", bit_blast);
        push_duration_ms(&mut stats, "cnf_encode_ms", cnf_encode);
        record_encoding_stats(&mut stats, &lowering, encoding.formula());

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
        let inprocessed = maybe_inprocess(config, encoding.formula(), deadline, &mut stats);
        let solve_formula: &CnfFormula = inprocessed
            .as_ref()
            .map_or_else(|| encoding.formula(), |out| &out.formula);
        let reconstruction = inprocessed.as_ref().map(|out| &out.reconstruction);

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

        let sat_timeout =
            deadline.map(|deadline| deadline.saturating_duration_since(Instant::now()));
        let solve_start = Instant::now();
        let mut sat_result = solve_with_rustsat_batsat_timeout(solve_formula, sat_timeout)
            .map_err(|error| map_sat_error(&error))?;
        stats.solve = solve_start.elapsed();

        // CDCL(XOR) search fallback (ADR-0035): only on an `unknown` batsat
        // verdict (timeout/budget), only when opted in, and only on a formula
        // carrying recognized XOR structure within the conservative clause cap.
        // Its `unsat` is the trusted `XorGaussian` ledger hole (no DRAT — XOR
        // reasoning is not RUP); its `sat` carries no trust cost (it threads the
        // same reconstruction + AIG/model/term replay the batsat path uses and is
        // discarded on replay failure). This never weakens an existing definite
        // verdict — it can only *upgrade* an `unknown`.
        let mut xor_cdcl_unsat = false;
        if matches!(sat_result, SatResult::Unknown(_)) && config.xor_cdcl_fallback {
            let fallback = maybe_xor_cdcl_fallback(solve_formula, sat_result, &mut stats);
            sat_result = fallback.result;
            xor_cdcl_unsat = fallback.unsat_from_xor;
        }

        // The xor-derived `unsat` is the trusted `XorGaussian` hole and is NOT
        // RUP, so it cannot be DRAT-verified (the checker would correctly reject a
        // synthesized proof). Skip the proof route for it; only batsat `unsat` is
        // DRAT-checked here.
        if config.prove_unsat && !xor_cdcl_unsat && matches!(sat_result, SatResult::Unsat(_)) {
            // The reduced formula is equisatisfiable with the original, so an
            // independent UNSAT proof of it certifies the original is UNSAT.
            verify_unsat_proof(solve_formula, &mut stats)?;
        }

        // Lift a reduced `sat` model back to the original CNF variables (no-op
        // without inprocessing) so the AIG/model lift uses the original encoding.
        let sat_result = reconstruct_sat_result(sat_result, reconstruction);

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
}

impl SolverBackend for SatBvBackend {
    fn capabilities(&self) -> Capabilities {
        Capabilities {
            name: "axeyum-sat-bv rustsat-batsat".to_owned(),
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
        self.check_with_replay(arena, assertions, None, config)
    }

    fn check_query(
        &mut self,
        arena: &TermArena,
        query: &Query,
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        let plan = query.plan_full(arena);
        let assertions = plan.solver_terms().collect::<Vec<_>>();
        self.check_with_replay(arena, &assertions, Some(&plan), config)
    }

    fn last_stats(&self) -> Option<&SolveStats> {
        self.stats.as_ref()
    }
}

/// Records the AIG and (un-inprocessed) CNF size counters for the most recent
/// encoding into `stats.backend`.
fn record_encoding_stats(stats: &mut SolveStats, lowering: &BitLowering, formula: &CnfFormula) {
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
}

/// A Tseitin formula after CNF inprocessing, plus the stack that lifts a model
/// of the reduced formula back to the original CNF variables.
struct Inprocessed {
    formula: CnfFormula,
    reconstruction: Reconstruction,
}

/// Inprocessing admission bound. Since T1.1.4 both passes are occurrence-list
/// indexed and near-linear with internal work budgets (`axeyum_cnf::simplify`
/// forward one-watch subsumption, `axeyum_cnf::bve` full occurrence lists + a
/// touched queue), so they no longer blow a solve budget on the wide bit-blasted
/// CNFs that the old `O(clauses²)`/`O(variables·clauses)` versions hung on (the
/// earlier 5k-var/20k-clause cap saw 13–22 s passes; the indexed versions run in
/// milliseconds). This is now a generous admission ceiling covering the whole
/// curated slice, not a hang-preventer; the passes' own budgets are the real
/// safety net.
const INPROCESS_MAX_VARIABLES: usize = 200_000;
const INPROCESS_MAX_CLAUSES: usize = 1_000_000;

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
/// whether the `unsat` verdict came from the trusted CDCL(XOR) core (so the
/// caller can skip the DRAT proof route, which cannot certify a non-RUP XOR
/// refutation, and surface the `XorGaussian` trust hole instead).
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
    let out = inprocess(formula, inprocess_deadline, stats);
    let elapsed = start.elapsed();
    stats.translate += elapsed;
    push_duration_ms(stats, "inprocess_ms", elapsed);
    Some(out)
}

/// Runs subsumption then bounded variable elimination on `formula`, recording
/// what each pass removed in `stats`. Subsumption is model-preserving; BVE is
/// equisatisfiable and pairs the reduced formula with a reconstruction stack. Both
/// passes stop scheduling new work once `deadline` passes.
fn inprocess(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    stats: &mut SolveStats,
) -> Inprocessed {
    // XOR propagation (CDCL(XOR) preprocessing, path 2 of the multiplier wall):
    // recover the XOR gates entailed by the formula, Gaussian-solve them, and
    // append the implied unit clauses. Each added unit is entailed by the formula
    // (the recognized gates are equivalent to clause-subsets of it), so it removes
    // no models and adds none — the augmented formula is logically equivalent and
    // needs no extra reconstruction. The contradictory-subsystem (`Unsat`) verdict
    // is *not* trusted as a certificate here (no XOR proof emitter yet); that
    // formula is left unchanged for the checked SAT solve to refute independently.
    // Capped separately because Gaussian carries no internal deadline yet.
    let xor_base: Option<CnfFormula> = if formula.clauses().len() <= XOR_PROPAGATE_MAX_CLAUSES {
        match xor_propagate(formula) {
            XorPropagation::Propagated {
                formula: augmented,
                stats: xstats,
            } => {
                stats.backend.push((
                    "xor_gates_recognized".to_owned(),
                    usize_to_f64(xstats.xors_recognized),
                ));
                stats.backend.push((
                    "xor_units_added".to_owned(),
                    usize_to_f64(xstats.units_added),
                ));
                stats.backend.push((
                    "xor_equalities_available".to_owned(),
                    usize_to_f64(xstats.equalities_available),
                ));
                (xstats.units_added > 0).then_some(augmented)
            }
            XorPropagation::Unsat => {
                stats.backend.push(("xor_subsystem_unsat".to_owned(), 1.0));
                None
            }
        }
    } else {
        stats
            .backend
            .push(("xor_propagate_skipped_size".to_owned(), 1.0));
        None
    };
    let base: &CnfFormula = xor_base.as_ref().unwrap_or(formula);

    let (simplified, subsume) = simplify_within(base, deadline);
    let bve = eliminate_variables_within(&simplified, BveOptions::default(), deadline);

    stats.backend.push(("cnf_inprocessing".to_owned(), 1.0));
    stats.backend.push((
        "subsume_tautologies_removed".to_owned(),
        usize_to_f64(subsume.tautologies_removed),
    ));
    stats.backend.push((
        "subsume_clauses_subsumed".to_owned(),
        usize_to_f64(subsume.clauses_subsumed),
    ));
    stats.backend.push((
        "subsume_literals_strengthened".to_owned(),
        usize_to_f64(subsume.literals_strengthened),
    ));
    stats.backend.push((
        "bve_variables_eliminated".to_owned(),
        usize_to_f64(bve.stats.variables_eliminated),
    ));
    stats.backend.push((
        "bve_clauses_removed".to_owned(),
        usize_to_f64(bve.stats.clauses_removed),
    ));
    stats.backend.push((
        "bve_clauses_added".to_owned(),
        usize_to_f64(bve.stats.clauses_added),
    ));
    // The variable count is preserved by both passes (an eliminated variable
    // simply occurs in no clause), so only the clause count moves here.
    stats.backend.push((
        "cnf_clauses_solved".to_owned(),
        usize_to_f64(bve.formula.clauses().len()),
    ));

    Inprocessed {
        formula: bve.formula,
        reconstruction: bve.reconstruction,
    }
}

/// Lifts a reduced `sat` assignment back to the original CNF variable space via
/// the BVE reconstruction stack. A no-op (identity) when inprocessing was off or
/// for non-`sat` results.
fn reconstruct_sat_result(result: SatResult, reconstruction: Option<&Reconstruction>) -> SatResult {
    match (result, reconstruction) {
        (SatResult::Sat(assignment), Some(reconstruction)) => SatResult::Sat(CnfAssignment::new(
            reconstruction.extend(assignment.values()),
        )),
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
/// - `Unsat` upgrades to `SatResult::Unsat` (`unsat_from_xor = true`): the trusted
///   `XorGaussian` hole, no DRAT proof.
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
            XorCdclFallback {
                result: SatResult::Unsat(SatUnsatEvidence {
                    proof: SatProofStatus::Unchecked,
                    failed_assumptions: Vec::new(),
                }),
                unsat_from_xor: true,
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

fn complete_model(arena: &TermArena, assignment: &Assignment) -> Model {
    let mut model = Model::new();
    for (symbol, _name, sort) in arena.symbols() {
        // A symbol unconstrained by the query gets its sort's well-founded
        // default (false/0/empty-array/base-constructor). Datatype symbols left
        // over from an eliminated datatype query are handled here too; an
        // uninhabited datatype simply gets no model entry.
        let value = assignment
            .get(symbol)
            .or_else(|| well_founded_default(arena, sort));
        if let Some(value) = value {
            model.set(symbol, value);
        }
    }
    model
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
            let lift_start = Instant::now();
            let aig_values = encoding
                .aig_node_values_from_assignment(lowering.aig(), &cnf_assignment)
                .map_err(|error| map_cnf_error(&error))?;
            let assignment = lowering
                .assignment_from_aig_values(&aig_values)
                .map_err(map_lower_error)?;
            let model = complete_model(arena, &assignment);
            replay_model(arena, assertions, replay_plan, &model)?;
            stats.model_lift = lift_start.elapsed();
            Ok(CheckResult::Sat(model))
        }
        SatResult::Unsat(_) => Ok(CheckResult::Unsat),
        SatResult::Unknown(reason) => {
            let kind = if reason.detail.contains("timeout") {
                UnknownKind::Timeout
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

fn replay_model(
    arena: &TermArena,
    assertions: &[TermId],
    replay_plan: Option<&QueryPlan>,
    model: &Model,
) -> Result<(), SolverError> {
    let assignment = model.to_assignment();
    if let Some(plan) = replay_plan {
        return plan
            .replay_original(arena, &assignment)
            .map_err(|error| SolverError::Backend(format!("sat model replay failed: {error}")));
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
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "sat model replay failed: assertion #{} failed evaluation: {error}",
                    term.index()
                )));
            }
        }
    }
    Ok(())
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
    const ABSOLUTE_CLAUSE_CEILING: u64 = 64_000_000;
    let estimated_clauses = estimate_blast_clauses(arena, assertions);
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

/// A cheap, pre-lowering **over-estimate** of the bit-blasted CNF clause count,
/// used to refuse oversized encodings before `lower_terms` allocates them
/// (graceful `unknown` instead of an out-of-memory abort). Walks the shared term
/// DAG once; each node contributes a per-operator cost in its result width —
/// multiplies are ~`w²`, divides/remainders ~`4w²`, shifts ~`w·log w`, and
/// everything else linear in `w` — then `~3×` the gate total approximates the
/// Tseitin clause count.
fn estimate_blast_clauses(arena: &TermArena, assertions: &[TermId]) -> u64 {
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
                Op::BvMul => w.saturating_mul(w),
                Op::BvUdiv | Op::BvUrem | Op::BvSdiv | Op::BvSrem | Op::BvSmod => {
                    w.saturating_mul(w).saturating_mul(4)
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

fn map_sat_error(error: &SatError) -> SolverError {
    SolverError::Backend(error.to_string())
}

/// Independently re-derives `unsat` with the proof-producing SAT core and
/// verifies its DRAT proof (ADR-0011/0012). A disagreement (the proof core
/// finds the formula satisfiable) or a failed proof is a soundness alarm.
fn verify_unsat_proof(formula: &CnfFormula, stats: &mut SolveStats) -> Result<(), SolverError> {
    match solve_with_drat_proof(formula) {
        ProofSolveOutcome::Unsat(proof) => match check_drat(formula, &proof) {
            Ok(true) => {
                stats.backend.push(("unsat_proof_checked".to_owned(), 1.0));
                Ok(())
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
        // The reference proof core exhausted its budget; the adapter's `unsat`
        // still stands, it is simply not DRAT-proof-checked.
        ProofSolveOutcome::ResourceOut => Ok(()),
    }
}

fn push_duration_ms(stats: &mut SolveStats, name: &str, duration: Duration) {
    stats
        .backend
        .push((name.to_owned(), duration.as_secs_f64() * 1000.0));
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

    fn stat(stats: &SolveStats, name: &str) -> Option<f64> {
        stats
            .backend
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| *v)
    }

    #[test]
    fn fallback_decides_xor_unsat_with_trust_signal() {
        // An XOR-structured UNSAT: the fallback upgrades `unknown` to `unsat`,
        // flags it as the trusted `XorGaussian` hole, and records the stat the
        // evidence layer reads.
        let f = parity_chain_unsat(6);
        assert!(
            extract_xors(&f).num_recognized > 0,
            "fixture must carry XORs"
        );
        let mut stats = SolveStats::default();
        let out = maybe_xor_cdcl_fallback(&f, unknown(), &mut stats);
        assert!(matches!(out.result, SatResult::Unsat(_)));
        assert!(out.unsat_from_xor, "unsat must be flagged as xor-derived");
        assert_eq!(stat(&stats, "xor_cdcl_fallback_fired"), Some(1.0));
        assert_eq!(stat(&stats, "xor_cdcl_fallback_unsat"), Some(1.0));
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
}
