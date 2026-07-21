//! Pure Rust SAT-backed bit-vector backend.
//!
//! This backend is the first Phase 5 composition slice: Axeyum query terms are
//! lowered to AIG, encoded to CNF, solved through the pure-Rust `BatSat` adapter,
//! lifted back into an Axeyum model, and replayed against the original terms
//! before a `sat` result is accepted. Z3 is not used and unsupported lowering
//! remains explicit rather than falling through to an oracle.

use std::collections::{BTreeMap, BTreeSet};
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
use axeyum_cnf::{
    BveOptions, CnfAssignment, CnfConstructionProfile, CnfDuplicateOriginProfile, CnfEncoding,
    CnfError, CnfFormula, CompactMap, DEFAULT_PROOF_SAT_CONFLICT_LIMIT, EncodedLit,
    ProofSolveOutcome, Reconstruction, SatError, SatProofStatus, SatResult, SatUnknownReason,
    SatUnsatEvidence, VivifyOptions, XorCdclResult, XorPropagation, check_drat, compact,
    eliminate_variables_within, extract_xors, simplify_within, solve_with_drat_proof,
    solve_with_drat_proof_with_limits, solve_with_rustsat_batsat_limits, solve_with_xor_cdcl,
    tseitin_encode, tseitin_encode_profiled_with_origins, vivify_within, write_drat,
    xor_gauss_drat_refutation, xor_propagate,
};
use axeyum_ir::{
    Assignment, IrError, Sort, SortId, TermArena, TermId, TermStats, Value, eval,
    well_founded_default,
};
use axeyum_query::{Query, QueryPlan, QueryReplayFailure};

use crate::backend::{
    BitLoweringMode, Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig,
    SolverError, UnknownKind, UnknownReason,
};
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

        let roots = lowering
            .roots()
            .iter()
            .map(|root| root.bits()[0])
            .collect::<Vec<_>>();
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

        let sat_timeout =
            deadline.map(|deadline| deadline.saturating_duration_since(Instant::now()));
        let solve_start = Instant::now();
        // Primary SAT search: the deadline-bounded native CDCL core when
        // `native_cdcl` is set, else the default `rustsat-batsat` adapter. Both
        // feed the same reconstruction + replay below (see `solve_with_native_cdcl`).
        let mut sat_result =
            primary_sat_search(config, solve_formula, deadline, sat_timeout, &mut stats)?;
        stats.solve = solve_start.elapsed();
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            self.stats = Some(stats);
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Timeout,
                detail: "pure-Rust BV backend timeout after SAT search".to_owned(),
            }));
        }

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
        // synthesized proof). Skip the proof route for it; only batsat/native
        // `unsat` is DRAT-checked here.
        let prove = config.prove_unsat && !xor_cdcl_unsat;
        if let Some(reason) =
            ensure_unsat_proof_checked(prove, &sat_result, solve_formula, &mut stats)?
        {
            self.stats = Some(stats);
            return Ok(CheckResult::Unknown(reason));
        }

        // Lift a compacted `sat` model back to the original CNF variables (no-op
        // without inprocessing) so the AIG/model lift uses the original encoding:
        // `compaction.expand` (→ BVE-reduced width) then `reconstruction.extend`.
        let sat_result = reconstruct_sat_result(sat_result, inprocessed.as_ref());

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
/// the reduced formula back to the original CNF variables.
///
/// The lift is a two-step composition. BVE removes clauses/variables but does
/// not renumber, so its reduced formula keeps the original (wide) variable count;
/// [`compact`] then densely renumbers the live variables, lowering
/// [`CnfFormula::variable_count`] so the variable-bound admission gate admits
/// cases that eliminated millions of variables. The `formula` field is the
/// *compacted* formula (the one submitted to the SAT solver); a `sat` model of it
/// is lifted by `compaction.expand` (→ original-width, BVE-reduced model) and then
/// `reconstruction.extend` (→ full original model), in that order.
struct Inprocessed {
    /// The compacted, BVE-reduced formula submitted to the SAT adapter.
    formula: CnfFormula,
    /// Lifts a compacted model up to the BVE-reduced (original-width) variables.
    compaction: CompactMap,
    /// Lifts a BVE-reduced model back to the original pre-BVE variables.
    reconstruction: Reconstruction,
}

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
    let out = inprocess(config, formula, inprocess_deadline, stats);
    let elapsed = start.elapsed();
    stats.translate += elapsed;
    push_duration_ms(stats, "inprocess_ms", elapsed);
    Some(out)
}

/// Runs clause vivification on `simplified` when `config.cnf_vivify` is set,
/// returning the strengthened (model-preserving) formula; otherwise returns
/// `simplified` unchanged.
///
/// Vivification has the same satisfying assignments and `variable_count` as its
/// input (no reconstruction trail), so the caller feeds the result straight into
/// `BVE` and the model-lift stack is untouched. The `vivify_*` stat keys mirror the
/// `subsume_*`/`bve_*` accounting.
///
/// In `prove_unsat` mode the pass's `DRAT` is *step-checked* as a standalone guard:
/// every step of `outcome.proof` must verify (RUP/RAT) against the pre-vivify
/// formula — i.e. [`check_drat`] returns `Ok(_)`, not `Err` (vivify's own contract:
/// each added clause is RUP by construction). This is not yet composed into the
/// end-to-end solve proof — the same accounting tier as subsumption/`BVE`. A failed
/// step-check is a soundness alarm, so the un-vivified formula is returned (the
/// verdict is unaffected either way, since vivify is model-preserving).
fn maybe_vivify(
    config: &SolverConfig,
    simplified: &CnfFormula,
    deadline: Option<Instant>,
    stats: &mut SolveStats,
) -> CnfFormula {
    if !config.cnf_vivify {
        return simplified.clone();
    }
    let outcome = vivify_within(simplified, VivifyOptions::default(), deadline);
    if config.prove_unsat {
        // Step-guard: every step of vivify's DRAT must verify (RUP/RAT) against the
        // formula it acted on. `check_drat` returns `Ok(true)` only when the proof
        // also derives the empty clause (a strengthening collapsing to `()`), and
        // `Ok(false)` for an ordinary strengthening that verifies but does not
        // refute — both are *step-sound*; only `Err` (an unjustified add) is a
        // soundness alarm. So the guard is `is_ok()`, matching vivify's own tests.
        let step_ok = check_drat(simplified, &outcome.proof).is_ok();
        stats.backend.push((
            "vivify_drat_step_checked".to_owned(),
            if step_ok { 1.0 } else { 0.0 },
        ));
        if !step_ok {
            // Conservative: discard the (unverifiable) strengthening and proceed on
            // the pre-vivify formula. Model-preserving either way, so no verdict change.
            return simplified.clone();
        }
    }
    stats.backend.push((
        "vivify_clauses_strengthened".to_owned(),
        usize_to_f64(outcome.stats.clauses_strengthened),
    ));
    stats.backend.push((
        "vivify_literals_removed".to_owned(),
        usize_to_f64(outcome.stats.literals_removed),
    ));
    stats.backend.push((
        "vivify_clauses_removed".to_owned(),
        usize_to_f64(outcome.stats.clauses_removed),
    ));
    outcome.formula
}

/// Runs subsumption, optional clause vivification, then bounded variable
/// elimination on `formula`, recording what each pass removed in `stats`.
/// Subsumption and vivification are model-preserving; `BVE` is equisatisfiable and
/// pairs the reduced formula with a reconstruction stack. All passes stop
/// scheduling new work once `deadline` passes. Vivification runs only when
/// `config.cnf_vivify` is set.
fn inprocess(
    config: &SolverConfig,
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
    // Optional clause vivification between subsumption and BVE. Vivify is
    // model-preserving (same satisfying assignments, same `variable_count`, no
    // reconstruction trail), so its output feeds BVE in place of `simplified` and
    // the model-lift stack is unchanged. See `maybe_vivify`.
    let vivified = maybe_vivify(config, &simplified, deadline, stats);
    let bve = eliminate_variables_within(&vivified, BveOptions::default(), deadline);

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
    // Compact: BVE removes clauses/variables but never renumbers, so its reduced
    // formula still reports the original (wide) `variable_count`. Densely
    // renumber the live variables so the var-bound admission gate sees the real
    // (much lower) count. Compaction is a pure renumbering bijection on the live
    // set — it cannot change sat/unsat — and a compacted `sat` model is lifted
    // back up by `compaction.expand` before the BVE `reconstruction.extend`.
    let bve_variable_count = bve.formula.variable_count();
    let (compacted, compaction) = compact(&bve.formula);
    let compacted_variable_count = compacted.variable_count();

    stats.backend.push((
        "cnf_compaction_variables_before".to_owned(),
        usize_to_f64(bve_variable_count),
    ));
    stats.backend.push((
        "cnf_compaction_variables_after".to_owned(),
        usize_to_f64(compacted_variable_count),
    ));
    stats.backend.push((
        "cnf_compaction_variables_dropped".to_owned(),
        usize_to_f64(bve_variable_count.saturating_sub(compacted_variable_count)),
    ));
    // The clause count is unchanged by compaction (renumbering only), so the
    // submitted clause count is the BVE-reduced count.
    stats.backend.push((
        "cnf_clauses_solved".to_owned(),
        usize_to_f64(compacted.clauses().len()),
    ));
    stats.backend.push((
        "cnf_variables_solved".to_owned(),
        usize_to_f64(compacted_variable_count),
    ));

    Inprocessed {
        formula: compacted,
        compaction,
        reconstruction: bve.reconstruction,
    }
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
            let lift_start = Instant::now();
            let aig_values = encoding
                .aig_node_values_from_assignment(lowering.aig(), &cnf_assignment)
                .map_err(|error| map_cnf_error(&error))?;
            let assignment = lowering
                .assignment_from_aig_values(&aig_values)
                .map_err(map_lower_error)?;
            let model = complete_model(arena, &assignment);
            // Replay is the soundness gate: a sat model is accepted only if it
            // satisfies the original query. If replay can't *evaluate* (e.g. an
            // arithmetic overflow in the trust-anchor evaluator), we cannot
            // confirm the model — the sound answer is a graceful `Unknown`, never
            // an accepted (unverified) sat and never a crash.
            if let Some(reason) = replay_model(arena, assertions, replay_plan, &model)? {
                return Ok(CheckResult::Unknown(reason));
            }
            stats.model_lift = lift_start.elapsed();
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

/// Dispatches the primary SAT search: the deadline-bounded native CDCL core when
/// `config.native_cdcl` is set — or when `config.prove_unsat` is set, since the
/// native core is the proof-producing engine and its inline proof lets a checked
/// `unsat` fall out of a **single** solve. Otherwise the default `rustsat-batsat`
/// adapter. Both produce a [`SatResult`] consumed identically downstream.
///
/// When the native core runs for `prove_unsat`, `check_proof` is set so any
/// `unsat` it returns is verified inline (`SatProofStatus::Checked`) and the
/// downstream re-derivation is skipped (see the call site in
/// [`SatBvBackend::check_with_replay`]). batsat stays the default engine when
/// `prove_unsat` is not requested.
fn primary_sat_search(
    config: &SolverConfig,
    formula: &CnfFormula,
    deadline: Option<Instant>,
    sat_timeout: Option<Duration>,
    stats: &mut SolveStats,
) -> Result<SatResult, SolverError> {
    if config.native_cdcl || config.prove_unsat {
        let outcome =
            solve_with_native_cdcl(formula, deadline, config.resource_limit, config.prove_unsat);
        if let Some(duration) = outcome.proof_replay {
            push_duration_ms(stats, "unsat_proof_replay_ms", duration);
        }
        Ok(outcome.result)
    } else {
        solve_with_rustsat_batsat_limits(formula, sat_timeout, config.resource_limit)
            .map_err(|error| map_sat_error(&error))
    }
}

/// Runs the in-tree proof-producing CDCL core as the primary SAT search,
/// mapping its [`ProofSolveOutcome`] onto the [`SatResult`] the batsat path
/// produces so the rest of the pipeline is unchanged.
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
}

fn solve_with_native_cdcl(
    formula: &CnfFormula,
    deadline: Option<Instant>,
    resource_limit: Option<u64>,
    check_proof: bool,
) -> NativeCdclOutcome {
    let max_conflicts = resource_limit.map_or(DEFAULT_PROOF_SAT_CONFLICT_LIMIT, |limit| {
        usize::try_from(limit).unwrap_or(usize::MAX)
    });
    match solve_with_drat_proof_with_limits(formula, deadline, max_conflicts) {
        ProofSolveOutcome::Sat(assignment) => NativeCdclOutcome {
            result: SatResult::Sat(assignment),
            proof_replay: None,
        },
        ProofSolveOutcome::Unsat(proof) => {
            if !check_proof {
                return NativeCdclOutcome {
                    result: SatResult::Unsat(SatUnsatEvidence {
                        proof: SatProofStatus::Unchecked,
                        failed_assumptions: Vec::new(),
                    }),
                    proof_replay: None,
                };
            }
            // Verify the inline proof in place. Only a checked proof yields an
            // accepted `unsat`; anything else is a conservative downgrade — we
            // never pass off an unverified `unsat` as checked.
            let replay_start = Instant::now();
            let checked = check_drat(formula, &proof);
            let proof_replay = Some(replay_start.elapsed());
            let result = match checked {
                Ok(true) => SatResult::Unsat(SatUnsatEvidence {
                    proof: SatProofStatus::Checked,
                    failed_assumptions: Vec::new(),
                }),
                Ok(false) => SatResult::Unknown(SatUnknownReason {
                    detail: "native unsat proof failed to check: did not derive the empty clause"
                        .to_owned(),
                }),
                Err(error) => SatResult::Unknown(SatUnknownReason {
                    detail: format!("native unsat proof failed to check: {error}"),
                }),
            };
            NativeCdclOutcome {
                result,
                proof_replay,
            }
        }
        ProofSolveOutcome::ResourceOut => NativeCdclOutcome {
            result: SatResult::Unknown(SatUnknownReason {
                detail: "native CDCL core exhausted its conflict budget".to_owned(),
            }),
            proof_replay: None,
        },
        ProofSolveOutcome::Interrupted => NativeCdclOutcome {
            result: SatResult::Unknown(SatUnknownReason {
                detail: "native CDCL core timeout".to_owned(),
            }),
            proof_replay: None,
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
    // The reduced formula is equisatisfiable with the original, so an independent
    // UNSAT proof of it certifies the original is UNSAT. Fail CLOSED for the
    // batsat path.
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
        let result = solve_with_native_cdcl(&f, None, None, true);
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
        let result = solve_with_native_cdcl(&f, None, None, false);
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
        let outcome = ensure_unsat_proof_checked(true, &checked, &f, &mut stats)
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
        let outcome = ensure_unsat_proof_checked(true, &unchecked, &f, &mut stats)
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
}
