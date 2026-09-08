//! Typed view of the pure-Rust bit-blasting pipeline stages.
//!
//! The backend records per-stage counters in the untyped
//! [`SolveStats::backend`] list so [`SolveStats`] can stay backend-agnostic.
//! [`BvLayerStats`] lifts those counters into a named, typed structure so the
//! lowering/optimization pipeline is a first-class thing callers can measure,
//! compare, and regression-test rather than a bag of strings.

use std::time::Duration;

use axeyum_bv::{BitLoweringMemoRepresentation, RangeDemandDecision};

use crate::backend::SolveStats;

/// The named stages of the `sat-bv` pipeline for one check.
///
/// Durations cover bit-blasting (term → AIG), CNF encoding (AIG → CNF), optional
/// CNF inprocessing, SAT solving, and model lifting (assignment → Axeyum model).
/// Sizes describe the AIG and CNF the encoder produced.
#[derive(Debug, Clone, Copy, PartialEq)]
#[allow(clippy::struct_excessive_bools)] // Flat typed view of independent backend facts.
pub struct BvLayerStats {
    /// Time lowering terms to the AIG.
    pub bit_blast: Duration,
    /// Time encoding the AIG to CNF.
    pub cnf_encode: Duration,
    /// Time simplifying the CNF before search (zero when disabled or skipped).
    pub cnf_inprocess: Duration,
    /// Time inside the SAT adapter.
    pub solve: Duration,
    /// Time lifting a satisfying assignment into an Axeyum model (AIG
    /// values -> lowering assignment -> `complete_model`) — NOT including
    /// [`Self::model_replay`], which is timed separately (see that field's
    /// docs for why this split exists).
    pub model_lift: Duration,
    /// Time replaying the accepted model against the original assertions
    /// (the soundness gate every `sat` from this backend passes before it is
    /// returned). `Duration::ZERO` when the check did not decide `Sat` (no
    /// replay to time), matching [`Self::model_lift`]'s convention. Split out
    /// of `model_lift` 2026-09-07 (docs/research/12-performance/
    /// instrument-coverage-2026-09-07.md): before the split, `model_lift`'s
    /// `Instant` was read AFTER the replay call returned, so a field named
    /// "lift" silently included the replay-check cost too. `Duration::ZERO`
    /// also for a `SolveStats` produced before this field existed (an older
    /// serialized snapshot, or a future backend that never sets
    /// `model_replay_ms`) — [`Self::from_solve_stats`] defaults an absent
    /// counter to zero, same as every other optional field here.
    pub model_replay: Duration,
    /// Symbolic AIG inputs (bit-level free variables).
    pub aig_inputs: u64,
    /// AIG nodes after lowering.
    pub aig_nodes: u64,
    /// Primitive AIG AND construction requests.
    pub aig_and_requests: u64,
    /// Primitive AND requests removed by constants/identities/complements.
    pub aig_and_trivial_simplifications: u64,
    /// Primitive AND requests removed by absorption/consensus.
    pub aig_and_absorption_simplifications: u64,
    /// Primitive AND requests served by the structural unique table.
    pub aig_and_structural_hash_hits: u64,
    /// Primitive AND requests that allocated a new node.
    pub aig_and_nodes_created: u64,
    /// Time spent computing conservative structural bit demand (nested in bit blast).
    pub bit_demand_analysis: Duration,
    /// Whether structural request/available/demanded statistics were computed.
    pub bit_demand_profile_complete: bool,
    /// Whether demand-driven lowering, rather than observational profiling,
    /// controlled which term and symbol bits were materialized.
    pub bit_demand_lowering_applied: bool,
    /// ADR-0158 admission/fallback result.
    pub range_demand_decision: RangeDemandDecision,
    /// Time spent in ADR-0158's cheap admission screen.
    pub range_demand_admission: Duration,
    /// Bits the admission screen conservatively estimated it could avoid.
    pub range_demand_estimated_bits_avoided: u64,
    /// Configured deterministic exact-analysis work ceiling.
    pub range_demand_analysis_work_budget: u64,
    /// Deterministic exact-analysis work consumed.
    pub range_demand_analysis_work: u64,
    /// Overlapping or adjacent range unions.
    pub range_demand_merges: u64,
    /// Fragmented terms conservatively promoted to full demand.
    pub range_demand_promotions: u64,
    /// Term-bit demand requests before unioning.
    pub term_bit_requests: u64,
    /// Bits in reachable terms before demand reduction.
    pub term_bits_available: u64,
    /// Unique term bits required by conservative structural propagation.
    pub term_bits_demanded: u64,
    /// Term bits materialized by the current lowerer.
    pub term_bits_lowered: u64,
    /// Whether private full-lowering memo accounting is complete.
    pub bit_lowering_memo_profile_complete: bool,
    /// Active private full-lowering memo representation.
    pub bit_lowering_memo_representation: BitLoweringMemoRepresentation,
    /// Terms in the source arena, including unreachable terms.
    pub bit_lowering_memo_source_terms: u64,
    /// Addressable memo slots/nodes.
    pub bit_lowering_memo_slots: u64,
    /// Completed terms retained in the memo.
    pub bit_lowering_memo_occupied: u64,
    /// Full-lowering memo lookups.
    pub bit_lowering_memo_lookups: u64,
    /// Memo lookup hits.
    pub bit_lowering_memo_hits: u64,
    /// Completed term vectors written.
    pub bit_lowering_memo_writes: u64,
    /// Initialized literal payload length.
    pub bit_lowering_memo_payload_literals: u64,
    /// Allocated literal payload capacity.
    pub bit_lowering_memo_payload_capacity_literals: u64,
    /// Conservative logical representation-header bytes.
    pub bit_lowering_memo_logical_header_bytes: u64,
    /// Initialized literal payload bytes.
    pub bit_lowering_memo_logical_payload_bytes: u64,
    /// Logical header plus initialized-payload bytes.
    pub bit_lowering_memo_logical_total_bytes: u64,
    /// Allocated-capacity bytes for literal payloads.
    pub bit_lowering_memo_payload_capacity_bytes: u64,
    /// Literal bits returned across all requested roots.
    pub bit_lowering_memo_root_bits: u64,
    /// Root bits required by the requested root sorts.
    pub bit_lowering_memo_expected_root_bits: u64,
    /// Whether representation-neutral accounting identities hold.
    pub bit_lowering_memo_invariants_hold: bool,
    /// Deterministic FNV-1a digest of the ordered AIG and lowering lift maps.
    pub bit_lowering_structure_digest: u64,
    /// Deterministic FNV-1a digest of the ordered CNF and CNF lift maps.
    pub cnf_structure_digest: u64,
    /// Symbol-bit demand requests before unioning.
    pub symbol_bit_requests: u64,
    /// Bits in reachable symbols before demand reduction.
    pub symbol_bits_available: u64,
    /// Unique symbol bits required by conservative structural propagation.
    pub symbol_bits_demanded: u64,
    /// Symbol bits materialized as AIG inputs by the current lowerer.
    pub symbol_bits_lowered: u64,
    /// CNF variables submitted to the SAT adapter.
    pub cnf_variables: u64,
    /// CNF clauses submitted to the SAT adapter.
    pub cnf_clauses: u64,
    /// CNF time spent planning reachability, polarity, and compound gates.
    pub cnf_planning: Duration,
    /// CNF time spent allocating retained node variables.
    pub cnf_variable_allocation: Duration,
    /// CNF time spent emitting non-root gate clauses.
    pub cnf_gate_encoding: Duration,
    /// CNF time spent encoding/asserting roots.
    pub cnf_root_encoding: Duration,
    /// Reachable AIG nodes considered by the sparse encoder.
    pub cnf_reachable_nodes: u64,
    /// Private helper nodes subsumed by recognized compound gates.
    pub cnf_skipped_helper_nodes: u64,
    /// Assertion-only roots encoded without dedicated variables.
    pub cnf_direct_root_nodes: u64,
    /// Recognized XOR gates.
    pub cnf_xor_gates: u64,
    /// Recognized complemented ITE/mux gates.
    pub cnf_not_ite_gates: u64,
    /// Recognized complemented-AND gates.
    pub cnf_not_and_gates: u64,
    /// Recognized private AND trees.
    pub cnf_and_tree_gates: u64,
    /// Remaining primitive binary AND gates.
    pub cnf_binary_and_gates: u64,
    /// Clause attempts before filtering.
    pub cnf_clause_attempts: u64,
    /// Tautological clause attempts skipped.
    pub cnf_tautological_clauses_skipped: u64,
    /// Duplicate canonical clauses skipped.
    pub cnf_duplicate_clauses_skipped: u64,
    /// Whether detailed CNF construction attribution is complete.
    pub cnf_construction_profile_complete: bool,
    /// Literals declared by clause-emission attempts.
    pub cnf_declared_clause_literals: u64,
    /// Literals visited before canonicalization returned or completed.
    pub cnf_visited_clause_literals: u64,
    /// Constant-false literals discarded.
    pub cnf_false_constants_dropped: u64,
    /// Repeated concrete literals discarded.
    pub cnf_repeated_literals_dropped: u64,
    /// Tautologies caused by constant-true literals.
    pub cnf_true_constant_tautologies: u64,
    /// Tautologies caused by complementary literals.
    pub cnf_complementary_literal_tautologies: u64,
    /// Literals across canonical non-tautological attempts.
    pub cnf_canonical_literals: u64,
    /// Canonical empty-clause attempts.
    pub cnf_canonical_empty_clauses: u64,
    /// Canonical unit-clause attempts.
    pub cnf_canonical_unit_clauses: u64,
    /// Canonical binary-clause attempts.
    pub cnf_canonical_binary_clauses: u64,
    /// Canonical ternary-clause attempts.
    pub cnf_canonical_ternary_clauses: u64,
    /// Canonical attempts containing four or more literals.
    pub cnf_canonical_larger_clauses: u64,
    /// Vacant primary fingerprint probes.
    pub cnf_primary_vacant_probes: u64,
    /// Occupied primary fingerprint probes.
    pub cnf_primary_occupied_probes: u64,
    /// Exact duplicates found in primary slots.
    pub cnf_primary_exact_duplicates: u64,
    /// Exact comparisons against collision-bucket entries.
    pub cnf_collision_bucket_comparisons: u64,
    /// Exact duplicates found in collision buckets.
    pub cnf_collision_exact_duplicates: u64,
    /// Distinct equal-fingerprint clauses inserted into collision buckets.
    pub cnf_collision_inserts: u64,
}

impl BvLayerStats {
    /// Extracts the pure-Rust pipeline stages from `stats`.
    ///
    /// Returns `None` when `stats` was not produced by the `sat-bv` backend
    /// (its identifying counters, `aig_nodes` and `cnf_variables`, are absent),
    /// so this never silently fabricates numbers for another backend.
    #[allow(clippy::too_many_lines)] // Flat typed telemetry contract; keep keys adjacent.
    pub fn from_solve_stats(stats: &SolveStats) -> Option<Self> {
        let aig_nodes = lookup(stats, "aig_nodes")?;
        let cnf_variables = lookup(stats, "cnf_variables")?;
        Some(Self {
            bit_blast: lookup(stats, "bit_blast_ms").map_or(Duration::ZERO, ms_to_duration),
            cnf_encode: lookup(stats, "cnf_encode_ms").map_or(Duration::ZERO, ms_to_duration),
            cnf_inprocess: lookup(stats, "inprocess_ms").map_or(Duration::ZERO, ms_to_duration),
            solve: stats.solve,
            model_lift: stats.model_lift,
            model_replay: lookup(stats, "model_replay_ms").map_or(Duration::ZERO, ms_to_duration),
            aig_inputs: lookup(stats, "aig_inputs").map_or(0, count_to_u64),
            aig_nodes: count_to_u64(aig_nodes),
            aig_and_requests: lookup(stats, "aig_and_requests").map_or(0, count_to_u64),
            aig_and_trivial_simplifications: lookup(stats, "aig_and_trivial_simplifications")
                .map_or(0, count_to_u64),
            aig_and_absorption_simplifications: lookup(stats, "aig_and_absorption_simplifications")
                .map_or(0, count_to_u64),
            aig_and_structural_hash_hits: lookup(stats, "aig_and_structural_hash_hits")
                .map_or(0, count_to_u64),
            aig_and_nodes_created: lookup(stats, "aig_and_nodes_created").map_or(0, count_to_u64),
            bit_demand_analysis: lookup(stats, "bit_demand_analysis_ms")
                .map_or(Duration::ZERO, ms_to_duration),
            bit_demand_profile_complete: lookup(stats, "bit_demand_profile_complete")
                .is_some_and(|value| value >= 1.0),
            bit_demand_lowering_applied: lookup(stats, "bit_demand_lowering_applied")
                .is_some_and(|value| value >= 1.0),
            range_demand_decision: RangeDemandDecision::from_code(
                lookup(stats, "range_demand_decision").map_or(0, count_to_u64),
            ),
            range_demand_admission: lookup(stats, "range_demand_admission_ms")
                .map_or(Duration::ZERO, ms_to_duration),
            range_demand_estimated_bits_avoided: lookup(
                stats,
                "range_demand_estimated_bits_avoided",
            )
            .map_or(0, count_to_u64),
            range_demand_analysis_work_budget: lookup(stats, "range_demand_analysis_work_budget")
                .map_or(0, count_to_u64),
            range_demand_analysis_work: lookup(stats, "range_demand_analysis_work")
                .map_or(0, count_to_u64),
            range_demand_merges: lookup(stats, "range_demand_merges").map_or(0, count_to_u64),
            range_demand_promotions: lookup(stats, "range_demand_promotions")
                .map_or(0, count_to_u64),
            term_bit_requests: lookup(stats, "term_bit_requests").map_or(0, count_to_u64),
            term_bits_available: lookup(stats, "term_bits_available").map_or(0, count_to_u64),
            term_bits_demanded: lookup(stats, "term_bits_demanded").map_or(0, count_to_u64),
            term_bits_lowered: lookup(stats, "term_bits_lowered").map_or(0, count_to_u64),
            bit_lowering_memo_profile_complete: lookup(stats, "bit_lowering_memo_profile_complete")
                .is_some_and(|value| value >= 1.0),
            bit_lowering_memo_representation: BitLoweringMemoRepresentation::from_code(
                lookup(stats, "bit_lowering_memo_representation").map_or(0, count_to_u64),
            ),
            bit_lowering_memo_source_terms: lookup(stats, "bit_lowering_memo_source_terms")
                .map_or(0, count_to_u64),
            bit_lowering_memo_slots: lookup(stats, "bit_lowering_memo_slots")
                .map_or(0, count_to_u64),
            bit_lowering_memo_occupied: lookup(stats, "bit_lowering_memo_occupied")
                .map_or(0, count_to_u64),
            bit_lowering_memo_lookups: lookup(stats, "bit_lowering_memo_lookups")
                .map_or(0, count_to_u64),
            bit_lowering_memo_hits: lookup(stats, "bit_lowering_memo_hits").map_or(0, count_to_u64),
            bit_lowering_memo_writes: lookup(stats, "bit_lowering_memo_writes")
                .map_or(0, count_to_u64),
            bit_lowering_memo_payload_literals: lookup(stats, "bit_lowering_memo_payload_literals")
                .map_or(0, count_to_u64),
            bit_lowering_memo_payload_capacity_literals: lookup(
                stats,
                "bit_lowering_memo_payload_capacity_literals",
            )
            .map_or(0, count_to_u64),
            bit_lowering_memo_logical_header_bytes: lookup(
                stats,
                "bit_lowering_memo_logical_header_bytes",
            )
            .map_or(0, count_to_u64),
            bit_lowering_memo_logical_payload_bytes: lookup(
                stats,
                "bit_lowering_memo_logical_payload_bytes",
            )
            .map_or(0, count_to_u64),
            bit_lowering_memo_logical_total_bytes: lookup(
                stats,
                "bit_lowering_memo_logical_total_bytes",
            )
            .map_or(0, count_to_u64),
            bit_lowering_memo_payload_capacity_bytes: lookup(
                stats,
                "bit_lowering_memo_payload_capacity_bytes",
            )
            .map_or(0, count_to_u64),
            bit_lowering_memo_root_bits: lookup(stats, "bit_lowering_memo_root_bits")
                .map_or(0, count_to_u64),
            bit_lowering_memo_expected_root_bits: lookup(
                stats,
                "bit_lowering_memo_expected_root_bits",
            )
            .map_or(0, count_to_u64),
            bit_lowering_memo_invariants_hold: lookup(stats, "bit_lowering_memo_invariants_hold")
                .is_some_and(|value| value >= 1.0),
            bit_lowering_structure_digest: lookup_digest(stats, "bit_lowering_structure_digest"),
            cnf_structure_digest: lookup_digest(stats, "cnf_structure_digest"),
            symbol_bit_requests: lookup(stats, "symbol_bit_requests").map_or(0, count_to_u64),
            symbol_bits_available: lookup(stats, "symbol_bits_available").map_or(0, count_to_u64),
            symbol_bits_demanded: lookup(stats, "symbol_bits_demanded").map_or(0, count_to_u64),
            symbol_bits_lowered: lookup(stats, "symbol_bits_lowered").map_or(0, count_to_u64),
            cnf_variables: count_to_u64(cnf_variables),
            cnf_clauses: lookup(stats, "cnf_clauses").map_or(0, count_to_u64),
            cnf_planning: lookup(stats, "cnf_plan_ms").map_or(Duration::ZERO, ms_to_duration),
            cnf_variable_allocation: lookup(stats, "cnf_allocate_ms")
                .map_or(Duration::ZERO, ms_to_duration),
            cnf_gate_encoding: lookup(stats, "cnf_gate_encode_ms")
                .map_or(Duration::ZERO, ms_to_duration),
            cnf_root_encoding: lookup(stats, "cnf_root_encode_ms")
                .map_or(Duration::ZERO, ms_to_duration),
            cnf_reachable_nodes: lookup(stats, "cnf_reachable_nodes").map_or(0, count_to_u64),
            cnf_skipped_helper_nodes: lookup(stats, "cnf_skipped_helper_nodes")
                .map_or(0, count_to_u64),
            cnf_direct_root_nodes: lookup(stats, "cnf_direct_root_nodes").map_or(0, count_to_u64),
            cnf_xor_gates: lookup(stats, "cnf_xor_gates").map_or(0, count_to_u64),
            cnf_not_ite_gates: lookup(stats, "cnf_not_ite_gates").map_or(0, count_to_u64),
            cnf_not_and_gates: lookup(stats, "cnf_not_and_gates").map_or(0, count_to_u64),
            cnf_and_tree_gates: lookup(stats, "cnf_and_tree_gates").map_or(0, count_to_u64),
            cnf_binary_and_gates: lookup(stats, "cnf_binary_and_gates").map_or(0, count_to_u64),
            cnf_clause_attempts: lookup(stats, "cnf_clause_attempts").map_or(0, count_to_u64),
            cnf_tautological_clauses_skipped: lookup(stats, "cnf_tautological_clauses_skipped")
                .map_or(0, count_to_u64),
            cnf_duplicate_clauses_skipped: lookup(stats, "cnf_duplicate_clauses_skipped")
                .map_or(0, count_to_u64),
            cnf_construction_profile_complete: lookup(stats, "cnf_construction_profile_complete")
                .is_some_and(|value| value >= 1.0),
            cnf_declared_clause_literals: lookup(stats, "cnf_declared_clause_literals")
                .map_or(0, count_to_u64),
            cnf_visited_clause_literals: lookup(stats, "cnf_visited_clause_literals")
                .map_or(0, count_to_u64),
            cnf_false_constants_dropped: lookup(stats, "cnf_false_constants_dropped")
                .map_or(0, count_to_u64),
            cnf_repeated_literals_dropped: lookup(stats, "cnf_repeated_literals_dropped")
                .map_or(0, count_to_u64),
            cnf_true_constant_tautologies: lookup(stats, "cnf_true_constant_tautologies")
                .map_or(0, count_to_u64),
            cnf_complementary_literal_tautologies: lookup(
                stats,
                "cnf_complementary_literal_tautologies",
            )
            .map_or(0, count_to_u64),
            cnf_canonical_literals: lookup(stats, "cnf_canonical_literals").map_or(0, count_to_u64),
            cnf_canonical_empty_clauses: lookup(stats, "cnf_canonical_empty_clauses")
                .map_or(0, count_to_u64),
            cnf_canonical_unit_clauses: lookup(stats, "cnf_canonical_unit_clauses")
                .map_or(0, count_to_u64),
            cnf_canonical_binary_clauses: lookup(stats, "cnf_canonical_binary_clauses")
                .map_or(0, count_to_u64),
            cnf_canonical_ternary_clauses: lookup(stats, "cnf_canonical_ternary_clauses")
                .map_or(0, count_to_u64),
            cnf_canonical_larger_clauses: lookup(stats, "cnf_canonical_larger_clauses")
                .map_or(0, count_to_u64),
            cnf_primary_vacant_probes: lookup(stats, "cnf_primary_vacant_probes")
                .map_or(0, count_to_u64),
            cnf_primary_occupied_probes: lookup(stats, "cnf_primary_occupied_probes")
                .map_or(0, count_to_u64),
            cnf_primary_exact_duplicates: lookup(stats, "cnf_primary_exact_duplicates")
                .map_or(0, count_to_u64),
            cnf_collision_bucket_comparisons: lookup(stats, "cnf_collision_bucket_comparisons")
                .map_or(0, count_to_u64),
            cnf_collision_exact_duplicates: lookup(stats, "cnf_collision_exact_duplicates")
                .map_or(0, count_to_u64),
            cnf_collision_inserts: lookup(stats, "cnf_collision_inserts").map_or(0, count_to_u64),
        })
    }

    /// Total wall-clock time across all pipeline stages.
    ///
    /// Deliberately the six top-level stage fields ONLY —
    /// [`Self::bit_demand_analysis`] and `range_demand_admission` are
    /// documented as nested inside [`Self::bit_blast`] (they are sub-timings
    /// taken *during* the same lowering call `bit_blast` wraps), so adding
    /// them here would double-count exactly the way `theory_assert_ms` did
    /// inside `boolean_propagate_ms` for the generic CDCL(T) driver (see
    /// `crate::theories::cdclt_diagnostics::TheoryLayerStats` and
    /// docs/research/12-performance/bench-divisions-2026-09-07.md's
    /// "Methodology correction"). This total is the non-double-counting
    /// answer; a caller that also wants the nested breakdown reads
    /// [`Self::bit_demand_analysis`] separately, never summed in.
    pub fn total(&self) -> Duration {
        self.bit_blast
            + self.cnf_encode
            + self.cnf_inprocess
            + self.solve
            + self.model_lift
            + self.model_replay
    }

    /// Clauses per CNF variable, a coarse encoding-density indicator
    /// (`0.0` when there are no variables).
    pub fn clause_density(&self) -> f64 {
        if self.cnf_variables == 0 {
            0.0
        } else {
            u64_to_f64(self.cnf_clauses) / u64_to_f64(self.cnf_variables)
        }
    }
}

std::thread_local! {
    /// Whether the *next* [`SatBvBackend`](crate::sat_bv_backend::SatBvBackend)
    /// check on this thread should publish its [`BvLayerStats`] to
    /// [`LAST_BV_LAYER_STATS`]. Scoped as a thread-local opt-in flag for the
    /// same reason `cdclt::COLLECT_LAYER_STATS` is: one knob at the top of a
    /// solve, read at the single publish point in `SatBvBackend`'s
    /// `SolverBackend::check`/`check_query`, rather than a parameter threaded
    /// through the ~10 internal `SatBvBackend::new()` call sites.
    ///
    /// Off by default costs nothing extra: the underlying `SolveStats`
    /// durations this reads (`bit_blast_ms`, `cnf_encode_ms`, `solve`,
    /// `model_lift`, `model_replay_ms`, …) are computed UNCONDITIONALLY by
    /// `SatBvBackend` regardless of this flag — they are ordinary `Instant`
    /// reads already on the hot path, not new clock reads this flag adds.
    /// What the flag gates is only the `Option<BvLayerStats>` clone into the
    /// thread-local below, which is skipped entirely when collection is off.
    static COLLECT_BV_LAYER_STATS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The [`BvLayerStats`] published by the most recently completed
    /// `SatBvBackend` check on this thread while collection was enabled.
    /// `None` until collection has been enabled and a `sat-bv` check has
    /// completed. "Last call wins": a solve that constructs `SatBvBackend`
    /// more than once (e.g. a shared-guard split, a CEGAR abstraction loop)
    /// leaves the FINAL check's stats here, matching
    /// `cdclt::LAST_THEORY_LAYER_STATS`'s same convention for a solve that
    /// runs more than one `CdclT` search.
    static LAST_BV_LAYER_STATS: std::cell::Cell<Option<BvLayerStats>> =
        const { std::cell::Cell::new(None) };
}

/// Enables [`BvLayerStats`] collection for every `SatBvBackend` check run on
/// this thread for the lifetime of the returned guard, restoring the
/// previous setting on drop (so nested/recursive solves compose correctly).
/// Off by default: constructing no guard means no extra work beyond what
/// `SatBvBackend` already computes unconditionally (see
/// [`COLLECT_BV_LAYER_STATS`]'s docs).
///
/// ```ignore
/// let _guard = axeyum_solver::BvLayerStatsGuard::enable();
/// let _ = axeyum_solver::solve_smtlib(text, &config);
/// let stats = axeyum_solver::last_bv_layer_stats(); // Some(..) if `sat-bv` ran
/// ```
pub struct BvLayerStatsGuard(bool);

impl BvLayerStatsGuard {
    /// Enables collection for the lifetime of the returned guard.
    #[must_use]
    pub fn enable() -> Self {
        BvLayerStatsGuard(COLLECT_BV_LAYER_STATS.with(|c| c.replace(true)))
    }
}

impl Drop for BvLayerStatsGuard {
    fn drop(&mut self) {
        COLLECT_BV_LAYER_STATS.with(|c| c.set(self.0));
    }
}

/// The [`BvLayerStats`] published by the most recently completed `sat-bv`
/// check on this thread while a [`BvLayerStatsGuard`] was active. `None` if
/// collection was never enabled, or no `SatBvBackend` check has completed yet
/// on this thread.
#[must_use]
pub fn last_bv_layer_stats() -> Option<BvLayerStats> {
    LAST_BV_LAYER_STATS.with(std::cell::Cell::get)
}

/// Publishes `stats` (if `sat-bv`-shaped) to [`LAST_BV_LAYER_STATS`] when
/// collection is enabled on this thread; a silent no-op otherwise. Called
/// from `SatBvBackend`'s `SolverBackend::check`/`check_query` after every
/// check, so this is the single publish point regardless of which of
/// `SatBvBackend`'s many internal construction sites ran.
pub(crate) fn publish_bv_layer_stats(stats: &SolveStats) {
    if COLLECT_BV_LAYER_STATS.with(std::cell::Cell::get) {
        LAST_BV_LAYER_STATS.with(|c| c.set(BvLayerStats::from_solve_stats(stats)));
    }
}

fn lookup(stats: &SolveStats, key: &str) -> Option<f64> {
    stats
        .backend
        .iter()
        .find(|(name, _)| name == key)
        .map(|(_, value)| *value)
}

fn lookup_digest(stats: &SolveStats, key: &str) -> u64 {
    let high = lookup(stats, &format!("{key}_hi")).map_or(0, count_to_u64);
    let low = lookup(stats, &format!("{key}_lo")).map_or(0, count_to_u64);
    (high << 32) | (low & u64::from(u32::MAX))
}

fn ms_to_duration(milliseconds: f64) -> Duration {
    Duration::from_secs_f64((milliseconds / 1000.0).max(0.0))
}

// Backend counters are small non-negative integers stored as f64; the round
// recovers the original count exactly within the f64 integer-exact range.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn count_to_u64(value: f64) -> u64 {
    value.round().max(0.0) as u64
}

#[allow(clippy::cast_precision_loss)]
fn u64_to_f64(value: u64) -> f64 {
    value as f64
}

/// Named stage/counter attribution for a generic CDCL(T) theory-route search
/// (`crate::cdclt::CdclT`) — the arithmetic/EUF/string/combined-theory
/// counterpart to [`BvLayerStats`] for the pure bit-blast pipeline.
///
/// This is what the 2026-08-21 linear-arithmetic diagnosis had to reconstruct
/// by hand from per-file TSVs (classifying ~800 files because no instrument
/// said where a 24 s budget went): time in Boolean unit propagation vs. theory
/// `assert`/`propagate` vs. conflict analysis, plus the search's own decision
/// and restart counters.
///
/// # Collection is opt-in and off by default
///
/// A `CdclT` search reads no extra clock beyond its existing deadline check
/// unless collection was enabled for the current thread (see
/// `crate::theories::cdclt_diagnostics::TheoryLayerStatsGuard::enable`); a
/// disabled `CdclT` leaves every field at its `Default` (all-zero) value.
/// Times are read only at stage *boundaries* — around each
/// `TheorySolver::assert`/`propagate`/`push`/`pop` call, around one Boolean
/// unit-propagation pass, and around one 1-UIP conflict analysis — never per
/// trail literal, so enabling collection adds a bounded number of
/// `Instant::now()` pairs per search rather than one per assignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct TheoryLayerStats {
    /// Time inside Boolean unit propagation (`CdclT::unit_propagate`).
    pub boolean_propagate: Duration,
    /// Time inside `TheorySolver::assert` calls.
    pub theory_assert: Duration,
    /// Time inside `TheorySolver::propagate` calls.
    pub theory_propagate: Duration,
    /// Time inside `TheorySolver::push`/`pop` calls (combined: both are
    /// cheap bookkeeping for most theories, and the driver calls them in
    /// strict lockstep with decisions/backjumps).
    pub theory_push_pop: Duration,
    /// Time inside 1-UIP conflict analysis (`CdclT::analyze_conflict`).
    pub conflict_analysis: Duration,
    /// Time inside `TheorySolver::final_check` calls — the *complete* check at a
    /// total Boolean assignment (ADR-1701). Zero for a theory that keeps the
    /// trait default, whose `final_check` body does nothing.
    pub theory_final_check: Duration,
    /// Time inside `TheorySolver::explain` calls resolving deferred explanation
    /// handles (ADR-1701). Zero for a theory that never emits a handle.
    pub theory_explain: Duration,
    /// Completed `TheorySolver::final_check` calls, i.e. the number of times the
    /// Boolean search reached a total assignment of the active variables. `0`
    /// distinguishes "never got that far" from "got there and the theory
    /// accepted it".
    pub final_checks: u64,
    /// Conflicts where the falsified clause traces to a theory
    /// `assert`/`propagate` inconsistency, as opposed to a purely Boolean
    /// (input-clause) conflict.
    pub theory_conflicts: u64,
    /// Literals assigned by theory propagation (mirrors the driver's
    /// existing `theory_propagations` counter).
    pub theory_propagations: u64,
    /// Search decisions taken (`CdclT::pick_unassigned` choices, not implied
    /// assignments).
    pub decisions: u64,
    /// Asserting clauses 1-UIP conflict analysis produced. The denominator of
    /// the mean learned-clause length.
    pub learned_clauses: u64,
    /// Literals summed over those clauses **after** recursive minimization.
    /// `learned_literals / learned_clauses` is the mean learned length — the
    /// figure a clause minimizer is scored on.
    pub learned_literals: u64,
    /// The same sum taken **before** minimization, so a single run reports what
    /// minimization removed (`before - after`) instead of requiring two runs to
    /// be compared. Equal to `learned_literals` when nothing was removed.
    pub learned_literals_before_minimization: u64,
    /// Completed Luby restarts.
    pub restarts: u64,
    /// Simplex pivots performed by the driving theory, when it exposes a
    /// pivot count (`TheorySolver::engine_counters`, S4). `None` when the
    /// `TheorySolver` implementation in use keeps no feasibility engine —
    /// which is every theory but the LRA one today.
    pub simplex_pivots: Option<u64>,
    /// Feasibility checks the driving theory's engine completed, when it
    /// exposes them. Paired with `simplex_pivots` this is the pivots-per-check
    /// figure the warm-start work is scored on.
    pub simplex_checks: Option<u64>,
    /// Checks that discarded the basis and restarted from the pristine one.
    /// A nonzero value is the direct measurement of a *cold* engine.
    pub simplex_cold_restarts: Option<u64>,
    /// Rows the theory's bound-stack reconciliation retracted, summed over
    /// every check — how much of the previous state each check throws away.
    pub bound_retractions: Option<u64>,
    /// Rows that reconciliation (re-)asserted, summed over every check.
    pub bound_assertions: Option<u64>,
    /// Literals the theory offered to the driver's propagation queue. Distinct
    /// from `theory_propagations`, which counts the ones the driver *assigned*.
    pub theory_propagations_offered: Option<u64>,
    /// Rows of the driving theory's dense tableau, when it keeps one.
    pub simplex_rows: Option<u64>,
    /// Columns of that tableau. With `simplex_rows` this prices one pivot.
    pub simplex_columns: Option<u64>,
    /// Conflicts the theory found in its **cheap partial check** at `assert`
    /// time, before the complete decision. Under the ADR-1701 deferred split
    /// this and Boolean propagation are the only things that prune the search
    /// between two total assignments, so it is the counter that says whether a
    /// high `final_checks` has anything standing in its way.
    pub assert_partial_conflicts: Option<u64>,
    /// `final_check` calls that answered `Conflict`. `final_checks -
    /// final_check_conflicts` is how often the search reached a total
    /// assignment the theory *accepted* (or could not decide).
    pub final_check_conflicts: Option<u64>,
    /// Literals summed over those cores; divided by `final_check_conflicts`
    /// this is the mean refutation width, the figure that says whether a theory
    /// lemma excludes a region or close to one assignment.
    pub final_check_core_literals: Option<u64>,
    /// Complete-check refutations whose Farkas multipliers named no row, so the
    /// core widened to the whole asserted set — sound, maximally coarse.
    pub final_check_core_widenings: Option<u64>,
    /// Live constraint rows summed over every complete check: the denominator
    /// the mean core width is a fraction of.
    pub final_check_live_rows: Option<u64>,
    /// Propagation calls the driving theory served, and the atoms those calls
    /// examined. `bound_scan_atoms / bound_scan_calls` prices one propagation
    /// call in work rather than in wall time, which is what distinguishes a
    /// propagation that is expensive because it derives a lot from one that is
    /// expensive because it looks at everything and derives nothing.
    pub bound_scan_calls: Option<u64>,
    /// Atoms those calls examined; see `bound_scan_calls`.
    pub bound_scan_atoms: Option<u64>,
    /// Cells the simplex pivot actually wrote, summed over the engine's life.
    /// `pivot_cells_written / simplex_pivots` is the measured cost of one pivot
    /// in exact-rational multiply-adds; `simplex_rows × simplex_columns` is the
    /// dense worst case, and the ratio says how much sparsity the pivot already
    /// exploits and therefore how much a sparse representation could still win.
    pub pivot_cells_written: Option<u64>,
    /// Rows the pivot combined. With `pivot_cells_written` this separates "a
    /// pivot touches many rows" from "a pivot touches long rows".
    pub pivot_rows_combined: Option<u64>,
    /// Columns the entering-variable scan examined.
    pub entering_scan_cells: Option<u64>,
    /// Rows the leaving-variable scan examined — what a violated-basic priority
    /// heap would remove.
    pub leaving_scan_rows: Option<u64>,
    /// Nonzero tableau cells summed over `fill_samples` feasibility calls;
    /// divided by that, fill-in.
    pub fill_nnz_sum: Option<u64>,
    /// The denominator of `fill_nnz_sum`.
    pub fill_samples: Option<u64>,
    /// Feasibility calls that finished under the Bland fallback.
    pub bland_fallbacks: Option<u64>,
    /// Infeasibility outcomes that produced a verified Farkas certificate.
    pub farkas_certificates: Option<u64>,
    /// Farkas declines because the infeasible row's basic variable is not a
    /// slack; a decline widens the conflict core to the whole asserted set.
    pub farkas_declined_basic_not_slack: Option<u64>,
    /// Farkas declines because a nonbasic problem variable appears in the row.
    pub farkas_declined_nonbasic_problem_var: Option<u64>,
    /// Farkas declines because the candidate failed its own self-check.
    pub farkas_declined_self_check: Option<u64>,
}

impl TheoryLayerStats {
    /// Total wall-clock time across the named stages (excludes whatever time
    /// the search spends outside `assert`/`propagate`/`push`/`pop`/conflict
    /// analysis — bookkeeping like VSIDS bumps, trail maintenance, and
    /// decision selection itself).
    #[must_use]
    pub fn total(&self) -> Duration {
        self.boolean_propagate
            + self.theory_assert
            + self.theory_propagate
            + self.theory_push_pop
            + self.conflict_analysis
            + self.theory_final_check
            + self.theory_explain
    }
}
