//! Bit-vector lowering from Axeyum terms to AIG wires.
//!
//! This first Phase 4 lowering slice is intentionally small: constants,
//! symbols, Boolean connectives, bit-vector bitwise operators, structural BV
//! operators, and the first arithmetic/comparison/shift circuits. It records
//! explicit term-bit and symbol-input maps so later CNF and SAT layers can
//! lift assignments back to original terms instead of trusting the lowered
//! form.

use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
};

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use axeyum_aig::{Aig, AigInputId, AigLit, AigNode};
use axeyum_ir::{
    Assignment, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
    lsb_bits_to_value, value_to_lsb_bits,
};

/// Lowers one or more root terms into an AIG.
///
/// # Errors
///
/// Returns [`BitLowerError`] if a term uses an operator outside the initial
/// Phase 4 lowering subset, an assignment is missing during replay, or an
/// internal lowering invariant is violated.
pub fn lower_terms(arena: &TermArena, roots: &[TermId]) -> Result<BitLowering, BitLowerError> {
    LoweringBuilder::new(arena).lower_roots(roots, false)
}

/// Lowers roots with exact structural bit demand (ADR-0157).
///
/// Every root remains complete, but only demanded child bits are materialized
/// through extract, concat, extensions, pointwise Bool/BV operators, `ite`,
/// constant rotations, and bit reinterpretation. All other operators are
/// conservative barriers that retain the existing full-width lowering. The
/// returned term-bit map is therefore intentionally sparse, and omitted symbol
/// bits are completed deterministically with `false` during model lift.
///
/// This is an additive experimental entry point. [`lower_terms`] remains the
/// production default until the ADR-0157 real-corpus gate is accepted.
///
/// # Errors
///
/// Returns the same errors as [`lower_terms`].
pub fn lower_terms_demanded(
    arena: &TermArena,
    roots: &[TermId],
) -> Result<BitLowering, BitLowerError> {
    LoweringBuilder::new(arena).lower_demanded_roots(roots)
}

/// Lowers roots into an AIG and also computes the observational structural
/// bit-demand profile.
///
/// Profiling can be substantially more expensive than lowering. It does not
/// change the generated AIG or lift maps; use [`lower_terms`] for production
/// solving and this entry point only when demand diagnostics are required.
///
/// # Errors
///
/// Returns the same errors as [`lower_terms`].
pub fn lower_terms_profiled(
    arena: &TermArena,
    roots: &[TermId],
) -> Result<BitLowering, BitLowerError> {
    let mut builder = LoweringBuilder::new(arena);
    builder.profiling_enabled = true;
    builder.lower_roots(roots, true)
}

/// Lowers one or more root terms into an AIG while honoring an absolute
/// wall-clock deadline.
///
/// The lowerer polls between DAG nodes and inside the quadratic multiplier and
/// divider circuits. Already-built AIG state is irrelevant for this one-shot
/// entry; on expiry it returns [`BitLowerError::DeadlineExceeded`] rather than
/// completing an oversized circuit after the caller's solving budget.
///
/// # Errors
///
/// Returns the same errors as [`lower_terms`], plus
/// [`BitLowerError::DeadlineExceeded`] when `deadline` passes.
pub fn lower_terms_with_deadline(
    arena: &TermArena,
    roots: &[TermId],
    deadline: Option<Instant>,
) -> Result<BitLowering, BitLowerError> {
    LoweringBuilder::with_deadline(arena, deadline).lower_roots(roots, false)
}

/// Demand-driven counterpart of [`lower_terms_with_deadline`].
///
/// Demand planning and AIG construction share the supplied absolute deadline.
/// The sparse lift-map and deterministic omitted-bit completion contract are
/// the same as [`lower_terms_demanded`].
///
/// # Errors
///
/// Returns the same errors as [`lower_terms_demanded`], plus
/// [`BitLowerError::DeadlineExceeded`] when `deadline` passes.
pub fn lower_terms_demanded_with_deadline(
    arena: &TermArena,
    roots: &[TermId],
    deadline: Option<Instant>,
) -> Result<BitLowering, BitLowerError> {
    LoweringBuilder::with_deadline(arena, deadline).lower_demanded_roots(roots)
}

/// Deterministic policy for ADR-0158's admission-controlled range demand path.
///
/// The defaults are intentionally conservative and experimental. They are not
/// used by [`lower_terms`] or [`lower_terms_demanded`]; callers must select this
/// policy explicitly while the Glaurung acceptance gate is being calibrated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RangeDemandPolicy {
    /// Minimum root-reachable term bits before range analysis may run.
    pub min_term_bits_available: u64,
    /// Minimum structurally estimated bits avoided before exact analysis.
    pub min_estimated_bits_avoided: u64,
    /// Minimum estimated avoided percentage, in the inclusive range 0--100.
    pub min_estimated_avoided_percent: u8,
    /// Minimum exact avoided bits before sparse materialization.
    pub min_exact_bits_avoided: u64,
    /// Minimum exact avoided percentage, in the inclusive range 0--100.
    pub min_exact_avoided_percent: u8,
    /// Maximum deterministic work units for exact range propagation.
    pub analysis_work_budget: u64,
}

impl Default for RangeDemandPolicy {
    fn default() -> Self {
        Self {
            min_term_bits_available: 256,
            min_estimated_bits_avoided: 128,
            min_estimated_avoided_percent: 50,
            min_exact_bits_avoided: 128,
            min_exact_avoided_percent: 50,
            analysis_work_budget: 50_000,
        }
    }
}

/// Stable admission result for ADR-0158 range demand lowering.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum RangeDemandDecision {
    /// No admission-controlled policy was requested.
    #[default]
    NotRequested,
    /// No narrowing structural edge was reachable.
    NoCandidate,
    /// The cheap estimate did not meet the configured savings floor.
    InsufficientEstimate,
    /// Exact range analysis exceeded its deterministic work budget.
    AnalysisBudgetExceeded,
    /// Exact demand erased the estimated savings.
    InsufficientExactSavings,
    /// Exact range demand controlled sparse materialization.
    Applied,
}

impl RangeDemandDecision {
    /// Stable numeric code used by backend telemetry and versioned artifacts.
    pub const fn code(self) -> u8 {
        match self {
            Self::NotRequested => 0,
            Self::NoCandidate => 1,
            Self::InsufficientEstimate => 2,
            Self::AnalysisBudgetExceeded => 3,
            Self::InsufficientExactSavings => 4,
            Self::Applied => 5,
        }
    }

    /// Stable artifact spelling for this decision.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NotRequested => "not-requested",
            Self::NoCandidate => "no-candidate",
            Self::InsufficientEstimate => "insufficient-estimate",
            Self::AnalysisBudgetExceeded => "analysis-budget-exceeded",
            Self::InsufficientExactSavings => "insufficient-exact-savings",
            Self::Applied => "applied",
        }
    }

    /// Decodes a stable telemetry code, treating unknown future values as not
    /// requested instead of fabricating an admission result.
    pub const fn from_code(code: u64) -> Self {
        match code {
            1 => Self::NoCandidate,
            2 => Self::InsufficientEstimate,
            3 => Self::AnalysisBudgetExceeded,
            4 => Self::InsufficientExactSavings,
            5 => Self::Applied,
            _ => Self::NotRequested,
        }
    }
}

/// Lowers roots with ADR-0158 admission-controlled range demand.
///
/// Rejected and budget-exhausted queries take the ordinary full lowerer. An
/// admitted query propagates a bounded inline set of half-open bit ranges and
/// stores only demanded term-bit bindings. Omitted symbol bits retain
/// ADR-0157's deterministic-false model completion and all solver callers must
/// continue replaying the original assertions.
///
/// # Errors
///
/// Returns the same errors as [`lower_terms`].
pub fn lower_terms_range_demanded(
    arena: &TermArena,
    roots: &[TermId],
    policy: RangeDemandPolicy,
) -> Result<BitLowering, BitLowerError> {
    lower_terms_range_demanded_with_deadline(arena, roots, policy, None)
}

/// Deadline-aware counterpart of [`lower_terms_range_demanded`].
///
/// # Errors
///
/// Returns the same errors as [`lower_terms_with_deadline`].
pub fn lower_terms_range_demanded_with_deadline(
    arena: &TermArena,
    roots: &[TermId],
    policy: RangeDemandPolicy,
    deadline: Option<Instant>,
) -> Result<BitLowering, BitLowerError> {
    let screen = DemandAdmissionScreen::compute(arena, roots, deadline)?;
    if let Some(decision) = screen.rejection(policy) {
        return LoweringBuilder::with_deadline(arena, deadline)
            .lower_roots_with_demand_stats(roots, screen.into_stats(decision));
    }

    let plan = match RangeDemandPlan::compute(arena, roots, deadline, policy, &screen) {
        Ok(plan) => plan,
        Err(stats) => {
            return LoweringBuilder::with_deadline(arena, deadline)
                .lower_roots_with_demand_stats(roots, *stats);
        }
    };
    LoweringBuilder::with_deadline(arena, deadline).lower_range_demanded_roots(roots, plan)
}

/// Lowers roots under an absolute deadline and also computes the observational
/// structural bit-demand profile under that same deadline.
///
/// Profiling does not change the generated AIG or lift maps. Use
/// [`lower_terms_with_deadline`] for production solving.
///
/// # Errors
///
/// Returns the same errors as [`lower_terms_with_deadline`].
pub fn lower_terms_with_deadline_profiled(
    arena: &TermArena,
    roots: &[TermId],
    deadline: Option<Instant>,
) -> Result<BitLowering, BitLowerError> {
    let mut builder = LoweringBuilder::with_deadline(arena, deadline);
    builder.profiling_enabled = true;
    builder.lower_roots(roots, true)
}

/// Returns the first operator outside the current bit-lowering subset.
///
/// This is a cheap preflight for callers that need unsupported triage before
/// applying size budgets.
pub fn first_unsupported_op(arena: &TermArena, roots: &[TermId]) -> Option<(TermId, Op)> {
    let mut seen = BTreeSet::new();
    let mut stack = roots.iter().rev().copied().collect::<Vec<_>>();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        if is_unsupported_op(*op) {
            return Some((term, *op));
        }
        stack.extend(args.iter().rev().copied());
    }
    None
}

/// Returns the first subterm whose sort the bit-blaster cannot represent
/// directly — an integer (ADR-0014) or an array (ADR-0010). Such terms must be
/// eliminated or otherwise handled before bit lowering; this preflight lets
/// callers triage them as `Unsupported` (it catches sorts that the op-based
/// [`first_unsupported_op`] misses, e.g. a bare integer leaf under `=`).
pub fn first_unsupported_sort(arena: &TermArena, roots: &[TermId]) -> Option<(TermId, Sort)> {
    let mut seen = BTreeSet::new();
    let mut stack = roots.iter().rev().copied().collect::<Vec<_>>();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.sort_of(term) {
            // Floating-point lowers structurally to BitVec(exp+sig) (ADR-0026).
            Sort::Bool | Sort::BitVec(_) | Sort::Float { .. } => {}
            other => return Some((term, other)),
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().rev().copied());
        }
    }
    None
}

/// Lowered term bits in ADR-0006 LSB-first order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweredTerm {
    term: TermId,
    sort: Sort,
    bits: Vec<AigLit>,
}

impl LoweredTerm {
    /// Original source term.
    pub fn term(&self) -> TermId {
        self.term
    }

    /// Source term sort.
    pub fn sort(&self) -> Sort {
        self.sort
    }

    /// AIG literals for this term. For `BV(w)`, element `i` is bit `i`.
    /// For `Bool`, the slice has length one.
    pub fn bits(&self) -> &[AigLit] {
        &self.bits
    }
}

/// Mapping from one original term bit to one AIG literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TermBitBinding {
    /// Source term.
    pub term: TermId,
    /// Bit index in ADR-0006 LSB-first order. Boolean terms use bit 0.
    pub bit_index: u32,
    /// AIG literal implementing this bit.
    pub literal: AigLit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TermBitRange {
    start: usize,
    len: usize,
}

/// Mapping from one source symbol bit to one AIG input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolBitInput {
    /// Source symbol.
    pub symbol: SymbolId,
    /// Source symbol name, copied for diagnostics and future serialized maps.
    pub symbol_name: String,
    /// Source symbol sort.
    pub sort: Sort,
    /// Bit index in ADR-0006 LSB-first order. Boolean symbols use bit 0.
    pub bit_index: u32,
    /// AIG input ID in creation order.
    pub input: AigInputId,
    /// Positive AIG literal for this input.
    pub literal: AigLit,
}

/// Conservative structural bit-demand diagnostics for one batch lowering.
///
/// Demand starts at every root bit and propagates exactly through extracts,
/// concatenation, extensions, pointwise BV operators, and `ite`. Operators
/// without a bit-local rule conservatively demand every operand bit. This is a
/// diagnostic upper bound, not a semantic cone-of-influence proof.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct BitDemandStats {
    /// Whether the structural request/available/demanded fields were computed.
    ///
    /// Actual lowered counts are populated in both modes. When this is false,
    /// all other profile-only counts and [`Self::analysis`] are zero and must
    /// not be interpreted as a complete zero-demand result.
    pub profile_complete: bool,
    /// Whether demand changed production materialization rather than only
    /// observing the ordinary full lowerer.
    pub lowering_applied: bool,
    /// ADR-0158 admission outcome, separate from ADR-0157's force-on route.
    pub range_decision: RangeDemandDecision,
    /// Time spent in ADR-0158's cheap structural admission screen.
    pub admission: Duration,
    /// Bits the admission screen conservatively predicts can be skipped.
    pub estimated_bits_avoided: u64,
    /// Configured deterministic work ceiling for exact range analysis.
    pub analysis_work_budget: u64,
    /// Work units consumed by exact range analysis.
    pub analysis_work: u64,
    /// Range unions that joined overlapping or adjacent intervals.
    pub range_merges: u64,
    /// Terms conservatively promoted to full demand after fragmentation.
    pub range_promotions: u64,
    /// Time spent computing this structural demand profile.
    pub analysis: Duration,
    /// Term-bit requests before unioning repeated demands.
    pub term_bit_requests: u64,
    /// Bits in all unique terms reachable from the roots.
    pub term_bits_available: u64,
    /// Unique reachable term bits demanded by the structural analysis.
    pub term_bits_demanded: u64,
    /// Term bits materialized by the current lowerer.
    pub term_bits_lowered: u64,
    /// Symbol-bit requests before unioning repeated demands.
    pub symbol_bit_requests: u64,
    /// Bits in all unique symbols reachable from the roots.
    pub symbol_bits_available: u64,
    /// Unique symbol bits demanded by the structural analysis.
    pub symbol_bits_demanded: u64,
    /// Symbol bits materialized as AIG inputs by the current lowerer.
    pub symbol_bits_lowered: u64,
}

/// Private full-lowering memo representation reported by diagnostic profiles.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum BitLoweringMemoRepresentation {
    /// Memo diagnostics were not collected for this lowering.
    #[default]
    Unavailable,
    /// Ordered-tree baseline used before ADR-0300 observation.
    BtreeV1,
    /// Dense `TermId`-indexed candidate preregistered by ADR-0300.
    DenseV1,
}

impl BitLoweringMemoRepresentation {
    /// Stable numeric code used by backend-neutral solve statistics.
    pub const fn code(self) -> u8 {
        match self {
            Self::Unavailable => 0,
            Self::BtreeV1 => 1,
            Self::DenseV1 => 2,
        }
    }

    /// Stable artifact spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Unavailable => "unavailable",
            Self::BtreeV1 => "btree-v1",
            Self::DenseV1 => "dense-v1",
        }
    }

    /// Decodes the stable numeric representation code.
    pub const fn from_code(code: u64) -> Self {
        match code {
            1 => Self::BtreeV1,
            2 => Self::DenseV1,
            _ => Self::Unavailable,
        }
    }
}

/// Representation-neutral accounting for the private full-lowering term memo.
///
/// These diagnostics are populated only by observational profiled lowering.
/// Logical bytes use native `size_of` values and exclude allocator/tree-node
/// metadata; payload capacity and process RSS remain separate measurements.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct BitLoweringMemoStats {
    /// Whether every field below was collected.
    pub profile_complete: bool,
    /// Active private representation.
    pub representation: BitLoweringMemoRepresentation,
    /// Terms in the source arena, including unreachable terms.
    pub source_terms: u64,
    /// Addressable memo slots/nodes in the active representation.
    pub slots: u64,
    /// Completed terms retained in the memo.
    pub occupied: u64,
    /// Exact term lookups performed by full lowering.
    pub lookups: u64,
    /// Lookups that found an already completed term.
    pub hits: u64,
    /// Completed term vectors written to the memo.
    pub writes: u64,
    /// Retained literal payload length across all memo values.
    pub payload_literals: u64,
    /// Retained literal payload capacity across all memo values.
    pub payload_capacity_literals: u64,
    /// Conservative logical bytes for representation headers/keys.
    pub logical_header_bytes: u64,
    /// Logical bytes for initialized literal payloads.
    pub logical_payload_bytes: u64,
    /// Header plus initialized-payload logical bytes.
    pub logical_total_bytes: u64,
    /// Allocated-capacity bytes for literal payloads.
    pub payload_capacity_bytes: u64,
    /// Literal bits returned across all requested roots, including duplicate roots.
    pub root_bits: u64,
    /// Root bits required by the requested root sorts.
    pub expected_root_bits: u64,
    /// Whether representation-independent accounting identities hold.
    pub invariants_hold: bool,
}

/// AIG plus lift-map metadata for lowered roots.
#[derive(Debug, Clone)]
pub struct BitLowering {
    aig: Aig,
    roots: Vec<LoweredTerm>,
    term_bits: Vec<TermBitBinding>,
    term_bit_ranges: Vec<Option<TermBitRange>>,
    symbol_inputs: Vec<SymbolBitInput>,
    demand_stats: BitDemandStats,
    memo_stats: BitLoweringMemoStats,
    complete_omitted_symbol_bits: bool,
}

impl BitLowering {
    /// The generated AIG.
    pub fn aig(&self) -> &Aig {
        &self.aig
    }

    /// Lowered roots in input order.
    pub fn roots(&self) -> &[LoweredTerm] {
        &self.roots
    }

    /// Term-bit lift-map entries in deterministic lowering order.
    pub fn term_bits(&self) -> &[TermBitBinding] {
        &self.term_bits
    }

    /// Symbol-bit to AIG-input map entries in AIG input order.
    pub fn symbol_inputs(&self) -> &[SymbolBitInput] {
        &self.symbol_inputs
    }

    /// Returns structural demand and actual-lowering counts for this batch.
    pub fn demand_stats(&self) -> BitDemandStats {
        self.demand_stats
    }

    /// Returns private full-lowering memo diagnostics.
    ///
    /// Ordinary and demand-sliced production lowering return an unavailable
    /// record. Observational profiled full lowering returns exact accounting.
    pub fn memo_stats(&self) -> BitLoweringMemoStats {
        self.memo_stats
    }

    /// Looks up the AIG literal for one original term bit.
    pub fn literal_for_term_bit(&self, term: TermId, bit_index: u32) -> Option<AigLit> {
        let range = self.term_bit_ranges.get(term.index()).copied().flatten()?;
        let end = range.start.checked_add(range.len)?;
        let bindings = self.term_bits.get(range.start..end)?;
        let offset = bindings
            .binary_search_by_key(&bit_index, |binding| binding.bit_index)
            .ok()?;
        let binding = bindings.get(offset)?;
        debug_assert_eq!(binding.term, term);
        debug_assert_eq!(binding.bit_index, bit_index);
        Some(binding.literal)
    }

    /// Converts an Axeyum assignment into AIG input values in creation order.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError::Ir`] for unbound symbols or invalid values,
    /// and [`BitLowerError::AssignmentSortMismatch`] when a binding has the
    /// wrong sort for its symbol.
    pub fn input_values(&self, assignment: &Assignment) -> Result<Vec<bool>, BitLowerError> {
        let mut inputs = Vec::with_capacity(self.symbol_inputs.len());
        for binding in &self.symbol_inputs {
            let value = assignment
                .get(binding.symbol)
                .ok_or(IrError::UnboundSymbol(binding.symbol))?;
            if value.sort() != binding.sort {
                return Err(BitLowerError::AssignmentSortMismatch {
                    symbol: binding.symbol,
                    expected: binding.sort,
                    found: value.sort(),
                });
            }
            let bits = value_to_lsb_bits(value)?;
            let bit = bits.get(binding.bit_index as usize).copied().ok_or(
                BitLowerError::BadInputBit {
                    symbol: binding.symbol,
                    bit_index: binding.bit_index,
                },
            )?;
            inputs.push(bit);
        }
        Ok(inputs)
    }

    /// Evaluates one lowered root and reconstructs an Axeyum value.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if input conversion, AIG evaluation, or value
    /// reconstruction fails.
    pub fn evaluate_root(
        &self,
        root_index: usize,
        assignment: &Assignment,
    ) -> Result<Value, BitLowerError> {
        let root = self
            .roots
            .get(root_index)
            .ok_or(BitLowerError::UnknownRoot(root_index))?;
        let inputs = self.input_values(assignment)?;
        let bits = self.aig.eval_many(root.bits(), &inputs)?;
        Ok(lsb_bits_to_value(root.sort, &bits)?)
    }

    /// Evaluates every lowered root and reconstructs Axeyum values.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if input conversion, AIG evaluation, or value
    /// reconstruction fails.
    pub fn evaluate_roots(&self, assignment: &Assignment) -> Result<Vec<Value>, BitLowerError> {
        let inputs = self.input_values(assignment)?;
        self.roots
            .iter()
            .map(|root| {
                let bits = self.aig.eval_many(root.bits(), &inputs)?;
                Ok(lsb_bits_to_value(root.sort, &bits)?)
            })
            .collect()
    }

    /// Reconstructs an Axeyum model from replayed AIG node values.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if the AIG values have the wrong length, do not
    /// match the AIG semantics, or are missing a symbol bit.
    pub fn assignment_from_aig_values(
        &self,
        node_values: &[bool],
    ) -> Result<Assignment, BitLowerError> {
        assignment_from_aig_node_values(
            &self.aig,
            &self.symbol_inputs,
            node_values,
            self.complete_omitted_symbol_bits,
        )
    }

    /// Reconstructs one lowered root value from replayed AIG node values.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if the root is unknown or the AIG values do not
    /// validate.
    pub fn root_value_from_aig_values(
        &self,
        root_index: usize,
        node_values: &[bool],
    ) -> Result<Value, BitLowerError> {
        self.validate_aig_values(node_values)?;
        let root = self
            .roots
            .get(root_index)
            .ok_or(BitLowerError::UnknownRoot(root_index))?;
        let bits = root
            .bits()
            .iter()
            .copied()
            .map(|lit| aig_lit_from_node_values(lit, node_values))
            .collect::<Result<Vec<_>, BitLowerError>>()?;
        Ok(lsb_bits_to_value(root.sort, &bits)?)
    }

    /// Reconstructs all lowered root values from replayed AIG node values.
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if the AIG values do not validate.
    pub fn root_values_from_aig_values(
        &self,
        node_values: &[bool],
    ) -> Result<Vec<Value>, BitLowerError> {
        self.validate_aig_values(node_values)?;
        self.roots
            .iter()
            .map(|root| {
                let bits = root
                    .bits()
                    .iter()
                    .copied()
                    .map(|lit| aig_lit_from_node_values(lit, node_values))
                    .collect::<Result<Vec<_>, BitLowerError>>()?;
                Ok(lsb_bits_to_value(root.sort, &bits)?)
            })
            .collect()
    }

    fn validate_aig_values(&self, node_values: &[bool]) -> Result<(), BitLowerError> {
        validate_aig_node_values(&self.aig, node_values)
    }
}

/// Checks that `node_values` is a consistent valuation of every AIG node.
///
/// Shared by [`BitLowering`] and [`IncrementalLowering`] so both use the same
/// trusted replay check.
///
/// # Errors
///
/// Returns [`BitLowerError::AigValueLengthMismatch`] for the wrong length or
/// [`BitLowerError::AigValueMismatch`] when a node value contradicts the AIG.
fn validate_aig_node_values(aig: &Aig, node_values: &[bool]) -> Result<(), BitLowerError> {
    if node_values.len() != aig.node_count() {
        return Err(BitLowerError::AigValueLengthMismatch {
            expected: aig.node_count(),
            found: node_values.len(),
        });
    }
    for (node_id, node) in aig.nodes() {
        let expected = match node {
            AigNode::ConstFalse => false,
            AigNode::Input(_) => continue,
            AigNode::And(lhs, rhs) => {
                aig_lit_from_node_values(lhs, node_values)?
                    && aig_lit_from_node_values(rhs, node_values)?
            }
        };
        let found = node_values[node_id.index()];
        if found != expected {
            return Err(BitLowerError::AigValueMismatch {
                node: node_id.index(),
                expected,
                found,
            });
        }
    }
    Ok(())
}

/// Reconstructs an Axeyum assignment from replayed AIG node values, using the
/// symbol-input map. Shared by [`BitLowering`] and [`IncrementalLowering`].
///
/// # Errors
///
/// Returns [`BitLowerError`] if the AIG values are inconsistent, a symbol bit is
/// out of range, or a model bit is missing.
fn assignment_from_aig_node_values(
    aig: &Aig,
    symbol_inputs: &[SymbolBitInput],
    node_values: &[bool],
    complete_omitted_bits: bool,
) -> Result<Assignment, BitLowerError> {
    validate_aig_node_values(aig, node_values)?;

    let mut symbol_bits: BTreeMap<SymbolId, SymbolModelBits> = BTreeMap::new();
    for binding in symbol_inputs {
        let entry = symbol_bits
            .entry(binding.symbol)
            .or_insert_with(|| SymbolModelBits::new(binding.sort));
        let bit_index = binding.bit_index as usize;
        if bit_index >= entry.bits.len() {
            return Err(BitLowerError::BadInputBit {
                symbol: binding.symbol,
                bit_index: binding.bit_index,
            });
        }
        entry.bits[bit_index] = aig_lit_from_node_values(binding.literal, node_values)?;
        entry.seen[bit_index] = true;
    }

    let mut assignment = Assignment::new();
    for (symbol, bits) in symbol_bits {
        if !complete_omitted_bits {
            for (bit_index, seen) in (0u32..).zip(bits.seen.iter().copied()) {
                if !seen {
                    return Err(BitLowerError::MissingModelBit { symbol, bit_index });
                }
            }
        }
        assignment.set(symbol, lsb_bits_to_value(bits.sort, &bits.bits)?);
    }
    Ok(assignment)
}

/// Opt-in cumulative bookkeeping counters for persistent term-to-AIG lowering.
///
/// These counters complement [`axeyum_aig::AigConstructionStats`]: the AIG
/// counters classify primitive unique-table requests, while this structure
/// accounts for term memo traffic and the literal-vector copies required by
/// the current lowering representation. Ordinary [`IncrementalLowering`]
/// instances leave every field at zero.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct IncrementalLoweringStats {
    /// Calls to [`IncrementalLowering::lower`] or its deadline-aware variant.
    pub lower_calls: u64,
    /// Term-memo lookups made while traversing lowering worklists.
    pub term_memo_lookups: u64,
    /// Term-memo lookups that reused an already lowered term.
    pub term_memo_hits: u64,
    /// New terms recorded in the persistent lowering memo.
    pub terms_lowered: u64,
    /// Operand literal vectors cloned before lowering a parent application.
    pub operand_vectors_copied: u64,
    /// Operand literals copied by those vector clones.
    pub operand_bits_copied: u64,
    /// Root literals copied when returning a lowered root to the caller.
    pub root_bits_copied: u64,
    /// Term-bit lift-map bindings written for newly lowered terms.
    pub term_bit_bindings_written: u64,
    /// Current number of terms retained in the lowering memo.
    pub memoized_terms: u64,
    /// Current number of retained term-bit lift-map bindings.
    pub term_bit_bindings: u64,
    /// Current number of retained symbol-bit input bindings.
    pub symbol_bit_inputs: u64,
}

impl IncrementalLoweringStats {
    /// Returns the saturating component-wise delta from `earlier` to `self`.
    #[must_use]
    pub fn delta_since(self, earlier: Self) -> Self {
        Self {
            lower_calls: self.lower_calls.saturating_sub(earlier.lower_calls),
            term_memo_lookups: self
                .term_memo_lookups
                .saturating_sub(earlier.term_memo_lookups),
            term_memo_hits: self.term_memo_hits.saturating_sub(earlier.term_memo_hits),
            terms_lowered: self.terms_lowered.saturating_sub(earlier.terms_lowered),
            operand_vectors_copied: self
                .operand_vectors_copied
                .saturating_sub(earlier.operand_vectors_copied),
            operand_bits_copied: self
                .operand_bits_copied
                .saturating_sub(earlier.operand_bits_copied),
            root_bits_copied: self
                .root_bits_copied
                .saturating_sub(earlier.root_bits_copied),
            term_bit_bindings_written: self
                .term_bit_bindings_written
                .saturating_sub(earlier.term_bit_bindings_written),
            memoized_terms: self.memoized_terms.saturating_sub(earlier.memoized_terms),
            term_bit_bindings: self
                .term_bit_bindings
                .saturating_sub(earlier.term_bit_bindings),
            symbol_bit_inputs: self
                .symbol_bit_inputs
                .saturating_sub(earlier.symbol_bit_inputs),
        }
    }
}

/// Persistent, incremental term-to-AIG lowering (ADR-0009 stage 2).
///
/// Unlike [`lower_terms`], which lowers a fixed batch into a fresh AIG, this
/// keeps one AIG and one symbol/term memo across many [`IncrementalLowering::lower`]
/// calls. A symbol always maps to the same AIG inputs, and shared subterms are
/// lowered once and reused, so an incremental backend can bit-blast each newly
/// asserted term without redoing the shared prefix.
///
/// Term and symbol IDs are arena-stable, so the **same arena** must be used
/// across all calls on one instance.
#[derive(Debug, Default)]
pub struct IncrementalLowering {
    aig: Aig,
    memo: BTreeMap<TermId, Vec<AigLit>>,
    term_bits: Vec<TermBitBinding>,
    term_bit_ranges: Vec<Option<TermBitRange>>,
    symbol_inputs: Vec<SymbolBitInput>,
    profiling_enabled: bool,
    stats: IncrementalLoweringStats,
}

impl IncrementalLowering {
    /// Creates an empty incremental lowering context.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an incremental lowering context with diagnostic bookkeeping.
    ///
    /// This does not change lowering semantics or AIG construction order, but
    /// it increments counters on memo and literal-copy operations. Production
    /// callers should use [`Self::new`] unless attribution is required.
    pub fn with_profiling() -> Self {
        Self {
            profiling_enabled: true,
            ..Self::default()
        }
    }

    /// The persistent AIG built so far.
    pub fn aig(&self) -> &Aig {
        &self.aig
    }

    /// Number of AIG nodes built so far (including constant-false and inputs).
    ///
    /// Callers can record this before [`IncrementalLowering::lower`] to learn
    /// which nodes are new afterwards (the new range is `[before, after)`).
    pub fn node_count(&self) -> usize {
        self.aig.node_count()
    }

    /// Symbol-bit to AIG-input map entries in AIG input order.
    pub fn symbol_inputs(&self) -> &[SymbolBitInput] {
        &self.symbol_inputs
    }

    /// Returns cumulative opt-in lowering work and current retained gauges.
    #[must_use]
    pub fn stats(&self) -> IncrementalLoweringStats {
        if !self.profiling_enabled {
            return IncrementalLoweringStats::default();
        }
        IncrementalLoweringStats {
            memoized_terms: usize_to_u64_saturating(self.memo.len()),
            term_bit_bindings: usize_to_u64_saturating(self.term_bits.len()),
            symbol_bit_inputs: usize_to_u64_saturating(self.symbol_inputs.len()),
            ..self.stats
        }
    }

    /// Lowers `root` into the persistent AIG, reusing already-lowered shared
    /// subterms, and returns the lowered root (its bit literals and sort).
    ///
    /// # Errors
    ///
    /// Returns [`BitLowerError`] if a term uses an operator outside the lowering
    /// subset or an internal lowering invariant is violated. On error the
    /// partially-built AIG state is retained.
    pub fn lower(&mut self, arena: &TermArena, root: TermId) -> Result<LoweredTerm, BitLowerError> {
        self.lower_with_deadline(arena, root, None)
    }

    /// Lowers `root` into the persistent AIG while honoring an absolute
    /// wall-clock deadline.
    ///
    /// Shared terms already present in the memo remain reusable. On expiry,
    /// completed child terms and any structurally hashed orphan gates are
    /// retained, but the interrupted root is not memoized; callers normally end
    /// the current query with `Unknown` and may reuse the completed prefix later.
    ///
    /// # Errors
    ///
    /// Returns the same errors as [`Self::lower`], plus
    /// [`BitLowerError::DeadlineExceeded`] when `deadline` passes.
    pub fn lower_with_deadline(
        &mut self,
        arena: &TermArena,
        root: TermId,
        deadline: Option<Instant>,
    ) -> Result<LoweredTerm, BitLowerError> {
        if self.term_bit_ranges.len() < arena.len() {
            self.term_bit_ranges.resize(arena.len(), None);
        }
        // Move the persistent accumulators into a one-shot builder, reuse the
        // existing lowering logic, then move the grown state back. The memo
        // makes shared subterms (and symbols) lower once across calls.
        let mut builder = LoweringBuilder {
            arena,
            deadline,
            aig: core::mem::take(&mut self.aig),
            memo: core::mem::take(&mut self.memo),
            term_bits: core::mem::take(&mut self.term_bits),
            term_bit_ranges: core::mem::take(&mut self.term_bit_ranges),
            symbol_inputs: core::mem::take(&mut self.symbol_inputs),
            profiling_enabled: self.profiling_enabled,
            incremental_stats: core::mem::take(&mut self.stats),
        };
        let result = builder.lower_term(root);
        self.aig = builder.aig;
        self.memo = builder.memo;
        self.term_bits = builder.term_bits;
        self.term_bit_ranges = builder.term_bit_ranges;
        self.symbol_inputs = builder.symbol_inputs;
        self.stats = builder.incremental_stats;
        let bits = result?;
        Ok(LoweredTerm {
            term: root,
            sort: arena.sort_of(root),
            bits,
        })
    }

    /// Reconstructs an Axeyum model from replayed AIG node values, using the
    /// accumulated symbol-input map.
    ///
    /// # Errors
    ///
    /// See [`BitLowering::assignment_from_aig_values`].
    pub fn assignment_from_aig_values(
        &self,
        node_values: &[bool],
    ) -> Result<Assignment, BitLowerError> {
        assignment_from_aig_node_values(&self.aig, &self.symbol_inputs, node_values, false)
    }
}

/// Errors produced by the initial bit-lowering layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BitLowerError {
    /// Error from the IR layer.
    Ir(IrError),
    /// Error from the AIG layer.
    Aig(axeyum_aig::AigError),
    /// The caller's absolute lowering deadline elapsed before construction
    /// completed.
    DeadlineExceeded,
    /// Operator is outside the currently supported lowering subset.
    UnsupportedOp {
        /// Source term containing the unsupported operator.
        term: TermId,
        /// Unsupported operator.
        op: Op,
    },
    /// A lowered term had the wrong number of bits for its sort.
    BitWidthMismatch {
        /// Source term.
        term: TermId,
        /// Expected bit count.
        expected: u32,
        /// Actual bit count.
        found: usize,
    },
    /// Assignment value sort does not match the symbol sort.
    AssignmentSortMismatch {
        /// Source symbol.
        symbol: SymbolId,
        /// Expected symbol sort.
        expected: Sort,
        /// Assignment value sort.
        found: Sort,
    },
    /// Internal invariant failure: a symbol input referenced a missing bit.
    BadInputBit {
        /// Source symbol.
        symbol: SymbolId,
        /// Requested bit index.
        bit_index: u32,
    },
    /// Requested root index does not exist.
    UnknownRoot(usize),
    /// Replayed AIG values do not match the generated AIG node count.
    AigValueLengthMismatch {
        /// Expected node count.
        expected: usize,
        /// Actual value count.
        found: usize,
    },
    /// Replayed AIG values do not match a node definition.
    AigValueMismatch {
        /// AIG node index.
        node: usize,
        /// Expected value from the node definition.
        expected: bool,
        /// Replayed node value.
        found: bool,
    },
    /// A reconstructed symbol model is missing one of its bits.
    MissingModelBit {
        /// Source symbol.
        symbol: SymbolId,
        /// Missing bit index.
        bit_index: u32,
    },
    /// Demand propagation promised a child bit that was not materialized
    /// before its parent.
    MissingDemandedBit {
        /// Source term whose bit is missing.
        term: TermId,
        /// Missing LSB-first bit index.
        bit_index: u32,
    },
}

impl From<IrError> for BitLowerError {
    fn from(error: IrError) -> Self {
        Self::Ir(error)
    }
}

impl From<axeyum_aig::AigError> for BitLowerError {
    fn from(error: axeyum_aig::AigError) -> Self {
        Self::Aig(error)
    }
}

impl core::fmt::Display for BitLowerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BitLowerError::Ir(error) => write!(f, "{error}"),
            BitLowerError::Aig(error) => write!(f, "{error}"),
            BitLowerError::DeadlineExceeded => {
                write!(f, "bit-vector lowering deadline exceeded")
            }
            BitLowerError::UnsupportedOp { term, op } => {
                write!(
                    f,
                    "term #{} uses unsupported lowering operator {op:?}",
                    term.index()
                )
            }
            BitLowerError::BitWidthMismatch {
                term,
                expected,
                found,
            } => write!(
                f,
                "term #{} lowered to {found} bits, expected {expected}",
                term.index()
            ),
            BitLowerError::AssignmentSortMismatch {
                symbol,
                expected,
                found,
            } => write!(
                f,
                "symbol #{} assignment has sort {found}, expected {expected}",
                symbol.index()
            ),
            BitLowerError::BadInputBit { symbol, bit_index } => write!(
                f,
                "symbol #{} input map referenced missing bit {bit_index}",
                symbol.index()
            ),
            BitLowerError::UnknownRoot(index) => write!(f, "unknown lowered root #{index}"),
            BitLowerError::AigValueLengthMismatch { expected, found } => {
                write!(f, "expected {expected} AIG node values, found {found}")
            }
            BitLowerError::AigValueMismatch {
                node,
                expected,
                found,
            } => write!(
                f,
                "AIG node #{node} replayed as {found}, expected {expected}"
            ),
            BitLowerError::MissingModelBit { symbol, bit_index } => write!(
                f,
                "symbol #{} reconstructed model is missing bit {bit_index}",
                symbol.index()
            ),
            BitLowerError::MissingDemandedBit { term, bit_index } => write!(
                f,
                "demanded term #{} bit {bit_index} was not materialized",
                term.index()
            ),
        }
    }
}

impl core::error::Error for BitLowerError {}

struct LoweringBuilder<'a> {
    arena: &'a TermArena,
    deadline: Option<Instant>,
    aig: Aig,
    memo: BTreeMap<TermId, Vec<AigLit>>,
    term_bits: Vec<TermBitBinding>,
    term_bit_ranges: Vec<Option<TermBitRange>>,
    symbol_inputs: Vec<SymbolBitInput>,
    profiling_enabled: bool,
    incremental_stats: IncrementalLoweringStats,
}

struct SymbolModelBits {
    sort: Sort,
    bits: Vec<bool>,
    seen: Vec<bool>,
}

impl SymbolModelBits {
    fn new(sort: Sort) -> Self {
        let width = sort_width(sort);
        Self {
            sort,
            bits: vec![false; width],
            seen: vec![false; width],
        }
    }
}

impl<'a> LoweringBuilder<'a> {
    fn new(arena: &'a TermArena) -> Self {
        Self::with_deadline(arena, None)
    }

    fn with_deadline(arena: &'a TermArena, deadline: Option<Instant>) -> Self {
        Self {
            arena,
            deadline,
            aig: Aig::new(),
            memo: BTreeMap::new(),
            term_bits: Vec::new(),
            term_bit_ranges: vec![None; arena.len()],
            symbol_inputs: Vec::new(),
            profiling_enabled: false,
            incremental_stats: IncrementalLoweringStats::default(),
        }
    }

    fn poll_deadline(&self) -> Result<(), BitLowerError> {
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            Err(BitLowerError::DeadlineExceeded)
        } else {
            Ok(())
        }
    }

    fn memo_stats(&self, roots: &[TermId]) -> BitLoweringMemoStats {
        if !self.profiling_enabled {
            return BitLoweringMemoStats::default();
        }
        let occupied = usize_to_u64_saturating(self.memo.len());
        let payload_literals = self.memo.values().fold(0_u64, |total, bits| {
            total.saturating_add(usize_to_u64_saturating(bits.len()))
        });
        let payload_capacity_literals = self.memo.values().fold(0_u64, |total, bits| {
            total.saturating_add(usize_to_u64_saturating(bits.capacity()))
        });
        let header_unit = usize_to_u64_saturating(
            core::mem::size_of::<TermId>() + core::mem::size_of::<Vec<AigLit>>(),
        );
        let literal_bytes = usize_to_u64_saturating(core::mem::size_of::<AigLit>());
        let logical_header_bytes = occupied.saturating_mul(header_unit);
        let logical_payload_bytes = payload_literals.saturating_mul(literal_bytes);
        let payload_capacity_bytes = payload_capacity_literals.saturating_mul(literal_bytes);
        let writes = self.incremental_stats.terms_lowered;
        let lookups = self.incremental_stats.term_memo_lookups;
        let hits = self.incremental_stats.term_memo_hits;
        let root_bits = roots.iter().fold(0_u64, |total, root| {
            total.saturating_add(
                self.memo
                    .get(root)
                    .map_or(0, |bits| usize_to_u64_saturating(bits.len())),
            )
        });
        let expected_root_bits = roots.iter().fold(0_u64, |total, root| {
            total.saturating_add(usize_to_u64_saturating(sort_width(
                self.arena.sort_of(*root),
            )))
        });
        BitLoweringMemoStats {
            profile_complete: true,
            representation: BitLoweringMemoRepresentation::BtreeV1,
            source_terms: usize_to_u64_saturating(self.arena.len()),
            slots: occupied,
            occupied,
            lookups,
            hits,
            writes,
            payload_literals,
            payload_capacity_literals,
            logical_header_bytes,
            logical_payload_bytes,
            logical_total_bytes: logical_header_bytes.saturating_add(logical_payload_bytes),
            payload_capacity_bytes,
            root_bits,
            expected_root_bits,
            invariants_hold: occupied == writes
                && hits <= lookups
                && payload_literals == usize_to_u64_saturating(self.term_bits.len())
                && root_bits == expected_root_bits,
        }
    }

    fn lower_roots(
        mut self,
        roots: &[TermId],
        profile_bit_demand: bool,
    ) -> Result<BitLowering, BitLowerError> {
        let mut lowered_roots = Vec::with_capacity(roots.len());
        for &root in roots {
            self.poll_deadline()?;
            let bits = self.lower_term(root)?;
            lowered_roots.push(LoweredTerm {
                term: root,
                sort: self.arena.sort_of(root),
                bits,
            });
        }
        let mut demand_stats = if profile_bit_demand {
            structural_bit_demand(self.arena, roots, self.deadline)?
        } else {
            BitDemandStats::default()
        };
        demand_stats.term_bits_lowered = usize_to_u64_saturating(self.term_bits.len());
        demand_stats.symbol_bits_lowered = usize_to_u64_saturating(self.symbol_inputs.len());
        let memo_stats = self.memo_stats(roots);
        Ok(BitLowering {
            aig: self.aig,
            roots: lowered_roots,
            term_bits: self.term_bits,
            term_bit_ranges: self.term_bit_ranges,
            symbol_inputs: self.symbol_inputs,
            demand_stats,
            memo_stats,
            complete_omitted_symbol_bits: false,
        })
    }

    fn lower_roots_with_demand_stats(
        mut self,
        roots: &[TermId],
        mut demand_stats: BitDemandStats,
    ) -> Result<BitLowering, BitLowerError> {
        let mut lowered_roots = Vec::with_capacity(roots.len());
        for &root in roots {
            self.poll_deadline()?;
            let bits = self.lower_term(root)?;
            lowered_roots.push(LoweredTerm {
                term: root,
                sort: self.arena.sort_of(root),
                bits,
            });
        }
        demand_stats.term_bits_lowered = usize_to_u64_saturating(self.term_bits.len());
        demand_stats.symbol_bits_lowered = usize_to_u64_saturating(self.symbol_inputs.len());
        let memo_stats = self.memo_stats(roots);
        Ok(BitLowering {
            aig: self.aig,
            roots: lowered_roots,
            term_bits: self.term_bits,
            term_bit_ranges: self.term_bit_ranges,
            symbol_inputs: self.symbol_inputs,
            demand_stats,
            memo_stats,
            complete_omitted_symbol_bits: false,
        })
    }

    fn lower_demanded_roots(mut self, roots: &[TermId]) -> Result<BitLowering, BitLowerError> {
        let mut demand = DenseBitDemand::compute(self.arena, roots, self.deadline)?;
        let mut materialized = vec![Vec::new(); self.arena.len()];

        for term_index in 0..self.arena.len() {
            self.poll_deadline()?;
            let term = self
                .arena
                .term_by_index(term_index)
                .expect("dense term index belongs to the arena");
            let requested = demand.term_bits(term);
            if requested.is_empty() {
                continue;
            }
            let bits = self.lower_demanded_term(term, requested, &materialized)?;
            self.record_sparse(term, &bits)?;
            materialized[term_index] = bits;
        }

        let mut lowered_roots = Vec::with_capacity(roots.len());
        for &root in roots {
            lowered_roots.push(LoweredTerm {
                term: root,
                sort: self.arena.sort_of(root),
                bits: Self::complete_materialized_bits(root, &materialized)?,
            });
        }
        demand.stats.lowering_applied = true;
        demand.stats.term_bits_lowered = usize_to_u64_saturating(self.term_bits.len());
        demand.stats.symbol_bits_lowered = usize_to_u64_saturating(self.symbol_inputs.len());
        Ok(BitLowering {
            aig: self.aig,
            roots: lowered_roots,
            term_bits: self.term_bits,
            term_bit_ranges: self.term_bit_ranges,
            symbol_inputs: self.symbol_inputs,
            demand_stats: demand.stats,
            memo_stats: BitLoweringMemoStats::default(),
            complete_omitted_symbol_bits: true,
        })
    }

    fn lower_range_demanded_roots(
        mut self,
        roots: &[TermId],
        mut plan: RangeDemandPlan,
    ) -> Result<BitLowering, BitLowerError> {
        for term_index in 0..self.arena.len() {
            self.poll_deadline()?;
            let demand = plan.term_demands[term_index];
            if demand.is_none() {
                continue;
            }
            let term = self
                .arena
                .term_by_index(term_index)
                .expect("dense term index belongs to the arena");
            self.lower_range_demanded_term(term, demand)?;
        }

        let mut lowered_roots = Vec::with_capacity(roots.len());
        for &root in roots {
            lowered_roots.push(LoweredTerm {
                term: root,
                sort: self.arena.sort_of(root),
                bits: self.complete_recorded_bits(root)?,
            });
        }
        plan.stats.lowering_applied = true;
        plan.stats.range_decision = RangeDemandDecision::Applied;
        plan.stats.term_bits_lowered = usize_to_u64_saturating(self.term_bits.len());
        plan.stats.symbol_bits_lowered = usize_to_u64_saturating(self.symbol_inputs.len());
        Ok(BitLowering {
            aig: self.aig,
            roots: lowered_roots,
            term_bits: self.term_bits,
            term_bit_ranges: self.term_bit_ranges,
            symbol_inputs: self.symbol_inputs,
            demand_stats: plan.stats,
            memo_stats: BitLoweringMemoStats::default(),
            complete_omitted_symbol_bits: true,
        })
    }

    fn lower_range_demanded_term(
        &mut self,
        term: TermId,
        demand: InlineBitDemand,
    ) -> Result<(), BitLowerError> {
        let width = u32::try_from(sort_width(self.arena.sort_of(term)))
            .expect("lowerable term width fits u32");
        let start = self.term_bits.len();
        match self.arena.node(term).clone() {
            TermNode::BoolConst(value) => self.push_sparse_binding(term, 0, const_lit(value)),
            TermNode::BvConst { value, .. } => {
                for range in demand.ranges(width) {
                    for bit in range.start..range.end {
                        self.push_sparse_binding(term, bit, const_lit(((value >> bit) & 1) != 0));
                    }
                }
            }
            TermNode::WideBvConst(value) => {
                for range in demand.ranges(width) {
                    for bit in range.start..range.end {
                        self.push_sparse_binding(term, bit, const_lit(value.bit(bit)));
                    }
                }
            }
            TermNode::IntConst(_) => {
                unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
            }
            TermNode::RealConst(_) => {
                unreachable!("real terms are rejected before bit lowering (ADR-0015)")
            }
            TermNode::Symbol(symbol) => {
                let (name, sort) = self.arena.symbol(symbol);
                let name = name.to_owned();
                for range in demand.ranges(width) {
                    for bit in range.start..range.end {
                        let literal = self.symbol_input(symbol, &name, sort, bit);
                        self.push_sparse_binding(term, bit, literal);
                    }
                }
            }
            TermNode::App { op, args } if is_demand_local_op(op) => {
                for range in demand.ranges(width) {
                    for bit in range.start..range.end {
                        let literal = self.lower_range_local_bit(term, op, &args, bit)?;
                        self.push_sparse_binding(term, bit, literal);
                    }
                }
            }
            TermNode::App { op, args } => {
                debug_assert!(demand.is_full());
                let operands = args
                    .iter()
                    .map(|&arg| self.complete_recorded_bits(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                let bits = self.lower_app(term, op, &operands)?;
                for (bit, literal) in bits.into_iter().enumerate() {
                    self.push_sparse_binding(
                        term,
                        u32::try_from(bit).expect("term bit fits u32"),
                        literal,
                    );
                }
            }
        }
        let len = self.term_bits.len() - start;
        let range = self
            .term_bit_ranges
            .get_mut(term.index())
            .expect("term range index fits the source arena");
        debug_assert!(range.is_none(), "term is recorded at most once");
        *range = Some(TermBitRange { start, len });
        Ok(())
    }

    fn push_sparse_binding(&mut self, term: TermId, bit_index: u32, literal: AigLit) {
        self.term_bits.push(TermBitBinding {
            term,
            bit_index,
            literal,
        });
    }

    fn recorded_bit(&self, term: TermId, bit_index: u32) -> Result<AigLit, BitLowerError> {
        let range = self
            .term_bit_ranges
            .get(term.index())
            .copied()
            .flatten()
            .ok_or(BitLowerError::MissingDemandedBit { term, bit_index })?;
        let bindings = &self.term_bits[range.start..range.start + range.len];
        bindings
            .binary_search_by_key(&bit_index, |binding| binding.bit_index)
            .ok()
            .and_then(|index| bindings.get(index))
            .map(|binding| binding.literal)
            .ok_or(BitLowerError::MissingDemandedBit { term, bit_index })
    }

    fn complete_recorded_bits(&self, term: TermId) -> Result<Vec<AigLit>, BitLowerError> {
        let width = u32::try_from(sort_width(self.arena.sort_of(term)))
            .expect("lowerable term width fits u32");
        (0..width).map(|bit| self.recorded_bit(term, bit)).collect()
    }

    fn lower_range_local_bit(
        &mut self,
        term: TermId,
        op: Op,
        args: &[TermId],
        bit: u32,
    ) -> Result<AigLit, BitLowerError> {
        let literal = match op {
            Op::BoolNot | Op::BvNot => self.recorded_bit(args[0], bit)?.negated(),
            Op::BoolAnd | Op::BvAnd => {
                let lhs = self.recorded_bit(args[0], bit)?;
                let rhs = self.recorded_bit(args[1], bit)?;
                self.aig.and(lhs, rhs)
            }
            Op::BoolOr | Op::BvOr => {
                let lhs = self.recorded_bit(args[0], bit)?;
                let rhs = self.recorded_bit(args[1], bit)?;
                self.aig.or(lhs, rhs)
            }
            Op::BoolXor | Op::BvXor => {
                let lhs = self.recorded_bit(args[0], bit)?;
                let rhs = self.recorded_bit(args[1], bit)?;
                self.aig.xor(lhs, rhs)
            }
            Op::BoolImplies => {
                let lhs = self.recorded_bit(args[0], 0)?;
                let rhs = self.recorded_bit(args[1], 0)?;
                self.aig.or(lhs.negated(), rhs)
            }
            Op::BvNand => {
                let lhs = self.recorded_bit(args[0], bit)?;
                let rhs = self.recorded_bit(args[1], bit)?;
                self.aig.and(lhs, rhs).negated()
            }
            Op::BvNor => {
                let lhs = self.recorded_bit(args[0], bit)?;
                let rhs = self.recorded_bit(args[1], bit)?;
                self.aig.or(lhs, rhs).negated()
            }
            Op::BvXnor => {
                let lhs = self.recorded_bit(args[0], bit)?;
                let rhs = self.recorded_bit(args[1], bit)?;
                self.aig.xor(lhs, rhs).negated()
            }
            Op::Ite => {
                let condition = self.recorded_bit(args[0], 0)?;
                let when_true = self.recorded_bit(args[1], bit)?;
                let when_false = self.recorded_bit(args[2], bit)?;
                self.aig.mux(condition, when_true, when_false)
            }
            Op::Extract { lo, .. } => self.recorded_bit(args[0], bit + lo)?,
            Op::Concat => {
                let low_width = u32::try_from(sort_width(self.arena.sort_of(args[1])))
                    .expect("lowerable term width fits u32");
                if bit < low_width {
                    self.recorded_bit(args[1], bit)?
                } else {
                    self.recorded_bit(args[0], bit - low_width)?
                }
            }
            Op::ZeroExt { .. } => {
                let source_width = u32::try_from(sort_width(self.arena.sort_of(args[0])))
                    .expect("lowerable term width fits u32");
                if bit < source_width {
                    self.recorded_bit(args[0], bit)?
                } else {
                    AigLit::FALSE
                }
            }
            Op::SignExt { .. } => {
                let source_width = u32::try_from(sort_width(self.arena.sort_of(args[0])))
                    .expect("lowerable term width fits u32");
                self.recorded_bit(args[0], bit.min(source_width - 1))?
            }
            Op::RotateLeft { by } => {
                let width = u32::try_from(sort_width(self.arena.sort_of(args[0])))
                    .expect("lowerable term width fits u32");
                let shift = by % width;
                self.recorded_bit(args[0], (bit + width - shift) % width)?
            }
            Op::RotateRight { by } => {
                let width = u32::try_from(sort_width(self.arena.sort_of(args[0])))
                    .expect("lowerable term width fits u32");
                let shift = by % width;
                self.recorded_bit(args[0], (bit + shift) % width)?
            }
            Op::FpFromBits { .. } => self.recorded_bit(args[0], bit)?,
            _ => return Err(BitLowerError::UnsupportedOp { term, op }),
        };
        Ok(literal)
    }

    fn lower_demanded_term(
        &mut self,
        term: TermId,
        requested: &[bool],
        materialized: &[Vec<Option<AigLit>>],
    ) -> Result<Vec<Option<AigLit>>, BitLowerError> {
        let width = sort_width(self.arena.sort_of(term));
        let bits = match self.arena.node(term).clone() {
            TermNode::BoolConst(value) => vec![Some(const_lit(value))],
            TermNode::BvConst { value, .. } => requested
                .iter()
                .copied()
                .enumerate()
                .map(|(bit, demanded)| demanded.then(|| const_lit(((value >> bit) & 1) != 0)))
                .collect(),
            TermNode::WideBvConst(value) => requested
                .iter()
                .copied()
                .enumerate()
                .map(|(bit, demanded)| {
                    demanded.then(|| {
                        const_lit(
                            value.bit(u32::try_from(bit).expect("wide constant bit fits u32")),
                        )
                    })
                })
                .collect(),
            TermNode::IntConst(_) => {
                unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
            }
            TermNode::RealConst(_) => {
                unreachable!("real terms are rejected before bit lowering (ADR-0015)")
            }
            TermNode::Symbol(symbol) => self.lower_demanded_symbol(symbol, requested),
            TermNode::App { op, args } if is_demand_local_op(op) => {
                let mut bits = vec![None; width];
                for (bit, demanded) in requested.iter().copied().enumerate() {
                    if demanded {
                        bits[bit] = Some(self.lower_demanded_local_bit(
                            term,
                            op,
                            &args,
                            u32::try_from(bit).expect("term bit fits u32"),
                            materialized,
                        )?);
                    }
                }
                bits
            }
            TermNode::App { op, args } => {
                let operands = args
                    .iter()
                    .map(|&arg| Self::complete_materialized_bits(arg, materialized))
                    .collect::<Result<Vec<_>, _>>()?;
                self.lower_app(term, op, &operands)?
                    .into_iter()
                    .map(Some)
                    .collect()
            }
        };
        if bits.len() != width {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(width).unwrap_or(u32::MAX),
                found: bits.len(),
            });
        }
        Ok(bits)
    }

    fn lower_demanded_symbol(
        &mut self,
        symbol: SymbolId,
        requested: &[bool],
    ) -> Vec<Option<AigLit>> {
        let (name, sort) = self.arena.symbol(symbol);
        requested
            .iter()
            .copied()
            .enumerate()
            .map(|(bit, demanded)| {
                demanded.then(|| {
                    self.symbol_input(
                        symbol,
                        name,
                        sort,
                        u32::try_from(bit).expect("symbol bit fits u32"),
                    )
                })
            })
            .collect()
    }

    fn complete_materialized_bits(
        term: TermId,
        materialized: &[Vec<Option<AigLit>>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let bits = &materialized[term.index()];
        bits.iter()
            .copied()
            .enumerate()
            .map(|(bit, literal)| {
                literal.ok_or(BitLowerError::MissingDemandedBit {
                    term,
                    bit_index: u32::try_from(bit).expect("term bit fits u32"),
                })
            })
            .collect()
    }

    fn demanded_materialized_bit(
        term: TermId,
        bit_index: u32,
        materialized: &[Vec<Option<AigLit>>],
    ) -> Result<AigLit, BitLowerError> {
        materialized
            .get(term.index())
            .and_then(|bits| bits.get(bit_index as usize))
            .copied()
            .flatten()
            .ok_or(BitLowerError::MissingDemandedBit { term, bit_index })
    }

    fn lower_demanded_local_bit(
        &mut self,
        term: TermId,
        op: Op,
        args: &[TermId],
        bit: u32,
        materialized: &[Vec<Option<AigLit>>],
    ) -> Result<AigLit, BitLowerError> {
        let get = |term, bit| Self::demanded_materialized_bit(term, bit, materialized);
        let literal = match op {
            Op::BoolNot | Op::BvNot => get(args[0], bit)?.negated(),
            Op::BoolAnd | Op::BvAnd => self.aig.and(get(args[0], bit)?, get(args[1], bit)?),
            Op::BoolOr | Op::BvOr => self.aig.or(get(args[0], bit)?, get(args[1], bit)?),
            Op::BoolXor | Op::BvXor => self.aig.xor(get(args[0], bit)?, get(args[1], bit)?),
            Op::BoolImplies => self.aig.or(get(args[0], 0)?.negated(), get(args[1], 0)?),
            Op::BvNand => self
                .aig
                .and(get(args[0], bit)?, get(args[1], bit)?)
                .negated(),
            Op::BvNor => self
                .aig
                .or(get(args[0], bit)?, get(args[1], bit)?)
                .negated(),
            Op::BvXnor => self
                .aig
                .xor(get(args[0], bit)?, get(args[1], bit)?)
                .negated(),
            Op::Ite => self
                .aig
                .mux(get(args[0], 0)?, get(args[1], bit)?, get(args[2], bit)?),
            Op::Extract { lo, .. } => get(args[0], bit + lo)?,
            Op::Concat => {
                let low_width = u32::try_from(sort_width(self.arena.sort_of(args[1])))
                    .expect("lowerable term width fits u32");
                if bit < low_width {
                    get(args[1], bit)?
                } else {
                    get(args[0], bit - low_width)?
                }
            }
            Op::ZeroExt { .. } => {
                let source_width = u32::try_from(sort_width(self.arena.sort_of(args[0])))
                    .expect("lowerable term width fits u32");
                if bit < source_width {
                    get(args[0], bit)?
                } else {
                    AigLit::FALSE
                }
            }
            Op::SignExt { .. } => {
                let source_width = u32::try_from(sort_width(self.arena.sort_of(args[0])))
                    .expect("lowerable term width fits u32");
                get(args[0], bit.min(source_width - 1))?
            }
            Op::RotateLeft { by } => {
                let width = u32::try_from(sort_width(self.arena.sort_of(args[0])))
                    .expect("lowerable term width fits u32");
                let shift = by % width;
                get(args[0], (bit + width - shift) % width)?
            }
            Op::RotateRight { by } => {
                let width = u32::try_from(sort_width(self.arena.sort_of(args[0])))
                    .expect("lowerable term width fits u32");
                let shift = by % width;
                get(args[0], (bit + shift) % width)?
            }
            Op::FpFromBits { .. } => get(args[0], bit)?,
            _ => {
                return Err(BitLowerError::UnsupportedOp { term, op });
            }
        };
        Ok(literal)
    }

    fn lower_term(&mut self, root: TermId) -> Result<Vec<AigLit>, BitLowerError> {
        if self.profiling_enabled {
            self.incremental_stats.lower_calls =
                self.incremental_stats.lower_calls.saturating_add(1);
        }
        let mut stack = vec![(root, false)];
        while let Some((term, children_ready)) = stack.pop() {
            self.poll_deadline()?;
            if self.profiling_enabled {
                self.incremental_stats.term_memo_lookups =
                    self.incremental_stats.term_memo_lookups.saturating_add(1);
            }
            if self.memo.contains_key(&term) {
                if self.profiling_enabled {
                    self.incremental_stats.term_memo_hits =
                        self.incremental_stats.term_memo_hits.saturating_add(1);
                }
                continue;
            }
            match self.arena.node(term) {
                TermNode::BoolConst(value) => {
                    self.record(term, vec![const_lit(*value)])?;
                }
                TermNode::BvConst { width, value } => {
                    let bits = axeyum_ir::bv_value_to_lsb_bits(*width, *value)?
                        .into_iter()
                        .map(const_lit)
                        .collect::<Vec<_>>();
                    self.record(term, bits)?;
                }
                TermNode::WideBvConst(w) => {
                    // A >128-bit constant lowers to its LSB-first bit literals
                    // (wide-BV; the AIG is bit-level so width is unbounded).
                    let bits = w
                        .to_lsb_bits()
                        .into_iter()
                        .map(const_lit)
                        .collect::<Vec<_>>();
                    self.record(term, bits)?;
                }
                TermNode::IntConst(_) => {
                    // Integers are not bit-blasted (ADR-0014); callers preflight
                    // with `first_unsupported_sort`.
                    unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
                }
                TermNode::RealConst(_) => {
                    // Reals are not bit-blasted (ADR-0015); callers preflight
                    // with `first_unsupported_sort`.
                    unreachable!("real terms are rejected before bit lowering (ADR-0015)")
                }
                TermNode::Symbol(symbol) => {
                    let bits = self.lower_symbol(*symbol);
                    self.record(term, bits)?;
                }
                TermNode::App { op, args } if children_ready => {
                    if self.profiling_enabled {
                        self.incremental_stats.operand_vectors_copied = self
                            .incremental_stats
                            .operand_vectors_copied
                            .saturating_add(usize_to_u64_saturating(args.len()));
                        let copied = args.iter().fold(0_u64, |total, arg| {
                            total.saturating_add(
                                self.memo
                                    .get(arg)
                                    .map_or(0, |bits| usize_to_u64_saturating(bits.len())),
                            )
                        });
                        self.incremental_stats.operand_bits_copied = self
                            .incremental_stats
                            .operand_bits_copied
                            .saturating_add(copied);
                    }
                    let operand_bits = args
                        .iter()
                        .map(|arg| {
                            self.memo
                                .get(arg)
                                .cloned()
                                .expect("children are lowered before parent")
                        })
                        .collect::<Vec<_>>();
                    let bits = self.lower_app(term, *op, &operand_bits)?;
                    self.record(term, bits)?;
                }
                TermNode::App { args, .. } => {
                    stack.push((term, true));
                    for &arg in args.iter().rev() {
                        stack.push((arg, false));
                    }
                }
            }
        }
        let root_bits = self.memo.get(&root).expect("root has been lowered");
        if self.profiling_enabled {
            self.incremental_stats.root_bits_copied = self
                .incremental_stats
                .root_bits_copied
                .saturating_add(usize_to_u64_saturating(root_bits.len()));
        }
        Ok(root_bits.clone())
    }

    fn lower_symbol(&mut self, symbol: SymbolId) -> Vec<AigLit> {
        let (name, sort) = self.arena.symbol(symbol);
        match sort {
            Sort::Bool => vec![self.symbol_input(symbol, name, sort, 0)],
            // Floating-point shares the bit-vector lowering: `exp + sig` input bits.
            Sort::BitVec(_) | Sort::Float { .. } => {
                (0..sort.lowered_width().expect("bitvec/float has a width"))
                    .map(|bit_index| self.symbol_input(symbol, name, sort, bit_index))
                    .collect()
            }
            // Array symbols are eliminated to bit-vectors before lowering
            // (ADR-0010); callers preflight with `first_unsupported_op`.
            Sort::Array { .. } => {
                unreachable!("array terms are eliminated before bit lowering (ADR-0010)")
            }
            Sort::Int => {
                unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
            }
            Sort::Real => {
                unreachable!("real terms are rejected before bit lowering (ADR-0015)")
            }
            Sort::Datatype(_) => {
                unreachable!("datatype terms are rejected before bit lowering (ADR-0022)")
            }
            Sort::Uninterpreted(_) => {
                unreachable!("uninterpreted-sort terms are rejected before bit lowering")
            }
            Sort::Seq(_) => {
                unreachable!("sequence terms are rejected before bit lowering (P2.7)")
            }
        }
    }

    fn symbol_input(&mut self, symbol: SymbolId, name: &str, sort: Sort, bit_index: u32) -> AigLit {
        let label = match sort {
            Sort::Bool => format!("{name}:bool"),
            Sort::BitVec(_) | Sort::Float { .. } => format!("{name}[{bit_index}]"),
            Sort::Array { .. } => {
                unreachable!("array terms are eliminated before bit lowering (ADR-0010)")
            }
            Sort::Int => {
                unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
            }
            Sort::Real => {
                unreachable!("real terms are rejected before bit lowering (ADR-0015)")
            }
            Sort::Datatype(_) => {
                unreachable!("datatype terms are rejected before bit lowering (ADR-0022)")
            }
            Sort::Uninterpreted(_) => {
                unreachable!("uninterpreted-sort terms are rejected before bit lowering")
            }
            Sort::Seq(_) => {
                unreachable!("sequence terms are rejected before bit lowering (P2.7)")
            }
        };
        let literal = self.aig.input(label);
        let input = match self
            .aig
            .node(literal.node())
            .expect("new input node exists in AIG")
        {
            AigNode::Input(input) => input,
            AigNode::ConstFalse | AigNode::And(_, _) => {
                unreachable!("AIG input construction returned a non-input node")
            }
        };
        self.symbol_inputs.push(SymbolBitInput {
            symbol,
            symbol_name: name.to_owned(),
            sort,
            bit_index,
            input,
            literal,
        });
        literal
    }

    #[allow(clippy::too_many_lines)]
    fn lower_app(
        &mut self,
        term: TermId,
        op: Op,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        self.poll_deadline()?;
        let bits = match op {
                Op::BoolNot => vec![expect_bool(term, &operands[0])?.negated()],
                Op::BoolAnd => vec![self.aig.and(
                    expect_bool(term, &operands[0])?,
                    expect_bool(term, &operands[1])?,
                )],
                Op::BoolOr => vec![self.aig.or(
                    expect_bool(term, &operands[0])?,
                    expect_bool(term, &operands[1])?,
                )],
                Op::BoolXor => vec![self.aig.xor(
                    expect_bool(term, &operands[0])?,
                    expect_bool(term, &operands[1])?,
                )],
                Op::BoolImplies => {
                    let antecedent = expect_bool(term, &operands[0])?;
                    let consequent = expect_bool(term, &operands[1])?;
                    vec![self.aig.or(antecedent.negated(), consequent)]
                }
                Op::BvNot => operands[0].iter().map(|bit| bit.negated()).collect(),
                Op::BvAnd => self.lower_pairwise(term, operands, Aig::and)?,
                Op::BvOr => self.lower_pairwise(term, operands, Aig::or)?,
                Op::BvXor => self.lower_pairwise(term, operands, Aig::xor)?,
                Op::BvNand => self
                    .lower_pairwise(term, operands, |aig, lhs, rhs| aig.and(lhs, rhs).negated())?,
                Op::BvNor => {
                    self.lower_pairwise(term, operands, |aig, lhs, rhs| aig.or(lhs, rhs).negated())?
                }
                Op::BvXnor => self
                    .lower_pairwise(term, operands, |aig, lhs, rhs| aig.xor(lhs, rhs).negated())?,
                Op::Eq | Op::BvComp => self.lower_equality_op(term, operands)?,
                Op::Ite => self.lower_ite_op(term, operands)?,
                Op::Extract { hi, lo } => Self::lower_extract(term, operands, hi, lo)?,
                Op::Concat => Self::lower_concat(term, operands)?,
                Op::ZeroExt { by } => Self::lower_zero_ext(term, operands, by)?,
                Op::SignExt { by } => Self::lower_sign_ext(term, operands, by)?,
                Op::BvNeg => self.lower_neg_op(term, operands)?,
                Op::BvAdd => self.lower_add_op(term, operands)?,
                Op::BvSub => self.lower_sub_op(term, operands)?,
                Op::BvMul => self.lower_mul_op(term, operands)?,
                Op::BvUdiv => self.lower_udiv_op(term, operands)?,
                Op::BvUrem => self.lower_urem_op(term, operands)?,
                Op::BvSdiv => self.lower_sdiv_op(term, operands)?,
                Op::BvSrem => self.lower_srem_op(term, operands)?,
                Op::BvSmod => self.lower_smod_op(term, operands)?,
                Op::BvUlt
                | Op::BvUle
                | Op::BvUgt
                | Op::BvUge
                | Op::BvSlt
                | Op::BvSle
                | Op::BvSgt
                | Op::BvSge => self.lower_compare_op(term, op, operands)?,
                Op::BvShl | Op::BvLshr | Op::BvAshr => self.lower_shift_op(term, op, operands)?,
                Op::RotateLeft { by } => Self::lower_rotate_op(term, operands, by, true)?,
                Op::RotateRight { by } => Self::lower_rotate_op(term, operands, by, false)?,
                // A floating-point reinterpret is identity on the bits (ADR-0026).
                Op::FpFromBits { .. } => {
                    let [source] = operands else {
                        return Err(BitLowerError::BitWidthMismatch {
                            term,
                            expected: 1,
                            found: operands.len(),
                        });
                    };
                    source.clone()
                }
                // Arrays are eliminated to QF_BV before lowering (ADR-0010);
                // uninterpreted functions via Ackermann reduction (ADR-0013);
                // integer arithmetic is not bit-blasted in this slice (ADR-0014).
                Op::Select
                | Op::Store
                | Op::ConstArray { .. }
                | Op::IntToReal
                | Op::RealToInt
                | Op::RealIsInt
                | Op::Bv2Nat
                | Op::Int2Bv { .. }
                | Op::Apply(_)
                | Op::IntNeg
                | Op::IntAdd
                | Op::IntSub
                | Op::IntMul
                | Op::IntDiv
                | Op::IntMod
                | Op::IntAbs
                | Op::IntLt
                | Op::IntLe
                | Op::IntGt
                | Op::IntGe
                | Op::RealNeg
                | Op::RealAdd
                | Op::RealSub
                | Op::RealMul
                | Op::RealDiv
                | Op::RealLt
                | Op::RealLe
                | Op::RealGt
                | Op::RealGe
                | Op::Forall(_)
                | Op::Exists(_)
                | Op::DtConstruct { .. }
                | Op::DtSelect { .. }
                | Op::DtTest(_)
                // `int.pow2` is an integer (NIA) term with no bit-vector lowering.
                | Op::IntPow2
                // Sequences (ADR-0051, P2.7) have no bit-vector lowering.
                | Op::SeqLen
                | Op::SeqEmpty(_)
                | Op::SeqUnit
                | Op::SeqConcat => {
                    return Err(BitLowerError::UnsupportedOp { term, op });
                }
            };
        self.check_width(term, &bits)?;
        Ok(bits)
    }

    fn lower_neg_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [source] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 1,
                found: operands.len(),
            });
        };
        let inverted = source.iter().map(|bit| bit.negated()).collect::<Vec<_>>();
        Ok(self.lower_increment(&inverted))
    }

    fn lower_add_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        self.lower_add_bits(term, lhs, rhs, AigLit::FALSE)
    }

    fn lower_sub_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        let inverted_rhs = rhs.iter().map(|bit| bit.negated()).collect::<Vec<_>>();
        self.lower_add_bits(term, lhs, &inverted_rhs, AigLit::TRUE)
    }

    fn lower_mul_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        if lhs.len() != rhs.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(lhs.len()).unwrap_or(u32::MAX),
                found: rhs.len(),
            });
        }
        let width = lhs.len();
        // Shift-and-add multiplier, truncated to `width` bits (SMT-LIB bvmul is
        // multiplication modulo 2^width). Partial product `i` is `lhs << i`
        // gated by `rhs[i]`; bits shifted past the top are dropped, so the
        // running sum stays `width` bits and equals the wrapping product. The
        // AIG folds the gated-`false` and shifted-in `false` bits, so low
        // multiplier bits and leading partial bits cost no gates.
        //
        // A modified-Booth (radix-4) recoding was implemented and verified
        // (exhaustive evaluator equality + DRAT miter) and then reverted: it
        // halves the partial-product *count* but its per-digit select/negate
        // logic is ~4x heavier than a single AND, so the net AND-node change was
        // only +6% at width 8, -8% at width 16, -14% at width 24. The public
        // QF_BV frontier instances are 8-bit, where Booth is a *regression*, so
        // it is not the right size lever here (see PLAN.md Status 2026-06-13).
        let mut result = vec![AigLit::FALSE; width];
        for i in 0..width {
            self.poll_deadline()?;
            let multiplier_bit = rhs[i];
            let mut partial = vec![AigLit::FALSE; width];
            for j in i..width {
                if j.is_multiple_of(64) {
                    self.poll_deadline()?;
                }
                partial[j] = self.aig.and(lhs[j - i], multiplier_bit);
            }
            result = self.lower_add_bits(term, &result, &partial, AigLit::FALSE)?;
        }
        Ok(result)
    }

    fn lower_udiv_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let (dividend, divisor) = expect_two(term, operands)?;
        let (quotient, _remainder) = self.unsigned_divrem(term, dividend, divisor)?;
        Ok(quotient)
    }

    fn lower_urem_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let (dividend, divisor) = expect_two(term, operands)?;
        let (_quotient, remainder) = self.unsigned_divrem(term, dividend, divisor)?;
        Ok(remainder)
    }

    /// Combinational restoring divider.
    ///
    /// Returns `(quotient, remainder)` for the unsigned division of `dividend`
    /// by `divisor`, both `width` bits, applying SMT-LIB totality: division by
    /// zero yields an all-ones quotient and the dividend as remainder. The AIG's
    /// structural hashing deduplicates the shared circuit when both `bvudiv` and
    /// `bvurem` of the same operands appear.
    fn unsigned_divrem(
        &mut self,
        term: TermId,
        dividend: &[AigLit],
        divisor: &[AigLit],
    ) -> Result<(Vec<AigLit>, Vec<AigLit>), BitLowerError> {
        let width = dividend.len();
        if divisor.len() != width {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(width).unwrap_or(u32::MAX),
                found: divisor.len(),
            });
        }

        // Zero-extend the divisor by one bit so the partial-remainder compare
        // and subtract never overflow: the invariant `remainder < divisor`
        // keeps `shifted = 2*remainder + bit < 2*divisor`, which fits in
        // `width + 1` bits, and the post-step value is again `< divisor`.
        let mut divisor_ext = divisor.to_vec();
        divisor_ext.push(AigLit::FALSE);
        let negated_divisor_ext = divisor_ext
            .iter()
            .map(|bit| bit.negated())
            .collect::<Vec<_>>();

        let mut remainder = vec![AigLit::FALSE; width];
        let mut quotient = vec![AigLit::FALSE; width];

        for index in (0..width).rev() {
            self.poll_deadline()?;
            // shifted = (remainder << 1) | dividend[index], width + 1 bits.
            let mut shifted = Vec::with_capacity(width + 1);
            shifted.push(dividend[index]);
            shifted.extend_from_slice(&remainder);

            let less = self.lower_unsigned_less(term, &shifted, &divisor_ext)?;
            let greater_equal = less.negated();
            // diff = shifted - divisor (two's complement add of the negation).
            let diff = self.lower_add_bits(term, &shifted, &negated_divisor_ext, AigLit::TRUE)?;
            let next = self.mux_bits(greater_equal, &diff, &shifted);
            // The post-step value is `< divisor`, so its top bit is zero.
            remainder = next[..width].to_vec();
            quotient[index] = greater_equal;
        }

        // SMT-LIB totality: `bvudiv x 0 = ~0`, `bvurem x 0 = x`.
        let divisor_is_zero = self.lower_all_bits_clear(divisor);
        let all_ones = vec![AigLit::TRUE; width];
        let quotient = self.mux_bits(divisor_is_zero, &all_ones, &quotient);
        let remainder = self.mux_bits(divisor_is_zero, dividend, &remainder);
        Ok((quotient, remainder))
    }

    fn mux_bits(
        &mut self,
        condition: AigLit,
        then_bits: &[AigLit],
        else_bits: &[AigLit],
    ) -> Vec<AigLit> {
        then_bits
            .iter()
            .copied()
            .zip(else_bits.iter().copied())
            .map(|(then_bit, else_bit)| self.aig.mux(condition, then_bit, else_bit))
            .collect()
    }

    /// Two's-complement negation: invert and increment.
    fn negate_bits(&mut self, bits: &[AigLit]) -> Vec<AigLit> {
        let inverted = bits.iter().map(|bit| bit.negated()).collect::<Vec<_>>();
        self.lower_increment(&inverted)
    }

    /// Absolute value under two's complement: `msb ? -x : x` (the most-negative
    /// value maps to itself, matching the SMT-LIB signed-division expansion).
    fn absolute_bits(&mut self, bits: &[AigLit]) -> Vec<AigLit> {
        let sign = bits[bits.len() - 1];
        let negated = self.negate_bits(bits);
        self.mux_bits(sign, &negated, bits)
    }

    /// Selects one of four equal-width vectors by two sign bits:
    /// `(sign_a, sign_b) -> v00 | v10 | v01 | v11`.
    fn select_by_signs(
        &mut self,
        sign_a: AigLit,
        sign_b: AigLit,
        v00: &[AigLit],
        v10: &[AigLit],
        v01: &[AigLit],
        v11: &[AigLit],
    ) -> Vec<AigLit> {
        let when_a_clear = self.mux_bits(sign_b, v01, v00);
        let when_a_set = self.mux_bits(sign_b, v11, v10);
        self.mux_bits(sign_a, &when_a_set, &when_a_clear)
    }

    /// Shared signed-division core: returns the operand sign bits and the
    /// unsigned quotient/remainder of the operands' absolute values. The AIG's
    /// structural hashing deduplicates this across `bvsdiv`/`bvsrem`/`bvsmod` of
    /// the same operands.
    fn signed_divrem_abs(
        &mut self,
        term: TermId,
        dividend: &[AigLit],
        divisor: &[AigLit],
    ) -> Result<(AigLit, AigLit, Vec<AigLit>, Vec<AigLit>), BitLowerError> {
        let width = dividend.len();
        if divisor.len() != width {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(width).unwrap_or(u32::MAX),
                found: divisor.len(),
            });
        }
        let sign_dividend = dividend[width - 1];
        let sign_divisor = divisor[width - 1];
        let abs_dividend = self.absolute_bits(dividend);
        let abs_divisor = self.absolute_bits(divisor);
        let (quotient, remainder) = self.unsigned_divrem(term, &abs_dividend, &abs_divisor)?;
        Ok((sign_dividend, sign_divisor, quotient, remainder))
    }

    fn lower_sdiv_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let (dividend, divisor) = expect_two(term, operands)?;
        let (sign_dividend, sign_divisor, quotient, _remainder) =
            self.signed_divrem_abs(term, dividend, divisor)?;
        // The quotient is negated exactly when the operand signs differ.
        let signs_differ = self.aig.xor(sign_dividend, sign_divisor);
        let negated_quotient = self.negate_bits(&quotient);
        Ok(self.mux_bits(signs_differ, &negated_quotient, &quotient))
    }

    fn lower_srem_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let (dividend, divisor) = expect_two(term, operands)?;
        let (sign_dividend, _sign_divisor, _quotient, remainder) =
            self.signed_divrem_abs(term, dividend, divisor)?;
        // The remainder's sign follows the dividend.
        let negated_remainder = self.negate_bits(&remainder);
        Ok(self.mux_bits(sign_dividend, &negated_remainder, &remainder))
    }

    fn lower_smod_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let (dividend, divisor) = expect_two(term, operands)?;
        let (sign_dividend, sign_divisor, _quotient, remainder) =
            self.signed_divrem_abs(term, dividend, divisor)?;
        // The result's sign follows the divisor (SMT-LIB bvsmod expansion); a
        // zero unsigned remainder yields zero regardless of signs.
        let remainder_is_zero = self.lower_all_bits_clear(&remainder);
        let negated_remainder = self.negate_bits(&remainder);
        let both_nonneg = remainder.clone();
        let dividend_neg = self.lower_add_bits(term, &negated_remainder, divisor, AigLit::FALSE)?;
        let divisor_neg = self.lower_add_bits(term, &remainder, divisor, AigLit::FALSE)?;
        let both_neg = negated_remainder.clone();
        let selected = self.select_by_signs(
            sign_dividend,
            sign_divisor,
            &both_nonneg,
            &dividend_neg,
            &divisor_neg,
            &both_neg,
        );
        Ok(self.mux_bits(remainder_is_zero, &remainder, &selected))
    }

    fn lower_compare_op(
        &mut self,
        term: TermId,
        op: Op,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        let comparison = match op {
            Op::BvUlt => self.lower_unsigned_less(term, lhs, rhs)?,
            Op::BvUle => self.lower_unsigned_less(term, rhs, lhs)?.negated(),
            Op::BvUgt => self.lower_unsigned_less(term, rhs, lhs)?,
            Op::BvUge => self.lower_unsigned_less(term, lhs, rhs)?.negated(),
            Op::BvSlt => self.lower_signed_less(term, lhs, rhs)?,
            Op::BvSle => self.lower_signed_less(term, rhs, lhs)?.negated(),
            Op::BvSgt => self.lower_signed_less(term, rhs, lhs)?,
            Op::BvSge => self.lower_signed_less(term, lhs, rhs)?.negated(),
            _ => unreachable!("caller only passes comparison operators"),
        };
        Ok(vec![comparison])
    }

    fn lower_shift_op(
        &mut self,
        term: TermId,
        op: Op,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [source, amount] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        if source.len() != amount.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(source.len()).unwrap_or(u32::MAX),
                found: amount.len(),
            });
        }

        let sign = *source
            .last()
            .expect("BitVec widths are non-zero by construction");
        let overflow_result = match op {
            Op::BvShl | Op::BvLshr => vec![AigLit::FALSE; source.len()],
            Op::BvAshr => vec![sign; source.len()],
            _ => unreachable!("caller only passes shift operators"),
        };

        let mut result = source.clone();
        let mut stage_shift = 1usize;
        let mut amount_bit = 0usize;
        while stage_shift < source.len() {
            self.poll_deadline()?;
            let shifted = Self::shifted_bits(op, &result, stage_shift);
            result = self.lower_mux_bits(term, amount[amount_bit], &shifted, &result)?;
            stage_shift <<= 1;
            amount_bit += 1;
        }

        let width_constant = constant_lits(
            amount.len(),
            u128::try_from(source.len()).expect("width fits u128"),
        );
        let in_range = self.lower_unsigned_less(term, amount, &width_constant)?;
        result = self.lower_mux_bits(term, in_range, &result, &overflow_result)?;
        Ok(result)
    }

    fn lower_rotate_op(
        term: TermId,
        operands: &[Vec<AigLit>],
        by: u32,
        left: bool,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [source] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 1,
                found: operands.len(),
            });
        };
        let width = source.len();
        let shift = usize::try_from(by).expect("rotate amount fits usize") % width;
        Ok((0..width)
            .map(|index| {
                let source_index = if left {
                    (index + width - shift) % width
                } else {
                    (index + shift) % width
                };
                source[source_index]
            })
            .collect())
    }

    fn lower_equality_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        Ok(vec![self.lower_equal(term, lhs, rhs)?])
    }

    fn lower_ite_op(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [condition, then_bits, else_bits] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 3,
                found: operands.len(),
            });
        };
        let condition = expect_bool(term, condition)?;
        self.lower_mux_bits(term, condition, then_bits, else_bits)
    }

    fn lower_extract(
        term: TermId,
        operands: &[Vec<AigLit>],
        hi: u32,
        lo: u32,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [bits] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 1,
                found: operands.len(),
            });
        };
        Ok(bits[lo as usize..=hi as usize].to_vec())
    }

    fn lower_concat(term: TermId, operands: &[Vec<AigLit>]) -> Result<Vec<AigLit>, BitLowerError> {
        let [high, low] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 2,
                found: operands.len(),
            });
        };
        Ok(low.iter().chain(high).copied().collect())
    }

    fn lower_zero_ext(
        term: TermId,
        operands: &[Vec<AigLit>],
        by: u32,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [source] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 1,
                found: operands.len(),
            });
        };
        let mut bits = source.clone();
        bits.extend(std::iter::repeat_n(AigLit::FALSE, by as usize));
        Ok(bits)
    }

    fn lower_sign_ext(
        term: TermId,
        operands: &[Vec<AigLit>],
        by: u32,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [source] = operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: 1,
                found: operands.len(),
            });
        };
        let mut bits = source.clone();
        let sign = *bits
            .last()
            .expect("BitVec widths are non-zero by construction");
        bits.extend(std::iter::repeat_n(sign, by as usize));
        Ok(bits)
    }

    fn lower_equal(
        &mut self,
        term: TermId,
        lhs: &[AigLit],
        rhs: &[AigLit],
    ) -> Result<AigLit, BitLowerError> {
        if lhs.len() != rhs.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(lhs.len()).unwrap_or(u32::MAX),
                found: rhs.len(),
            });
        }
        let mut equal = AigLit::TRUE;
        for (index, (lhs, rhs)) in lhs.iter().copied().zip(rhs.iter().copied()).enumerate() {
            if index.is_multiple_of(64) {
                self.poll_deadline()?;
            }
            let bit_equal = self.aig.xor(lhs, rhs).negated();
            equal = self.aig.and(equal, bit_equal);
        }
        Ok(equal)
    }

    fn lower_mux_bits(
        &mut self,
        term: TermId,
        condition: AigLit,
        then_bits: &[AigLit],
        else_bits: &[AigLit],
    ) -> Result<Vec<AigLit>, BitLowerError> {
        self.poll_deadline()?;
        if then_bits.len() != else_bits.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(then_bits.len()).unwrap_or(u32::MAX),
                found: else_bits.len(),
            });
        }
        Ok(then_bits
            .iter()
            .copied()
            .zip(else_bits.iter().copied())
            .map(|(then_lit, else_lit)| self.aig.mux(condition, then_lit, else_lit))
            .collect())
    }

    fn lower_increment(&mut self, bits: &[AigLit]) -> Vec<AigLit> {
        let mut carry = AigLit::TRUE;
        bits.iter()
            .copied()
            .map(|bit| {
                let sum = self.aig.xor(bit, carry);
                carry = self.aig.and(bit, carry);
                sum
            })
            .collect()
    }

    fn lower_add_bits(
        &mut self,
        term: TermId,
        lhs: &[AigLit],
        rhs: &[AigLit],
        mut carry: AigLit,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        if lhs.len() != rhs.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(lhs.len()).unwrap_or(u32::MAX),
                found: rhs.len(),
            });
        }
        let mut result = Vec::with_capacity(lhs.len());
        for (index, (lhs, rhs)) in lhs.iter().copied().zip(rhs.iter().copied()).enumerate() {
            if index.is_multiple_of(64) {
                self.poll_deadline()?;
            }
            let pair_sum = self.aig.xor(lhs, rhs);
            let sum = self.aig.xor(pair_sum, carry);
            let carry_from_pair = self.aig.and(lhs, rhs);
            let carry_from_input = self.aig.and(pair_sum, carry);
            carry = self.aig.or(carry_from_pair, carry_from_input);
            result.push(sum);
        }
        Ok(result)
    }

    fn lower_unsigned_less(
        &mut self,
        term: TermId,
        lhs: &[AigLit],
        rhs: &[AigLit],
    ) -> Result<AigLit, BitLowerError> {
        if lhs.len() != rhs.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(lhs.len()).unwrap_or(u32::MAX),
                found: rhs.len(),
            });
        }
        if lhs == rhs || constant_bits_are(rhs, false) || constant_bits_are(lhs, true) {
            return Ok(AigLit::FALSE);
        }
        if let Some(lhs_value) = constant_bits_value(lhs)
            && let Some(rhs_value) = constant_bits_value(rhs)
        {
            return Ok(const_lit(lhs_value < rhs_value));
        }
        if constant_bits_are(lhs, false) {
            return Ok(self.lower_any_bit_set(rhs));
        }
        if constant_bits_are(rhs, true) {
            return Ok(self.lower_any_bit_clear(lhs));
        }
        if let Some(lhs_value) = constant_bits_value(lhs)
            && let Some(next) = lhs_value.checked_add(1)
            && next.is_power_of_two()
        {
            let first_possible_greater_bit =
                usize::try_from(next.trailing_zeros()).expect("trailing zeros fits usize");
            return Ok(self.lower_any_bit_set(&rhs[first_possible_greater_bit..]));
        }
        if let Some(rhs_value) = constant_bits_value(rhs)
            && rhs_value.is_power_of_two()
        {
            let first_forbidden_bit =
                usize::try_from(rhs_value.trailing_zeros()).expect("trailing zeros fits usize");
            return Ok(self.lower_all_bits_clear(&lhs[first_forbidden_bit..]));
        }
        let mut less = AigLit::FALSE;
        let mut equal = AigLit::TRUE;
        for index in (0..lhs.len()).rev() {
            if index.is_multiple_of(64) {
                self.poll_deadline()?;
            }
            let lhs = lhs[index];
            let rhs = rhs[index];
            let bit_less = self.aig.and(lhs.negated(), rhs);
            let active_less = self.aig.and(equal, bit_less);
            less = self.aig.or(less, active_less);
            if index > 0 {
                let bits_equal = self.aig.xor(lhs, rhs).negated();
                equal = self.aig.and(equal, bits_equal);
            }
        }
        Ok(less)
    }

    fn lower_signed_less(
        &mut self,
        term: TermId,
        lhs: &[AigLit],
        rhs: &[AigLit],
    ) -> Result<AigLit, BitLowerError> {
        let lhs_sign = *lhs
            .last()
            .expect("BitVec widths are non-zero by construction");
        let rhs_sign = *rhs
            .last()
            .expect("BitVec widths are non-zero by construction");
        match (constant_lit_value(lhs_sign), constant_lit_value(rhs_sign)) {
            (Some(false), Some(true)) => return Ok(AigLit::FALSE),
            (Some(true), Some(false)) => return Ok(AigLit::TRUE),
            (Some(_), Some(_)) => {
                return self.lower_unsigned_less(
                    term,
                    &lhs[..lhs.len() - 1],
                    &rhs[..rhs.len() - 1],
                );
            }
            (None, Some(false)) if constant_bits_are(&rhs[..rhs.len() - 1], false) => {
                return Ok(lhs_sign);
            }
            (None, Some(false)) => {
                let magnitude_less =
                    self.lower_unsigned_less(term, &lhs[..lhs.len() - 1], &rhs[..rhs.len() - 1])?;
                return Ok(self.aig.or(lhs_sign, magnitude_less));
            }
            (None, Some(true)) => {
                let magnitude_less =
                    self.lower_unsigned_less(term, &lhs[..lhs.len() - 1], &rhs[..rhs.len() - 1])?;
                return Ok(self.aig.and(lhs_sign, magnitude_less));
            }
            (Some(false), None) => {
                let magnitude_less =
                    self.lower_unsigned_less(term, &lhs[..lhs.len() - 1], &rhs[..rhs.len() - 1])?;
                return Ok(self.aig.and(rhs_sign.negated(), magnitude_less));
            }
            (Some(true), None) => {
                let magnitude_less =
                    self.lower_unsigned_less(term, &lhs[..lhs.len() - 1], &rhs[..rhs.len() - 1])?;
                return Ok(self.aig.or(rhs_sign.negated(), magnitude_less));
            }
            (None, None) => {}
        }
        let magnitude_less =
            self.lower_unsigned_less(term, &lhs[..lhs.len() - 1], &rhs[..rhs.len() - 1])?;
        let signs_equal = self.aig.xor(lhs_sign, rhs_sign).negated();
        let lhs_negative_rhs_nonnegative = self.aig.and(lhs_sign, rhs_sign.negated());
        let same_sign_less = self.aig.and(signs_equal, magnitude_less);
        Ok(self.aig.or(lhs_negative_rhs_nonnegative, same_sign_less))
    }

    fn shifted_bits(op: Op, source: &[AigLit], shift: usize) -> Vec<AigLit> {
        let sign = *source
            .last()
            .expect("BitVec widths are non-zero by construction");
        (0..source.len())
            .map(|index| match op {
                Op::BvShl => index
                    .checked_sub(shift)
                    .map_or(AigLit::FALSE, |source_index| source[source_index]),
                Op::BvLshr => source.get(index + shift).copied().unwrap_or(AigLit::FALSE),
                Op::BvAshr => source.get(index + shift).copied().unwrap_or(sign),
                _ => unreachable!("caller only passes shift operators"),
            })
            .collect()
    }

    fn lower_pairwise(
        &mut self,
        term: TermId,
        operands: &[Vec<AigLit>],
        build: impl Fn(&mut Aig, AigLit, AigLit) -> AigLit,
    ) -> Result<Vec<AigLit>, BitLowerError> {
        let [lhs, rhs] = &operands else {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: self.expected_width(term),
                found: operands.len(),
            });
        };
        if lhs.len() != rhs.len() {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected: u32::try_from(lhs.len()).unwrap_or(u32::MAX),
                found: rhs.len(),
            });
        }
        let mut result = Vec::with_capacity(lhs.len());
        for (index, (lhs, rhs)) in lhs.iter().copied().zip(rhs.iter().copied()).enumerate() {
            if index.is_multiple_of(64) {
                self.poll_deadline()?;
            }
            result.push(build(&mut self.aig, lhs, rhs));
        }
        Ok(result)
    }

    fn lower_any_bit_set(&mut self, bits: &[AigLit]) -> AigLit {
        bits.iter()
            .copied()
            .fold(AigLit::FALSE, |acc, bit| self.aig.or(acc, bit))
    }

    fn lower_any_bit_clear(&mut self, bits: &[AigLit]) -> AigLit {
        bits.iter()
            .copied()
            .fold(AigLit::FALSE, |acc, bit| self.aig.or(acc, bit.negated()))
    }

    fn lower_all_bits_clear(&mut self, bits: &[AigLit]) -> AigLit {
        self.lower_any_bit_set(bits).negated()
    }

    fn record(&mut self, term: TermId, bits: Vec<AigLit>) -> Result<(), BitLowerError> {
        self.check_width(term, &bits)?;
        if self.profiling_enabled {
            self.incremental_stats.terms_lowered =
                self.incremental_stats.terms_lowered.saturating_add(1);
            self.incremental_stats.term_bit_bindings_written = self
                .incremental_stats
                .term_bit_bindings_written
                .saturating_add(usize_to_u64_saturating(bits.len()));
        }
        let start = self.term_bits.len();
        for (index, &literal) in bits.iter().enumerate() {
            let bit_index = u32::try_from(index).expect("bit index fits u32");
            let binding = TermBitBinding {
                term,
                bit_index,
                literal,
            };
            self.term_bits.push(binding);
        }
        let range = self
            .term_bit_ranges
            .get_mut(term.index())
            .expect("term range index fits the source arena");
        debug_assert!(range.is_none(), "term is recorded at most once");
        *range = Some(TermBitRange {
            start,
            len: bits.len(),
        });
        self.memo.insert(term, bits);
        Ok(())
    }

    fn record_sparse(
        &mut self,
        term: TermId,
        bits: &[Option<AigLit>],
    ) -> Result<(), BitLowerError> {
        let expected = self.expected_width(term);
        if bits.len() != expected as usize {
            return Err(BitLowerError::BitWidthMismatch {
                term,
                expected,
                found: bits.len(),
            });
        }
        let start = self.term_bits.len();
        for (index, literal) in bits.iter().copied().enumerate() {
            let Some(literal) = literal else {
                continue;
            };
            self.term_bits.push(TermBitBinding {
                term,
                bit_index: u32::try_from(index).expect("bit index fits u32"),
                literal,
            });
        }
        let len = self.term_bits.len() - start;
        let range = self
            .term_bit_ranges
            .get_mut(term.index())
            .expect("term range index fits the source arena");
        debug_assert!(range.is_none(), "term is recorded at most once");
        *range = Some(TermBitRange { start, len });
        Ok(())
    }

    fn check_width(&self, term: TermId, bits: &[AigLit]) -> Result<(), BitLowerError> {
        let expected = self.expected_width(term);
        if bits.len() == expected as usize {
            Ok(())
        } else {
            Err(BitLowerError::BitWidthMismatch {
                term,
                expected,
                found: bits.len(),
            })
        }
    }

    fn expected_width(&self, term: TermId) -> u32 {
        match self.arena.sort_of(term) {
            Sort::Bool => 1,
            Sort::BitVec(width) => width,
            Sort::Float { exp, sig } => exp + sig,
            Sort::Array { .. } => {
                unreachable!("array terms are eliminated before bit lowering (ADR-0010)")
            }
            Sort::Int => {
                unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
            }
            Sort::Real => {
                unreachable!("real terms are rejected before bit lowering (ADR-0015)")
            }
            Sort::Datatype(_) => {
                unreachable!("datatype terms are rejected before bit lowering (ADR-0022)")
            }
            Sort::Uninterpreted(_) => {
                unreachable!("uninterpreted-sort terms are rejected before bit lowering")
            }
            Sort::Seq(_) => {
                unreachable!("sequence terms are rejected before bit lowering (P2.7)")
            }
        }
    }
}

fn const_lit(value: bool) -> AigLit {
    if value { AigLit::TRUE } else { AigLit::FALSE }
}

fn constant_lit_value(lit: AigLit) -> Option<bool> {
    if lit == AigLit::FALSE {
        Some(false)
    } else if lit == AigLit::TRUE {
        Some(true)
    } else {
        None
    }
}

fn constant_bits_are(bits: &[AigLit], value: bool) -> bool {
    bits.iter()
        .copied()
        .all(|bit| constant_lit_value(bit) == Some(value))
}

fn constant_bits_value(bits: &[AigLit]) -> Option<u128> {
    if bits.len() > u128::BITS as usize {
        return None;
    }
    let mut value = 0u128;
    for (index, bit) in bits.iter().copied().enumerate() {
        if constant_lit_value(bit)? {
            value |= 1u128 << index;
        }
    }
    Some(value)
}

fn structural_bit_demand(
    arena: &TermArena,
    roots: &[TermId],
    deadline: Option<Instant>,
) -> Result<BitDemandStats, BitLowerError> {
    Ok(DenseBitDemand::compute(arena, roots, deadline)?.stats)
}

const INLINE_DEMAND_RANGES: usize = 4;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct BitRange {
    start: u32,
    end: u32,
}

impl BitRange {
    fn new(start: u32, end: u32) -> Self {
        debug_assert!(start < end);
        Self { start, end }
    }

    fn len(self) -> u64 {
        u64::from(self.end - self.start)
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct InlineRangeList {
    items: [BitRange; INLINE_DEMAND_RANGES],
    len: u8,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum InlineBitDemand {
    #[default]
    None,
    Ranges(InlineRangeList),
    Full,
}

#[derive(Debug, Clone, Copy, Default)]
struct RangeInsertResult {
    changed: bool,
    merges: u64,
    promoted: bool,
}

impl InlineBitDemand {
    fn is_none(self) -> bool {
        matches!(self, Self::None)
    }

    fn is_full(self) -> bool {
        matches!(self, Self::Full)
    }

    fn ranges(self, width: u32) -> impl Iterator<Item = BitRange> {
        let list = match self {
            Self::None => InlineRangeList::default(),
            Self::Ranges(list) => list,
            Self::Full => {
                let mut list = InlineRangeList::default();
                if width > 0 {
                    list.items[0] = BitRange::new(0, width);
                    list.len = 1;
                }
                list
            }
        };
        list.items.into_iter().take(usize::from(list.len))
    }

    fn bit_count(self, width: u32) -> u64 {
        self.ranges(width).map(BitRange::len).sum()
    }

    fn insert(&mut self, range: BitRange, width: u32) -> RangeInsertResult {
        let range = BitRange {
            start: range.start.min(width),
            end: range.end.min(width),
        };
        if range.start >= range.end || self.is_full() {
            return RangeInsertResult::default();
        }
        if range.start == 0 && range.end == width {
            let changed = !self.is_full();
            *self = Self::Full;
            return RangeInsertResult {
                changed,
                ..RangeInsertResult::default()
            };
        }

        let old = *self;
        let mut candidates = [BitRange::default(); INLINE_DEMAND_RANGES + 1];
        let mut candidate_len = 0usize;
        if let Self::Ranges(list) = old {
            let len = usize::from(list.len);
            candidates[..len].copy_from_slice(&list.items[..len]);
            candidate_len = len;
        }
        candidates[candidate_len] = range;
        candidate_len += 1;
        candidates[..candidate_len].sort_unstable_by_key(|item| (item.start, item.end));

        let mut merged = [BitRange::default(); INLINE_DEMAND_RANGES];
        let mut merged_len = 0usize;
        let mut merge_count = 0u64;
        for candidate in candidates.into_iter().take(candidate_len) {
            if merged_len > 0 && candidate.start <= merged[merged_len - 1].end {
                let previous = &mut merged[merged_len - 1];
                previous.end = previous.end.max(candidate.end);
                merge_count = merge_count.saturating_add(1);
                continue;
            }
            if merged_len == INLINE_DEMAND_RANGES {
                *self = Self::Full;
                return RangeInsertResult {
                    changed: true,
                    merges: merge_count,
                    promoted: true,
                };
            }
            merged[merged_len] = candidate;
            merged_len += 1;
        }
        *self = Self::Ranges(InlineRangeList {
            items: merged,
            len: u8::try_from(merged_len).expect("inline demand range count fits u8"),
        });
        RangeInsertResult {
            changed: *self != old,
            merges: merge_count,
            promoted: false,
        }
    }
}

struct DemandAdmissionScreen {
    reachable: Vec<bool>,
    candidate: bool,
    stats: BitDemandStats,
}

impl DemandAdmissionScreen {
    fn compute(
        arena: &TermArena,
        roots: &[TermId],
        deadline: Option<Instant>,
    ) -> Result<Self, BitLowerError> {
        let start = Instant::now();
        let mut reachable = vec![false; arena.len()];
        let mut uses = vec![0u32; arena.len()];
        let mut stack = roots.to_vec();
        for &root in roots {
            uses[root.index()] = uses[root.index()].saturating_add(1);
        }
        while let Some(term) = stack.pop() {
            poll_analysis_deadline(deadline)?;
            if reachable[term.index()] {
                continue;
            }
            reachable[term.index()] = true;
            if let TermNode::App { args, .. } = arena.node(term) {
                for &arg in args {
                    debug_assert!(arg.index() < term.index(), "term arena must be topological");
                    uses[arg.index()] = uses[arg.index()].saturating_add(1);
                    stack.push(arg);
                }
            }
        }

        let symbol_count = arena.symbols().count();
        let mut reachable_symbols = vec![false; symbol_count];
        let mut stats = BitDemandStats {
            profile_complete: true,
            ..BitDemandStats::default()
        };
        let mut candidate = false;
        let mut slice_uses = vec![0u32; arena.len()];
        let mut slice_min = vec![u32::MAX; arena.len()];
        let mut slice_max = vec![0u32; arena.len()];
        for (term_index, &is_reachable) in reachable.iter().enumerate() {
            if !is_reachable {
                continue;
            }
            poll_analysis_deadline(deadline)?;
            let term = arena
                .term_by_index(term_index)
                .expect("dense term index belongs to the arena");
            stats.term_bits_available = stats
                .term_bits_available
                .saturating_add(usize_to_u64_saturating(sort_width(arena.sort_of(term))));
            match arena.node(term) {
                TermNode::Symbol(symbol) => {
                    if !reachable_symbols[symbol.index()] {
                        reachable_symbols[symbol.index()] = true;
                        stats.symbol_bits_available =
                            stats
                                .symbol_bits_available
                                .saturating_add(usize_to_u64_saturating(sort_width(
                                    arena.symbol(*symbol).1,
                                )));
                    }
                }
                TermNode::App {
                    op: Op::Extract { hi, lo },
                    args,
                } => {
                    let source = args[0];
                    let source_width = u32::try_from(sort_width(arena.sort_of(source)))
                        .expect("lowerable term width fits u32");
                    let result_width = hi - lo + 1;
                    if result_width < source_width {
                        candidate = true;
                        slice_uses[source.index()] = slice_uses[source.index()].saturating_add(1);
                        slice_min[source.index()] = slice_min[source.index()].min(*lo);
                        slice_max[source.index()] =
                            slice_max[source.index()].max(hi.saturating_add(1));
                    }
                }
                TermNode::App { .. }
                | TermNode::BoolConst(_)
                | TermNode::BvConst { .. }
                | TermNode::WideBvConst(_)
                | TermNode::IntConst(_)
                | TermNode::RealConst(_) => {}
            }
        }

        for term_index in 0..arena.len() {
            if slice_uses[term_index] == 0 || slice_uses[term_index] != uses[term_index] {
                continue;
            }
            let term = arena
                .term_by_index(term_index)
                .expect("dense term index belongs to the arena");
            let width = u32::try_from(sort_width(arena.sort_of(term)))
                .expect("lowerable term width fits u32");
            let live_envelope = slice_max[term_index].saturating_sub(slice_min[term_index]);
            stats.estimated_bits_avoided = stats
                .estimated_bits_avoided
                .saturating_add(u64::from(width.saturating_sub(live_envelope)));
        }
        stats.admission = start.elapsed();
        Ok(Self {
            reachable,
            candidate,
            stats,
        })
    }

    fn rejection(&self, policy: RangeDemandPolicy) -> Option<RangeDemandDecision> {
        if !self.candidate {
            return Some(RangeDemandDecision::NoCandidate);
        }
        let enough_size = self.stats.term_bits_available >= policy.min_term_bits_available;
        let enough_savings = meets_savings_floor(
            self.stats.term_bits_available,
            self.stats.estimated_bits_avoided,
            policy.min_estimated_bits_avoided,
            policy.min_estimated_avoided_percent,
        );
        (!enough_size || !enough_savings).then_some(RangeDemandDecision::InsufficientEstimate)
    }

    fn into_stats(mut self, decision: RangeDemandDecision) -> BitDemandStats {
        self.stats.range_decision = decision;
        self.stats
    }
}

struct RangeDemandPlan {
    term_demands: Vec<InlineBitDemand>,
    stats: BitDemandStats,
}

impl RangeDemandPlan {
    // This is a flat, auditable per-operator transfer table. Keeping the rules
    // together makes comparison with `propagate_bit_demand` less error-prone.
    #[allow(clippy::too_many_lines)]
    fn compute(
        arena: &TermArena,
        roots: &[TermId],
        deadline: Option<Instant>,
        policy: RangeDemandPolicy,
        screen: &DemandAdmissionScreen,
    ) -> Result<Self, Box<BitDemandStats>> {
        let analysis_start = Instant::now();
        let mut stats = screen.stats;
        stats.analysis_work_budget = policy.analysis_work_budget;
        let mut demands = vec![InlineBitDemand::None; arena.len()];
        let mut work = 0u64;

        for &root in roots {
            let width = term_width_u32(arena, root);
            if !add_range_demand(
                arena,
                root,
                BitRange::new(0, width),
                &mut demands,
                &mut stats,
                &mut work,
                policy.analysis_work_budget,
            ) {
                return Err(Box::new(finish_budget_fallback(
                    stats,
                    analysis_start,
                    work,
                )));
            }
        }

        for term_index in (0..arena.len()).rev() {
            let demand = demands[term_index];
            if demand.is_none() {
                continue;
            }
            if !charge_work(&mut work, policy.analysis_work_budget, 1) {
                return Err(Box::new(finish_budget_fallback(
                    stats,
                    analysis_start,
                    work,
                )));
            }
            poll_analysis_deadline(deadline).map_err(|_| {
                stats.analysis = analysis_start.elapsed();
                Box::new(stats)
            })?;
            let term = arena
                .term_by_index(term_index)
                .expect("dense term index belongs to the arena");
            debug_assert!(screen.reachable[term_index]);
            let TermNode::App { op, args } = arena.node(term) else {
                continue;
            };
            let term_width = term_width_u32(arena, term);
            let mut add = |arg: TermId, range: BitRange| {
                debug_assert!(arg.index() < term.index(), "term arena must be topological");
                add_range_demand(
                    arena,
                    arg,
                    range,
                    &mut demands,
                    &mut stats,
                    &mut work,
                    policy.analysis_work_budget,
                )
            };
            let mut complete = true;
            match *op {
                Op::Extract { lo, .. } => {
                    for range in demand.ranges(term_width) {
                        complete &= add(args[0], BitRange::new(range.start + lo, range.end + lo));
                    }
                }
                Op::Concat => {
                    let low_width = term_width_u32(arena, args[1]);
                    for range in demand.ranges(term_width) {
                        if range.start < low_width {
                            complete &= add(
                                args[1],
                                BitRange::new(range.start, range.end.min(low_width)),
                            );
                        }
                        if range.end > low_width {
                            complete &= add(
                                args[0],
                                BitRange::new(
                                    range.start.max(low_width) - low_width,
                                    range.end - low_width,
                                ),
                            );
                        }
                    }
                }
                Op::ZeroExt { .. } => {
                    let source_width = term_width_u32(arena, args[0]);
                    for range in demand.ranges(term_width) {
                        if range.start < source_width {
                            complete &= add(
                                args[0],
                                BitRange::new(range.start, range.end.min(source_width)),
                            );
                        }
                    }
                }
                Op::SignExt { .. } => {
                    let source_width = term_width_u32(arena, args[0]);
                    for range in demand.ranges(term_width) {
                        if range.start < source_width {
                            complete &= add(
                                args[0],
                                BitRange::new(range.start, range.end.min(source_width)),
                            );
                        }
                        if range.end > source_width {
                            complete &= add(args[0], BitRange::new(source_width - 1, source_width));
                        }
                    }
                }
                Op::BoolNot
                | Op::BoolAnd
                | Op::BoolOr
                | Op::BoolXor
                | Op::BoolImplies
                | Op::BvNot
                | Op::BvAnd
                | Op::BvOr
                | Op::BvXor
                | Op::BvNand
                | Op::BvNor
                | Op::BvXnor
                | Op::FpFromBits { .. } => {
                    for range in demand.ranges(term_width) {
                        for &arg in args {
                            complete &= add(arg, range);
                        }
                    }
                }
                Op::Ite => {
                    complete &= add(args[0], BitRange::new(0, 1));
                    for range in demand.ranges(term_width) {
                        complete &= add(args[1], range);
                        complete &= add(args[2], range);
                    }
                }
                Op::RotateLeft { by } => {
                    let shift = by % term_width;
                    for range in demand.ranges(term_width) {
                        for mapped in shifted_ranges(range, term_width - shift, term_width) {
                            complete &= add(args[0], mapped);
                        }
                    }
                }
                Op::RotateRight { by } => {
                    let shift = by % term_width;
                    for range in demand.ranges(term_width) {
                        for mapped in shifted_ranges(range, shift, term_width) {
                            complete &= add(args[0], mapped);
                        }
                    }
                }
                _ => {
                    for &arg in args {
                        complete &= add(arg, BitRange::new(0, term_width_u32(arena, arg)));
                    }
                }
            }
            if !complete {
                return Err(Box::new(finish_budget_fallback(
                    stats,
                    analysis_start,
                    work,
                )));
            }
        }

        for (term_index, &term_demand) in demands.iter().enumerate() {
            if term_demand.is_none() {
                continue;
            }
            let term = arena
                .term_by_index(term_index)
                .expect("dense term index belongs to the arena");
            let count = term_demand.bit_count(term_width_u32(arena, term));
            stats.term_bits_demanded = stats.term_bits_demanded.saturating_add(count);
            if matches!(arena.node(term), TermNode::Symbol(_)) {
                stats.symbol_bits_demanded = stats.symbol_bits_demanded.saturating_add(count);
            }
        }
        stats.analysis = analysis_start.elapsed();
        stats.analysis_work = work;
        let exact_avoided = stats
            .term_bits_available
            .saturating_sub(stats.term_bits_demanded);
        if !meets_savings_floor(
            stats.term_bits_available,
            exact_avoided,
            policy.min_exact_bits_avoided,
            policy.min_exact_avoided_percent,
        ) {
            stats.range_decision = RangeDemandDecision::InsufficientExactSavings;
            return Err(Box::new(stats));
        }
        Ok(Self {
            term_demands: demands,
            stats,
        })
    }
}

fn add_range_demand(
    arena: &TermArena,
    term: TermId,
    range: BitRange,
    demands: &mut [InlineBitDemand],
    stats: &mut BitDemandStats,
    work: &mut u64,
    budget: u64,
) -> bool {
    if !charge_work(work, budget, 1) {
        return false;
    }
    let requested = range.len();
    stats.term_bit_requests = stats.term_bit_requests.saturating_add(requested);
    if matches!(arena.node(term), TermNode::Symbol(_)) {
        stats.symbol_bit_requests = stats.symbol_bit_requests.saturating_add(requested);
    }
    let update = demands[term.index()].insert(range, term_width_u32(arena, term));
    stats.range_merges = stats.range_merges.saturating_add(update.merges);
    if update.promoted {
        stats.range_promotions = stats.range_promotions.saturating_add(1);
    }
    if update.changed && !charge_work(work, budget, 1) {
        return false;
    }
    true
}

fn finish_budget_fallback(mut stats: BitDemandStats, start: Instant, work: u64) -> BitDemandStats {
    stats.analysis = start.elapsed();
    stats.analysis_work = work;
    stats.range_decision = RangeDemandDecision::AnalysisBudgetExceeded;
    stats
}

fn charge_work(work: &mut u64, budget: u64, amount: u64) -> bool {
    let next = work.saturating_add(amount);
    if next > budget {
        false
    } else {
        *work = next;
        true
    }
}

fn meets_savings_floor(available: u64, avoided: u64, minimum: u64, percent: u8) -> bool {
    let percent = u64::from(percent.min(100));
    avoided >= minimum
        && u128::from(avoided).saturating_mul(100)
            >= u128::from(available).saturating_mul(u128::from(percent))
}

fn term_width_u32(arena: &TermArena, term: TermId) -> u32 {
    u32::try_from(sort_width(arena.sort_of(term))).expect("lowerable term width fits u32")
}

fn shifted_ranges(range: BitRange, shift: u32, width: u32) -> impl Iterator<Item = BitRange> {
    let mut result = InlineRangeList::default();
    let shifted_start = range.start + shift;
    let shifted_end = range.end + shift;
    if shifted_start < width {
        result.items[0] = BitRange::new(shifted_start, shifted_end.min(width));
        result.len = 1;
        if shifted_end > width {
            result.items[1] = BitRange::new(0, shifted_end - width);
            result.len = 2;
        }
    } else {
        result.items[0] = BitRange::new(shifted_start - width, shifted_end - width);
        result.len = 1;
    }
    result.items.into_iter().take(usize::from(result.len))
}

struct DenseBitDemand {
    term_bits: Vec<Vec<bool>>,
    stats: BitDemandStats,
}

impl DenseBitDemand {
    fn compute(
        arena: &TermArena,
        roots: &[TermId],
        deadline: Option<Instant>,
    ) -> Result<Self, BitLowerError> {
        let start = Instant::now();
        let mut stats = BitDemandStats {
            profile_complete: true,
            ..BitDemandStats::default()
        };
        let symbol_count = arena.symbols().count();
        let mut reachable_terms = vec![false; arena.len()];
        let mut reachable_symbols = vec![false; symbol_count];
        let mut reachable_stack = roots.to_vec();
        while let Some(term) = reachable_stack.pop() {
            poll_analysis_deadline(deadline)?;
            if reachable_terms[term.index()] {
                continue;
            }
            reachable_terms[term.index()] = true;
            stats.term_bits_available = stats
                .term_bits_available
                .saturating_add(usize_to_u64_saturating(sort_width(arena.sort_of(term))));
            match arena.node(term) {
                TermNode::Symbol(symbol) => {
                    if !reachable_symbols[symbol.index()] {
                        reachable_symbols[symbol.index()] = true;
                        stats.symbol_bits_available =
                            stats
                                .symbol_bits_available
                                .saturating_add(usize_to_u64_saturating(sort_width(
                                    arena.symbol(*symbol).1,
                                )));
                    }
                }
                TermNode::App { args, .. } => reachable_stack.extend(args.iter().copied()),
                TermNode::BoolConst(_)
                | TermNode::BvConst { .. }
                | TermNode::WideBvConst(_)
                | TermNode::IntConst(_)
                | TermNode::RealConst(_) => {}
            }
        }

        let mut demanded_term_bits = vec![Vec::new(); arena.len()];
        let mut demanded_symbol_bits = vec![Vec::new(); symbol_count];
        let mut demand_stack = Vec::new();
        for &root in roots {
            push_all_term_bits(arena, root, &mut demand_stack);
        }
        while let Some((term, bit)) = demand_stack.pop() {
            poll_analysis_deadline(deadline)?;
            stats.term_bit_requests = stats.term_bit_requests.saturating_add(1);
            if matches!(arena.node(term), TermNode::Symbol(_)) {
                stats.symbol_bit_requests = stats.symbol_bit_requests.saturating_add(1);
            }
            let width = sort_width(arena.sort_of(term));
            let term_bits = &mut demanded_term_bits[term.index()];
            if term_bits.is_empty() {
                *term_bits = vec![false; width];
            }
            let bit_index = usize::try_from(bit).expect("lowerable bit index fits usize");
            if term_bits[bit_index] {
                continue;
            }
            term_bits[bit_index] = true;
            stats.term_bits_demanded = stats.term_bits_demanded.saturating_add(1);
            if let TermNode::Symbol(symbol) = arena.node(term) {
                let symbol_width = sort_width(arena.symbol(*symbol).1);
                let symbol_bits = &mut demanded_symbol_bits[symbol.index()];
                if symbol_bits.is_empty() {
                    *symbol_bits = vec![false; symbol_width];
                }
                if !symbol_bits[bit_index] {
                    symbol_bits[bit_index] = true;
                    stats.symbol_bits_demanded = stats.symbol_bits_demanded.saturating_add(1);
                }
            }
            propagate_bit_demand(arena, term, bit, &mut demand_stack);
        }
        stats.analysis = start.elapsed();
        Ok(Self {
            term_bits: demanded_term_bits,
            stats,
        })
    }

    fn term_bits(&self, term: TermId) -> &[bool] {
        &self.term_bits[term.index()]
    }
}

fn poll_analysis_deadline(deadline: Option<Instant>) -> Result<(), BitLowerError> {
    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
        Err(BitLowerError::DeadlineExceeded)
    } else {
        Ok(())
    }
}

fn is_demand_local_op(op: Op) -> bool {
    matches!(
        op,
        Op::BoolNot
            | Op::BoolAnd
            | Op::BoolOr
            | Op::BoolXor
            | Op::BoolImplies
            | Op::BvNot
            | Op::BvAnd
            | Op::BvOr
            | Op::BvXor
            | Op::BvNand
            | Op::BvNor
            | Op::BvXnor
            | Op::Ite
            | Op::Extract { .. }
            | Op::Concat
            | Op::ZeroExt { .. }
            | Op::SignExt { .. }
            | Op::RotateLeft { .. }
            | Op::RotateRight { .. }
            | Op::FpFromBits { .. }
    )
}

fn propagate_bit_demand(arena: &TermArena, term: TermId, bit: u32, stack: &mut Vec<(TermId, u32)>) {
    let TermNode::App { op, args } = arena.node(term) else {
        return;
    };
    match *op {
        Op::Extract { lo, .. } => stack.push((args[0], bit + lo)),
        Op::Concat => {
            let low_width = u32::try_from(sort_width(arena.sort_of(args[1])))
                .expect("lowerable term width fits u32");
            if bit < low_width {
                stack.push((args[1], bit));
            } else {
                stack.push((args[0], bit - low_width));
            }
        }
        Op::ZeroExt { .. } => {
            let source_width = u32::try_from(sort_width(arena.sort_of(args[0])))
                .expect("lowerable term width fits u32");
            if bit < source_width {
                stack.push((args[0], bit));
            }
        }
        Op::SignExt { .. } => {
            let source_width = u32::try_from(sort_width(arena.sort_of(args[0])))
                .expect("lowerable term width fits u32");
            stack.push((args[0], bit.min(source_width - 1)));
        }
        Op::BoolNot
        | Op::BoolAnd
        | Op::BoolOr
        | Op::BoolXor
        | Op::BoolImplies
        | Op::BvNot
        | Op::BvAnd
        | Op::BvOr
        | Op::BvXor
        | Op::BvNand
        | Op::BvNor
        | Op::BvXnor
        | Op::FpFromBits { .. } => {
            stack.extend(args.iter().map(|arg| (*arg, bit)));
        }
        Op::Ite => {
            stack.push((args[0], 0));
            stack.push((args[1], bit));
            stack.push((args[2], bit));
        }
        Op::RotateLeft { by } => {
            let width = u32::try_from(sort_width(arena.sort_of(args[0])))
                .expect("lowerable term width fits u32");
            let shift = by % width;
            stack.push((args[0], (bit + width - shift) % width));
        }
        Op::RotateRight { by } => {
            let width = u32::try_from(sort_width(arena.sort_of(args[0])))
                .expect("lowerable term width fits u32");
            let shift = by % width;
            stack.push((args[0], (bit + shift) % width));
        }
        _ => {
            for &arg in args {
                push_all_term_bits(arena, arg, stack);
            }
        }
    }
}

fn push_all_term_bits(arena: &TermArena, term: TermId, stack: &mut Vec<(TermId, u32)>) {
    let width =
        u32::try_from(sort_width(arena.sort_of(term))).expect("lowerable term width fits u32");
    stack.extend((0..width).map(|bit| (term, bit)));
}

fn usize_to_u64_saturating(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}

fn sort_width(sort: Sort) -> usize {
    match sort {
        Sort::Bool => 1,
        Sort::BitVec(width) => width as usize,
        Sort::Float { exp, sig } => (exp + sig) as usize,
        Sort::Array { .. } => {
            unreachable!("array terms are eliminated before bit lowering (ADR-0010)")
        }
        Sort::Int => {
            unreachable!("integer terms are rejected before bit lowering (ADR-0014)")
        }
        Sort::Real => {
            unreachable!("real terms are rejected before bit lowering (ADR-0015)")
        }
        Sort::Datatype(_) => {
            unreachable!("datatype terms are rejected before bit lowering (ADR-0022)")
        }
        Sort::Uninterpreted(_) => {
            unreachable!("uninterpreted-sort terms are rejected before bit lowering")
        }
        Sort::Seq(_) => {
            unreachable!("sequence terms are rejected before bit lowering (P2.7)")
        }
    }
}

fn aig_lit_from_node_values(lit: AigLit, node_values: &[bool]) -> Result<bool, BitLowerError> {
    let value = node_values.get(lit.node().index()).copied().ok_or(
        BitLowerError::AigValueLengthMismatch {
            expected: lit.node().index() + 1,
            found: node_values.len(),
        },
    )?;
    Ok(value ^ lit.is_inverted())
}

fn constant_lits(width: usize, value: u128) -> Vec<AigLit> {
    // `width` may exceed 128 (wide bit-vectors), while `value` always fits a
    // `u128` (callers pass a bit-width). Bits at position `>= 128` of a `u128`
    // are zero, so guard the shift to avoid a shift-amount overflow panic.
    (0..width)
        .map(|bit| const_lit(bit < 128 && ((value >> bit) & 1) == 1))
        .collect()
}

fn expect_bool(term: TermId, bits: &[AigLit]) -> Result<AigLit, BitLowerError> {
    if let [bit] = bits {
        Ok(*bit)
    } else {
        Err(BitLowerError::BitWidthMismatch {
            term,
            expected: 1,
            found: bits.len(),
        })
    }
}

fn expect_two(
    term: TermId,
    operands: &[Vec<AigLit>],
) -> Result<(&[AigLit], &[AigLit]), BitLowerError> {
    if let [lhs, rhs] = operands {
        Ok((lhs, rhs))
    } else {
        Err(BitLowerError::BitWidthMismatch {
            term,
            expected: 2,
            found: operands.len(),
        })
    }
}

fn is_unsupported_op(op: Op) -> bool {
    // The full scalar QF_BV operator set lowers; array operations are eliminated
    // to QF_BV before lowering (ADR-0010) and uninterpreted-function
    // applications via Ackermann reduction (ADR-0013), so neither is supported
    // by the bit-blaster directly.
    matches!(
        op,
        Op::Select
            | Op::Store
            | Op::ConstArray { .. }
            | Op::IntToReal
            | Op::RealToInt
            | Op::RealIsInt
            | Op::Bv2Nat
            | Op::Int2Bv { .. }
            | Op::Apply(_)
            | Op::IntNeg
            | Op::IntAdd
            | Op::IntSub
            | Op::IntMul
            | Op::IntLt
            | Op::IntLe
            | Op::IntGt
            | Op::IntGe
            | Op::RealNeg
            | Op::RealAdd
            | Op::RealSub
            | Op::RealMul
            | Op::RealDiv
            | Op::RealLt
            | Op::RealLe
            | Op::RealGt
            | Op::RealGe
            | Op::Forall(_)
            | Op::Exists(_)
            | Op::DtConstruct { .. }
            | Op::DtSelect { .. }
            | Op::DtTest(_)
    )
}

/// Evaluates an original term and its lowered AIG root under the same
/// assignment.
///
/// This helper is intended for tests and future differential harnesses.
///
/// # Errors
///
/// Returns [`BitLowerError`] if lowering, IR evaluation, or AIG evaluation
/// fails.
pub fn eval_lowered_once(
    arena: &TermArena,
    term: TermId,
    assignment: &Assignment,
) -> Result<(Value, Value), BitLowerError> {
    let lowering = lower_terms(arena, &[term])?;
    let expected = eval(arena, term, assignment)?;
    let lowered = lowering.evaluate_root(0, assignment)?;
    Ok((expected, lowered))
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, Instant};

    use axeyum_aig::{AigLit, AigNode};
    use axeyum_ir::{Assignment, IrError, Sort, TermArena, TermId, Value, eval};

    use super::{
        BitLowerError, BitLowering, BitLoweringMemoRepresentation, BitLoweringMemoStats,
        IncrementalLowering, RangeDemandDecision, RangeDemandPolicy, eval_lowered_once,
        lower_terms, lower_terms_demanded, lower_terms_demanded_with_deadline,
        lower_terms_profiled, lower_terms_range_demanded, lower_terms_range_demanded_with_deadline,
        usize_to_u64_saturating,
    };

    fn bv(width: u32, value: u128) -> Value {
        Value::Bv { width, value }
    }

    fn evaluated_aig_nodes(lowering: &BitLowering, assignment: &Assignment) -> Vec<bool> {
        let inputs = lowering.input_values(assignment).unwrap();
        let mut values = vec![false; lowering.aig().node_count()];
        for (node_id, node) in lowering.aig().nodes() {
            values[node_id.index()] = match node {
                AigNode::ConstFalse => false,
                AigNode::Input(input) => inputs[input.index()],
                AigNode::And(lhs, rhs) => {
                    let value =
                        |literal: AigLit| values[literal.node().index()] ^ literal.is_inverted();
                    value(lhs) && value(rhs)
                }
            };
        }
        values
    }

    #[test]
    fn incremental_lowering_interrupts_wide_division() {
        let mut arena = TermArena::new();
        let x_symbol = arena.declare("x", Sort::BitVec(1024)).unwrap();
        let y_symbol = arena.declare("y", Sort::BitVec(1024)).unwrap();
        let x = arena.var(x_symbol);
        let y = arena.var(y_symbol);
        let quotient = arena.bv_udiv(x, y).unwrap();

        let mut lowering = IncrementalLowering::new();
        lowering.lower(&arena, x).unwrap();
        lowering.lower(&arena, y).unwrap();

        let start = Instant::now();
        let deadline = start.checked_add(Duration::from_millis(20));
        let result = lowering.lower_with_deadline(&arena, quotient, deadline);
        let elapsed = start.elapsed();

        assert_eq!(result, Err(BitLowerError::DeadlineExceeded));
        assert!(
            elapsed < Duration::from_secs(5),
            "wide division lowering ignored its deadline for {elapsed:?}"
        );

        let nodes_after_timeout = lowering.node_count();
        lowering.lower(&arena, x).unwrap();
        lowering.lower(&arena, y).unwrap();
        assert_eq!(
            lowering.node_count(),
            nodes_after_timeout,
            "completed children remain memoized after an interrupted parent"
        );
    }

    #[test]
    fn constants_lower_to_lsb_first_literals_and_lift_map() {
        let mut arena = TermArena::new();
        let bool_true = arena.bool_const(true);
        let bv_value = arena.bv_const(4, 0b1010).unwrap();
        let unlowered = arena.bv_const(3, 0b101).unwrap();
        let lowering = lower_terms(&arena, &[bool_true, bv_value]).unwrap();

        assert_eq!(lowering.roots()[0].bits(), &[AigLit::TRUE]);
        assert_eq!(
            lowering.roots()[1].bits(),
            &[AigLit::FALSE, AigLit::TRUE, AigLit::FALSE, AigLit::TRUE]
        );
        assert_eq!(
            lowering.literal_for_term_bit(bv_value, 0),
            Some(AigLit::FALSE)
        );
        assert_eq!(
            lowering.literal_for_term_bit(bv_value, 1),
            Some(AigLit::TRUE)
        );
        assert_eq!(lowering.literal_for_term_bit(bv_value, 4), None);
        assert_eq!(lowering.literal_for_term_bit(unlowered, 0), None);
        assert_eq!(lowering.term_bits().len(), 5);
        assert!(lowering.symbol_inputs().is_empty());
    }

    #[test]
    fn symbols_create_stable_input_map_and_replay_assignments() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
        let p_sym = arena.declare("p", Sort::Bool).unwrap();
        let x = arena.var(x_sym);
        let p = arena.var(p_sym);

        let lowering = lower_terms(&arena, &[x, p]).unwrap();
        assert_eq!(lowering.aig().input_count(), 4);
        assert_eq!(
            lowering
                .symbol_inputs()
                .iter()
                .map(|input| (input.symbol_name.as_str(), input.bit_index))
                .collect::<Vec<_>>(),
            vec![("x", 0), ("x", 1), ("x", 2), ("p", 0)]
        );

        let mut assignment = Assignment::new();
        assignment.set(x_sym, bv(3, 0b101));
        assignment.set(p_sym, Value::Bool(true));
        assert_eq!(
            lowering.input_values(&assignment).unwrap(),
            vec![true, false, true, true]
        );
        assert_eq!(
            lowering.evaluate_roots(&assignment).unwrap(),
            vec![bv(3, 0b101), Value::Bool(true)]
        );
    }

    #[test]
    fn boolean_connectives_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let p_sym = arena.declare("p", Sort::Bool).unwrap();
        let q_sym = arena.declare("q", Sort::Bool).unwrap();
        let p = arena.var(p_sym);
        let q = arena.var(q_sym);
        let not_q = arena.not(q).unwrap();
        let p_and_not_q = arena.and(p, not_q).unwrap();
        let p_implies_q = arena.implies(p, q).unwrap();
        let root = arena.xor(p_and_not_q, p_implies_q).unwrap();
        let lowering = lower_terms(&arena, &[root]).unwrap();

        for p_value in [false, true] {
            for q_value in [false, true] {
                let mut assignment = Assignment::new();
                assignment.set(p_sym, Value::Bool(p_value));
                assignment.set(q_sym, Value::Bool(q_value));
                assert_eq!(
                    lowering.evaluate_root(0, &assignment).unwrap(),
                    eval(&arena, root, &assignment).unwrap()
                );
            }
        }
    }

    #[test]
    fn bv_bitwise_ops_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(3)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let not_x = arena.bv_not(x).unwrap();
        let x_and_y = arena.bv_and(x, y).unwrap();
        let y_or_not_x = arena.bv_or(y, not_x).unwrap();
        let xnor = arena.bv_xnor(x_and_y, y_or_not_x).unwrap();
        let nand = arena.bv_nand(x, y).unwrap();
        let root = arena.bv_xor(xnor, nand).unwrap();
        let lowering = lower_terms(&arena, &[root]).unwrap();

        for x_value in 0..8 {
            for y_value in 0..8 {
                let mut assignment = Assignment::new();
                assignment.set(x_sym, bv(3, x_value));
                assignment.set(y_sym, bv(3, y_value));
                assert_eq!(
                    lowering.evaluate_root(0, &assignment).unwrap(),
                    eval(&arena, root, &assignment).unwrap(),
                    "x={x_value} y={y_value}"
                );
            }
        }
    }

    #[test]
    fn structural_ops_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(3)).unwrap();
        let z_sym = arena.declare("z", Sort::BitVec(2)).unwrap();
        let p_sym = arena.declare("p", Sort::Bool).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let z = arena.var(z_sym);
        let p = arena.var(p_sym);

        let x_low = arena.extract(1, 0, x).unwrap();
        let x_high = arena.extract(2, 1, x).unwrap();
        let concat = arena.concat(x_high, z).unwrap();
        let zero_ext = arena.zero_ext(2, x_low).unwrap();
        let sign_ext = arena.sign_ext(2, x_low).unwrap();
        let eq_bv = arena.eq(x, y).unwrap();
        let bv_comp = arena.bv_comp(x, y).unwrap();
        let ite_bv = arena.ite(eq_bv, zero_ext, sign_ext).unwrap();
        let not_eq_bv = arena.not(eq_bv).unwrap();
        let ite_bool = arena.ite(p, eq_bv, not_eq_bv).unwrap();
        let not_p = arena.not(p).unwrap();
        let eq_bool = arena.eq(p, not_p).unwrap();
        let roots = [
            eq_bv, bv_comp, x_low, x_high, concat, zero_ext, sign_ext, ite_bv, ite_bool, eq_bool,
        ];
        let lowering = lower_terms(&arena, &roots).unwrap();

        for x_value in 0..8 {
            for y_value in 0..8 {
                for z_value in 0..4 {
                    for p_value in [false, true] {
                        let mut assignment = Assignment::new();
                        assignment.set(x_sym, bv(3, x_value));
                        assignment.set(y_sym, bv(3, y_value));
                        assignment.set(z_sym, bv(2, z_value));
                        assignment.set(p_sym, Value::Bool(p_value));
                        let expected = roots
                            .iter()
                            .copied()
                            .map(|root| eval(&arena, root, &assignment))
                            .collect::<Result<Vec<_>, _>>()
                            .unwrap();
                        assert_eq!(
                            lowering.evaluate_roots(&assignment).unwrap(),
                            expected,
                            "x={x_value} y={y_value} z={z_value} p={p_value}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn arithmetic_ops_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(4)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(4)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let neg_x = arena.bv_neg(x).unwrap();
        let neg_y = arena.bv_neg(y).unwrap();
        let add = arena.bv_add(x, y).unwrap();
        let sub = arena.bv_sub(x, y).unwrap();
        let reverse_sub = arena.bv_sub(y, x).unwrap();
        let add_then_sub = arena.bv_sub(add, x).unwrap();
        let roots = [neg_x, neg_y, add, sub, reverse_sub, add_then_sub];
        let lowering = lower_terms(&arena, &roots).unwrap();

        for x_value in 0..16 {
            for y_value in 0..16 {
                let mut assignment = Assignment::new();
                assignment.set(x_sym, bv(4, x_value));
                assignment.set(y_sym, bv(4, y_value));
                let expected = roots
                    .iter()
                    .copied()
                    .map(|root| eval(&arena, root, &assignment))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();
                assert_eq!(
                    lowering.evaluate_roots(&assignment).unwrap(),
                    expected,
                    "x={x_value} y={y_value}"
                );
            }
        }
    }

    #[test]
    fn comparison_ops_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(3)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let roots = [
            arena.bv_ult(x, y).unwrap(),
            arena.bv_ule(x, y).unwrap(),
            arena.bv_ugt(x, y).unwrap(),
            arena.bv_uge(x, y).unwrap(),
            arena.bv_slt(x, y).unwrap(),
            arena.bv_sle(x, y).unwrap(),
            arena.bv_sgt(x, y).unwrap(),
            arena.bv_sge(x, y).unwrap(),
        ];
        let lowering = lower_terms(&arena, &roots).unwrap();

        for x_value in 0..8 {
            for y_value in 0..8 {
                let mut assignment = Assignment::new();
                assignment.set(x_sym, bv(3, x_value));
                assignment.set(y_sym, bv(3, y_value));
                let expected = roots
                    .iter()
                    .copied()
                    .map(|root| eval(&arena, root, &assignment))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();
                assert_eq!(
                    lowering.evaluate_roots(&assignment).unwrap(),
                    expected,
                    "x={x_value} y={y_value}"
                );
            }
        }
    }

    #[test]
    fn shift_ops_match_ground_evaluator() {
        assert_shift_ops_match_ground_evaluator(1);
        assert_shift_ops_match_ground_evaluator(4);
        assert_shift_ops_match_ground_evaluator(5);
    }

    fn assert_shift_ops_match_ground_evaluator(width: u32) {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
        let k_sym = arena.declare("k", Sort::BitVec(width)).unwrap();
        let x = arena.var(x_sym);
        let k = arena.var(k_sym);
        let roots = [
            arena.bv_shl(x, k).unwrap(),
            arena.bv_lshr(x, k).unwrap(),
            arena.bv_ashr(x, k).unwrap(),
        ];
        let lowering = lower_terms(&arena, &roots).unwrap();

        let value_count = 1u128 << width;
        for x_value in 0..value_count {
            for k_value in 0..value_count {
                let mut assignment = Assignment::new();
                assignment.set(x_sym, bv(width, x_value));
                assignment.set(k_sym, bv(width, k_value));
                let expected = roots
                    .iter()
                    .copied()
                    .map(|root| eval(&arena, root, &assignment))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();
                assert_eq!(
                    lowering.evaluate_roots(&assignment).unwrap(),
                    expected,
                    "width={width} x={x_value} k={k_value}"
                );
            }
        }
    }

    #[test]
    fn rotate_ops_match_ground_evaluator() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(5)).unwrap();
        let x = arena.var(x_sym);
        let mut roots = Vec::new();
        for by in 0..10 {
            roots.push(arena.rotate_left(by, x).unwrap());
            roots.push(arena.rotate_right(by, x).unwrap());
        }
        let lowering = lower_terms(&arena, &roots).unwrap();

        for x_value in 0..32 {
            let mut assignment = Assignment::new();
            assignment.set(x_sym, bv(5, x_value));
            let expected = roots
                .iter()
                .copied()
                .map(|root| eval(&arena, root, &assignment))
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            assert_eq!(
                lowering.evaluate_roots(&assignment).unwrap(),
                expected,
                "x={x_value}"
            );
        }
    }

    #[test]
    fn concat_lift_map_preserves_lsb_first_order() {
        let mut arena = TermArena::new();
        let high_sym = arena.declare("high", Sort::BitVec(2)).unwrap();
        let low_sym = arena.declare("low", Sort::BitVec(2)).unwrap();
        let high = arena.var(high_sym);
        let low = arena.var(low_sym);
        let concat = arena.concat(high, low).unwrap();
        let lowering = lower_terms(&arena, &[concat]).unwrap();
        let root_bits = lowering.roots()[0].bits();

        assert_eq!(root_bits.len(), 4);
        assert_eq!(
            Some(root_bits[0]),
            lowering.literal_for_term_bit(low, 0),
            "concat bit 0 comes from the low operand bit 0"
        );
        assert_eq!(
            Some(root_bits[1]),
            lowering.literal_for_term_bit(low, 1),
            "concat bit 1 comes from the low operand bit 1"
        );
        assert_eq!(
            Some(root_bits[2]),
            lowering.literal_for_term_bit(high, 0),
            "concat bit 2 comes from the high operand bit 0"
        );
        assert_eq!(
            Some(root_bits[3]),
            lowering.literal_for_term_bit(high, 1),
            "concat bit 3 comes from the high operand bit 1"
        );
    }

    #[test]
    fn structural_demand_exposes_full_child_lowering_for_narrow_extract() {
        let mut arena = TermArena::new();
        let x_symbol = arena.declare("x", Sort::BitVec(64)).unwrap();
        let x = arena.var(x_symbol);
        let low_byte = arena.extract(7, 0, x).unwrap();
        let expected = arena.bv_const(8, 0x5a).unwrap();
        let root = arena.eq(low_byte, expected).unwrap();

        let lowering = lower_terms_profiled(&arena, &[root]).unwrap();
        let stats = lowering.demand_stats();
        assert!(stats.profile_complete);
        assert_eq!(stats.term_bit_requests, 25);
        assert_eq!(stats.term_bits_available, 81);
        assert_eq!(stats.term_bits_demanded, 25);
        assert_eq!(stats.term_bits_lowered, 81);
        assert_eq!(stats.symbol_bit_requests, 8);
        assert_eq!(stats.symbol_bits_available, 64);
        assert_eq!(stats.symbol_bits_demanded, 8);
        assert_eq!(stats.symbol_bits_lowered, 64);
    }

    #[test]
    fn demanded_lowering_materializes_only_narrow_extract_cone() {
        let mut arena = TermArena::new();
        let x_symbol = arena.declare("x", Sort::BitVec(64)).unwrap();
        let x = arena.var(x_symbol);
        let low_byte = arena.extract(7, 0, x).unwrap();
        let expected = arena.bv_const(8, 0x5a).unwrap();
        let root = arena.eq(low_byte, expected).unwrap();

        let lowering = lower_terms_demanded(&arena, &[root]).unwrap();
        let stats = lowering.demand_stats();
        assert!(stats.profile_complete);
        assert!(stats.lowering_applied);
        assert_eq!(stats.term_bit_requests, 25);
        assert_eq!(stats.term_bits_available, 81);
        assert_eq!(stats.term_bits_demanded, 25);
        assert_eq!(stats.term_bits_lowered, 25);
        assert_eq!(stats.symbol_bit_requests, 8);
        assert_eq!(stats.symbol_bits_available, 64);
        assert_eq!(stats.symbol_bits_demanded, 8);
        assert_eq!(stats.symbol_bits_lowered, 8);
        assert!(lowering.literal_for_term_bit(x, 0).is_some());
        assert!(lowering.literal_for_term_bit(x, 7).is_some());
        assert_eq!(lowering.literal_for_term_bit(x, 8), None);
        assert_eq!(lowering.symbol_inputs().len(), 8);

        for value in [0u128, 0x5a, 0x15a, u128::from(u64::MAX)] {
            let mut assignment = Assignment::new();
            assignment.set(x_symbol, bv(64, value));
            assert_eq!(
                lowering.evaluate_root(0, &assignment).unwrap(),
                eval(&arena, root, &assignment).unwrap()
            );
        }
    }

    #[test]
    fn demanded_structural_ops_match_evaluator_exhaustively() {
        let mut arena = TermArena::new();
        let x_symbol = arena.declare("x", Sort::BitVec(4)).unwrap();
        let y_symbol = arena.declare("y", Sort::BitVec(4)).unwrap();
        let p_symbol = arena.declare("p", Sort::Bool).unwrap();
        let x = arena.var(x_symbol);
        let y = arena.var(y_symbol);
        let p = arena.var(p_symbol);
        let joined = arena.concat(x, y).unwrap();
        let middle = arena.extract(5, 2, joined).unwrap();
        let rotated = arena.rotate_left(1, middle).unwrap();
        let inverted = arena.bv_not(rotated).unwrap();
        let selected = arena.ite(p, rotated, inverted).unwrap();
        let target = arena.bv_const(4, 0b1010).unwrap();
        let root = arena.eq(selected, target).unwrap();
        let lowering = lower_terms_demanded(&arena, &[root]).unwrap();

        for x_value in 0..16 {
            for y_value in 0..16 {
                for p_value in [false, true] {
                    let mut assignment = Assignment::new();
                    assignment.set(x_symbol, bv(4, x_value));
                    assignment.set(y_symbol, bv(4, y_value));
                    assignment.set(p_symbol, Value::Bool(p_value));
                    assert_eq!(
                        lowering.evaluate_root(0, &assignment).unwrap(),
                        eval(&arena, root, &assignment).unwrap(),
                        "x={x_value} y={y_value} p={p_value}"
                    );
                }
            }
        }
    }

    #[test]
    fn demanded_lowering_unions_disjoint_shared_slices_and_completes_model_bits() {
        let mut arena = TermArena::new();
        let x_symbol = arena.declare("x", Sort::BitVec(8)).unwrap();
        let x = arena.var(x_symbol);
        let low = arena.extract(1, 0, x).unwrap();
        let high = arena.extract(7, 6, x).unwrap();
        let low_value = arena.bv_const(2, 0b11).unwrap();
        let high_value = arena.bv_const(2, 0b11).unwrap();
        let roots = [
            arena.eq(low, low_value).unwrap(),
            arena.eq(high, high_value).unwrap(),
        ];
        let lowering = lower_terms_demanded(&arena, &roots).unwrap();

        assert_eq!(lowering.symbol_inputs().len(), 4);
        for bit in [0, 1, 6, 7] {
            assert!(lowering.literal_for_term_bit(x, bit).is_some());
        }
        for bit in 2..6 {
            assert_eq!(lowering.literal_for_term_bit(x, bit), None);
        }

        let mut assignment = Assignment::new();
        assignment.set(x_symbol, bv(8, 0xff));
        let node_values = evaluated_aig_nodes(&lowering, &assignment);
        let reconstructed = lowering.assignment_from_aig_values(&node_values).unwrap();
        assert_eq!(reconstructed.get(x_symbol), Some(bv(8, 0b1100_0011)));
        assert_eq!(
            lowering.evaluate_roots(&assignment).unwrap(),
            vec![Value::Bool(true), Value::Bool(true)]
        );
    }

    #[test]
    fn demanded_lowering_uses_conservative_full_arithmetic_barrier() {
        let mut arena = TermArena::new();
        let x_symbol = arena.declare("x", Sort::BitVec(4)).unwrap();
        let y_symbol = arena.declare("y", Sort::BitVec(4)).unwrap();
        let x = arena.var(x_symbol);
        let y = arena.var(y_symbol);
        let sum = arena.bv_add(x, y).unwrap();
        let low_bit = arena.extract(0, 0, sum).unwrap();
        let one = arena.bv_const(1, 1).unwrap();
        let root = arena.eq(low_bit, one).unwrap();
        let lowering = lower_terms_demanded(&arena, &[root]).unwrap();

        assert!(
            lowering.demand_stats().term_bits_lowered > lowering.demand_stats().term_bits_demanded
        );
        for bit in 0..4 {
            assert!(lowering.literal_for_term_bit(sum, bit).is_some());
        }
        for x_value in 0..16 {
            for y_value in 0..16 {
                let mut assignment = Assignment::new();
                assignment.set(x_symbol, bv(4, x_value));
                assignment.set(y_symbol, bv(4, y_value));
                assert_eq!(
                    lowering.evaluate_root(0, &assignment).unwrap(),
                    eval(&arena, root, &assignment).unwrap(),
                    "x={x_value} y={y_value}"
                );
            }
        }
    }

    #[test]
    fn demanded_lowering_skips_irrelevant_zero_extension_source() {
        let mut arena = TermArena::new();
        let x_symbol = arena.declare("x", Sort::BitVec(8)).unwrap();
        let x = arena.var(x_symbol);
        let extended = arena.zero_ext(8, x).unwrap();
        let high = arena.extract(15, 8, extended).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let root = arena.eq(high, zero).unwrap();
        let lowering = lower_terms_demanded(&arena, &[root]).unwrap();

        assert!(lowering.symbol_inputs().is_empty());
        assert_eq!(lowering.literal_for_term_bit(x, 0), None);
        let assignment = Assignment::new();
        let node_values = evaluated_aig_nodes(&lowering, &assignment);
        assert!(
            lowering
                .assignment_from_aig_values(&node_values)
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            lowering
                .root_value_from_aig_values(0, &node_values)
                .unwrap(),
            Value::Bool(true)
        );
    }

    #[test]
    fn demanded_lowering_honors_expired_deadline() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 64).unwrap();
        let root = arena.eq(x, x).unwrap();
        assert!(matches!(
            lower_terms_demanded_with_deadline(&arena, &[root], Some(Instant::now())),
            Err(BitLowerError::DeadlineExceeded)
        ));
    }

    fn permissive_range_policy() -> RangeDemandPolicy {
        RangeDemandPolicy {
            min_term_bits_available: 0,
            min_estimated_bits_avoided: 0,
            min_estimated_avoided_percent: 0,
            min_exact_bits_avoided: 0,
            min_exact_avoided_percent: 0,
            analysis_work_budget: 10_000,
        }
    }

    #[test]
    fn range_demand_applies_to_profitable_register_slice() {
        let mut arena = TermArena::new();
        let x_symbol = arena.declare("x", Sort::BitVec(64)).unwrap();
        let x = arena.var(x_symbol);
        let low_byte = arena.extract(7, 0, x).unwrap();
        let expected = arena.bv_const(8, 0x5a).unwrap();
        let root = arena.eq(low_byte, expected).unwrap();
        let policy = RangeDemandPolicy {
            min_term_bits_available: 64,
            min_estimated_bits_avoided: 32,
            min_estimated_avoided_percent: 50,
            min_exact_bits_avoided: 32,
            min_exact_avoided_percent: 50,
            analysis_work_budget: 1_000,
        };

        let lowering = lower_terms_range_demanded(&arena, &[root], policy).unwrap();
        let stats = lowering.demand_stats();
        assert_eq!(stats.range_decision, RangeDemandDecision::Applied);
        assert!(stats.lowering_applied);
        assert_eq!(stats.estimated_bits_avoided, 56);
        assert_eq!(stats.term_bits_available, 81);
        assert_eq!(stats.term_bits_demanded, 25);
        assert_eq!(stats.term_bits_lowered, 25);
        assert_eq!(stats.symbol_bits_available, 64);
        assert_eq!(stats.symbol_bits_demanded, 8);
        assert_eq!(stats.symbol_bits_lowered, 8);
        assert!(stats.analysis_work <= stats.analysis_work_budget);

        for value in [0u128, 0x5a, 0x15a, u128::from(u64::MAX)] {
            let mut assignment = Assignment::new();
            assignment.set(x_symbol, bv(64, value));
            assert_eq!(
                lowering.evaluate_root(0, &assignment).unwrap(),
                eval(&arena, root, &assignment).unwrap()
            );
        }
    }

    #[test]
    fn range_demand_rejection_uses_unchanged_full_lowerer() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let seven = arena.bv_const(8, 7).unwrap();
        let root = arena.eq(x, seven).unwrap();

        let full = lower_terms(&arena, &[root]).unwrap();
        let rejected =
            lower_terms_range_demanded(&arena, &[root], RangeDemandPolicy::default()).unwrap();
        assert_eq!(
            rejected.demand_stats().range_decision,
            RangeDemandDecision::NoCandidate
        );
        assert!(!rejected.demand_stats().lowering_applied);
        assert_eq!(rejected.roots()[0].bits(), full.roots()[0].bits());
        assert_eq!(rejected.term_bits(), full.term_bits());
        assert_eq!(rejected.symbol_inputs(), full.symbol_inputs());
        assert_eq!(rejected.aig().node_count(), full.aig().node_count());
    }

    #[test]
    fn range_demand_budget_exhaustion_falls_back_deterministically() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 64).unwrap();
        let low = arena.extract(7, 0, x).unwrap();
        let expected = arena.bv_const(8, 0x5a).unwrap();
        let root = arena.eq(low, expected).unwrap();
        let mut policy = permissive_range_policy();
        policy.analysis_work_budget = 0;

        let first = lower_terms_range_demanded(&arena, &[root], policy).unwrap();
        let second = lower_terms_range_demanded(&arena, &[root], policy).unwrap();
        assert_eq!(
            first.demand_stats().range_decision,
            RangeDemandDecision::AnalysisBudgetExceeded
        );
        assert_eq!(first.demand_stats().analysis_work, 0);
        assert_eq!(first.term_bits(), second.term_bits());
        assert_eq!(first.symbol_inputs(), second.symbol_inputs());
        assert_eq!(first.aig().node_count(), second.aig().node_count());
        assert_eq!(first.demand_stats().term_bits_lowered, 81);
        assert_eq!(first.demand_stats().symbol_bits_lowered, 64);
    }

    #[test]
    fn range_demand_matches_dense_planner_on_structural_dag() {
        let mut arena = TermArena::new();
        let x_symbol = arena.declare("x", Sort::BitVec(8)).unwrap();
        let p_symbol = arena.declare("p", Sort::Bool).unwrap();
        let x = arena.var(x_symbol);
        let p = arena.var(p_symbol);
        let extended = arena.sign_ext(4, x).unwrap();
        let rotated = arena.rotate_right(3, extended).unwrap();
        let selected = arena.ite(p, extended, rotated).unwrap();
        let low = arena.extract(2, 0, selected).unwrap();
        let high = arena.extract(11, 9, selected).unwrap();
        let target = arena.bv_const(3, 0b101).unwrap();
        let roots = [
            arena.eq(low, target).unwrap(),
            arena.eq(high, target).unwrap(),
        ];

        let dense = lower_terms_demanded(&arena, &roots).unwrap();
        let ranged = lower_terms_range_demanded(&arena, &roots, permissive_range_policy()).unwrap();
        assert_eq!(
            ranged.demand_stats().range_decision,
            RangeDemandDecision::Applied
        );
        assert_eq!(
            ranged.demand_stats().term_bits_demanded,
            dense.demand_stats().term_bits_demanded
        );
        assert_eq!(
            ranged.demand_stats().symbol_bits_demanded,
            dense.demand_stats().symbol_bits_demanded
        );
        assert_eq!(ranged.term_bits().len(), dense.term_bits().len());
        assert_eq!(ranged.symbol_inputs().len(), dense.symbol_inputs().len());

        for x_value in 0..256 {
            for p_value in [false, true] {
                let mut assignment = Assignment::new();
                assignment.set(x_symbol, bv(8, x_value));
                assignment.set(p_symbol, Value::Bool(p_value));
                assert_eq!(
                    ranged.evaluate_roots(&assignment).unwrap(),
                    dense.evaluate_roots(&assignment).unwrap(),
                    "x={x_value} p={p_value}"
                );
            }
        }
    }

    #[test]
    fn range_demand_fragmentation_promotes_to_full_without_heap_ranges() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 16).unwrap();
        let mut roots = Vec::new();
        for bit in [0, 2, 4, 6, 8] {
            let slice = arena.extract(bit, bit, x).unwrap();
            let one = arena.bv_const(1, 1).unwrap();
            roots.push(arena.eq(slice, one).unwrap());
        }

        let lowering =
            lower_terms_range_demanded(&arena, &roots, permissive_range_policy()).unwrap();
        assert_eq!(
            lowering.demand_stats().range_decision,
            RangeDemandDecision::Applied
        );
        assert_eq!(lowering.demand_stats().range_promotions, 1);
        assert_eq!(lowering.demand_stats().symbol_bits_demanded, 16);
        assert_eq!(lowering.demand_stats().symbol_bits_lowered, 16);
    }

    #[test]
    fn range_demand_honors_expired_deadline_before_admission() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 64).unwrap();
        let root = arena.eq(x, x).unwrap();
        assert!(matches!(
            lower_terms_range_demanded_with_deadline(
                &arena,
                &[root],
                permissive_range_policy(),
                Some(Instant::now())
            ),
            Err(BitLowerError::DeadlineExceeded)
        ));
    }

    #[test]
    fn production_lowering_skips_structural_demand_profile() {
        let mut arena = TermArena::new();
        let x_symbol = arena.declare("x", Sort::BitVec(64)).unwrap();
        let x = arena.var(x_symbol);
        let low_byte = arena.extract(7, 0, x).unwrap();
        let expected = arena.bv_const(8, 0x5a).unwrap();
        let root = arena.eq(low_byte, expected).unwrap();

        let lowering = lower_terms(&arena, &[root]).unwrap();
        let stats = lowering.demand_stats();
        assert!(!stats.profile_complete);
        assert_eq!(stats.analysis, Duration::ZERO);
        assert_eq!(stats.term_bit_requests, 0);
        assert_eq!(stats.term_bits_available, 0);
        assert_eq!(stats.term_bits_demanded, 0);
        assert_eq!(stats.term_bits_lowered, 81);
        assert_eq!(stats.symbol_bit_requests, 0);
        assert_eq!(stats.symbol_bits_available, 0);
        assert_eq!(stats.symbol_bits_demanded, 0);
        assert_eq!(stats.symbol_bits_lowered, 64);
    }

    #[test]
    fn incremental_lowering_matches_batch_and_shares_subterms() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let y = arena.bv_var("y", 8).unwrap();
        let sum = arena.bv_add(x, y).unwrap();
        let prod = arena.bv_mul(x, y).unwrap();
        let seven = arena.bv_const(8, 7).unwrap();
        let a = arena.eq(sum, seven).unwrap();
        // `b` shares `sum`, `x`, and `y` with `a`.
        let b = arena.bv_ult(prod, sum).unwrap();

        let batch = lower_terms(&arena, &[a, b]).unwrap();

        let mut incremental = IncrementalLowering::new();
        let lowered_a = incremental.lower(&arena, a).unwrap();
        let lowered_b = incremental.lower(&arena, b).unwrap();

        // Incremental lowering builds the same AIG and the same root bits as a
        // single batch lowering, so it inherits the batch path's correctness.
        assert_eq!(lowered_a.bits(), batch.roots()[0].bits());
        assert_eq!(lowered_b.bits(), batch.roots()[1].bits());
        assert_eq!(incremental.node_count(), batch.aig().node_count());
        assert_eq!(incremental.symbol_inputs(), batch.symbol_inputs());

        // Re-lowering an already-lowered term adds no AIG nodes (memoized).
        let before = incremental.node_count();
        let lowered_again = incremental.lower(&arena, a).unwrap();
        assert_eq!(lowered_again.bits(), lowered_a.bits());
        assert_eq!(
            incremental.node_count(),
            before,
            "shared subterms must not be re-lowered"
        );
    }

    #[test]
    fn profiled_incremental_lowering_accounts_for_memo_and_literal_copy_work() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let sum = arena.bv_add(x, one).unwrap();
        let expected = arena.bv_const(8, 7).unwrap();
        let root = arena.eq(sum, expected).unwrap();
        let mut lowering = IncrementalLowering::with_profiling();

        let empty = lowering.stats();
        lowering.lower(&arena, root).unwrap();
        let first = lowering.stats().delta_since(empty);
        assert_eq!(first.lower_calls, 1);
        assert!(first.term_memo_lookups > first.terms_lowered);
        assert_eq!(first.term_memo_hits, 0);
        assert_eq!(first.memoized_terms, first.terms_lowered);
        assert_eq!(first.term_bit_bindings, first.term_bit_bindings_written);
        assert!(first.operand_vectors_copied > 0);
        assert!(first.operand_bits_copied > 0);
        assert_eq!(first.root_bits_copied, 1);
        assert_eq!(first.symbol_bit_inputs, 8);

        let before_reuse = lowering.stats();
        lowering.lower(&arena, root).unwrap();
        let reused = lowering.stats().delta_since(before_reuse);
        assert_eq!(reused.lower_calls, 1);
        assert_eq!(reused.term_memo_lookups, 1);
        assert_eq!(reused.term_memo_hits, 1);
        assert_eq!(reused.terms_lowered, 0);
        assert_eq!(reused.operand_vectors_copied, 0);
        assert_eq!(reused.operand_bits_copied, 0);
        assert_eq!(reused.root_bits_copied, 1);
        assert_eq!(reused.memoized_terms, 0);
        assert_eq!(reused.term_bit_bindings, 0);
        assert_eq!(reused.symbol_bit_inputs, 0);
    }

    #[test]
    fn profiled_batch_lowering_reports_exact_btree_memo_accounting() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let sum = arena.bv_add(x, one).unwrap();
        let expected = arena.bv_const(8, 7).unwrap();
        let root = arena.eq(sum, expected).unwrap();
        let _unreachable = arena.bv_var("unreachable", 32).unwrap();

        let profiled = lower_terms_profiled(&arena, &[root, sum]).unwrap();
        let stats = profiled.memo_stats();
        assert!(stats.profile_complete);
        assert_eq!(stats.representation, BitLoweringMemoRepresentation::BtreeV1);
        assert_eq!(stats.source_terms, usize_to_u64_saturating(arena.len()));
        assert_eq!(stats.slots, stats.occupied);
        assert_eq!(stats.occupied, stats.writes);
        assert!(stats.occupied < stats.source_terms);
        assert!(stats.lookups > stats.writes);
        assert!(stats.hits > 0);
        assert_eq!(
            stats.payload_literals,
            usize_to_u64_saturating(profiled.term_bits().len())
        );
        assert!(stats.payload_capacity_literals >= stats.payload_literals);
        let header_unit = usize_to_u64_saturating(
            core::mem::size_of::<TermId>() + core::mem::size_of::<Vec<AigLit>>(),
        );
        let literal_bytes = usize_to_u64_saturating(core::mem::size_of::<AigLit>());
        assert_eq!(stats.logical_header_bytes, stats.occupied * header_unit);
        assert_eq!(
            stats.logical_payload_bytes,
            stats.payload_literals * literal_bytes
        );
        assert_eq!(
            stats.logical_total_bytes,
            stats.logical_header_bytes + stats.logical_payload_bytes
        );
        assert_eq!(stats.root_bits, 9);
        assert_eq!(stats.root_bits, stats.expected_root_bits);
        assert!(stats.invariants_hold);

        assert_eq!(
            lower_terms(&arena, &[root, sum]).unwrap().memo_stats(),
            BitLoweringMemoStats::default()
        );
        assert_eq!(
            lower_terms_demanded(&arena, &[root, sum])
                .unwrap()
                .memo_stats(),
            BitLoweringMemoStats::default()
        );
    }

    #[test]
    fn incremental_term_bit_ranges_grow_with_the_arena() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let mut incremental = IncrementalLowering::new();
        incremental.lower(&arena, x).unwrap();

        let x_range = incremental.term_bit_ranges[x.index()].unwrap();
        let first_arena_len = arena.len();
        assert_eq!(incremental.term_bit_ranges.len(), first_arena_len);

        let one = arena.bv_const(8, 1).unwrap();
        let sum = arena.bv_add(x, one).unwrap();
        assert!(arena.len() > first_arena_len);
        incremental.lower(&arena, sum).unwrap();

        assert_eq!(incremental.term_bit_ranges.len(), arena.len());
        assert_eq!(incremental.term_bit_ranges[x.index()], Some(x_range));
        assert!(incremental.term_bit_ranges[one.index()].is_some());
        assert!(incremental.term_bit_ranges[sum.index()].is_some());
    }

    #[test]
    fn signed_division_matches_ground_evaluator() {
        for width in [1u32, 2, 3, 4, 5] {
            let mut arena = TermArena::new();
            let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
            let y_sym = arena.declare("y", Sort::BitVec(width)).unwrap();
            let x = arena.var(x_sym);
            let y = arena.var(y_sym);
            // Signed divide/rem/mod over all input pairs, including negative
            // operands, the most-negative value, and the divide-by-zero path.
            let roots = [
                arena.bv_sdiv(x, y).unwrap(),
                arena.bv_srem(x, y).unwrap(),
                arena.bv_smod(x, y).unwrap(),
            ];
            let lowering = lower_terms(&arena, &roots).unwrap();

            let bound = 1u128 << width;
            for x_value in 0..bound {
                for y_value in 0..bound {
                    let mut assignment = Assignment::new();
                    assignment.set(x_sym, bv(width, x_value));
                    assignment.set(y_sym, bv(width, y_value));
                    let expected = roots
                        .iter()
                        .copied()
                        .map(|root| eval(&arena, root, &assignment))
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap();
                    assert_eq!(
                        lowering.evaluate_roots(&assignment).unwrap(),
                        expected,
                        "width={width} x={x_value} y={y_value}"
                    );
                }
            }
        }
    }

    #[test]
    fn unsigned_division_matches_ground_evaluator() {
        for width in [1u32, 2, 3, 4, 5] {
            let mut arena = TermArena::new();
            let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
            let y_sym = arena.declare("y", Sort::BitVec(width)).unwrap();
            let x = arena.var(x_sym);
            let y = arena.var(y_sym);
            // Cover divide-by-symbol, divide-by-constant, and self-division so
            // the divide-by-zero totality path is exercised (y ranges over 0).
            let three = arena.bv_const(width, 3 & ((1u128 << width) - 1)).unwrap();
            let roots = [
                arena.bv_udiv(x, y).unwrap(),
                arena.bv_urem(x, y).unwrap(),
                arena.bv_udiv(x, three).unwrap(),
                arena.bv_urem(x, three).unwrap(),
            ];
            let lowering = lower_terms(&arena, &roots).unwrap();

            let bound = 1u128 << width;
            for x_value in 0..bound {
                for y_value in 0..bound {
                    let mut assignment = Assignment::new();
                    assignment.set(x_sym, bv(width, x_value));
                    assignment.set(y_sym, bv(width, y_value));
                    let expected = roots
                        .iter()
                        .copied()
                        .map(|root| eval(&arena, root, &assignment))
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap();
                    assert_eq!(
                        lowering.evaluate_roots(&assignment).unwrap(),
                        expected,
                        "width={width} x={x_value} y={y_value}"
                    );
                }
            }
        }
    }

    #[test]
    fn multiplication_matches_ground_evaluator() {
        // Widths span Booth radix-4 grouping cases: 1 (degenerate), even, and
        // odd (last digit straddles the top bit).
        for width in [1u32, 2, 3, 4, 5, 6, 7] {
            let mut arena = TermArena::new();
            let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
            let y_sym = arena.declare("y", Sort::BitVec(width)).unwrap();
            let x = arena.var(x_sym);
            let y = arena.var(y_sym);
            // Cover symbol*symbol, squaring (shared operand), and
            // symbol*constant so partial-product folding is exercised too.
            let width_mask = (1u128 << width) - 1;
            let three = arena.bv_const(width, 3 & width_mask).unwrap();
            let roots = [
                arena.bv_mul(x, y).unwrap(),
                arena.bv_mul(x, x).unwrap(),
                arena.bv_mul(x, three).unwrap(),
            ];
            let lowering = lower_terms(&arena, &roots).unwrap();

            let bound = 1u128 << width;
            for x_value in 0..bound {
                for y_value in 0..bound {
                    let mut assignment = Assignment::new();
                    assignment.set(x_sym, bv(width, x_value));
                    assignment.set(y_sym, bv(width, y_value));
                    let expected = roots
                        .iter()
                        .copied()
                        .map(|root| eval(&arena, root, &assignment))
                        .collect::<Result<Vec<_>, _>>()
                        .unwrap();
                    assert_eq!(
                        lowering.evaluate_roots(&assignment).unwrap(),
                        expected,
                        "width={width} x={x_value} y={y_value}"
                    );
                }
            }
        }
    }

    #[test]
    fn assignment_errors_are_reported_before_aig_evaluation() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(2)).unwrap();
        let x = arena.var(x_sym);
        let lowering = lower_terms(&arena, &[x]).unwrap();

        assert!(matches!(
            lowering.input_values(&Assignment::new()),
            Err(BitLowerError::Ir(IrError::UnboundSymbol(symbol))) if symbol == x_sym
        ));

        let mut wrong_sort = Assignment::new();
        wrong_sort.set(x_sym, Value::Bool(true));
        assert!(matches!(
            lowering.input_values(&wrong_sort),
            Err(BitLowerError::AssignmentSortMismatch {
                expected: Sort::BitVec(2),
                found: Sort::Bool,
                ..
            })
        ));
    }

    #[test]
    fn eval_lowered_once_returns_evaluator_and_aig_values() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(2)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(2)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let root = arena.bv_or(x, y).unwrap();
        let mut assignment = Assignment::new();
        assignment.set(x_sym, bv(2, 0b01));
        assignment.set(y_sym, bv(2, 0b10));

        assert_eq!(
            eval_lowered_once(&arena, root, &assignment).unwrap(),
            (bv(2, 0b11), bv(2, 0b11))
        );
    }
}
