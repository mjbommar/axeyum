//! Reason-preserving handoff from an undecided proof to directed fuzzing.
//!
//! This module keeps proof, replayed refutation, and sampled testing visibly
//! distinct. In particular, a [`HybridOutcome::FuzzedOnly`] is produced only
//! from [`ProofOutcome::Unknown`]; it never means proved or solver-refuted.
//!
//! ```no_run
//! use axeyum_ir::{Sort, TermArena};
//! use axeyum_solver::SolverConfig;
//! use axeyum_verify::directed_fuzz::{
//!     DirectedFuzzPlan, FuzzInput, check_with_directed_fuzz,
//! };
//!
//! let mut arena = TermArena::new();
//! let x = arena.declare("x", Sort::BitVec(8)).unwrap();
//! let x_term = arena.var(x);
//! let goal = arena.eq(x_term, x_term).unwrap();
//! let plan = DirectedFuzzPlan::new("reflexive", vec![FuzzInput::full(x)], 16).unwrap();
//! let outcome = check_with_directed_fuzz(
//!     &mut arena,
//!     &[],
//!     goal,
//!     &SolverConfig::default(),
//!     plan,
//!     |_| true,
//!     |_| true,
//! )?;
//! # let _ = outcome;
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use std::collections::BTreeSet;

use axeyum_ir::{
    Assignment, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
};
use axeyum_smtlib::write_script;
use axeyum_solver::{
    EvidenceReport, Model, ProofOutcome, SolverConfig, SolverError, UnknownKind, UnknownReason,
    prove,
};

/// Schema identifier for canonical directed-fuzz target JSON.
pub const TARGET_SCHEMA: &str = "axeyum-directed-fuzz-target-v1";
/// Schema identifier for canonical directed-fuzz report JSON.
pub const REPORT_SCHEMA: &str = "axeyum-directed-fuzz-report-v1";

const DEFAULT_SEED: u64 = 0xd1ec_7edf_0220_0340;
const LCG_MULTIPLIER: u64 = 6_364_136_223_846_793_005;
const LCG_INCREMENT: u64 = 1;
const CORNER_COUNT: usize = 5;

/// Sampling domain for one scalar input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FuzzDomain {
    /// The complete Bool or bit-vector domain.
    Full,
    /// An inclusive unsigned interval for a bit-vector input.
    BitVecRange {
        /// Inclusive unsigned lower bound.
        min: u128,
        /// Inclusive unsigned upper bound.
        max: u128,
    },
}

/// One explicitly ordered fuzz input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FuzzInput {
    /// Arena-owned symbol sampled at this position.
    pub symbol: SymbolId,
    /// Domain used to produce values.
    pub domain: FuzzDomain,
}

impl FuzzInput {
    /// Samples the complete domain of `symbol`.
    #[must_use]
    pub const fn full(symbol: SymbolId) -> Self {
        Self {
            symbol,
            domain: FuzzDomain::Full,
        }
    }

    /// Samples the inclusive unsigned bit-vector interval `min..=max`.
    #[must_use]
    pub const fn bitvec_range(symbol: SymbolId, min: u128, max: u128) -> Self {
        Self {
            symbol,
            domain: FuzzDomain::BitVecRange { min, max },
        }
    }
}

/// Deterministic, explicit configuration for one handoff.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirectedFuzzPlan {
    id: String,
    inputs: Vec<FuzzInput>,
    sample_budget: usize,
    seed: u64,
}

impl DirectedFuzzPlan {
    /// Constructs a plan with Axeyum's stable default seed.
    ///
    /// # Errors
    ///
    /// Rejects an unstable ID, a zero budget, or duplicate symbols. Query- and
    /// sort-dependent validation occurs before solving.
    pub fn new(
        id: impl Into<String>,
        inputs: Vec<FuzzInput>,
        sample_budget: usize,
    ) -> Result<Self, DirectedFuzzError> {
        let id = id.into();
        if !valid_id(&id) {
            return Err(DirectedFuzzError::InvalidId(id));
        }
        if sample_budget == 0 {
            return Err(DirectedFuzzError::ZeroSampleBudget);
        }
        let mut seen = BTreeSet::new();
        for input in &inputs {
            if !seen.insert(input.symbol) {
                return Err(DirectedFuzzError::DuplicateInput(input.symbol));
            }
        }
        Ok(Self {
            id,
            inputs,
            sample_budget,
            seed: DEFAULT_SEED,
        })
    }

    /// Replaces the deterministic seed.
    #[must_use]
    pub const fn with_seed(mut self, seed: u64) -> Self {
        self.seed = seed;
        self
    }

    /// Stable target identifier.
    #[must_use]
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Declaration-ordered inputs.
    #[must_use]
    pub fn inputs(&self) -> &[FuzzInput] {
        &self.inputs
    }

    /// Requested number of samples.
    #[must_use]
    pub const fn sample_budget(&self) -> usize {
        self.sample_budget
    }

    /// Deterministic sampling seed.
    #[must_use]
    pub const fn seed(&self) -> u64 {
        self.seed
    }
}

/// One typed value passed to the caller's original-semantics oracle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SampleValue {
    /// Arena-owned symbol.
    pub symbol: SymbolId,
    /// Stable arena-owned name copied into the sample.
    pub name: String,
    /// Bool or width-preserving bit-vector value.
    pub value: Value,
}

/// Canonical, owned handoff target.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirectedFuzzTarget {
    /// Stable target ID.
    pub id: String,
    /// Exact structured reason returned by the solver.
    pub reason: UnknownReason,
    /// Deterministic seed.
    pub seed: u64,
    /// Requested sample count.
    pub sample_budget: usize,
    /// Ordered input-domain descriptions.
    pub inputs: Vec<TargetInput>,
    /// Sharing-preserving SMT-LIB for `hypotheses AND NOT goal`.
    pub violation_query_smt2: String,
}

impl DirectedFuzzTarget {
    /// Returns canonical compact JSON with a trailing newline.
    #[must_use]
    pub fn to_json(&self) -> String {
        let mut out = String::new();
        out.push_str("{\"schema\":");
        push_json_string(&mut out, TARGET_SCHEMA);
        out.push_str(",\"id\":");
        push_json_string(&mut out, &self.id);
        out.push_str(",\"unknown\":{\"kind\":");
        push_json_string(&mut out, unknown_kind_label(self.reason.kind));
        out.push_str(",\"detail\":");
        push_json_string(&mut out, &self.reason.detail);
        out.push_str("},\"seed\":");
        out.push_str(&self.seed.to_string());
        out.push_str(",\"sample_budget\":");
        out.push_str(&self.sample_budget.to_string());
        out.push_str(",\"inputs\":[");
        for (index, input) in self.inputs.iter().enumerate() {
            if index != 0 {
                out.push(',');
            }
            input.push_json(&mut out);
        }
        out.push_str("],\"violation_query_smt2\":");
        push_json_string(&mut out, &self.violation_query_smt2);
        out.push_str("}\n");
        out
    }
}

/// Owned description of one target input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TargetInput {
    /// Stable arena symbol name.
    pub name: String,
    /// Scalar sort.
    pub sort: Sort,
    /// Validated sampling domain.
    pub domain: FuzzDomain,
}

impl TargetInput {
    fn push_json(&self, out: &mut String) {
        out.push_str("{\"name\":");
        push_json_string(out, &self.name);
        out.push_str(",\"sort\":");
        match self.sort {
            Sort::Bool => push_json_string(out, "Bool"),
            Sort::BitVec(width) => push_json_string(out, &format!("(_ BitVec {width})")),
            _ => unreachable!("validated directed-fuzz input sort"),
        }
        match self.domain {
            FuzzDomain::Full => out.push_str(",\"domain\":{\"kind\":\"full\"}"),
            FuzzDomain::BitVecRange { min, max } => {
                out.push_str(",\"domain\":{\"kind\":\"unsigned-range\",\"min\":");
                push_json_string(out, &min.to_string());
                out.push_str(",\"max\":");
                push_json_string(out, &max.to_string());
                out.push('}');
            }
        }
        out.push('}');
    }
}

/// Accounting for the sampled-only branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirectedFuzzReport {
    /// Stable target ID.
    pub target_id: String,
    /// Requested samples.
    pub requested: usize,
    /// Samples satisfying every hypothesis.
    pub admitted: usize,
    /// Samples rejected by at least one hypothesis.
    pub guard_rejected: usize,
    /// Admitted samples on which reflection and source agree the goal fails.
    pub violations: usize,
    /// Admitted samples on which reflection and source differ.
    pub disagreements: usize,
    /// First agreed violation, if any.
    pub first_violation: Option<Vec<SampleValue>>,
    /// First reflection/source disagreement, if any.
    pub first_disagreement: Option<Vec<SampleValue>>,
}

impl DirectedFuzzReport {
    /// Returns canonical compact JSON with a trailing newline.
    #[must_use]
    pub fn to_json(&self) -> String {
        let mut out = String::new();
        out.push_str("{\"schema\":");
        push_json_string(&mut out, REPORT_SCHEMA);
        out.push_str(",\"target_id\":");
        push_json_string(&mut out, &self.target_id);
        out.push_str(",\"status\":\"fuzzed-only\",\"requested\":");
        out.push_str(&self.requested.to_string());
        out.push_str(",\"admitted\":");
        out.push_str(&self.admitted.to_string());
        out.push_str(",\"guard_rejected\":");
        out.push_str(&self.guard_rejected.to_string());
        out.push_str(",\"violations\":");
        out.push_str(&self.violations.to_string());
        out.push_str(",\"disagreements\":");
        out.push_str(&self.disagreements.to_string());
        out.push_str(",\"first_violation\":");
        push_sample_option(&mut out, self.first_violation.as_deref());
        out.push_str(",\"first_disagreement\":");
        push_sample_option(&mut out, self.first_disagreement.as_deref());
        out.push_str("}\n");
        out
    }
}

/// Disjoint result of proof, replayed refutation, or sampled-only follow-up.
#[derive(Debug, Clone)]
pub enum HybridOutcome {
    /// Checked proof of the goal.
    Proved(Box<EvidenceReport>),
    /// Solver countermodel after one successful caller-owned replay.
    RefutedReplayed(Model),
    /// Bounded testing caused only by the retained solver nondecision.
    FuzzedOnly {
        /// Exact nondecision reason.
        reason: UnknownReason,
        /// Canonical target material.
        target: DirectedFuzzTarget,
        /// Honest sampled-work accounting.
        report: DirectedFuzzReport,
    },
}

/// Fail-closed validation or execution error.
#[derive(Debug)]
#[non_exhaustive]
pub enum DirectedFuzzError {
    /// Target ID is not `[a-z][a-z0-9_]*`.
    InvalidId(String),
    /// At least one sample is required.
    ZeroSampleBudget,
    /// A symbol occurs more than once in the plan.
    DuplicateInput(SymbolId),
    /// Plan inputs are not in arena declaration order.
    InputOrder,
    /// Plan symbols do not exactly cover reachable free symbols.
    SymbolCoverage {
        /// Reachable free-symbol names in declaration order.
        expected: Vec<String>,
        /// Plan symbol names in declaration order.
        actual: Vec<String>,
    },
    /// A root formula is not Boolean.
    NonBooleanFormula(TermId),
    /// A reachable term is outside quantifier-free Bool/BV(1..=128).
    UnsupportedTerm(TermId, String),
    /// An input domain is incompatible with its symbol sort or bounds.
    InvalidDomain(SymbolId, String),
    /// The solver failed operationally; this never starts fuzzing.
    Solver(SolverError),
    /// Ground evaluation failed while sampling.
    Evaluation(IrError),
    /// A supposedly Boolean expression evaluated to another value kind.
    EvaluationSort(TermId),
    /// The caller rejected the already solver-replayed countermodel.
    CountermodelReplayFailed,
}

impl core::fmt::Display for DirectedFuzzError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidId(id) => write!(f, "invalid directed-fuzz target ID {id:?}"),
            Self::ZeroSampleBudget => f.write_str("directed-fuzz sample budget must be nonzero"),
            Self::DuplicateInput(symbol) => write!(f, "duplicate input symbol #{}", symbol.index()),
            Self::InputOrder => f.write_str("directed-fuzz inputs must be in declaration order"),
            Self::SymbolCoverage { expected, actual } => {
                write!(
                    f,
                    "input coverage mismatch: expected {expected:?}, got {actual:?}"
                )
            }
            Self::NonBooleanFormula(term) => write!(f, "formula #{} is not Boolean", term.index()),
            Self::UnsupportedTerm(term, why) => {
                write!(f, "term #{} is outside directed QF_BV: {why}", term.index())
            }
            Self::InvalidDomain(symbol, why) => {
                write!(f, "invalid domain for symbol #{}: {why}", symbol.index())
            }
            Self::Solver(error) => write!(f, "solver error: {error}"),
            Self::Evaluation(error) => write!(f, "sample evaluation failed: {error}"),
            Self::EvaluationSort(term) => {
                write!(f, "formula #{} did not evaluate to Bool", term.index())
            }
            Self::CountermodelReplayFailed => f.write_str("countermodel failed caller replay"),
        }
    }
}

impl core::error::Error for DirectedFuzzError {}

impl From<SolverError> for DirectedFuzzError {
    fn from(error: SolverError) -> Self {
        Self::Solver(error)
    }
}

impl From<IrError> for DirectedFuzzError {
    fn from(error: IrError) -> Self {
        Self::Evaluation(error)
    }
}

/// Proves once, replay-checks a refutation once, or fuzzes only an exact
/// structured nondecision.
///
/// `replay_countermodel` is called only for [`ProofOutcome::Disproved`].
/// `source_oracle` is called only for guard-admitted samples after
/// [`ProofOutcome::Unknown`].
///
/// # Errors
///
/// Returns [`DirectedFuzzError`] for malformed plans/queries, operational
/// solver/evaluator failures, or a failed caller countermodel replay.
pub fn check_with_directed_fuzz<R, O>(
    arena: &mut TermArena,
    hypotheses: &[TermId],
    goal: TermId,
    config: &SolverConfig,
    plan: DirectedFuzzPlan,
    replay_countermodel: R,
    mut source_oracle: O,
) -> Result<HybridOutcome, DirectedFuzzError>
where
    R: FnOnce(&Model) -> bool,
    O: FnMut(&[SampleValue]) -> bool,
{
    let target_inputs = validate(arena, hypotheses, goal, &plan)?;
    let negated_goal = arena.not(goal).map_err(SolverError::from)?;
    let mut assertions = hypotheses.to_vec();
    assertions.push(negated_goal);
    let violation_query_smt2 = write_script(arena, &assertions);

    match prove(arena, hypotheses, goal, config)? {
        ProofOutcome::Proved(report) => Ok(HybridOutcome::Proved(report)),
        ProofOutcome::Disproved(model) => {
            if replay_countermodel(&model) {
                Ok(HybridOutcome::RefutedReplayed(model))
            } else {
                Err(DirectedFuzzError::CountermodelReplayFailed)
            }
        }
        ProofOutcome::Unknown(reason) => {
            let report = run_samples(
                arena,
                hypotheses,
                goal,
                &plan,
                &target_inputs,
                &mut source_oracle,
            )?;
            let target = DirectedFuzzTarget {
                id: plan.id,
                reason: reason.clone(),
                seed: plan.seed,
                sample_budget: plan.sample_budget,
                inputs: target_inputs,
                violation_query_smt2,
            };
            Ok(HybridOutcome::FuzzedOnly {
                reason,
                target,
                report,
            })
        }
    }
}

fn validate(
    arena: &TermArena,
    hypotheses: &[TermId],
    goal: TermId,
    plan: &DirectedFuzzPlan,
) -> Result<Vec<TargetInput>, DirectedFuzzError> {
    for &formula in hypotheses.iter().chain(std::iter::once(&goal)) {
        if arena.sort_of(formula) != Sort::Bool {
            return Err(DirectedFuzzError::NonBooleanFormula(formula));
        }
    }

    if !plan
        .inputs
        .windows(2)
        .all(|pair| pair[0].symbol < pair[1].symbol)
    {
        return Err(DirectedFuzzError::InputOrder);
    }

    let mut reachable_symbols = BTreeSet::new();
    let mut seen_terms = BTreeSet::new();
    let mut stack: Vec<TermId> = hypotheses
        .iter()
        .copied()
        .chain(std::iter::once(goal))
        .collect();
    while let Some(term) = stack.pop() {
        if !seen_terms.insert(term) {
            continue;
        }
        match arena.sort_of(term) {
            Sort::Bool | Sort::BitVec(1..=128) => {}
            sort => {
                return Err(DirectedFuzzError::UnsupportedTerm(
                    term,
                    format!("unsupported sort {sort:?}"),
                ));
            }
        }
        match arena.node(term) {
            TermNode::BoolConst(_) | TermNode::BvConst { .. } => {}
            TermNode::Symbol(symbol) => {
                reachable_symbols.insert(*symbol);
            }
            TermNode::App { op, args } if qfbv_op(*op) => stack.extend(args.iter().copied()),
            TermNode::App { op, .. } => {
                return Err(DirectedFuzzError::UnsupportedTerm(
                    term,
                    format!("unsupported operator {op:?}"),
                ));
            }
            node => {
                return Err(DirectedFuzzError::UnsupportedTerm(
                    term,
                    format!("unsupported node {node:?}"),
                ));
            }
        }
    }

    let actual: BTreeSet<SymbolId> = plan.inputs.iter().map(|input| input.symbol).collect();
    if actual != reachable_symbols {
        return Err(DirectedFuzzError::SymbolCoverage {
            expected: symbol_names(arena, &reachable_symbols),
            actual: symbol_names(arena, &actual),
        });
    }

    plan.inputs
        .iter()
        .map(|input| {
            let (name, sort) = arena.symbol(input.symbol);
            validate_domain(input.symbol, sort, input.domain)?;
            Ok(TargetInput {
                name: name.to_owned(),
                sort,
                domain: input.domain,
            })
        })
        .collect()
}

fn qfbv_op(op: Op) -> bool {
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
            | Op::BvNeg
            | Op::BvAdd
            | Op::BvSub
            | Op::BvMul
            | Op::BvUdiv
            | Op::BvUrem
            | Op::BvSdiv
            | Op::BvSrem
            | Op::BvSmod
            | Op::BvShl
            | Op::BvLshr
            | Op::BvAshr
            | Op::BvUlt
            | Op::BvUle
            | Op::BvUgt
            | Op::BvUge
            | Op::BvSlt
            | Op::BvSle
            | Op::BvSgt
            | Op::BvSge
            | Op::Eq
            | Op::Ite
            | Op::BvComp
            | Op::Extract { .. }
            | Op::Concat
            | Op::ZeroExt { .. }
            | Op::SignExt { .. }
            | Op::RotateLeft { .. }
            | Op::RotateRight { .. }
    )
}

fn validate_domain(
    symbol: SymbolId,
    sort: Sort,
    domain: FuzzDomain,
) -> Result<(), DirectedFuzzError> {
    match (sort, domain) {
        (Sort::Bool | Sort::BitVec(1..=128), FuzzDomain::Full) => Ok(()),
        (Sort::BitVec(width @ 1..=128), FuzzDomain::BitVecRange { min, max }) => {
            let mask = width_mask(width);
            if min > max {
                Err(DirectedFuzzError::InvalidDomain(
                    symbol,
                    "range minimum exceeds maximum".to_owned(),
                ))
            } else if max > mask {
                Err(DirectedFuzzError::InvalidDomain(
                    symbol,
                    format!("range value exceeds {width}-bit width"),
                ))
            } else {
                Ok(())
            }
        }
        (Sort::Bool, FuzzDomain::BitVecRange { .. }) => Err(DirectedFuzzError::InvalidDomain(
            symbol,
            "Bool input cannot use a bit-vector range".to_owned(),
        )),
        (sort, _) => Err(DirectedFuzzError::InvalidDomain(
            symbol,
            format!("unsupported input sort {sort:?}"),
        )),
    }
}

fn run_samples<O>(
    arena: &TermArena,
    hypotheses: &[TermId],
    goal: TermId,
    plan: &DirectedFuzzPlan,
    target_inputs: &[TargetInput],
    source_oracle: &mut O,
) -> Result<DirectedFuzzReport, DirectedFuzzError>
where
    O: FnMut(&[SampleValue]) -> bool,
{
    let mut report = DirectedFuzzReport {
        target_id: plan.id.clone(),
        requested: plan.sample_budget,
        admitted: 0,
        guard_rejected: 0,
        violations: 0,
        disagreements: 0,
        first_violation: None,
        first_disagreement: None,
    };
    let mut state = plan.seed;

    for sample_index in 0..plan.sample_budget {
        let mut assignment = Assignment::new();
        let mut sample = Vec::with_capacity(plan.inputs.len());
        for (input, description) in plan.inputs.iter().zip(target_inputs) {
            let value = sampled_value(
                description.sort,
                description.domain,
                sample_index,
                &mut state,
            );
            assignment.set(input.symbol, value.clone());
            sample.push(SampleValue {
                symbol: input.symbol,
                name: description.name.clone(),
                value,
            });
        }

        let mut admitted = true;
        for &hypothesis in hypotheses {
            match eval(arena, hypothesis, &assignment)? {
                Value::Bool(true) => {}
                Value::Bool(false) => {
                    admitted = false;
                    break;
                }
                _ => return Err(DirectedFuzzError::EvaluationSort(hypothesis)),
            }
        }
        if !admitted {
            report.guard_rejected += 1;
            continue;
        }

        report.admitted += 1;
        let Value::Bool(reflected) = eval(arena, goal, &assignment)? else {
            return Err(DirectedFuzzError::EvaluationSort(goal));
        };
        let source = source_oracle(&sample);
        if reflected != source {
            report.disagreements += 1;
            if report.first_disagreement.is_none() {
                report.first_disagreement = Some(sample);
            }
        } else if !reflected {
            report.violations += 1;
            if report.first_violation.is_none() {
                report.first_violation = Some(sample);
            }
        }
    }
    Ok(report)
}

fn sampled_value(sort: Sort, domain: FuzzDomain, sample_index: usize, state: &mut u64) -> Value {
    match sort {
        Sort::Bool => {
            let value = if sample_index < CORNER_COUNT {
                sample_index % 2 == 1
            } else {
                next_u64(state) & 1 == 1
            };
            Value::Bool(value)
        }
        Sort::BitVec(width) => {
            let (min, max) = match domain {
                FuzzDomain::Full => (0, width_mask(width)),
                FuzzDomain::BitVecRange { min, max } => (min, max),
            };
            let value = if sample_index < CORNER_COUNT {
                corner(min, max, sample_index)
            } else {
                ranged_random(min, max, state)
            };
            Value::Bv { width, value }
        }
        _ => unreachable!("validated directed-fuzz scalar sort"),
    }
}

fn corner(min: u128, max: u128, index: usize) -> u128 {
    match index {
        0 => min,
        1 => min.saturating_add(1).min(max),
        2 => max,
        3 => max.saturating_sub(1).max(min),
        4 => min + (max - min) / 2,
        _ => unreachable!("corner index"),
    }
}

fn ranged_random(min: u128, max: u128, state: &mut u64) -> u128 {
    let raw = u128::from(next_u64(state)) << 64 | u128::from(next_u64(state));
    let span = max - min;
    if span == u128::MAX {
        raw
    } else {
        min + raw % (span + 1)
    }
}

fn next_u64(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(LCG_MULTIPLIER)
        .wrapping_add(LCG_INCREMENT);
    *state
}

const fn width_mask(width: u32) -> u128 {
    if width == 128 {
        u128::MAX
    } else {
        (1_u128 << width) - 1
    }
}

fn symbol_names(arena: &TermArena, symbols: &BTreeSet<SymbolId>) -> Vec<String> {
    symbols
        .iter()
        .map(|symbol| arena.symbol(*symbol).0.to_owned())
        .collect()
}

fn valid_id(id: &str) -> bool {
    let mut chars = id.chars();
    matches!(chars.next(), Some('a'..='z'))
        && chars.all(|character| {
            character.is_ascii_lowercase() || character.is_ascii_digit() || character == '_'
        })
}

fn unknown_kind_label(kind: UnknownKind) -> &'static str {
    match kind {
        UnknownKind::Timeout => "timeout",
        UnknownKind::ResourceLimit => "resource-limit",
        UnknownKind::MemoryLimit => "memory-limit",
        UnknownKind::NodeBudget => "node-budget",
        UnknownKind::EncodingBudget => "encoding-budget",
        UnknownKind::Incomplete => "incomplete",
        UnknownKind::Other => "other",
        _ => "unknown",
    }
}

fn push_sample_option(out: &mut String, sample: Option<&[SampleValue]>) {
    let Some(sample) = sample else {
        out.push_str("null");
        return;
    };
    out.push('[');
    for (index, value) in sample.iter().enumerate() {
        if index != 0 {
            out.push(',');
        }
        out.push_str("{\"name\":");
        push_json_string(out, &value.name);
        match value.value {
            Value::Bool(bit) => {
                out.push_str(",\"sort\":\"Bool\",\"value\":");
                out.push_str(if bit { "true" } else { "false" });
            }
            Value::Bv { width, value } => {
                out.push_str(",\"sort\":");
                push_json_string(out, &format!("(_ BitVec {width})"));
                out.push_str(",\"value\":");
                push_json_string(out, &value.to_string());
            }
            _ => unreachable!("validated sample value"),
        }
        out.push('}');
    }
    out.push(']');
}

fn push_json_string(out: &mut String, value: &str) {
    out.push('"');
    for character in value.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            character if character <= '\u{1f}' => {
                use core::fmt::Write as _;
                write!(out, "\\u{:04x}", u32::from(character)).expect("write to String");
            }
            character => out.push(character),
        }
    }
    out.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plan_rejects_invalid_fields() {
        let mut arena = TermArena::new();
        let symbol = arena.declare("x", Sort::Bool).expect("declare x");
        assert!(matches!(
            DirectedFuzzPlan::new("Bad-ID", vec![], 1),
            Err(DirectedFuzzError::InvalidId(_))
        ));
        assert!(matches!(
            DirectedFuzzPlan::new("valid", vec![], 0),
            Err(DirectedFuzzError::ZeroSampleBudget)
        ));
        assert!(matches!(
            DirectedFuzzPlan::new("valid", vec![FuzzInput::full(symbol); 2], 1),
            Err(DirectedFuzzError::DuplicateInput(_))
        ));
    }

    #[test]
    fn unknown_labels_are_exhaustive_for_current_kinds() {
        assert_eq!(unknown_kind_label(UnknownKind::Timeout), "timeout");
        assert_eq!(
            unknown_kind_label(UnknownKind::ResourceLimit),
            "resource-limit"
        );
        assert_eq!(unknown_kind_label(UnknownKind::MemoryLimit), "memory-limit");
        assert_eq!(unknown_kind_label(UnknownKind::NodeBudget), "node-budget");
        assert_eq!(
            unknown_kind_label(UnknownKind::EncodingBudget),
            "encoding-budget"
        );
        assert_eq!(unknown_kind_label(UnknownKind::Incomplete), "incomplete");
        assert_eq!(unknown_kind_label(UnknownKind::Other), "other");
    }

    #[test]
    fn width_128_full_sampling_is_overflow_free() {
        let mut state = 7;
        assert_eq!(
            sampled_value(Sort::BitVec(128), FuzzDomain::Full, 0, &mut state),
            Value::Bv {
                width: 128,
                value: 0
            }
        );
        assert_eq!(
            sampled_value(Sort::BitVec(128), FuzzDomain::Full, 2, &mut state),
            Value::Bv {
                width: 128,
                value: u128::MAX
            }
        );
        let Value::Bv { width, .. } =
            sampled_value(Sort::BitVec(128), FuzzDomain::Full, 9, &mut state)
        else {
            panic!("BV sample")
        };
        assert_eq!(width, 128);
    }

    #[test]
    fn json_escapes_controls() {
        let mut json = String::new();
        push_json_string(&mut json, "quote \" slash \\ line\n\t\u{0001}");
        assert_eq!(json, "\"quote \\\" slash \\\\ line\\n\\t\\u0001\"");
        assert!(!json.contains('\u{0001}'));
    }
}
