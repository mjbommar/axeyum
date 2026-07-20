//! CNF layer for Axeyum.
//!
//! This crate owns the first Phase 4 CNF contract: simple Tseitin encoding
//! from AIG, DIMACS parsing/writing, CNF evaluation, and lift maps from CNF
//! variables back to AIG literals. It also owns the first pure-Rust SAT adapter
//! path for CNF formulas.

use axeyum_aig::{Aig, AigLit, AigNode, AigNodeId};
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::hash::{BuildHasherDefault, Hasher};
use std::time::Duration;

// Monotonic clock: the browser has no `std` clock, so on wasm32 use `web-time`'s
// drop-in `Instant` (ADR-0017). Native targets use the std clock.
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

mod alethe;
mod bve;
mod compact;
mod drat;
mod gf2;
mod interpolant;
mod lrat;
mod proof_sat;
mod simplify;
mod vivify;
mod xor_cdcl;
mod xor_dpll;
mod xor_drat;
mod xor_extract;
mod xor_matrix;
mod xor_propagate;
mod xor_search;

pub use alethe::{
    AletheClause, AletheCommand, AletheError, AletheLit, AletheTerm, check_alethe,
    check_alethe_with, lrat_to_alethe, parse_alethe, write_alethe,
};
pub use bve::{
    BveOptions, BveOutcome, BveStats, Reconstruction, eliminate_variables,
    eliminate_variables_within,
};
pub use compact::{CompactMap, compact};
pub use drat::{DratError, DratStep, check_drat, parse_drat, write_drat};
pub use gf2::{Gf2Outcome, Gf2Solution, Gf2System};
pub use interpolant::{BoolExpr, propositional_interpolant};
pub use lrat::{LratError, LratStep, check_lrat, elaborate_drat_to_lrat, parse_lrat, write_lrat};
pub use proof_sat::{
    DEFAULT_PROOF_SAT_CONFLICT_LIMIT, ProofSolveOutcome, solve_with_drat_proof,
    solve_with_drat_proof_with_limits, solve_with_drat_proof_within,
};
pub use simplify::{SubsumeStats, simplify, simplify_within};
pub use vivify::{VivifyOptions, VivifyOutcome, VivifyStats, vivify, vivify_within};
pub use xor_cdcl::{XorCdclResult, solve_with_xor_cdcl};
pub use xor_dpll::{XorDpllResult, solve_with_xor};
pub use xor_drat::{MAX_XOR_WIDTH, XorGaussRefutation, xor_gauss_drat_refutation};
pub use xor_extract::{ExtractedXors, extract_xors};
pub use xor_matrix::{IncrementalXorMatrix, XorMatrixStep};
pub use xor_propagate::{XorPropagateStats, XorPropagation, xor_propagate};
pub use xor_search::{
    XorConstraintInput, XorImplication, XorImplied, constraints_from_pairs, xor_implications,
};

use rustsat::{
    solvers::{Solve, SolveIncremental, SolverResult as RustSatSolverResult},
    types::{
        Clause as RustSatClause, Lit as RustSatLit, TernaryVal as RustSatTernaryVal,
        Var as RustSatVar,
    },
};

/// Stable CNF variable ID.
///
/// Variables are zero-based internally and render as one-based DIMACS
/// variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CnfVar(u32);

impl CnfVar {
    /// Creates a variable from a zero-based index.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::VariableIndexTooLarge`] if `index` does not fit in
    /// the internal `u32` representation.
    pub fn new(index: usize) -> Result<Self, CnfError> {
        let index = u32::try_from(index).map_err(|_| CnfError::VariableIndexTooLarge { index })?;
        Ok(Self(index))
    }

    /// Zero-based variable index.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// One-based DIMACS variable number.
    pub fn dimacs(self) -> u32 {
        self.0 + 1
    }
}

/// A signed CNF literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CnfLit {
    var: CnfVar,
    negated: bool,
}

impl CnfLit {
    /// Creates a positive literal for `var`.
    pub fn positive(var: CnfVar) -> Self {
        Self {
            var,
            negated: false,
        }
    }

    /// Returns the variable referenced by this literal.
    pub fn var(self) -> CnfVar {
        self.var
    }

    /// Returns `true` if this literal is negated.
    pub fn is_negated(self) -> bool {
        self.negated
    }

    /// Returns the complement of this literal.
    #[must_use]
    pub fn negated(self) -> Self {
        Self {
            var: self.var,
            negated: !self.negated,
        }
    }

    /// Signed DIMACS literal.
    pub fn dimacs(self) -> i64 {
        let variable = i64::from(self.var.dimacs());
        if self.negated { -variable } else { variable }
    }
}

/// A disjunction of CNF literals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CnfClause {
    lits: Vec<CnfLit>,
}

impl CnfClause {
    /// Creates a clause from literals.
    pub fn new(lits: Vec<CnfLit>) -> Self {
        Self { lits }
    }

    /// Clause literals in stored order.
    pub fn lits(&self) -> &[CnfLit] {
        &self.lits
    }

    fn into_lits(self) -> Vec<CnfLit> {
        self.lits
    }

    fn evaluate(&self, assignment: &[bool]) -> bool {
        self.lits
            .iter()
            .copied()
            .any(|lit| eval_lit(lit, assignment))
    }
}

/// A CNF formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CnfFormula {
    variable_count: usize,
    literals: Vec<CnfLit>,
    clause_ends: Vec<u32>,
}

/// Exact retained-storage accounting for a CNF formula.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CnfStorageProfile {
    /// Number of clauses.
    pub clauses: usize,
    /// Number of literals across all clauses.
    pub literals: usize,
    /// Logical bytes occupied by the monotone clause-end array.
    pub clause_end_logical_bytes: usize,
    /// Logical bytes occupied by the literal arena.
    pub literal_logical_bytes: usize,
    /// Total logical bytes occupied by both flat arrays.
    pub arena_logical_bytes: usize,
    /// Allocated-capacity bytes held by both flat arrays.
    pub arena_capacity_bytes: usize,
    /// Conservative logical lower bound for the prior `Vec<CnfClause>` layout.
    pub legacy_logical_lower_bound_bytes: usize,
}

impl CnfStorageProfile {
    /// Returns whether all additive byte-accounting identities hold.
    pub fn invariants_hold(self) -> bool {
        self.arena_logical_bytes
            == self
                .clause_end_logical_bytes
                .saturating_add(self.literal_logical_bytes)
            && self.arena_capacity_bytes >= self.arena_logical_bytes
            && self.legacy_logical_lower_bound_bytes >= self.literal_logical_bytes
    }
}

/// Ordered borrowed clauses from one flat [`CnfFormula`].
#[derive(Debug, Clone)]
pub struct CnfClauses<'a> {
    formula: &'a CnfFormula,
    front: usize,
    back: usize,
}

impl<'a> Iterator for CnfClauses<'a> {
    type Item = &'a [CnfLit];

    fn next(&mut self) -> Option<Self::Item> {
        if self.front == self.back {
            return None;
        }
        let index = self.front;
        self.front += 1;
        self.formula.clause(index)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.back - self.front;
        (remaining, Some(remaining))
    }
}

impl DoubleEndedIterator for CnfClauses<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front == self.back {
            return None;
        }
        self.back -= 1;
        self.formula.clause(self.back)
    }
}

impl ExactSizeIterator for CnfClauses<'_> {}
impl std::iter::FusedIterator for CnfClauses<'_> {}

impl CnfFormula {
    fn checked_clause_end(&self, additional: usize) -> Result<u32, CnfError> {
        checked_literal_end(self.literals.len(), additional)
    }

    fn check_clause_lits(&self, lits: &[CnfLit]) -> Result<(), CnfError> {
        for lit in lits {
            self.check_var(lit.var())?;
        }
        Ok(())
    }

    fn append_clause_lits(&mut self, lits: &[CnfLit], end: u32) {
        self.literals.extend_from_slice(lits);
        self.clause_ends.push(end);
    }
}

impl CnfFormula {
    /// Creates an empty formula over `variable_count` variables.
    pub fn new(variable_count: usize) -> Self {
        Self {
            variable_count,
            literals: Vec::new(),
            clause_ends: Vec::new(),
        }
    }

    /// Number of variables.
    pub fn variable_count(&self) -> usize {
        self.variable_count
    }

    /// Number of clauses.
    pub fn clause_count(&self) -> usize {
        self.clause_ends.len()
    }

    /// Number of stored clause literals.
    pub fn literal_count(&self) -> usize {
        self.literals.len()
    }

    /// Returns one clause by insertion index.
    pub fn clause(&self, index: usize) -> Option<&[CnfLit]> {
        let end = usize::try_from(*self.clause_ends.get(index)?).ok()?;
        let start = if index == 0 {
            0
        } else {
            usize::try_from(self.clause_ends[index - 1]).ok()?
        };
        self.literals.get(start..end)
    }

    /// Formula clauses in stored order.
    pub fn clauses(&self) -> CnfClauses<'_> {
        CnfClauses {
            formula: self,
            front: 0,
            back: self.clause_count(),
        }
    }

    /// Exact retained-storage accounting for this formula.
    pub fn storage_profile(&self) -> CnfStorageProfile {
        let clause_end_logical_bytes = self
            .clause_count()
            .saturating_mul(std::mem::size_of::<u32>());
        let literal_logical_bytes = self
            .literal_count()
            .saturating_mul(std::mem::size_of::<CnfLit>());
        let arena_logical_bytes = clause_end_logical_bytes.saturating_add(literal_logical_bytes);
        let arena_capacity_bytes = self
            .clause_ends
            .capacity()
            .saturating_mul(std::mem::size_of::<u32>())
            .saturating_add(
                self.literals
                    .capacity()
                    .saturating_mul(std::mem::size_of::<CnfLit>()),
            );
        let legacy_logical_lower_bound_bytes = self
            .clause_count()
            .saturating_mul(std::mem::size_of::<CnfClause>())
            .saturating_add(literal_logical_bytes);
        CnfStorageProfile {
            clauses: self.clause_count(),
            literals: self.literal_count(),
            clause_end_logical_bytes,
            literal_logical_bytes,
            arena_logical_bytes,
            arena_capacity_bytes,
            legacy_logical_lower_bound_bytes,
        }
    }

    /// Adds one clause.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::InvalidVariable`] if a literal references a variable
    /// outside this formula, or [`CnfError::LiteralIndexTooLarge`] if the total
    /// literal count does not fit the formula's stable offset representation.
    pub fn add_clause(&mut self, clause: CnfClause) -> Result<(), CnfError> {
        self.check_clause_lits(clause.lits())?;
        let end = self.checked_clause_end(clause.lits().len())?;
        self.literals.extend(clause.into_lits());
        self.clause_ends.push(end);
        Ok(())
    }

    /// Adds one clause by copying its literal slice into the formula arena.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::InvalidVariable`] if a literal references a variable
    /// outside this formula, or [`CnfError::LiteralIndexTooLarge`] if the total
    /// literal count does not fit the formula's stable offset representation.
    pub fn add_clause_from_slice(&mut self, lits: &[CnfLit]) -> Result<(), CnfError> {
        self.check_clause_lits(lits)?;
        let end = self.checked_clause_end(lits.len())?;
        self.append_clause_lits(lits, end);
        Ok(())
    }

    /// Evaluates the formula under a full variable assignment.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::AssignmentLengthMismatch`] when the assignment
    /// length does not match [`CnfFormula::variable_count`].
    pub fn evaluate(&self, assignment: &[bool]) -> Result<bool, CnfError> {
        if assignment.len() != self.variable_count {
            return Err(CnfError::AssignmentLengthMismatch {
                expected: self.variable_count,
                found: assignment.len(),
            });
        }
        Ok(self
            .clauses()
            .all(|clause| clause.iter().copied().any(|lit| eval_lit(lit, assignment))))
    }

    /// Renders this formula as DIMACS CNF.
    pub fn to_dimacs(&self) -> String {
        let mut out = format!("p cnf {} {}\n", self.variable_count, self.clause_count());
        for clause in self.clauses() {
            for lit in clause {
                out.push_str(&lit.dimacs().to_string());
                out.push(' ');
            }
            out.push_str("0\n");
        }
        out
    }

    fn check_var(&self, var: CnfVar) -> Result<(), CnfError> {
        if var.index() < self.variable_count {
            Ok(())
        } else {
            Err(CnfError::InvalidVariable {
                variable: var.dimacs(),
                variable_count: self.variable_count,
            })
        }
    }
}

/// A full Boolean assignment for a CNF formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CnfAssignment {
    values: Vec<bool>,
}

impl CnfAssignment {
    /// Creates an assignment from variable values in zero-based CNF order.
    pub fn new(values: Vec<bool>) -> Self {
        Self { values }
    }

    /// Assignment values in zero-based CNF variable order.
    pub fn values(&self) -> &[bool] {
        &self.values
    }

    /// Number of assigned variables.
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Returns `true` when the assignment has no variables.
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Returns the value assigned to `variable`, if the assignment covers it.
    pub fn value(&self, variable: CnfVar) -> Option<bool> {
        self.values.get(variable.index()).copied()
    }

    /// Evaluates `formula` under this assignment.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::AssignmentLengthMismatch`] when the assignment length
    /// does not match the formula variable count.
    pub fn satisfies(&self, formula: &CnfFormula) -> Result<bool, CnfError> {
        formula.evaluate(&self.values)
    }
}

/// SAT backend capability flags for the CNF layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SatCapabilities {
    /// Solver is implemented in Rust and does not require a native C/C++
    /// dependency in the default Axeyum build.
    pub dependency: SatDependencyProfile,
    /// Solver accepts assumptions through its native API.
    pub assumptions: SatFeatureSupport,
    /// Solver can continue from an existing clause database.
    pub incremental: SatFeatureSupport,
    /// Solver can emit checkable unsat proofs through this adapter.
    pub proof_logging: SatFeatureSupport,
}

/// Native dependency profile for a SAT adapter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatDependencyProfile {
    /// Adapter has no native C/C++ solver dependency.
    PureRust,
    /// Adapter requires a native C/C++ solver dependency.
    Native,
}

/// Whether a SAT adapter feature is currently exposed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatFeatureSupport {
    /// Feature is supported.
    Supported,
    /// Feature is not supported.
    Unsupported,
}

/// CNF SAT solver trait.
pub trait SatSolver {
    /// Stable backend name for artifacts and diagnostics.
    fn name(&self) -> &'static str;

    /// Backend capabilities.
    fn capabilities(&self) -> SatCapabilities;

    /// Solves `formula`.
    ///
    /// # Errors
    ///
    /// Returns [`SatError`] for adapter failures or invalid models returned by
    /// the underlying solver. `unknown` is represented as [`SatResult::Unknown`],
    /// not an error.
    fn solve(&mut self, formula: &CnfFormula) -> Result<SatResult, SatError>;
}

/// SAT result for a CNF formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatResult {
    /// The formula is satisfiable under the included assignment.
    Sat(CnfAssignment),
    /// The formula is unsatisfiable. The first adapter does not provide a
    /// checkable proof, so this is lower assurance than future proof-backed
    /// results.
    Unsat(SatUnsatEvidence),
    /// The solver stopped before deciding satisfiability.
    Unknown(SatUnknownReason),
}

/// UNSAT evidence metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SatUnsatEvidence {
    /// Proof availability for this UNSAT result.
    pub proof: SatProofStatus,
    /// When the solve was under assumptions, the subset of those assumption
    /// literals that the solver found sufficient for the contradiction (its
    /// final-conflict core). Empty for an assumption-free solve. This is the
    /// path-pruning primitive for symbolic execution / reachability: it names the
    /// branch conditions that are *already* jointly infeasible.
    pub failed_assumptions: Vec<CnfLit>,
}

/// Proof status for an UNSAT result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatProofStatus {
    /// No proof artifact is available through this adapter.
    Unchecked,
    /// An independent DRAT proof of this unsat was produced and verified
    /// (the empty clause was derived and the proof passed `check_drat`).
    /// An unsat carrying this status is checked **by construction**.
    Checked,
}

/// Unknown result metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SatUnknownReason {
    /// Backend-provided diagnostic.
    pub detail: String,
}

/// SAT adapter errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatError {
    /// Error from the CNF layer.
    Cnf(CnfError),
    /// Formula has more variables than the adapter can submit.
    VariableCountTooLarge {
        /// Formula variable count.
        variable_count: usize,
    },
    /// The underlying solver returned an error.
    Solver(String),
    /// Solver reported `sat`, but the lifted assignment did not satisfy the CNF.
    InvalidModel,
}

impl From<CnfError> for SatError {
    fn from(error: CnfError) -> Self {
        Self::Cnf(error)
    }
}

impl core::fmt::Display for SatError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SatError::Cnf(error) => write!(f, "{error}"),
            SatError::VariableCountTooLarge { variable_count } => write!(
                f,
                "CNF variable count {variable_count} exceeds SAT adapter capacity"
            ),
            SatError::Solver(error) => write!(f, "SAT solver error: {error}"),
            SatError::InvalidModel => write!(f, "SAT solver returned an invalid model"),
        }
    }
}

impl core::error::Error for SatError {}

/// First pure-Rust SAT adapter, backed by `rustsat-batsat`.
#[derive(Debug, Default, Clone, Copy)]
pub struct RustSatBatsatSolver;

/// The randomness-related options used by the pinned `BatSat` adapter.
///
/// Axeyum currently constructs `rustsat-batsat` through its default solver
/// constructor, whose internal `BatSat` options are not mutable through the
/// wrapper API. Exposing the values read from [`batsat::SolverOpts::default`]
/// lets benchmark artifacts bind themselves to the *actual* options instead of
/// recording a decorative seed that the backend never consumed.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BatSatDeterminism {
    /// `BatSat`'s floating-point pseudorandom generator seed.
    pub random_seed: f64,
    /// Probability of choosing a random branching variable.
    pub random_var_freq: f64,
    /// Whether branching polarities are randomized.
    pub random_polarity: bool,
    /// Whether initial variable activities are randomized.
    pub random_initial_activity: bool,
}

/// Returns the randomness-related defaults used by [`RustSatBatsatSolver`].
///
/// This reads the pinned dependency's option object at runtime, so a future
/// dependency update changes the benchmark configuration identity rather than
/// silently reusing an old, hand-copied seed label.
#[must_use]
pub fn rustsat_batsat_determinism() -> BatSatDeterminism {
    let options = batsat::SolverOpts::default();
    BatSatDeterminism {
        random_seed: options.random_seed,
        random_var_freq: options.random_var_freq,
        random_polarity: options.rnd_pol,
        random_initial_activity: options.rnd_init_act,
    }
}

impl RustSatBatsatSolver {
    /// Creates a BatSat-backed CNF solver.
    pub fn new() -> Self {
        Self
    }
}

impl SatSolver for RustSatBatsatSolver {
    fn name(&self) -> &'static str {
        "rustsat-batsat"
    }

    fn capabilities(&self) -> SatCapabilities {
        SatCapabilities {
            dependency: SatDependencyProfile::PureRust,
            assumptions: SatFeatureSupport::Supported,
            incremental: SatFeatureSupport::Supported,
            proof_logging: SatFeatureSupport::Unsupported,
        }
    }

    fn solve(&mut self, formula: &CnfFormula) -> Result<SatResult, SatError> {
        solve_with_rustsat_batsat(formula)
    }
}

/// Solves `formula` with the first pure-Rust SAT adapter.
///
/// # Errors
///
/// Returns [`SatError`] for adapter failures or invalid models returned by the
/// underlying solver.
pub fn solve_with_rustsat_batsat(formula: &CnfFormula) -> Result<SatResult, SatError> {
    solve_with_rustsat_batsat_timeout(formula, None)
}

/// Solves `formula` with the first pure-Rust SAT adapter and an optional
/// cooperative wall-clock timeout.
///
/// The timeout is implemented through `BatSat`'s stop callback. `BatSat` checks
/// that callback at solver progress points, so the limit is cooperative rather
/// than a hard thread preemption boundary.
///
/// # Errors
///
/// Returns [`SatError`] for adapter failures or invalid models returned by the
/// underlying solver.
pub fn solve_with_rustsat_batsat_timeout(
    formula: &CnfFormula,
    timeout: Option<Duration>,
) -> Result<SatResult, SatError> {
    solve_with_rustsat_batsat_limits(formula, timeout, None)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BatSatStopReason {
    ResourceLimit,
    Timeout,
}

#[derive(Default)]
struct BatSatLimitCallbacks {
    deadline: Option<Instant>,
    progress_check_limit: Option<u64>,
    progress_checks: Cell<u64>,
    stop_reason: Cell<Option<BatSatStopReason>>,
}

impl batsat::Callbacks for BatSatLimitCallbacks {
    fn on_start(&mut self) {
        self.progress_checks.set(0);
        self.stop_reason.set(None);
    }

    fn stop(&self) -> bool {
        if let Some(limit) = self.progress_check_limit {
            let checks = self.progress_checks.get();
            if checks >= limit {
                self.stop_reason.set(Some(BatSatStopReason::ResourceLimit));
                return true;
            }
            self.progress_checks.set(checks.saturating_add(1));
        }
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            self.stop_reason.set(Some(BatSatStopReason::Timeout));
            return true;
        }
        false
    }
}

type LimitedBatSat = rustsat_batsat::Solver<BatSatLimitCallbacks>;

/// Solves `formula` with optional wall-clock and deterministic search limits.
///
/// `progress_check_limit` bounds the number of successful `BatSat`
/// `within_budget` callback polls. Those polls occur at deterministic solver
/// progress points for a fixed formula, solver version, options, and seed. The
/// unit is deliberately named rather than presented as a cross-solver conflict
/// count: `BatSat` does not expose its private conflict/propagation budget
/// setters through the `RustSAT` adapter.
///
/// A zero limit is useful for tests and causes the first budget poll to stop the
/// search. Reaching either limit returns [`SatResult::Unknown`], never a guessed
/// verdict.
///
/// # Errors
///
/// Returns [`SatError`] for adapter failures or invalid models returned by the
/// underlying solver.
pub fn solve_with_rustsat_batsat_limits(
    formula: &CnfFormula,
    timeout: Option<Duration>,
    progress_check_limit: Option<u64>,
) -> Result<SatResult, SatError> {
    let mut solver = LimitedBatSat::default();
    let timeout_deadline = timeout.and_then(|duration| Instant::now().checked_add(duration));
    {
        let callbacks = solver.batsat_mut().cb_mut();
        callbacks.deadline = timeout_deadline;
        callbacks.progress_check_limit = progress_check_limit;
    }
    reserve_rustsat_variables(&mut solver, formula.variable_count())?;
    for clause in formula.clauses() {
        solver
            .add_clause(rustsat_clause(clause)?)
            .map_err(|error| SatError::Solver(error.to_string()))?;
    }

    match solver
        .solve()
        .map_err(|error| SatError::Solver(error.to_string()))?
    {
        RustSatSolverResult::Sat => {
            let assignment = rustsat_assignment(&solver, formula.variable_count())?;
            if assignment.satisfies(formula)? {
                Ok(SatResult::Sat(assignment))
            } else {
                Err(SatError::InvalidModel)
            }
        }
        RustSatSolverResult::Unsat => Ok(SatResult::Unsat(SatUnsatEvidence {
            proof: SatProofStatus::Unchecked,
            failed_assumptions: Vec::new(), // one-shot solve has no assumptions
        })),
        RustSatSolverResult::Interrupted => {
            let callbacks = solver.batsat_ref().cb();
            let detail = match callbacks.stop_reason.get() {
                Some(BatSatStopReason::ResourceLimit) => format!(
                    "rustsat-batsat deterministic progress-check budget {} exhausted",
                    progress_check_limit.unwrap_or(0)
                ),
                Some(BatSatStopReason::Timeout) => "rustsat-batsat timeout".to_owned(),
                None => "rustsat-batsat interrupted".to_owned(),
            };
            Ok(SatResult::Unknown(SatUnknownReason { detail }))
        }
    }
}

#[derive(Default)]
struct DeadlineCallbacks {
    deadline: Option<Instant>,
    progress_check_limit: Option<u64>,
    progress_checks: Cell<u64>,
    stop_reason: Cell<Option<BatSatStopReason>>,
}

impl batsat::Callbacks for DeadlineCallbacks {
    fn on_start(&mut self) {
        self.progress_checks.set(0);
        self.stop_reason.set(None);
    }

    fn stop(&self) -> bool {
        if let Some(limit) = self.progress_check_limit {
            let checks = self.progress_checks.get();
            if checks >= limit {
                self.stop_reason.set(Some(BatSatStopReason::ResourceLimit));
                return true;
            }
            self.progress_checks.set(checks.saturating_add(1));
        }
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            self.stop_reason.set(Some(BatSatStopReason::Timeout));
            return true;
        }
        false
    }
}

type IncrementalBatSat = rustsat_batsat::Solver<DeadlineCallbacks>;

/// A warm, incremental CNF SAT solver over the pure-Rust `BatSat` adapter
/// (ADR-0009, stage 1).
///
/// Unlike [`solve_with_rustsat_batsat`], the solver instance persists across
/// [`IncrementalSat::solve`] calls: clauses added with
/// [`IncrementalSat::add_clause`] stay in the database and the solver's learned
/// clauses are reused. Assumptions passed to [`IncrementalSat::solve_assuming`]
/// hold for that one solve only — the mechanism behind SMT-LIB `push`/`pop`
/// (via selector literals) and `check-sat-assuming`.
///
/// The clause database is monotone (clauses are never removed); the variable
/// namespace grows as clauses reference higher variables. Every `sat` is
/// self-checked: the returned assignment must satisfy all accumulated clauses
/// and the assumptions. `unsat` is lower-assurance until a proof path exists,
/// matching the one-shot adapter (ADR-0007).
#[derive(Default)]
pub struct IncrementalSat {
    solver: IncrementalBatSat,
    clauses: Vec<CnfClause>,
    variable_count: usize,
}

impl core::fmt::Debug for IncrementalSat {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // The BatSat handle is opaque here; show the database
        // shape instead.
        f.debug_struct("IncrementalSat")
            .field("clauses", &self.clauses.len())
            .field("variable_count", &self.variable_count)
            .finish_non_exhaustive()
    }
}

impl IncrementalSat {
    /// Creates an empty incremental solver.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of variables reserved so far.
    pub fn variable_count(&self) -> usize {
        self.variable_count
    }

    /// Number of clauses added so far.
    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }

    /// Copies the persistent input-clause database into a standalone formula.
    ///
    /// Learned clauses are intentionally absent: this is the stable problem
    /// presented to the incremental core, not a serialization of opaque solver
    /// internals. The snapshot is suitable for exact cross-core diagnostics.
    ///
    /// # Panics
    ///
    /// Panics only if the solver's already-validated persistent clause database
    /// violates the formula representation invariant.
    #[must_use]
    pub fn formula_snapshot(&self) -> CnfFormula {
        let mut formula = CnfFormula::new(self.variable_count);
        for clause in &self.clauses {
            formula
                .add_clause(clause.clone())
                .expect("incremental clauses were validated when inserted");
        }
        formula
    }

    /// Reserves variable space up to `variable_count` variables.
    ///
    /// # Errors
    ///
    /// Returns [`SatError::VariableCountTooLarge`] if the count exceeds the
    /// adapter's variable limit.
    pub fn reserve(&mut self, variable_count: usize) -> Result<(), SatError> {
        if variable_count > self.variable_count {
            self.variable_count = variable_count;
        }
        reserve_rustsat_variables(&mut self.solver, self.variable_count)
    }

    /// Adds a clause to the persistent database.
    ///
    /// The variable namespace grows to cover the clause's literals.
    ///
    /// # Errors
    ///
    /// Returns [`SatError`] for adapter failures or variable counts beyond the
    /// adapter limit.
    pub fn add_clause(&mut self, clause: CnfClause) -> Result<(), SatError> {
        for lit in clause.lits() {
            let needed = lit.var().index() + 1;
            if needed > self.variable_count {
                self.variable_count = needed;
            }
        }
        reserve_rustsat_variables(&mut self.solver, self.variable_count)?;
        self.solver
            .add_clause(rustsat_clause(clause.lits())?)
            .map_err(|error| SatError::Solver(error.to_string()))?;
        self.clauses.push(clause);
        Ok(())
    }

    /// Solves the accumulated clauses, optionally bounded by a cooperative
    /// wall-clock timeout.
    ///
    /// # Errors
    ///
    /// Returns [`SatError`] for adapter failures or invalid models.
    pub fn solve(&mut self, timeout: Option<Duration>) -> Result<SatResult, SatError> {
        self.solve_with_limits(timeout, None)
    }

    /// Solves the accumulated clauses with optional wall-clock and deterministic
    /// progress-check limits.
    ///
    /// The deterministic unit matches [`solve_with_rustsat_batsat_limits`]: one
    /// successful `BatSat` `within_budget` callback poll. The counter is reset
    /// for every solve, including checks on a retained solver instance.
    ///
    /// # Errors
    ///
    /// Returns [`SatError`] for adapter failures or invalid models.
    pub fn solve_with_limits(
        &mut self,
        timeout: Option<Duration>,
        progress_check_limit: Option<u64>,
    ) -> Result<SatResult, SatError> {
        self.solve_inner(&[], timeout, progress_check_limit)
    }

    /// Solves the accumulated clauses under one-shot `assumptions`, which hold
    /// for this solve only.
    ///
    /// # Errors
    ///
    /// Returns [`SatError`] for adapter failures or invalid models.
    pub fn solve_assuming(
        &mut self,
        assumptions: &[CnfLit],
        timeout: Option<Duration>,
    ) -> Result<SatResult, SatError> {
        self.solve_assuming_with_limits(assumptions, timeout, None)
    }

    /// Solves under one-shot assumptions with optional wall-clock and
    /// deterministic progress-check limits.
    ///
    /// # Errors
    ///
    /// Returns [`SatError`] for adapter failures or invalid models.
    pub fn solve_assuming_with_limits(
        &mut self,
        assumptions: &[CnfLit],
        timeout: Option<Duration>,
        progress_check_limit: Option<u64>,
    ) -> Result<SatResult, SatError> {
        self.solve_inner(assumptions, timeout, progress_check_limit)
    }

    fn solve_inner(
        &mut self,
        assumptions: &[CnfLit],
        timeout: Option<Duration>,
        progress_check_limit: Option<u64>,
    ) -> Result<SatResult, SatError> {
        let timeout_deadline = timeout.and_then(|duration| Instant::now().checked_add(duration));
        // Store the deadline as data instead of BatSat's `Box<dyn Fn()>`. The
        // latter is not `Send`; an `Instant` is, so a warm solver can move to a
        // worker thread without unsafe code or a shared global context.
        {
            let callbacks = self.solver.batsat_mut().cb_mut();
            callbacks.deadline = timeout_deadline;
            callbacks.progress_check_limit = progress_check_limit;
        }

        let result = if assumptions.is_empty() {
            self.solver.solve()
        } else {
            let lits = assumptions
                .iter()
                .copied()
                .map(rustsat_lit)
                .collect::<Result<Vec<_>, _>>()?;
            self.solver.solve_assumps(&lits)
        }
        .map_err(|error| SatError::Solver(error.to_string()))?;

        match result {
            RustSatSolverResult::Sat => {
                let assignment = rustsat_assignment(&self.solver, self.variable_count)?;
                if self.assignment_is_model(&assignment, assumptions) {
                    Ok(SatResult::Sat(assignment))
                } else {
                    Err(SatError::InvalidModel)
                }
            }
            RustSatSolverResult::Unsat => {
                // Under assumptions, recover the solver's final-conflict core: the
                // subset of `assumptions` sufficient for the contradiction. The
                // solver returns it as the clause `⋁ ¬aᵢ`, so each core literal is
                // the negation of a failed assumption; map back and intersect with
                // the assumptions actually passed (defensive).
                let failed_assumptions = if assumptions.is_empty() {
                    Vec::new()
                } else {
                    let passed: std::collections::HashSet<CnfLit> =
                        assumptions.iter().copied().collect();
                    let core = self
                        .solver
                        .core()
                        .map_err(|error| SatError::Solver(error.to_string()))?;
                    let mut failed = Vec::new();
                    for core_lit in core {
                        let assumption = cnf_lit_from_rustsat(core_lit)?.negated();
                        if passed.contains(&assumption) {
                            failed.push(assumption);
                        }
                    }
                    failed
                };
                Ok(SatResult::Unsat(SatUnsatEvidence {
                    proof: SatProofStatus::Unchecked,
                    failed_assumptions,
                }))
            }
            RustSatSolverResult::Interrupted => {
                let detail = match self.solver.batsat_ref().cb().stop_reason.get() {
                    Some(BatSatStopReason::ResourceLimit) => format!(
                        "rustsat-batsat deterministic progress-check budget {} exhausted",
                        progress_check_limit.unwrap_or(0)
                    ),
                    Some(BatSatStopReason::Timeout) => "rustsat-batsat timeout".to_owned(),
                    None => "rustsat-batsat interrupted".to_owned(),
                };
                Ok(SatResult::Unknown(SatUnknownReason { detail }))
            }
        }
    }

    /// Checks a candidate model against every accumulated clause and assumption.
    fn assignment_is_model(&self, assignment: &CnfAssignment, assumptions: &[CnfLit]) -> bool {
        let values = assignment.values();
        self.clauses.iter().all(|clause| clause.evaluate(values))
            && assumptions.iter().all(|lit| eval_lit(*lit, values))
    }
}

/// Opt-in structural attribution for [`IncrementalCnf`].
///
/// Every field is monotone for the lifetime of one encoder. Ordinary
/// [`IncrementalCnf::new`] construction leaves the counters at zero and does
/// not run the local gate-shape or direct-root opportunity scans; use
/// [`IncrementalCnf::with_profiling`] when collecting diagnostics.
///
/// The five `*_half_definitions` fields form a partition of
/// `up_half_definitions + down_half_definitions`. They classify the local AIG
/// shape at the moment a primitive implication half is emitted. A shape hit is
/// an opportunity measurement, not evidence that the corresponding one-shot
/// fusion is incrementally admissible.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct IncrementalCnfStats {
    /// AND nodes discovered while synchronizing the growing AIG.
    pub and_nodes_synced: u64,
    /// Positive-use `v -> (lhs & rhs)` halves emitted.
    pub up_half_definitions: u64,
    /// Negative-use `(lhs & rhs) -> v` halves emitted.
    pub down_half_definitions: u64,
    /// Emitted half-definitions whose local AIG shape is XOR/XNOR-like.
    pub xor_half_definitions: u64,
    /// Emitted half-definitions whose local AIG shape is mux/ITE-like.
    pub not_ite_half_definitions: u64,
    /// Emitted half-definitions with at least one complemented AND child.
    pub not_and_half_definitions: u64,
    /// Emitted half-definitions with at least one positive AND child.
    pub and_tree_half_definitions: u64,
    /// Remaining primitive binary-AND half-definitions.
    pub binary_and_half_definitions: u64,
    /// Fresh positive internal AND-tree halves whose bounded flattening would
    /// emit fewer clauses than their primitive implication expansion.
    pub internal_positive_and_opportunities: u64,
    /// Opportunity nodes that would be bypassed by bounded flattening.
    pub internal_positive_and_opportunity_nodes: u64,
    /// Positive internal AND-tree halves actually flattened.
    pub internal_positive_and_flattened: u64,
    /// Primitive definition clauses avoided at the moment flattening applies.
    /// Later helper reuse can still emit those ordinary definitions.
    pub internal_positive_and_immediate_clauses_avoided: u64,
    /// Constant-node clauses emitted while synchronizing the AIG.
    pub constant_clauses: u64,
    /// Primitive AND implication clauses emitted by `require`.
    pub definition_clauses: u64,
    /// Unit or selector-guarded assertion clauses emitted for roots.
    pub root_clauses: u64,
    /// Asserted roots that are positive AND nodes and can be flattened safely.
    pub direct_positive_and_roots: u64,
    /// Unique positive AND nodes below those roots.
    pub direct_positive_and_nodes: u64,
    /// Unique non-positive-AND leaves below those roots.
    pub direct_positive_and_leaves: u64,
    /// Direct-root leaves whose local shape is XOR/XNOR-like.
    pub direct_xor_leaves: u64,
    /// Direct-root leaves whose local shape is mux/ITE-like.
    pub direct_not_ite_leaves: u64,
    /// Asserted roots that are complemented AND nodes.
    pub direct_negative_and_roots: u64,
    /// Positive AND roots actually encoded through the direct assertion path.
    pub fused_positive_and_roots: u64,
    /// Positive AND nodes bypassed by direct root-tree flattening.
    pub fused_positive_and_nodes: u64,
    /// Structural XOR leaves encoded directly without their outer/helper nodes.
    pub fused_xor_leaves: u64,
    /// Root assertions presented to the incremental encoder.
    pub root_assertions: u64,
    /// Root assertions protected by a scope selector.
    pub guarded_root_assertions: u64,
    /// Root assertions repeated with the same literal and selector context.
    pub repeated_same_context_roots: u64,
    /// Repeated same-context root assertions skipped by the production path.
    pub deduplicated_root_assertions: u64,
    /// Root literals reused under a different selector context.
    pub reused_cross_context_roots: u64,
    /// Root-derived clauses protected by a scope selector.
    pub guarded_root_clauses: u64,
    /// Root-derived clauses attempted by non-deduplicated root contexts.
    pub root_clause_attempts: u64,
    /// Root clauses whose assertion payload contains one literal.
    pub unit_payload_root_clauses: u64,
    /// Root clauses whose assertion payload contains two literals.
    pub binary_payload_root_clauses: u64,
    /// Root clauses whose assertion payload contains at least three literals.
    pub wide_payload_root_clauses: u64,
    /// Definition clauses exactly duplicating an earlier emitted clause.
    pub duplicate_definition_clauses: u64,
    /// Root clauses exactly duplicating an earlier emitted clause.
    pub duplicate_root_clauses: u64,
    /// Root clauses exactly duplicating an earlier root clause.
    pub duplicate_prior_root_clauses: u64,
    /// Root clauses duplicating an earlier constant or definition clause.
    pub root_clauses_duplicate_non_root: u64,
    /// Tautological definition clauses emitted by the primitive path.
    pub tautological_definition_clauses: u64,
    /// Tautological root clauses emitted by the assertion path.
    pub tautological_root_clauses: u64,
    /// Negative AND roots whose down half was not already present.
    pub fresh_negative_root_definitions: u64,
    /// Negative AND roots whose down half was already present.
    pub reused_negative_root_definitions: u64,
}

impl IncrementalCnfStats {
    /// Returns the saturating component-wise delta from `earlier` to `self`.
    #[must_use]
    pub fn delta_since(self, earlier: Self) -> Self {
        let root_residual = Self::root_residual_delta(&self, &earlier);
        Self {
            and_nodes_synced: self
                .and_nodes_synced
                .saturating_sub(earlier.and_nodes_synced),
            up_half_definitions: self
                .up_half_definitions
                .saturating_sub(earlier.up_half_definitions),
            down_half_definitions: self
                .down_half_definitions
                .saturating_sub(earlier.down_half_definitions),
            xor_half_definitions: self
                .xor_half_definitions
                .saturating_sub(earlier.xor_half_definitions),
            not_ite_half_definitions: self
                .not_ite_half_definitions
                .saturating_sub(earlier.not_ite_half_definitions),
            not_and_half_definitions: self
                .not_and_half_definitions
                .saturating_sub(earlier.not_and_half_definitions),
            and_tree_half_definitions: self
                .and_tree_half_definitions
                .saturating_sub(earlier.and_tree_half_definitions),
            binary_and_half_definitions: self
                .binary_and_half_definitions
                .saturating_sub(earlier.binary_and_half_definitions),
            internal_positive_and_opportunities: self
                .internal_positive_and_opportunities
                .saturating_sub(earlier.internal_positive_and_opportunities),
            internal_positive_and_opportunity_nodes: self
                .internal_positive_and_opportunity_nodes
                .saturating_sub(earlier.internal_positive_and_opportunity_nodes),
            internal_positive_and_flattened: self
                .internal_positive_and_flattened
                .saturating_sub(earlier.internal_positive_and_flattened),
            internal_positive_and_immediate_clauses_avoided: self
                .internal_positive_and_immediate_clauses_avoided
                .saturating_sub(earlier.internal_positive_and_immediate_clauses_avoided),
            constant_clauses: self
                .constant_clauses
                .saturating_sub(earlier.constant_clauses),
            definition_clauses: self
                .definition_clauses
                .saturating_sub(earlier.definition_clauses),
            root_clauses: self.root_clauses.saturating_sub(earlier.root_clauses),
            direct_positive_and_roots: self
                .direct_positive_and_roots
                .saturating_sub(earlier.direct_positive_and_roots),
            direct_positive_and_nodes: self
                .direct_positive_and_nodes
                .saturating_sub(earlier.direct_positive_and_nodes),
            direct_positive_and_leaves: self
                .direct_positive_and_leaves
                .saturating_sub(earlier.direct_positive_and_leaves),
            direct_xor_leaves: self
                .direct_xor_leaves
                .saturating_sub(earlier.direct_xor_leaves),
            direct_not_ite_leaves: self
                .direct_not_ite_leaves
                .saturating_sub(earlier.direct_not_ite_leaves),
            direct_negative_and_roots: self
                .direct_negative_and_roots
                .saturating_sub(earlier.direct_negative_and_roots),
            fused_positive_and_roots: self
                .fused_positive_and_roots
                .saturating_sub(earlier.fused_positive_and_roots),
            fused_positive_and_nodes: self
                .fused_positive_and_nodes
                .saturating_sub(earlier.fused_positive_and_nodes),
            fused_xor_leaves: self
                .fused_xor_leaves
                .saturating_sub(earlier.fused_xor_leaves),
            ..root_residual
        }
    }

    fn root_residual_delta(current: &Self, earlier: &Self) -> Self {
        Self {
            root_assertions: current
                .root_assertions
                .saturating_sub(earlier.root_assertions),
            guarded_root_assertions: current
                .guarded_root_assertions
                .saturating_sub(earlier.guarded_root_assertions),
            repeated_same_context_roots: current
                .repeated_same_context_roots
                .saturating_sub(earlier.repeated_same_context_roots),
            deduplicated_root_assertions: current
                .deduplicated_root_assertions
                .saturating_sub(earlier.deduplicated_root_assertions),
            reused_cross_context_roots: current
                .reused_cross_context_roots
                .saturating_sub(earlier.reused_cross_context_roots),
            guarded_root_clauses: current
                .guarded_root_clauses
                .saturating_sub(earlier.guarded_root_clauses),
            root_clause_attempts: current
                .root_clause_attempts
                .saturating_sub(earlier.root_clause_attempts),
            unit_payload_root_clauses: current
                .unit_payload_root_clauses
                .saturating_sub(earlier.unit_payload_root_clauses),
            binary_payload_root_clauses: current
                .binary_payload_root_clauses
                .saturating_sub(earlier.binary_payload_root_clauses),
            wide_payload_root_clauses: current
                .wide_payload_root_clauses
                .saturating_sub(earlier.wide_payload_root_clauses),
            duplicate_definition_clauses: current
                .duplicate_definition_clauses
                .saturating_sub(earlier.duplicate_definition_clauses),
            duplicate_root_clauses: current
                .duplicate_root_clauses
                .saturating_sub(earlier.duplicate_root_clauses),
            duplicate_prior_root_clauses: current
                .duplicate_prior_root_clauses
                .saturating_sub(earlier.duplicate_prior_root_clauses),
            root_clauses_duplicate_non_root: current
                .root_clauses_duplicate_non_root
                .saturating_sub(earlier.root_clauses_duplicate_non_root),
            tautological_definition_clauses: current
                .tautological_definition_clauses
                .saturating_sub(earlier.tautological_definition_clauses),
            tautological_root_clauses: current
                .tautological_root_clauses
                .saturating_sub(earlier.tautological_root_clauses),
            fresh_negative_root_definitions: current
                .fresh_negative_root_definitions
                .saturating_sub(earlier.fresh_negative_root_definitions),
            reused_negative_root_definitions: current
                .reused_negative_root_definitions
                .saturating_sub(earlier.reused_negative_root_definitions),
            ..Self::default()
        }
    }
}

/// Incremental Tseitin encoder over a warm [`IncrementalSat`] (ADR-0009 stage 2).
///
/// Encodes AIG nodes into CNF on demand as the AIG grows — one CNF variable per
/// node (simple per-node Tseitin) — and asserts roots, optionally guarded by a
/// selector variable so SMT-LIB `push`/`pop` scopes can be activated and
/// deactivated through assumptions. The one-variable-per-node mapping makes
/// lifting a SAT assignment back to AIG node values direct, which feeds the
/// existing symbol-model reconstruction and original-term replay.
///
/// Gate definitions use **lazy (on-demand) Plaisted–Greenbaum polarity
/// encoding**: an AND node's two implication halves are emitted only in the
/// polarity in which the node is actually *used*, and the opposite half is added
/// later if and only if an opposite-polarity use appears. This is the
/// satisfiability-preserving polarity optimization that the one-shot
/// [`tseitin_encode`] applies globally (it knows every use up front); here it is
/// applied incrementally, which is sound because the encoder only ever *adds*
/// clauses — never retracts — so a half emitted for an early use stays valid as
/// the formula grows, and a new use simply triggers the missing half. Gate
/// definitions are unconditional (only roots are selector-guarded), so push/pop
/// scopes do not interact with the polarity bookkeeping.
///
/// Because a node may be left polarity-underconstrained (its CNF variable can
/// take an arbitrary value the gate definition does not pin), the model lift
/// [`IncrementalCnf::aig_node_values`] reconstructs every node value by forward
/// evaluation from the input bits rather than reading internal node variables —
/// the same recompute-from-inputs discipline the one-shot sparse path uses.
///
/// Asserted positive AND roots are flattened directly into selector-guarded
/// conjunct clauses. Structural XOR leaves are likewise asserted with their two
/// truth clauses. These root-only transformations are sound under future reuse:
/// they do not mark any node definition as emitted, so a later opposite-polarity
/// or differently scoped occurrence can still trigger the ordinary lazy
/// definition. Other [`tseitin_encode`] gate fusions remain unported because
/// their global single-use plans are not stable as the AIG grows.
///
/// An already-installed `(root literal, selector)` assertion is not expanded a
/// second time. The exact context key keeps different scope selectors distinct,
/// while repeated assertions in one permanent or scoped frame reuse the clauses
/// already retained by the monotone SAT database.
#[derive(Debug, Default)]
pub struct IncrementalCnf {
    sat: IncrementalSat,
    node_var: Vec<CnfVar>,
    next_var: usize,
    /// AND-node children (`None` for inputs/const), parallel to `node_var`.
    and_children: Vec<Option<(AigLit, AigLit)>>,
    /// Whether the `v -> (lhs & rhs)` half has been emitted, parallel to `node_var`.
    emitted_up: Vec<bool>,
    /// Whether the `(lhs & rhs) -> v` half has been emitted, parallel to `node_var`.
    emitted_down: Vec<bool>,
    /// Enables bounded positive internal AND-tree implication flattening.
    internal_positive_and_flattening: bool,
    /// Reused bounded traversal stack for internal AND-tree admission.
    internal_and_stack: Vec<AigLit>,
    /// Reused unique AND nodes bypassed by an admitted flattening.
    internal_and_nodes: Vec<AigNodeId>,
    /// Reused conjunction leaves emitted by an admitted flattening.
    internal_and_leaves: Vec<AigLit>,
    profiling_enabled: bool,
    stats: IncrementalCnfStats,
    /// Canonical clauses seen by the opt-in diagnostic path only.
    profiled_clauses: BTreeSet<Vec<CnfLit>>,
    /// Canonical root clauses seen by the opt-in diagnostic path only.
    profiled_root_clauses: BTreeSet<Vec<CnfLit>>,
    /// `(node, inversion, selector)` root contexts seen by profiling.
    profiled_root_contexts: BTreeSet<(usize, bool, Option<usize>)>,
    /// Root literals seen under any selector context by profiling.
    profiled_root_literals: BTreeSet<(usize, bool)>,
    /// Root/selector contexts already installed in the persistent CNF.
    asserted_root_contexts: BTreeSet<(usize, bool, Option<usize>)>,
}

#[derive(Debug, Clone, Copy)]
enum IncrementalClauseKind {
    Constant,
    Definition,
    Root,
}

const INTERNAL_AND_FLATTEN_NODE_LIMIT: usize = 64;

impl IncrementalCnf {
    /// Creates an empty incremental encoder.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an encoder with experimental bounded positive internal AND-tree
    /// implication flattening.
    ///
    /// The policy is off by default. It applies only when every bypassed
    /// positive half is still fresh, the traversal stays within a fixed work
    /// bound, and direct leaf clauses are fewer than primitive implication
    /// clauses. Bypassed helper definitions remain unmarked and can be emitted
    /// normally if later assertions reuse them.
    pub fn with_internal_positive_and_flattening() -> Self {
        Self {
            internal_positive_and_flattening: true,
            ..Self::default()
        }
    }

    /// Creates an empty incremental encoder with structural attribution.
    ///
    /// Encoding semantics are unchanged. This opt-in constructor additionally
    /// counts emitted implication families and scans asserted roots for
    /// direct-root fusion opportunities.
    pub fn with_profiling() -> Self {
        Self {
            profiling_enabled: true,
            ..Self::default()
        }
    }

    /// Creates an encoder with both structural attribution and experimental
    /// positive internal AND-tree flattening enabled.
    pub fn with_profiling_and_internal_positive_and_flattening() -> Self {
        Self {
            internal_positive_and_flattening: true,
            profiling_enabled: true,
            ..Self::default()
        }
    }

    /// Returns the monotone opt-in structural counters.
    #[must_use]
    pub fn stats(&self) -> IncrementalCnfStats {
        self.stats
    }

    /// Number of CNF variables allocated so far (nodes plus selectors).
    pub fn variable_count(&self) -> usize {
        self.next_var
    }

    /// Number of clauses in the persistent database.
    pub fn clause_count(&self) -> usize {
        self.sat.clause_count()
    }

    /// Copies the persistent clause database and activates `assumptions` as
    /// positive unit clauses.
    ///
    /// Incremental BV scopes use positive selector assumptions. Materializing
    /// them as units yields a standalone CNF with the same active input problem
    /// for a fresh SAT core. Learned clauses are not exported.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::InvalidVariable`] if an assumption is outside the
    /// retained variable namespace.
    pub fn formula_snapshot_assuming(
        &self,
        assumptions: &[CnfVar],
    ) -> Result<CnfFormula, CnfError> {
        let mut formula = self.sat.formula_snapshot();
        for &var in assumptions {
            formula.add_clause(CnfClause::new(vec![CnfLit::positive(var)]))?;
        }
        Ok(formula)
    }

    fn alloc_var(&mut self) -> Result<CnfVar, SatError> {
        let var =
            CnfVar::new(self.next_var).map_err(|error| SatError::Solver(error.to_string()))?;
        self.next_var += 1;
        Ok(var)
    }

    /// Allocates a fresh selector variable for a push/pop scope.
    ///
    /// # Errors
    ///
    /// Returns [`SatError`] if the variable space is exhausted.
    pub fn fresh_selector(&mut self) -> Result<CnfVar, SatError> {
        let var = self.alloc_var()?;
        self.sat.reserve(self.next_var)?;
        Ok(var)
    }

    fn lit(&self, aig_lit: AigLit) -> CnfLit {
        let var = self.node_var[aig_lit.node().index()];
        let lit = CnfLit::positive(var);
        if aig_lit.is_inverted() {
            lit.negated()
        } else {
            lit
        }
    }

    fn record_profile_clause(&mut self, clause: &CnfClause, kind: IncrementalClauseKind) {
        let mut canonical = clause.lits().to_vec();
        canonical.sort_unstable();
        canonical.dedup();
        let tautological = canonical
            .windows(2)
            .any(|pair| pair[0].var() == pair[1].var());
        if tautological {
            match kind {
                IncrementalClauseKind::Definition => {
                    self.stats.tautological_definition_clauses =
                        self.stats.tautological_definition_clauses.saturating_add(1);
                }
                IncrementalClauseKind::Root => {
                    self.stats.tautological_root_clauses =
                        self.stats.tautological_root_clauses.saturating_add(1);
                }
                IncrementalClauseKind::Constant => {}
            }
            return;
        }

        let duplicate_root = matches!(kind, IncrementalClauseKind::Root)
            && !self.profiled_root_clauses.insert(canonical.clone());
        let duplicate_any = !self.profiled_clauses.insert(canonical);
        if duplicate_any {
            match kind {
                IncrementalClauseKind::Definition => {
                    self.stats.duplicate_definition_clauses =
                        self.stats.duplicate_definition_clauses.saturating_add(1);
                }
                IncrementalClauseKind::Root => {
                    self.stats.duplicate_root_clauses =
                        self.stats.duplicate_root_clauses.saturating_add(1);
                    if duplicate_root {
                        self.stats.duplicate_prior_root_clauses =
                            self.stats.duplicate_prior_root_clauses.saturating_add(1);
                    } else {
                        self.stats.root_clauses_duplicate_non_root =
                            self.stats.root_clauses_duplicate_non_root.saturating_add(1);
                    }
                }
                IncrementalClauseKind::Constant => {}
            }
        }
    }

    fn add_incremental_clause(
        &mut self,
        clause: CnfClause,
        kind: IncrementalClauseKind,
    ) -> Result<(), SatError> {
        if self.profiling_enabled {
            self.record_profile_clause(&clause, kind);
        }
        self.sat.add_clause(clause)?;
        if self.profiling_enabled {
            match kind {
                IncrementalClauseKind::Constant => {
                    self.stats.constant_clauses = self.stats.constant_clauses.saturating_add(1);
                }
                IncrementalClauseKind::Definition => {
                    self.stats.definition_clauses = self.stats.definition_clauses.saturating_add(1);
                }
                IncrementalClauseKind::Root => {
                    self.stats.root_clauses = self.stats.root_clauses.saturating_add(1);
                }
            }
        }
        Ok(())
    }

    /// Allocates a CNF variable for every new AIG node. AND-gate defining
    /// clauses are *not* emitted here; they are added lazily, in the needed
    /// polarity only, by [`IncrementalCnf::require`].
    fn sync(&mut self, aig: &Aig) -> Result<(), SatError> {
        for (id, node) in aig.nodes() {
            if id.index() < self.node_var.len() {
                continue;
            }
            let var = self.alloc_var()?;
            self.node_var.push(var);
            let children = match node {
                AigNode::ConstFalse => {
                    // Force the constant-false node's variable to false.
                    self.add_incremental_clause(
                        CnfClause::new(vec![CnfLit::positive(var).negated()]),
                        IncrementalClauseKind::Constant,
                    )?;
                    None
                }
                AigNode::Input(_) => {
                    // A free variable; no defining clause.
                    None
                }
                // Defer the `var <-> (lhs & rhs)` clauses to `require`, which
                // emits only the polarity halves that are actually used.
                AigNode::And(lhs, rhs) => {
                    if self.profiling_enabled {
                        self.stats.and_nodes_synced = self.stats.and_nodes_synced.saturating_add(1);
                    }
                    Some((lhs, rhs))
                }
            };
            self.and_children.push(children);
            self.emitted_up.push(false);
            self.emitted_down.push(false);
        }
        // Ensure the solver knows about every node variable, including inputs
        // that appear in no clause, so a returned assignment covers them.
        self.sat.reserve(self.next_var)?;
        Ok(())
    }

    /// Collects one fresh positive AND tree whose direct implication clauses
    /// are cheaper than recursively emitting primitive positive halves.
    ///
    /// XOR/XNOR and not-ITE shapes remain opaque leaves so the experiment does
    /// not silently subsume the separately attributed gate families. A fixed
    /// node bound makes rejected admission deterministic and prevents a DAG
    /// with heavy reconvergence from turning the scan into its own blow-up.
    fn collect_internal_positive_and_tree(
        &mut self,
        aig: &Aig,
        start: AigNodeId,
    ) -> Option<(usize, usize)> {
        self.internal_and_stack.clear();
        self.internal_and_nodes.clear();
        self.internal_and_leaves.clear();

        let Some(node @ AigNode::And(lhs, rhs)) = aig.node(start) else {
            return None;
        };
        if detect_xor_gate(aig, node).is_some() || detect_not_ite_gate(aig, node).is_some() {
            return None;
        }
        self.internal_and_nodes.push(start);
        self.internal_and_stack.push(lhs);
        self.internal_and_stack.push(rhs);

        while let Some(lit) = self.internal_and_stack.pop() {
            let child = lit.node();
            let nested = if lit.is_inverted() {
                false
            } else if let Some(node @ AigNode::And(_, _)) = aig.node(child) {
                detect_xor_gate(aig, node).is_none() && detect_not_ite_gate(aig, node).is_none()
            } else {
                false
            };
            if !nested {
                self.internal_and_leaves.push(lit);
                continue;
            }

            let child_index = child.index();
            if self.emitted_up[child_index] {
                return None;
            }
            if self.internal_and_nodes.contains(&child) {
                continue;
            }
            if self.internal_and_nodes.len() >= INTERNAL_AND_FLATTEN_NODE_LIMIT {
                return None;
            }
            self.internal_and_nodes.push(child);
            let Some(AigNode::And(lhs, rhs)) = aig.node(child) else {
                unreachable!("a nested AND was checked above");
            };
            self.internal_and_stack.push(lhs);
            self.internal_and_stack.push(rhs);
        }

        if self.internal_and_nodes.len() < 2 {
            return None;
        }
        self.internal_and_leaves.sort_unstable();
        self.internal_and_leaves.dedup();
        let primitive_clauses = self.internal_and_nodes.len().checked_mul(2)?;
        let immediate_clauses_avoided =
            primitive_clauses.checked_sub(self.internal_and_leaves.len())?;
        (immediate_clauses_avoided > 0)
            .then_some((self.internal_and_nodes.len(), immediate_clauses_avoided))
    }

    fn try_flatten_internal_positive_and(
        &mut self,
        aig: &Aig,
        start: AigNodeId,
        var: CnfLit,
        require_stack: &mut Vec<(AigNodeId, bool)>,
    ) -> Result<bool, SatError> {
        if !self.internal_positive_and_flattening && !self.profiling_enabled {
            return Ok(false);
        }
        let Some((nodes, immediate_clauses_avoided)) =
            self.collect_internal_positive_and_tree(aig, start)
        else {
            return Ok(false);
        };
        if self.profiling_enabled {
            self.stats.internal_positive_and_opportunities = self
                .stats
                .internal_positive_and_opportunities
                .saturating_add(1);
            self.stats.internal_positive_and_opportunity_nodes = self
                .stats
                .internal_positive_and_opportunity_nodes
                .saturating_add(usize_to_u64_saturating(nodes));
        }
        if !self.internal_positive_and_flattening {
            return Ok(false);
        }

        self.emitted_up[start.index()] = true;
        for index in 0..self.internal_and_leaves.len() {
            let leaf = self.internal_and_leaves[index];
            self.add_incremental_clause(
                CnfClause::new(vec![var.negated(), self.lit(leaf)]),
                IncrementalClauseKind::Definition,
            )?;
        }
        for index in 0..self.internal_and_leaves.len() {
            let leaf = self.internal_and_leaves[index];
            require_stack.push((leaf.node(), !leaf.is_inverted()));
        }
        if self.profiling_enabled {
            self.stats.internal_positive_and_flattened =
                self.stats.internal_positive_and_flattened.saturating_add(1);
            self.stats.internal_positive_and_immediate_clauses_avoided = self
                .stats
                .internal_positive_and_immediate_clauses_avoided
                .saturating_add(usize_to_u64_saturating(immediate_clauses_avoided));
        }
        Ok(true)
    }

    /// Lazily emits the Plaisted–Greenbaum half-definitions needed so that an
    /// occurrence of AIG node `start` in polarity `want_up` is sound.
    ///
    /// `want_up == true` means node `start` occurs positively (`+v`), which needs
    /// the `v -> (lhs & rhs)` implication; `false` means it occurs negatively
    /// (`¬v`), needing `(lhs & rhs) -> v`. Emitting a half introduces child
    /// occurrences whose polarities are propagated recursively. Each
    /// `(node, direction)` is emitted at most once, so the propagation is finite
    /// and monotone. An explicit work-stack avoids deep recursion on tall AIGs.
    fn require(&mut self, aig: &Aig, start: AigNodeId, want_up: bool) -> Result<(), SatError> {
        let mut stack = vec![(start, want_up)];
        while let Some((node_id, up)) = stack.pop() {
            let idx = node_id.index();
            // Only AND nodes carry a defining implication; inputs and the
            // constant are already fully determined.
            let Some((lhs, rhs)) = self.and_children[idx] else {
                continue;
            };
            let var = CnfLit::positive(self.node_var[idx]);
            let lhs_lit = self.lit(lhs);
            let rhs_lit = self.lit(rhs);
            if up {
                if self.emitted_up[idx] {
                    continue;
                }
                if self.try_flatten_internal_positive_and(aig, node_id, var, &mut stack)? {
                    continue;
                }
                self.emitted_up[idx] = true;
                // v -> (lhs & rhs): (¬v ∨ lhs)(¬v ∨ rhs).
                self.add_incremental_clause(
                    CnfClause::new(vec![var.negated(), lhs_lit]),
                    IncrementalClauseKind::Definition,
                )?;
                self.add_incremental_clause(
                    CnfClause::new(vec![var.negated(), rhs_lit]),
                    IncrementalClauseKind::Definition,
                )?;
                if self.profiling_enabled {
                    self.stats.up_half_definitions =
                        self.stats.up_half_definitions.saturating_add(1);
                    self.record_half_family(aig, node_id);
                }
                // Children occur with their own literal polarity: positive
                // occurrence needs `up`, negated occurrence needs `down`.
                stack.push((lhs.node(), !lhs.is_inverted()));
                stack.push((rhs.node(), !rhs.is_inverted()));
            } else {
                if self.emitted_down[idx] {
                    continue;
                }
                self.emitted_down[idx] = true;
                // (lhs & rhs) -> v: (v ∨ ¬lhs ∨ ¬rhs).
                self.add_incremental_clause(
                    CnfClause::new(vec![var, lhs_lit.negated(), rhs_lit.negated()]),
                    IncrementalClauseKind::Definition,
                )?;
                if self.profiling_enabled {
                    self.stats.down_half_definitions =
                        self.stats.down_half_definitions.saturating_add(1);
                    self.record_half_family(aig, node_id);
                }
                // Children appear negated here, flipping the required polarity:
                // a non-inverted child occurs negatively (needs `down`); an
                // inverted child occurs positively (needs `up`).
                stack.push((lhs.node(), lhs.is_inverted()));
                stack.push((rhs.node(), rhs.is_inverted()));
            }
        }
        Ok(())
    }

    fn record_half_family(&mut self, aig: &Aig, node_id: AigNodeId) {
        let Some(node @ AigNode::And(lhs, rhs)) = aig.node(node_id) else {
            unreachable!("only synchronized AND nodes receive half-definitions");
        };
        if detect_xor_gate(aig, node).is_some() {
            self.stats.xor_half_definitions = self.stats.xor_half_definitions.saturating_add(1);
        } else if detect_not_ite_gate(aig, node).is_some() {
            self.stats.not_ite_half_definitions =
                self.stats.not_ite_half_definitions.saturating_add(1);
        } else if [lhs, rhs].iter().any(|lit| {
            lit.is_inverted()
                && lit.node().index() != 0
                && matches!(aig.node(lit.node()), Some(AigNode::And(_, _)))
        }) {
            self.stats.not_and_half_definitions =
                self.stats.not_and_half_definitions.saturating_add(1);
        } else if [lhs, rhs].iter().any(|lit| {
            !lit.is_inverted()
                && lit.node().index() != 0
                && matches!(aig.node(lit.node()), Some(AigNode::And(_, _)))
        }) {
            self.stats.and_tree_half_definitions =
                self.stats.and_tree_half_definitions.saturating_add(1);
        } else {
            self.stats.binary_and_half_definitions =
                self.stats.binary_and_half_definitions.saturating_add(1);
        }
    }

    fn root_context(root: AigLit, selector: Option<CnfVar>) -> (usize, bool, Option<usize>) {
        (
            root.node().index(),
            root.is_inverted(),
            selector.map(CnfVar::index),
        )
    }

    fn record_root_assertion(&mut self, root: AigLit, selector: Option<CnfVar>) {
        self.stats.root_assertions = self.stats.root_assertions.saturating_add(1);
        if selector.is_some() {
            self.stats.guarded_root_assertions =
                self.stats.guarded_root_assertions.saturating_add(1);
        }

        let literal = (root.node().index(), root.is_inverted());
        let context = Self::root_context(root, selector);
        let seen_literal = !self.profiled_root_literals.insert(literal);
        if !self.profiled_root_contexts.insert(context) {
            self.stats.repeated_same_context_roots =
                self.stats.repeated_same_context_roots.saturating_add(1);
        } else if seen_literal {
            self.stats.reused_cross_context_roots =
                self.stats.reused_cross_context_roots.saturating_add(1);
        }
    }

    fn record_direct_root_opportunity(&mut self, aig: &Aig, root: AigLit) {
        let Some(AigNode::And(_, _)) = aig.node(root.node()) else {
            return;
        };
        if root.is_inverted() {
            self.stats.direct_negative_and_roots =
                self.stats.direct_negative_and_roots.saturating_add(1);
            if self.emitted_down[root.node().index()] {
                self.stats.reused_negative_root_definitions = self
                    .stats
                    .reused_negative_root_definitions
                    .saturating_add(1);
            } else {
                self.stats.fresh_negative_root_definitions =
                    self.stats.fresh_negative_root_definitions.saturating_add(1);
            }
            return;
        }

        self.stats.direct_positive_and_roots =
            self.stats.direct_positive_and_roots.saturating_add(1);
        let mut stack = vec![root];
        let mut and_nodes = BTreeSet::new();
        let mut leaves = BTreeSet::new();
        while let Some(lit) = stack.pop() {
            if !lit.is_inverted()
                && let Some(node @ AigNode::And(lhs, rhs)) = aig.node(lit.node())
            {
                if detect_xor_gate(aig, node).is_some() || detect_not_ite_gate(aig, node).is_some()
                {
                    leaves.insert(lit);
                } else if and_nodes.insert(lit.node()) {
                    stack.push(lhs);
                    stack.push(rhs);
                }
            } else {
                leaves.insert(lit);
            }
        }
        self.stats.direct_positive_and_nodes = self
            .stats
            .direct_positive_and_nodes
            .saturating_add(usize_to_u64_saturating(and_nodes.len()));
        self.stats.direct_positive_and_leaves = self
            .stats
            .direct_positive_and_leaves
            .saturating_add(usize_to_u64_saturating(leaves.len()));
        for leaf in leaves {
            let Some(node @ AigNode::And(_, _)) = aig.node(leaf.node()) else {
                continue;
            };
            if detect_xor_gate(aig, node).is_some() {
                self.stats.direct_xor_leaves = self.stats.direct_xor_leaves.saturating_add(1);
            } else if detect_not_ite_gate(aig, node).is_some() {
                self.stats.direct_not_ite_leaves =
                    self.stats.direct_not_ite_leaves.saturating_add(1);
            }
        }
    }

    fn direct_positive_root_leaves(
        aig: &Aig,
        root: AigLit,
    ) -> Option<(BTreeSet<AigNodeId>, BTreeSet<AigLit>)> {
        if root.is_inverted() || !matches!(aig.node(root.node()), Some(AigNode::And(_, _))) {
            return None;
        }

        let mut stack = vec![root];
        let mut and_nodes = BTreeSet::new();
        let mut leaves = BTreeSet::new();
        while let Some(lit) = stack.pop() {
            if !lit.is_inverted()
                && let Some(node @ AigNode::And(lhs, rhs)) = aig.node(lit.node())
            {
                // Preserve the XOR helper shape as one logical leaf. Unlike
                // global one-shot planning, this recognition does not depend
                // on current use counts.
                if detect_xor_gate(aig, node).is_some() || detect_not_ite_gate(aig, node).is_some()
                {
                    leaves.insert(lit);
                } else if and_nodes.insert(lit.node()) {
                    stack.push(lhs);
                    stack.push(rhs);
                }
            } else {
                leaves.insert(lit);
            }
        }
        Some((and_nodes, leaves))
    }

    fn add_root_clause(
        &mut self,
        selector: Option<CnfVar>,
        aig_lits: &[AigLit],
    ) -> Result<(), SatError> {
        let mut lits = Vec::with_capacity(aig_lits.len() + usize::from(selector.is_some()));
        if let Some(selector) = selector {
            lits.push(CnfLit::positive(selector).negated());
        }
        lits.extend(aig_lits.iter().copied().map(|lit| self.lit(lit)));
        let clause = CnfClause::new(lits);
        if self.profiling_enabled {
            self.stats.root_clause_attempts = self.stats.root_clause_attempts.saturating_add(1);
            if selector.is_some() {
                self.stats.guarded_root_clauses = self.stats.guarded_root_clauses.saturating_add(1);
            }
            match aig_lits.len() {
                0 | 1 => {
                    self.stats.unit_payload_root_clauses =
                        self.stats.unit_payload_root_clauses.saturating_add(1);
                }
                2 => {
                    self.stats.binary_payload_root_clauses =
                        self.stats.binary_payload_root_clauses.saturating_add(1);
                }
                _ => {
                    self.stats.wide_payload_root_clauses =
                        self.stats.wide_payload_root_clauses.saturating_add(1);
                }
            }
            self.record_profile_clause(&clause, IncrementalClauseKind::Root);
        }
        self.sat.add_clause(clause)?;
        if self.profiling_enabled {
            self.stats.root_clauses = self.stats.root_clauses.saturating_add(1);
        }
        Ok(())
    }

    fn assert_direct_xor_leaf(
        &mut self,
        aig: &Aig,
        leaf: AigLit,
        gate: XorGate,
        selector: Option<CnfVar>,
    ) -> Result<(), SatError> {
        let clauses = if leaf.is_inverted() {
            [
                [gate.lhs.negated(), gate.rhs],
                [gate.lhs, gate.rhs.negated()],
            ]
        } else {
            [
                [gate.lhs, gate.rhs],
                [gate.lhs.negated(), gate.rhs.negated()],
            ]
        };
        for clause in clauses {
            for lit in clause {
                self.require(aig, lit.node(), !lit.is_inverted())?;
            }
            self.add_root_clause(selector, &clause)?;
        }
        if self.profiling_enabled {
            self.stats.fused_xor_leaves = self.stats.fused_xor_leaves.saturating_add(1);
        }
        Ok(())
    }

    fn assert_direct_positive_root(
        &mut self,
        aig: &Aig,
        root: AigLit,
        selector: Option<CnfVar>,
    ) -> Result<bool, SatError> {
        let Some((and_nodes, leaves)) = Self::direct_positive_root_leaves(aig, root) else {
            return Ok(false);
        };
        if self.profiling_enabled {
            self.stats.fused_positive_and_roots =
                self.stats.fused_positive_and_roots.saturating_add(1);
            self.stats.fused_positive_and_nodes = self
                .stats
                .fused_positive_and_nodes
                .saturating_add(usize_to_u64_saturating(and_nodes.len()));
        }

        for leaf in leaves {
            let xor_gate = aig
                .node(leaf.node())
                .and_then(|node| detect_xor_gate(aig, node));
            if let Some(gate) = xor_gate {
                self.assert_direct_xor_leaf(aig, leaf, gate, selector)?;
            } else {
                self.require(aig, leaf.node(), !leaf.is_inverted())?;
                self.add_root_clause(selector, &[leaf])?;
            }
        }
        Ok(true)
    }

    /// Encodes any new AIG nodes, then asserts `root`.
    ///
    /// When `selector` is `Some`, the assertion is guarded so it holds only
    /// while that selector is assumed true in [`IncrementalCnf::solve`] — the
    /// mechanism behind push/pop scopes. When `None`, the root is asserted
    /// permanently.
    ///
    /// # Errors
    ///
    /// Returns [`SatError`] for adapter failures or variable-space exhaustion.
    pub fn assert_root(
        &mut self,
        aig: &Aig,
        root: AigLit,
        selector: Option<CnfVar>,
    ) -> Result<(), SatError> {
        self.sync(aig)?;
        if self.profiling_enabled {
            self.record_root_assertion(root, selector);
            self.record_direct_root_opportunity(aig, root);
        }
        let context = Self::root_context(root, selector);
        if self.asserted_root_contexts.contains(&context) {
            if self.profiling_enabled {
                self.stats.deduplicated_root_assertions =
                    self.stats.deduplicated_root_assertions.saturating_add(1);
            }
            return Ok(());
        }
        if self.assert_direct_positive_root(aig, root, selector)? {
            self.asserted_root_contexts.insert(context);
            return Ok(());
        }
        // The asserted clause contains `root` positively, so the root node
        // occurs positively iff it is not inverted: emit that polarity half.
        self.require(aig, root.node(), !root.is_inverted())?;
        self.add_root_clause(selector, &[root])?;
        self.asserted_root_contexts.insert(context);
        Ok(())
    }

    /// Solves with the given scope selectors assumed active (true).
    ///
    /// # Errors
    ///
    /// Returns [`SatError`] for adapter failures or invalid models.
    pub fn solve(
        &mut self,
        active_selectors: &[CnfVar],
        timeout: Option<Duration>,
    ) -> Result<SatResult, SatError> {
        self.solve_with_limits(active_selectors, timeout, None)
    }

    /// Solves with the given scope selectors and optional wall-clock and
    /// deterministic SAT progress-check limits.
    ///
    /// # Errors
    ///
    /// Returns [`SatError`] for adapter failures or invalid models.
    pub fn solve_with_limits(
        &mut self,
        active_selectors: &[CnfVar],
        timeout: Option<Duration>,
        progress_check_limit: Option<u64>,
    ) -> Result<SatResult, SatError> {
        if active_selectors.is_empty() {
            self.sat.solve_with_limits(timeout, progress_check_limit)
        } else {
            let assumptions = active_selectors
                .iter()
                .map(|&var| CnfLit::positive(var))
                .collect::<Vec<_>>();
            self.sat
                .solve_assuming_with_limits(&assumptions, timeout, progress_check_limit)
        }
    }

    /// Maps a satisfying assignment to AIG node values in node-id order, ready
    /// for the bit-lowering symbol-model reconstruction.
    ///
    /// Internal AND nodes may be polarity-underconstrained under lazy
    /// Plaisted–Greenbaum encoding, so their CNF variables are *not* trusted.
    /// Instead every node value is recomputed by a single forward pass over the
    /// AIG (nodes are in topological order, children before parents), reading
    /// only the free input variables from the assignment. The result is a
    /// consistent valuation of every gate, which the downstream replay check
    /// (`validate_aig_node_values`) requires.
    pub fn aig_node_values(&self, aig: &Aig, assignment: &CnfAssignment) -> Vec<bool> {
        let assigned = assignment.values();
        let mut values = vec![false; aig.node_count()];
        for (id, node) in aig.nodes() {
            let idx = id.index();
            values[idx] = match node {
                AigNode::ConstFalse => false,
                AigNode::Input(_) => self
                    .node_var
                    .get(idx)
                    .and_then(|var| assigned.get(var.index()).copied())
                    .unwrap_or(false),
                AigNode::And(lhs, rhs) => {
                    aig_lit_in_values(lhs, &values) && aig_lit_in_values(rhs, &values)
                }
            };
        }
        values
    }
}

/// CNF variable to AIG literal lift-map entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CnfVarBinding {
    /// CNF variable.
    pub variable: CnfVar,
    /// Positive AIG literal represented by the variable.
    pub aig_literal: AigLit,
}

/// Encoded root mapping.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CnfRoot {
    /// Source AIG root.
    pub aig_literal: AigLit,
    /// CNF-side representation of the asserted root.
    ///
    /// Assertion-only roots may be encoded directly into clauses without a
    /// dedicated root variable; those roots are represented as
    /// [`EncodedLit::Const`] with value `true` because the formula already
    /// asserts them.
    pub cnf_lit: EncodedLit,
}

/// A CNF-side literal or constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EncodedLit {
    /// Boolean constant.
    Const(bool),
    /// Concrete CNF literal.
    Lit(CnfLit),
}

impl EncodedLit {
    fn negated(self) -> Self {
        match self {
            EncodedLit::Const(value) => EncodedLit::Const(!value),
            EncodedLit::Lit(lit) => EncodedLit::Lit(lit.negated()),
        }
    }
}

/// Opt-in attribution for literal canonicalization and clause-index work.
///
/// The ordinary [`tseitin_encode`] route returns the all-zero, incomplete
/// value. [`tseitin_encode_profiled`] selects a separate monomorphized encoder
/// whose profiling storage and counter updates do not exist on the ordinary
/// route.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CnfConstructionProfile {
    /// Whether every detailed construction counter was collected.
    pub profile_complete: bool,
    /// Literals declared by all clause-emission attempts.
    pub declared_clause_literals: u64,
    /// Literals visited before canonicalization returned or completed.
    pub visited_clause_literals: u64,
    /// Constant-false literals discarded from clauses.
    pub false_constants_dropped: u64,
    /// Repeated literals discarded from clauses.
    pub repeated_literals_dropped: u64,
    /// Tautologies detected from a constant-true literal.
    pub true_constant_tautologies: u64,
    /// Tautologies detected from complementary concrete literals.
    pub complementary_literal_tautologies: u64,
    /// Total literals in canonical non-tautological clause attempts.
    pub canonical_literals: u64,
    /// Canonical empty-clause attempts.
    pub canonical_empty_clauses: u64,
    /// Canonical unit-clause attempts.
    pub canonical_unit_clauses: u64,
    /// Canonical binary-clause attempts.
    pub canonical_binary_clauses: u64,
    /// Canonical ternary-clause attempts.
    pub canonical_ternary_clauses: u64,
    /// Canonical attempts containing four or more literals.
    pub canonical_larger_clauses: u64,
    /// Fingerprint lookups whose primary slot was vacant.
    pub primary_vacant_probes: u64,
    /// Fingerprint lookups whose primary slot was occupied.
    pub primary_occupied_probes: u64,
    /// Duplicates equal to the primary clause for their fingerprint.
    pub primary_exact_duplicates: u64,
    /// Exact clause comparisons against collision-bucket entries.
    pub collision_bucket_comparisons: u64,
    /// Duplicates found in a collision bucket.
    pub collision_exact_duplicates: u64,
    /// Distinct clauses inserted behind an occupied equal-fingerprint slot.
    pub collision_inserts: u64,
}

/// Encoding phase that attempted a canonical CNF clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CnfClauseOriginPhase {
    /// Clause emitted while defining a retained non-root gate.
    Gate,
    /// Clause emitted while directly encoding or asserting a root.
    Root,
}

impl CnfClauseOriginPhase {
    /// Stable artifact spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Gate => "gate",
            Self::Root => "root",
        }
    }
}

/// Stable family/direction/template slot for one CNF clause attempt.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum CnfClauseOriginTemplate {
    /// XOR forward clause with positive inputs.
    XorForwardPositiveInputs,
    /// XOR forward clause with negative inputs.
    XorForwardNegativeInputs,
    /// XOR reverse clause negating the left input.
    XorReverseLeftNegative,
    /// XOR reverse clause negating the right input.
    XorReverseRightNegative,
    /// Not-ITE forward then-arm clause.
    NotIteForwardThen,
    /// Not-ITE forward else-arm clause.
    NotIteForwardElse,
    /// Not-ITE reverse then-arm clause.
    NotIteReverseThen,
    /// Not-ITE reverse else-arm clause.
    NotIteReverseElse,
    /// Not-AND forward clause for a literal factor.
    NotAndForwardLiteral,
    /// Not-AND forward clause for a complemented-AND factor.
    NotAndForwardNested,
    /// Not-AND reverse clause for two literal factors.
    NotAndReverseLiteralPair,
    /// Not-AND reverse clause for literal/nested factors, nested left child.
    NotAndReverseLiteralNestedLeft,
    /// Not-AND reverse clause for literal/nested factors, nested right child.
    NotAndReverseLiteralNestedRight,
    /// Not-AND reverse clause for nested/literal factors, nested left child.
    NotAndReverseNestedLiteralLeft,
    /// Not-AND reverse clause for nested/literal factors, nested right child.
    NotAndReverseNestedLiteralRight,
    /// Not-AND reverse nested/nested `aa` product.
    NotAndReverseNestedNestedAa,
    /// Not-AND reverse nested/nested `ab` product.
    NotAndReverseNestedNestedAb,
    /// Not-AND reverse nested/nested `ba` product.
    NotAndReverseNestedNestedBa,
    /// Not-AND reverse nested/nested `bb` product.
    NotAndReverseNestedNestedBb,
    /// AND-tree forward clause for a literal leaf.
    AndTreeForwardLiteral,
    /// AND-tree forward clause for a complemented-AND leaf.
    AndTreeForwardNotAnd,
    /// AND-tree forward parity-implication clause.
    AndTreeForwardParity,
    /// AND-tree reverse long clause.
    AndTreeReverse,
    /// Binary-AND forward clause for the left input.
    BinaryAndForwardLhs,
    /// Binary-AND forward clause for the right input.
    BinaryAndForwardRhs,
    /// Binary-AND reverse clause.
    BinaryAndReverse,
    /// Direct negative-AND distribution leaf clause.
    DirectNegativeAndLeaf,
    /// Ordinary unit root assertion.
    RootUnit,
}

impl CnfClauseOriginTemplate {
    /// Stable `family/direction/template` artifact spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::XorForwardPositiveInputs => "xor/forward/positive_inputs",
            Self::XorForwardNegativeInputs => "xor/forward/negative_inputs",
            Self::XorReverseLeftNegative => "xor/reverse/left_negative",
            Self::XorReverseRightNegative => "xor/reverse/right_negative",
            Self::NotIteForwardThen => "not_ite/forward/then",
            Self::NotIteForwardElse => "not_ite/forward/else",
            Self::NotIteReverseThen => "not_ite/reverse/then",
            Self::NotIteReverseElse => "not_ite/reverse/else",
            Self::NotAndForwardLiteral => "not_and/forward/literal",
            Self::NotAndForwardNested => "not_and/forward/nested",
            Self::NotAndReverseLiteralPair => "not_and/reverse/literal_pair",
            Self::NotAndReverseLiteralNestedLeft => "not_and/reverse/literal_nested_left",
            Self::NotAndReverseLiteralNestedRight => "not_and/reverse/literal_nested_right",
            Self::NotAndReverseNestedLiteralLeft => "not_and/reverse/nested_literal_left",
            Self::NotAndReverseNestedLiteralRight => "not_and/reverse/nested_literal_right",
            Self::NotAndReverseNestedNestedAa => "not_and/reverse/nested_nested_aa",
            Self::NotAndReverseNestedNestedAb => "not_and/reverse/nested_nested_ab",
            Self::NotAndReverseNestedNestedBa => "not_and/reverse/nested_nested_ba",
            Self::NotAndReverseNestedNestedBb => "not_and/reverse/nested_nested_bb",
            Self::AndTreeForwardLiteral => "and_tree/forward/literal",
            Self::AndTreeForwardNotAnd => "and_tree/forward/not_and",
            Self::AndTreeForwardParity => "and_tree/forward/parity",
            Self::AndTreeReverse => "and_tree/reverse/long",
            Self::BinaryAndForwardLhs => "binary_and/forward/lhs",
            Self::BinaryAndForwardRhs => "binary_and/forward/rhs",
            Self::BinaryAndReverse => "binary_and/reverse/clause",
            Self::DirectNegativeAndLeaf => "direct_negative_and/direct/leaf",
            Self::RootUnit => "root/assertion/unit",
        }
    }
}

/// Owner-independent origin site used in duplicate matrices.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct CnfClauseOriginSite {
    /// Gate or root encoding phase.
    pub phase: CnfClauseOriginPhase,
    /// Stable family/direction/template slot.
    pub template: CnfClauseOriginTemplate,
}

impl CnfClauseOriginSite {
    /// Creates a stable clause-origin site.
    pub const fn new(phase: CnfClauseOriginPhase, template: CnfClauseOriginTemplate) -> Self {
        Self { phase, template }
    }

    /// Stable `phase/family/direction/template` artifact key.
    pub fn stable_key(self) -> String {
        format!("{}/{}", self.phase.as_str(), self.template.as_str())
    }
}

/// One nonzero first-origin/duplicate-origin/owner-relation cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CnfDuplicateOriginRow {
    /// Origin site of the first emitted equal clause.
    pub first_origin: CnfClauseOriginSite,
    /// Origin site of the later rejected duplicate.
    pub duplicate_origin: CnfClauseOriginSite,
    /// Whether both attempts belong to the same AIG owner node.
    pub same_owner: bool,
    /// Exact duplicate attempts in this cell.
    pub duplicate_clauses: u64,
    /// Canonical literals visited by duplicate attempts in this cell.
    pub duplicate_canonical_literals: u64,
    /// Empty duplicate clauses.
    pub empty_clauses: u64,
    /// Canonical literals in empty duplicate clauses (always zero).
    pub empty_literals: u64,
    /// Unit duplicate clauses.
    pub unit_clauses: u64,
    /// Canonical literals in unit duplicate clauses.
    pub unit_literals: u64,
    /// Binary duplicate clauses.
    pub binary_clauses: u64,
    /// Canonical literals in binary duplicate clauses.
    pub binary_literals: u64,
    /// Ternary duplicate clauses.
    pub ternary_clauses: u64,
    /// Canonical literals in ternary duplicate clauses.
    pub ternary_literals: u64,
    /// Duplicate clauses containing four or more literals.
    pub larger_clauses: u64,
    /// Canonical literals in duplicate clauses containing four or more literals.
    pub larger_literals: u64,
}

impl CnfDuplicateOriginRow {
    fn new(first: CnfClauseOriginSite, duplicate: CnfClauseOriginSite, same_owner: bool) -> Self {
        Self {
            first_origin: first,
            duplicate_origin: duplicate,
            same_owner,
            duplicate_clauses: 0,
            duplicate_canonical_literals: 0,
            empty_clauses: 0,
            empty_literals: 0,
            unit_clauses: 0,
            unit_literals: 0,
            binary_clauses: 0,
            binary_literals: 0,
            ternary_clauses: 0,
            ternary_literals: 0,
            larger_clauses: 0,
            larger_literals: 0,
        }
    }

    fn record(&mut self, len: usize) {
        let literals = usize_to_u64_saturating(len);
        self.duplicate_clauses = self.duplicate_clauses.saturating_add(1);
        self.duplicate_canonical_literals =
            self.duplicate_canonical_literals.saturating_add(literals);
        let (clauses, bucket_literals) = match len {
            0 => (&mut self.empty_clauses, &mut self.empty_literals),
            1 => (&mut self.unit_clauses, &mut self.unit_literals),
            2 => (&mut self.binary_clauses, &mut self.binary_literals),
            3 => (&mut self.ternary_clauses, &mut self.ternary_literals),
            _ => (&mut self.larger_clauses, &mut self.larger_literals),
        };
        *clauses = clauses.saturating_add(1);
        *bucket_literals = bucket_literals.saturating_add(literals);
    }

    fn length_clauses(&self) -> u64 {
        self.empty_clauses
            .saturating_add(self.unit_clauses)
            .saturating_add(self.binary_clauses)
            .saturating_add(self.ternary_clauses)
            .saturating_add(self.larger_clauses)
    }

    fn length_literals(&self) -> u64 {
        self.empty_literals
            .saturating_add(self.unit_literals)
            .saturating_add(self.binary_literals)
            .saturating_add(self.ternary_literals)
            .saturating_add(self.larger_literals)
    }
}

/// Bounded structural shape of one direct parity leaf.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct CnfParityLeafShape {
    /// Raw input occurrences before clause canonicalization.
    pub raw_arity: u8,
    /// Non-inverted constant-false input occurrences.
    pub false_constants: u8,
    /// Inverted constant-true input occurrences.
    pub true_constants: u8,
    /// Distinct nonconstant AIG nodes referenced by the inputs.
    pub distinct_nonconstant_nodes: u8,
    /// Equal-literal pairs among the raw input occurrences.
    pub repeated_literal_pairs: u8,
    /// Same-node/opposite-polarity pairs among the raw input occurrences.
    pub complementary_literal_pairs: u8,
}

impl CnfParityLeafShape {
    /// Stable compact artifact spelling.
    pub fn stable_key(self) -> String {
        format!(
            "a{}-f{}-t{}-d{}-r{}-x{}",
            self.raw_arity,
            self.false_constants,
            self.true_constants,
            self.distinct_nonconstant_nodes,
            self.repeated_literal_pairs,
            self.complementary_literal_pairs,
        )
    }

    /// Checks the fixed one-to-three-input shape bounds.
    pub fn invariants_hold(self) -> bool {
        let constants = self.false_constants.saturating_add(self.true_constants);
        let nonconstants = self.raw_arity.saturating_sub(constants);
        let pair_count = self
            .raw_arity
            .saturating_mul(self.raw_arity.saturating_sub(1))
            / 2;
        (1..=3).contains(&self.raw_arity)
            && constants <= self.raw_arity
            && self.distinct_nonconstant_nodes <= nonconstants
            && (nonconstants == 0 || self.distinct_nonconstant_nodes > 0)
            && self.repeated_literal_pairs <= pair_count
            && self.complementary_literal_pairs <= pair_count
            && self
                .repeated_literal_pairs
                .saturating_add(self.complementary_literal_pairs)
                <= pair_count
    }
}

/// Relationship between two equal parity clauses' enclosing leaves.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CnfParityOverlapRelation {
    /// Both clauses were attempted by the same leaf of the same owner.
    WithinLeaf,
    /// Clauses came from different leaves under the same owner.
    CrossLeafSameOwner,
    /// Clauses came from different owners.
    CrossOwner,
}

impl CnfParityOverlapRelation {
    /// Stable artifact spelling.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::WithinLeaf => "within_leaf",
            Self::CrossLeafSameOwner => "cross_leaf_same_owner",
            Self::CrossOwner => "cross_owner",
        }
    }
}

/// One nonzero parity-clause overlap relation/shape cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CnfParityOverlapRow {
    /// Within-leaf, cross-leaf/same-owner, or cross-owner relation.
    pub relation: CnfParityOverlapRelation,
    /// Shape of the first leaf that emitted the equal clause.
    pub first_shape: CnfParityLeafShape,
    /// Shape of the later leaf whose clause was rejected as a duplicate.
    pub duplicate_shape: CnfParityLeafShape,
    /// Exact duplicate clauses in this cell.
    pub duplicate_clauses: u64,
    /// Canonical literals in those duplicate clauses.
    pub duplicate_canonical_literals: u64,
    /// Empty duplicate clauses.
    pub empty_clauses: u64,
    /// Canonical literals in empty duplicate clauses.
    pub empty_literals: u64,
    /// Unit duplicate clauses.
    pub unit_clauses: u64,
    /// Canonical literals in unit duplicate clauses.
    pub unit_literals: u64,
    /// Binary duplicate clauses.
    pub binary_clauses: u64,
    /// Canonical literals in binary duplicate clauses.
    pub binary_literals: u64,
    /// Ternary duplicate clauses.
    pub ternary_clauses: u64,
    /// Canonical literals in ternary duplicate clauses.
    pub ternary_literals: u64,
    /// Duplicate clauses containing four or more literals.
    pub larger_clauses: u64,
    /// Canonical literals in duplicate clauses containing four or more literals.
    pub larger_literals: u64,
}

impl CnfParityOverlapRow {
    fn new(
        relation: CnfParityOverlapRelation,
        first_shape: CnfParityLeafShape,
        duplicate_shape: CnfParityLeafShape,
    ) -> Self {
        Self {
            relation,
            first_shape,
            duplicate_shape,
            duplicate_clauses: 0,
            duplicate_canonical_literals: 0,
            empty_clauses: 0,
            empty_literals: 0,
            unit_clauses: 0,
            unit_literals: 0,
            binary_clauses: 0,
            binary_literals: 0,
            ternary_clauses: 0,
            ternary_literals: 0,
            larger_clauses: 0,
            larger_literals: 0,
        }
    }

    fn record(&mut self, len: usize) {
        let literals = usize_to_u64_saturating(len);
        self.duplicate_clauses = self.duplicate_clauses.saturating_add(1);
        self.duplicate_canonical_literals =
            self.duplicate_canonical_literals.saturating_add(literals);
        let (clauses, bucket_literals) = match len {
            0 => (&mut self.empty_clauses, &mut self.empty_literals),
            1 => (&mut self.unit_clauses, &mut self.unit_literals),
            2 => (&mut self.binary_clauses, &mut self.binary_literals),
            3 => (&mut self.ternary_clauses, &mut self.ternary_literals),
            _ => (&mut self.larger_clauses, &mut self.larger_literals),
        };
        *clauses = clauses.saturating_add(1);
        *bucket_literals = bucket_literals.saturating_add(literals);
    }

    fn length_clauses(&self) -> u64 {
        self.empty_clauses
            .saturating_add(self.unit_clauses)
            .saturating_add(self.binary_clauses)
            .saturating_add(self.ternary_clauses)
            .saturating_add(self.larger_clauses)
    }

    fn length_literals(&self) -> u64 {
        self.empty_literals
            .saturating_add(self.unit_literals)
            .saturating_add(self.binary_literals)
            .saturating_add(self.ternary_literals)
            .saturating_add(self.larger_literals)
    }
}

/// Opt-in exact parity-leaf clause-overlap profile.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CnfParityOverlapProfile {
    /// Whether every parity/parity duplicate carried leaf metadata.
    pub profile_complete: bool,
    /// Exact parity/parity duplicate clauses represented by `rows`.
    pub duplicate_clauses: u64,
    /// Canonical literals represented by those duplicate attempts.
    pub duplicate_canonical_literals: u64,
    /// Deterministically sorted nonzero relation/shape cells.
    pub rows: Vec<CnfParityOverlapRow>,
}

impl CnfParityOverlapProfile {
    /// Checks shape, relation, clause-length, and literal partitions.
    pub fn invariants_hold(&self) -> bool {
        self.profile_complete
            && self.duplicate_clauses
                == self.rows.iter().fold(0u64, |total, row| {
                    total.saturating_add(row.duplicate_clauses)
                })
            && self.duplicate_canonical_literals
                == self.rows.iter().fold(0u64, |total, row| {
                    total.saturating_add(row.duplicate_canonical_literals)
                })
            && self.rows.iter().all(|row| {
                row.first_shape.invariants_hold()
                    && row.duplicate_shape.invariants_hold()
                    && row.duplicate_clauses == row.length_clauses()
                    && row.duplicate_canonical_literals == row.length_literals()
            })
    }
}

/// Opt-in exact duplicate-clause origin matrix.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CnfDuplicateOriginProfile {
    /// Whether origin metadata was collected for every exact duplicate.
    pub profile_complete: bool,
    /// Exact duplicates represented by `rows`.
    pub duplicate_clauses: u64,
    /// Canonical literals represented by duplicate attempts.
    pub duplicate_canonical_literals: u64,
    /// Deterministically sorted nonzero origin cells.
    pub rows: Vec<CnfDuplicateOriginRow>,
    /// Exact parity/parity duplicate partition by enclosing leaf relation/shape.
    pub parity_overlap: CnfParityOverlapProfile,
}

impl CnfDuplicateOriginProfile {
    /// Checks row, owner, clause-length, and literal partitions.
    pub fn invariants_hold(&self) -> bool {
        if !self.profile_complete {
            return false;
        }
        let parity_clauses = self
            .rows
            .iter()
            .filter(|row| {
                row.first_origin.template == CnfClauseOriginTemplate::AndTreeForwardParity
                    && row.duplicate_origin.template
                        == CnfClauseOriginTemplate::AndTreeForwardParity
            })
            .fold(0u64, |total, row| {
                total.saturating_add(row.duplicate_clauses)
            });
        let parity_literals = self
            .rows
            .iter()
            .filter(|row| {
                row.first_origin.template == CnfClauseOriginTemplate::AndTreeForwardParity
                    && row.duplicate_origin.template
                        == CnfClauseOriginTemplate::AndTreeForwardParity
            })
            .fold(0u64, |total, row| {
                total.saturating_add(row.duplicate_canonical_literals)
            });
        self.duplicate_clauses
            == self
                .rows
                .iter()
                .fold(0, |total, row| total.saturating_add(row.duplicate_clauses))
            && self.duplicate_canonical_literals
                == self.rows.iter().fold(0, |total, row| {
                    total.saturating_add(row.duplicate_canonical_literals)
                })
            && self
                .rows
                .iter()
                .all(|row| row.duplicate_clauses == row.length_clauses())
            && self
                .rows
                .iter()
                .all(|row| row.duplicate_canonical_literals == row.length_literals())
            && self.parity_overlap.invariants_hold()
            && self.parity_overlap.duplicate_clauses == parity_clauses
            && self.parity_overlap.duplicate_canonical_literals == parity_literals
    }
}

/// Diagnostics for one AIG-to-CNF encoding.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CnfEncodingStats {
    /// Time spent computing reachability, polarity, and compound-gate plans.
    pub planning: Duration,
    /// Time spent assigning CNF variables to retained AIG nodes.
    pub variable_allocation: Duration,
    /// Time spent emitting clauses for planned non-root gates.
    pub gate_encoding: Duration,
    /// Time spent encoding and asserting roots.
    pub root_encoding: Duration,
    /// AIG nodes reachable from at least one requested root.
    pub reachable_nodes: u64,
    /// Private helper nodes subsumed by a recognized compound gate.
    pub skipped_helper_nodes: u64,
    /// Assertion-only roots encoded without dedicated CNF variables.
    pub direct_root_nodes: u64,
    /// Recognized XOR gates.
    pub xor_gates: u64,
    /// Recognized complemented ITE/mux gates.
    pub not_ite_gates: u64,
    /// Recognized complemented-AND gates.
    pub not_and_gates: u64,
    /// Recognized private AND trees.
    pub and_tree_gates: u64,
    /// Remaining primitive binary AND gates.
    pub binary_and_gates: u64,
    /// Clause-emission attempts before tautology and duplicate filtering.
    pub clause_attempts: u64,
    /// Clause attempts discarded because a constant-true or complementary pair
    /// made the clause tautological.
    pub tautological_clauses_skipped: u64,
    /// Canonical clauses discarded because an identical clause was emitted.
    pub duplicate_clauses_skipped: u64,
    /// Clauses retained in the final formula.
    pub clauses_emitted: u64,
    /// Exact retained-storage accounting for the final formula arena.
    pub storage: CnfStorageProfile,
    /// Opt-in literal-canonicalization and clause-index attribution.
    pub construction_profile: CnfConstructionProfile,
}

impl CnfEncodingStats {
    /// Checks every ADR-0259 construction-profile partition.
    ///
    /// Returns `false` when detailed profiling was not selected.
    pub fn construction_profile_invariants_hold(&self) -> bool {
        let profile = self.construction_profile;
        if !profile.profile_complete {
            return false;
        }
        let non_tautological = self
            .clause_attempts
            .saturating_sub(self.tautological_clauses_skipped);
        let canonical_attempts = profile
            .canonical_empty_clauses
            .saturating_add(profile.canonical_unit_clauses)
            .saturating_add(profile.canonical_binary_clauses)
            .saturating_add(profile.canonical_ternary_clauses)
            .saturating_add(profile.canonical_larger_clauses);
        let index_attempts = profile
            .primary_vacant_probes
            .saturating_add(profile.primary_occupied_probes);
        let occupied_outcomes = profile
            .primary_exact_duplicates
            .saturating_add(profile.collision_exact_duplicates)
            .saturating_add(profile.collision_inserts);
        let duplicate_outcomes = profile
            .primary_exact_duplicates
            .saturating_add(profile.collision_exact_duplicates);
        let emitted_outcomes = profile
            .primary_vacant_probes
            .saturating_add(profile.collision_inserts);
        let tautology_outcomes = profile
            .true_constant_tautologies
            .saturating_add(profile.complementary_literal_tautologies);
        non_tautological == canonical_attempts
            && non_tautological == index_attempts
            && profile.primary_occupied_probes == occupied_outcomes
            && self.duplicate_clauses_skipped == duplicate_outcomes
            && self.clauses_emitted == emitted_outcomes
            && self.tautological_clauses_skipped == tautology_outcomes
    }
}

/// Result of Tseitin encoding AIG roots.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CnfEncoding {
    formula: CnfFormula,
    roots: Vec<CnfRoot>,
    reachable_nodes: Vec<bool>,
    variable_bindings: Vec<CnfVarBinding>,
    stats: CnfEncodingStats,
}

impl CnfEncoding {
    /// Generated CNF formula.
    pub fn formula(&self) -> &CnfFormula {
        &self.formula
    }

    /// Root mappings in input order.
    pub fn roots(&self) -> &[CnfRoot] {
        &self.roots
    }

    /// Variable-to-AIG lift-map entries in CNF variable order.
    pub fn variable_bindings(&self) -> &[CnfVarBinding] {
        &self.variable_bindings
    }

    /// Returns deterministic structure counters and measured encoder subphases.
    pub fn stats(&self) -> CnfEncodingStats {
        self.stats
    }

    /// Builds a full CNF variable assignment from AIG input values.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::Aig`] if AIG evaluation rejects the input count.
    pub fn assignment_from_aig_inputs(
        &self,
        aig: &Aig,
        inputs: &[bool],
    ) -> Result<Vec<bool>, CnfError> {
        self.variable_bindings
            .iter()
            .map(|binding| Ok(aig.eval(binding.aig_literal, inputs)?))
            .collect()
    }

    /// Builds a typed CNF assignment from AIG input values.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::Aig`] if AIG evaluation rejects the input count.
    pub fn cnf_assignment_from_aig_inputs(
        &self,
        aig: &Aig,
        inputs: &[bool],
    ) -> Result<CnfAssignment, CnfError> {
        Ok(CnfAssignment::new(
            self.assignment_from_aig_inputs(aig, inputs)?,
        ))
    }

    /// Replays a satisfying CNF assignment into one Boolean value per AIG node.
    ///
    /// The returned vector is indexed by `AigNodeId::index()`. This method first
    /// checks the CNF formula, then independently checks every encoded AIG AND
    /// node against the lifted node values.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError`] when the assignment has the wrong length, does not
    /// satisfy the encoded CNF, or does not replay through the AIG gates.
    pub fn aig_node_values_from_assignment(
        &self,
        aig: &Aig,
        assignment: &CnfAssignment,
    ) -> Result<Vec<bool>, CnfError> {
        if !assignment.satisfies(&self.formula)? {
            return Err(CnfError::UnsatisfiedAssignment);
        }
        let mut assigned = vec![None; aig.node_count()];
        let mut values = vec![false; aig.node_count()];
        for binding in &self.variable_bindings {
            let value =
                assignment
                    .value(binding.variable)
                    .ok_or(CnfError::AssignmentLengthMismatch {
                        expected: self.formula.variable_count(),
                        found: assignment.len(),
                    })?;
            let index = binding.aig_literal.node().index();
            values[index] = value;
            assigned[index] = Some(value);
        }
        replay_sparse_aig_values(aig, &mut values, &assigned, &self.reachable_nodes)?;
        Ok(values)
    }
}

/// Encodes AIG roots into CNF using simple Tseitin clauses.
///
/// The returned formula asserts every requested root. Assertion-only AIG root
/// nodes may be encoded directly into child clauses instead of receiving a
/// dedicated root variable and unit clause.
///
/// # Errors
///
/// Returns [`CnfError`] if the AIG graph is internally inconsistent.
pub fn tseitin_encode(aig: &Aig, roots: &[AigLit]) -> Result<CnfEncoding, CnfError> {
    let encoder = TseitinEncoder::new(aig);
    encoder.encode(roots)
}

/// Encodes AIG roots into CNF while collecting detailed construction work.
///
/// This selects a separately monomorphized encoder. The generated formula,
/// roots, and lift map have the same semantics and deterministic order as
/// [`tseitin_encode`].
///
/// # Errors
///
/// Returns [`CnfError`] if the AIG graph is internally inconsistent.
pub fn tseitin_encode_profiled(aig: &Aig, roots: &[AigLit]) -> Result<CnfEncoding, CnfError> {
    let encoder = TseitinEncoder::<EnabledConstructionProfile>::new_profiled(aig);
    encoder.encode(roots)
}

/// Encodes AIG roots while also returning exact duplicate-clause origins.
///
/// This is the ADR-0260 diagnostic route. Origin metadata is retained only in
/// the enabled profiler; [`tseitin_encode`] still instantiates a zero-sized
/// disabled store.
///
/// # Errors
///
/// Returns [`CnfError`] if the AIG graph is internally inconsistent.
///
/// # Panics
///
/// Panics only if the statically selected enabled profiler fails to return its
/// own origin snapshot, which would be an internal implementation invariant
/// violation.
pub fn tseitin_encode_profiled_with_origins(
    aig: &Aig,
    roots: &[AigLit],
) -> Result<(CnfEncoding, CnfDuplicateOriginProfile), CnfError> {
    let encoder = TseitinEncoder::<EnabledConstructionProfile>::new_profiled(aig);
    let (encoding, origins) = encoder.encode_with_origins(roots)?;
    Ok((
        encoding,
        origins.expect("enabled construction profiler returns origin metadata"),
    ))
}

/// Parses a DIMACS CNF string.
///
/// # Errors
///
/// Returns [`CnfError`] if the input is malformed or references variables
/// outside the declared problem line.
pub fn parse_dimacs(input: &str) -> Result<CnfFormula, CnfError> {
    let mut variable_count = None;
    let mut expected_clauses = None;
    let mut formula = None;
    let mut current_clause = Vec::new();

    for line in input.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        if trimmed.starts_with('p') {
            if variable_count.is_some() {
                return Err(CnfError::DuplicateProblemLine);
            }
            let parts = trimmed.split_whitespace().collect::<Vec<_>>();
            if parts.len() != 4 || parts[0] != "p" || parts[1] != "cnf" {
                return Err(CnfError::InvalidProblemLine(trimmed.to_owned()));
            }
            let count = parse_usize(parts[2])?;
            variable_count = Some(count);
            formula = Some(CnfFormula::new(count));
            expected_clauses = Some(parse_usize(parts[3])?);
            continue;
        }

        let count = variable_count.ok_or(CnfError::MissingProblemLine)?;
        for token in trimmed.split_whitespace() {
            let value = parse_dimacs_lit_token(token)?;
            if value == 0 {
                formula
                    .as_mut()
                    .ok_or(CnfError::MissingProblemLine)?
                    .add_clause(CnfClause::new(std::mem::take(&mut current_clause)))?;
            } else {
                current_clause.push(lit_from_dimacs(value, count)?);
            }
        }
    }

    let variable_count = variable_count.ok_or(CnfError::MissingProblemLine)?;
    let expected_clauses = expected_clauses.ok_or(CnfError::MissingProblemLine)?;
    let formula = formula.ok_or(CnfError::MissingProblemLine)?;
    if !current_clause.is_empty() {
        return Err(CnfError::MissingClauseTerminator);
    }
    if formula.clause_count() != expected_clauses {
        return Err(CnfError::ClauseCountMismatch {
            expected: expected_clauses,
            found: formula.clause_count(),
        });
    }
    debug_assert_eq!(formula.variable_count(), variable_count);
    Ok(formula)
}

/// CNF layer errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CnfError {
    /// Error from the AIG layer.
    Aig(axeyum_aig::AigError),
    /// CNF assignment length does not match variable count.
    AssignmentLengthMismatch {
        /// Expected assignment length.
        expected: usize,
        /// Actual assignment length.
        found: usize,
    },
    /// A zero-based variable index does not fit in the internal representation.
    VariableIndexTooLarge {
        /// Requested zero-based index.
        index: usize,
    },
    /// The formula's total literal count does not fit its stable offset type.
    LiteralIndexTooLarge {
        /// Requested total literal count.
        literals: usize,
    },
    /// A literal referenced a variable outside the formula.
    InvalidVariable {
        /// One-based variable number.
        variable: u32,
        /// Declared variable count.
        variable_count: usize,
    },
    /// A candidate SAT assignment did not satisfy the CNF formula.
    UnsatisfiedAssignment,
    /// A replayed assignment came from a different AIG shape.
    AigNodeCountMismatch {
        /// Expected AIG node count.
        expected: usize,
        /// Actual AIG node count.
        found: usize,
    },
    /// A CNF assignment omitted a variable required to seed AIG replay.
    MissingAigNodeAssignment {
        /// AIG node index.
        node: usize,
    },
    /// A replayed assignment did not match the encoded AIG node semantics.
    AigReplayMismatch {
        /// AIG node index.
        node: usize,
        /// Expected value from the node definition.
        expected: bool,
        /// Value carried by the replayed assignment.
        found: bool,
    },
    /// DIMACS input is missing a `p cnf` line.
    MissingProblemLine,
    /// DIMACS input has more than one problem line.
    DuplicateProblemLine,
    /// DIMACS problem line is malformed.
    InvalidProblemLine(String),
    /// DIMACS integer token is malformed.
    InvalidLiteral(String),
    /// Final DIMACS clause did not end with `0`.
    MissingClauseTerminator,
    /// Parsed clause count does not match the problem line.
    ClauseCountMismatch {
        /// Declared clause count.
        expected: usize,
        /// Parsed clause count.
        found: usize,
    },
}

impl From<axeyum_aig::AigError> for CnfError {
    fn from(error: axeyum_aig::AigError) -> Self {
        Self::Aig(error)
    }
}

impl core::fmt::Display for CnfError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            CnfError::Aig(error) => write!(f, "{error}"),
            CnfError::AssignmentLengthMismatch { expected, found } => {
                write!(
                    f,
                    "expected {expected} CNF assignment values, found {found}"
                )
            }
            CnfError::VariableIndexTooLarge { index } => {
                write!(f, "CNF variable index {index} does not fit in u32")
            }
            CnfError::LiteralIndexTooLarge { literals } => {
                write!(f, "CNF literal count {literals} does not fit in u32")
            }
            CnfError::InvalidVariable {
                variable,
                variable_count,
            } => write!(
                f,
                "CNF variable {variable} exceeds declared variable count {variable_count}"
            ),
            CnfError::UnsatisfiedAssignment => {
                write!(f, "CNF assignment does not satisfy the formula")
            }
            CnfError::AigNodeCountMismatch { expected, found } => write!(
                f,
                "replayed assignment has {found} AIG nodes, expected {expected}"
            ),
            CnfError::MissingAigNodeAssignment { node } => {
                write!(f, "missing CNF assignment for AIG node #{node}")
            }
            CnfError::AigReplayMismatch {
                node,
                expected,
                found,
            } => write!(
                f,
                "AIG node #{node} replayed as {found}, expected {expected}"
            ),
            CnfError::MissingProblemLine => write!(f, "missing DIMACS problem line"),
            CnfError::DuplicateProblemLine => write!(f, "duplicate DIMACS problem line"),
            CnfError::InvalidProblemLine(line) => write!(f, "invalid DIMACS problem line: {line}"),
            CnfError::InvalidLiteral(token) => write!(f, "invalid DIMACS literal: {token}"),
            CnfError::MissingClauseTerminator => write!(f, "DIMACS clause missing terminator 0"),
            CnfError::ClauseCountMismatch { expected, found } => {
                write!(f, "expected {expected} DIMACS clauses, found {found}")
            }
        }
    }
}

impl core::error::Error for CnfError {}

// The disabled implementation is a zero-sized production type. Forced
// inlining makes its no-op calls disappear at the monomorphized hot sites.
#[allow(clippy::inline_always)]
trait ConstructionProfiler: Default {
    #[inline(always)]
    fn snapshot(&self) -> CnfConstructionProfile {
        CnfConstructionProfile::default()
    }

    #[inline(always)]
    fn record_declared_literals(&mut self, _count: usize) {}

    #[inline(always)]
    fn record_visited_literal(&mut self) {}

    #[inline(always)]
    fn record_false_constant(&mut self) {}

    #[inline(always)]
    fn record_repeated_literal(&mut self) {}

    #[inline(always)]
    fn record_true_tautology(&mut self) {}

    #[inline(always)]
    fn record_complementary_tautology(&mut self) {}

    #[inline(always)]
    fn record_canonical_clause(&mut self, _len: usize) {}

    #[inline(always)]
    fn record_primary_vacant(&mut self) {}

    #[inline(always)]
    fn record_primary_occupied(&mut self) {}

    #[inline(always)]
    fn record_primary_duplicate(&mut self) {}

    #[inline(always)]
    fn record_collision_comparison(&mut self) {}

    #[inline(always)]
    fn record_collision_duplicate(&mut self) {}

    #[inline(always)]
    fn record_collision_insert(&mut self) {}

    #[inline(always)]
    fn record_emitted_origin(&mut self, _clause_index: usize, _origin: CnfClauseOrigin) {}

    #[inline(always)]
    fn record_duplicate_origin(
        &mut self,
        _first_clause_index: usize,
        _origin: CnfClauseOrigin,
        _canonical_len: usize,
    ) {
    }

    #[inline(always)]
    fn duplicate_origin_snapshot(&self) -> Option<CnfDuplicateOriginProfile> {
        None
    }
}

#[derive(Default)]
struct DisabledDuplicateOriginStore;

#[derive(Default)]
struct DisabledConstructionProfile(DisabledDuplicateOriginStore);

impl ConstructionProfiler for DisabledConstructionProfile {}

#[derive(Debug, Clone, Copy)]
struct CnfClauseOrigin {
    site: CnfClauseOriginSite,
    owner: AigNodeId,
    parity_leaf: Option<CnfParityLeafOrigin>,
}

#[derive(Debug, Clone, Copy)]
struct CnfParityLeafOrigin {
    leaf_index: usize,
    shape: CnfParityLeafShape,
}

#[derive(Debug, Clone, Copy)]
struct EmissionContext {
    phase: CnfClauseOriginPhase,
    owner: AigNodeId,
}

impl EmissionContext {
    const fn origin(self, template: CnfClauseOriginTemplate) -> CnfClauseOrigin {
        CnfClauseOrigin {
            site: CnfClauseOriginSite::new(self.phase, template),
            owner: self.owner,
            parity_leaf: None,
        }
    }

    const fn parity_origin(self, leaf_index: usize, shape: CnfParityLeafShape) -> CnfClauseOrigin {
        CnfClauseOrigin {
            site: CnfClauseOriginSite::new(
                self.phase,
                CnfClauseOriginTemplate::AndTreeForwardParity,
            ),
            owner: self.owner,
            parity_leaf: Some(CnfParityLeafOrigin { leaf_index, shape }),
        }
    }
}

#[derive(Default)]
struct EnabledDuplicateOriginStore {
    emitted_origins: Vec<CnfClauseOrigin>,
    rows: BTreeMap<(CnfClauseOriginSite, CnfClauseOriginSite, bool), CnfDuplicateOriginRow>,
    parity_rows: BTreeMap<
        (
            CnfParityOverlapRelation,
            CnfParityLeafShape,
            CnfParityLeafShape,
        ),
        CnfParityOverlapRow,
    >,
    duplicate_clauses: u64,
    duplicate_canonical_literals: u64,
    parity_duplicate_clauses: u64,
    parity_duplicate_canonical_literals: u64,
}

impl EnabledDuplicateOriginStore {
    fn record_emitted(&mut self, clause_index: usize, origin: CnfClauseOrigin) {
        debug_assert_eq!(
            clause_index,
            self.emitted_origins.len(),
            "origin metadata follows formula clause order"
        );
        self.emitted_origins.push(origin);
    }

    fn record_duplicate(
        &mut self,
        first_clause_index: usize,
        origin: CnfClauseOrigin,
        canonical_len: usize,
    ) {
        let first = self.emitted_origins[first_clause_index];
        let key = (first.site, origin.site, first.owner == origin.owner);
        self.rows
            .entry(key)
            .or_insert_with(|| CnfDuplicateOriginRow::new(key.0, key.1, key.2))
            .record(canonical_len);
        self.duplicate_clauses = self.duplicate_clauses.saturating_add(1);
        self.duplicate_canonical_literals = self
            .duplicate_canonical_literals
            .saturating_add(usize_to_u64_saturating(canonical_len));
        if first.site.template == CnfClauseOriginTemplate::AndTreeForwardParity
            && origin.site.template == CnfClauseOriginTemplate::AndTreeForwardParity
        {
            let first_leaf = first
                .parity_leaf
                .expect("profiled parity origin carries first-leaf metadata");
            let duplicate_leaf = origin
                .parity_leaf
                .expect("profiled parity origin carries duplicate-leaf metadata");
            let relation = if first.owner != origin.owner {
                CnfParityOverlapRelation::CrossOwner
            } else if first_leaf.leaf_index == duplicate_leaf.leaf_index {
                CnfParityOverlapRelation::WithinLeaf
            } else {
                CnfParityOverlapRelation::CrossLeafSameOwner
            };
            let key = (relation, first_leaf.shape, duplicate_leaf.shape);
            self.parity_rows
                .entry(key)
                .or_insert_with(|| CnfParityOverlapRow::new(key.0, key.1, key.2))
                .record(canonical_len);
            self.parity_duplicate_clauses = self.parity_duplicate_clauses.saturating_add(1);
            self.parity_duplicate_canonical_literals = self
                .parity_duplicate_canonical_literals
                .saturating_add(usize_to_u64_saturating(canonical_len));
        }
    }

    fn snapshot(&self) -> CnfDuplicateOriginProfile {
        CnfDuplicateOriginProfile {
            profile_complete: true,
            duplicate_clauses: self.duplicate_clauses,
            duplicate_canonical_literals: self.duplicate_canonical_literals,
            rows: self.rows.values().cloned().collect(),
            parity_overlap: CnfParityOverlapProfile {
                profile_complete: true,
                duplicate_clauses: self.parity_duplicate_clauses,
                duplicate_canonical_literals: self.parity_duplicate_canonical_literals,
                rows: self.parity_rows.values().cloned().collect(),
            },
        }
    }
}

struct EnabledConstructionProfile {
    counters: CnfConstructionProfile,
    origins: EnabledDuplicateOriginStore,
}

impl Default for EnabledConstructionProfile {
    fn default() -> Self {
        Self {
            counters: CnfConstructionProfile {
                profile_complete: true,
                ..CnfConstructionProfile::default()
            },
            origins: EnabledDuplicateOriginStore::default(),
        }
    }
}

#[allow(clippy::inline_always)]
impl ConstructionProfiler for EnabledConstructionProfile {
    #[inline(always)]
    fn snapshot(&self) -> CnfConstructionProfile {
        self.counters
    }

    #[inline(always)]
    fn record_declared_literals(&mut self, count: usize) {
        self.counters.declared_clause_literals = self
            .counters
            .declared_clause_literals
            .saturating_add(usize_to_u64_saturating(count));
    }

    #[inline(always)]
    fn record_visited_literal(&mut self) {
        self.counters.visited_clause_literals =
            self.counters.visited_clause_literals.saturating_add(1);
    }

    #[inline(always)]
    fn record_false_constant(&mut self) {
        self.counters.false_constants_dropped =
            self.counters.false_constants_dropped.saturating_add(1);
    }

    #[inline(always)]
    fn record_repeated_literal(&mut self) {
        self.counters.repeated_literals_dropped =
            self.counters.repeated_literals_dropped.saturating_add(1);
    }

    #[inline(always)]
    fn record_true_tautology(&mut self) {
        self.counters.true_constant_tautologies =
            self.counters.true_constant_tautologies.saturating_add(1);
    }

    #[inline(always)]
    fn record_complementary_tautology(&mut self) {
        self.counters.complementary_literal_tautologies = self
            .counters
            .complementary_literal_tautologies
            .saturating_add(1);
    }

    #[inline(always)]
    fn record_canonical_clause(&mut self, len: usize) {
        self.counters.canonical_literals = self
            .counters
            .canonical_literals
            .saturating_add(usize_to_u64_saturating(len));
        let bucket = match len {
            0 => &mut self.counters.canonical_empty_clauses,
            1 => &mut self.counters.canonical_unit_clauses,
            2 => &mut self.counters.canonical_binary_clauses,
            3 => &mut self.counters.canonical_ternary_clauses,
            _ => &mut self.counters.canonical_larger_clauses,
        };
        *bucket = bucket.saturating_add(1);
    }

    #[inline(always)]
    fn record_primary_vacant(&mut self) {
        self.counters.primary_vacant_probes = self.counters.primary_vacant_probes.saturating_add(1);
    }

    #[inline(always)]
    fn record_primary_occupied(&mut self) {
        self.counters.primary_occupied_probes =
            self.counters.primary_occupied_probes.saturating_add(1);
    }

    #[inline(always)]
    fn record_primary_duplicate(&mut self) {
        self.counters.primary_exact_duplicates =
            self.counters.primary_exact_duplicates.saturating_add(1);
    }

    #[inline(always)]
    fn record_collision_comparison(&mut self) {
        self.counters.collision_bucket_comparisons =
            self.counters.collision_bucket_comparisons.saturating_add(1);
    }

    #[inline(always)]
    fn record_collision_duplicate(&mut self) {
        self.counters.collision_exact_duplicates =
            self.counters.collision_exact_duplicates.saturating_add(1);
    }

    #[inline(always)]
    fn record_collision_insert(&mut self) {
        self.counters.collision_inserts = self.counters.collision_inserts.saturating_add(1);
    }

    #[inline(always)]
    fn record_emitted_origin(&mut self, clause_index: usize, origin: CnfClauseOrigin) {
        self.origins.record_emitted(clause_index, origin);
    }

    #[inline(always)]
    fn record_duplicate_origin(
        &mut self,
        first_clause_index: usize,
        origin: CnfClauseOrigin,
        canonical_len: usize,
    ) {
        self.origins
            .record_duplicate(first_clause_index, origin, canonical_len);
    }

    #[inline(always)]
    fn duplicate_origin_snapshot(&self) -> Option<CnfDuplicateOriginProfile> {
        Some(self.origins.snapshot())
    }
}

struct TseitinEncoder<'a, P = DisabledConstructionProfile> {
    aig: &'a Aig,
    formula: CnfFormula,
    node_vars: Vec<Option<CnfVar>>,
    reachable_nodes: Vec<bool>,
    skip_nodes: Vec<bool>,
    direct_root_nodes: Vec<bool>,
    root_polarities: Vec<Option<bool>>,
    xor_gates: Vec<Option<XorGate>>,
    not_ite_gates: Vec<Option<NotIteGate>>,
    not_and_gates: Vec<Option<NotAndGate>>,
    and_tree_gates: Vec<Option<AndTreeGate>>,
    clause_scratch: Vec<CnfLit>,
    clause_index: ClauseIndex,
    variable_bindings: Vec<CnfVarBinding>,
    clause_attempts: u64,
    tautological_clauses_skipped: u64,
    duplicate_clauses_skipped: u64,
    construction_profile: P,
}

impl<'a> TseitinEncoder<'a, DisabledConstructionProfile> {
    fn new(aig: &'a Aig) -> Self {
        Self::new_with_profile(aig)
    }
}

impl<'a> TseitinEncoder<'a, EnabledConstructionProfile> {
    fn new_profiled(aig: &'a Aig) -> Self {
        Self::new_with_profile(aig)
    }
}

impl<'a, P: ConstructionProfiler> TseitinEncoder<'a, P> {
    fn new_with_profile(aig: &'a Aig) -> Self {
        Self {
            aig,
            formula: CnfFormula::new(0),
            node_vars: vec![None; aig.node_count()],
            reachable_nodes: vec![false; aig.node_count()],
            skip_nodes: vec![false; aig.node_count()],
            direct_root_nodes: vec![false; aig.node_count()],
            root_polarities: vec![None; aig.node_count()],
            xor_gates: vec![None; aig.node_count()],
            not_ite_gates: vec![None; aig.node_count()],
            not_and_gates: vec![None; aig.node_count()],
            and_tree_gates: vec![None; aig.node_count()],
            clause_scratch: Vec::with_capacity(4),
            clause_index: ClauseIndex::default(),
            variable_bindings: Vec::new(),
            clause_attempts: 0,
            tautological_clauses_skipped: 0,
            duplicate_clauses_skipped: 0,
            construction_profile: P::default(),
        }
    }

    #[cfg(test)]
    fn construction_profile(&self) -> CnfConstructionProfile {
        self.construction_profile.snapshot()
    }

    fn encode(self, roots: &[AigLit]) -> Result<CnfEncoding, CnfError> {
        self.encode_with_origins(roots)
            .map(|(encoding, _)| encoding)
    }

    fn encode_with_origins(
        mut self,
        roots: &[AigLit],
    ) -> Result<(CnfEncoding, Option<CnfDuplicateOriginProfile>), CnfError> {
        let planning_start = Instant::now();
        self.plan_sparse_encoding(roots);
        let planning = planning_start.elapsed();
        let allocation_start = Instant::now();
        self.allocate_variables();
        let variable_allocation = allocation_start.elapsed();
        let gate_start = Instant::now();
        self.encode_gates()?;
        let gate_encoding = gate_start.elapsed();
        let root_start = Instant::now();
        let roots = roots
            .iter()
            .copied()
            .map(|aig_literal| {
                let cnf_lit = self.assert_root(aig_literal)?;
                Ok(CnfRoot {
                    aig_literal,
                    cnf_lit,
                })
            })
            .collect::<Result<Vec<_>, CnfError>>()?;
        let root_encoding = root_start.elapsed();
        let stats =
            self.encoding_stats(planning, variable_allocation, gate_encoding, root_encoding);
        let origins = self.construction_profile.duplicate_origin_snapshot();
        Ok((
            CnfEncoding {
                formula: self.formula,
                roots,
                reachable_nodes: self.reachable_nodes,
                variable_bindings: self.variable_bindings,
                stats,
            },
            origins,
        ))
    }

    fn encoding_stats(
        &self,
        planning: Duration,
        variable_allocation: Duration,
        gate_encoding: Duration,
        root_encoding: Duration,
    ) -> CnfEncodingStats {
        let binary_and_gates = self
            .aig
            .nodes()
            .filter(|(node_id, node)| {
                let index = node_id.index();
                self.reachable_nodes[index]
                    && !self.skip_nodes[index]
                    && !self.direct_root_nodes[index]
                    && matches!(node, AigNode::And(_, _))
                    && self.xor_gates[index].is_none()
                    && self.not_ite_gates[index].is_none()
                    && self.not_and_gates[index].is_none()
                    && self.and_tree_gates[index].is_none()
            })
            .count();
        CnfEncodingStats {
            planning,
            variable_allocation,
            gate_encoding,
            root_encoding,
            reachable_nodes: count_true(&self.reachable_nodes),
            skipped_helper_nodes: count_true(&self.skip_nodes),
            direct_root_nodes: count_true(&self.direct_root_nodes),
            xor_gates: count_some(&self.xor_gates),
            not_ite_gates: count_some(&self.not_ite_gates),
            not_and_gates: count_some(&self.not_and_gates),
            and_tree_gates: count_some(&self.and_tree_gates),
            binary_and_gates: usize_to_u64_saturating(binary_and_gates),
            clause_attempts: self.clause_attempts,
            tautological_clauses_skipped: self.tautological_clauses_skipped,
            duplicate_clauses_skipped: self.duplicate_clauses_skipped,
            clauses_emitted: usize_to_u64_saturating(self.formula.clauses().len()),
            storage: self.formula.storage_profile(),
            construction_profile: self.construction_profile.snapshot(),
        }
    }

    fn plan_sparse_encoding(&mut self, roots: &[AigLit]) {
        self.reachable_nodes = reachable_node_mask(self.aig, roots);
        let use_counts = node_use_counts(self.aig, roots, &self.reachable_nodes);
        self.plan_root_polarities(roots, &use_counts);
        self.plan_xor_and_not_ite_gates(&use_counts);
        self.plan_not_and_gates(&use_counts);
        self.plan_and_tree_gates(&use_counts);
        self.plan_direct_root_nodes(&use_counts);
    }

    fn plan_root_polarities(&mut self, roots: &[AigLit], use_counts: &[u32]) {
        let mut root_counts = vec![0u32; self.aig.node_count()];
        let mut root_polarities = vec![None; self.aig.node_count()];
        let mut mixed_root_polarities = vec![false; self.aig.node_count()];
        for root in roots {
            let index = root.node().index();
            if index == 0 {
                continue;
            }
            root_counts[index] = root_counts[index].saturating_add(1);
            let polarity = !root.is_inverted();
            root_polarities[index] = match root_polarities[index] {
                Some(existing) if existing != polarity => {
                    mixed_root_polarities[index] = true;
                    None
                }
                existing @ Some(_) => existing,
                None if mixed_root_polarities[index] => None,
                None => Some(polarity),
            };
        }
        for (index, count) in root_counts.iter().copied().enumerate() {
            if count > 0 && use_counts[index] == count && !mixed_root_polarities[index] {
                self.root_polarities[index] = root_polarities[index];
            }
        }
    }

    fn plan_xor_and_not_ite_gates(&mut self, use_counts: &[u32]) {
        for (node_id, node) in self.aig.nodes() {
            if !self.reachable_nodes[node_id.index()] {
                continue;
            }
            if let Some(xor_gate) = detect_xor_gate(self.aig, node)
                && xor_gate
                    .helper_nodes
                    .iter()
                    .all(|helper| use_counts[helper.index()] == 1)
            {
                self.xor_gates[node_id.index()] = Some(xor_gate);
                for helper in xor_gate.helper_nodes {
                    self.skip_nodes[helper.index()] = true;
                }
                continue;
            }
            if let Some(not_ite_gate) = detect_not_ite_gate(self.aig, node)
                && not_ite_gate
                    .helper_nodes
                    .iter()
                    .all(|helper| use_counts[helper.index()] == 1)
            {
                self.not_ite_gates[node_id.index()] = Some(not_ite_gate);
                for helper in not_ite_gate.helper_nodes {
                    self.skip_nodes[helper.index()] = true;
                }
            }
        }
    }

    fn plan_not_and_gates(&mut self, use_counts: &[u32]) {
        for (node_id, node) in self.aig.nodes() {
            if !self.reachable_nodes[node_id.index()]
                || self.skip_nodes[node_id.index()]
                || self.xor_gates[node_id.index()].is_some()
                || self.not_ite_gates[node_id.index()].is_some()
            {
                continue;
            }
            let Some(not_and_gate) = detect_not_and_gate(
                self.aig,
                node,
                use_counts,
                &self.skip_nodes,
                &self.xor_gates,
                &self.not_ite_gates,
            ) else {
                continue;
            };
            for helper in &not_and_gate.helper_nodes {
                self.skip_nodes[helper.index()] = true;
            }
            self.not_and_gates[node_id.index()] = Some(not_and_gate);
        }
    }

    fn plan_and_tree_gates(&mut self, use_counts: &[u32]) {
        let nodes = self.aig.nodes().collect::<Vec<_>>();
        for (node_id, node) in nodes.into_iter().rev() {
            if !self.reachable_nodes[node_id.index()]
                || self.skip_nodes[node_id.index()]
                || self.xor_gates[node_id.index()].is_some()
                || self.not_ite_gates[node_id.index()].is_some()
                || self.not_and_gates[node_id.index()].is_some()
            {
                continue;
            }
            let context = SparsePlanContext {
                aig: self.aig,
                use_counts,
                skip_nodes: &self.skip_nodes,
                xor_gates: &self.xor_gates,
                not_ite_gates: &self.not_ite_gates,
                not_and_gates: &self.not_and_gates,
            };
            let positive_root_only = self.root_polarities[node_id.index()] == Some(true);
            let Some(and_tree_gate) = collect_private_and_tree(&context, node, positive_root_only)
            else {
                continue;
            };
            for helper in &and_tree_gate.helper_nodes {
                self.skip_nodes[helper.index()] = true;
            }
            self.and_tree_gates[node_id.index()] = Some(and_tree_gate);
        }
    }

    fn plan_direct_root_nodes(&mut self, use_counts: &[u32]) {
        for (node_id, node) in self.aig.nodes() {
            if !self.reachable_nodes[node_id.index()]
                || self.skip_nodes[node_id.index()]
                || self.root_polarities[node_id.index()].is_none()
                || !matches!(node, AigNode::And(_, _))
            {
                continue;
            }
            if self.root_polarities[node_id.index()] == Some(false)
                && let AigNode::And(lhs, rhs) = node
                && let Some(plan) = distributable_negative_and_plan(
                    &SparsePlanContext {
                        aig: self.aig,
                        use_counts,
                        skip_nodes: &self.skip_nodes,
                        xor_gates: &self.xor_gates,
                        not_ite_gates: &self.not_ite_gates,
                        not_and_gates: &self.not_and_gates,
                    },
                    lhs,
                    rhs,
                )
            {
                for helper in plan.helper_nodes {
                    self.skip_nodes[helper.index()] = true;
                }
            }
            self.direct_root_nodes[node_id.index()] = true;
        }
    }

    fn allocate_variables(&mut self) {
        for (node_id, node) in self.aig.nodes() {
            if !self.reachable_nodes[node_id.index()]
                || matches!(node, AigNode::ConstFalse)
                || self.skip_nodes[node_id.index()]
                || self.direct_root_nodes[node_id.index()]
            {
                continue;
            }
            let variable = CnfVar(
                u32::try_from(self.variable_bindings.len()).expect("CNF variable count fits u32"),
            );
            self.node_vars[node_id.index()] = Some(variable);
            self.variable_bindings.push(CnfVarBinding {
                variable,
                aig_literal: AigLit::positive(node_id),
            });
        }
        self.formula = CnfFormula::new(self.variable_bindings.len());
    }

    fn encode_gates(&mut self) -> Result<(), CnfError> {
        for (node_id, node) in self.aig.nodes() {
            if !self.reachable_nodes[node_id.index()]
                || self.skip_nodes[node_id.index()]
                || self.direct_root_nodes[node_id.index()]
            {
                continue;
            }
            let AigNode::And(lhs, rhs) = node else {
                continue;
            };
            let out = EncodedLit::Lit(CnfLit::positive(
                self.node_vars[node_id.index()].expect("AND node has CNF variable"),
            ));
            let context = EmissionContext {
                phase: CnfClauseOriginPhase::Gate,
                owner: node_id,
            };
            let (encode_forward, encode_reverse) = self.clause_directions(node_id);
            if let Some(xor_gate) = self.xor_gates[node_id.index()] {
                self.encode_xor_gate(context, out, xor_gate, encode_forward, encode_reverse)?;
                continue;
            }
            if let Some(not_ite_gate) = self.not_ite_gates[node_id.index()] {
                self.encode_not_ite_gate(
                    context,
                    out,
                    not_ite_gate,
                    encode_forward,
                    encode_reverse,
                )?;
                continue;
            }
            if let Some(not_and_gate) = self.not_and_gates[node_id.index()].clone() {
                self.encode_not_and_gate(
                    context,
                    out,
                    &not_and_gate,
                    encode_forward,
                    encode_reverse,
                )?;
                continue;
            }
            if let Some(and_tree_gate) = self.and_tree_gates[node_id.index()].clone() {
                self.encode_and_tree_gate(
                    context,
                    out,
                    &and_tree_gate,
                    encode_forward,
                    encode_reverse,
                )?;
                continue;
            }
            self.encode_binary_and_gate(context, out, lhs, rhs, encode_forward, encode_reverse)?;
        }
        Ok(())
    }

    fn encode_xor_gate(
        &mut self,
        context: EmissionContext,
        out: EncodedLit,
        gate: XorGate,
        encode_forward: bool,
        encode_reverse: bool,
    ) -> Result<(), CnfError> {
        let lhs = self.encode_lit(gate.lhs);
        let rhs = self.encode_lit(gate.rhs);
        if encode_forward {
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::XorForwardPositiveInputs),
                &[out.negated(), lhs, rhs],
            )?;
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::XorForwardNegativeInputs),
                &[out.negated(), lhs.negated(), rhs.negated()],
            )?;
        }
        if encode_reverse {
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::XorReverseLeftNegative),
                &[out, lhs.negated(), rhs],
            )?;
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::XorReverseRightNegative),
                &[out, lhs, rhs.negated()],
            )?;
        }
        Ok(())
    }

    fn encode_not_ite_gate(
        &mut self,
        context: EmissionContext,
        out: EncodedLit,
        gate: NotIteGate,
        encode_forward: bool,
        encode_reverse: bool,
    ) -> Result<(), CnfError> {
        let condition = self.encode_lit(gate.condition);
        let then_lit = self.encode_lit(gate.then_lit);
        let else_lit = self.encode_lit(gate.else_lit);
        if encode_forward {
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::NotIteForwardThen),
                &[out.negated(), condition.negated(), then_lit.negated()],
            )?;
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::NotIteForwardElse),
                &[out.negated(), condition, else_lit.negated()],
            )?;
        }
        if encode_reverse {
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::NotIteReverseThen),
                &[out, condition.negated(), then_lit],
            )?;
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::NotIteReverseElse),
                &[out, condition, else_lit],
            )?;
        }
        Ok(())
    }

    fn encode_not_and_gate(
        &mut self,
        context: EmissionContext,
        out: EncodedLit,
        gate: &NotAndGate,
        encode_forward: bool,
        encode_reverse: bool,
    ) -> Result<(), CnfError> {
        if encode_forward {
            for factor in &gate.factors {
                match factor {
                    AndFactor::Lit(lit) => {
                        self.add_encoded_clause(
                            context.origin(CnfClauseOriginTemplate::NotAndForwardLiteral),
                            &[out.negated(), self.encode_lit(*lit)],
                        )?;
                    }
                    AndFactor::NotAnd(lhs, rhs) => {
                        self.add_encoded_clause(
                            context.origin(CnfClauseOriginTemplate::NotAndForwardNested),
                            &[
                                out.negated(),
                                self.encode_lit(*lhs).negated(),
                                self.encode_lit(*rhs).negated(),
                            ],
                        )?;
                    }
                }
            }
        }

        if encode_reverse {
            self.encode_not_and_reverse(context, out, gate.factors)?;
        }
        Ok(())
    }

    fn encode_not_and_reverse(
        &mut self,
        context: EmissionContext,
        out: EncodedLit,
        factors: [AndFactor; 2],
    ) -> Result<(), CnfError> {
        match factors {
            [AndFactor::Lit(lhs), AndFactor::Lit(rhs)] => self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::NotAndReverseLiteralPair),
                &[
                    out,
                    self.encode_lit(lhs).negated(),
                    self.encode_lit(rhs).negated(),
                ],
            ),
            [AndFactor::Lit(lit), AndFactor::NotAnd(lhs, rhs)] => {
                let lit = self.encode_lit(lit).negated();
                self.add_encoded_clause(
                    context.origin(CnfClauseOriginTemplate::NotAndReverseLiteralNestedLeft),
                    &[out, lit, self.encode_lit(lhs)],
                )?;
                self.add_encoded_clause(
                    context.origin(CnfClauseOriginTemplate::NotAndReverseLiteralNestedRight),
                    &[out, lit, self.encode_lit(rhs)],
                )
            }
            [AndFactor::NotAnd(lhs, rhs), AndFactor::Lit(lit)] => {
                let lit = self.encode_lit(lit).negated();
                self.add_encoded_clause(
                    context.origin(CnfClauseOriginTemplate::NotAndReverseNestedLiteralLeft),
                    &[out, self.encode_lit(lhs), lit],
                )?;
                self.add_encoded_clause(
                    context.origin(CnfClauseOriginTemplate::NotAndReverseNestedLiteralRight),
                    &[out, self.encode_lit(rhs), lit],
                )
            }
            [
                AndFactor::NotAnd(lhs_a, lhs_b),
                AndFactor::NotAnd(rhs_a, rhs_b),
            ] => {
                let lhs_a = self.encode_lit(lhs_a);
                let lhs_b = self.encode_lit(lhs_b);
                let rhs_a = self.encode_lit(rhs_a);
                let rhs_b = self.encode_lit(rhs_b);
                self.add_encoded_clause(
                    context.origin(CnfClauseOriginTemplate::NotAndReverseNestedNestedAa),
                    &[out, lhs_a, rhs_a],
                )?;
                self.add_encoded_clause(
                    context.origin(CnfClauseOriginTemplate::NotAndReverseNestedNestedAb),
                    &[out, lhs_a, rhs_b],
                )?;
                self.add_encoded_clause(
                    context.origin(CnfClauseOriginTemplate::NotAndReverseNestedNestedBa),
                    &[out, lhs_b, rhs_a],
                )?;
                self.add_encoded_clause(
                    context.origin(CnfClauseOriginTemplate::NotAndReverseNestedNestedBb),
                    &[out, lhs_b, rhs_b],
                )
            }
        }
    }

    fn encode_and_tree_gate(
        &mut self,
        context: EmissionContext,
        out: EncodedLit,
        gate: &AndTreeGate,
        encode_forward: bool,
        encode_reverse: bool,
    ) -> Result<(), CnfError> {
        if encode_forward {
            for (leaf_index, leaf) in gate.leaves.iter().enumerate() {
                match leaf {
                    AndTreeLeaf::Lit(lit) => {
                        let lit = self.encode_lit(*lit);
                        self.add_encoded_clause(
                            context.origin(CnfClauseOriginTemplate::AndTreeForwardLiteral),
                            &[out.negated(), lit],
                        )?;
                    }
                    AndTreeLeaf::NotAnd { lhs, rhs } => {
                        let lhs = self.encode_lit(*lhs).negated();
                        let rhs = self.encode_lit(*rhs).negated();
                        self.add_encoded_clause(
                            context.origin(CnfClauseOriginTemplate::AndTreeForwardNotAnd),
                            &[out.negated(), lhs, rhs],
                        )?;
                    }
                    AndTreeLeaf::Parity { lits, expected } => {
                        self.encode_parity_implication(
                            context,
                            out,
                            leaf_index,
                            parity_leaf_shape(lits),
                            lits,
                            *expected,
                        )?;
                    }
                }
            }
        }
        if encode_reverse {
            debug_assert!(
                gate.leaves
                    .iter()
                    .all(|leaf| matches!(leaf, AndTreeLeaf::Lit(_))),
                "direct non-literal leaves are only planned for positive root-only AND trees"
            );
            let mut long_clause = Vec::with_capacity(gate.leaves.len() + 1);
            long_clause.push(out);
            for leaf in &gate.leaves {
                match leaf {
                    AndTreeLeaf::Lit(lit) => {
                        long_clause.push(self.encode_lit(*lit).negated());
                    }
                    AndTreeLeaf::Parity { .. } => unreachable!(
                        "direct equality leaves are only planned when reverse clauses are omitted"
                    ),
                    AndTreeLeaf::NotAnd { .. } => unreachable!(
                        "direct not-and leaves are only planned when reverse clauses are omitted"
                    ),
                }
            }
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::AndTreeReverse),
                &long_clause,
            )?;
        }
        Ok(())
    }

    fn encode_parity_implication(
        &mut self,
        context: EmissionContext,
        out: EncodedLit,
        leaf_index: usize,
        leaf_shape: CnfParityLeafShape,
        lits: &[AigLit],
        expected: bool,
    ) -> Result<(), CnfError> {
        debug_assert!(
            !lits.is_empty() && lits.len() <= 3,
            "direct parity leaves are intentionally capped"
        );
        let encoded = lits
            .iter()
            .copied()
            .map(|lit| self.encode_lit(lit))
            .collect::<Vec<_>>();
        for mask in 0..(1usize << encoded.len()) {
            let parity = mask.count_ones() % 2 == 1;
            if parity == expected {
                continue;
            }
            let mut clause = Vec::with_capacity(encoded.len() + 1);
            clause.push(out.negated());
            for (index, lit) in encoded.iter().copied().enumerate() {
                let value = ((mask >> index) & 1) == 1;
                clause.push(if value { lit.negated() } else { lit });
            }
            self.add_encoded_clause(context.parity_origin(leaf_index, leaf_shape), &clause)?;
        }
        Ok(())
    }

    fn encode_binary_and_gate(
        &mut self,
        context: EmissionContext,
        out: EncodedLit,
        lhs: AigLit,
        rhs: AigLit,
        encode_forward: bool,
        encode_reverse: bool,
    ) -> Result<(), CnfError> {
        let lhs = self.encode_lit(lhs);
        let rhs = self.encode_lit(rhs);
        if encode_forward {
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::BinaryAndForwardLhs),
                &[out.negated(), lhs],
            )?;
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::BinaryAndForwardRhs),
                &[out.negated(), rhs],
            )?;
        }
        if encode_reverse {
            self.add_encoded_clause(
                context.origin(CnfClauseOriginTemplate::BinaryAndReverse),
                &[out, lhs.negated(), rhs.negated()],
            )?;
        }
        Ok(())
    }

    fn assert_root(&mut self, root: AigLit) -> Result<EncodedLit, CnfError> {
        if root.node().index() != 0 && self.direct_root_nodes[root.node().index()] {
            self.assert_direct_root(root)?;
            Ok(EncodedLit::Const(true))
        } else {
            let cnf_lit = self.encode_lit(root);
            self.add_encoded_clause(
                EmissionContext {
                    phase: CnfClauseOriginPhase::Root,
                    owner: root.node(),
                }
                .origin(CnfClauseOriginTemplate::RootUnit),
                &[cnf_lit],
            )?;
            Ok(cnf_lit)
        }
    }

    fn assert_direct_root(&mut self, root: AigLit) -> Result<(), CnfError> {
        let node_id = root.node();
        let Some(AigNode::And(lhs, rhs)) = self.aig.node(node_id) else {
            unreachable!("direct root nodes are planned only for AND nodes");
        };
        let context = EmissionContext {
            phase: CnfClauseOriginPhase::Root,
            owner: node_id,
        };
        if root.is_inverted()
            && let Some(plan) =
                distributable_negative_and_encoding(self.aig, lhs, rhs, &self.skip_nodes)
        {
            let other = self.encode_lit(plan.other).negated();
            for leaf in plan.or_leaves {
                let leaf = self.encode_lit(leaf).negated();
                self.add_encoded_clause(
                    context.origin(CnfClauseOriginTemplate::DirectNegativeAndLeaf),
                    &[other, leaf],
                )?;
            }
            return Ok(());
        }
        let out = EncodedLit::Const(!root.is_inverted());
        let (encode_forward, encode_reverse) = if root.is_inverted() {
            (false, true)
        } else {
            (true, false)
        };
        if let Some(xor_gate) = self.xor_gates[node_id.index()] {
            self.encode_xor_gate(context, out, xor_gate, encode_forward, encode_reverse)?;
        } else if let Some(not_ite_gate) = self.not_ite_gates[node_id.index()] {
            self.encode_not_ite_gate(context, out, not_ite_gate, encode_forward, encode_reverse)?;
        } else if let Some(not_and_gate) = self.not_and_gates[node_id.index()].clone() {
            self.encode_not_and_gate(context, out, &not_and_gate, encode_forward, encode_reverse)?;
        } else if let Some(and_tree_gate) = self.and_tree_gates[node_id.index()].clone() {
            self.encode_and_tree_gate(
                context,
                out,
                &and_tree_gate,
                encode_forward,
                encode_reverse,
            )?;
        } else {
            self.encode_binary_and_gate(context, out, lhs, rhs, encode_forward, encode_reverse)?;
        }
        Ok(())
    }

    fn clause_directions(&self, node_id: AigNodeId) -> (bool, bool) {
        match self.root_polarities[node_id.index()] {
            Some(true) => (true, false),
            Some(false) => (false, true),
            None => (true, true),
        }
    }

    fn encode_lit(&self, lit: AigLit) -> EncodedLit {
        if lit.node().index() == 0 {
            return EncodedLit::Const(lit.is_inverted());
        }
        debug_assert!(
            !self.skip_nodes[lit.node().index()],
            "optimized-away helper AIG node referenced outside its parent"
        );
        let variable = self.node_vars[lit.node().index()].expect("AIG node has CNF variable");
        let cnf_lit = CnfLit::positive(variable);
        if lit.is_inverted() {
            EncodedLit::Lit(cnf_lit.negated())
        } else {
            EncodedLit::Lit(cnf_lit)
        }
    }

    fn add_encoded_clause(
        &mut self,
        origin: CnfClauseOrigin,
        lits: &[EncodedLit],
    ) -> Result<(), CnfError> {
        self.clause_attempts = self.clause_attempts.saturating_add(1);
        self.construction_profile
            .record_declared_literals(lits.len());
        self.clause_scratch.clear();
        for lit in lits {
            self.construction_profile.record_visited_literal();
            match lit {
                EncodedLit::Const(true) => {
                    self.construction_profile.record_true_tautology();
                    self.tautological_clauses_skipped =
                        self.tautological_clauses_skipped.saturating_add(1);
                    return Ok(());
                }
                EncodedLit::Const(false) => {
                    self.construction_profile.record_false_constant();
                }
                EncodedLit::Lit(cnf_lit) => {
                    if self
                        .clause_scratch
                        .iter()
                        .any(|lit| *lit == cnf_lit.negated())
                    {
                        self.construction_profile.record_complementary_tautology();
                        self.tautological_clauses_skipped =
                            self.tautological_clauses_skipped.saturating_add(1);
                        return Ok(());
                    }
                    if self.clause_scratch.contains(cnf_lit) {
                        self.construction_profile.record_repeated_literal();
                    } else {
                        self.clause_scratch.push(*cnf_lit);
                    }
                }
            }
        }
        self.clause_scratch.sort_unstable();
        self.construction_profile
            .record_canonical_clause(self.clause_scratch.len());
        let fingerprint = clause_fingerprint(&self.clause_scratch);
        let clause = core::mem::take(&mut self.clause_scratch);
        let mut clause = self.insert_canonical_clause(clause, fingerprint, origin)?;
        clause.clear();
        self.clause_scratch = clause;
        Ok(())
    }

    fn insert_canonical_clause(
        &mut self,
        clause: Vec<CnfLit>,
        fingerprint: u64,
        origin: CnfClauseOrigin,
    ) -> Result<Vec<CnfLit>, CnfError> {
        let primary = &mut self.clause_index.primary;
        let collisions = &mut self.clause_index.collisions;
        match primary.entry(fingerprint) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                self.construction_profile.record_primary_vacant();
                let index = self.formula.clause_count();
                self.formula.add_clause_from_slice(&clause)?;
                entry.insert(index);
                self.construction_profile
                    .record_emitted_origin(index, origin);
            }
            std::collections::hash_map::Entry::Occupied(entry) => {
                self.construction_profile.record_primary_occupied();
                if self.formula.clause(*entry.get()) == Some(clause.as_slice()) {
                    self.construction_profile.record_primary_duplicate();
                    self.construction_profile.record_duplicate_origin(
                        *entry.get(),
                        origin,
                        clause.len(),
                    );
                    self.duplicate_clauses_skipped =
                        self.duplicate_clauses_skipped.saturating_add(1);
                    return Ok(clause);
                }
                if let Some(indices) = collisions.get(&fingerprint) {
                    for &index in indices {
                        self.construction_profile.record_collision_comparison();
                        if self.formula.clause(index) == Some(clause.as_slice()) {
                            self.construction_profile.record_collision_duplicate();
                            self.construction_profile.record_duplicate_origin(
                                index,
                                origin,
                                clause.len(),
                            );
                            self.duplicate_clauses_skipped =
                                self.duplicate_clauses_skipped.saturating_add(1);
                            return Ok(clause);
                        }
                    }
                }

                self.construction_profile.record_collision_insert();
                let index = self.formula.clause_count();
                self.formula.add_clause_from_slice(&clause)?;
                collisions.entry(fingerprint).or_default().push(index);
                self.construction_profile
                    .record_emitted_origin(index, origin);
            }
        }
        Ok(clause)
    }
}

type FingerprintMap<T> = HashMap<u64, T, BuildHasherDefault<FingerprintHasher>>;

#[derive(Default)]
struct ClauseIndex {
    primary: FingerprintMap<usize>,
    collisions: FingerprintMap<Vec<usize>>,
}

/// The clause key is already a mixed 64-bit fingerprint. Preserve it as the
/// table hash so lookup has no second hashing pass. The fallback `write` keeps
/// this a total `Hasher` implementation even though `u64::hash` uses
/// `write_u64`.
#[derive(Default)]
struct FingerprintHasher(u64);

impl Hasher for FingerprintHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
        const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;
        let mut hash = FNV_OFFSET;
        for &byte in bytes {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        self.0 = hash;
    }

    fn write_u64(&mut self, value: u64) {
        self.0 = value;
    }
}

fn clause_fingerprint(clause: &[CnfLit]) -> u64 {
    const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut hash = FNV_OFFSET;
    for lit in clause {
        let signed_var = (u64::from(lit.var.0) << 1) | u64::from(lit.negated);
        for byte in signed_var.to_le_bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(FNV_PRIME);
        }
    }
    hash
}

fn count_true(values: &[bool]) -> u64 {
    usize_to_u64_saturating(values.iter().filter(|value| **value).count())
}

fn count_some<T>(values: &[Option<T>]) -> u64 {
    usize_to_u64_saturating(values.iter().filter(|value| value.is_some()).count())
}

fn usize_to_u64_saturating(value: usize) -> u64 {
    u64::try_from(value).unwrap_or(u64::MAX)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct XorGate {
    lhs: AigLit,
    rhs: AigLit,
    helper_nodes: [AigNodeId; 2],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NotIteGate {
    condition: AigLit,
    then_lit: AigLit,
    else_lit: AigLit,
    helper_nodes: [AigNodeId; 2],
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NotAndGate {
    factors: [AndFactor; 2],
    helper_nodes: Vec<AigNodeId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AndFactor {
    Lit(AigLit),
    NotAnd(AigLit, AigLit),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AndTreeGate {
    leaves: Vec<AndTreeLeaf>,
    helper_nodes: Vec<AigNodeId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum AndTreeLeaf {
    Lit(AigLit),
    NotAnd { lhs: AigLit, rhs: AigLit },
    Parity { lits: Vec<AigLit>, expected: bool },
}

struct SparsePlanContext<'a> {
    aig: &'a Aig,
    use_counts: &'a [u32],
    skip_nodes: &'a [bool],
    xor_gates: &'a [Option<XorGate>],
    not_ite_gates: &'a [Option<NotIteGate>],
    not_and_gates: &'a [Option<NotAndGate>],
}

/// Computes the set of AIG nodes reachable from `roots`, as a mask indexed by
/// [`AigNodeId::index`].
///
/// A node is reachable when it is a root node or a transitive AND-child of one.
/// This drives the sparse Tseitin encoding (only reachable gates are encoded) and
/// is also the partition primitive for Craig interpolation: a joint CNF clause is
/// attributed to the `A`-side or `B`-side of a partition by which roots its gates
/// are reachable from. The returned vector has one entry per AIG node, indexed by
/// [`AigNodeId::index`].
#[must_use]
pub fn reachable_node_mask(aig: &Aig, roots: &[AigLit]) -> Vec<bool> {
    let mut reachable = vec![false; aig.node_count()];
    let mut stack = roots.iter().map(|root| root.node()).collect::<Vec<_>>();
    while let Some(node_id) = stack.pop() {
        let index = node_id.index();
        if reachable[index] {
            continue;
        }
        reachable[index] = true;
        if let Some(AigNode::And(lhs, rhs)) = aig.node(node_id) {
            stack.push(lhs.node());
            stack.push(rhs.node());
        }
    }
    reachable
}

fn node_use_counts(aig: &Aig, roots: &[AigLit], reachable: &[bool]) -> Vec<u32> {
    let mut counts = vec![0u32; aig.node_count()];
    for root in roots {
        counts[root.node().index()] = counts[root.node().index()].saturating_add(1);
    }
    for (node_id, node) in aig.nodes() {
        if !reachable[node_id.index()] {
            continue;
        }
        if let AigNode::And(lhs, rhs) = node {
            counts[lhs.node().index()] = counts[lhs.node().index()].saturating_add(1);
            counts[rhs.node().index()] = counts[rhs.node().index()].saturating_add(1);
        }
    }
    counts
}

fn detect_xor_gate(aig: &Aig, node: AigNode) -> Option<XorGate> {
    let AigNode::And(left, right) = node else {
        return None;
    };
    if !left.is_inverted() || !right.is_inverted() {
        return None;
    }
    let left_node = left.node();
    let right_node = right.node();
    let AigNode::And(left_a, left_b) = aig.node(left_node)? else {
        return None;
    };
    let AigNode::And(right_a, right_b) = aig.node(right_node)? else {
        return None;
    };

    if unordered_pair_eq([right_a, right_b], [left_a.negated(), left_b.negated()]) {
        Some(XorGate {
            lhs: left_a,
            rhs: left_b,
            helper_nodes: [left_node, right_node],
        })
    } else {
        None
    }
}

fn detect_not_ite_gate(aig: &Aig, node: AigNode) -> Option<NotIteGate> {
    let AigNode::And(left, right) = node else {
        return None;
    };
    if !left.is_inverted() || !right.is_inverted() {
        return None;
    }
    let left_node = left.node();
    let right_node = right.node();
    let AigNode::And(left_a, left_b) = aig.node(left_node)? else {
        return None;
    };
    let AigNode::And(right_a, right_b) = aig.node(right_node)? else {
        return None;
    };
    not_ite_from_pairs(
        [left_a, left_b],
        [right_a, right_b],
        [left_node, right_node],
    )
}

fn not_ite_from_pairs(
    left: [AigLit; 2],
    right: [AigLit; 2],
    helper_nodes: [AigNodeId; 2],
) -> Option<NotIteGate> {
    for left_index in [0usize, 1] {
        for right_index in [0usize, 1] {
            if left[left_index] == right[right_index].negated() {
                return Some(NotIteGate {
                    condition: left[left_index],
                    then_lit: left[1 - left_index],
                    else_lit: right[1 - right_index],
                    helper_nodes,
                });
            }
        }
    }
    None
}

fn detect_not_and_gate(
    aig: &Aig,
    node: AigNode,
    use_counts: &[u32],
    skip_nodes: &[bool],
    xor_gates: &[Option<XorGate>],
    not_ite_gates: &[Option<NotIteGate>],
) -> Option<NotAndGate> {
    let AigNode::And(lhs, rhs) = node else {
        return None;
    };
    let mut helper_nodes = Vec::new();
    let factors = [
        detect_not_and_factor(
            aig,
            lhs,
            use_counts,
            skip_nodes,
            xor_gates,
            not_ite_gates,
            &mut helper_nodes,
        ),
        detect_not_and_factor(
            aig,
            rhs,
            use_counts,
            skip_nodes,
            xor_gates,
            not_ite_gates,
            &mut helper_nodes,
        ),
    ];
    (!helper_nodes.is_empty()).then_some(NotAndGate {
        factors,
        helper_nodes,
    })
}

fn detect_not_and_factor(
    aig: &Aig,
    lit: AigLit,
    use_counts: &[u32],
    skip_nodes: &[bool],
    xor_gates: &[Option<XorGate>],
    not_ite_gates: &[Option<NotIteGate>],
    helper_nodes: &mut Vec<AigNodeId>,
) -> AndFactor {
    let node = lit.node();
    if lit.is_inverted()
        && node.index() != 0
        && use_counts[node.index()] == 1
        && !skip_nodes[node.index()]
        && xor_gates[node.index()].is_none()
        && not_ite_gates[node.index()].is_none()
        && let Some(AigNode::And(lhs, rhs)) = aig.node(node)
        && lit_has_cnf_var_or_const(lhs, skip_nodes)
        && lit_has_cnf_var_or_const(rhs, skip_nodes)
    {
        helper_nodes.push(node);
        AndFactor::NotAnd(lhs, rhs)
    } else {
        AndFactor::Lit(lit)
    }
}

fn lit_has_cnf_var_or_const(lit: AigLit, skip_nodes: &[bool]) -> bool {
    lit.node().index() == 0 || !skip_nodes[lit.node().index()]
}

struct DistributableNegativeAnd {
    other: AigLit,
    or_leaves: Vec<AigLit>,
    helper_nodes: Vec<AigNodeId>,
}

fn distributable_negative_and_plan(
    context: &SparsePlanContext<'_>,
    lhs: AigLit,
    rhs: AigLit,
) -> Option<DistributableNegativeAnd> {
    if lit_has_cnf_var_or_const(rhs, context.skip_nodes)
        && let Some(or_tree) = collect_private_or_tree_plan(context, lhs)
    {
        return Some(DistributableNegativeAnd {
            other: rhs,
            or_leaves: or_tree.or_leaves,
            helper_nodes: or_tree.helper_nodes,
        });
    }
    if lit_has_cnf_var_or_const(lhs, context.skip_nodes)
        && let Some(or_tree) = collect_private_or_tree_plan(context, rhs)
    {
        return Some(DistributableNegativeAnd {
            other: lhs,
            or_leaves: or_tree.or_leaves,
            helper_nodes: or_tree.helper_nodes,
        });
    }
    None
}

fn distributable_negative_and_encoding(
    aig: &Aig,
    lhs: AigLit,
    rhs: AigLit,
    skip_nodes: &[bool],
) -> Option<DistributableNegativeAnd> {
    if lit_has_cnf_var_or_const(rhs, skip_nodes)
        && let Some(or_tree) = collect_skipped_or_tree(aig, lhs, skip_nodes)
    {
        return Some(DistributableNegativeAnd {
            other: rhs,
            or_leaves: or_tree.or_leaves,
            helper_nodes: or_tree.helper_nodes,
        });
    }
    if lit_has_cnf_var_or_const(lhs, skip_nodes)
        && let Some(or_tree) = collect_skipped_or_tree(aig, rhs, skip_nodes)
    {
        return Some(DistributableNegativeAnd {
            other: lhs,
            or_leaves: or_tree.or_leaves,
            helper_nodes: or_tree.helper_nodes,
        });
    }
    None
}

fn collect_private_or_tree_plan(
    context: &SparsePlanContext<'_>,
    lit: AigLit,
) -> Option<DistributableNegativeAnd> {
    let mut tree = DistributableNegativeAnd {
        other: AigLit::FALSE,
        or_leaves: Vec::new(),
        helper_nodes: Vec::new(),
    };
    collect_private_or_tree_plan_lit(context, lit, &mut tree)?;
    (!tree.helper_nodes.is_empty()).then_some(tree)
}

fn collect_private_or_tree_plan_lit(
    context: &SparsePlanContext<'_>,
    lit: AigLit,
    tree: &mut DistributableNegativeAnd,
) -> Option<()> {
    let node = lit.node();
    if lit.is_inverted()
        && node.index() != 0
        && context.use_counts[node.index()] == 1
        && !context.skip_nodes[node.index()]
        && context.xor_gates[node.index()].is_none()
        && context.not_ite_gates[node.index()].is_none()
        && context.not_and_gates[node.index()].is_none()
        && let Some(AigNode::And(lhs, rhs)) = context.aig.node(node)
    {
        tree.helper_nodes.push(node);
        collect_private_or_tree_plan_lit(context, lhs.negated(), tree)?;
        collect_private_or_tree_plan_lit(context, rhs.negated(), tree)?;
        return Some(());
    }
    if lit_has_cnf_var_or_const(lit, context.skip_nodes) {
        tree.or_leaves.push(lit);
        Some(())
    } else {
        None
    }
}

fn collect_skipped_or_tree(
    aig: &Aig,
    lit: AigLit,
    skip_nodes: &[bool],
) -> Option<DistributableNegativeAnd> {
    let mut tree = DistributableNegativeAnd {
        other: AigLit::FALSE,
        or_leaves: Vec::new(),
        helper_nodes: Vec::new(),
    };
    collect_skipped_or_tree_lit(aig, lit, skip_nodes, &mut tree)?;
    (!tree.helper_nodes.is_empty()).then_some(tree)
}

fn collect_skipped_or_tree_lit(
    aig: &Aig,
    lit: AigLit,
    skip_nodes: &[bool],
    tree: &mut DistributableNegativeAnd,
) -> Option<()> {
    let node = lit.node();
    if lit.is_inverted()
        && node.index() != 0
        && skip_nodes[node.index()]
        && let Some(AigNode::And(lhs, rhs)) = aig.node(node)
    {
        tree.helper_nodes.push(node);
        collect_skipped_or_tree_lit(aig, lhs.negated(), skip_nodes, tree)?;
        collect_skipped_or_tree_lit(aig, rhs.negated(), skip_nodes, tree)?;
        return Some(());
    }
    if lit_has_cnf_var_or_const(lit, skip_nodes) {
        tree.or_leaves.push(lit);
        Some(())
    } else {
        None
    }
}

fn collect_private_and_tree(
    context: &SparsePlanContext<'_>,
    node: AigNode,
    allow_equal_leaves: bool,
) -> Option<AndTreeGate> {
    let AigNode::And(lhs, rhs) = node else {
        return None;
    };
    let mut gate = AndTreeGate {
        leaves: Vec::new(),
        helper_nodes: Vec::new(),
    };
    collect_private_and_leaf(context, lhs, &mut gate, allow_equal_leaves);
    collect_private_and_leaf(context, rhs, &mut gate, allow_equal_leaves);
    (!gate.helper_nodes.is_empty()).then_some(gate)
}

fn collect_private_and_leaf(
    context: &SparsePlanContext<'_>,
    lit: AigLit,
    gate: &mut AndTreeGate,
    allow_equal_leaves: bool,
) {
    let node = lit.node();
    if allow_equal_leaves
        && !lit.is_inverted()
        && node.index() != 0
        && let Some(parity) = collect_private_xor_parity(context, lit)
    {
        gate.helper_nodes.extend(parity.helper_nodes);
        gate.leaves.push(AndTreeLeaf::Parity {
            lits: parity.lits,
            expected: parity.expected,
        });
        return;
    }
    if allow_equal_leaves
        && lit.is_inverted()
        && node.index() != 0
        && context.use_counts[node.index()] == 1
        && !context.skip_nodes[node.index()]
        && context.xor_gates[node.index()].is_none()
        && context.not_ite_gates[node.index()].is_none()
        && context.not_and_gates[node.index()].is_none()
        && let Some(AigNode::And(lhs, rhs)) = context.aig.node(node)
        && lit_has_cnf_var_or_const(lhs, context.skip_nodes)
        && lit_has_cnf_var_or_const(rhs, context.skip_nodes)
    {
        gate.helper_nodes.push(node);
        gate.leaves.push(AndTreeLeaf::NotAnd { lhs, rhs });
        return;
    }
    if lit.is_inverted()
        || node.index() == 0
        || context.use_counts[node.index()] != 1
        || context.skip_nodes[node.index()]
        || context.xor_gates[node.index()].is_some()
        || context.not_ite_gates[node.index()].is_some()
        || context.not_and_gates[node.index()].is_some()
    {
        gate.leaves.push(AndTreeLeaf::Lit(lit));
        return;
    }

    let Some(AigNode::And(lhs, rhs)) = context.aig.node(node) else {
        gate.leaves.push(AndTreeLeaf::Lit(lit));
        return;
    };
    gate.helper_nodes.push(node);
    collect_private_and_leaf(context, lhs, gate, allow_equal_leaves);
    collect_private_and_leaf(context, rhs, gate, allow_equal_leaves);
}

struct ParityLeaf {
    lits: Vec<AigLit>,
    expected: bool,
    helper_nodes: Vec<AigNodeId>,
}

fn parity_leaf_shape(lits: &[AigLit]) -> CnfParityLeafShape {
    debug_assert!((1..=3).contains(&lits.len()));
    let mut false_constants = 0u8;
    let mut true_constants = 0u8;
    let mut nonconstant_nodes = BTreeSet::new();
    for lit in lits {
        if lit.node().index() == 0 {
            if lit.is_inverted() {
                true_constants = true_constants.saturating_add(1);
            } else {
                false_constants = false_constants.saturating_add(1);
            }
        } else {
            nonconstant_nodes.insert(lit.node());
        }
    }
    let mut repeated_literal_pairs = 0u8;
    let mut complementary_literal_pairs = 0u8;
    for lhs in 0..lits.len() {
        for rhs in (lhs + 1)..lits.len() {
            if lits[lhs] == lits[rhs] {
                repeated_literal_pairs = repeated_literal_pairs.saturating_add(1);
            } else if lits[lhs].node() == lits[rhs].node()
                && lits[lhs].is_inverted() != lits[rhs].is_inverted()
            {
                complementary_literal_pairs = complementary_literal_pairs.saturating_add(1);
            }
        }
    }
    CnfParityLeafShape {
        raw_arity: u8::try_from(lits.len()).expect("parity leaf arity is capped at three"),
        false_constants,
        true_constants,
        distinct_nonconstant_nodes: u8::try_from(nonconstant_nodes.len())
            .expect("parity leaf has at most three distinct nodes"),
        repeated_literal_pairs,
        complementary_literal_pairs,
    }
}

fn collect_private_xor_parity(context: &SparsePlanContext<'_>, lit: AigLit) -> Option<ParityLeaf> {
    let mut lits = Vec::new();
    let mut inverted = false;
    let mut helper_nodes = Vec::new();
    collect_private_xor_parity_lit(context, lit, &mut lits, &mut inverted, &mut helper_nodes)?;
    if lits.is_empty() || lits.len() > 3 || helper_nodes.is_empty() {
        return None;
    }
    Some(ParityLeaf {
        lits,
        expected: !inverted,
        helper_nodes,
    })
}

fn collect_private_xor_parity_lit(
    context: &SparsePlanContext<'_>,
    lit: AigLit,
    lits: &mut Vec<AigLit>,
    inverted: &mut bool,
    helper_nodes: &mut Vec<AigNodeId>,
) -> Option<()> {
    let node = lit.node();
    if node.index() != 0
        && context.use_counts[node.index()] == 1
        && !context.skip_nodes[node.index()]
        && let Some(xor_gate) = context.xor_gates[node.index()]
    {
        helper_nodes.push(node);
        if lit.is_inverted() {
            *inverted = !*inverted;
        }
        collect_private_xor_parity_lit(context, xor_gate.lhs, lits, inverted, helper_nodes)?;
        collect_private_xor_parity_lit(context, xor_gate.rhs, lits, inverted, helper_nodes)?;
        return Some(());
    }
    lits.push(lit);
    Some(())
}

fn unordered_pair_eq(lhs: [AigLit; 2], rhs: [AigLit; 2]) -> bool {
    (lhs[0] == rhs[0] && lhs[1] == rhs[1]) || (lhs[0] == rhs[1] && lhs[1] == rhs[0])
}

fn eval_lit(lit: CnfLit, assignment: &[bool]) -> bool {
    assignment[lit.var().index()] ^ lit.is_negated()
}

fn checked_literal_end(current: usize, additional: usize) -> Result<u32, CnfError> {
    let literals = current
        .checked_add(additional)
        .ok_or(CnfError::LiteralIndexTooLarge {
            literals: usize::MAX,
        })?;
    u32::try_from(literals).map_err(|_| CnfError::LiteralIndexTooLarge { literals })
}

fn reserve_rustsat_variables<Cb: batsat::Callbacks>(
    solver: &mut rustsat_batsat::Solver<Cb>,
    variable_count: usize,
) -> Result<(), SatError> {
    if variable_count == 0 {
        return Ok(());
    }
    let max_index = variable_count - 1;
    let max_index = u32::try_from(max_index)
        .ok()
        .filter(|index| *index <= RustSatVar::MAX_IDX)
        .ok_or(SatError::VariableCountTooLarge { variable_count })?;
    solver
        .reserve(RustSatVar::new(max_index))
        .map_err(|error| SatError::Solver(error.to_string()))
}

fn rustsat_clause(clause: &[CnfLit]) -> Result<RustSatClause, SatError> {
    clause
        .iter()
        .copied()
        .map(rustsat_lit)
        .collect::<Result<RustSatClause, SatError>>()
}

/// Inverse of [`rustsat_lit`]: a `rustsat` literal back to a [`CnfLit`] (used to
/// read the assumption core after an unsat solve).
fn cnf_lit_from_rustsat(lit: RustSatLit) -> Result<CnfLit, SatError> {
    let index = lit.var().idx();
    let var = CnfVar::new(index).map_err(|_| SatError::VariableCountTooLarge {
        variable_count: index + 1,
    })?;
    let positive = CnfLit::positive(var);
    Ok(if lit.is_neg() {
        positive.negated()
    } else {
        positive
    })
}

fn rustsat_lit(lit: CnfLit) -> Result<RustSatLit, SatError> {
    let index = u32::try_from(lit.var().index()).map_err(|_| SatError::VariableCountTooLarge {
        variable_count: lit.var().index() + 1,
    })?;
    if index > RustSatVar::MAX_IDX {
        return Err(SatError::VariableCountTooLarge {
            variable_count: lit.var().index() + 1,
        });
    }
    Ok(RustSatVar::new(index).lit(lit.is_negated()))
}

fn rustsat_assignment<Cb: batsat::Callbacks>(
    solver: &rustsat_batsat::Solver<Cb>,
    variable_count: usize,
) -> Result<CnfAssignment, SatError> {
    if variable_count == 0 {
        return Ok(CnfAssignment::new(Vec::new()));
    }
    let max_index = u32::try_from(variable_count - 1)
        .ok()
        .filter(|index| *index <= RustSatVar::MAX_IDX)
        .ok_or(SatError::VariableCountTooLarge { variable_count })?;
    let assignment = solver
        .solution(RustSatVar::new(max_index))
        .map_err(|error| SatError::Solver(error.to_string()))?;
    let values = (0..variable_count)
        .map(|index| {
            let index = u32::try_from(index).expect("index is bounded by max_index");
            match assignment.var_value(RustSatVar::new(index)) {
                RustSatTernaryVal::True => true,
                RustSatTernaryVal::False | RustSatTernaryVal::DontCare => false,
            }
        })
        .collect();
    Ok(CnfAssignment::new(values))
}

fn replay_sparse_aig_values(
    aig: &Aig,
    values: &mut [bool],
    assigned: &[Option<bool>],
    reachable: &[bool],
) -> Result<(), CnfError> {
    for (node_id, node) in aig.nodes() {
        let index = node_id.index();
        let expected = match node {
            AigNode::ConstFalse => false,
            AigNode::Input(_) => assigned[index].map_or_else(
                || {
                    if reachable[index] {
                        Err(CnfError::MissingAigNodeAssignment { node: index })
                    } else {
                        Ok(false)
                    }
                },
                Ok,
            )?,
            AigNode::And(lhs, rhs) => aig_lit_value(lhs, values)? && aig_lit_value(rhs, values)?,
        };
        if let Some(found) = assigned[index] {
            if found != expected {
                return Err(CnfError::AigReplayMismatch {
                    node: node_id.index(),
                    expected,
                    found,
                });
            }
        } else {
            values[index] = expected;
        }
    }
    Ok(())
}

/// Evaluates an AIG literal against an already-computed node-value table.
///
/// Used by the incremental forward recompute, where children precede parents in
/// node-id order, so the child value is always present.
fn aig_lit_in_values(lit: AigLit, values: &[bool]) -> bool {
    let value = values.get(lit.node().index()).copied().unwrap_or(false);
    value ^ lit.is_inverted()
}

fn aig_lit_value(lit: AigLit, values: &[bool]) -> Result<bool, CnfError> {
    let value = values
        .get(lit.node().index())
        .copied()
        .ok_or(CnfError::AigNodeCountMismatch {
            expected: lit.node().index() + 1,
            found: values.len(),
        })?;
    Ok(value ^ lit.is_inverted())
}

fn parse_usize(token: &str) -> Result<usize, CnfError> {
    token
        .parse::<usize>()
        .map_err(|_| CnfError::InvalidLiteral(token.to_owned()))
}

fn parse_dimacs_lit_token(token: &str) -> Result<i64, CnfError> {
    token
        .parse::<i64>()
        .map_err(|_| CnfError::InvalidLiteral(token.to_owned()))
}

fn lit_from_dimacs(value: i64, variable_count: usize) -> Result<CnfLit, CnfError> {
    let abs = value
        .checked_abs()
        .ok_or_else(|| CnfError::InvalidLiteral(value.to_string()))?;
    let variable = usize::try_from(abs - 1)
        .map_err(|_| CnfError::InvalidLiteral(value.to_string()))
        .and_then(CnfVar::new)?;
    if variable.index() >= variable_count {
        return Err(CnfError::InvalidVariable {
            variable: variable.dimacs(),
            variable_count,
        });
    }
    let lit = CnfLit::positive(variable);
    if value < 0 {
        Ok(lit.negated())
    } else {
        Ok(lit)
    }
}
#[cfg(test)]
mod tests {
    use axeyum_aig::{Aig, AigLit};
    use axeyum_bv::lower_terms;
    use axeyum_ir::{Sort, TermArena, Value, eval};

    use super::{
        CnfClause, CnfClauseOriginPhase, CnfClauseOriginSite, CnfClauseOriginTemplate, CnfError,
        CnfLit, CnfVar, EncodedLit, IncrementalCnf, IncrementalCnfStats, IncrementalSat,
        RustSatBatsatSolver, SatProofStatus, SatResult, SatSolver, aig_lit_value,
        checked_literal_end, parse_dimacs, rustsat_batsat_determinism, solve_with_rustsat_batsat,
        solve_with_rustsat_batsat_limits, tseitin_encode, tseitin_encode_profiled,
        tseitin_encode_profiled_with_origins,
    };

    fn test_clause_origin(template: CnfClauseOriginTemplate) -> super::CnfClauseOrigin {
        super::EmissionContext {
            phase: CnfClauseOriginPhase::Root,
            owner: AigLit::FALSE.node(),
        }
        .origin(template)
    }

    #[test]
    fn flat_clause_end_rejects_overflow_without_allocating() {
        let current = usize::try_from(u32::MAX).unwrap();
        let literals = current.saturating_add(1);
        assert_eq!(
            checked_literal_end(current, 1),
            Err(CnfError::LiteralIndexTooLarge { literals })
        );
        assert_eq!(
            checked_literal_end(usize::MAX, 1),
            Err(CnfError::LiteralIndexTooLarge {
                literals: usize::MAX,
            })
        );
    }

    #[test]
    fn profiled_duplicate_origins_partition_same_owner_root_units() {
        let mut aig = Aig::new();
        let input = aig.input("p");
        let (encoding, origins) =
            tseitin_encode_profiled_with_origins(&aig, &[input, input]).unwrap();

        assert_eq!(encoding.stats().duplicate_clauses_skipped, 1);
        assert!(origins.profile_complete);
        assert_eq!(origins.duplicate_clauses, 1);
        assert_eq!(origins.duplicate_canonical_literals, 1);
        assert!(origins.invariants_hold());
        assert_eq!(origins.rows.len(), 1);
        let row = &origins.rows[0];
        let root_unit = CnfClauseOriginSite::new(
            CnfClauseOriginPhase::Root,
            CnfClauseOriginTemplate::RootUnit,
        );
        assert_eq!(row.first_origin, root_unit);
        assert_eq!(row.duplicate_origin, root_unit);
        assert!(row.same_owner);
        assert_eq!(row.duplicate_clauses, 1);
        assert_eq!(row.duplicate_canonical_literals, 1);
        assert_eq!(row.unit_clauses, 1);
        assert_eq!(row.unit_literals, 1);
        assert_eq!(
            std::mem::size_of::<super::DisabledDuplicateOriginStore>(),
            0,
            "ordinary encoding must retain no origin metadata"
        );
    }

    #[test]
    fn parity_leaf_shape_counts_constants_repetition_and_complements() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");

        let repeated = super::parity_leaf_shape(&[p, p, q]);
        assert_eq!(repeated.raw_arity, 3);
        assert_eq!(repeated.false_constants, 0);
        assert_eq!(repeated.true_constants, 0);
        assert_eq!(repeated.distinct_nonconstant_nodes, 2);
        assert_eq!(repeated.repeated_literal_pairs, 1);
        assert_eq!(repeated.complementary_literal_pairs, 0);
        assert!(repeated.invariants_hold());

        let constants_and_complement =
            super::parity_leaf_shape(&[AigLit::FALSE, AigLit::TRUE, p.negated()]);
        assert_eq!(constants_and_complement.false_constants, 1);
        assert_eq!(constants_and_complement.true_constants, 1);
        assert_eq!(constants_and_complement.distinct_nonconstant_nodes, 1);
        assert!(constants_and_complement.invariants_hold());

        let complement = super::parity_leaf_shape(&[p, p.negated(), q]);
        assert_eq!(complement.repeated_literal_pairs, 0);
        assert_eq!(complement.complementary_literal_pairs, 1);
        assert!(complement.invariants_hold());
        assert_eq!(complement.stable_key(), "a3-f0-t0-d2-r0-x1");
    }

    #[test]
    fn parity_duplicate_profile_partitions_within_cross_leaf_and_owner() {
        let p = CnfLit::positive(CnfVar::new(0).unwrap());
        let mut aig = Aig::new();
        let owner_p = aig.input("owner-p").node();
        let owner_q = aig.input("owner-q").node();
        let leaf_input = aig.input("leaf");
        let shape = super::parity_leaf_shape(&[leaf_input, leaf_input]);
        let mut encoder =
            super::TseitinEncoder::<super::EnabledConstructionProfile>::new_profiled(&aig);
        encoder.formula = super::CnfFormula::new(1);
        let context_p = super::EmissionContext {
            phase: CnfClauseOriginPhase::Root,
            owner: owner_p,
        };
        let context_q = super::EmissionContext {
            phase: CnfClauseOriginPhase::Root,
            owner: owner_q,
        };
        let origins = [
            context_p.parity_origin(0, shape),
            context_p.parity_origin(0, shape),
            context_p.parity_origin(1, shape),
            context_q.parity_origin(0, shape),
        ];
        for origin in origins {
            encoder.insert_canonical_clause(vec![p], 7, origin).unwrap();
        }

        let profile = encoder.construction_profile.origins.snapshot();
        assert!(profile.invariants_hold());
        assert_eq!(profile.duplicate_clauses, 3);
        assert_eq!(profile.parity_overlap.duplicate_clauses, 3);
        assert_eq!(profile.parity_overlap.duplicate_canonical_literals, 3);
        assert_eq!(profile.parity_overlap.rows.len(), 3);
        for relation in [
            super::CnfParityOverlapRelation::WithinLeaf,
            super::CnfParityOverlapRelation::CrossLeafSameOwner,
            super::CnfParityOverlapRelation::CrossOwner,
        ] {
            let row = profile
                .parity_overlap
                .rows
                .iter()
                .find(|row| row.relation == relation)
                .expect("every preregistered relation is represented");
            assert_eq!(row.first_shape, shape);
            assert_eq!(row.duplicate_shape, shape);
            assert_eq!(row.duplicate_clauses, 1);
            assert_eq!(row.unit_clauses, 1);
            assert_eq!(row.unit_literals, 1);
        }
    }

    #[test]
    fn clause_fingerprint_collision_requires_exact_equality() {
        let p = CnfLit::positive(CnfVar::new(0).unwrap());
        let q = CnfLit::positive(CnfVar::new(1).unwrap());
        let aig = Aig::new();
        let mut encoder = super::TseitinEncoder::new(&aig);
        encoder.formula = super::CnfFormula::new(2);

        let forced_fingerprint = 7;
        let origin = test_clause_origin(CnfClauseOriginTemplate::RootUnit);
        encoder
            .insert_canonical_clause(vec![p], forced_fingerprint, origin)
            .unwrap();
        encoder
            .insert_canonical_clause(vec![q], forced_fingerprint, origin)
            .unwrap();
        encoder
            .insert_canonical_clause(vec![p], forced_fingerprint, origin)
            .unwrap();
        encoder
            .insert_canonical_clause(vec![q], forced_fingerprint, origin)
            .unwrap();

        assert_eq!(
            encoder
                .formula
                .clauses()
                .map(<[CnfLit]>::to_vec)
                .collect::<Vec<_>>(),
            vec![vec![p], vec![q]],
            "a fingerprint collision must retain both distinct clauses"
        );
        assert_eq!(encoder.duplicate_clauses_skipped, 2);
        assert_eq!(encoder.clause_index.primary.len(), 1);
        assert_eq!(encoder.clause_index.collisions.len(), 1);
        assert_eq!(
            encoder.clause_index.collisions[&forced_fingerprint],
            vec![1]
        );
    }

    #[test]
    fn tseitin_clause_scratch_grows_and_is_clean_between_attempts() {
        let aig = Aig::new();
        let mut encoder = super::TseitinEncoder::new(&aig);
        encoder.formula = super::CnfFormula::new(6);
        let lits = (0..6)
            .map(|index| CnfLit::positive(CnfVar::new(index).unwrap()))
            .collect::<Vec<_>>();
        let encoded_lits = lits
            .iter()
            .copied()
            .map(EncodedLit::Lit)
            .collect::<Vec<_>>();
        let origin = test_clause_origin(CnfClauseOriginTemplate::RootUnit);

        encoder.add_encoded_clause(origin, &encoded_lits).unwrap();
        assert!(encoder.clause_scratch.capacity() >= encoded_lits.len());
        encoder
            .add_encoded_clause(origin, &[EncodedLit::Lit(lits[0].negated())])
            .unwrap();
        encoder.add_encoded_clause(origin, &encoded_lits).unwrap();

        assert_eq!(encoder.formula.clause(0), Some(lits.as_slice()));
        assert_eq!(encoder.formula.clause(1), Some(&[lits[0].negated()][..]));
        assert_eq!(encoder.formula.clause_count(), 2);
        assert_eq!(encoder.duplicate_clauses_skipped, 1);
        assert!(encoder.clause_scratch.is_empty());
        assert!(encoder.clause_scratch.capacity() >= encoded_lits.len());
    }

    #[test]
    fn profiled_clause_construction_counts_forced_collision_paths() {
        assert_eq!(
            std::mem::size_of::<super::DisabledConstructionProfile>(),
            0,
            "ordinary encoder profiling storage must remain zero-sized"
        );
        assert!(
            std::mem::size_of::<super::TseitinEncoder<'_, super::EnabledConstructionProfile>>()
                > std::mem::size_of::<super::TseitinEncoder<'_>>(),
            "only the profiled monomorph may carry detailed counters"
        );
        let p = CnfLit::positive(CnfVar::new(0).unwrap());
        let q = CnfLit::positive(CnfVar::new(1).unwrap());
        let aig = Aig::new();
        let mut encoder =
            super::TseitinEncoder::<super::EnabledConstructionProfile>::new_profiled(&aig);
        encoder.formula = super::CnfFormula::new(2);

        let forced_fingerprint = 7;
        let origin = test_clause_origin(CnfClauseOriginTemplate::RootUnit);
        encoder
            .insert_canonical_clause(vec![p], forced_fingerprint, origin)
            .unwrap();
        encoder
            .insert_canonical_clause(vec![q], forced_fingerprint, origin)
            .unwrap();
        encoder
            .insert_canonical_clause(vec![p], forced_fingerprint, origin)
            .unwrap();
        encoder
            .insert_canonical_clause(vec![q], forced_fingerprint, origin)
            .unwrap();

        let profile = encoder.construction_profile();
        assert!(profile.profile_complete);
        assert_eq!(profile.primary_vacant_probes, 1);
        assert_eq!(profile.primary_occupied_probes, 3);
        assert_eq!(profile.primary_exact_duplicates, 1);
        assert_eq!(profile.collision_bucket_comparisons, 1);
        assert_eq!(profile.collision_exact_duplicates, 1);
        assert_eq!(profile.collision_inserts, 1);
    }

    #[test]
    fn duplicate_origins_keep_first_collision_owner_and_cross_template_cells() {
        let p = CnfLit::positive(CnfVar::new(0).unwrap());
        let q = CnfLit::positive(CnfVar::new(1).unwrap());
        let mut aig = Aig::new();
        let owner_p = aig.input("owner-p").node();
        let owner_q = aig.input("owner-q").node();
        let mut encoder =
            super::TseitinEncoder::<super::EnabledConstructionProfile>::new_profiled(&aig);
        encoder.formula = super::CnfFormula::new(2);
        let gate_lhs_p = super::EmissionContext {
            phase: CnfClauseOriginPhase::Gate,
            owner: owner_p,
        }
        .origin(CnfClauseOriginTemplate::BinaryAndForwardLhs);
        let gate_lhs_q = super::EmissionContext {
            phase: CnfClauseOriginPhase::Gate,
            owner: owner_q,
        }
        .origin(CnfClauseOriginTemplate::BinaryAndForwardLhs);
        let root_p = super::EmissionContext {
            phase: CnfClauseOriginPhase::Root,
            owner: owner_p,
        }
        .origin(CnfClauseOriginTemplate::RootUnit);
        let root_q = super::EmissionContext {
            phase: CnfClauseOriginPhase::Root,
            owner: owner_q,
        }
        .origin(CnfClauseOriginTemplate::RootUnit);

        let forced_fingerprint = 7;
        encoder
            .insert_canonical_clause(vec![p], forced_fingerprint, gate_lhs_p)
            .unwrap();
        encoder
            .insert_canonical_clause(vec![p], forced_fingerprint, gate_lhs_q)
            .unwrap();
        encoder
            .insert_canonical_clause(vec![p], forced_fingerprint, root_p)
            .unwrap();
        encoder
            .insert_canonical_clause(vec![q], forced_fingerprint, root_q)
            .unwrap();
        encoder
            .insert_canonical_clause(vec![q], forced_fingerprint, gate_lhs_q)
            .unwrap();

        let origins = encoder.construction_profile.origins.snapshot();
        assert!(origins.invariants_hold());
        assert_eq!(origins.duplicate_clauses, 3);
        assert_eq!(origins.duplicate_canonical_literals, 3);
        assert_eq!(origins.rows.len(), 3);
        assert!(origins.rows.iter().any(|row| {
            row.first_origin.template == CnfClauseOriginTemplate::BinaryAndForwardLhs
                && row.duplicate_origin.template == CnfClauseOriginTemplate::BinaryAndForwardLhs
                && !row.same_owner
        }));
        assert!(origins.rows.iter().any(|row| {
            row.first_origin.template == CnfClauseOriginTemplate::BinaryAndForwardLhs
                && row.duplicate_origin.template == CnfClauseOriginTemplate::RootUnit
                && row.same_owner
        }));
        assert!(origins.rows.iter().any(|row| {
            row.first_origin.template == CnfClauseOriginTemplate::RootUnit
                && row.duplicate_origin.template == CnfClauseOriginTemplate::BinaryAndForwardLhs
                && row.same_owner
        }));
    }

    #[test]
    fn profiled_clause_construction_counts_canonicalization_paths() {
        let p = CnfLit::positive(CnfVar::new(0).unwrap());
        let q = CnfLit::positive(CnfVar::new(1).unwrap());
        let aig = Aig::new();
        let mut encoder =
            super::TseitinEncoder::<super::EnabledConstructionProfile>::new_profiled(&aig);
        encoder.formula = super::CnfFormula::new(2);
        let origin = test_clause_origin(CnfClauseOriginTemplate::RootUnit);

        encoder
            .add_encoded_clause(
                origin,
                &[
                    EncodedLit::Const(false),
                    EncodedLit::Lit(p),
                    EncodedLit::Lit(p),
                ],
            )
            .unwrap();
        encoder
            .add_encoded_clause(
                origin,
                &[
                    EncodedLit::Const(false),
                    EncodedLit::Lit(p),
                    EncodedLit::Lit(p),
                ],
            )
            .unwrap();
        encoder
            .add_encoded_clause(
                origin,
                &[
                    EncodedLit::Lit(p),
                    EncodedLit::Lit(p.negated()),
                    EncodedLit::Lit(q),
                ],
            )
            .unwrap();
        encoder
            .add_encoded_clause(origin, &[EncodedLit::Const(true), EncodedLit::Lit(q)])
            .unwrap();

        let profile = encoder.construction_profile();
        assert!(profile.profile_complete);
        assert_eq!(profile.declared_clause_literals, 11);
        assert_eq!(profile.visited_clause_literals, 9);
        assert_eq!(profile.false_constants_dropped, 2);
        assert_eq!(profile.repeated_literals_dropped, 2);
        assert_eq!(profile.true_constant_tautologies, 1);
        assert_eq!(profile.complementary_literal_tautologies, 1);
        assert_eq!(profile.canonical_literals, 2);
        assert_eq!(profile.canonical_empty_clauses, 0);
        assert_eq!(profile.canonical_unit_clauses, 2);
        assert_eq!(profile.canonical_binary_clauses, 0);
        assert_eq!(profile.canonical_ternary_clauses, 0);
        assert_eq!(profile.canonical_larger_clauses, 0);
        assert_eq!(profile.primary_vacant_probes, 1);
        assert_eq!(profile.primary_occupied_probes, 1);
        assert_eq!(profile.primary_exact_duplicates, 1);
        assert_eq!(profile.collision_bucket_comparisons, 0);
        assert_eq!(profile.collision_exact_duplicates, 0);
        assert_eq!(profile.collision_inserts, 0);
        assert_eq!(encoder.clause_attempts, 4);
        assert_eq!(encoder.tautological_clauses_skipped, 2);
        assert_eq!(encoder.duplicate_clauses_skipped, 1);
        assert_eq!(encoder.formula.clause(0), Some(&[p][..]));
    }

    #[test]
    fn tseitin_formula_tracks_aig_root_truth() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let root = aig.xor(p, q);
        let encoding = tseitin_encode(&aig, &[root]).unwrap();

        assert_eq!(
            encoding.variable_bindings().len(),
            2,
            "XOR-shaped helper ANDs and assertion-only root are not assigned CNF variables"
        );
        assert!(
            encoding.variable_bindings().len() < aig.node_count() - 1,
            "sparse encoding should be smaller than one variable per AIG node"
        );
        let stats = encoding.stats();
        assert_eq!(
            stats.construction_profile,
            super::CnfConstructionProfile::default()
        );
        assert_eq!(stats.xor_gates, 1);
        assert_eq!(stats.skipped_helper_nodes, 2);
        assert_eq!(stats.direct_root_nodes, 1);
        assert_eq!(
            stats.clauses_emitted,
            encoding.formula().clauses().len() as u64
        );
        assert!(stats.clause_attempts >= stats.clauses_emitted);
        assert_eq!(
            stats.clause_attempts,
            stats.clauses_emitted
                + stats.tautological_clauses_skipped
                + stats.duplicate_clauses_skipped,
            "every clause attempt is emitted or skipped for one recorded reason"
        );

        for p_value in [false, true] {
            for q_value in [false, true] {
                let inputs = [p_value, q_value];
                let cnf_assignment = encoding
                    .cnf_assignment_from_aig_inputs(&aig, &inputs)
                    .unwrap();
                let expected_root = aig.eval(root, &inputs).unwrap();
                assert_eq!(
                    cnf_assignment.satisfies(encoding.formula()).unwrap(),
                    expected_root,
                    "p={p_value} q={q_value}"
                );
                if expected_root {
                    let aig_values = encoding
                        .aig_node_values_from_assignment(&aig, &cnf_assignment)
                        .unwrap();
                    assert_eq!(
                        aig_lit_value(root, &aig_values).unwrap(),
                        expected_root,
                        "sparse replay reconstructs p={p_value} q={q_value}"
                    );
                }
            }
        }
    }

    #[test]
    fn profiled_tseitin_is_structurally_identical_and_satisfies_partitions() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let xor = aig.xor(p, q);
        let root = aig.and(xor, p);
        let ordinary = tseitin_encode(&aig, &[root]).unwrap();
        let profiled = tseitin_encode_profiled(&aig, &[root]).unwrap();

        assert_eq!(profiled.formula(), ordinary.formula());
        assert_eq!(
            profiled.formula().to_dimacs(),
            ordinary.formula().to_dimacs()
        );
        assert_eq!(profiled.roots(), ordinary.roots());
        assert_eq!(profiled.variable_bindings(), ordinary.variable_bindings());
        let ordinary_stats = ordinary.stats();
        let profiled_stats = profiled.stats();
        assert_eq!(
            profiled_stats.clause_attempts,
            ordinary_stats.clause_attempts
        );
        assert_eq!(
            profiled_stats.tautological_clauses_skipped,
            ordinary_stats.tautological_clauses_skipped
        );
        assert_eq!(
            profiled_stats.duplicate_clauses_skipped,
            ordinary_stats.duplicate_clauses_skipped
        );
        assert_eq!(
            profiled_stats.clauses_emitted,
            ordinary_stats.clauses_emitted
        );

        let profile = profiled_stats.construction_profile;
        assert!(profile.profile_complete);
        let non_tautological = profiled_stats
            .clause_attempts
            .saturating_sub(profiled_stats.tautological_clauses_skipped);
        assert_eq!(
            non_tautological,
            profile.canonical_empty_clauses
                + profile.canonical_unit_clauses
                + profile.canonical_binary_clauses
                + profile.canonical_ternary_clauses
                + profile.canonical_larger_clauses
        );
        assert_eq!(
            non_tautological,
            profile.primary_vacant_probes + profile.primary_occupied_probes
        );
        assert_eq!(
            profile.primary_occupied_probes,
            profile.primary_exact_duplicates
                + profile.collision_exact_duplicates
                + profile.collision_inserts
        );
        assert_eq!(
            profiled_stats.duplicate_clauses_skipped,
            profile.primary_exact_duplicates + profile.collision_exact_duplicates
        );
        assert_eq!(
            profiled_stats.clauses_emitted,
            profile.primary_vacant_probes + profile.collision_inserts
        );
        assert_eq!(
            profiled_stats.tautological_clauses_skipped,
            profile.true_constant_tautologies + profile.complementary_literal_tautologies
        );
    }

    #[test]
    fn tseitin_asserts_positive_and_root_without_root_variable() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let root = aig.and(p, q);
        let encoding = tseitin_encode(&aig, &[root]).unwrap();

        assert_eq!(
            encoding.variable_bindings().len(),
            2,
            "assertion-only AND root does not need a CNF variable"
        );
        assert_eq!(encoding.roots()[0].cnf_lit, EncodedLit::Const(true));

        for p_value in [false, true] {
            for q_value in [false, true] {
                let inputs = [p_value, q_value];
                let expected_root = aig.eval(root, &inputs).unwrap();
                let cnf_assignment = encoding
                    .cnf_assignment_from_aig_inputs(&aig, &inputs)
                    .unwrap();
                assert_eq!(
                    cnf_assignment.satisfies(encoding.formula()).unwrap(),
                    expected_root,
                    "p={p_value} q={q_value}"
                );
                if expected_root {
                    let aig_values = encoding
                        .aig_node_values_from_assignment(&aig, &cnf_assignment)
                        .unwrap();
                    assert_eq!(aig_lit_value(root, &aig_values).unwrap(), expected_root);
                }
            }
        }
    }

    #[test]
    fn tseitin_asserts_negative_and_root_without_root_variable() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let positive_root = aig.and(p, q);
        let root = positive_root.negated();
        let encoding = tseitin_encode(&aig, &[root]).unwrap();

        assert_eq!(
            encoding.variable_bindings().len(),
            2,
            "assertion-only negated AND root does not need a CNF variable"
        );
        assert_eq!(encoding.roots()[0].cnf_lit, EncodedLit::Const(true));

        for p_value in [false, true] {
            for q_value in [false, true] {
                let inputs = [p_value, q_value];
                let expected_root = aig.eval(root, &inputs).unwrap();
                let cnf_assignment = encoding
                    .cnf_assignment_from_aig_inputs(&aig, &inputs)
                    .unwrap();
                assert_eq!(
                    cnf_assignment.satisfies(encoding.formula()).unwrap(),
                    expected_root,
                    "p={p_value} q={q_value}"
                );
                if expected_root {
                    let aig_values = encoding
                        .aig_node_values_from_assignment(&aig, &cnf_assignment)
                        .unwrap();
                    assert_eq!(aig_lit_value(root, &aig_values).unwrap(), expected_root);
                }
            }
        }
    }

    #[test]
    fn tseitin_sparse_encodes_private_mux_helpers() {
        let mut aig = Aig::new();
        let c = aig.input("c");
        let p = aig.input("p");
        let q = aig.input("q");
        let root = aig.mux(c, p, q);
        let encoding = tseitin_encode(&aig, &[root]).unwrap();

        assert_eq!(
            encoding.variable_bindings().len(),
            3,
            "private mux helper ANDs and assertion-only root are not assigned CNF variables"
        );
        assert!(
            encoding.variable_bindings().len() < aig.node_count() - 1,
            "sparse mux encoding should be smaller than one variable per AIG node"
        );

        for c_value in [false, true] {
            for p_value in [false, true] {
                for q_value in [false, true] {
                    let inputs = [c_value, p_value, q_value];
                    let expected_root = aig.eval(root, &inputs).unwrap();
                    let cnf_assignment = encoding
                        .cnf_assignment_from_aig_inputs(&aig, &inputs)
                        .unwrap();
                    assert_eq!(
                        cnf_assignment.satisfies(encoding.formula()).unwrap(),
                        expected_root,
                        "c={c_value} p={p_value} q={q_value}"
                    );
                    if expected_root {
                        let aig_values = encoding
                            .aig_node_values_from_assignment(&aig, &cnf_assignment)
                            .unwrap();
                        assert_eq!(
                            aig_lit_value(root, &aig_values).unwrap(),
                            expected_root,
                            "sparse replay reconstructs c={c_value} p={p_value} q={q_value}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn tseitin_flattens_private_and_tree_helpers() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let r = aig.input("r");
        let s = aig.input("s");
        let left = aig.and(p, q);
        let right = aig.and(r, s);
        let root = aig.and(left, right);
        let encoding = tseitin_encode(&aig, &[root]).unwrap();

        assert_eq!(
            encoding.variable_bindings().len(),
            4,
            "private AND-tree helper nodes and assertion-only root are not assigned CNF variables"
        );
        assert!(
            !encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == left.node()),
            "left private AND helper should be skipped"
        );
        assert!(
            !encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == right.node()),
            "right private AND helper should be skipped"
        );

        for p_value in [false, true] {
            for q_value in [false, true] {
                for r_value in [false, true] {
                    for s_value in [false, true] {
                        let inputs = [p_value, q_value, r_value, s_value];
                        let expected_root = aig.eval(root, &inputs).unwrap();
                        let cnf_assignment = encoding
                            .cnf_assignment_from_aig_inputs(&aig, &inputs)
                            .unwrap();
                        assert_eq!(
                            cnf_assignment.satisfies(encoding.formula()).unwrap(),
                            expected_root,
                            "p={p_value} q={q_value} r={r_value} s={s_value}"
                        );
                        if expected_root {
                            let aig_values = encoding
                                .aig_node_values_from_assignment(&aig, &cnf_assignment)
                                .unwrap();
                            assert_eq!(
                                aig_lit_value(root, &aig_values).unwrap(),
                                expected_root,
                                "sparse replay reconstructs p={p_value} q={q_value} r={r_value} s={s_value}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn tseitin_encodes_positive_root_not_and_leaves_directly() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let r = aig.input("r");
        let s = aig.input("s");
        let left_or = aig.or(p, q);
        let right_or = aig.or(r, s);
        let root = aig.and(left_or, right_or);
        let encoding = tseitin_encode(&aig, &[root]).unwrap();

        assert_eq!(
            encoding.variable_bindings().len(),
            4,
            "input variables are enough for an asserted AND of private OR leaves"
        );
        assert_eq!(
            encoding.formula().clauses().len(),
            2,
            "positive root not-and leaves encode as direct OR clauses"
        );
        assert!(
            !encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == left_or.node()),
            "left OR helper should be skipped"
        );
        assert!(
            !encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == right_or.node()),
            "right OR helper should be skipped"
        );

        for p_value in [false, true] {
            for q_value in [false, true] {
                for r_value in [false, true] {
                    for s_value in [false, true] {
                        let inputs = [p_value, q_value, r_value, s_value];
                        let expected_root = aig.eval(root, &inputs).unwrap();
                        let cnf_assignment = encoding
                            .cnf_assignment_from_aig_inputs(&aig, &inputs)
                            .unwrap();
                        assert_eq!(
                            cnf_assignment.satisfies(encoding.formula()).unwrap(),
                            expected_root,
                            "p={p_value} q={q_value} r={r_value} s={s_value}"
                        );
                        if expected_root {
                            let aig_values = encoding
                                .aig_node_values_from_assignment(&aig, &cnf_assignment)
                                .unwrap();
                            assert_eq!(aig_lit_value(root, &aig_values).unwrap(), expected_root);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn tseitin_internal_not_and_gate_matches_truth_table_in_both_directions() {
        let mut aig = Aig::new();
        let left_a = aig.input("p");
        let left_b = aig.input("q");
        let right_a = aig.input("r");
        let right_b = aig.input("s");
        let pivot = aig.input("t");
        let left_or = aig.or(left_a, left_b);
        let right_or = aig.or(right_a, right_b);
        let not_and_gate = aig.and(left_or, right_or);
        let root = aig.xor(not_and_gate, pivot);
        let encoding = tseitin_encode(&aig, &[root]).unwrap();

        assert_eq!(
            encoding.stats().not_and_gates,
            1,
            "the internal gate should exercise the two-private-factor not-AND encoder"
        );

        for mask in 0_u8..32 {
            let inputs = [
                mask & 1 != 0,
                mask & 2 != 0,
                mask & 4 != 0,
                mask & 8 != 0,
                mask & 16 != 0,
            ];
            let expected_root = aig.eval(root, &inputs).unwrap();
            let cnf_assignment = encoding
                .cnf_assignment_from_aig_inputs(&aig, &inputs)
                .unwrap();
            assert_eq!(
                cnf_assignment.satisfies(encoding.formula()).unwrap(),
                expected_root,
                "mask={mask:05b}"
            );
            if expected_root {
                let aig_values = encoding
                    .aig_node_values_from_assignment(&aig, &cnf_assignment)
                    .unwrap();
                assert_eq!(aig_lit_value(root, &aig_values).unwrap(), expected_root);
            }
        }
    }

    #[test]
    fn tseitin_distributes_negative_root_over_private_or_tree() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let r = aig.input("r");
        let disjunction = aig.or(p, q);
        let root = aig.and(disjunction, r).negated();
        let encoding = tseitin_encode(&aig, &[root]).unwrap();

        assert_eq!(
            encoding.variable_bindings().len(),
            3,
            "inputs are enough for an asserted negated AND over a private OR child"
        );
        assert_eq!(
            encoding.formula().clauses().len(),
            2,
            "not((p or q) and r) distributes to two direct clauses"
        );
        assert!(
            !encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == disjunction.node()),
            "private OR child should be skipped"
        );

        for p_value in [false, true] {
            for q_value in [false, true] {
                for r_value in [false, true] {
                    let inputs = [p_value, q_value, r_value];
                    let expected_root = aig.eval(root, &inputs).unwrap();
                    let cnf_assignment = encoding
                        .cnf_assignment_from_aig_inputs(&aig, &inputs)
                        .unwrap();
                    assert_eq!(
                        cnf_assignment.satisfies(encoding.formula()).unwrap(),
                        expected_root,
                        "p={p_value} q={q_value} r={r_value}"
                    );
                    if expected_root {
                        let aig_values = encoding
                            .aig_node_values_from_assignment(&aig, &cnf_assignment)
                            .unwrap();
                        assert_eq!(aig_lit_value(root, &aig_values).unwrap(), expected_root);
                    }
                }
            }
        }
    }

    #[test]
    fn tseitin_sparse_encodes_private_or_of_and_helpers() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let r = aig.input("r");
        let s = aig.input("s");
        let left = aig.and(p, q);
        let right = aig.and(r, s);
        let root = aig.or(left, right);
        let encoding = tseitin_encode(&aig, &[root]).unwrap();

        assert_eq!(
            encoding.variable_bindings().len(),
            4,
            "private OR-of-AND helpers and assertion-only root are encoded through the parent"
        );
        assert!(
            !encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == left.node()),
            "left private AND helper should be skipped"
        );
        assert!(
            !encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == right.node()),
            "right private AND helper should be skipped"
        );

        for p_value in [false, true] {
            for q_value in [false, true] {
                for r_value in [false, true] {
                    for s_value in [false, true] {
                        let inputs = [p_value, q_value, r_value, s_value];
                        let expected_root = aig.eval(root, &inputs).unwrap();
                        let cnf_assignment = encoding
                            .cnf_assignment_from_aig_inputs(&aig, &inputs)
                            .unwrap();
                        assert_eq!(
                            cnf_assignment.satisfies(encoding.formula()).unwrap(),
                            expected_root,
                            "p={p_value} q={q_value} r={r_value} s={s_value}"
                        );
                        if expected_root {
                            let aig_values = encoding
                                .aig_node_values_from_assignment(&aig, &cnf_assignment)
                                .unwrap();
                            assert_eq!(
                                aig_lit_value(root, &aig_values).unwrap(),
                                expected_root,
                                "sparse replay reconstructs p={p_value} q={q_value} r={r_value} s={s_value}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn tseitin_encodes_positive_root_equality_leaves_directly() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(2)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(2)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let root = arena.eq(x, y).unwrap();
        let lowering = lower_terms(&arena, &[root]).unwrap();
        let root_lit = lowering.roots()[0].bits()[0];
        let encoding = tseitin_encode(lowering.aig(), &[root_lit]).unwrap();

        assert_eq!(
            encoding.variable_bindings().len(),
            4,
            "two input bit-vectors are encoded; the equality assertion root is direct"
        );
        assert_eq!(
            encoding.formula().clauses().len(),
            4,
            "positive root equality uses direct leaf clauses instead of XOR Tseitin variables"
        );

        for x_value in 0..4 {
            for y_value in 0..4 {
                let mut assignment = axeyum_ir::Assignment::new();
                assignment.set(
                    x_sym,
                    Value::Bv {
                        width: 2,
                        value: x_value,
                    },
                );
                assignment.set(
                    y_sym,
                    Value::Bv {
                        width: 2,
                        value: y_value,
                    },
                );
                let inputs = lowering.input_values(&assignment).unwrap();
                let expected_root = eval(&arena, root, &assignment).unwrap() == Value::Bool(true);
                let cnf_assignment = encoding
                    .cnf_assignment_from_aig_inputs(lowering.aig(), &inputs)
                    .unwrap();
                assert_eq!(
                    cnf_assignment.satisfies(encoding.formula()).unwrap(),
                    expected_root,
                    "x={x_value} y={y_value}"
                );
                if expected_root {
                    let aig_values = encoding
                        .aig_node_values_from_assignment(lowering.aig(), &cnf_assignment)
                        .unwrap();
                    assert_eq!(
                        aig_lit_value(root_lit, &aig_values).unwrap(),
                        expected_root,
                        "direct equality leaf replay reconstructs x={x_value} y={y_value}"
                    );
                }
            }
        }
    }

    #[test]
    fn tseitin_ignores_dead_aig_nodes() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let dead = aig.and(p, q);
        let encoding = tseitin_encode(&aig, &[p]).unwrap();

        assert_eq!(
            encoding.variable_bindings().len(),
            1,
            "unreachable input and AND nodes are not assigned CNF variables"
        );
        assert!(
            !encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == q.node()),
            "dead input should not be encoded"
        );
        assert!(
            !encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == dead.node()),
            "dead AND should not be encoded"
        );

        let cnf_assignment = encoding
            .cnf_assignment_from_aig_inputs(&aig, &[true, true])
            .unwrap();
        assert!(cnf_assignment.satisfies(encoding.formula()).unwrap());
        let aig_values = encoding
            .aig_node_values_from_assignment(&aig, &cnf_assignment)
            .unwrap();
        assert!(aig_lit_value(p, &aig_values).unwrap());
        assert!(!aig_lit_value(q, &aig_values).unwrap());
        assert!(!aig_lit_value(dead, &aig_values).unwrap());
    }

    #[test]
    fn tseitin_keeps_shared_and_helper_variable() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let r = aig.input("r");
        let shared = aig.and(p, q);
        let root_a = aig.and(shared, r);
        let root_b = aig.and(shared, r.negated());
        let encoding = tseitin_encode(&aig, &[root_a, root_b]).unwrap();

        assert!(
            encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == shared.node()),
            "shared AND helper must retain a CNF variable"
        );
        assert_eq!(
            encoding.variable_bindings().len(),
            4,
            "shared internal helper is kept while assertion-only roots are direct"
        );
        assert!(
            !encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == root_a.node()),
            "first assertion root should be direct"
        );
        assert!(
            !encoding
                .variable_bindings()
                .iter()
                .any(|binding| binding.aig_literal.node() == root_b.node()),
            "second assertion root should be direct"
        );
    }

    #[test]
    fn constants_encode_without_variables() {
        let aig = Aig::new();
        let true_encoding = tseitin_encode(&aig, &[AigLit::TRUE]).unwrap();
        let false_encoding = tseitin_encode(&aig, &[AigLit::FALSE]).unwrap();

        assert_eq!(true_encoding.formula().variable_count(), 0);
        assert!(true_encoding.formula().evaluate(&[]).unwrap());
        assert!(!false_encoding.formula().evaluate(&[]).unwrap());
        assert_eq!(false_encoding.formula().clause(0), Some(&[][..]));
        assert_eq!(true_encoding.roots()[0].cnf_lit, EncodedLit::Const(true));
    }

    #[test]
    fn dimacs_round_trip_preserves_formula() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let root = aig.mux(p, q, q.negated());
        let encoding = tseitin_encode(&aig, &[root]).unwrap();
        let dimacs = encoding.formula().to_dimacs();
        let reparsed = parse_dimacs(&dimacs).unwrap();

        assert_eq!(reparsed, *encoding.formula());
    }

    #[test]
    fn parser_rejects_malformed_dimacs() {
        assert!(matches!(
            parse_dimacs("1 0\n"),
            Err(CnfError::MissingProblemLine)
        ));
        assert!(matches!(
            parse_dimacs("p cnf 1 1\n2 0\n"),
            Err(CnfError::InvalidVariable {
                variable: 2,
                variable_count: 1
            })
        ));
        assert!(matches!(
            parse_dimacs("p cnf 1 2\n1 0\n"),
            Err(CnfError::ClauseCountMismatch {
                expected: 2,
                found: 1
            })
        ));
    }

    #[test]
    fn evaluator_rejects_wrong_assignment_length() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let encoding = tseitin_encode(&aig, &[p]).unwrap();

        assert!(matches!(
            encoding.formula().evaluate(&[]),
            Err(CnfError::AssignmentLengthMismatch {
                expected: 1,
                found: 0
            })
        ));
    }

    #[test]
    fn rustsat_batsat_solves_raw_cnf_and_replays_assignment() {
        let formula = parse_dimacs(
            "\
p cnf 2 2
1 2 0
-1 2 0
",
        )
        .unwrap();

        let result = solve_with_rustsat_batsat(&formula).unwrap();
        let SatResult::Sat(assignment) = result else {
            panic!("expected SAT result");
        };

        assert!(assignment.satisfies(&formula).unwrap());
        assert_eq!(assignment.values().len(), 2);
        assert!(assignment.values()[1], "second variable is forced true");
    }

    #[test]
    fn rustsat_batsat_determinism_matches_the_reviewed_pinned_defaults() {
        let profile = rustsat_batsat_determinism();
        assert_eq!(profile.random_seed.to_bits(), 91_648_253.0_f64.to_bits());
        assert_eq!(profile.random_var_freq.to_bits(), 0.0_f64.to_bits());
        assert!(!profile.random_polarity);
        assert!(!profile.random_initial_activity);
    }

    #[test]
    fn rustsat_batsat_deterministic_resource_limit_is_an_unknown_not_a_verdict() {
        let formula = parse_dimacs(
            "\
p cnf 2 1
1 2 0
",
        )
        .unwrap();

        for _ in 0..2 {
            assert!(matches!(
                solve_with_rustsat_batsat_limits(&formula, None, Some(0)).unwrap(),
                SatResult::Unknown(reason)
                    if reason.detail
                        == "rustsat-batsat deterministic progress-check budget 0 exhausted"
            ));
        }
        assert!(matches!(
            solve_with_rustsat_batsat_limits(&formula, None, Some(100)).unwrap(),
            SatResult::Sat(assignment) if assignment.satisfies(&formula).unwrap()
        ));
    }

    #[test]
    fn rustsat_batsat_marks_unsat_lower_assurance_without_proof() {
        let formula = parse_dimacs(
            "\
p cnf 1 2
1 0
-1 0
",
        )
        .unwrap();

        assert!(matches!(
            solve_with_rustsat_batsat(&formula).unwrap(),
            SatResult::Unsat(evidence) if evidence.proof == SatProofStatus::Unchecked
        ));
    }

    #[test]
    fn dimacs_micro_corpus_solves_through_sat_trait() {
        let corpus =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/micro-cnf");
        // `read_dir` can transiently return `NotFound` on a shared checkout when a
        // concurrent process is walking/rebuilding the tree during a
        // `--workspace --lib` sweep; the directory is committed and static, so a
        // bounded retry rides over the race instead of a spurious test failure.
        let entries = {
            let mut attempt = 0;
            loop {
                match std::fs::read_dir(&corpus) {
                    Ok(entries) => break entries,
                    Err(err) if err.kind() == std::io::ErrorKind::NotFound && attempt < 10 => {
                        attempt += 1;
                        std::thread::sleep(std::time::Duration::from_millis(50));
                    }
                    Err(err) => panic!("read_dir({}): {err}", corpus.display()),
                }
            }
        };
        let mut files = entries
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|extension| extension == "cnf"))
            .collect::<Vec<_>>();
        files.sort();
        assert_eq!(files.len(), 2);

        for file in files {
            let input = std::fs::read_to_string(&file).unwrap();
            let formula = parse_dimacs(&input).unwrap();
            let mut solver = RustSatBatsatSolver::new();
            let result = solver.solve(&formula).unwrap();
            let name = file.file_name().unwrap().to_string_lossy();
            match (name.contains("unsat"), result) {
                (true, SatResult::Unsat(evidence)) => {
                    assert_eq!(evidence.proof, SatProofStatus::Unchecked);
                }
                (false, SatResult::Sat(assignment)) => {
                    assert!(assignment.satisfies(&formula).unwrap());
                }
                (expected_unsat, other) => {
                    panic!("{name}: expected_unsat={expected_unsat}, got {other:?}");
                }
            }
        }
    }

    #[test]
    fn sat_assignment_lifts_through_cnf_aig_and_original_terms() {
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(3)).unwrap();
        let y_sym = arena.declare("y", Sort::BitVec(3)).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let two = arena.bv_const(3, 2).unwrap();
        let five = arena.bv_const(3, 5).unwrap();
        let x_is_two = arena.eq(x, two).unwrap();
        let sum = arena.bv_add(x, y).unwrap();
        let sum_is_five = arena.eq(sum, five).unwrap();
        let root = arena.and(x_is_two, sum_is_five).unwrap();

        let lowering = lower_terms(&arena, &[root]).unwrap();
        let root_lit = lowering.roots()[0].bits()[0];
        let encoding = tseitin_encode(lowering.aig(), &[root_lit]).unwrap();

        let result = solve_with_rustsat_batsat(encoding.formula()).unwrap();
        let SatResult::Sat(cnf_assignment) = result else {
            panic!("expected SAT result");
        };

        let aig_values = encoding
            .aig_node_values_from_assignment(lowering.aig(), &cnf_assignment)
            .unwrap();
        let model = lowering.assignment_from_aig_values(&aig_values).unwrap();

        assert_eq!(eval(&arena, root, &model).unwrap(), Value::Bool(true));
        assert_eq!(
            lowering.root_values_from_aig_values(&aig_values).unwrap(),
            vec![Value::Bool(true)]
        );
    }

    fn var(index: usize) -> CnfVar {
        CnfVar::new(index).unwrap()
    }

    fn pos(index: usize) -> CnfLit {
        CnfLit::positive(var(index))
    }

    fn neg(index: usize) -> CnfLit {
        CnfLit::positive(var(index)).negated()
    }

    #[test]
    fn incremental_accumulates_clauses_across_solves() {
        let mut sat = IncrementalSat::new();
        // (x0 ∨ x1)
        sat.add_clause(CnfClause::new(vec![pos(0), pos(1)]))
            .unwrap();
        let SatResult::Sat(first) = sat.solve(None).unwrap() else {
            panic!("expected sat after first clause");
        };
        assert!(first.values()[0] || first.values()[1]);

        // Add (¬x0); the warm solver keeps the earlier clause, so x1 is forced.
        sat.add_clause(CnfClause::new(vec![neg(0)])).unwrap();
        let SatResult::Sat(second) = sat.solve(None).unwrap() else {
            panic!("expected sat after second clause");
        };
        assert!(!second.values()[0], "x0 is forced false");
        assert!(
            second.values()[1],
            "x1 is forced true by the retained clause"
        );
    }

    #[test]
    fn incremental_assumptions_hold_for_one_solve_only() {
        let mut sat = IncrementalSat::new();
        sat.add_clause(CnfClause::new(vec![pos(0), pos(1)]))
            .unwrap();

        // Assuming both literals false contradicts the clause: unsat this solve.
        assert!(matches!(
            sat.solve_assuming(&[neg(0), neg(1)], None).unwrap(),
            SatResult::Unsat(_)
        ));
        // Without the assumptions the formula is satisfiable again.
        assert!(matches!(sat.solve(None).unwrap(), SatResult::Sat(_)));
    }

    #[test]
    fn incremental_formula_snapshot_materializes_the_same_active_problem() {
        let mut cnf = IncrementalCnf::new();
        let selector = cnf.fresh_selector().unwrap();
        let input = cnf.fresh_selector().unwrap();
        cnf.sat
            .add_clause(CnfClause::new(vec![
                CnfLit::positive(selector).negated(),
                CnfLit::positive(input),
            ]))
            .unwrap();
        cnf.sat
            .add_clause(CnfClause::new(vec![CnfLit::positive(input).negated()]))
            .unwrap();

        let snapshot = cnf.formula_snapshot_assuming(&[selector]).unwrap();
        assert_eq!(snapshot.variable_count(), 2);
        assert_eq!(snapshot.clauses().len(), 3);
        assert!(matches!(
            solve_with_rustsat_batsat(&snapshot).unwrap(),
            SatResult::Unsat(_)
        ));
    }

    #[test]
    fn incremental_solver_is_send_and_timeout_state_is_per_solve() {
        fn assert_send<T: Send>() {}
        assert_send::<IncrementalSat>();

        let mut sat = IncrementalSat::new();
        sat.add_clause(CnfClause::new(vec![pos(0), pos(1)]))
            .unwrap();
        assert!(matches!(
            sat.solve(Some(std::time::Duration::ZERO)).unwrap(),
            SatResult::Unknown(_)
        ));
        assert!(
            matches!(sat.solve(None).unwrap(), SatResult::Sat(_)),
            "an untimed solve must clear the preceding deadline"
        );
    }

    #[test]
    fn incremental_timeout_can_continue_with_a_fresh_bounded_deadline() {
        let mut sat = IncrementalSat::new();
        sat.add_clause(CnfClause::new(vec![pos(0), pos(1)]))
            .unwrap();
        assert!(matches!(
            sat.solve(Some(std::time::Duration::ZERO)).unwrap(),
            SatResult::Unknown(_)
        ));
        assert!(
            matches!(
                sat.solve(Some(std::time::Duration::from_secs(1))).unwrap(),
                SatResult::Sat(_)
            ),
            "a fresh bounded solve must clear the preceding deadline and reuse the instance"
        );
    }

    #[test]
    fn incremental_resource_limit_is_deterministic_and_reset_per_solve() {
        let mut sat = IncrementalSat::new();
        sat.add_clause(CnfClause::new(vec![pos(0), pos(1)]))
            .unwrap();

        for _ in 0..2 {
            assert!(matches!(
                sat.solve_with_limits(None, Some(0)).unwrap(),
                SatResult::Unknown(reason)
                    if reason.detail
                        == "rustsat-batsat deterministic progress-check budget 0 exhausted"
            ));
        }
        assert!(
            matches!(
                sat.solve_with_limits(None, Some(100)).unwrap(),
                SatResult::Sat(_)
            ),
            "a fresh larger work budget must clear the preceding exhausted limit"
        );
    }

    #[test]
    fn incremental_selector_literals_emulate_push_pop() {
        let mut sat = IncrementalSat::new();
        // Base assertion: x0 is true (unit clause).
        sat.add_clause(CnfClause::new(vec![pos(0)])).unwrap();
        // Scoped assertion guarded by selector x1: (¬x1 ∨ ¬x0), i.e. "if the
        // scope is active, x0 must be false" — contradicts the base.
        sat.add_clause(CnfClause::new(vec![neg(1), neg(0)]))
            .unwrap();

        // Scope active (assume x1): contradiction -> unsat.
        assert!(matches!(
            sat.solve_assuming(&[pos(1)], None).unwrap(),
            SatResult::Unsat(_)
        ));
        // Scope popped (assume ¬x1, deactivating the guarded clause): sat again.
        assert!(matches!(
            sat.solve_assuming(&[neg(1)], None).unwrap(),
            SatResult::Sat(_)
        ));
    }

    #[test]
    fn incremental_cnf_encodes_solves_and_lifts_node_values() {
        let mut aig = Aig::new();
        let p = aig.input("p");
        let q = aig.input("q");
        let conj = aig.and(p, q);

        let mut cnf = IncrementalCnf::new();
        cnf.assert_root(&aig, conj, None).unwrap();
        let SatResult::Sat(assignment) = cnf.solve(&[], None).unwrap() else {
            panic!("expected sat for `p & q`");
        };
        let node_values = cnf.aig_node_values(&aig, &assignment);
        assert!(aig_lit_value(conj, &node_values).unwrap(), "root holds");
        assert!(aig_lit_value(p, &node_values).unwrap(), "p forced true");
        assert!(aig_lit_value(q, &node_values).unwrap(), "q forced true");

        // Asserting the constant-false literal is unsatisfiable, matching the
        // one-shot path's verdict on the same circuit.
        let mut contradiction = IncrementalCnf::new();
        contradiction
            .assert_root(&aig, AigLit::FALSE, None)
            .unwrap();
        assert!(matches!(
            contradiction.solve(&[], None).unwrap(),
            SatResult::Unsat(_)
        ));
    }

    #[test]
    fn incremental_cnf_profile_partitions_halves_and_direct_root_opportunities() {
        let mut aig = Aig::new();
        let a = aig.input("a");
        let b = aig.input("b");
        let c = aig.input("c");
        let d = aig.input("d");
        let ab = aig.and(a, b);
        let cd = aig.and(c, d);
        let root = aig.and(ab, cd);

        let mut cnf = IncrementalCnf::with_profiling();
        let before = cnf.stats();
        cnf.assert_root(&aig, root, None).unwrap();
        let stats = cnf.stats().delta_since(before);

        assert_eq!(stats.and_nodes_synced, 3);
        assert_eq!(stats.up_half_definitions, 0);
        assert_eq!(stats.down_half_definitions, 0);
        assert_eq!(stats.and_tree_half_definitions, 0);
        assert_eq!(stats.binary_and_half_definitions, 0);
        assert_eq!(stats.xor_half_definitions, 0);
        assert_eq!(stats.not_ite_half_definitions, 0);
        assert_eq!(stats.not_and_half_definitions, 0);
        assert_eq!(stats.constant_clauses, 1);
        assert_eq!(stats.definition_clauses, 0);
        assert_eq!(stats.root_clauses, 4);
        assert_eq!(stats.direct_positive_and_roots, 1);
        assert_eq!(stats.direct_positive_and_nodes, 3);
        assert_eq!(stats.direct_positive_and_leaves, 4);
        assert_eq!(stats.direct_negative_and_roots, 0);
        assert_eq!(stats.fused_positive_and_roots, 1);
        assert_eq!(stats.fused_positive_and_nodes, 3);
        assert_eq!(stats.fused_xor_leaves, 0);
        assert_eq!(stats.root_assertions, 1);
        assert_eq!(stats.guarded_root_assertions, 0);
        assert_eq!(stats.repeated_same_context_roots, 0);
        assert_eq!(stats.deduplicated_root_assertions, 0);
        assert_eq!(stats.reused_cross_context_roots, 0);
        assert_eq!(stats.root_clause_attempts, 4);
        assert_eq!(stats.unit_payload_root_clauses, 4);
        assert_eq!(stats.binary_payload_root_clauses, 0);
        assert_eq!(stats.wide_payload_root_clauses, 0);
        assert_eq!(stats.duplicate_definition_clauses, 0);
        assert_eq!(stats.duplicate_root_clauses, 0);
        assert_eq!(stats.duplicate_prior_root_clauses, 0);
        assert_eq!(stats.root_clauses_duplicate_non_root, 0);
        assert_eq!(
            stats.xor_half_definitions
                + stats.not_ite_half_definitions
                + stats.not_and_half_definitions
                + stats.and_tree_half_definitions
                + stats.binary_and_half_definitions,
            stats.up_half_definitions + stats.down_half_definitions
        );
        assert_eq!(
            stats.constant_clauses + stats.definition_clauses + stats.root_clauses,
            u64::try_from(cnf.clause_count()).unwrap()
        );

        let before_negative = cnf.stats();
        cnf.assert_root(&aig, root.negated(), None).unwrap();
        let negative = cnf.stats().delta_since(before_negative);
        assert_eq!(negative.down_half_definitions, 3);
        assert_eq!(negative.and_tree_half_definitions, 1);
        assert_eq!(negative.binary_and_half_definitions, 2);
        assert_eq!(negative.definition_clauses, 3);
        assert_eq!(negative.root_clauses, 1);
        assert_eq!(negative.direct_negative_and_roots, 1);
        assert_eq!(negative.fresh_negative_root_definitions, 1);
        assert_eq!(negative.reused_negative_root_definitions, 0);
    }

    #[test]
    fn incremental_cnf_profile_finds_direct_parity_leaf_without_flattening_it() {
        let mut aig = Aig::new();
        let a = aig.input("a");
        let b = aig.input("b");
        let xnor = xor_lit(&mut aig, a, b).negated();
        let mut cnf = IncrementalCnf::with_profiling();

        cnf.assert_root(&aig, xnor, None).unwrap();
        let stats = cnf.stats();

        assert_eq!(stats.direct_positive_and_roots, 1);
        assert_eq!(stats.direct_positive_and_nodes, 0);
        assert_eq!(stats.direct_positive_and_leaves, 1);
        assert_eq!(stats.direct_xor_leaves, 1);
        assert_eq!(stats.direct_not_ite_leaves, 0);
        assert_eq!(stats.xor_half_definitions, 0);
        assert_eq!(stats.definition_clauses, 0);
        assert_eq!(stats.root_clauses, 2);
        assert_eq!(stats.fused_positive_and_roots, 1);
        assert_eq!(stats.fused_positive_and_nodes, 0);
        assert_eq!(stats.fused_xor_leaves, 1);
    }

    #[test]
    fn incremental_cnf_direct_positive_tree_reduces_clauses() {
        let mut aig = Aig::new();
        let a = aig.input("a");
        let b = aig.input("b");
        let c = aig.input("c");
        let d = aig.input("d");
        let ab = aig.and(a, b);
        let cd = aig.and(c, d);
        let root = aig.and(ab, cd);
        let mut cnf = IncrementalCnf::new();

        cnf.assert_root(&aig, root, None).unwrap();

        // One constant clause plus one direct assertion per unique leaf. The
        // primitive incremental encoding used seven non-constant clauses here.
        assert_eq!(cnf.clause_count(), 5);
        assert!(matches!(cnf.solve(&[], None).unwrap(), SatResult::Sat(_)));
    }

    fn internal_positive_and_case() -> (Aig, AigLit, AigLit, Vec<AigLit>) {
        let mut aig = Aig::new();
        let input_a = aig.input("a");
        let input_b = aig.input("b");
        let input_c = aig.input("c");
        let input_d = aig.input("d");
        let input_e = aig.input("e");
        let pair_ab = aig.and(input_a, input_b);
        let pair_cd = aig.and(input_c, input_d);
        let tree = aig.and(pair_ab, pair_cd);
        // `tree | !e`: the negated AND root requires `tree` positively, but
        // does not enter the direct-positive-root assertion path.
        let root = aig.and(tree.negated(), input_e).negated();
        (
            aig,
            root,
            tree,
            vec![input_a, input_b, input_c, input_d, input_e],
        )
    }

    #[test]
    fn incremental_internal_positive_and_flattening_reduces_clauses() {
        let (aig, root, _, _) = internal_positive_and_case();
        let mut baseline = IncrementalCnf::new();
        baseline.assert_root(&aig, root, None).unwrap();
        let mut candidate = IncrementalCnf::with_internal_positive_and_flattening();
        candidate.assert_root(&aig, root, None).unwrap();

        assert_eq!(baseline.clause_count(), 9);
        assert_eq!(candidate.clause_count(), 7);
        assert!(matches!(
            candidate.solve(&[], None).unwrap(),
            SatResult::Sat(_)
        ));
    }

    #[test]
    fn incremental_internal_positive_and_profile_is_causal() {
        let (aig, root, _, _) = internal_positive_and_case();
        let mut baseline = IncrementalCnf::with_profiling();
        baseline.assert_root(&aig, root, None).unwrap();
        let baseline_stats = baseline.stats();
        assert_eq!(baseline_stats.internal_positive_and_opportunities, 1);
        assert_eq!(baseline_stats.internal_positive_and_opportunity_nodes, 3);
        assert_eq!(baseline_stats.internal_positive_and_flattened, 0);
        assert_eq!(
            baseline_stats.internal_positive_and_immediate_clauses_avoided,
            0
        );

        let mut candidate = IncrementalCnf::with_profiling_and_internal_positive_and_flattening();
        candidate.assert_root(&aig, root, None).unwrap();
        let stats = candidate.stats();
        assert_eq!(stats.internal_positive_and_opportunities, 1);
        assert_eq!(stats.internal_positive_and_opportunity_nodes, 3);
        assert_eq!(stats.internal_positive_and_flattened, 1);
        assert_eq!(stats.internal_positive_and_immediate_clauses_avoided, 2);
        assert_eq!(stats.up_half_definitions, 0);
        assert_eq!(stats.down_half_definitions, 1);
        assert_eq!(stats.definition_clauses, 5);
    }

    #[test]
    fn incremental_internal_positive_and_flattening_matches_every_input() {
        let (aig, root, _, inputs) = internal_positive_and_case();
        for mask in 0u32..(1 << inputs.len()) {
            let values = (0..inputs.len())
                .map(|bit| (mask >> bit) & 1 == 1)
                .collect::<Vec<_>>();
            let expected = aig.eval(root, &values).unwrap();
            let mut cnf = IncrementalCnf::with_internal_positive_and_flattening();
            cnf.assert_root(&aig, root, None).unwrap();
            for (bit, input) in inputs.iter().copied().enumerate() {
                let literal = if values[bit] { input } else { input.negated() };
                cnf.assert_root(&aig, literal, None).unwrap();
            }
            let actual = matches!(cnf.solve(&[], None).unwrap(), SatResult::Sat(_));
            assert_eq!(actual, expected, "input mask {mask:#07b}");
        }
    }

    #[test]
    fn incremental_internal_positive_and_remains_sound_under_later_reuse() {
        let (aig, root, tree, inputs) = internal_positive_and_case();
        let e = inputs[4];
        let mut cnf = IncrementalCnf::with_internal_positive_and_flattening();
        cnf.assert_root(&aig, root, None).unwrap();
        // Reusing the bypassed tree negatively must emit its ordinary down
        // half rather than trusting an underconstrained helper variable.
        cnf.assert_root(&aig, tree.negated(), None).unwrap();
        let selector = cnf.fresh_selector().unwrap();
        cnf.assert_root(&aig, e, Some(selector)).unwrap();

        assert!(matches!(cnf.solve(&[], None).unwrap(), SatResult::Sat(_)));
        assert!(matches!(
            cnf.solve(&[selector], None).unwrap(),
            SatResult::Unsat(_)
        ));
    }

    #[test]
    fn incremental_cnf_direct_root_remains_sound_under_opposite_reuse() {
        let mut aig = Aig::new();
        let a = aig.input("a");
        let b = aig.input("b");
        let root = aig.and(a, b);
        let mut cnf = IncrementalCnf::new();
        let selector = cnf.fresh_selector().unwrap();

        // The positive root is direct and scoped. Its ordinary node definition
        // must remain available when the opposite polarity is added later.
        cnf.assert_root(&aig, root, Some(selector)).unwrap();
        cnf.assert_root(&aig, root.negated(), None).unwrap();

        assert!(matches!(
            cnf.solve(&[selector], None).unwrap(),
            SatResult::Unsat(_)
        ));
        assert!(matches!(cnf.solve(&[], None).unwrap(), SatResult::Sat(_)));
    }

    #[test]
    fn incremental_cnf_direct_xnor_clauses_are_scope_guarded() {
        let mut aig = Aig::new();
        let a = aig.input("a");
        let b = aig.input("b");
        let xnor = xor_lit(&mut aig, a, b).negated();
        let mut cnf = IncrementalCnf::new();
        let selector = cnf.fresh_selector().unwrap();

        cnf.assert_root(&aig, xnor, Some(selector)).unwrap();
        cnf.assert_root(&aig, a, None).unwrap();
        cnf.assert_root(&aig, b.negated(), None).unwrap();

        assert!(matches!(
            cnf.solve(&[selector], None).unwrap(),
            SatResult::Unsat(_)
        ));
        assert!(matches!(cnf.solve(&[], None).unwrap(), SatResult::Sat(_)));
    }

    #[test]
    fn incremental_cnf_profile_attributes_same_context_root_duplicates() {
        let mut aig = Aig::new();
        let a = aig.input("a");
        let b = aig.input("b");
        let root = aig.and(a, b);
        let mut cnf = IncrementalCnf::with_profiling();

        cnf.assert_root(&aig, root, None).unwrap();
        cnf.assert_root(&aig, root, None).unwrap();
        let stats = cnf.stats();

        assert_eq!(stats.root_assertions, 2);
        assert_eq!(stats.repeated_same_context_roots, 1);
        assert_eq!(stats.deduplicated_root_assertions, 1);
        assert_eq!(stats.reused_cross_context_roots, 0);
        assert_eq!(stats.root_clause_attempts, 2);
        assert_eq!(stats.root_clauses, 2);
        assert_eq!(stats.duplicate_root_clauses, 0);
        assert_eq!(stats.duplicate_prior_root_clauses, 0);
        assert_eq!(stats.root_clauses_duplicate_non_root, 0);
        assert_eq!(stats.duplicate_definition_clauses, 0);
        assert_eq!(stats.tautological_root_clauses, 0);
        assert_eq!(stats.unit_payload_root_clauses, 2);
    }

    #[test]
    fn incremental_cnf_profile_keeps_cross_scope_roots_distinct() {
        let mut aig = Aig::new();
        let a = aig.input("a");
        let b = aig.input("b");
        let root = aig.and(a, b);
        let mut cnf = IncrementalCnf::with_profiling();
        let first = cnf.fresh_selector().unwrap();
        let second = cnf.fresh_selector().unwrap();

        cnf.assert_root(&aig, root, Some(first)).unwrap();
        cnf.assert_root(&aig, root, Some(second)).unwrap();
        let stats = cnf.stats();

        assert_eq!(stats.root_assertions, 2);
        assert_eq!(stats.guarded_root_assertions, 2);
        assert_eq!(stats.repeated_same_context_roots, 0);
        assert_eq!(stats.deduplicated_root_assertions, 0);
        assert_eq!(stats.reused_cross_context_roots, 1);
        assert_eq!(stats.guarded_root_clauses, 4);
        assert_eq!(stats.root_clause_attempts, 4);
        assert_eq!(stats.root_clauses, 4);
        assert_eq!(stats.duplicate_root_clauses, 0);
    }

    #[test]
    fn incremental_cnf_profile_separates_fresh_and_reused_negative_roots() {
        let mut aig = Aig::new();
        let a = aig.input("a");
        let b = aig.input("b");
        let root = aig.and(a, b).negated();
        let mut cnf = IncrementalCnf::with_profiling();

        cnf.assert_root(&aig, root, None).unwrap();
        cnf.assert_root(&aig, root, None).unwrap();
        let stats = cnf.stats();

        assert_eq!(stats.direct_negative_and_roots, 2);
        assert_eq!(stats.fresh_negative_root_definitions, 1);
        assert_eq!(stats.reused_negative_root_definitions, 1);
        assert_eq!(stats.definition_clauses, 1);
        assert_eq!(stats.root_clause_attempts, 1);
        assert_eq!(stats.root_clauses, 1);
        assert_eq!(stats.duplicate_root_clauses, 0);
        assert_eq!(stats.duplicate_prior_root_clauses, 0);
        assert_eq!(stats.root_clauses_duplicate_non_root, 0);
        assert_eq!(stats.repeated_same_context_roots, 1);
        assert_eq!(stats.deduplicated_root_assertions, 1);
    }

    #[test]
    fn incremental_cnf_ordinary_constructor_keeps_profile_counters_zero() {
        let mut aig = Aig::new();
        let a = aig.input("a");
        let b = aig.input("b");
        let root = aig.and(a, b);
        let mut cnf = IncrementalCnf::new();

        cnf.assert_root(&aig, root, None).unwrap();

        assert_eq!(cnf.stats(), IncrementalCnfStats::default());
    }

    #[test]
    fn incremental_cnf_selector_scopes_toggle_assertions() {
        let mut aig = Aig::new();
        let p = aig.input("p");

        let mut cnf = IncrementalCnf::new();
        // Base scope: p must be true (permanent).
        cnf.assert_root(&aig, p, None).unwrap();
        // Nested scope: if its selector is active, ¬p — contradicting the base.
        let selector = cnf.fresh_selector().unwrap();
        cnf.assert_root(&aig, p.negated(), Some(selector)).unwrap();

        // Scope active -> contradiction -> unsat.
        assert!(matches!(
            cnf.solve(&[selector], None).unwrap(),
            SatResult::Unsat(_)
        ));
        // Scope popped (selector not assumed) -> satisfiable again.
        assert!(matches!(cnf.solve(&[], None).unwrap(), SatResult::Sat(_)));
    }

    #[test]
    fn incremental_cnf_deduplicates_only_within_one_selector_context() {
        let mut aig = Aig::new();
        let p = aig.input("p");

        let mut cnf = IncrementalCnf::new();
        let selector = cnf.fresh_selector().unwrap();
        cnf.assert_root(&aig, p.negated(), Some(selector)).unwrap();
        let clauses_after_first_assertion = cnf.clause_count();

        // The SAT database retains the first guarded clause, so repeating the
        // same root in the same scope must not install it again.
        cnf.assert_root(&aig, p.negated(), Some(selector)).unwrap();
        assert_eq!(cnf.clause_count(), clauses_after_first_assertion);

        // A permanent assertion is a different context and remains distinct.
        cnf.assert_root(&aig, p, None).unwrap();
        assert!(matches!(
            cnf.solve(&[selector], None).unwrap(),
            SatResult::Unsat(_)
        ));
        assert!(matches!(cnf.solve(&[], None).unwrap(), SatResult::Sat(_)));
    }

    #[test]
    fn incremental_permanent_contradiction_stays_unsat() {
        let mut sat = IncrementalSat::new();
        sat.add_clause(CnfClause::new(vec![pos(0)])).unwrap();
        sat.add_clause(CnfClause::new(vec![neg(0)])).unwrap();
        assert!(matches!(sat.solve(None).unwrap(), SatResult::Unsat(_)));
        // Still unsat on a later solve; the contradiction is permanent.
        assert!(matches!(sat.solve(None).unwrap(), SatResult::Unsat(_)));
        assert_eq!(sat.clause_count(), 2);
        assert_eq!(sat.variable_count(), 1);
    }

    /// `xor(a, b)` built from ANDs and inversion: ¬(¬(a & ¬b) & ¬(¬a & b)).
    fn xor_lit(aig: &mut Aig, a: AigLit, b: AigLit) -> AigLit {
        let only_a = aig.and(a, b.negated());
        let only_b = aig.and(a.negated(), b);
        aig.and(only_a.negated(), only_b.negated()).negated()
    }

    /// A spread of small combinational circuits, each as `(aig, root)`.
    fn pg_differential_cases() -> Vec<(Aig, AigLit)> {
        let mut cases = Vec::new();

        // Positive AND chain (single-polarity throughout).
        {
            let mut aig = Aig::new();
            let mut acc = aig.input("x0");
            for i in 1..4 {
                let next = aig.input(format!("x{i}"));
                acc = aig.and(acc, next);
            }
            cases.push((aig, acc));
        }
        // OR of two ANDs (mixes polarity through De Morgan).
        {
            let mut aig = Aig::new();
            let a = aig.input("a");
            let b = aig.input("b");
            let c = aig.input("c");
            let d = aig.input("d");
            let ab = aig.and(a, b);
            let cd = aig.and(c, d);
            let or = aig.and(ab.negated(), cd.negated()).negated();
            cases.push((aig, or));
        }
        // XOR (both polarity halves of inner nodes are needed).
        {
            let mut aig = Aig::new();
            let a = aig.input("a");
            let b = aig.input("b");
            let root = xor_lit(&mut aig, a, b);
            cases.push((aig, root));
        }
        // Negated root over an AND (root used in negative polarity).
        {
            let mut aig = Aig::new();
            let a = aig.input("a");
            let b = aig.input("b");
            let ab = aig.and(a, b);
            cases.push((aig, ab.negated()));
        }
        // Contradiction: x XOR x is always false -> unsatisfiable.
        {
            let mut aig = Aig::new();
            let x = aig.input("x");
            let root = xor_lit(&mut aig, x, x);
            cases.push((aig, root));
        }
        // Tautology asserted: (a | ¬a) is always true -> satisfiable.
        {
            let mut aig = Aig::new();
            let a = aig.input("a");
            let root = aig.and(a.negated(), a).negated();
            cases.push((aig, root));
        }
        cases
    }

    #[test]
    fn incremental_pg_agrees_with_brute_force_and_one_shot() {
        // The lazy Plaisted–Greenbaum incremental encoder must reach the same
        // verdict as (1) exhaustive AIG evaluation and (2) the one-shot
        // `tseitin_encode` path, and any SAT model it lifts must satisfy the
        // asserted root. This is the soundness check for the polarity encoding.
        for (case, (aig, root)) in pg_differential_cases().iter().enumerate() {
            let k = aig.input_count();
            let brute_sat = (0u32..(1u32 << k)).any(|mask| {
                let inputs = (0..k).map(|bit| (mask >> bit) & 1 == 1).collect::<Vec<_>>();
                aig.eval(*root, &inputs).expect("eval")
            });

            let one_shot = solve_with_rustsat_batsat(
                tseitin_encode(aig, &[*root])
                    .expect("one-shot encode")
                    .formula(),
            )
            .expect("one-shot solve");
            let one_shot_sat = matches!(one_shot, SatResult::Sat(_));
            assert_eq!(
                one_shot_sat, brute_sat,
                "case {case}: one-shot disagrees with brute force"
            );

            let mut cnf = IncrementalCnf::new();
            cnf.assert_root(aig, *root, None).expect("assert root");
            match cnf.solve(&[], None).expect("incremental solve") {
                SatResult::Sat(assignment) => {
                    assert!(
                        brute_sat,
                        "case {case}: incremental SAT but brute force UNSAT"
                    );
                    let node_values = cnf.aig_node_values(aig, &assignment);
                    assert!(
                        aig_lit_value(*root, &node_values).expect("lift"),
                        "case {case}: lifted model must satisfy the root"
                    );
                }
                SatResult::Unsat(_) => {
                    assert!(
                        !brute_sat,
                        "case {case}: incremental UNSAT but brute force SAT"
                    );
                }
                other @ SatResult::Unknown(_) => panic!("case {case}: unexpected {other:?}"),
            }
        }
    }

    #[test]
    fn incremental_direct_root_emits_fewer_clauses_than_full_tseitin() {
        // A positive AND chain is asserted as one clause per unique leaf. No
        // gate definition is needed unless a later assertion reuses a bypassed
        // node in another polarity.
        let mut aig = Aig::new();
        let mut acc = aig.input("x0");
        let n_ands = 8usize;
        for i in 1..=n_ands {
            let next = aig.input(format!("x{i}"));
            acc = aig.and(acc, next);
        }
        let mut cnf = IncrementalCnf::new();
        cnf.assert_root(&aig, acc, None).expect("assert root");

        // 1 const-false unit + one clause for each of n_ands + 1 inputs.
        let direct = cnf.clause_count();
        assert_eq!(direct, 1 + n_ands + 1);
        // Full both-polarity Tseitin would emit three clauses per AND.
        let full_tseitin = 1 + 3 * n_ands + 1;
        assert!(
            direct < full_tseitin,
            "direct root {direct} should beat full Tseitin {full_tseitin}"
        );
        assert!(matches!(
            cnf.solve(&[], None).expect("solve"),
            SatResult::Sat(_)
        ));
    }
}
