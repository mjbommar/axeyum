//! CNF layer for Axeyum.
//!
//! This crate owns the first Phase 4 CNF contract: simple Tseitin encoding
//! from AIG, DIMACS parsing/writing, CNF evaluation, and lift maps from CNF
//! variables back to AIG literals. It also owns the first pure-Rust SAT adapter
//! path for CNF formulas.

use axeyum_aig::{Aig, AigLit, AigNode, AigNodeId};
use std::collections::BTreeSet;
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
pub use proof_sat::{ProofSolveOutcome, solve_with_drat_proof, solve_with_drat_proof_within};
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
    clauses: Vec<CnfClause>,
}

impl CnfFormula {
    /// Creates an empty formula over `variable_count` variables.
    pub fn new(variable_count: usize) -> Self {
        Self {
            variable_count,
            clauses: Vec::new(),
        }
    }

    /// Number of variables.
    pub fn variable_count(&self) -> usize {
        self.variable_count
    }

    /// Formula clauses.
    pub fn clauses(&self) -> &[CnfClause] {
        &self.clauses
    }

    /// Adds one clause.
    ///
    /// # Errors
    ///
    /// Returns [`CnfError::InvalidVariable`] if a literal references a variable
    /// outside this formula.
    pub fn add_clause(&mut self, clause: CnfClause) -> Result<(), CnfError> {
        for lit in clause.lits() {
            self.check_var(lit.var())?;
        }
        self.clauses.push(clause);
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
            .clauses
            .iter()
            .all(|clause| clause.evaluate(assignment)))
    }

    /// Renders this formula as DIMACS CNF.
    pub fn to_dimacs(&self) -> String {
        let mut out = format!("p cnf {} {}\n", self.variable_count, self.clauses.len());
        for clause in &self.clauses {
            for lit in clause.lits() {
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
    let mut solver = rustsat_batsat::BasicSolver::default();
    let timeout_deadline = timeout.and_then(|duration| Instant::now().checked_add(duration));
    if let Some(deadline) = timeout_deadline {
        solver
            .batsat_mut()
            .cb_mut()
            .set_stop(move || Instant::now() >= deadline);
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
            let detail = if timeout_deadline.is_some() {
                "rustsat-batsat timeout".to_owned()
            } else {
                "rustsat-batsat interrupted".to_owned()
            };
            Ok(SatResult::Unknown(SatUnknownReason { detail }))
        }
    }
}

#[derive(Default)]
struct DeadlineCallbacks {
    deadline: Option<Instant>,
}

impl batsat::Callbacks for DeadlineCallbacks {
    fn stop(&self) -> bool {
        self.deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
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
            .add_clause(rustsat_clause(&clause)?)
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
        self.solve_inner(&[], timeout)
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
        self.solve_inner(assumptions, timeout)
    }

    fn solve_inner(
        &mut self,
        assumptions: &[CnfLit],
        timeout: Option<Duration>,
    ) -> Result<SatResult, SatError> {
        let timeout_deadline = timeout.and_then(|duration| Instant::now().checked_add(duration));
        // Store the deadline as data instead of BatSat's `Box<dyn Fn()>`. The
        // latter is not `Send`; an `Instant` is, so a warm solver can move to a
        // worker thread without unsafe code or a shared global context.
        self.solver.batsat_mut().cb_mut().deadline = timeout_deadline;

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
                let detail = if timeout_deadline.is_some() {
                    "rustsat-batsat timeout".to_owned()
                } else {
                    "rustsat-batsat interrupted".to_owned()
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
/// The gate-fusion optimizations of [`tseitin_encode`] (XOR/mux/and-tree
/// detection) are deliberately *not* ported: they rely on global single-use
/// counts that are not stable as the AIG grows, so they are not sound to apply
/// incrementally.
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
}

impl IncrementalCnf {
    /// Creates an empty incremental encoder.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of CNF variables allocated so far (nodes plus selectors).
    pub fn variable_count(&self) -> usize {
        self.next_var
    }

    /// Number of clauses in the persistent database.
    pub fn clause_count(&self) -> usize {
        self.sat.clause_count()
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
                    self.sat
                        .add_clause(CnfClause::new(vec![CnfLit::positive(var).negated()]))?;
                    None
                }
                AigNode::Input(_) => {
                    // A free variable; no defining clause.
                    None
                }
                // Defer the `var <-> (lhs & rhs)` clauses to `require`, which
                // emits only the polarity halves that are actually used.
                AigNode::And(lhs, rhs) => Some((lhs, rhs)),
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

    /// Lazily emits the Plaisted–Greenbaum half-definitions needed so that an
    /// occurrence of AIG node `start` in polarity `want_up` is sound.
    ///
    /// `want_up == true` means node `start` occurs positively (`+v`), which needs
    /// the `v -> (lhs & rhs)` implication; `false` means it occurs negatively
    /// (`¬v`), needing `(lhs & rhs) -> v`. Emitting a half introduces child
    /// occurrences whose polarities are propagated recursively. Each
    /// `(node, direction)` is emitted at most once, so the propagation is finite
    /// and monotone. An explicit work-stack avoids deep recursion on tall AIGs.
    fn require(&mut self, start: usize, want_up: bool) -> Result<(), SatError> {
        let mut stack = vec![(start, want_up)];
        while let Some((idx, up)) = stack.pop() {
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
                self.emitted_up[idx] = true;
                // v -> (lhs & rhs): (¬v ∨ lhs)(¬v ∨ rhs).
                self.sat
                    .add_clause(CnfClause::new(vec![var.negated(), lhs_lit]))?;
                self.sat
                    .add_clause(CnfClause::new(vec![var.negated(), rhs_lit]))?;
                // Children occur with their own literal polarity: positive
                // occurrence needs `up`, negated occurrence needs `down`.
                stack.push((lhs.node().index(), !lhs.is_inverted()));
                stack.push((rhs.node().index(), !rhs.is_inverted()));
            } else {
                if self.emitted_down[idx] {
                    continue;
                }
                self.emitted_down[idx] = true;
                // (lhs & rhs) -> v: (v ∨ ¬lhs ∨ ¬rhs).
                self.sat.add_clause(CnfClause::new(vec![
                    var,
                    lhs_lit.negated(),
                    rhs_lit.negated(),
                ]))?;
                // Children appear negated here, flipping the required polarity:
                // a non-inverted child occurs negatively (needs `down`); an
                // inverted child occurs positively (needs `up`).
                stack.push((lhs.node().index(), lhs.is_inverted()));
                stack.push((rhs.node().index(), rhs.is_inverted()));
            }
        }
        Ok(())
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
        // The asserted clause contains `root` positively, so the root node
        // occurs positively iff it is not inverted: emit that polarity half.
        self.require(root.node().index(), !root.is_inverted())?;
        let root_lit = self.lit(root);
        let clause = match selector {
            None => CnfClause::new(vec![root_lit]),
            Some(sel) => CnfClause::new(vec![CnfLit::positive(sel).negated(), root_lit]),
        };
        self.sat.add_clause(clause)
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
        if active_selectors.is_empty() {
            self.sat.solve(timeout)
        } else {
            let assumptions = active_selectors
                .iter()
                .map(|&var| CnfLit::positive(var))
                .collect::<Vec<_>>();
            self.sat.solve_assuming(&assumptions, timeout)
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

/// Result of Tseitin encoding AIG roots.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CnfEncoding {
    formula: CnfFormula,
    roots: Vec<CnfRoot>,
    reachable_nodes: Vec<bool>,
    variable_bindings: Vec<CnfVarBinding>,
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

/// Parses a DIMACS CNF string.
///
/// # Errors
///
/// Returns [`CnfError`] if the input is malformed or references variables
/// outside the declared problem line.
pub fn parse_dimacs(input: &str) -> Result<CnfFormula, CnfError> {
    let mut variable_count = None;
    let mut expected_clauses = None;
    let mut clauses = Vec::new();
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
            variable_count = Some(parse_usize(parts[2])?);
            expected_clauses = Some(parse_usize(parts[3])?);
            continue;
        }

        let count = variable_count.ok_or(CnfError::MissingProblemLine)?;
        for token in trimmed.split_whitespace() {
            let value = parse_dimacs_lit_token(token)?;
            if value == 0 {
                clauses.push(CnfClause::new(std::mem::take(&mut current_clause)));
            } else {
                current_clause.push(lit_from_dimacs(value, count)?);
            }
        }
    }

    let variable_count = variable_count.ok_or(CnfError::MissingProblemLine)?;
    let expected_clauses = expected_clauses.ok_or(CnfError::MissingProblemLine)?;
    if !current_clause.is_empty() {
        return Err(CnfError::MissingClauseTerminator);
    }
    if clauses.len() != expected_clauses {
        return Err(CnfError::ClauseCountMismatch {
            expected: expected_clauses,
            found: clauses.len(),
        });
    }
    Ok(CnfFormula {
        variable_count,
        clauses,
    })
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

struct TseitinEncoder<'a> {
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
    clause_keys: BTreeSet<Vec<CnfLit>>,
    variable_bindings: Vec<CnfVarBinding>,
}

impl<'a> TseitinEncoder<'a> {
    fn new(aig: &'a Aig) -> Self {
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
            clause_keys: BTreeSet::new(),
            variable_bindings: Vec::new(),
        }
    }

    fn encode(mut self, roots: &[AigLit]) -> Result<CnfEncoding, CnfError> {
        self.plan_sparse_encoding(roots);
        self.allocate_variables();
        self.encode_gates()?;
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
        Ok(CnfEncoding {
            formula: self.formula,
            roots,
            reachable_nodes: self.reachable_nodes,
            variable_bindings: self.variable_bindings,
        })
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
            let (encode_forward, encode_reverse) = self.clause_directions(node_id);
            if let Some(xor_gate) = self.xor_gates[node_id.index()] {
                self.encode_xor_gate(out, xor_gate, encode_forward, encode_reverse)?;
                continue;
            }
            if let Some(not_ite_gate) = self.not_ite_gates[node_id.index()] {
                self.encode_not_ite_gate(out, not_ite_gate, encode_forward, encode_reverse)?;
                continue;
            }
            if let Some(not_and_gate) = self.not_and_gates[node_id.index()].clone() {
                self.encode_not_and_gate(out, &not_and_gate, encode_forward, encode_reverse)?;
                continue;
            }
            if let Some(and_tree_gate) = self.and_tree_gates[node_id.index()].clone() {
                self.encode_and_tree_gate(out, &and_tree_gate, encode_forward, encode_reverse)?;
                continue;
            }
            self.encode_binary_and_gate(out, lhs, rhs, encode_forward, encode_reverse)?;
        }
        Ok(())
    }

    fn encode_xor_gate(
        &mut self,
        out: EncodedLit,
        gate: XorGate,
        encode_forward: bool,
        encode_reverse: bool,
    ) -> Result<(), CnfError> {
        let lhs = self.encode_lit(gate.lhs);
        let rhs = self.encode_lit(gate.rhs);
        if encode_forward {
            self.add_encoded_clause(&[out.negated(), lhs, rhs])?;
            self.add_encoded_clause(&[out.negated(), lhs.negated(), rhs.negated()])?;
        }
        if encode_reverse {
            self.add_encoded_clause(&[out, lhs.negated(), rhs])?;
            self.add_encoded_clause(&[out, lhs, rhs.negated()])?;
        }
        Ok(())
    }

    fn encode_not_ite_gate(
        &mut self,
        out: EncodedLit,
        gate: NotIteGate,
        encode_forward: bool,
        encode_reverse: bool,
    ) -> Result<(), CnfError> {
        let condition = self.encode_lit(gate.condition);
        let then_lit = self.encode_lit(gate.then_lit);
        let else_lit = self.encode_lit(gate.else_lit);
        if encode_forward {
            self.add_encoded_clause(&[out.negated(), condition.negated(), then_lit.negated()])?;
            self.add_encoded_clause(&[out.negated(), condition, else_lit.negated()])?;
        }
        if encode_reverse {
            self.add_encoded_clause(&[out, condition.negated(), then_lit])?;
            self.add_encoded_clause(&[out, condition, else_lit])?;
        }
        Ok(())
    }

    fn encode_not_and_gate(
        &mut self,
        out: EncodedLit,
        gate: &NotAndGate,
        encode_forward: bool,
        encode_reverse: bool,
    ) -> Result<(), CnfError> {
        if encode_forward {
            for factor in &gate.factors {
                let mut clause = vec![out.negated()];
                match factor {
                    AndFactor::Lit(lit) => clause.push(self.encode_lit(*lit)),
                    AndFactor::NotAnd(lhs, rhs) => {
                        clause.push(self.encode_lit(*lhs).negated());
                        clause.push(self.encode_lit(*rhs).negated());
                    }
                }
                self.add_encoded_clause(&clause)?;
            }
        }

        if encode_reverse {
            for clause in self.not_and_reverse_clauses(out, &gate.factors) {
                self.add_encoded_clause(&clause)?;
            }
        }
        Ok(())
    }

    fn not_and_reverse_clauses(
        &self,
        out: EncodedLit,
        factors: &[AndFactor; 2],
    ) -> Vec<Vec<EncodedLit>> {
        let mut reverse_clauses = vec![vec![out]];
        for factor in factors {
            match factor {
                AndFactor::Lit(lit) => {
                    let lit = self.encode_lit(*lit).negated();
                    for clause in &mut reverse_clauses {
                        clause.push(lit);
                    }
                }
                AndFactor::NotAnd(lhs, rhs) => {
                    let lhs = self.encode_lit(*lhs);
                    let rhs = self.encode_lit(*rhs);
                    let mut expanded = Vec::with_capacity(reverse_clauses.len() * 2);
                    for clause in reverse_clauses {
                        let mut lhs_clause = clause.clone();
                        lhs_clause.push(lhs);
                        expanded.push(lhs_clause);
                        let mut rhs_clause = clause;
                        rhs_clause.push(rhs);
                        expanded.push(rhs_clause);
                    }
                    reverse_clauses = expanded;
                }
            }
        }
        reverse_clauses
    }

    fn encode_and_tree_gate(
        &mut self,
        out: EncodedLit,
        gate: &AndTreeGate,
        encode_forward: bool,
        encode_reverse: bool,
    ) -> Result<(), CnfError> {
        if encode_forward {
            for leaf in &gate.leaves {
                match leaf {
                    AndTreeLeaf::Lit(lit) => {
                        let lit = self.encode_lit(*lit);
                        self.add_encoded_clause(&[out.negated(), lit])?;
                    }
                    AndTreeLeaf::NotAnd { lhs, rhs } => {
                        let lhs = self.encode_lit(*lhs).negated();
                        let rhs = self.encode_lit(*rhs).negated();
                        self.add_encoded_clause(&[out.negated(), lhs, rhs])?;
                    }
                    AndTreeLeaf::Parity { lits, expected } => {
                        self.encode_parity_implication(out, lits, *expected)?;
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
            self.add_encoded_clause(&long_clause)?;
        }
        Ok(())
    }

    fn encode_parity_implication(
        &mut self,
        out: EncodedLit,
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
            self.add_encoded_clause(&clause)?;
        }
        Ok(())
    }

    fn encode_binary_and_gate(
        &mut self,
        out: EncodedLit,
        lhs: AigLit,
        rhs: AigLit,
        encode_forward: bool,
        encode_reverse: bool,
    ) -> Result<(), CnfError> {
        let lhs = self.encode_lit(lhs);
        let rhs = self.encode_lit(rhs);
        if encode_forward {
            self.add_encoded_clause(&[out.negated(), lhs])?;
            self.add_encoded_clause(&[out.negated(), rhs])?;
        }
        if encode_reverse {
            self.add_encoded_clause(&[out, lhs.negated(), rhs.negated()])?;
        }
        Ok(())
    }

    fn assert_root(&mut self, root: AigLit) -> Result<EncodedLit, CnfError> {
        if root.node().index() != 0 && self.direct_root_nodes[root.node().index()] {
            self.assert_direct_root(root)?;
            Ok(EncodedLit::Const(true))
        } else {
            let cnf_lit = self.encode_lit(root);
            self.add_encoded_clause(&[cnf_lit])?;
            Ok(cnf_lit)
        }
    }

    fn assert_direct_root(&mut self, root: AigLit) -> Result<(), CnfError> {
        let node_id = root.node();
        let Some(AigNode::And(lhs, rhs)) = self.aig.node(node_id) else {
            unreachable!("direct root nodes are planned only for AND nodes");
        };
        if root.is_inverted()
            && let Some(plan) =
                distributable_negative_and_encoding(self.aig, lhs, rhs, &self.skip_nodes)
        {
            let other = self.encode_lit(plan.other).negated();
            for leaf in plan.or_leaves {
                let leaf = self.encode_lit(leaf).negated();
                self.add_encoded_clause(&[other, leaf])?;
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
            self.encode_xor_gate(out, xor_gate, encode_forward, encode_reverse)?;
        } else if let Some(not_ite_gate) = self.not_ite_gates[node_id.index()] {
            self.encode_not_ite_gate(out, not_ite_gate, encode_forward, encode_reverse)?;
        } else if let Some(not_and_gate) = self.not_and_gates[node_id.index()].clone() {
            self.encode_not_and_gate(out, &not_and_gate, encode_forward, encode_reverse)?;
        } else if let Some(and_tree_gate) = self.and_tree_gates[node_id.index()].clone() {
            self.encode_and_tree_gate(out, &and_tree_gate, encode_forward, encode_reverse)?;
        } else {
            self.encode_binary_and_gate(out, lhs, rhs, encode_forward, encode_reverse)?;
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

    fn add_encoded_clause(&mut self, lits: &[EncodedLit]) -> Result<(), CnfError> {
        let mut clause = Vec::new();
        for lit in lits {
            match lit {
                EncodedLit::Const(true) => return Ok(()),
                EncodedLit::Const(false) => {}
                EncodedLit::Lit(cnf_lit) => {
                    if clause.iter().any(|lit| *lit == cnf_lit.negated()) {
                        return Ok(());
                    }
                    if !clause.contains(cnf_lit) {
                        clause.push(*cnf_lit);
                    }
                }
            }
        }
        clause.sort_unstable();
        if !self.clause_keys.insert(clause.clone()) {
            return Ok(());
        }
        self.formula.add_clause(CnfClause::new(clause))
    }
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

fn rustsat_clause(clause: &CnfClause) -> Result<RustSatClause, SatError> {
    clause
        .lits()
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
        CnfClause, CnfError, CnfLit, CnfVar, EncodedLit, IncrementalCnf, IncrementalSat,
        RustSatBatsatSolver, SatProofStatus, SatResult, SatSolver, aig_lit_value, parse_dimacs,
        solve_with_rustsat_batsat, tseitin_encode,
    };

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
        assert_eq!(false_encoding.formula().clauses()[0].lits(), &[]);
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
    fn incremental_pg_emits_fewer_clauses_than_full_tseitin() {
        // A positive AND chain uses every gate in one (positive) polarity, so
        // lazy Plaisted–Greenbaum emits only the `v -> lhs & rhs` half — two
        // clauses per AND instead of the full three — proving the polarity win.
        let mut aig = Aig::new();
        let mut acc = aig.input("x0");
        let n_ands = 8usize;
        for i in 1..=n_ands {
            let next = aig.input(format!("x{i}"));
            acc = aig.and(acc, next);
        }
        let mut cnf = IncrementalCnf::new();
        cnf.assert_root(&aig, acc, None).expect("assert root");

        // 1 const-false unit + 2 clauses per AND (up half only) + 1 root unit.
        let lazy_pg = cnf.clause_count();
        assert_eq!(lazy_pg, 1 + 2 * n_ands + 1);
        // Full both-polarity Tseitin would emit three clauses per AND.
        let full_tseitin = 1 + 3 * n_ands + 1;
        assert!(
            lazy_pg < full_tseitin,
            "lazy PG {lazy_pg} should beat full Tseitin {full_tseitin}"
        );
        assert!(matches!(
            cnf.solve(&[], None).expect("solve"),
            SatResult::Sat(_)
        ));
    }
}
