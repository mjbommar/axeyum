//! The `rustsat-batsat` adapter, kept **only** as a differential oracle
//! (ADR-1703).
//!
//! ADR-0007 chose `rustsat-batsat` as the first pure-Rust SAT adapter, before
//! any native core existed, and labelled it scaffolding whose `unsat` was
//! "explicitly lower-assurance until a proof-producing path and checker exist".
//! That path exists (ADR-0011 / ADR-0012 / ADR-0613), so ADR-1703 makes the
//! native core the SAT engine on every Axeyum path and demotes this adapter to
//! the role ADR-0002 gives Z3: an independent referee for differential testing,
//! never a shipping engine.
//!
//! The whole module is behind the non-default `batsat-reference` feature, so
//! the default dependency graph contains no `batsat`, `rustsat`, or
//! `rustsat-batsat` (`cargo tree -e normal -p axeyum-cnf`). Slice 2 of ADR-1703
//! deletes this file and the feature with it — which is exactly why the adapter
//! lives in one file rather than scattered through `lib.rs`.
//!
//! Nothing outside tests may call into here. The production entry points are
//! [`crate::solve_with_native_core`] and [`crate::NativeIncrementalCdcl`].

use std::cell::Cell;
use std::time::Duration;

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use rustsat::{
    solvers::{Solve, SolveIncremental, SolverResult as RustSatSolverResult},
    types::{
        Clause as RustSatClause, Lit as RustSatLit, TernaryVal as RustSatTernaryVal,
        Var as RustSatVar,
    },
};

use crate::{
    CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar, SatCapabilities, SatDependencyProfile,
    SatError, SatFeatureSupport, SatProofStatus, SatResult, SatSolver, SatUnknownReason,
    SatUnsatEvidence,
};

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
