//! A high-level incremental solver façade.
//!
//! [`Solver`] wraps any [`SolverBackend`] with an assertion stack and
//! SMT-LIB-style [`Solver::push`]/[`Solver::pop`] scopes, plus one-shot
//! [`Solver::check_assuming`] assumptions. It is the ergonomic surface a
//! consumer like a symbolic-execution engine wants: push a branch predicate,
//! check, pop, continue down another path.
//!
//! The façade is incremental at the *interface* level. The underlying backend
//! is still one-shot for now (each check re-submits the active assertions), so
//! a future incremental backend can be dropped in without changing consumer
//! code (incrementality note). Every `sat` is still checked by the backend's
//! own model replay.
//!
//! # Example
//!
//! ```
//! use axeyum_ir::{Sort, TermArena};
//! use axeyum_solver::{CheckResult, SatBvBackend, Solver};
//!
//! let mut arena = TermArena::new();
//! let x_sym = arena.declare("x", Sort::BitVec(8))?;
//! let x = arena.var(x_sym);
//! let ten = arena.bv_const(8, 10)?;
//! let x_lt_10 = arena.bv_ult(x, ten)?;
//!
//! let mut solver = Solver::new(SatBvBackend::new());
//! solver.assert(x_lt_10);
//!
//! // Explore a branch under a scope, then discard it.
//! solver.push();
//! let zero = arena.bv_const(8, 0)?;
//! let x_is_zero = arena.eq(x, zero)?;
//! solver.assert(x_is_zero);
//! assert!(matches!(solver.check(&arena)?, CheckResult::Sat(_)));
//! solver.pop();
//!
//! // A one-shot assumption does not persist after the check.
//! let five = arena.bv_const(8, 5)?;
//! let x_is_five = arena.eq(x, five)?;
//! assert!(matches!(
//!     solver.check_assuming(&arena, &[x_is_five])?,
//!     CheckResult::Sat(_)
//! ));
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use axeyum_ir::{TermArena, TermId};

use crate::backend::{
    Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig, SolverError,
};

/// A stateful, incremental front end over a [`SolverBackend`].
#[derive(Debug)]
pub struct Solver<B> {
    backend: B,
    config: SolverConfig,
    assertions: Vec<TermId>,
    scopes: Vec<usize>,
}

impl<B: SolverBackend> Solver<B> {
    /// Creates a solver over `backend` with the default configuration.
    pub fn new(backend: B) -> Self {
        Self::with_config(backend, SolverConfig::default())
    }

    /// Creates a solver over `backend` with an explicit configuration.
    pub fn with_config(backend: B, config: SolverConfig) -> Self {
        Self {
            backend,
            config,
            assertions: Vec::new(),
            scopes: Vec::new(),
        }
    }

    /// The current per-check configuration.
    pub fn config(&self) -> &SolverConfig {
        &self.config
    }

    /// Replaces the per-check configuration.
    pub fn set_config(&mut self, config: SolverConfig) {
        self.config = config;
    }

    /// Reports what the underlying backend supports.
    pub fn capabilities(&self) -> Capabilities {
        self.backend.capabilities()
    }

    /// Adds a Boolean assertion to the current scope.
    ///
    /// The sort is validated by the backend at [`Solver::check`] time, which
    /// returns [`SolverError::NonBooleanAssertion`] for a non-Boolean term.
    pub fn assert(&mut self, term: TermId) {
        self.assertions.push(term);
    }

    /// Adds several assertions to the current scope.
    pub fn assert_all(&mut self, terms: &[TermId]) {
        self.assertions.extend_from_slice(terms);
    }

    /// Opens a new scope; assertions added afterwards are removed by the
    /// matching [`Solver::pop`].
    pub fn push(&mut self) {
        self.scopes.push(self.assertions.len());
    }

    /// Closes the most recent scope, discarding assertions added since the
    /// matching [`Solver::push`].
    ///
    /// Returns `false` if there was no open scope to close.
    pub fn pop(&mut self) -> bool {
        match self.scopes.pop() {
            Some(mark) => {
                self.assertions.truncate(mark);
                true
            }
            None => false,
        }
    }

    /// The number of currently open scopes.
    pub fn scope_depth(&self) -> usize {
        self.scopes.len()
    }

    /// The assertions currently active across all open scopes.
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// Checks satisfiability of the active assertions.
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the backend (for example a non-Boolean
    /// assertion or an unsupported construct). An undecided query is
    /// `Ok(CheckResult::Unknown)`.
    pub fn check(&mut self, arena: &TermArena) -> Result<CheckResult, SolverError> {
        self.backend.check(arena, &self.assertions, &self.config)
    }

    /// Checks the active assertions together with one-shot `assumptions`.
    ///
    /// The assumptions hold only for this check and are not retained, matching
    /// SMT-LIB `check-sat-assuming` semantics.
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the backend.
    pub fn check_assuming(
        &mut self,
        arena: &TermArena,
        assumptions: &[TermId],
    ) -> Result<CheckResult, SolverError> {
        if assumptions.is_empty() {
            return self.check(arena);
        }
        let mut terms = Vec::with_capacity(self.assertions.len() + assumptions.len());
        terms.extend_from_slice(&self.assertions);
        terms.extend_from_slice(assumptions);
        self.backend.check(arena, &terms, &self.config)
    }

    /// Layer-attributed measurements from the most recent check, if recorded.
    pub fn last_stats(&self) -> Option<&SolveStats> {
        self.backend.last_stats()
    }

    /// Consumes the façade and returns the wrapped backend.
    pub fn into_backend(self) -> B {
        self.backend
    }
}
