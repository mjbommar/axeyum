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

    /// Reconstruct a kernel-checked Lean proof that the active assertions are UNSAT,
    /// dispatching to the matching theory emitter+reconstructor (see
    /// [`crate::prove_unsat_to_lean`]); returns the [`crate::ProofFragment`] routed.
    ///
    /// Call after [`Solver::check`] reports [`CheckResult::Unsat`]: this re-derives
    /// the refutation as a machine-checkable Lean term the trusted kernel accepts,
    /// over the supported fragments (`QF_BV`/`QF_UF`/`QF_UFBV`/`QF_ABV`, datatypes,
    /// `LRA`, `∀`/`∃`).
    /// `arena` is taken mutably because the emitters introduce fresh terms (skolems,
    /// lowered operators) during proof construction.
    ///
    /// # Errors
    ///
    /// Propagates [`crate::ReconstructError`] when the fragment is unsupported, the
    /// instance is not UNSAT through it, or reconstruction does not kernel-check.
    pub fn prove_unsat_to_lean(
        &self,
        arena: &mut TermArena,
    ) -> Result<crate::ProofFragment, crate::ReconstructError> {
        crate::prove_unsat_to_lean(arena, &self.assertions)
    }

    /// Like [`Solver::prove_unsat_to_lean`], but also returns a **self-contained
    /// Lean 4 module** (`prelude`-mode source) that re-proves the refutation and is
    /// checkable by an independent `lean` binary (see
    /// [`crate::prove_unsat_to_lean_module`]).
    ///
    /// # Errors
    ///
    /// Same as [`Solver::prove_unsat_to_lean`].
    pub fn prove_unsat_to_lean_module(
        &self,
        arena: &mut TermArena,
    ) -> Result<(crate::ProofFragment, String), crate::ReconstructError> {
        crate::prove_unsat_to_lean_module(arena, &self.assertions)
    }

    /// Computes a (deletion-minimized) unsat core of the active assertions as
    /// indices into them, or `None` if they are not `unsat` (see
    /// [`crate::unsat_core`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the underlying solve.
    pub fn unsat_core(&self, arena: &mut TermArena) -> Result<Option<Vec<usize>>, SolverError> {
        crate::unsat_core(arena, &self.assertions, &self.config)
    }

    /// Computes a verified Craig interpolant for the partition of the active
    /// assertions in which `a_indices` selects the `A`-side and the remaining
    /// assertions form the `B`-side. Returns `Ok(Some(I))` with a fully
    /// re-checked interpolant, or `Ok(None)` when no Farkas interpolant is
    /// available (the conjunction is satisfiable, outside conjunctive `QF_LRA`,
    /// or the candidate fails its re-checks). Out-of-range indices are ignored.
    /// See [`crate::lra_interpolant`].
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the underlying Farkas decision / the
    /// interpolant re-verification.
    pub fn interpolant(
        &self,
        arena: &mut TermArena,
        a_indices: &[usize],
    ) -> Result<Option<TermId>, SolverError> {
        let n = self.assertions.len();
        let a_set: std::collections::BTreeSet<usize> =
            a_indices.iter().copied().filter(|&i| i < n).collect();
        let a: Vec<TermId> = a_set.iter().map(|&i| self.assertions[i]).collect();
        let b: Vec<TermId> = (0..n)
            .filter(|i| !a_set.contains(i))
            .map(|i| self.assertions[i])
            .collect();
        // Try the QF_LRA Farkas interpolant, then ground EUF, then the QF_BV
        // bit-blast interpolant — the natural fallback for QF_BV partitions —
        // when the earlier theories decline (Unsupported or `Ok(None)`).
        match crate::lra_interpolant(arena, &a, &b) {
            Ok(Some(interpolant)) => Ok(Some(interpolant)),
            Ok(None) | Err(SolverError::Unsupported(_)) => {
                match crate::qf_uf_interpolant(arena, &a, &b) {
                    Ok(Some(interpolant)) => Ok(Some(interpolant)),
                    Ok(None) => Ok(crate::qf_bv_interpolant(arena, &a, &b)),
                    Err(other) => Err(other),
                }
            }
            Err(other) => Err(other),
        }
    }

    /// Maximizes the integer-linear `objective` subject to the active assertions
    /// (see [`crate::maximize_lia`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn maximize_lia(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<crate::OptOutcome, SolverError> {
        crate::maximize_lia(arena, &self.assertions, objective)
    }

    /// Maximizes the unsigned bit-vector `objective` subject to the active
    /// assertions (see [`crate::maximize_bv`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn maximize_bv(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<crate::OptOutcome, SolverError> {
        crate::maximize_bv_with_config(arena, &self.assertions, objective, &self.config)
    }

    /// Minimizes the unsigned bit-vector `objective` subject to the active
    /// assertions (see [`crate::minimize_bv`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn minimize_bv(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<crate::OptOutcome, SolverError> {
        crate::minimize_bv_with_config(arena, &self.assertions, objective, &self.config)
    }

    /// Minimizes the integer-linear `objective` subject to the active assertions
    /// (see [`crate::minimize_lia`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn minimize_lia(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<crate::OptOutcome, SolverError> {
        crate::minimize_lia(arena, &self.assertions, objective)
    }

    /// Lexicographic multi-objective optimization over the active assertions (see
    /// [`crate::optimize_lia_lexicographic`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_lexicographic(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::LexObjective],
    ) -> Result<crate::LexOutcome, SolverError> {
        crate::optimize_lia_lexicographic(arena, &self.assertions, objectives)
    }

    /// Box (independent) multi-objective optimization over the active assertions
    /// (see [`crate::optimize_lia_box`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_box(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::LexObjective],
    ) -> Result<Vec<crate::OptOutcome>, SolverError> {
        crate::optimize_lia_box(arena, &self.assertions, objectives)
    }

    /// Pareto-front multi-objective optimization over the active assertions (see
    /// [`crate::optimize_lia_pareto`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_pareto(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::LexObjective],
    ) -> Result<crate::ParetoOutcome, SolverError> {
        crate::optimize_lia_pareto(arena, &self.assertions, objectives)
    }

    /// Lexicographic multi-objective optimization over **bit-vector** objectives
    /// (see [`crate::optimize_bv_lexicographic`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_lexicographic_bv(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::BvLexObjective],
    ) -> Result<crate::LexOutcome, SolverError> {
        crate::optimize_bv_lexicographic_with_config(
            arena,
            &self.assertions,
            objectives,
            &self.config,
        )
    }

    /// Box (independent) multi-objective optimization over **bit-vector**
    /// objectives (see [`crate::optimize_bv_box`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_box_bv(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::BvLexObjective],
    ) -> Result<Vec<crate::OptOutcome>, SolverError> {
        crate::optimize_bv_box_with_config(arena, &self.assertions, objectives, &self.config)
    }

    /// Pareto-front multi-objective optimization over **bit-vector** objectives
    /// (see [`crate::optimize_bv_pareto`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn optimize_pareto_bv(
        &self,
        arena: &mut TermArena,
        objectives: &[crate::BvLexObjective],
    ) -> Result<crate::ParetoOutcome, SolverError> {
        crate::optimize_bv_pareto_with_config(arena, &self.assertions, objectives, &self.config)
    }

    /// Maximizes the number of satisfied `soft` constraints subject to the active
    /// assertions (`MaxSAT`), returning the witnessing model (see
    /// [`crate::max_satisfiable_model`]).
    ///
    /// # Errors
    ///
    /// Propagates [`SolverError`] from the optimizer.
    pub fn max_satisfiable(
        &self,
        arena: &mut TermArena,
        soft: &[TermId],
    ) -> Result<crate::MaxSatOutcome, SolverError> {
        crate::max_satisfiable_model(arena, &self.assertions, soft)
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

#[cfg(test)]
mod tests {
    use axeyum_ir::{Sort, TermArena};

    use crate::{CheckResult, ProofFragment, SatBvBackend, Solver};

    /// End-to-end on the façade: assert an UNSAT bit-vector query, confirm the
    /// backend decides `Unsat`, then reconstruct a kernel-checked Lean proof of it
    /// via [`Solver::prove_unsat_to_lean`] — the full solve → machine-checkable-proof
    /// flow on the public API.
    #[test]
    fn facade_solve_then_prove_unsat_to_lean() {
        let mut arena = TermArena::new();
        let a = {
            let s = arena.declare("a", Sort::BitVec(2)).unwrap();
            arena.var(s)
        };
        let b = {
            let s = arena.declare("b", Sort::BitVec(2)).unwrap();
            arena.var(s)
        };
        let sub = arena.bv_sub(a, b).unwrap(); // a - b
        let e1 = arena.eq(sub, a).unwrap(); // a - b = a  ⇒ b = 0
        let e2 = arena.bv_ult(a, b).unwrap(); // a < b, with b = 0 ⇒ a < 0, impossible

        let mut solver = Solver::new(SatBvBackend::new());
        solver.assert(e1);
        solver.assert(e2);
        assert!(matches!(solver.check(&arena).unwrap(), CheckResult::Unsat));

        let fragment = solver
            .prove_unsat_to_lean(&mut arena)
            .expect("the UNSAT bit-vector query reconstructs to a kernel-checked Lean `False`");
        assert_eq!(fragment, ProofFragment::QfBv);
    }

    /// The façade exposes optimization end-to-end: assert `0 ≤ x ≤ 7`, then
    /// `maximize_lia` over the active assertions → 7.
    #[test]
    fn facade_maximize_lia() {
        use crate::OptOutcome;

        let mut arena = TermArena::new();
        let x = {
            let s = arena.declare("x", Sort::Int).unwrap();
            arena.var(s)
        };
        let zero = arena.int_const(0);
        let seven = arena.int_const(7);
        let lo = arena.int_ge(x, zero).unwrap();
        let hi = arena.int_le(x, seven).unwrap();

        let mut solver = Solver::new(SatBvBackend::new());
        solver.assert(lo);
        solver.assert(hi);
        assert_eq!(
            solver.maximize_lia(&mut arena, x).unwrap(),
            OptOutcome::Optimal(7)
        );
    }
    /// The façade exposes unsat-core extraction: of three assertions where two
    /// conflict (`x=5`, `x=6`) plus an irrelevant one, the core is a subset that
    /// excludes the irrelevant assertion.
    #[test]
    fn facade_unsat_core() {
        let mut arena = TermArena::new();
        let x = {
            let s = arena.declare("x", Sort::BitVec(8)).unwrap();
            arena.var(s)
        };
        let five = arena.bv_const(8, 5).unwrap();
        let six = arena.bv_const(8, 6).unwrap();
        let y = {
            let s = arena.declare("y", Sort::BitVec(8)).unwrap();
            arena.var(s)
        };
        let one = arena.bv_const(8, 1).unwrap();
        let x5 = arena.eq(x, five).unwrap();
        let x6 = arena.eq(x, six).unwrap();
        let irrelevant = arena.eq(y, one).unwrap();

        let mut solver = Solver::new(SatBvBackend::new());
        solver.assert(x5);
        solver.assert(irrelevant);
        solver.assert(x6);
        let core = solver
            .unsat_core(&mut arena)
            .unwrap()
            .expect("the query is unsat, so it has a core");
        // The conflict is x5 (index 0) and x6 (index 2); index 1 (irrelevant) is out.
        assert!(core.contains(&0) && core.contains(&2));
        assert!(
            !core.contains(&1),
            "irrelevant assertion must not be in the core"
        );
    }
}
