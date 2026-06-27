//! A symbolic-execution driver: depth-first path exploration with feasibility
//! pruning and concrete model (test-input) extraction.
//!
//! Reachability ([`bounded_model_check`](crate::bounded_model_check),
//! [`prove_safety_k_induction`](crate::prove_safety_k_induction)) is the
//! *verification* face of symbolic execution; this is the *exploration* face —
//! the loop a KLEE/angr-style engine runs: maintain a **path condition**, ask at
//! each branch which directions are feasible, follow the feasible ones, and read
//! off a concrete input witnessing each reached path.
//!
//! [`SymbolicExecutor`] wraps the warm [`IncrementalBvSolver`] and exposes that
//! loop directly:
//!
//! * [`assume`](SymbolicExecutor::assume) commits a constraint to the current
//!   path and reports whether the path is still feasible.
//! * [`branch`](SymbolicExecutor::branch) reports, *without committing*, which of
//!   `cond` / `¬cond` the current path can still take — the fork decision.
//! * [`enter`](SymbolicExecutor::enter) / [`backtrack`](SymbolicExecutor::backtrack)
//!   open and discard a choice point, so a caller can explore the path tree
//!   depth-first and undo a branch.
//! * [`model`](SymbolicExecutor::model) returns a concrete assignment satisfying
//!   the current path — a ready-to-run test input.
//!
//! Soundness is inherited verbatim from the incremental engine: every `model` is
//! replay-checked against the path constraints by the ground evaluator, and
//! `unknown` (a resource limit) is a first-class [`PathStatus`], never silently
//! treated as infeasible (which would wrongly prune a live path).
//!
//! [`SymbolicMemory`] is the companion frontend helper for memory-bearing paths:
//! it owns the current SMT array term, builds `select`/`store` terms, and routes
//! load-equality feasibility through the memory-aware executor APIs. It is a thin
//! term-building layer, not the final warm lazy-array engine.

use axeyum_ir::{IrError, Sort, SymbolId, TermArena, TermId};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::incremental::IncrementalBvSolver;
use crate::model::Model;
use crate::optimize::{
    OptOutcome, maximize_bv, maximize_bv_signed, maximize_lia, minimize_bv, minimize_bv_signed,
    minimize_lia,
};

/// The feasibility of a path (prefix) under the solver: a sound three-valued
/// answer. `Unknown` preserves the "never wrong" contract — an undecided path is
/// not pruned.
#[derive(Debug, Clone)]
pub enum PathStatus {
    /// The path condition is satisfiable; exploration may continue.
    Feasible,
    /// The path condition is unsatisfiable; this sub-tree is dead and can be
    /// pruned.
    Infeasible,
    /// Undecided within the resource limit. Sound callers treat this as "may be
    /// feasible" (do not prune) and surface it.
    Unknown(UnknownReason),
}

impl PathStatus {
    /// Whether the path is known satisfiable.
    #[must_use]
    pub fn is_feasible(&self) -> bool {
        matches!(self, PathStatus::Feasible)
    }

    /// Whether the path is *known* unsatisfiable. `Unknown` is **not** infeasible
    /// — this is the pruning-safety predicate (only a definite `Infeasible`
    /// justifies cutting a branch).
    #[must_use]
    pub fn is_infeasible(&self) -> bool {
        matches!(self, PathStatus::Infeasible)
    }
}

/// Which directions of a conditional the current path can take, evaluated
/// without committing to either (the fork decision in symbolic execution).
#[derive(Debug, Clone)]
pub struct Branch {
    /// Feasibility of taking the branch with `cond` true.
    pub if_true: PathStatus,
    /// Feasibility of taking the branch with `cond` false.
    pub if_false: PathStatus,
}

impl Branch {
    /// Whether both directions are feasible — a genuine fork (the path splits).
    #[must_use]
    pub fn forks(&self) -> bool {
        self.if_true.is_feasible() && self.if_false.is_feasible()
    }
}

/// A typed symbolic memory value backed by an SMT array term.
///
/// This is the small frontend-facing memory abstraction needed by CFG symbolic
/// executors: `load` builds `select(mem, addr)`, `store` advances the current
/// memory term to `store(mem, addr, value)`, and the convenience branch/assume
/// helpers ask [`SymbolicExecutor`] through its memory-aware path. It deliberately
/// does not claim warm lazy-array incrementality; the solver route is still the
/// one-shot full dispatcher behind [`SymbolicExecutor::branch_with_memory`] and
/// [`SymbolicExecutor::assume_with_memory`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolicMemory {
    array: TermId,
    index_sort: Sort,
    element_sort: Sort,
}

impl SymbolicMemory {
    /// Declares a bit-vector indexed/value memory and wraps its array term.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if either width is invalid or `name` is already
    /// declared with a different sort.
    pub fn declare_bv(
        arena: &mut TermArena,
        name: &str,
        index_width: u32,
        element_width: u32,
    ) -> Result<Self, SolverError> {
        let array = arena.array_var(name, index_width, element_width)?;
        Self::from_array(arena, array)
    }

    /// Declares an array memory with arbitrary non-array index and element sorts
    /// and wraps its array term.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if either component sort is unsupported for arrays
    /// or `name` is already declared with a different sort.
    pub fn declare_with_sorts(
        arena: &mut TermArena,
        name: &str,
        index: Sort,
        element: Sort,
    ) -> Result<Self, SolverError> {
        let array = arena.array_var_with_sorts(name, index, element)?;
        Self::from_array(arena, array)
    }

    /// Creates a memory wrapper from an existing array term.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if `array` is not an array term.
    pub fn from_array(arena: &TermArena, array: TermId) -> Result<Self, SolverError> {
        let Sort::Array { index, element } = arena.sort_of(array) else {
            return Err(IrError::SortMismatch {
                expected: "Array",
                found: arena.sort_of(array),
            }
            .into());
        };
        Ok(Self {
            array,
            index_sort: index.to_sort(),
            element_sort: element.to_sort(),
        })
    }

    /// The current array term representing this memory state.
    #[must_use]
    pub fn term(&self) -> TermId {
        self.array
    }

    /// Sort of valid memory addresses.
    #[must_use]
    pub fn index_sort(&self) -> Sort {
        self.index_sort
    }

    /// Sort of values stored in memory.
    #[must_use]
    pub fn element_sort(&self) -> Sort {
        self.element_sort
    }

    /// Builds `select(current_memory, index)`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if `index` does not match this memory's index
    /// sort.
    pub fn load(&self, arena: &mut TermArena, index: TermId) -> Result<TermId, SolverError> {
        arena.select(self.array, index).map_err(Into::into)
    }

    /// Advances this memory to `store(current_memory, index, value)` and returns
    /// the new current memory term.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if `index` or `value` does not match this memory's
    /// array sort.
    pub fn store(
        &mut self,
        arena: &mut TermArena,
        index: TermId,
        value: TermId,
    ) -> Result<TermId, SolverError> {
        self.array = arena.store(self.array, index, value)?;
        Ok(self.array)
    }

    /// Returns a copy of this memory after one store, leaving `self` unchanged.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if `index` or `value` does not match this memory's
    /// array sort.
    pub fn with_store(
        &self,
        arena: &mut TermArena,
        index: TermId,
        value: TermId,
    ) -> Result<Self, SolverError> {
        let mut next = *self;
        next.store(arena, index, value)?;
        Ok(next)
    }

    /// Builds the Boolean term `select(current_memory, index) = expected`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if `index` or `expected` has the wrong sort.
    pub fn load_eq(
        &self,
        arena: &mut TermArena,
        index: TermId,
        expected: TermId,
    ) -> Result<TermId, SolverError> {
        let loaded = self.load(arena, index)?;
        arena.eq(loaded, expected).map_err(Into::into)
    }

    /// Commits `select(current_memory, index) = expected` to `executor` and
    /// checks feasibility through the memory-aware solver route.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from term construction or the executor check.
    pub fn assume_load_eq(
        &self,
        executor: &mut SymbolicExecutor,
        arena: &mut TermArena,
        index: TermId,
        expected: TermId,
    ) -> Result<PathStatus, SolverError> {
        let cond = self.load_eq(arena, index, expected)?;
        executor.assume_with_memory(arena, cond)
    }

    /// Checks the feasibility of both directions of
    /// `select(current_memory, index) = expected`, without committing either
    /// direction to `executor`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from term construction or the executor check.
    pub fn branch_load_eq(
        &self,
        executor: &mut SymbolicExecutor,
        arena: &mut TermArena,
        index: TermId,
        expected: TermId,
    ) -> Result<Branch, SolverError> {
        let cond = self.load_eq(arena, index, expected)?;
        executor.branch_with_memory(arena, cond)
    }
}

/// A symbolic-execution engine over the pure-Rust incremental BV solver.
///
/// Bound to a single [`TermArena`]; path constraints accumulate across calls and
/// scope with [`enter`](Self::enter) / [`backtrack`](Self::backtrack).
#[derive(Debug, Default)]
pub struct SymbolicExecutor {
    solver: IncrementalBvSolver,
    /// The current path condition as a flat list of committed constraints, kept
    /// in sync with the solver so the path can be handed to the optimizers
    /// ([`minimize`](Self::minimize) / [`maximize`](Self::maximize)).
    path: Vec<TermId>,
    /// `path.len()` at each open choice point, so [`backtrack`](Self::backtrack)
    /// can drop the constraints added since the matching [`enter`](Self::enter).
    marks: Vec<usize>,
}

impl SymbolicExecutor {
    /// Creates an executor with the default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an executor with an explicit configuration (e.g. a per-query
    /// timeout that bounds each feasibility check).
    #[must_use]
    pub fn with_config(config: SolverConfig) -> Self {
        Self {
            solver: IncrementalBvSolver::with_config(config),
            path: Vec::new(),
            marks: Vec::new(),
        }
    }

    /// The current path condition (the committed constraints, in order).
    #[must_use]
    pub fn path_condition(&self) -> &[TermId] {
        &self.path
    }

    /// The number of open choice points (from [`enter`](Self::enter)).
    #[must_use]
    pub fn depth(&self) -> usize {
        self.solver.scope_depth()
    }

    /// Opens a choice point. Constraints added afterwards are discarded by the
    /// matching [`backtrack`](Self::backtrack) — the DFS "fork".
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the underlying scope cannot be opened.
    pub fn enter(&mut self) -> Result<(), SolverError> {
        self.solver.push()?;
        self.marks.push(self.path.len());
        Ok(())
    }

    /// Discards the most recent choice point and everything assumed under it.
    /// Returns `false` if there was no open choice point.
    pub fn backtrack(&mut self) -> bool {
        if self.solver.pop() {
            if let Some(mark) = self.marks.pop() {
                self.path.truncate(mark);
            }
            true
        } else {
            false
        }
    }

    /// Commits `cond` to the current path condition and reports whether the path
    /// remains feasible.
    ///
    /// A returned [`PathStatus::Infeasible`] means the path is now dead (the
    /// constraint contradicts the prefix); the caller typically
    /// [`backtrack`](Self::backtrack)s. The constraint stays asserted regardless
    /// — wrap speculative assumptions in [`enter`](Self::enter) /
    /// [`backtrack`](Self::backtrack) if you may need to undo them.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the underlying assert/check (e.g. a
    /// non-Boolean condition or an unsupported operator).
    pub fn assume(&mut self, arena: &TermArena, cond: TermId) -> Result<PathStatus, SolverError> {
        self.solver.assert(arena, cond)?;
        self.path.push(cond);
        Ok(status_of(self.solver.check(arena)?))
    }

    /// Commits `cond` and checks feasibility through the memory/theory-aware
    /// one-shot dispatcher. Use this when the path condition mentions arrays
    /// (`select`/`store`) or uninterpreted functions.
    ///
    /// The constraint is still scoped by [`enter`](Self::enter) /
    /// [`backtrack`](Self::backtrack); only the feasibility check falls back from
    /// the warm BV path to the full dispatcher.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the underlying assert/check.
    pub fn assume_with_memory(
        &mut self,
        arena: &mut TermArena,
        cond: TermId,
    ) -> Result<PathStatus, SolverError> {
        self.solver.assert(arena, cond)?;
        self.path.push(cond);
        Ok(status_of(self.solver.check_with_memory(arena)?))
    }

    /// Reports which directions of `cond` the current path can take, **without**
    /// committing to either — the fork query. Use it to decide whether to
    /// explore the then-branch, the else-branch, or both.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if building `¬cond` or a feasibility check fails.
    pub fn branch(&mut self, arena: &mut TermArena, cond: TermId) -> Result<Branch, SolverError> {
        let not_cond = arena.not(cond)?;
        let if_true = status_or_unknown(self.solver.check_assuming(arena, &[cond]))?;
        let if_false = status_or_unknown(self.solver.check_assuming(arena, &[not_cond]))?;
        Ok(Branch { if_true, if_false })
    }

    /// Memory/theory-aware version of [`Self::branch`]. The branch condition may
    /// mention arrays or uninterpreted functions; both directions are checked as
    /// one-shot assumptions and are not retained.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if building `¬cond` or a feasibility check fails.
    pub fn branch_with_memory(
        &mut self,
        arena: &mut TermArena,
        cond: TermId,
    ) -> Result<Branch, SolverError> {
        let not_cond = arena.not(cond)?;
        let if_true = status_or_unknown(self.solver.check_assuming_with_memory(arena, &[cond]))?;
        let if_false =
            status_or_unknown(self.solver.check_assuming_with_memory(arena, &[not_cond]))?;
        Ok(Branch { if_true, if_false })
    }

    /// Feasibility of the current path condition on its own.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the underlying check.
    pub fn status(&mut self, arena: &TermArena) -> Result<PathStatus, SolverError> {
        status_or_unknown(self.solver.check(arena))
    }

    /// Feasibility of the current path through the memory/theory-aware
    /// dispatcher. Use when the committed path mentions arrays or UFs.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the underlying check.
    pub fn status_with_memory(&mut self, arena: &mut TermArena) -> Result<PathStatus, SolverError> {
        status_or_unknown(self.solver.check_with_memory(arena))
    }

    /// A concrete assignment satisfying the current path condition — a runnable
    /// test input for the explored path — or `None` if the path is infeasible (or
    /// `unknown`). The model is replay-checked by the incremental engine before it
    /// is returned.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the underlying check.
    pub fn model(&mut self, arena: &TermArena) -> Result<Option<Model>, SolverError> {
        match self.solver.check(arena)? {
            CheckResult::Sat(model) => Ok(Some(model)),
            CheckResult::Unsat | CheckResult::Unknown(_) => Ok(None),
        }
    }

    /// A concrete assignment for the current path through the memory/theory-aware
    /// dispatcher. Use when the committed path mentions arrays or UFs.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the underlying check.
    pub fn model_with_memory(
        &mut self,
        arena: &mut TermArena,
    ) -> Result<Option<Model>, SolverError> {
        match self.solver.check_with_memory(arena)? {
            CheckResult::Sat(model) => Ok(Some(model)),
            CheckResult::Unsat | CheckResult::Unknown(_) => Ok(None),
        }
    }

    /// Enumerates up to `limit` **distinct** concrete inputs (over `symbols`)
    /// that all drive the current path — a test suite for this path. Each input
    /// is a replay-checked [`Model`] and differs from every other on at least one
    /// listed symbol (all-SAT by blocking clauses).
    ///
    /// The enumeration runs in a temporary scope, so the blocking clauses are
    /// discarded afterwards and the path condition is left exactly as it was —
    /// the executor can keep exploring or optimizing. Fewer than `limit` results
    /// means the path admits only that many distinct assignments over `symbols`
    /// (or the solver returned `unknown`/`unsat` first — a short list is never a
    /// wrong claim of exhaustiveness, just what was found).
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the underlying scope, solve, or block step.
    pub fn enumerate_inputs(
        &mut self,
        arena: &mut TermArena,
        symbols: &[SymbolId],
        limit: usize,
    ) -> Result<Vec<Model>, SolverError> {
        let mut inputs = Vec::new();
        // Isolate the blocking clauses so the path condition survives the call.
        self.solver.push()?;
        while inputs.len() < limit {
            match self.solver.check(arena)? {
                CheckResult::Sat(model) => {
                    self.solver.block_model(arena, &model, symbols)?;
                    inputs.push(model);
                }
                CheckResult::Unsat | CheckResult::Unknown(_) => break,
            }
        }
        self.solver.pop();
        Ok(inputs)
    }

    /// Memory/theory-aware version of [`Self::enumerate_inputs`]. Blocking
    /// clauses remain warm BV constraints, while each feasibility/model query
    /// uses the full dispatcher so array/UF path conditions are honored.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the underlying scope, solve, or block step.
    pub fn enumerate_inputs_with_memory(
        &mut self,
        arena: &mut TermArena,
        symbols: &[SymbolId],
        limit: usize,
    ) -> Result<Vec<Model>, SolverError> {
        let mut inputs = Vec::new();
        self.solver.push()?;
        while inputs.len() < limit {
            match self.solver.check_with_memory(arena)? {
                CheckResult::Sat(model) => {
                    self.solver.block_model(arena, &model, symbols)?;
                    inputs.push(model);
                }
                CheckResult::Unsat | CheckResult::Unknown(_) => break,
            }
        }
        self.solver.pop();
        Ok(inputs)
    }

    /// Maximizes the **unsigned** bit-vector `objective` subject to the current
    /// path condition — e.g. the worst-case value a variable can take along this
    /// path. The optimum is certified by the underlying procedure (a witness model
    /// at the bound). This is the constrained-optimization face of symbolic
    /// execution: optimize over exactly the inputs that drive this path.
    ///
    /// # Errors
    ///
    /// As [`maximize_bv`]: [`SolverError::Unsupported`] for a non-bit-vector or
    /// too-wide `objective`, or [`SolverError::Backend`].
    pub fn maximize(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<OptOutcome, SolverError> {
        maximize_bv(arena, &self.path, objective)
    }

    /// Minimizes the **unsigned** bit-vector `objective` subject to the current
    /// path condition — e.g. the smallest input that still drives this path.
    ///
    /// # Errors
    ///
    /// See [`Self::maximize`].
    pub fn minimize(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<OptOutcome, SolverError> {
        minimize_bv(arena, &self.path, objective)
    }

    /// Maximizes the **signed** (two's-complement) bit-vector `objective` subject
    /// to the current path condition.
    ///
    /// # Errors
    ///
    /// See [`Self::maximize`].
    pub fn maximize_signed(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<OptOutcome, SolverError> {
        maximize_bv_signed(arena, &self.path, objective)
    }

    /// Minimizes the **signed** (two's-complement) bit-vector `objective` subject
    /// to the current path condition.
    ///
    /// # Errors
    ///
    /// See [`Self::maximize`].
    pub fn minimize_signed(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<OptOutcome, SolverError> {
        minimize_bv_signed(arena, &self.path, objective)
    }

    /// Maximizes the integer-linear `objective` subject to the current path
    /// condition (for `Int`-sorted objectives / `QF_LIA` paths).
    ///
    /// # Errors
    ///
    /// As [`maximize_lia`].
    pub fn maximize_int(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<OptOutcome, SolverError> {
        maximize_lia(arena, &self.path, objective)
    }

    /// Minimizes the integer-linear `objective` subject to the current path
    /// condition (for `Int`-sorted objectives / `QF_LIA` paths).
    ///
    /// # Errors
    ///
    /// As [`minimize_lia`].
    pub fn minimize_int(
        &self,
        arena: &mut TermArena,
        objective: TermId,
    ) -> Result<OptOutcome, SolverError> {
        minimize_lia(arena, &self.path, objective)
    }
}

/// Maps a raw [`CheckResult`] to the three-valued [`PathStatus`].
fn status_of(result: CheckResult) -> PathStatus {
    match result {
        CheckResult::Sat(_) => PathStatus::Feasible,
        CheckResult::Unsat => PathStatus::Infeasible,
        CheckResult::Unknown(reason) => PathStatus::Unknown(reason),
    }
}

/// Maps a feasibility-check result to a [`PathStatus`], turning a backend
/// `Unsupported` (the warm BV solver cannot represent an operator in the path
/// condition — e.g. an uninterpreted `Apply` from an unmodeled call) into a sound
/// [`PathStatus::Unknown`] rather than a hard error. `Unknown` is treated as "may
/// be feasible" (not pruned), so this never wrongly cuts a branch; it honors the
/// "unknown is never an error" rule for these feasibility *decision* queries. Any
/// other [`SolverError`] (a genuine internal failure) still propagates.
fn status_or_unknown(result: Result<CheckResult, SolverError>) -> Result<PathStatus, SolverError> {
    match result {
        Ok(r) => Ok(status_of(r)),
        Err(SolverError::Unsupported(detail)) => Ok(PathStatus::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail,
        })),
        Err(other) => Err(other),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{Assignment, Sort, Value, eval};

    fn x(arena: &mut TermArena) -> TermId {
        arena.bv_var("x", 8).unwrap()
    }

    #[test]
    fn branch_over_uninterpreted_call_is_unknown_not_error() {
        // Modeling an unmodeled library/syscall as an uninterpreted `g`: branching
        // on `g(x) == 5` must yield a graceful three-valued verdict (Unknown — "may
        // be feasible, do not prune"), NOT a hard `Err` — the warm BV backend can't
        // represent `Apply`, but a feasibility *decision* query honors "unknown is
        // never an error".
        let mut arena = TermArena::new();
        let xv = x(&mut arena);
        let g = arena
            .declare_fun("g", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let gx = arena.apply(g, &[xv]).unwrap();
        let five = arena.bv_const(8, 5).unwrap();
        let cond = arena.eq(gx, five).unwrap();
        let mut exec = SymbolicExecutor::new();
        let branch = exec
            .branch(&mut arena, cond)
            .expect("branch must not error on a UF condition");
        assert!(
            matches!(branch.if_true, PathStatus::Unknown(_)),
            "UF branch then-direction must be Unknown, got {:?}",
            branch.if_true
        );
        assert!(
            matches!(branch.if_false, PathStatus::Unknown(_)),
            "UF branch else-direction must be Unknown, got {:?}",
            branch.if_false
        );
    }

    #[test]
    fn infeasible_nested_branch_is_pruned() {
        // Symbolic program: if (x > 10) { if (x < 5) { BUG } }. The inner branch
        // (x > 10 ∧ x < 5) is infeasible and must be reported as a dead path.
        let mut arena = TermArena::new();
        let xv = x(&mut arena);
        let ten = arena.bv_const(8, 10).unwrap();
        let five = arena.bv_const(8, 5).unwrap();
        let x_gt_10 = arena.bv_ugt(xv, ten).unwrap();
        let x_lt_5 = arena.bv_ult(xv, five).unwrap();

        let mut se = SymbolicExecutor::new();
        assert!(se.assume(&arena, x_gt_10).unwrap().is_feasible());

        let branch = se.branch(&mut arena, x_lt_5).unwrap();
        assert!(
            branch.if_true.is_infeasible(),
            "x > 10 ∧ x < 5 is unsatisfiable"
        );
        assert!(branch.if_false.is_feasible(), "x > 10 ∧ x >= 5 is fine");
        assert!(!branch.forks(), "the buggy branch does not fork");

        // Committing the infeasible condition kills the path.
        assert!(se.assume(&arena, x_lt_5).unwrap().is_infeasible());
    }

    #[test]
    fn feasible_path_yields_a_replayable_test_input() {
        let mut arena = TermArena::new();
        let xv = x(&mut arena);
        let ten = arena.bv_const(8, 10).unwrap();
        let x_gt_10 = arena.bv_ugt(xv, ten).unwrap();

        let mut se = SymbolicExecutor::new();
        assert!(se.assume(&arena, x_gt_10).unwrap().is_feasible());

        let model = se.model(&arena).unwrap().expect("path is feasible");
        // The concrete input genuinely drives execution down this path.
        let assignment: Assignment = model.to_assignment();
        assert_eq!(
            eval(&arena, x_gt_10, &assignment).unwrap(),
            Value::Bool(true),
            "the extracted test input must satisfy the path condition"
        );
    }

    #[test]
    fn backtracking_explores_sibling_paths() {
        // if (x & 1 == 0) take EVEN else take ODD — enumerate one input per side.
        let mut arena = TermArena::new();
        let xv = x(&mut arena);
        let one = arena.bv_const(8, 1).unwrap();
        let lsb = arena.bv_and(xv, one).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let is_even = arena.eq(lsb, zero).unwrap();

        let mut se = SymbolicExecutor::new();
        let branch = se.branch(&mut arena, is_even).unwrap();
        assert!(branch.forks(), "parity genuinely forks on a free input");

        let even_one = arena.not(is_even).unwrap();

        // Explore the even side, then backtrack and explore the odd side.
        se.enter().unwrap();
        assert!(se.assume(&arena, is_even).unwrap().is_feasible());
        let even_model = se.model(&arena).unwrap().expect("even path feasible");
        let even_x = even_model.to_assignment();
        assert_eq!(
            eval(&arena, is_even, &even_x).unwrap(),
            Value::Bool(true),
            "even path input is even"
        );
        assert!(se.backtrack());

        se.enter().unwrap();
        assert!(se.assume(&arena, even_one).unwrap().is_feasible());
        let odd_model = se.model(&arena).unwrap().expect("odd path feasible");
        let odd_x = odd_model.to_assignment();
        assert_eq!(
            eval(&arena, is_even, &odd_x).unwrap(),
            Value::Bool(false),
            "odd path input is odd"
        );
        assert!(se.backtrack());
        assert_eq!(se.depth(), 0, "fully backtracked to the root path");
    }

    #[test]
    fn optimize_objective_along_the_path_condition() {
        // Path: x > 10 ∧ x is even. Smallest such x is 12, largest (8-bit) is 254.
        let mut arena = TermArena::new();
        let xv = x(&mut arena);
        let ten = arena.bv_const(8, 10).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let x_gt_10 = arena.bv_ugt(xv, ten).unwrap();
        let lsb = arena.bv_and(xv, one).unwrap();
        let is_even = arena.eq(lsb, zero).unwrap();

        let mut se = SymbolicExecutor::new();
        assert!(se.assume(&arena, x_gt_10).unwrap().is_feasible());
        assert!(se.assume(&arena, is_even).unwrap().is_feasible());

        assert_eq!(
            se.minimize(&mut arena, xv).unwrap(),
            crate::OptOutcome::Optimal(12),
            "smallest even input above 10"
        );
        assert_eq!(
            se.maximize(&mut arena, xv).unwrap(),
            crate::OptOutcome::Optimal(254),
            "largest even 8-bit input"
        );
    }

    #[test]
    fn enumerate_inputs_generates_a_distinct_test_suite() {
        // Path: x is even. Generate three distinct even test inputs, then confirm
        // the path condition is intact and still optimizable afterwards.
        let mut arena = TermArena::new();
        let xv = x(&mut arena);
        let one = arena.bv_const(8, 1).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let lsb = arena.bv_and(xv, one).unwrap();
        let is_even = arena.eq(lsb, zero).unwrap();
        let x_sym = arena.find_symbol("x").unwrap();

        let mut se = SymbolicExecutor::new();
        assert!(se.assume(&arena, is_even).unwrap().is_feasible());

        let suite = se.enumerate_inputs(&mut arena, &[x_sym], 3).unwrap();
        assert_eq!(
            suite.len(),
            3,
            "three distinct inputs requested and available"
        );

        let mut values = Vec::new();
        for model in &suite {
            let assignment = model.to_assignment();
            // Every generated input genuinely drives the path (x even)...
            assert_eq!(
                eval(&arena, is_even, &assignment).unwrap(),
                Value::Bool(true)
            );
            let Value::Bv { value, .. } = model.get(x_sym).unwrap() else {
                panic!("x is a bit-vector");
            };
            values.push(value);
        }
        values.sort_unstable();
        values.dedup();
        assert_eq!(
            values.len(),
            3,
            "...and the three inputs are pairwise distinct"
        );

        // The temporary blocking clauses were discarded: the path still optimizes.
        assert_eq!(
            se.minimize(&mut arena, xv).unwrap(),
            crate::OptOutcome::Optimal(0),
            "path condition intact after enumeration (smallest even is 0)"
        );
    }
}
