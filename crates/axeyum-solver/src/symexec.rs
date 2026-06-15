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

use axeyum_ir::{TermArena, TermId};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownReason};
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

    /// Reports which directions of `cond` the current path can take, **without**
    /// committing to either — the fork query. Use it to decide whether to
    /// explore the then-branch, the else-branch, or both.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if building `¬cond` or a feasibility check fails.
    pub fn branch(&mut self, arena: &mut TermArena, cond: TermId) -> Result<Branch, SolverError> {
        let not_cond = arena.not(cond)?;
        let if_true = status_of(self.solver.check_assuming(arena, &[cond])?);
        let if_false = status_of(self.solver.check_assuming(arena, &[not_cond])?);
        Ok(Branch { if_true, if_false })
    }

    /// Feasibility of the current path condition on its own.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the underlying check.
    pub fn status(&mut self, arena: &TermArena) -> Result<PathStatus, SolverError> {
        Ok(status_of(self.solver.check(arena)?))
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

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{Assignment, Value, eval};

    fn x(arena: &mut TermArena) -> TermId {
        arena.bv_var("x", 8).unwrap()
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
}
