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
//! * [`assume_auto`](SymbolicExecutor::assume_auto) does the same while keeping
//!   the retained warm select/UF abstraction slices on the warm route and using
//!   the memory/theory-aware route for remaining array or UF conditions.
//! * [`branch`](SymbolicExecutor::branch) reports, *without committing*, which of
//!   `cond` / `¬cond` the current path can still take — the fork decision; it
//!   keeps retained warm select/UF abstraction slices on the warm route and uses
//!   the memory/theory-aware route when the path or condition still needs it.
//! * [`enter`](SymbolicExecutor::enter) / [`backtrack`](SymbolicExecutor::backtrack)
//!   open and discard a choice point, so a caller can explore the path tree
//!   depth-first and undo a branch.
//! * [`model`](SymbolicExecutor::model) returns a concrete assignment satisfying
//!   the current path — a ready-to-run test input.
//! * [`explore_cfg`](SymbolicExecutor::explore_cfg) is the reusable DFS harness:
//!   a frontend supplies CFG states and branch terms; the executor handles
//!   scopes, feasibility pruning, and model-checked target witnesses.
//! * [`explore_cfg_checked`](SymbolicExecutor::explore_cfg_checked) adds the
//!   unicorn-style concrete replay hook: a frontend extracts concrete inputs
//!   from each model and independently checks that they reproduce the target.
//!
//! Soundness is inherited verbatim from the incremental engine: every `model` is
//! replay-checked against the path constraints by the ground evaluator, and
//! `unknown` (a resource limit) is a first-class [`PathStatus`], never silently
//! treated as infeasible (which would wrongly prune a live path).
//!
//! [`SymbolicMemory`] is the companion frontend helper for memory-bearing paths:
//! it owns the current SMT array term, builds `select`/`store` terms, and routes
//! load-equality feasibility through the executor's automatic warm/memory route.
//! It is a thin term-building layer, not the final warm lazy-array engine.

use axeyum_ir::{IrError, Sort, SymbolId, TermArena, TermId};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::incremental::{IncrementalBvSolver, known_literal_distinct};
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
/// helpers ask [`SymbolicExecutor`] through its automatic warm/memory path. It
/// deliberately does not claim warm lazy-array incrementality; unreduced
/// array/UF terms still route to the one-shot full dispatcher behind
/// [`SymbolicExecutor::branch_with_memory`] and
/// [`SymbolicExecutor::assume_with_memory`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolicMemory {
    array: TermId,
    index_sort: Sort,
    element_sort: Sort,
}

/// One frontend-owned symbolic memory write.
///
/// This is a construction helper for consumers that track memory writes as a
/// log before deciding whether to materialize an SMT array `store` chain or a
/// read-specific read-over-write `ite` chain. Later writes shadow earlier writes
/// at the same syntactic/concrete index, and read-specific construction skips
/// writes whose literal address is known not to alias the read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolicMemoryWrite {
    /// Address/index written.
    pub index: TermId,
    /// Value written at `index`.
    pub value: TermId,
}

impl SymbolicMemoryWrite {
    /// Creates a symbolic memory write entry.
    #[must_use]
    pub fn new(index: TermId, value: TermId) -> Self {
        Self { index, value }
    }
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

    /// Returns a normalized last-writer-wins write log for this memory sort.
    ///
    /// The normalization is intentionally conservative: it drops writes shadowed
    /// by a later write to the same `TermId` index, which covers concrete
    /// addresses because constants are interned by [`TermArena`], and it
    /// preserves all other writes in program order. This gives frontends a
    /// deterministic compact log without proving arbitrary index equivalences.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if any write index or value has the wrong sort.
    pub fn normalized_writes(
        &self,
        arena: &TermArena,
        writes: &[SymbolicMemoryWrite],
    ) -> Result<Vec<SymbolicMemoryWrite>, SolverError> {
        let mut reversed = Vec::with_capacity(writes.len());
        let mut seen_indices = Vec::new();
        for &write in writes.iter().rev() {
            self.check_write_sorts(arena, write)?;
            if seen_indices.contains(&write.index) {
                continue;
            }
            seen_indices.push(write.index);
            reversed.push(write);
        }
        reversed.reverse();
        Ok(reversed)
    }

    /// Builds `select(base_memory_after_writes, read_index)` as a compact
    /// read-over-write `ite` chain.
    ///
    /// Writes are first normalized with [`Self::normalized_writes`], so shadowed
    /// same-index writes do not emit dead equality guards. Writes at literal
    /// indices known distinct from `read_index` are skipped, and an exact
    /// same-index write becomes the current read value without an equality
    /// guard. The emitted term is:
    ///
    /// `ite(read_index = i_last, v_last, ... select(base, read_index))`
    ///
    /// with one equality guard per visible write that may alias the read. This
    /// is a frontend-side scaling helper for deep memory logs while the true
    /// warm lazy-array route remains in progress; it does not change the
    /// solver's theory support.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if `read_index` or any write has the wrong sort, or
    /// if term construction fails.
    pub fn load_with_write_log(
        &self,
        arena: &mut TermArena,
        read_index: TermId,
        writes: &[SymbolicMemoryWrite],
    ) -> Result<TermId, SolverError> {
        self.check_index_sort(arena, read_index)?;
        let visible = self.normalized_writes(arena, writes)?;
        let mut loaded = self.load(arena, read_index)?;
        for write in &visible {
            if known_literal_distinct(arena, read_index, write.index) {
                continue;
            }
            if write.index == read_index {
                loaded = write.value;
                continue;
            }
            let guard = arena.eq(read_index, write.index)?;
            loaded = arena.ite(guard, write.value, loaded)?;
        }
        Ok(loaded)
    }

    /// Builds `select(base_memory_after_writes, read_index) = expected` using the
    /// compact write-log read helper.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if `read_index`, `expected`, or any write has the
    /// wrong sort, or if term construction fails.
    pub fn load_eq_with_write_log(
        &self,
        arena: &mut TermArena,
        read_index: TermId,
        writes: &[SymbolicMemoryWrite],
        expected: TermId,
    ) -> Result<TermId, SolverError> {
        self.check_element_sort(arena, expected)?;
        let loaded = self.load_with_write_log(arena, read_index, writes)?;
        arena.eq(loaded, expected).map_err(Into::into)
    }

    /// Commits a compact write-log load equality to `executor` and checks it
    /// through the automatic warm/memory route.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from term construction or the executor check.
    pub fn assume_load_eq_with_write_log(
        &self,
        executor: &mut SymbolicExecutor,
        arena: &mut TermArena,
        read_index: TermId,
        writes: &[SymbolicMemoryWrite],
        expected: TermId,
    ) -> Result<PathStatus, SolverError> {
        let cond = self.load_eq_with_write_log(arena, read_index, writes, expected)?;
        executor.assume_auto(arena, cond)
    }

    /// Branches on a compact write-log load equality without committing either
    /// direction to `executor`, using the automatic warm/memory route.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from term construction or the executor check.
    pub fn branch_load_eq_with_write_log(
        &self,
        executor: &mut SymbolicExecutor,
        arena: &mut TermArena,
        read_index: TermId,
        writes: &[SymbolicMemoryWrite],
        expected: TermId,
    ) -> Result<Branch, SolverError> {
        let cond = self.load_eq_with_write_log(arena, read_index, writes, expected)?;
        executor.branch(arena, cond)
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
    /// checks feasibility through the automatic warm/memory route.
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
        executor.assume_auto(arena, cond)
    }

    /// Checks the feasibility of both directions of
    /// `select(current_memory, index) = expected`, without committing either
    /// direction to `executor`, using the automatic warm/memory route.
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
        executor.branch(arena, cond)
    }

    fn check_write_sorts(
        &self,
        arena: &TermArena,
        write: SymbolicMemoryWrite,
    ) -> Result<(), SolverError> {
        self.check_index_sort(arena, write.index)?;
        self.check_element_sort(arena, write.value)
    }

    fn check_index_sort(&self, arena: &TermArena, index: TermId) -> Result<(), SolverError> {
        let found = arena.sort_of(index);
        if found != self.index_sort {
            return Err(IrError::SortsDiffer(found, self.index_sort).into());
        }
        Ok(())
    }

    fn check_element_sort(&self, arena: &TermArena, value: TermId) -> Result<(), SolverError> {
        let found = arena.sort_of(value);
        if found != self.element_sort {
            return Err(IrError::SortsDiffer(found, self.element_sort).into());
        }
        Ok(())
    }
}

/// Resource and routing configuration for [`SymbolicExecutor::explore_cfg`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CfgExploreConfig {
    /// Maximum number of CFG states whose transfer function may be evaluated.
    pub max_steps: usize,
    /// Maximum number of target states to return before stopping exploration.
    pub max_targets: usize,
    /// Whether branch/assume/model checks force the memory-aware full
    /// dispatcher. The default `false` uses the automatic route: warm BV first
    /// when memory simplification removes arrays/UFs, otherwise memory fallback.
    pub memory_aware: bool,
}

impl Default for CfgExploreConfig {
    fn default() -> Self {
        Self {
            max_steps: 1024,
            max_targets: usize::MAX,
            memory_aware: false,
        }
    }
}

/// One target reached by [`SymbolicExecutor::explore_cfg`].
#[derive(Debug, Clone)]
pub struct CfgReached<State> {
    /// Frontend state at the target.
    pub state: State,
    /// Replay-checked model witnessing that the current path can reach `state`.
    pub model: Model,
    /// Axeyum path condition active when the target was reached.
    pub path_condition: Vec<TermId>,
}

/// One target whose model also passed an external concrete-emulation check.
#[derive(Debug, Clone)]
pub struct CfgCheckedReached<State, Witness> {
    /// Frontend state at the target.
    pub state: State,
    /// Replay-checked solver model witnessing the symbolic path.
    pub model: Model,
    /// Axeyum path condition active when the target was reached.
    pub path_condition: Vec<TermId>,
    /// Concrete witness extracted from the model and accepted by the caller's
    /// concrete checker.
    pub witness: Witness,
}

/// A symbolic target whose extracted concrete witness did not reproduce the
/// target under the caller's independent concrete checker.
#[derive(Debug, Clone)]
pub struct CfgConcreteMismatch<State, Witness> {
    /// Frontend state at the target.
    pub state: State,
    /// Replay-checked solver model for the symbolic path.
    pub model: Model,
    /// Axeyum path condition active when the target was reached.
    pub path_condition: Vec<TermId>,
    /// Concrete witness extracted from the model but rejected by the concrete
    /// checker.
    pub witness: Witness,
}

/// Exploration result from [`SymbolicExecutor::explore_cfg`].
#[derive(Debug, Clone)]
pub struct CfgExploreOutcome<State> {
    /// Model-witnessed target states found within the configured limits.
    pub reached: Vec<CfgReached<State>>,
    /// Number of CFG states whose transfer function was evaluated.
    pub steps: usize,
    /// Number of branch/assume directions pruned because they were proved
    /// infeasible.
    pub pruned_infeasible: usize,
    /// Number of branch directions whose feasibility was unknown and therefore
    /// explored as maybe-feasible.
    pub unknown_branches: usize,
    /// Number of target states that could not be reported because final
    /// feasibility/model extraction was `unknown`.
    pub undecided_targets: usize,
    /// Whether exploration stopped because `max_steps` or `max_targets` was
    /// reached.
    pub truncated: bool,
}

/// Exploration plus concrete-emulation checking result from
/// [`SymbolicExecutor::explore_cfg_checked`].
#[derive(Debug, Clone)]
pub struct CfgCheckedOutcome<State, Witness> {
    /// Targets accepted by both symbolic solving and concrete replay.
    pub verified: Vec<CfgCheckedReached<State, Witness>>,
    /// Symbolic targets for which the caller could not extract a concrete
    /// witness from the model.
    pub missing_witnesses: Vec<CfgReached<State>>,
    /// Symbolic targets whose concrete witness failed the caller's concrete
    /// replay check.
    pub mismatches: Vec<CfgConcreteMismatch<State, Witness>>,
    /// Number of CFG states whose transfer function was evaluated.
    pub steps: usize,
    /// Number of branch/assume directions pruned because they were proved
    /// infeasible.
    pub pruned_infeasible: usize,
    /// Number of branch directions whose feasibility was unknown and therefore
    /// explored as maybe-feasible.
    pub unknown_branches: usize,
    /// Number of target states that could not be reported because final
    /// feasibility/model extraction was `unknown`.
    pub undecided_targets: usize,
    /// Whether exploration stopped because `max_steps` or `max_targets` was
    /// reached.
    pub truncated: bool,
}

impl<State> Default for CfgExploreOutcome<State> {
    fn default() -> Self {
        Self {
            reached: Vec::new(),
            steps: 0,
            pruned_infeasible: 0,
            unknown_branches: 0,
            undecided_targets: 0,
            truncated: false,
        }
    }
}

/// A single frontend transfer step consumed by
/// [`SymbolicExecutor::explore_cfg`].
#[derive(Debug, Clone)]
pub enum CfgStep<State> {
    /// Move to another CFG state without adding a path constraint.
    Continue(State),
    /// Add `condition` to the current path and continue with `next` if the
    /// resulting path is not proved infeasible.
    Assume {
        /// Boolean condition to commit.
        condition: TermId,
        /// Successor state under the assumption.
        next: State,
    },
    /// Fork on `condition`: `if_true` is explored under `condition`, and
    /// `if_false` is explored under `not(condition)`.
    Branch {
        /// Boolean branch condition.
        condition: TermId,
        /// Successor state for the true edge.
        if_true: State,
        /// Successor state for the false edge.
        if_false: State,
    },
    /// Report a target state if the active path yields a replay-checked model.
    Target(State),
    /// Stop exploring this path without reporting a target.
    Stop,
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

    /// Commits `cond` and automatically selects the precise feasibility route:
    /// warm BV when the path remains array/UF-free or inside the retained warm
    /// select/UF abstraction slices, otherwise the memory/theory-aware
    /// dispatcher.
    ///
    /// This is the ergonomic path for frontends that may mix ordinary BV
    /// constraints with occasional symbolic memory or uninterpreted-call terms.
    /// The constraint remains scoped by [`enter`](Self::enter) /
    /// [`backtrack`](Self::backtrack).
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the underlying assert/check.
    pub fn assume_auto(
        &mut self,
        arena: &mut TermArena,
        cond: TermId,
    ) -> Result<PathStatus, SolverError> {
        self.solver.assert_simplifying_memory(arena, cond)?;
        self.path.push(cond);
        if self.needs_memory_route_for_current_path() {
            Ok(status_of(self.solver.check_with_memory(arena)?))
        } else {
            status_or_unknown(self.solver.check(arena))
        }
    }

    /// Reports which directions of `cond` the current path can take, **without**
    /// committing to either — the fork query. Use it to decide whether to
    /// explore the then-branch, the else-branch, or both.
    ///
    /// The method keeps pure-BV queries and retained warm select/UF abstraction
    /// slices on the warm path, and dispatches to the memory/theory-aware solver
    /// when the current path or branch condition contains array/UF structure
    /// outside those slices. This avoids returning a coarse `Unknown` solely
    /// because a branch mentions symbolic memory or a UF, while still preserving
    /// the fast route for simple store/read-back, BV-array select, and scalar UF
    /// fork queries.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if building `¬cond` or a feasibility check fails.
    pub fn branch(&mut self, arena: &mut TermArena, cond: TermId) -> Result<Branch, SolverError> {
        let not_cond = arena.not(cond)?;
        let encoded_cond =
            IncrementalBvSolver::simplify_memory_for_retained_warm_assertion(arena, cond);
        let encoded_not_cond =
            IncrementalBvSolver::simplify_memory_for_retained_warm_assertion(arena, not_cond);
        if self.needs_memory_route_for_current_path()
            || !IncrementalBvSolver::term_supported_by_warm_abstraction(arena, encoded_cond)
            || !IncrementalBvSolver::term_supported_by_warm_abstraction(arena, encoded_not_cond)
        {
            return self.branch_with_memory(arena, cond);
        }
        let if_true = status_or_unknown(
            self.solver
                .check_assuming_simplifying_memory(arena, &[cond]),
        )?;
        let if_false = status_or_unknown(
            self.solver
                .check_assuming_simplifying_memory(arena, &[not_cond]),
        )?;
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

    /// Feasibility of the current path, automatically selecting the memory-aware
    /// dispatcher if an active assertion contains arrays or UFs.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the selected check.
    pub fn status_auto(&mut self, arena: &mut TermArena) -> Result<PathStatus, SolverError> {
        if self.needs_memory_route_for_current_path() {
            self.status_with_memory(arena)
        } else {
            self.status(arena)
        }
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

    /// A concrete assignment for the current path, automatically selecting the
    /// memory-aware dispatcher if an active assertion contains arrays or UFs.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the selected check.
    pub fn model_auto(&mut self, arena: &mut TermArena) -> Result<Option<Model>, SolverError> {
        if self.needs_memory_route_for_current_path() {
            self.model_with_memory(arena)
        } else {
            self.model(arena)
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

    /// Explores a frontend CFG depth-first from `initial`.
    ///
    /// The caller supplies a transfer function from frontend states to
    /// [`CfgStep`]s. The executor owns the solver mechanics: it queries branch
    /// feasibility, opens a scope for each explored edge, commits the edge
    /// condition, backtracks after the recursive subtree, and reports only target
    /// states that have a replay-checked [`Model`]. `Unknown` branch directions
    /// are treated as maybe-feasible and explored; `Unknown` targets are counted
    /// in [`CfgExploreOutcome::undecided_targets`] rather than reported.
    ///
    /// The executor's incoming path condition is preserved when this method
    /// returns.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from the transfer function, term construction, or
    /// solver operations.
    pub fn explore_cfg<State, F>(
        &mut self,
        arena: &mut TermArena,
        initial: State,
        config: CfgExploreConfig,
        step: F,
    ) -> Result<CfgExploreOutcome<State>, SolverError>
    where
        F: FnMut(&mut TermArena, State) -> Result<CfgStep<State>, SolverError>,
    {
        let mut search = CfgSearch {
            executor: self,
            arena,
            config,
            step,
            outcome: CfgExploreOutcome::default(),
        };
        search.visit(initial)?;
        Ok(search.outcome)
    }

    /// Explores a frontend CFG and checks each symbolic target against an
    /// independent concrete witness.
    ///
    /// This wraps [`Self::explore_cfg`]. For each model-witnessed target,
    /// `extract_witness` lifts the solver model into a concrete input/test case,
    /// and `concrete_check` independently confirms that the input reproduces the
    /// target in the caller's concrete semantics. A target is reported in
    /// [`CfgCheckedOutcome::verified`] only when both layers agree. Missing
    /// witnesses and concrete mismatches are kept as explicit diagnostics because
    /// they usually indicate a frontend/lifter/model-lifting bug, not a solver
    /// proof of reachability.
    ///
    /// The executor's incoming path condition is preserved when this method
    /// returns.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] from CFG exploration, witness extraction, or the
    /// concrete checker.
    pub fn explore_cfg_checked<State, Witness, Step, Extract, Check>(
        &mut self,
        arena: &mut TermArena,
        initial: State,
        config: CfgExploreConfig,
        step: Step,
        mut extract_witness: Extract,
        mut concrete_check: Check,
    ) -> Result<CfgCheckedOutcome<State, Witness>, SolverError>
    where
        Step: FnMut(&mut TermArena, State) -> Result<CfgStep<State>, SolverError>,
        Extract: FnMut(&Model, &State) -> Result<Option<Witness>, SolverError>,
        Check: FnMut(&State, &Witness) -> Result<bool, SolverError>,
    {
        let exploration = self.explore_cfg(arena, initial, config, step)?;
        let CfgExploreOutcome {
            reached,
            steps,
            pruned_infeasible,
            unknown_branches,
            undecided_targets,
            truncated,
        } = exploration;
        let mut outcome = CfgCheckedOutcome {
            verified: Vec::new(),
            missing_witnesses: Vec::new(),
            mismatches: Vec::new(),
            steps,
            pruned_infeasible,
            unknown_branches,
            undecided_targets,
            truncated,
        };
        for reached in reached {
            let CfgReached {
                state,
                model,
                path_condition,
            } = reached;
            let Some(witness) = extract_witness(&model, &state)? else {
                outcome.missing_witnesses.push(CfgReached {
                    state,
                    model,
                    path_condition,
                });
                continue;
            };
            if concrete_check(&state, &witness)? {
                outcome.verified.push(CfgCheckedReached {
                    state,
                    model,
                    path_condition,
                    witness,
                });
            } else {
                outcome.mismatches.push(CfgConcreteMismatch {
                    state,
                    model,
                    path_condition,
                    witness,
                });
            }
        }
        Ok(outcome)
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

    fn needs_memory_route_for_current_path(&self) -> bool {
        self.solver.has_deferred_theory_assertions()
    }
}

struct CfgSearch<'a, State, F> {
    executor: &'a mut SymbolicExecutor,
    arena: &'a mut TermArena,
    config: CfgExploreConfig,
    step: F,
    outcome: CfgExploreOutcome<State>,
}

impl<State, F> CfgSearch<'_, State, F>
where
    F: FnMut(&mut TermArena, State) -> Result<CfgStep<State>, SolverError>,
{
    fn visit(&mut self, state: State) -> Result<(), SolverError> {
        if self.limit_reached() {
            return Ok(());
        }
        if self.outcome.steps >= self.config.max_steps {
            self.outcome.truncated = true;
            return Ok(());
        }
        self.outcome.steps += 1;

        match (self.step)(self.arena, state)? {
            CfgStep::Continue(next) => self.visit(next),
            CfgStep::Assume { condition, next } => self.visit_assumption(condition, next),
            CfgStep::Branch {
                condition,
                if_true,
                if_false,
            } => self.visit_branch(condition, if_true, if_false),
            CfgStep::Target(target) => self.record_target(target),
            CfgStep::Stop => Ok(()),
        }
    }

    fn visit_branch(
        &mut self,
        condition: TermId,
        if_true: State,
        if_false: State,
    ) -> Result<(), SolverError> {
        let branch = if self.config.memory_aware {
            self.executor.branch_with_memory(self.arena, condition)?
        } else {
            self.executor.branch(self.arena, condition)?
        };
        self.visit_direction(condition, &branch.if_true, if_true)?;
        let not_condition = self.arena.not(condition)?;
        self.visit_direction(not_condition, &branch.if_false, if_false)
    }

    fn visit_direction(
        &mut self,
        assumption: TermId,
        branch_status: &PathStatus,
        state: State,
    ) -> Result<(), SolverError> {
        match branch_status {
            PathStatus::Infeasible => {
                self.outcome.pruned_infeasible += 1;
                Ok(())
            }
            PathStatus::Unknown(_) => {
                self.outcome.unknown_branches += 1;
                self.visit_assumption(assumption, state)
            }
            PathStatus::Feasible => self.visit_assumption(assumption, state),
        }
    }

    fn visit_assumption(&mut self, condition: TermId, state: State) -> Result<(), SolverError> {
        self.executor.enter()?;
        let status = match if self.config.memory_aware {
            self.executor.assume_with_memory(self.arena, condition)
        } else {
            self.executor.assume_auto(self.arena, condition)
        } {
            Ok(status) => status,
            Err(error) => {
                self.executor.backtrack();
                return Err(error);
            }
        };
        if status.is_infeasible() {
            self.outcome.pruned_infeasible += 1;
        } else {
            self.visit(state)?;
        }
        if self.executor.backtrack() {
            Ok(())
        } else {
            Err(SolverError::Backend(
                "CFG exploration scope stack underflow".to_owned(),
            ))
        }
    }

    fn record_target(&mut self, state: State) -> Result<(), SolverError> {
        match self.current_status()? {
            PathStatus::Feasible => {
                if let Some(model) = self.current_model()? {
                    self.outcome.reached.push(CfgReached {
                        state,
                        model,
                        path_condition: self.executor.path_condition().to_vec(),
                    });
                } else {
                    self.outcome.undecided_targets += 1;
                }
                Ok(())
            }
            PathStatus::Infeasible => {
                self.outcome.pruned_infeasible += 1;
                Ok(())
            }
            PathStatus::Unknown(_) => {
                self.outcome.undecided_targets += 1;
                Ok(())
            }
        }
    }

    fn current_status(&mut self) -> Result<PathStatus, SolverError> {
        if self.config.memory_aware {
            self.executor.status_with_memory(self.arena)
        } else {
            self.executor.status_auto(self.arena)
        }
    }

    fn current_model(&mut self) -> Result<Option<Model>, SolverError> {
        if self.config.memory_aware {
            self.executor.model_with_memory(self.arena)
        } else {
            self.executor.model_auto(self.arena)
        }
    }

    fn limit_reached(&mut self) -> bool {
        if self.outcome.reached.len() >= self.config.max_targets {
            self.outcome.truncated = true;
            true
        } else {
            false
        }
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
    use axeyum_ir::{ArraySortKey, Assignment, Sort, Value, WideUint, eval};

    fn x(arena: &mut TermArena) -> TermId {
        arena.bv_var("x", 8).unwrap()
    }

    #[test]
    fn branch_over_scalar_uf_auto_stays_warm() {
        // Modeling an unmodeled library/syscall as an uninterpreted `g`: branching
        // on `g(x) == 5` must not require callers to pick the explicit
        // memory/theory-aware entry point. The scalar Bool/BV UF slice should now
        // stay on the retained warm abstraction route.
        let mut arena = TermArena::new();
        let xv = x(&mut arena);
        let g = arena
            .declare_fun("g", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let gx = arena.apply(g, &[xv]).unwrap();
        let five = arena.bv_const(8, 5).unwrap();
        let cond = arena.eq(gx, five).unwrap();
        let mut exec = SymbolicExecutor::new();
        let clauses_before = exec.solver.encoded_clause_count();
        let branch = exec
            .branch(&mut arena, cond)
            .expect("branch should auto-route a scalar UF condition");
        let clauses_after = exec.solver.encoded_clause_count();
        assert!(
            branch.if_true.is_feasible(),
            "UF branch then-direction should be feasible, got {:?}",
            branch.if_true
        );
        assert!(
            branch.if_false.is_feasible(),
            "UF branch else-direction should be feasible, got {:?}",
            branch.if_false
        );
        assert!(
            clauses_after > clauses_before,
            "scalar UF branch should encode warm one-shot assumptions instead of using the dispatcher"
        );
        assert!(
            !exec.solver.has_deferred_theory_assertions(),
            "one-shot scalar UF branch queries must not persist as deferred theory assertions"
        );
    }

    #[test]
    fn branch_over_wide_bv_uf_auto_stays_warm() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("branch_warm_wide_uf_x", 256).unwrap();
        let g = arena
            .declare_fun(
                "branch_warm_wide_uf_g",
                &[Sort::BitVec(256)],
                Sort::BitVec(256),
            )
            .unwrap();
        let gx = arena.apply(g, &[x]).unwrap();
        let target = arena.wide_bv_const(
            WideUint::from_u128(0x5a, 256).or(&WideUint::from_u128(1, 256).shl(190)),
        );
        let cond = arena.eq(gx, target).unwrap();

        let mut exec = SymbolicExecutor::new();
        let clauses_before = exec.solver.encoded_clause_count();
        let branch = exec
            .branch(&mut arena, cond)
            .expect("branch should auto-route a wide scalar UF condition");
        let clauses_after = exec.solver.encoded_clause_count();

        assert!(
            branch.if_true.is_feasible(),
            "wide UF branch then-direction should be feasible, got {:?}",
            branch.if_true
        );
        assert!(
            branch.if_false.is_feasible(),
            "wide UF branch else-direction should be feasible, got {:?}",
            branch.if_false
        );
        assert!(
            clauses_after > clauses_before,
            "wide UF branch should encode warm one-shot assumptions instead of using the dispatcher"
        );
        assert!(
            !exec.solver.has_deferred_theory_assertions(),
            "one-shot wide UF branch queries must not persist as deferred theory assertions"
        );
    }

    #[test]
    fn branch_over_bv_array_select_auto_stays_warm() {
        let mut arena = TermArena::new();
        let mem_sym = arena
            .declare(
                "branch_warm_select_mem",
                Sort::Array {
                    index: ArraySortKey::BitVec(8),
                    element: ArraySortKey::BitVec(8),
                },
            )
            .unwrap();
        let idx = arena.bv_var("branch_warm_select_idx", 8).unwrap();
        let mem = arena.var(mem_sym);
        let loaded = arena.select(mem, idx).unwrap();
        let target = arena.bv_const(8, 0x5a).unwrap();
        let cond = arena.eq(loaded, target).unwrap();

        let mut exec = SymbolicExecutor::new();
        let clauses_before = exec.solver.encoded_clause_count();
        let branch = exec
            .branch(&mut arena, cond)
            .expect("branch should auto-route a BV-array select condition");
        let clauses_after = exec.solver.encoded_clause_count();

        assert!(
            branch.if_true.is_feasible(),
            "array-select branch then-direction should be feasible, got {:?}",
            branch.if_true
        );
        assert!(
            branch.if_false.is_feasible(),
            "array-select branch else-direction should be feasible, got {:?}",
            branch.if_false
        );
        assert!(
            clauses_after > clauses_before,
            "BV-array select branch should encode warm one-shot assumptions instead of using the dispatcher"
        );
        assert!(
            !exec.solver.has_deferred_theory_assertions(),
            "one-shot select branch queries must not persist as deferred theory assertions"
        );
    }

    #[test]
    fn branch_over_wide_bv_array_select_auto_stays_warm() {
        let mut arena = TermArena::new();
        let mem_sym = arena
            .declare(
                "branch_warm_wide_select_mem",
                Sort::Array {
                    index: ArraySortKey::BitVec(256),
                    element: ArraySortKey::BitVec(256),
                },
            )
            .unwrap();
        let idx = arena.bv_var("branch_warm_wide_select_idx", 256).unwrap();
        let mem = arena.var(mem_sym);
        let loaded = arena.select(mem, idx).unwrap();
        let target = arena.wide_bv_const(
            WideUint::from_u128(0x5a, 256).or(&WideUint::from_u128(1, 256).shl(190)),
        );
        let cond = arena.eq(loaded, target).unwrap();

        let mut exec = SymbolicExecutor::new();
        let clauses_before = exec.solver.encoded_clause_count();
        let branch = exec
            .branch(&mut arena, cond)
            .expect("branch should auto-route a wide BV-array select condition");
        let clauses_after = exec.solver.encoded_clause_count();

        assert!(
            branch.if_true.is_feasible(),
            "wide array-select branch then-direction should be feasible, got {:?}",
            branch.if_true
        );
        assert!(
            branch.if_false.is_feasible(),
            "wide array-select branch else-direction should be feasible, got {:?}",
            branch.if_false
        );
        assert!(
            clauses_after > clauses_before,
            "wide BV-array select branch should encode warm one-shot assumptions instead of using the dispatcher"
        );
        assert!(
            !exec.solver.has_deferred_theory_assertions(),
            "one-shot wide select branch queries must not persist as deferred theory assertions"
        );
    }

    #[test]
    fn branch_over_bool_array_select_auto_stays_warm() {
        let mut arena = TermArena::new();
        let mem_sym = arena
            .declare(
                "branch_warm_bool_select_mem",
                Sort::Array {
                    index: ArraySortKey::BitVec(8),
                    element: ArraySortKey::Bool,
                },
            )
            .unwrap();
        let idx = arena.bv_var("branch_warm_bool_select_idx", 8).unwrap();
        let mem = arena.var(mem_sym);
        let cond = arena.select(mem, idx).unwrap();

        let mut exec = SymbolicExecutor::new();
        let clauses_before = exec.solver.encoded_clause_count();
        let branch = exec
            .branch(&mut arena, cond)
            .expect("branch should auto-route a Bool-array select condition");
        let clauses_after = exec.solver.encoded_clause_count();

        assert!(
            branch.if_true.is_feasible(),
            "Bool-array select branch then-direction should be feasible, got {:?}",
            branch.if_true
        );
        assert!(
            branch.if_false.is_feasible(),
            "Bool-array select branch else-direction should be feasible, got {:?}",
            branch.if_false
        );
        assert!(
            clauses_after > clauses_before,
            "Bool-array select branch should encode warm one-shot assumptions instead of using the dispatcher"
        );
        assert!(
            !exec.solver.has_deferred_theory_assertions(),
            "one-shot Bool-select branch queries must not persist as deferred theory assertions"
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
