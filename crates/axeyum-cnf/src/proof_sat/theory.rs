//! Theory hooks for the native CDCL core (ADR-1701 slice 2 **spike**).
//!
//! This module is the shape a theory would attach to [`super::Cdcl`] with,
//! mirroring `axeyum_solver::euf_egraph::TheorySolver` as ADR-1701 widened it:
//! assert-on-assignment, propagation into a driver-owned queue, a complete
//! `final_check` at a total assignment, `push`/`pop` in lockstep with decision
//! levels, lazy explanation, and dynamic atom registration.
//!
//! It cannot *be* that trait: `axeyum-cnf` sits below `axeyum-solver` in the
//! dependency graph (the solver depends on the CNF layer, never the reverse),
//! so the driver-side adapter in slice 2 proper is a blanket
//! `impl NativeTheory for T where T: TheorySolver` written in `axeyum-solver`,
//! translating `CnfLit` <-> `TheoryLit` at the boundary. The shape is kept
//! deliberately identical so that adapter is mechanical.
//!
//! **Nothing in this module is public API and no shipping entry point uses
//! anything but [`NullTheory`].** Every existing `solve_with_drat_proof*`
//! function constructs the search with [`NullTheory`], whose methods are empty
//! and whose [`NativeTheory::HAS_THEORY`] is `false`, so the search
//! trajectory, the DRAT stream and every verdict are unchanged.
//!
//! # What this spike does NOT do
//!
//! - It does not implement conflict-driven theory learning. A theory conflict
//!   or a theory propagation reaches the search and is answered by abandoning
//!   it with the *undecided* outcome `SearchOutcome::Interrupted`. That is
//!   deliberate: a theory lemma is **not** RUP against the CNF, so admitting
//!   one into the learned-clause database would silently invalidate the DRAT
//!   proof this core emits. The proof contract under theory lemmas is the
//!   first thing slice 2 proper has to decide (see the design memo,
//!   `docs/plan/adr-1701-slice-2-design-2026-09-05.md`).
//! - It does not change the reason representation. `reason[v]` is still
//!   `Option<CRef>`, so a lazily-explained theory implication has nowhere to
//!   live yet; the cost of widening it to an enum is unmeasured here.

// The module is deliberately the WHOLE slice-2 shape, mirroring
// `TheorySolver` method for method, while the spike's search consumes only the
// part it can act on without touching the DRAT contract (see the module header).
// The unused half -- `TheoryExplanation::Eager`, `FinalCheckOutcome::Unknown`,
// and the queue's read side -- is what a real theory writes and what slice 2
// proper reads, and deleting it now would make the memo describe an interface
// that is not in the tree. Scoped to this module so dead code anywhere else in
// the core is still a warning.
#![allow(dead_code)]

use crate::CnfLit;

/// An opaque, theory-owned handle to an explanation the theory has **not**
/// materialised. Mirrors `axeyum_solver::euf_egraph::ExplanationId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExplanationId(pub u64);

/// A theory conflict core or propagation reason: literals now, or a handle the
/// driver resolves on demand. Mirrors
/// `axeyum_solver::euf_egraph::TheoryExplanation`, over [`CnfLit`] rather than
/// `TheoryLit`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TheoryExplanation {
    /// The literals, materialised now.
    Eager(Vec<CnfLit>),
    /// A handle resolved through [`NativeTheory::explain`] on demand.
    Lazy(ExplanationId),
}

/// The answer a theory gives to [`NativeTheory::final_check`]. Mirrors
/// `axeyum_solver::euf_egraph::FinalCheckOutcome`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FinalCheckOutcome {
    /// The total assignment is theory-consistent.
    Sat,
    /// The total assignment is theory-inconsistent; `!AND core` is a valid
    /// theory lemma.
    Conflict(TheoryExplanation),
    /// The check could not be completed. Never a verdict.
    Unknown,
}

/// The driver-owned propagation queue handed to
/// [`NativeTheory::propagate_into`]. Mirrors
/// `axeyum_solver::euf_egraph::PropagationQueue`.
///
/// The driver owns one for the whole search and clears it between fixpoint
/// iterations, so its allocation is paid once rather than per call.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct PropagationQueue {
    items: Vec<(CnfLit, TheoryExplanation)>,
}

impl PropagationQueue {
    /// An empty queue.
    pub fn new() -> Self {
        Self::default()
    }

    /// Enqueues `lit` with an already-materialised explanation.
    pub fn push_eager(&mut self, lit: CnfLit, reason: Vec<CnfLit>) {
        self.items.push((lit, TheoryExplanation::Eager(reason)));
    }

    /// Enqueues `lit` with a **deferred** explanation.
    pub fn push_lazy(&mut self, lit: CnfLit, handle: ExplanationId) {
        self.items.push((lit, TheoryExplanation::Lazy(handle)));
    }

    /// Number of queued propagations.
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Whether the queue is empty.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Empties the queue, retaining its allocation.
    pub fn clear(&mut self) {
        self.items.clear();
    }

    /// The queued propagations, in enqueue order.
    pub fn entries(&self) -> &[(CnfLit, TheoryExplanation)] {
        &self.items
    }
}

/// A theory the native CDCL core can drive (the slice-2 shape).
///
/// Atoms are identified by **SAT variable index**: the driver tells the theory
/// about `(var, value)` and the theory owns any var-to-atom map it needs. That
/// is the same convention `TheorySolver::assert` uses (its `atom: usize` is the
/// driver's variable index in every in-tree implementor).
pub trait NativeTheory {
    /// Whether this theory does anything at all.
    ///
    /// [`NullTheory`] sets it `false`, which lets the search skip every
    /// theory-side branch at monomorphization time rather than at run time.
    /// Consulting it in the search is design **B** of the slice-2 spike
    /// measurement; design **A** calls the same hooks unconditionally with
    /// empty `#[inline]` bodies. Both are measured in the design memo.
    const HAS_THEORY: bool = true;

    /// Asserts SAT variable `var` at `value` (the cheap partial check).
    ///
    /// # Errors
    ///
    /// Returns the conflicting literals when the assertion makes the theory
    /// state inconsistent.
    fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>>;

    /// Saves a backtrack point aligned with a SAT decision level.
    fn push(&mut self);

    /// Undoes every assertion back to the most recent [`Self::push`].
    fn pop(&mut self);

    /// Sound theory propagation into the driver-owned `queue`.
    fn propagate_into(&mut self, queue: &mut PropagationQueue);

    /// The **complete** check, run at a total Boolean assignment.
    fn final_check(&mut self) -> FinalCheckOutcome {
        FinalCheckOutcome::Sat
    }

    /// Resolves a deferred explanation handle. `None` is a theory bug, never a
    /// verdict.
    fn explain(&mut self, handle: ExplanationId) -> Option<Vec<CnfLit>> {
        let _ = handle;
        None
    }

    /// Number of theory atoms registered since the previous call.
    fn take_new_atoms(&mut self) -> usize {
        0
    }
}

/// The theory that does nothing: the default for every shipping entry point.
///
/// `HAS_THEORY = false`, so a `Cdcl<'_, S, NullTheory>` is the same machine as
/// the pre-spike core.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct NullTheory;

impl NativeTheory for NullTheory {
    const HAS_THEORY: bool = false;

    #[inline]
    fn assert(&mut self, _var: usize, _value: bool) -> Result<(), Vec<CnfLit>> {
        Ok(())
    }

    #[inline]
    fn push(&mut self) {}

    #[inline]
    fn pop(&mut self) {}

    #[inline]
    fn propagate_into(&mut self, _queue: &mut PropagationQueue) {}

    #[inline]
    fn final_check(&mut self) -> FinalCheckOutcome {
        FinalCheckOutcome::Sat
    }

    #[inline]
    fn explain(&mut self, _handle: ExplanationId) -> Option<Vec<CnfLit>> {
        None
    }

    #[inline]
    fn take_new_atoms(&mut self) -> usize {
        0
    }
}
