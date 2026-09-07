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
//! # The literal convention: every explanation is a CLAUSE
//!
//! Every literal list this trait passes to the driver -- an [`Self::assert`]
//! conflict, a [`Self::final_check`] conflict, and an [`Self::explain`]
//! answer -- is **the clause itself**, not the asserted literals whose
//! conjunction is refuted. So a conflict `a & b` is reported as
//! `[~a, ~b]`, with every literal FALSE under the current assignment, and a
//! propagation reason for `p` is reported as `[p, ~a, ~b]`, with `p` the
//! implied literal and the rest false.
//!
//! That is deliberately the opposite of `axeyum_solver::euf_egraph`'s
//! `TheorySolver`, whose channel carries the asserted literals and whose
//! driver negates them; the adapter written on the solver side does the
//! negation once, at the boundary. Here the clause form is what the driver
//! installs, so carrying anything else would mean negating on the hot path.
//!
//! # What this module does NOT do
//!
//! It carries no per-lemma theory certificate. Under
//! [ADR-1704] a lemma the theory cannot discharge is legal and is *counted*
//! (`theory_lemmas_unchecked`); a lemma that is not enumerated at all is not.
//! Every clause that enters the database from a theory is recorded in the
//! artifact, which is what makes the count a subtraction rather than a claim.
//!
//! [ADR-1704]: ../../../../docs/research/09-decisions/adr-1704-cdclt-unsat-is-two-streams-a-boolean-refutation-over-cnf-plus-enumerated-theory-lemmas.md

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
    /// The total assignment is theory-inconsistent. The payload is the
    /// **conflict clause** (see the module header): every literal false under
    /// the current assignment, and the clause itself a valid theory lemma.
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

    /// Enqueues `lit` with an already-materialised explanation. `reason` is
    /// the **clause** `lit` together with one false literal per antecedent
    /// (see the module header).
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
    /// Returns the **conflict clause** when the assertion makes the theory
    /// state inconsistent: the negation of the refuted conjunction, so every
    /// literal in it is false under the current assignment (see the module
    /// header's convention note). An empty clause is not a refutation the
    /// driver will act on -- it names nothing to learn from, and the search
    /// degrades to the undecided outcome rather than reporting `unsat`.
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

    /// Resolves a deferred explanation handle into the **clause** it stands
    /// for: the implied literal (for a propagation) or nothing else (for a
    /// conflict), plus one false literal per antecedent. `None` is a theory
    /// bug, never a verdict.
    ///
    /// `implied` says which of the two the driver is asking for: `Some(lit)`
    /// when the handle justifies the propagation of `lit` (so `lit` must be in
    /// the returned clause), `None` when it is a conflict core (so every
    /// literal returned is false under the current assignment).
    ///
    /// A theory whose handles already stand for whole clauses ignores the
    /// argument. It exists for the adapters: `axeyum_solver::euf_egraph`'s
    /// `TheorySolver::explain` returns the **asserted literals** whose
    /// conjunction justifies the handle, and turning those into this module's
    /// clause form needs the implied literal that the asserted form leaves
    /// out. Without it an adapter would have to force every reason eagerly and
    /// the lazy channel would never pay.
    fn explain(&mut self, handle: ExplanationId, implied: Option<CnfLit>) -> Option<Vec<CnfLit>> {
        let _ = (handle, implied);
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
    fn explain(&mut self, _handle: ExplanationId, _implied: Option<CnfLit>) -> Option<Vec<CnfLit>> {
        None
    }

    #[inline]
    fn take_new_atoms(&mut self) -> usize {
        0
    }
}

/// A theory reached through a mutable borrow is the same theory.
///
/// This is what lets a caller keep ownership of its theory across a solve —
/// [`super::Cdcl`] owns its `T`, so the entry point passes `&mut theory` and
/// reads the theory's state back afterwards to build a model. Without it every
/// caller would have to hand the theory over and get it back by value.
impl<T: NativeTheory + ?Sized> NativeTheory for &mut T {
    const HAS_THEORY: bool = T::HAS_THEORY;

    #[inline]
    fn assert(&mut self, var: usize, value: bool) -> Result<(), Vec<CnfLit>> {
        (**self).assert(var, value)
    }

    #[inline]
    fn push(&mut self) {
        (**self).push();
    }

    #[inline]
    fn pop(&mut self) {
        (**self).pop();
    }

    #[inline]
    fn propagate_into(&mut self, queue: &mut PropagationQueue) {
        (**self).propagate_into(queue);
    }

    #[inline]
    fn final_check(&mut self) -> FinalCheckOutcome {
        (**self).final_check()
    }

    #[inline]
    fn explain(&mut self, handle: ExplanationId, implied: Option<CnfLit>) -> Option<Vec<CnfLit>> {
        (**self).explain(handle, implied)
    }

    #[inline]
    fn take_new_atoms(&mut self) -> usize {
        (**self).take_new_atoms()
    }
}
