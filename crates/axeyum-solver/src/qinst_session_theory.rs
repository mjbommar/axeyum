//! The quantifier-instance session's theory: an `EUF` e-graph with a `LIA`
//! theory beside it, sharing one atom index space (ADR-2130).
//!
//! # Why this exists
//!
//! [ADR-2124] found that `OnlineQuantifierClauseSession` declines to exist on
//! any ground set carrying an arithmetic atom, which puts `UFLIA`, `AUFLIRA`,
//! `UFNIA`, `AUFDTLIRA` and `UFDTLIRA` in the re-solve regime for their whole
//! run. Its lever made the session *exist* on such a set by **abstracting** the
//! arithmetic atom to a free propositional variable. An abstracted atom is a
//! weakening: it only adds models, so the session can still decline to re-solve,
//! but it can never **refute** through the arithmetic. This module is the other
//! half — the session hosts the arithmetic theory instead of abstracting it, so
//! its `unsat` can be a Farkas conflict rather than only a congruence one.
//!
//! # The one design decision, and why it is not `CombinedIncrementalLia`
//!
//! [`crate::combined_theory_lia::CombinedIncrementalLia`] already implements
//! [`TheorySolver`] and already performs a real `Nelson–Oppen` combination of
//! these two theories. It is **not** what this module wraps, and the reason is
//! structural rather than a preference.
//!
//! `CombinedIncrementalLia::build` (`combined_theory_lia.rs:663`) computes the
//! shared-interface pairs **once, up front** from the full atom set
//! (`combined_theory_lia.rs:686-687`) and then constructs both sub-theories over
//! a *combined* atom list that interleaves three synthetic order/equality atoms
//! per interface pair (`combined_theory_lia.rs:713-730`). Two consequences make
//! it unusable for a set that grows after construction:
//!
//! 1. A new atom can propose a new interface pair, which appends three more
//!    synthetic atoms — so the combined index space is not append-only in the
//!    original atoms. Every clause already in the session's SAT database was
//!    built against the old indices.
//! 2. Those pairs come with `structural_clauses` (`combined_theory_lia.rs:781`)
//!    — totality plus three mutual exclusions per pair — which a growing session
//!    would have to insert into a clause database that is mid-search.
//!
//! So this module composes the two theories **side by side** over one shared
//! atom index space and propagates no interface equalities between them. That
//! is an *incompleteness*, not an unsoundness, and the incompleteness is free
//! here for a reason specific to this caller: the session's `Sat` is **never a
//! verdict**. `qinst_egraph`'s session reports only refutations, and even those
//! are re-established by `replay_online_refutation` over the same ground set
//! with the ordinary cold route before they become the answer. A combination
//! that misses a conflict costs a refutation; it cannot manufacture one.
//!
//! Adding the interface layer is the named next increment, and it is a real one:
//! it is what would let the session refute `f(x) = f(y)` against `x < y ∧ y < x`
//! -style goals that need both theories at once.
//!
//! # Why there is no atom index mapping
//!
//! Both sub-theories were already built to tolerate an atom they cannot
//! represent, because both were written to keep their indices aligned with a
//! caller's Boolean variable numbering:
//!
//! - [`EufTheory`] stores `None` sides for a non-equality atom and asserting one
//!   is a congruence no-op (`euf_egraph.rs:477-479`).
//! - [`LiaTheory`] classifies a non-`LIA` atom as `AtomKind::Unsupported` and
//!   asserting one adds no constraint (`lia_online.rs:111-113`).
//!
//! So composite atom `i` is `EUF` atom `i` **and** `LIA` atom `i`, and a
//! conflict core from either sub-theory is already in composite indices. There
//! is no translation step to get wrong. An integer equality is registered in
//! both and is seen by both, which is the one place the two theories genuinely
//! agree on a shape and is exactly where that is wanted.
//!
//! # How arithmetic is retracted on backjump
//!
//! The brief for this work expected a bound trail that has to be unwound.
//! There is none, and the reason is a property of [`LiaTheory`] worth stating
//! because it is what makes this module small:
//!
//! `IntSimplexEngine::sync` (`lia_online.rs:359-388`) reconciles the engine's
//! imposed bounds against the live set by retracting a diverging suffix and
//! asserting the remainder, and its own doc says the result is *"a pure function
//! of `live` — no hidden coupling to call order"*. `live` is derived from
//! `LiaTheory::assigned`, and `LiaTheory::pop` (`lia_online.rs:1787-1795`)
//! unassigns every atom back to the `push` marker. So a bound asserted under a
//! decision is retracted by the atom's assignment disappearing, at the next
//! check, with no bound trail to maintain.
//!
//! **This is load-bearing and is what the mutation suite aims at.** Removing
//! this module's `lia.pop()` forwarding leaves the arithmetic assignments from a
//! backjumped-over branch live, and the next feasibility check then refutes a
//! set the search has not actually asserted — a wrong `unsat`.
//!
//! [ADR-2124]: ../../../docs/research/09-decisions/adr-2124-incremental-ground-closure-for-quantifier-instances.md

use std::time::Instant;

use axeyum_ir::{Op, TermArena, TermId, TermNode};

use crate::euf_egraph::{
    EufTheory, ExplanationId, FinalCheckOutcome, PropagationQueue, TheoryLit, TheoryProp,
    TheorySolver,
};
use crate::lia_online::LiaTheory;

/// Whether `term` is an atom shape the `LIA` sub-theory can host as a real
/// constraint rather than as a no-op.
///
/// This is deliberately **narrower** than `lia_online::classify`: it names only
/// the order atoms. An integer equality is `AtomKind::Equality` there and is
/// hosted too, but it is *also* an `EUF` atom, so it already reaches the session
/// through the ordinary equality route and does not need this predicate to let
/// it in. What this predicate decides is the one question the session asks:
/// "is this a Boolean-position term the `EUF` encoder has no arm for that the
/// arithmetic theory can nonetheless refute through?"
///
/// Read off `lia_online::classify` (`lia_online.rs:1835-1844`) rather than
/// recalled — the same discipline `online_opaque_clause_atom` records for the
/// connective list it got wrong once.
pub(crate) fn session_lia_hostable_atom(arena: &TermArena, term: TermId) -> bool {
    matches!(
        arena.node(term),
        TermNode::App {
            op: Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe,
            ..
        }
    )
}

/// Appends every `LIA`-hostable order atom reachable from `term` that is not
/// already registered, in a deterministic traversal order (ADR-2130).
///
/// # Why the INITIAL ground set needs this and not just the instances
///
/// The session's atom list comes from `collect_euf_atoms`, which by
/// construction collects only the shapes the congruence closure owns. An
/// arithmetic comparison in the ORIGINAL ground set is therefore not an atom,
/// and `Encoder::encode` reaches its abstraction arm and spends an opaque
/// variable on it — so the arithmetic sub-theory would never see the atom no
/// matter what the session did with later instances.
///
/// That is not a corner: measured on ADR-2124's ground-check population
/// (`bench-results/quant-session-arith-20260916/SIZING-ledger.txt`), **53 of the
/// 77 arithmetic-bearing files carry a comparison in a ground position** and
/// only 24 acquire one solely through an instance. Registering here is what
/// reaches the larger half.
///
/// Registered atoms are what `Encoder::encode` looks up first
/// (`euf_egraph.rs:2216-2218`), so appending a term to the atom list is exactly
/// what moves it from "opaque variable" to "theory atom". `EufTheory::new`
/// stores `None` sides for it (it is not an equality), which is the same inert
/// slot [`EufTheory::add_atom_or_inert_at_root`] gives a later one, and
/// `LiaTheory` classifies it as an order atom and builds its row.
pub(crate) fn collect_session_lia_atoms(
    arena: &TermArena,
    term: TermId,
    out: &mut Vec<TermId>,
    seen: &mut std::collections::HashSet<TermId>,
) {
    if !seen.insert(term) {
        return;
    }
    if session_lia_hostable_atom(arena, term) {
        out.push(term);
    }
    if let TermNode::App { args, .. } = arena.node(term) {
        let args = args.clone();
        for arg in args {
            collect_session_lia_atoms(arena, arg, out, seen);
        }
    }
}

/// `EUF` plus an optional `LIA` sub-theory over one shared atom index space.
///
/// With `lia` absent this forwards every call to [`EufTheory`] and is behaviour-
/// identical to using that theory directly — which is what ground-session levels
/// 0 and 1 do, so those levels are unchanged by this type existing.
pub(crate) struct EufLiaSessionTheory {
    euf: EufTheory,
    /// The arithmetic sub-theory, present only at ground-session level 2.
    ///
    /// `None` is not "no arithmetic atoms yet" — it is "this session does not
    /// host arithmetic at all". The two are different and collapsing them would
    /// silently turn a level-2 session into a level-1 one.
    lia: Option<LiaTheory>,
    /// Every atom the session has registered, in composite index order. Kept
    /// even when `lia` is `None` so a rebuild has the whole list; it is the
    /// session's `atom_terms` mirrored, not a second source of truth for it.
    atom_terms: Vec<TermId>,
    /// Composite atoms registered since `lia` was last rebuilt. While this is
    /// nonzero the `LIA` sub-theory's index space is SHORTER than the composite
    /// one and every forward to it must be bounds-guarded.
    lia_pending: usize,
    /// A conflict found while replaying root assignments into a rebuilt `LIA`
    /// sub-theory, to be reported from the next [`TheorySolver::assert`].
    ///
    /// A rebuild happens between solves, where there is no caller to return a
    /// conflict to. Dropping it would be sound (a lost refutation is a
    /// completeness loss) but it is free to keep, and a stored root conflict is
    /// a valid lemma at any later point because it is over root assignments.
    pending_root_conflict: Option<Vec<TheoryLit>>,
    /// Wall-clock bound handed to a rebuilt `LIA` sub-theory, so a rebuild does
    /// not silently drop the session's deadline.
    deadline: Option<Instant>,
    /// How many times the `LIA` sub-theory has been rebuilt, for the trace.
    lia_rebuilds: usize,
}

impl EufLiaSessionTheory {
    /// An `EUF`-only session theory: levels 0 and 1.
    pub(crate) fn euf_only(euf: EufTheory, atom_terms: Vec<TermId>) -> Self {
        Self {
            euf,
            lia: None,
            atom_terms,
            lia_pending: 0,
            pending_root_conflict: None,
            deadline: None,
            lia_rebuilds: 0,
        }
    }

    /// An `EUF` + `LIA` session theory: level 2.
    ///
    /// Returns an `EUF`-only theory when the arithmetic sub-theory cannot be
    /// built over `atom_terms`. That is a decline to *host*, never a decline to
    /// *exist*: the session stays live on the `EUF` half, which is strictly
    /// better than the historical behaviour of refusing the whole session.
    pub(crate) fn euf_with_lia(
        arena: &TermArena,
        euf: EufTheory,
        atom_terms: Vec<TermId>,
        deadline: Option<Instant>,
    ) -> Self {
        // `new_with_opaque_apps`, NOT `new`, and the difference decides whether
        // this lever can move anything at all. A `UFLIA` arithmetic atom almost
        // always mentions an Int-sorted UF application (`(< (f a) 5)`); plain
        // `LiaTheory::new` cannot build a row for one, so the atom would land as
        // `AtomRow::None` and the theory would host it as a NO-OP -- an
        // arithmetic theory that refuses exactly the arithmetic this lane
        // exists for.
        //
        // The opaque-app constructor treats each Int-sorted application as its
        // own integer variable. That is an OVER-approximation of the model
        // space -- it forgets that `a = b` forces `f(a) = f(b)` -- so it can
        // only ever LOSE conflicts, never invent one, which is why its own doc
        // calls it an "UNSAT-oriented UFLIA combination hook". Its stated cost
        // is that a satisfiable opaque abstraction is model-incomplete, and
        // that cost is zero here: this session's `Sat` is not a verdict.
        let lia = LiaTheory::new_with_opaque_apps(arena, &atom_terms).with_deadline(deadline);
        Self {
            euf,
            lia: Some(lia),
            atom_terms,
            lia_pending: 0,
            pending_root_conflict: None,
            deadline,
            lia_rebuilds: 0,
        }
    }

    /// Whether this theory hosts arithmetic at all.
    pub(crate) fn hosts_arithmetic(&self) -> bool {
        self.lia.is_some()
    }

    /// How many times the arithmetic sub-theory has been rebuilt.
    pub(crate) fn lia_rebuild_count(&self) -> usize {
        self.lia_rebuilds
    }

    /// The composite atom count.
    pub(crate) fn atom_count(&self) -> usize {
        self.atom_terms.len()
    }

    /// Registers `atom_term` at the next composite index, at the root scope.
    ///
    /// The `EUF` half takes the atom when it has a shape it can represent and an
    /// inert slot otherwise, so the index space stays dense either way. The
    /// `LIA` half is not rebuilt here — see [`Self::flush_pending_atoms`].
    ///
    /// # Errors
    ///
    /// When the `EUF` half refuses the registration, which it does outside the
    /// root scope. The caller must then abandon the session rather than continue
    /// with a half-registered atom.
    pub(crate) fn add_atom_at_root(
        &mut self,
        arena: &TermArena,
        atom_term: TermId,
    ) -> Result<usize, &'static str> {
        let expected = self.atom_terms.len();
        // WHICH `EUF` registration is used is a behaviour difference between the
        // levels, not a detail, and getting it wrong would have changed the
        // SHIPPED arm.
        //
        // Historically a Boolean-position term the congruence closure has no
        // opinion about reached `EufTheory::add_atom_at_root`, was REFUSED, and
        // the refusal disabled the whole session -- which is exactly how level 0
        // behaves and what ADR-2124's A/B arm A measured. Accepting an inert
        // slot unconditionally would keep the session alive on a file where the
        // shipped build abandons it, so levels 0 and 1 would no longer be byte
        // for byte the historical behaviour and every A/B against them would be
        // measuring two changes at once.
        //
        // So the inert slot is offered ONLY where it buys something: a session
        // that hosts arithmetic, for an atom the arithmetic theory can actually
        // constrain. Everything else keeps the strict registration and the
        // historical refusal.
        let inert_ok = self.lia.is_some() && session_lia_hostable_atom(arena, atom_term);
        let atom = if inert_ok {
            self.euf.add_atom_or_inert_at_root(arena, atom_term)?
        } else {
            self.euf.add_atom_at_root(arena, atom_term)?
        };
        if atom != expected {
            return Err("EUF atom index diverged from the composite index space");
        }
        self.atom_terms.push(atom_term);
        if self.lia.is_some() {
            self.lia_pending += 1;
        }
        Ok(atom)
    }

    /// Rebuilds the `LIA` sub-theory over the grown atom list, if it grew.
    ///
    /// # Why a rebuild and not an append
    ///
    /// `LiaTheory` freezes three things at construction that an appended atom
    /// would have to reach into: the simplex tableau built by
    /// `build_int_simplex_engine` (`lia_online.rs:420-455`), whose row set and
    /// column count go into `simplex::Incremental::new` and for which
    /// `simplex::Incremental` exposes no row- or column-append method at all;
    /// the warm decider's literal table, whose own doc says the key table *"must
    /// not change for the life of the decider"* (`lra/warm.rs:381-383`); and the
    /// theory's **owned clone of the arena**, which carries `BoolNot` nodes at
    /// ids the caller's arena does not have, so it cannot simply be replaced by
    /// a newer clone of the caller's.
    ///
    /// Rebuilding sidesteps all three and is correct for a reason that is not
    /// obvious and is the whole argument for this design: the simplex's imposed
    /// bounds are **derived**, not accumulated. `IntSimplexEngine::sync`
    /// reconciles them against the live set on every check and is documented as
    /// a pure function of it, so a fresh engine with no bounds imposed and the
    /// same assignments reaches the same state on its next check.
    ///
    /// What a rebuild costs is one arena clone and one tableau build per growth
    /// event. Growth events are per instantiation *round*, not per literal — the
    /// session registers a whole batch of instance atoms and then solves once —
    /// which is why this is deferred to an explicit flush instead of running
    /// inside [`Self::add_atom_at_root`].
    ///
    /// **This is not the fully incremental theory and the ADR does not claim it
    /// is.** The Boolean search, the clause database, the learned clauses and
    /// the `EUF` e-graph all stay warm across a growth event; the arithmetic
    /// tableau does not. A real `simplex::Incremental::add_row` is the named
    /// next increment.
    pub(crate) fn flush_pending_atoms(&mut self, arena: &TermArena) {
        if self.lia_pending == 0 {
            return;
        }
        let Some(old) = self.lia.as_ref() else {
            self.lia_pending = 0;
            return;
        };
        // Snapshot the root assignments before the old theory is dropped. Only
        // root assignments can exist here: a flush runs between solves, after
        // the session has unwound to root, so the LIA trail is empty. The
        // snapshot is taken through the public accessor rather than by
        // remembering what was asserted, so it cannot drift from the theory.
        let root_assignments = old.root_assignments();
        let mut rebuilt =
            LiaTheory::new_with_opaque_apps(arena, &self.atom_terms).with_deadline(self.deadline);
        let mut conflict = None;
        for &(atom, value) in &root_assignments {
            if let Err(core) = rebuilt.assert(atom, value) {
                // A genuine root-level refutation. Keep the FIRST one: later
                // asserts run against an already-inconsistent state and their
                // cores are not more informative.
                conflict.get_or_insert(core);
            }
        }
        self.lia = Some(rebuilt);
        self.lia_pending = 0;
        self.lia_rebuilds += 1;
        if let Some(core) = conflict {
            self.pending_root_conflict.get_or_insert(core);
        }
    }

    /// Whether the `LIA` sub-theory currently covers composite atom `atom`.
    ///
    /// False while a growth event is un-flushed. A forward to an atom the
    /// sub-theory does not have would index out of range, so this is checked
    /// rather than assumed even though the session always flushes before
    /// solving.
    fn lia_covers(&self, atom: usize) -> bool {
        atom < self.atom_terms.len() - self.lia_pending
    }
}

impl TheorySolver for EufLiaSessionTheory {
    fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        if let Some(core) = self.pending_root_conflict.take() {
            return Err(core);
        }
        self.euf.assert(atom, value)?;
        if self.lia_covers(atom)
            && let Some(lia) = self.lia.as_mut()
        {
            lia.assert(atom, value)?;
        }
        Ok(())
    }

    fn push(&mut self) {
        self.euf.push();
        if let Some(lia) = self.lia.as_mut() {
            lia.push();
        }
    }

    /// Undoes both halves in lockstep.
    ///
    /// **The `LIA` half is what retracts the arithmetic bounds**, and not by
    /// unwinding a bound trail: unassigning the atoms shrinks the live set, and
    /// `IntSimplexEngine::sync` re-derives the imposed bounds from it on the
    /// next check. Dropping this forward leaves a backjumped-over branch's
    /// arithmetic asserted and the next check then refutes a set the search
    /// never asserted — a wrong `unsat`, and the mutation suite's target.
    fn pop(&mut self) {
        self.euf.pop();
        if let Some(lia) = self.lia.as_mut() {
            lia.pop();
        }
    }

    fn propagate(&self) -> Vec<TheoryProp> {
        let mut props = self.euf.propagate();
        if let Some(lia) = self.lia.as_ref()
            && self.lia_pending == 0
        {
            props.extend(lia.propagate());
        }
        props
    }

    fn final_check(&mut self) -> FinalCheckOutcome {
        match self.euf.final_check() {
            FinalCheckOutcome::Sat => {}
            other => return other,
        }
        if let Some(lia) = self.lia.as_mut()
            && self.lia_pending == 0
        {
            return lia.final_check();
        }
        FinalCheckOutcome::Sat
    }

    fn propagate_into(&mut self, queue: &mut PropagationQueue) {
        for prop in self.propagate() {
            queue.push_eager(prop.lit, prop.reason);
        }
    }

    fn explain(&mut self, handle: ExplanationId) -> Option<Vec<TheoryLit>> {
        // Neither sub-theory emits a deferred handle today (both take the
        // trait's `None` default), so a handle reaching here is a driver bug
        // rather than a shape to route. Returning `None` is what the driver
        // treats as "abandon and report Unknown", which is the safe answer.
        let _ = handle;
        None
    }

    /// Always `0`.
    ///
    /// **This is deliberate and is a soundness point, not an omission.** The
    /// warm route this theory serves registers atoms through the DRIVER-side
    /// channel — `WarmNativeCdclT::add_theory_variable` paired with
    /// [`Self::add_atom_at_root`] — because `take_new_atoms` is polled by the
    /// core at a propagation fixpoint *inside* a solve and so cannot hand an
    /// index back to a caller that is still building the clause the variable
    /// belongs to (`native_cdclt.rs:340-352`). Reporting a nonzero count here
    /// would make the driver append a SECOND variable for an atom that already
    /// has one, and every later atom index would be off by one.
    fn take_new_atoms(&mut self) -> usize {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Sort;

    /// Three integer order atoms over one symbol, plus one `EUF` equality.
    ///
    /// `a < 1` and `a > 5` are jointly infeasible and INDIVIDUALLY feasible,
    /// which is what lets the retraction fixture below separate "the bound was
    /// retracted" from "the bound was never imposed".
    fn fixture(arena: &mut TermArena) -> (TermId, TermId, TermId, TermId) {
        let a = arena.declare("qsa_a", Sort::Int).unwrap();
        let av = arena.var(a);
        let b = arena.declare("qsa_b", Sort::Int).unwrap();
        let bv = arena.var(b);
        let one = arena.int_const(1);
        let five = arena.int_const(5);
        let zero = arena.int_const(0);
        let a_lt_one = arena.int_lt(av, one).unwrap();
        let a_gt_five = arena.int_gt(av, five).unwrap();
        let a_gt_zero = arena.int_gt(av, zero).unwrap();
        let a_eq_b = arena.eq(av, bv).unwrap();
        (a_lt_one, a_gt_five, a_gt_zero, a_eq_b)
    }

    fn hosted(arena: &TermArena, atoms: &[TermId]) -> EufLiaSessionTheory {
        let euf = EufTheory::new(arena, atoms);
        EufLiaSessionTheory::euf_with_lia(arena, euf, atoms.to_vec(), None)
    }

    fn euf_only(arena: &TermArena, atoms: &[TermId]) -> EufLiaSessionTheory {
        let euf = EufTheory::new(arena, atoms);
        EufLiaSessionTheory::euf_only(euf, atoms.to_vec())
    }

    /// The capability this lane adds, in one assertion — and its negative half.
    ///
    /// `a < 1 ∧ a > 5` is a refutation no congruence closure can find: neither
    /// atom is an equality, so the `EUF` half has no opinion about either. The
    /// `EUF`-only arm must therefore accept both, and the hosted arm must
    /// refuse the second. Asserting only the hosted half would pass against a
    /// theory that had started refusing everything.
    #[test]
    fn hosting_refutes_an_arithmetic_conflict_the_euf_half_cannot_see() {
        let mut arena = TermArena::new();
        let (a_lt_one, a_gt_five, _, a_eq_b) = fixture(&mut arena);
        let atoms = vec![a_eq_b, a_lt_one, a_gt_five];

        let mut bare = euf_only(&arena, &atoms);
        assert!(bare.assert(1, true).is_ok());
        assert!(
            bare.assert(2, true).is_ok(),
            "an EUF-only session has no opinion about two integer comparisons -- \
             if this refuses, the fixture is not measuring the arithmetic"
        );

        let mut both = hosted(&arena, &atoms);
        assert!(both.assert(1, true).is_ok(), "`a < 1` alone is feasible");
        let core = both
            .assert(2, true)
            .expect_err("`a < 1` and `a > 5` are jointly infeasible over the integers");
        assert!(
            !core.is_empty(),
            "a conflict core must name the literals it refutes; an empty core is \
             an unconditional `unsat` and would be a wrong answer"
        );
        assert!(
            core.iter().all(|lit| lit.atom < atoms.len()),
            "every core literal must be a COMPOSITE atom index -- a core in a \
             sub-theory's own numbering would be silently misattributed"
        );
    }

    /// **The soundness fixture, and the mutation suite's target.**
    ///
    /// An arithmetic bound asserted under a decision must be gone once that
    /// decision is backjumped over. There is no bound trail to unwind here: the
    /// simplex's imposed bounds are re-derived from the live assignment set on
    /// every check, so the retraction IS `LiaTheory::pop` unassigning the atom.
    ///
    /// The shape is chosen so the two outcomes are distinguishable. `a > 5` is
    /// asserted under a `push`, then popped. `a < 1` is then asserted at the
    /// root. Each is feasible alone, so an `Ok` here means the popped bound is
    /// really gone; an `Err` means a branch the search abandoned is still
    /// constraining the theory — a refutation of a set nobody asserted, which
    /// reaches the caller as a wrong `unsat`.
    #[test]
    fn pop_retracts_an_arithmetic_bound_a_backjump_undid() {
        let mut arena = TermArena::new();
        let (a_lt_one, a_gt_five, _, a_eq_b) = fixture(&mut arena);
        let atoms = vec![a_eq_b, a_lt_one, a_gt_five];
        let mut theory = hosted(&arena, &atoms);

        theory.push();
        assert!(
            theory.assert(2, true).is_ok(),
            "`a > 5` is feasible on its own -- if this refuses, the fixture \
             cannot tell a retracted bound from an unimposed one"
        );
        theory.pop();

        assert!(
            theory.assert(1, true).is_ok(),
            "`a < 1` must be feasible once `a > 5` has been backjumped over; an \
             Err here means the popped branch's bound is still imposed"
        );
    }

    /// Hosting is a REFUTATION capability, never a source of refutations.
    ///
    /// Every atom below is asserted at a value the whole set satisfies
    /// (`a = b`, `a > 0`, `a > 5`, and `a < 1` left false), across a push/pop
    /// cycle so the theory is exercised at more than one scope. Nothing may
    /// refuse.
    #[test]
    fn hosting_never_manufactures_a_conflict_on_a_satisfiable_assignment() {
        let mut arena = TermArena::new();
        let (a_lt_one, a_gt_five, a_gt_zero, a_eq_b) = fixture(&mut arena);
        let atoms = vec![a_eq_b, a_lt_one, a_gt_five, a_gt_zero];
        let mut theory = hosted(&arena, &atoms);

        // a = b, a > 0, a > 5 -- satisfiable at a = b = 6.
        assert!(theory.assert(0, true).is_ok());
        assert!(theory.assert(3, true).is_ok());
        theory.push();
        assert!(theory.assert(2, true).is_ok());
        assert!(
            theory.assert(1, false).is_ok(),
            "`a < 1` asserted FALSE is `a >= 1`, which a = 6 satisfies"
        );
        theory.pop();
        assert!(
            theory.assert(1, false).is_ok(),
            "the same assignment must stay feasible after the scope closes"
        );
    }

    /// A rebuild must not lose what was already asserted at the root.
    ///
    /// The arithmetic sub-theory is rebuilt whole when the atom list grows, so
    /// the root assignments are replayed into the replacement. If they were
    /// dropped, the theory would silently forget `a > 5` and accept `a < 1`
    /// afterwards — a lost refutation rather than a wrong one, but a lever that
    /// loses its refutations exactly when an instance lands is a lever that
    /// measures as doing nothing.
    #[test]
    fn a_rebuild_replays_the_root_assignments_into_the_new_sub_theory() {
        let mut arena = TermArena::new();
        let (a_lt_one, a_gt_five, a_gt_zero, a_eq_b) = fixture(&mut arena);
        let atoms = vec![a_eq_b, a_gt_five];
        let mut theory = hosted(&arena, &atoms);
        assert!(theory.assert(1, true).is_ok(), "`a > 5` at the root");

        // An instance lands, registering two more atoms.
        assert_eq!(theory.add_atom_at_root(&arena, a_gt_zero).unwrap(), 2);
        assert_eq!(theory.add_atom_at_root(&arena, a_lt_one).unwrap(), 3);
        assert_eq!(
            theory.lia_rebuild_count(),
            0,
            "growth alone rebuilds nothing"
        );
        theory.flush_pending_atoms(&arena);
        assert_eq!(
            theory.lia_rebuild_count(),
            1,
            "one rebuild per flush, not per atom"
        );
        assert_eq!(theory.atom_count(), 4);

        assert!(
            theory.assert(3, true).is_err(),
            "`a < 1` must still be refuted by the root-level `a > 5` the rebuild \
             replayed; an Ok here means the rebuild forgot it"
        );
    }

    /// A flush that added no atom rebuilds nothing.
    ///
    /// A rebuild costs an arena clone and a whole tableau build. The session
    /// flushes once per admitted batch whether or not the batch registered an
    /// atom, so an unconditional rebuild would pay that price every round.
    #[test]
    fn a_flush_with_no_pending_atom_is_a_no_op() {
        let mut arena = TermArena::new();
        let (_, a_gt_five, _, a_eq_b) = fixture(&mut arena);
        let atoms = vec![a_eq_b, a_gt_five];
        let mut theory = hosted(&arena, &atoms);
        theory.flush_pending_atoms(&arena);
        theory.flush_pending_atoms(&arena);
        assert_eq!(theory.lia_rebuild_count(), 0);
    }

    /// An `EUF`-only composite must host nothing, and must not start.
    ///
    /// Levels 0 and 1 use this arm, so it is the shipped behaviour. A composite
    /// that quietly built a `LIA` half here would make ADR-2124's A/B arms
    /// measure two changes at once.
    #[test]
    fn the_euf_only_arm_hosts_no_arithmetic_and_never_rebuilds() {
        let mut arena = TermArena::new();
        let (a_lt_one, a_gt_five, _, a_eq_b) = fixture(&mut arena);
        let atoms = vec![a_eq_b, a_lt_one, a_gt_five];
        let mut theory = euf_only(&arena, &atoms);
        assert!(!theory.hosts_arithmetic());
        assert!(
            theory.add_atom_at_root(&arena, a_gt_five).is_err(),
            "without a LIA half an arithmetic atom has no home, and the strict \
             EUF registration must keep refusing it -- that refusal is what \
             disables the session at levels 0 and 1"
        );
        theory.flush_pending_atoms(&arena);
        assert_eq!(theory.lia_rebuild_count(), 0);
    }

    /// `take_new_atoms` must stay `0`.
    ///
    /// The warm route registers through the DRIVER-side channel, so a nonzero
    /// count here would make the core append a SECOND SAT variable for an atom
    /// that already has one and every later atom index would be off by one — a
    /// silent misattribution of asserted literals, not a crash.
    #[test]
    fn take_new_atoms_is_always_zero_because_the_driver_registers() {
        let mut arena = TermArena::new();
        let (a_lt_one, a_gt_five, _, a_eq_b) = fixture(&mut arena);
        let atoms = vec![a_eq_b, a_gt_five];
        let mut theory = hosted(&arena, &atoms);
        assert_eq!(theory.take_new_atoms(), 0);
        theory.add_atom_at_root(&arena, a_lt_one).unwrap();
        theory.flush_pending_atoms(&arena);
        assert_eq!(
            theory.take_new_atoms(),
            0,
            "registering an atom must NOT be reported through this channel"
        );
    }

    /// The hostable-atom predicate names order atoms and nothing else.
    ///
    /// Derived from the shapes rather than asserted as a list: an integer
    /// equality is hosted too, but it reaches the theory as an `EUF` atom and
    /// must not be pulled out of the abstraction by this predicate.
    #[test]
    fn only_order_atoms_are_pulled_back_from_the_abstraction() {
        let mut arena = TermArena::new();
        let (a_lt_one, a_gt_five, a_gt_zero, a_eq_b) = fixture(&mut arena);
        for term in [a_lt_one, a_gt_five, a_gt_zero] {
            assert!(session_lia_hostable_atom(&arena, term));
        }
        assert!(
            !session_lia_hostable_atom(&arena, a_eq_b),
            "an equality already has an EUF arm; pulling it out of the \
             abstraction here would be a second route to the same atom"
        );
    }
}
