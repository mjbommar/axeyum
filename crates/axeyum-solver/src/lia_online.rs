//! Online (incremental, backtrackable) linear integer arithmetic (`QF_LIA`)
//! theory solver — the integer analogue of the online [`crate::lra_online`]
//! solver (Track 1, P1.6).
//!
//! The offline [`crate::lra::check_with_lia_simplex`] path decides a *conjunction*
//! of linear-integer atoms by branch-and-bound over the exact-rational simplex
//! (with gcd-aware strict-integer tightening and Gomory cuts), sound for both
//! `sat` and `unsat`. This module adds the **warm** counterpart: a [`LiaTheory`]
//! keeping a backtrackable stack of asserted linear-integer atoms that a
//! `DPLL(T)` loop drives via the same [`TheorySolver`] trait the online
//! [`crate::euf_egraph::EufTheory`] and [`crate::lra_online::LraTheory`] implement
//! — `assert` / `push` / `pop` in lockstep with the search's decision levels.
//!
//! **The engine is re-decided-incremental.** Exactly as
//! [`crate::lra_online::LraTheory`] re-runs Fourier–Motzkin over its live stack,
//! [`LiaTheory`] keeps a backtrackable list of asserted atom literals and, on each
//! `assert` / feasibility query, **re-decides integer feasibility** of the
//! currently-asserted set by reconstructing a conjunctive `QF_LIA` IR term and
//! handing it to the trusted offline [`crate::lra::check_with_lia_simplex`]. This
//! reuses the trusted decider verbatim — including its **strict integer
//! tightening** (`0 < x ∧ x < 1` is integer-`unsat` though rationally-`sat`,
//! handled by the offline gcd-aware tightening / branch-and-bound), the whole
//! point of `LIA` over `LRA`. On infeasibility the conflict core is a
//! **deletion-minimized** subset of the asserted literals that stays
//! `check_with_lia_simplex`-`unsat` (a sound, typically small core, the
//! integer analogue of the Farkas core).
//!
//! [`LiaTheory`] implements [`TheorySolver`]:
//! - [`LiaTheory::assert`] records an order/equality atom (true or false) on the
//!   trail and re-decides integer feasibility of the live set. On infeasibility it
//!   returns the deletion-minimized conflict core.
//! - [`LiaTheory::push`] / [`LiaTheory::pop`] snapshot and restore the trail
//!   length, so a backtrack drops exactly the literals added since the matching
//!   `push`.
//! - [`LiaTheory::propagate`] mirrors [`crate::lra_online::LraTheory::propagate`]:
//!   the **negation probe**, but tested with the *cheap, sound* **LP relaxation**
//!   rather than a full integer solve. For each unassigned tracked order atom it
//!   appends the atom's opposite-polarity constraint to the live conjunction and
//!   asks [`crate::lra::lp_relaxation_feasibility`]; an `Infeasible` relaxation
//!   *over the reals* implies the integer system is infeasible too (integer
//!   solutions are a subset of real ones), so the atom is **entailed over ℤ** —
//!   emitted as a [`TheoryProp`] whose `reason` is the **asserted-only** core. An
//!   LP-`Feasible` probe is inconclusive about ℤ → skip (no fabricated
//!   propagation). The relaxation skips integer tightening / Gomory cuts /
//!   branch-and-bound, so it stays far cheaper than the per-`assert` integer
//!   feasibility decision.
//!
//! [`check_qf_lia_online`] wires [`LiaTheory`] into a self-contained `DPLL(T)`
//! search over the Boolean skeleton (the same shape as
//! [`crate::lra_online::check_qf_lra_online`]). It is the warm analogue of the
//! offline [`crate::lra::check_with_lia_simplex`] / [`crate::dpll_lia`] paths.
//!
//! **Trust.** This is a decision procedure; its soundness is established by the
//! differential gate against the trusted offline
//! [`crate::lra::check_with_lia_simplex`] (see `tests/lia_online.rs`) plus model
//! replay, not by a post-hoc re-check. Every `sat` model the driver returns is
//! replayed through the ground evaluator against the *original* assertions — with
//! **integer** values — before it is handed back, so neither the Boolean search
//! nor the incremental theory can yield an unsound `sat`. Every `unsat` is only
//! ever reported at a root-level conflict whose core is itself
//! `check_with_lia_simplex`-`unsat`. Any overflow / resource limit inside the
//! offline decider degrades the *current feasibility check* to "don't know"
//! (treated as feasible — never a wrong `unsat`), which the driver carries to a
//! conservative [`CheckResult::Unknown`].

use std::collections::{HashMap, HashSet};

use axeyum_ir::{Assignment, Op, Sort, TermArena, TermId, TermNode, Value, eval};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::euf_egraph::{TheoryLit, TheoryProp, TheorySolver};
use crate::lra::{LpRelaxation, check_with_lia_simplex, lp_relaxation_feasibility};
use crate::model::Model;

/// The kind of a registered atom, used to reconstruct the live conjunctive
/// `QF_LIA` term the offline decider consumes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AtomKind {
    /// A linear-integer order atom (`<,<=,>,>=`): contributes its
    /// polarity-applied `TermId` in either polarity.
    Order,
    /// A linear-integer equality atom: contributes when asserted **true**; asserted
    /// **false** (an integer disequality) it is a no-op — the conjunctive offline
    /// decider declines a bare disequality, so the theory records the assignment
    /// but contributes no constraint (sound: it never makes a feasible state
    /// infeasible, so it cannot cause a wrong `unsat`).
    Equality,
    /// A non-`LIA` atom (BV / nonlinear / non-integer): asserting it is a no-op,
    /// keeping atom indices aligned with the caller's numbering.
    Unsupported,
}

/// Online (incremental, backtrackable) `QF_LIA` theory solver over a stack of
/// asserted linear-integer atoms. Implements [`TheorySolver`] so a `DPLL(T)` loop
/// drives it: the SAT search asserts atoms as its trail grows, backtracks in
/// lockstep via [`push`](TheorySolver::push) / [`pop`](TheorySolver::pop), and
/// learns the explained conflict on infeasibility.
///
/// Feasibility is **re-decided** by the trusted offline
/// [`crate::lra::check_with_lia_simplex`] over a conjunctive `QF_LIA` term
/// reconstructed from the currently-asserted atom literals; on infeasibility the
/// conflict core is a deletion-minimized subset that stays
/// `check_with_lia_simplex`-`unsat`.
pub struct LiaTheory {
    /// The atom terms the theory was built over (atom index → term).
    atom_terms: Vec<TermId>,
    /// Per registered atom: how its polarities translate to live constraints.
    kinds: Vec<AtomKind>,
    /// Per atom index: the value it is currently asserted at (`None` if
    /// unassigned), so a re-assert of the same value is idempotent.
    assigned: Vec<Option<bool>>,
    /// Atom indices assigned since the start, in order — the backtrack log.
    assigned_log: Vec<usize>,
    /// Backtrack trail: per [`push`](TheorySolver::push), the `assigned_log`
    /// length to restore on the matching [`pop`](TheorySolver::pop).
    trail: Vec<usize>,
    /// Cloneable copy of the arena, so feasibility can reconstruct live terms
    /// (the offline decider needs an arena; building polarity-applied
    /// `BoolNot`/conjunction terms can grow it, hence an owned clone).
    arena: TermArena,
}

/// Outcome of an incremental integer-feasibility check over the asserted atoms.
enum Feasibility {
    /// The asserted constraints are jointly integer-feasible.
    Sat,
    /// Integer-infeasible; the asserted atom literals participating in a
    /// deletion-minimized infeasible subset (the conflict core).
    Unsat(Vec<TheoryLit>),
    /// The offline decider returned `unknown` (resource limit / overflow / outside
    /// its fragment): inconclusive. Treated as feasible by the caller (never a
    /// wrong `unsat`).
    Unknown,
}

impl LiaTheory {
    /// Builds an online `LIA` theory over the given atom terms. Each `(< a b)` /
    /// `(<= a b)` / `(> a b)` / `(>= a b)` and each integer `(= a b)` registers as
    /// a constraint atom; any other atom registers as a no-op so indices stay
    /// aligned with the caller's atom numbering.
    #[must_use]
    pub fn new(arena: &TermArena, atom_terms: &[TermId]) -> Self {
        let kinds: Vec<AtomKind> = atom_terms.iter().map(|&t| classify(arena, t)).collect();
        let count = atom_terms.len();
        Self {
            atom_terms: atom_terms.to_vec(),
            kinds,
            assigned: vec![None; count],
            assigned_log: Vec::new(),
            trail: Vec::new(),
            arena: arena.clone(),
        }
    }

    /// Whether atom `index` is a `LIA` order/equality atom this theory tracks.
    /// (`false` for a registered no-op, e.g. a BV or non-integer atom.)
    #[must_use]
    pub fn tracks(&self, index: usize) -> bool {
        self.kinds
            .get(index)
            .is_some_and(|k| !matches!(k, AtomKind::Unsupported))
    }

    /// An integer witness for the currently-asserted constraints, over the original
    /// symbols, or `None` if the live system is infeasible / inconclusive (resource
    /// limit / overflow / outside the offline fragment). The crate-internal reader the
    /// online theory-combination path ([`crate::uflia_online`]) uses to build the `LIA`
    /// half of a combined model at a consistent leaf — the same reconstruction
    /// [`theory_model`] performs (re-running the trusted offline
    /// [`check_with_lia_simplex`] over the live conjunction and lifting its `sat`
    /// model). Soundness rests on the caller replaying the assembled model against the
    /// original assertions.
    #[must_use]
    pub(crate) fn integer_model(&self) -> Option<Model> {
        theory_model(self)
    }

    /// The currently-asserted atom literals that contribute a live constraint
    /// (order atoms in either polarity, equality atoms asserted true). Equality
    /// atoms asserted false and unsupported atoms contribute nothing.
    fn live_lits(&self) -> Vec<TheoryLit> {
        let mut lits = Vec::new();
        for &atom in &self.assigned_log {
            let Some(value) = self.assigned[atom] else {
                continue;
            };
            match self.kinds[atom] {
                // Order atoms contribute in either polarity.
                AtomKind::Order => lits.push(TheoryLit { atom, value }),
                // Equality contributes only when true; false (disequality) is a
                // sound no-op the conjunctive decider cannot represent.
                AtomKind::Equality if value => lits.push(TheoryLit { atom, value }),
                AtomKind::Equality | AtomKind::Unsupported => {}
            }
        }
        lits
    }

    /// Builds the conjunctive `QF_LIA` term for a set of atom literals: each atom
    /// applied at its polarity (`atom` when true, `not atom` when false). Returns
    /// the per-literal asserted term plus the arena it lives in (a working clone,
    /// so building polarity terms never mutates the theory's own arena across a
    /// feasibility check). `None` if a `BoolNot` build overflows the arena (never
    /// expected for well-formed atoms — degrades to `Unknown`).
    fn live_terms(&self, lits: &[TheoryLit]) -> Option<(TermArena, Vec<TermId>)> {
        let mut arena = self.arena.clone();
        let mut terms = Vec::with_capacity(lits.len());
        for lit in lits {
            let atom = self.atom_terms[lit.atom];
            let term = if lit.value {
                atom
            } else {
                arena.not(atom).ok()?
            };
            terms.push(term);
        }
        Some((arena, terms))
    }

    /// Re-decides integer feasibility of the currently-asserted constraint atoms
    /// by the trusted offline [`check_with_lia_simplex`]. On `unsat`, returns a
    /// deletion-minimized infeasible subset as the conflict core.
    fn feasibility(&self) -> Feasibility {
        let lits = self.live_lits();
        if lits.is_empty() {
            return Feasibility::Sat;
        }
        let Some((arena, terms)) = self.live_terms(&lits) else {
            return Feasibility::Unknown;
        };
        match check_with_lia_simplex(&arena, &terms) {
            Ok(CheckResult::Sat(_)) => Feasibility::Sat,
            Ok(CheckResult::Unknown(_)) | Err(_) => Feasibility::Unknown,
            Ok(CheckResult::Unsat) => Feasibility::Unsat(minimize_core(&arena, &lits, &terms)),
        }
    }

    /// Sound `LIA` theory propagation by the **LP-relaxation negation probe** — the
    /// integer analogue of [`crate::lra_online::LraTheory::propagate`], made cheap by
    /// testing entailment with the real relaxation rather than a full integer solve.
    ///
    /// For each unassigned tracked order atom: build the live asserted conjunction,
    /// append the atom's *opposite* polarity, and ask the LP relaxation. If the
    /// relaxation is infeasible *over the reals*, the integer system is infeasible
    /// too (integer points ⊆ real points), so the atom is **entailed over ℤ** at the
    /// tested polarity — emit a [`TheoryProp`] whose `reason` is the **asserted-only**
    /// (and deletion-minimized) core. An LP-`Feasible` probe is inconclusive about ℤ,
    /// and an `Unknown` (overflow / outside the fragment / backstop) probe declines:
    /// either way nothing is emitted — a sound under-approximation that **never**
    /// fabricates a propagation. Equality atoms are skipped (their negation is a
    /// disjunction the conjunctive relaxation cannot represent — the same restriction
    /// [`TheorySolver::assert`] makes).
    #[must_use]
    pub fn propagate(&self) -> Vec<TheoryProp> {
        let asserted = self.live_lits();
        let mut out = Vec::new();
        for atom in 0..self.kinds.len() {
            if self.assigned.get(atom).copied().flatten().is_some() {
                continue; // already decided by the search
            }
            if !matches!(self.kinds[atom], AtomKind::Order) {
                continue; // equality-false is a disjunction; unsupported is a no-op
            }
            // Probe ¬atom (atom false): LP-infeasible ⇒ atom entailed true.
            if let Some(reason) = self.probe_entails(&asserted, atom, false) {
                out.push(TheoryProp {
                    lit: TheoryLit { atom, value: true },
                    reason,
                });
                continue;
            }
            // Probe atom (atom true): LP-infeasible ⇒ ¬atom entailed.
            if let Some(reason) = self.probe_entails(&asserted, atom, true) {
                out.push(TheoryProp {
                    lit: TheoryLit { atom, value: false },
                    reason,
                });
            }
        }
        out
    }

    /// Tests whether the live asserted set plus `atom` at `probe_value` is
    /// LP-relaxation-infeasible (so `atom` is entailed at the *opposite* polarity
    /// over ℤ). On infeasibility returns the **asserted-only**, deletion-minimized
    /// reason (the probed atom excluded); otherwise `None` (feasible or
    /// inconclusive — never a fabrication).
    fn probe_entails(
        &self,
        asserted: &[TheoryLit],
        atom: usize,
        probe_value: bool,
    ) -> Option<Vec<TheoryLit>> {
        let probe = TheoryLit {
            atom,
            value: probe_value,
        };
        if !self.probe_lp_infeasible(asserted, Some(probe)) {
            return None;
        }
        Some(self.minimize_probe_reason(asserted, probe))
    }

    /// Whether the asserted literals `asserted` together with the optional extra
    /// literal `probe` are LP-relaxation-infeasible (and so integer-infeasible).
    /// `false` on LP-feasible *or* inconclusive (overflow / outside the fragment) —
    /// the conservative direction, so a `true` here is always a sound entailment.
    fn probe_lp_infeasible(&self, asserted: &[TheoryLit], probe: Option<TheoryLit>) -> bool {
        let mut lits: Vec<TheoryLit> = asserted.to_vec();
        if let Some(p) = probe {
            lits.push(p);
        }
        let Some((arena, terms)) = self.live_terms(&lits) else {
            return false;
        };
        matches!(
            lp_relaxation_feasibility(&arena, &terms),
            LpRelaxation::Infeasible
        )
    }

    /// Deletion-minimizes the asserted-only reason behind an entailment: greedily
    /// drops asserted literals while `kept ∧ probe` stays LP-infeasible. The result
    /// is a sound (minimal-by-deletion) core — every retained subset is re-checked
    /// LP-infeasible, so the learned lemma `¬(reason ∧ ¬entailed)` is entailed by the
    /// asserted state alone. The `probe` literal is the speculative negation, never
    /// part of the reason.
    fn minimize_probe_reason(&self, asserted: &[TheoryLit], probe: TheoryLit) -> Vec<TheoryLit> {
        let mut keep: Vec<bool> = vec![true; asserted.len()];
        for drop_idx in 0..asserted.len() {
            keep[drop_idx] = false;
            let subset: Vec<TheoryLit> = asserted
                .iter()
                .zip(&keep)
                .filter_map(|(&lit, &k)| k.then_some(lit))
                .collect();
            if self.probe_lp_infeasible(&subset, Some(probe)) {
                // Still entailed without this literal — drop it.
            } else {
                keep[drop_idx] = true; // needed for the refutation; keep it.
            }
        }
        let core: Vec<TheoryLit> = asserted
            .iter()
            .zip(&keep)
            .filter_map(|(&lit, &k)| k.then_some(lit))
            .collect();
        // Fall back to the full asserted set if minimization somehow emptied the
        // core (a refutation resting on no asserted atom would not be a sound
        // propagation, but the caller already confirmed LP-infeasibility *with* the
        // probe; an empty reason here means the probe alone refutes, which the
        // unassigned-atom guard rules out — keep the full set, sound and coarse).
        if core.is_empty() {
            asserted.to_vec()
        } else {
            core
        }
    }
}

impl TheorySolver for LiaTheory {
    /// Asserts atom `index` at `value`, recording it on the trail and re-deciding
    /// integer feasibility of the live set. Returns the deletion-minimized
    /// conflict core on integer-infeasibility.
    ///
    /// An equality atom asserted **false** (integer disequality) is a no-op the
    /// conjunctive offline decider cannot represent; the theory records the
    /// assignment but adds no constraint (sound — it never makes a feasible state
    /// infeasible). The driver in [`check_qf_lia_online`] does not abstract bare
    /// equalities, so equality atoms are only ever asserted true there anyway.
    fn assert(&mut self, index: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        // Idempotent re-assert at the same value.
        if self.assigned.get(index).copied().flatten() == Some(value) {
            return Ok(());
        }
        self.assigned[index] = Some(value);
        self.assigned_log.push(index);

        match self.feasibility() {
            Feasibility::Sat | Feasibility::Unknown => Ok(()),
            Feasibility::Unsat(core) => Err(core),
        }
    }

    /// Saves a backtrack point: the current `assigned_log` length.
    fn push(&mut self) {
        self.trail.push(self.assigned_log.len());
    }

    /// Restores to the most recent [`push`](TheorySolver::push): drops every atom
    /// assignment added since.
    fn pop(&mut self) {
        let Some(log_len) = self.trail.pop() else {
            return;
        };
        while self.assigned_log.len() > log_len {
            let atom = self.assigned_log.pop().expect("log non-empty above marker");
            self.assigned[atom] = None;
        }
    }

    fn propagate(&self) -> Vec<TheoryProp> {
        LiaTheory::propagate(self)
    }
}

/// Classifies one atom term into its [`AtomKind`] for the integer theory.
fn classify(arena: &TermArena, term: TermId) -> AtomKind {
    match arena.node(term) {
        TermNode::App {
            op: Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe,
            ..
        } => AtomKind::Order,
        TermNode::App { op: Op::Eq, args } if is_int(arena, args[0]) => AtomKind::Equality,
        _ => AtomKind::Unsupported,
    }
}

/// Deletion-minimizes an infeasible literal set: greedily drops literals while the
/// remaining subset stays `check_with_lia_simplex`-`unsat`. The result is a sound
/// (minimal-by-deletion) conflict core — a wrong `unsat` is impossible because
/// every returned subset is re-checked `unsat`. `terms[i]` is the
/// polarity-applied term for `lits[i]` in `arena`.
fn minimize_core(arena: &TermArena, lits: &[TheoryLit], terms: &[TermId]) -> Vec<TheoryLit> {
    // Start from the full asserted set; try removing each literal in turn.
    let mut keep: Vec<bool> = vec![true; lits.len()];
    for drop_idx in 0..lits.len() {
        keep[drop_idx] = false;
        let subset: Vec<TermId> = terms
            .iter()
            .zip(&keep)
            .filter_map(|(&t, &k)| k.then_some(t))
            .collect();
        let still_unsat = subset.len() < terms.len()
            && matches!(
                check_with_lia_simplex(arena, &subset),
                Ok(CheckResult::Unsat)
            );
        if !still_unsat {
            // Dropping this literal lost (or could not confirm) the refutation —
            // keep it.
            keep[drop_idx] = true;
        }
    }
    let core: Vec<TheoryLit> = lits
        .iter()
        .zip(&keep)
        .filter_map(|(&lit, &k)| k.then_some(lit))
        .collect();
    // Fall back to the full set if minimization somehow emptied the core (should
    // not happen for a genuine refutation) — a sound, if coarse, conflict.
    if core.is_empty() { lits.to_vec() } else { core }
}

/// Whether `term` is integer-sorted.
fn is_int(arena: &TermArena, term: TermId) -> bool {
    arena.sort_of(term) == Sort::Int
}

// --- The online DPLL(T) driver (a mirror of lra_online::Dpll retargeted to
// --- LiaTheory). ------------------------------------------------------------

/// A CNF literal in the online `DPLL(T)` skeleton: a variable index and polarity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Lit {
    var: usize,
    positive: bool,
}

impl Lit {
    fn negate(self) -> Self {
        Self {
            var: self.var,
            positive: !self.positive,
        }
    }
}

/// How a variable came to be assigned, so backtracking undoes theory state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cause {
    Decision,
    Implied,
}

/// A conflict surfaced by propagation: the falsified clause to analyze, tagged
/// with whether it is a **theory** clause (a theory conflict `¬⋀core`, entailed by
/// the theory alone) or a Boolean input clause. The tag seeds the theory-lemma
/// provenance tracked through 1-UIP resolution.
struct Conflict {
    clause: Vec<Lit>,
    is_theory: bool,
}

/// A self-contained `DPLL(T)` search over the CNF skeleton driving a [`LiaTheory`]
/// online: **1-UIP** theory-conflict learning with non-chronological backjumping,
/// the theory pushed on each decision and popped once per decision crossed when
/// backjumping. Mirrors [`crate::lra_online`]'s `Dpll` retargeted to [`LiaTheory`].
struct Dpll {
    var_count: usize,
    atom_count: usize,
    clauses: Vec<Vec<Lit>>,
    value: Vec<Option<bool>>,
    /// The assignment trail: `(var, value, cause)` in assignment order.
    trail: Vec<(usize, bool, Cause)>,
    /// Per variable: the decision level it was assigned at (valid only while the
    /// variable is assigned).
    level: Vec<usize>,
    /// Per variable: the reason clause that forced it (a clause that, once all its
    /// other literals are false, propagates this variable). `None` for a decision.
    /// Valid only while the variable is assigned.
    reason: Vec<Option<Vec<Lit>>>,
    /// Per variable: whether its reason clause is a *theory* clause (a theory
    /// conflict `¬⋀core` or a theory propagation `¬reason ∨ lit`, both entailed by
    /// the theory alone) rather than a Boolean input clause. A 1-UIP clause resolved
    /// only through theory clauses is itself a theory lemma — the test gate uses
    /// this to pick clauses it can independently re-validate with the trusted offline
    /// integer decider.
    reason_theory: Vec<bool>,
    /// The current decision level (incremented on every decision, restored on
    /// backjump).
    decision_level: usize,
    /// Test-only diagnostics for the 1-UIP path (fires counter and learned-vs-full
    /// conflict-clause lengths). Compiled out of the production library.
    #[cfg(test)]
    diag: Diagnostics,
}

/// Test-only counters proving the 1-UIP analysis fires and that its asserting
/// clauses are shorter than the full `¬⋀core` clause the old chronological scheme
/// would have learned.
#[cfg(test)]
#[derive(Default)]
struct Diagnostics {
    /// The number of 1-UIP analyses run.
    analyze_fires: usize,
    /// Summed length of every learned asserting clause.
    learned_len_total: u64,
    /// Summed length of the corresponding full conflict clause (`¬⋀core`).
    conflict_len_total: u64,
    /// The number of clauses present before any learning (the encoded skeleton);
    /// every clause at or after this index is a learned 1-UIP asserting clause.
    initial_clauses: usize,
    /// Per stored learned clause (aligned with `clauses[initial_clauses..]`):
    /// whether it is a pure theory lemma (entailed by the theory plus the level-0
    /// facts), so the test gate can re-validate it with the integer offline decider.
    lemma_flags: Vec<bool>,
    /// Per stored learned clause: the level-0 atom assignments `(atom, value)` in
    /// force when it was learned — the unconditional facts the lemma rests on, so
    /// the entailment oracle conjoins them with `¬clause`.
    lemma_level0: Vec<Vec<(usize, bool)>>,
}

impl Dpll {
    fn new(var_count: usize, atom_count: usize, clauses: Vec<Vec<Lit>>) -> Self {
        #[cfg(test)]
        let diag = Diagnostics {
            initial_clauses: clauses.len(),
            ..Diagnostics::default()
        };
        Self {
            var_count,
            atom_count,
            clauses,
            value: vec![None; var_count],
            trail: Vec::new(),
            level: vec![0; var_count],
            reason: vec![None; var_count],
            reason_theory: vec![false; var_count],
            decision_level: 0,
            #[cfg(test)]
            diag,
        }
    }

    fn lit_sat(&self, lit: Lit) -> Option<bool> {
        self.value[lit.var].map(|v| v == lit.positive)
    }

    /// The literal currently true for `var` (its trail polarity).
    fn true_literal(&self, var: usize) -> Lit {
        Lit {
            var,
            positive: self.value[var].expect("assigned variable has a value"),
        }
    }

    /// Assigns `var := value` at the current decision level, recording its level and
    /// reason and mirroring a theory atom into [`LiaTheory`]. `reason` is the forcing
    /// clause for a propagation, `None` for a decision.
    fn assign(
        &mut self,
        theory: &mut LiaTheory,
        var: usize,
        value: bool,
        cause: Cause,
        reason: Option<Vec<Lit>>,
        reason_is_theory: bool,
    ) -> Result<(), Vec<TheoryLit>> {
        self.value[var] = Some(value);
        self.level[var] = self.decision_level;
        self.reason[var] = reason;
        self.reason_theory[var] = reason_is_theory;
        self.trail.push((var, value, cause));
        if var < self.atom_count {
            theory.assert(var, value)?;
        }
        Ok(())
    }

    /// Boolean unit propagation to fixpoint. `Err` carries a falsified conflict
    /// clause (literals all currently false) on a Boolean conflict, or a learned
    /// theory-conflict clause on a forced theory inconsistency — tagged with which.
    fn unit_propagate(&mut self, theory: &mut LiaTheory) -> Result<(), Conflict> {
        let mut changed = true;
        while changed {
            changed = false;
            for ci in 0..self.clauses.len() {
                let mut unassigned: Option<Lit> = None;
                let mut satisfied = false;
                let mut count = 0;
                for &lit in &self.clauses[ci] {
                    match self.lit_sat(lit) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            unassigned = Some(lit);
                            count += 1;
                        }
                    }
                }
                if satisfied {
                    continue;
                }
                if count == 0 {
                    // The whole clause is falsified: a Boolean conflict clause.
                    return Err(Conflict {
                        clause: self.clauses[ci].clone(),
                        is_theory: false,
                    });
                }
                if count == 1 {
                    let lit = unassigned.expect("count == 1 has the unit literal");
                    // The reason for `lit` is this clause itself: once its other
                    // literals are false, it forces `lit`.
                    let reason = self.clauses[ci].clone();
                    if let Err(core) = self.assign(
                        theory,
                        lit.var,
                        lit.positive,
                        Cause::Implied,
                        Some(reason),
                        false,
                    ) {
                        return Err(Conflict {
                            clause: Self::theory_conflict_clause(&core),
                            is_theory: true,
                        });
                    }
                    changed = true;
                }
            }
        }
        Ok(())
    }

    /// Applies sound theory propagations to the trail until fixpoint. Returns the
    /// learned theory-conflict clause on a theory conflict, else `Ok(())`. A mirror
    /// of `crate::lra_online::Dpll::theory_propagate` retargeted to [`LiaTheory`].
    fn theory_propagate(&mut self, theory: &mut LiaTheory) -> Result<(), Conflict> {
        loop {
            let props = theory.propagate();
            let mut progress = false;
            for prop in props {
                let var = prop.lit.atom;
                match self.value[var] {
                    Some(v) if v == prop.lit.value => {}
                    Some(_) => {
                        // Theory entails the opposite of the current value: a
                        // conflict. Learn ¬(reason ∧ current literal).
                        let mut core = prop.reason.clone();
                        core.push(TheoryLit {
                            atom: var,
                            value: !prop.lit.value,
                        });
                        return Err(Conflict {
                            clause: Self::theory_conflict_clause(&core),
                            is_theory: true,
                        });
                    }
                    None => {
                        // The reason clause for the propagated literal is
                        // `¬(reason) ∨ lit`: once every reason literal is asserted
                        // (so its negation is false), this clause forces `lit`.
                        let reason_clause = Self::theory_reason_clause(&prop.reason, prop.lit);
                        if let Err(c) = self.assign(
                            theory,
                            var,
                            prop.lit.value,
                            Cause::Implied,
                            Some(reason_clause),
                            true,
                        ) {
                            return Err(Conflict {
                                clause: Self::theory_conflict_clause(&c),
                                is_theory: true,
                            });
                        }
                        progress = true;
                    }
                }
            }
            if !progress {
                return Ok(());
            }
        }
    }

    /// Unit propagation interleaved with theory propagation to a joint fixpoint. A
    /// mirror of `crate::lra_online::Dpll::propagate` retargeted to [`LiaTheory`].
    fn propagate(&mut self, theory: &mut LiaTheory) -> Result<(), Conflict> {
        loop {
            self.unit_propagate(theory)?;
            let before = self.trail.len();
            self.theory_propagate(theory)?;
            if self.trail.len() == before {
                return Ok(());
            }
        }
    }

    /// Maps a theory conflict core to a learned CNF conflict clause `¬⋀core` (every
    /// literal currently false, so it is the falsified clause to analyze).
    fn theory_conflict_clause(core: &[TheoryLit]) -> Vec<Lit> {
        core.iter()
            .map(|l| Lit {
                var: l.atom,
                positive: !l.value,
            })
            .collect()
    }

    /// The reason clause for a theory propagation `reason ⊨ lit`, namely
    /// `¬(reason) ∨ lit`: each reason literal contributes its negation, plus the
    /// propagated literal. Once every reason literal is asserted, this clause is
    /// unit and forces `lit` — the invariant [`Self::analyze_conflict`] relies on.
    fn theory_reason_clause(reason: &[TheoryLit], lit: TheoryLit) -> Vec<Lit> {
        let mut clause: Vec<Lit> = reason
            .iter()
            .map(|l| Lit {
                var: l.atom,
                positive: !l.value,
            })
            .collect();
        clause.push(Lit {
            var: lit.atom,
            positive: lit.value,
        });
        clause
    }

    /// 1-UIP conflict analysis: resolves the falsified `conflict` clause against the
    /// reason clauses of current-decision-level literals (newest-first on the trail)
    /// until a single current-level literal — the first UIP — remains. Returns the
    /// asserting clause (the UIP literal at index 0, the lower-level literals after
    /// it), the backjump level (the second-highest decision level among the clause's
    /// literals, `0` if it has none), and whether the clause is a pure **theory
    /// lemma** — derived by resolving only theory clauses (the seed conflict and
    /// every resolved reason were theory clauses), so it is entailed by the theory
    /// alone. A mirror of `axeyum_cnf::proof_sat`'s `analyze`, without the
    /// VSIDS/LBD/minimization machinery (kept deliberately minimal for the online
    /// theory loop).
    fn analyze_conflict(&self, conflict: &[Lit], seed_is_theory: bool) -> (Vec<Lit>, usize, bool) {
        let mut seen = vec![false; self.var_count];
        let mut lower: Vec<Lit> = Vec::new();
        let mut path_count = 0_usize;
        let mut pivot: Option<usize> = None;
        let mut index = self.trail.len();
        let current = self.decision_level;
        let mut all_theory = seed_is_theory;
        // Seed the worklist with the falsified conflict clause; afterwards each
        // iteration resolves against the popped literal's reason clause.
        let mut clause: Vec<Lit> = conflict.to_vec();

        loop {
            for lit in &clause {
                let v = lit.var;
                if Some(v) == pivot || seen[v] || self.level[v] == 0 {
                    continue;
                }
                seen[v] = true;
                if self.level[v] >= current {
                    path_count += 1;
                } else {
                    lower.push(*lit);
                }
            }

            // Walk the trail newest-first for the next seen variable.
            let mut found = false;
            while index > 0 {
                index -= 1;
                if seen[self.trail[index].0] {
                    found = true;
                    break;
                }
            }
            if !found {
                // The conflict is implied at level 0: the empty asserting clause.
                return (Vec::new(), 0, all_theory);
            }

            let var = self.trail[index].0;
            seen[var] = false;
            path_count -= 1;
            pivot = Some(var);

            if path_count == 0 {
                // `var` is the 1-UIP. The asserting literal is the negation of its
                // trail polarity (the clause forces it the opposite way after the
                // backjump).
                let mut learned = Vec::with_capacity(lower.len() + 1);
                learned.push(self.true_literal(var).negate());
                learned.extend(lower);
                let backjump = Self::backjump_level(&self.level, &learned);
                return (learned, backjump, all_theory);
            }

            // Resolve against the reason clause of the next current-level literal;
            // the result is a theory lemma only if that reason is also a theory
            // clause.
            all_theory = all_theory && self.reason_theory[var];
            clause.clone_from(
                self.reason[var]
                    .as_ref()
                    .expect("a current-level implied literal has a reason clause"),
            );
        }
    }

    /// The backjump level of an asserting clause: the second-highest decision level
    /// among its literals (the asserting literal at index 0 sits at the highest
    /// level), or `0` for a unit asserting clause.
    fn backjump_level(level: &[usize], learned: &[Lit]) -> usize {
        learned
            .iter()
            .skip(1)
            .map(|lit| level[lit.var])
            .max()
            .unwrap_or(0)
    }

    /// Backjumps to `target_level`: pops every trail entry strictly above it,
    /// unassigning each variable and popping the theory **once per decision crossed**
    /// (the theory was pushed once per decision, so this keeps the push/pop stack in
    /// lockstep).
    fn backjump_to(&mut self, theory: &mut LiaTheory, target_level: usize) {
        while let Some(&(var, _, _)) = self.trail.last() {
            if self.level[var] <= target_level {
                break;
            }
            let (var, _, cause) = self.trail.pop().expect("non-empty trail");
            self.value[var] = None;
            self.reason[var] = None;
            self.reason_theory[var] = false;
            if cause == Cause::Decision {
                theory.pop();
            }
        }
        self.decision_level = target_level;
    }

    /// The lowest-index unassigned variable, or `None` when total.
    fn pick_unassigned(&self) -> Option<usize> {
        (0..self.var_count).find(|&v| self.value[v].is_none())
    }

    /// Runs the search. Returns `true` iff the skeleton is UNSAT under the theory,
    /// `false` on a Boolean- and theory-consistent total assignment.
    fn solve(&mut self, theory: &mut LiaTheory) -> bool {
        loop {
            match self.propagate(theory) {
                Ok(()) => {}
                Err(conflict) => {
                    if !self.learn_and_backjump(theory, &conflict) {
                        return true;
                    }
                    continue;
                }
            }
            match self.pick_unassigned() {
                None => return false,
                Some(var) => {
                    self.decision_level += 1;
                    theory.push();
                    if let Err(core) = self.assign(theory, var, true, Cause::Decision, None, false)
                    {
                        let conflict = Conflict {
                            clause: Self::theory_conflict_clause(&core),
                            is_theory: true,
                        };
                        if !self.learn_and_backjump(theory, &conflict) {
                            return true;
                        }
                    }
                }
            }
        }
    }

    /// Handles a conflict by 1-UIP analysis: learns the asserting clause, jumps
    /// non-chronologically to the backjump level, and enqueues the UIP literal as an
    /// implied assignment with the learned clause as its reason. `false` when the
    /// conflict is implied at level 0 (UNSAT) — there is nothing to assert.
    fn learn_and_backjump(&mut self, theory: &mut LiaTheory, conflict: &Conflict) -> bool {
        let (learned, backjump, is_theory_lemma) =
            self.analyze_conflict(&conflict.clause, conflict.is_theory);
        #[cfg(test)]
        {
            self.diag.analyze_fires += 1;
            self.diag.conflict_len_total +=
                u64::try_from(conflict.clause.len()).expect("clause length fits u64");
        }
        if learned.is_empty() {
            return false;
        }
        #[cfg(test)]
        {
            // Only non-empty learned clauses are stored in `clauses`; keep the
            // length-total and lemma-flag streams aligned with that storage.
            self.diag.learned_len_total +=
                u64::try_from(learned.len()).expect("clause length fits u64");
            self.diag.lemma_flags.push(is_theory_lemma);
            // The level-0 atom facts the lemma rests on (analyze drops them as
            // unconditional). The conflict was analyzed against the current trail, so
            // capture the level-0 atom prefix now, before backjumping.
            let level0: Vec<(usize, bool)> = self
                .trail
                .iter()
                .filter(|&&(v, _, _)| self.level[v] == 0 && v < self.atom_count)
                .map(|&(v, val, _)| (v, val))
                .collect();
            self.diag.lemma_level0.push(level0);
        }
        self.backjump_to(theory, backjump);
        let uip = learned[0];
        let reason = if learned.len() == 1 {
            None
        } else {
            Some(learned.clone())
        };
        self.clauses.push(learned);
        // Enqueue the UIP literal. At the backjump level its theory assertion is
        // consistent (the asserting clause is an entailed resolvent), but a *theory*
        // conflict can still surface here — re-analyze that conflict. The learned
        // clause is the UIP's reason, a theory clause iff it is a theory lemma.
        match self.assign(
            theory,
            uip.var,
            uip.positive,
            Cause::Implied,
            reason,
            is_theory_lemma,
        ) {
            Ok(()) => true,
            Err(core) => self.learn_and_backjump(
                theory,
                &Conflict {
                    clause: Self::theory_conflict_clause(&core),
                    is_theory: true,
                },
            ),
        }
    }
}

/// Tseitin encoder from the typed Boolean IR into a CNF skeleton, with the first
/// `atom_terms.len()` variables reserved for the registered `LIA` atoms (numbered
/// to match [`LiaTheory`]).
struct Encoder {
    term_var: HashMap<TermId, usize>,
    var_count: usize,
}

impl Encoder {
    fn new(atom_terms: &[TermId]) -> Self {
        let mut term_var = HashMap::new();
        for (i, &t) in atom_terms.iter().enumerate() {
            term_var.insert(t, i);
        }
        Self {
            term_var,
            var_count: atom_terms.len(),
        }
    }

    fn fresh(&mut self) -> usize {
        let v = self.var_count;
        self.var_count += 1;
        v
    }

    /// Encodes Boolean term `t`, returning the variable whose truth equals `t`, or
    /// `None` for structure outside the supported connectives (sound give-up).
    fn encode(
        &mut self,
        arena: &TermArena,
        t: TermId,
        clauses: &mut Vec<Vec<Lit>>,
    ) -> Option<usize> {
        if let Some(&v) = self.term_var.get(&t) {
            return Some(v);
        }
        let v = match arena.node(t) {
            TermNode::Symbol(_) if arena.sort_of(t) == Sort::Bool => self.fresh(),
            TermNode::BoolConst(b) => {
                let value = *b;
                let g = self.fresh();
                clauses.push(vec![Lit {
                    var: g,
                    positive: value,
                }]);
                g
            }
            TermNode::App { op, args } => {
                let op = *op;
                let args = args.clone();
                self.encode_app(arena, op, &args, clauses)?
            }
            _ => return None,
        };
        self.term_var.insert(t, v);
        Some(v)
    }

    fn encode_app(
        &mut self,
        arena: &TermArena,
        op: Op,
        args: &[TermId],
        clauses: &mut Vec<Vec<Lit>>,
    ) -> Option<usize> {
        let lits: Vec<Lit> = args
            .iter()
            .map(|&a| {
                self.encode(arena, a, clauses).map(|var| Lit {
                    var,
                    positive: true,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let g = self.fresh();
        let gl = Lit {
            var: g,
            positive: true,
        };
        match (op, lits.as_slice()) {
            (Op::BoolNot, [a]) => {
                clauses.push(vec![gl.negate(), a.negate()]);
                clauses.push(vec![gl, *a]);
            }
            (Op::BoolAnd, [a, b]) => {
                clauses.push(vec![gl.negate(), *a]);
                clauses.push(vec![gl.negate(), *b]);
                clauses.push(vec![a.negate(), b.negate(), gl]);
            }
            (Op::BoolOr, [a, b]) => {
                clauses.push(vec![gl, a.negate()]);
                clauses.push(vec![gl, b.negate()]);
                clauses.push(vec![gl.negate(), *a, *b]);
            }
            (Op::BoolImplies, [a, b]) => {
                clauses.push(vec![gl, *a]);
                clauses.push(vec![gl, b.negate()]);
                clauses.push(vec![gl.negate(), a.negate(), *b]);
            }
            (Op::BoolXor, [a, b]) => {
                clauses.push(vec![gl.negate(), *a, *b]);
                clauses.push(vec![gl.negate(), a.negate(), b.negate()]);
                clauses.push(vec![gl, a.negate(), *b]);
                clauses.push(vec![gl, *a, b.negate()]);
            }
            (Op::Ite, [c, x, y]) => {
                clauses.push(vec![c.negate(), x.negate(), gl]);
                clauses.push(vec![c.negate(), *x, gl.negate()]);
                clauses.push(vec![*c, y.negate(), gl]);
                clauses.push(vec![*c, *y, gl.negate()]);
            }
            _ => return None,
        }
        Some(g)
    }
}

/// Collects the distinct integer order/equality atoms in `term`, in a stable
/// left-to-right scan (so atom indexing is deterministic).
fn collect_lia_atoms(
    arena: &TermArena,
    term: TermId,
    out: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
) {
    if is_lia_atom(arena, term) {
        if seen.insert(term) {
            out.push(term);
        }
        return;
    }
    if let TermNode::App { args, .. } = arena.node(term) {
        for &a in args {
            collect_lia_atoms(arena, a, out, seen);
        }
    }
}

/// Whether `term` is a linear-integer order atom (`<,<=,>,>=`) or an integer
/// equality atom — the atoms this online theory abstracts.
fn is_lia_atom(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App {
            op: Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe,
            ..
        } => true,
        TermNode::App { op: Op::Eq, args } => is_int(arena, args[0]),
        _ => false,
    }
}

/// Decides a `QF_LIA` query (an arbitrary Boolean combination of linear integer
/// order/equality atoms) by the **online** `DPLL(T)` loop, returning a
/// **replay-checked, integer-valued** model on `sat`. The warm analogue of the
/// offline [`crate::lra::check_with_lia_simplex`].
///
/// The Boolean skeleton (over the distinct integer atoms plus any Boolean leaves)
/// is searched by a self-contained `DPLL(T)` driver that keeps one backtrackable
/// [`LiaTheory`] in lockstep; on a Boolean- and theory-consistent total
/// assignment it builds a candidate integer model and **replays it against the
/// original assertions** — the soundness gate, so a model the incremental theory
/// cannot justify yields [`CheckResult::Unknown`], never a wrong `sat`. `unsat` is
/// a sound refutation (only ever returned at a root-level conflict whose core is
/// `check_with_lia_simplex`-`unsat`).
///
/// Returns [`CheckResult::Unknown`] when there are no `LIA` atoms, the Boolean
/// skeleton has structure the encoder does not cover, or the offline feasibility
/// check was inconclusive (resource limit / overflow / outside its fragment).
///
/// # Errors
///
/// Never returns `Err` in this slice (every give-up is a conservative
/// [`CheckResult::Unknown`]); the [`SolverError`] return type matches
/// [`crate::lra_online::check_qf_lra_online`] for interchange so a future stricter
/// variant can surface [`SolverError::Unsupported`].
pub fn check_qf_lia_online(
    arena: &TermArena,
    assertions: &[TermId],
    _config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Distinct integer atoms over the whole assertion set become the theory's atom
    // indices and the first `atom_count` skeleton variables.
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_lia_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return Ok(CheckResult::Unknown(unknown(
            "no linear-integer atoms for the online LIA path",
        )));
    }

    let mut enc = Encoder::new(&atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    for &assertion in assertions {
        let Some(top) = enc.encode(arena, assertion, &mut clauses) else {
            return Ok(CheckResult::Unknown(unknown(
                "boolean skeleton outside the online LIA encoder",
            )));
        };
        clauses.push(vec![Lit {
            var: top,
            positive: true,
        }]);
    }

    let atom_count = atom_terms.len();
    let mut theory = LiaTheory::new(arena, &atom_terms);

    let mut solver = Dpll::new(enc.var_count, atom_count, clauses);
    if solver.solve(&mut theory) {
        return Ok(CheckResult::Unsat);
    }
    // Theory-consistent total assignment: reconstruct an integer model from the
    // live atoms (via the trusted offline decider) and replay it.
    match theory_model(&theory) {
        Some(model) if replays_integer(arena, assertions, &model) => Ok(CheckResult::Sat(model)),
        _ => Ok(CheckResult::Unknown(unknown(
            "online LIA model did not replay (arithmetic outside the incremental engine)",
        ))),
    }
}

/// Reconstructs an integer model for the currently-asserted constraint atoms by
/// re-running the trusted offline [`check_with_lia_simplex`] over the live
/// conjunction and lifting its `sat` model. `None` if the live system is (now)
/// infeasible / inconclusive — the caller then yields `Unknown`, never a wrong
/// `sat`.
fn theory_model(theory: &LiaTheory) -> Option<Model> {
    let lits = theory.live_lits();
    let (arena, terms) = theory.live_terms(&lits)?;
    if terms.is_empty() {
        // No live constraints: any assignment works; an empty model replays
        // trivially against any free integer symbols (the evaluator treats unset
        // integer symbols as zero is not assumed — but with no constraints the
        // assertions are tautological at this leaf, so an empty model suffices).
        return Some(Model::new());
    }
    match check_with_lia_simplex(&arena, &terms) {
        Ok(CheckResult::Sat(model)) => Some(model),
        _ => None,
    }
}

/// Whether `model` satisfies every assertion under the ground evaluator **with
/// integer values**. Any non-`true`, non-integer, or evaluation error makes it not
/// replay (→ `Unknown`, never a wrong `sat`).
fn replays_integer(arena: &TermArena, assertions: &[TermId], model: &Model) -> bool {
    let mut assignment = Assignment::new();
    for (symbol, value) in model.iter() {
        if !matches!(value, Value::Int(_)) {
            return false;
        }
        assignment.set(symbol, value);
    }
    assertions
        .iter()
        .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))))
}

/// A classified `unknown` reason for the online LIA path.
fn unknown(detail: &str) -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: detail.to_owned(),
    }
}

/// Test-only diagnostic run of the online LIA driver over a conjunction of
/// `assertions`: returns the registered atom terms, the atom count, the learned
/// 1-UIP asserting clauses, and the fires/length diagnostics. Mirrors the setup of
/// [`check_qf_lia_online`]. Used by the in-source soundness tests to confirm each
/// learned clause is entailed and that 1-UIP fired and shrank the learned clauses
/// below the full conflict cores.
#[cfg(test)]
struct OnlineDiag {
    atom_terms: Vec<TermId>,
    atom_count: usize,
    learned: Vec<Vec<Lit>>,
    /// Aligned with `learned`: whether each stored clause is a pure theory lemma.
    lemma_flags: Vec<bool>,
    /// Aligned with `learned`: the level-0 atom facts each lemma rests on.
    lemma_level0: Vec<Vec<(usize, bool)>>,
    analyze_fires: usize,
    learned_len_total: u64,
    conflict_len_total: u64,
}

#[cfg(test)]
fn run_online_diag(arena: &TermArena, assertions: &[TermId]) -> Option<OnlineDiag> {
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_lia_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return None;
    }
    let mut enc = Encoder::new(&atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    for &assertion in assertions {
        let top = enc.encode(arena, assertion, &mut clauses)?;
        clauses.push(vec![Lit {
            var: top,
            positive: true,
        }]);
    }
    let atom_count = atom_terms.len();
    let mut theory = LiaTheory::new(arena, &atom_terms);
    let mut solver = Dpll::new(enc.var_count, atom_count, clauses);
    let _ = solver.solve(&mut theory);
    let learned = solver.clauses[solver.diag.initial_clauses..].to_vec();
    debug_assert_eq!(
        learned.len(),
        solver.diag.lemma_flags.len(),
        "one lemma flag per stored learned clause"
    );
    Some(OnlineDiag {
        atom_terms,
        atom_count,
        learned,
        lemma_flags: solver.diag.lemma_flags,
        lemma_level0: solver.diag.lemma_level0,
        analyze_fires: solver.diag.analyze_fires,
        learned_len_total: solver.diag.learned_len_total,
        conflict_len_total: solver.diag.conflict_len_total,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Rational;

    fn iconst(arena: &mut TermArena, n: i128) -> TermId {
        arena.int_const(n)
    }

    fn ivar(arena: &mut TermArena, name: &str) -> TermId {
        let s = arena.declare(name, Sort::Int).expect("declare int");
        arena.var(s)
    }

    #[test]
    fn strict_tightening_set_yields_lia_unsat_core() {
        // 0 < x  and  x < 1: integer-UNSAT (rationally SAT) — the LIA point.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = iconst(&mut arena, 0);
        let one = iconst(&mut arena, 1);
        let gt = arena.int_gt(x, zero).expect("x>0");
        let lt = arena.int_lt(x, one).expect("x<1");

        let mut theory = LiaTheory::new(&arena, &[gt, lt]);
        assert!(theory.assert(0, true).is_ok());
        let core = theory.assert(1, true).expect_err("integer-infeasible");
        assert!(!core.is_empty(), "conflict core must be non-empty");
        // The core's atoms, asserted at their polarities, must be
        // check_with_lia_simplex-unsat.
        let core_terms: Vec<TermId> = core
            .iter()
            .map(|l| if l.atom == 0 { gt } else { lt })
            .collect();
        let verdict = check_with_lia_simplex(&arena, &core_terms).expect("decidable");
        assert_eq!(verdict, CheckResult::Unsat, "explained core must be unsat");
    }

    #[test]
    fn infeasible_order_set_yields_lia_unsat_core() {
        // x > 1 and x < 0: infeasible (over the integers and the rationals).
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let one = iconst(&mut arena, 1);
        let zero = iconst(&mut arena, 0);
        let gt = arena.int_gt(x, one).expect("x>1");
        let lt = arena.int_lt(x, zero).expect("x<0");

        let mut theory = LiaTheory::new(&arena, &[gt, lt]);
        assert!(theory.assert(0, true).is_ok());
        let core = theory.assert(1, true).expect_err("infeasible");
        let core_terms: Vec<TermId> = core
            .iter()
            .map(|l| if l.atom == 0 { gt } else { lt })
            .collect();
        assert_eq!(
            check_with_lia_simplex(&arena, &core_terms).expect("decidable"),
            CheckResult::Unsat
        );
    }

    #[test]
    fn push_assert_pop_restores_feasibility() {
        // Start feasible (x >= 0). Push, add x <= -1 (infeasible), pop, feasible
        // again.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = iconst(&mut arena, 0);
        let neg1 = iconst(&mut arena, -1);
        let ge = arena.int_ge(x, zero).expect("x>=0");
        let le = arena.int_le(x, neg1).expect("x<=-1");

        let mut theory = LiaTheory::new(&arena, &[ge, le]);
        assert!(theory.assert(0, true).is_ok());
        theory.push();
        assert!(theory.assert(1, true).is_err(), "x>=0 and x<=-1 infeasible");
        theory.pop();
        // After pop, asserting the negated bound succeeds (x>=0 and not(x<=-1)).
        theory.push();
        assert!(
            theory.assert(1, false).is_ok(),
            "x>=0 and not(x<=-1) feasible"
        );
    }

    #[test]
    fn non_lia_atom_is_a_no_op() {
        // A BV equality atom registers as Unsupported (no-op), never panics.
        let mut arena = TermArena::new();
        let bv = arena.declare("b", Sort::BitVec(8)).expect("declare bv");
        let v = arena.var(bv);
        let k = arena.bv_const(8, 5).expect("bv const");
        let eq = arena.eq(v, k).expect("bv eq");

        let mut theory = LiaTheory::new(&arena, &[eq]);
        assert!(!theory.tracks(0));
        assert!(
            theory.assert(0, true).is_ok(),
            "no-op assert never conflicts"
        );
        assert!(theory.assert(0, false).is_ok());
    }

    #[test]
    fn equality_atom_true_constrains() {
        // x = 3 then x < 2: infeasible.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let three = iconst(&mut arena, 3);
        let two = iconst(&mut arena, 2);
        let eq = arena.eq(x, three).expect("x=3");
        let lt = arena.int_lt(x, two).expect("x<2");

        let mut theory = LiaTheory::new(&arena, &[eq, lt]);
        assert!(theory.tracks(0) && theory.tracks(1));
        assert!(theory.assert(0, true).is_ok());
        assert!(theory.assert(1, true).is_err(), "x=3 and x<2 infeasible");
    }

    #[test]
    fn online_decider_agrees_on_a_strict_tightening_unsat() {
        // 0 < x  and  x < 1: integer-unsat.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = iconst(&mut arena, 0);
        let one = iconst(&mut arena, 1);
        let gt = arena.int_gt(x, zero).expect("x>0");
        let lt = arena.int_lt(x, one).expect("x<1");
        let verdict =
            check_qf_lia_online(&arena, &[gt, lt], &SolverConfig::default()).expect("decidable");
        assert_eq!(verdict, CheckResult::Unsat);
    }

    #[test]
    fn online_decider_sat_model_replays_with_integers() {
        // (x < y) or (y < x): sat, model must replay with integer values.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let xy = arena.int_lt(x, y).expect("x<y");
        let yx = arena.int_lt(y, x).expect("y<x");
        let or = arena.or(xy, yx).expect("or");
        let verdict =
            check_qf_lia_online(&arena, &[or], &SolverConfig::default()).expect("decidable");
        match verdict {
            CheckResult::Sat(model) => {
                assert!(replays_integer(&arena, &[or], &model));
                for (_symbol, value) in model.iter() {
                    assert!(matches!(value, Value::Int(_)), "model must be integer");
                }
            }
            other => panic!("expected sat, got {other:?}"),
        }
    }

    /// A tiny deterministic LCG (numerical-recipes constants) for the in-source
    /// 1-UIP soundness fuzz — no `rand`, no clock, reproducible from the seed.
    struct Lcg(u64);

    impl Lcg {
        fn next_u64(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next_u64() % n
        }
    }

    /// Builds a random linear-integer order atom `Σ cᵢ·xᵢ <rel> k` (orders only —
    /// every such atom has a representable single-constraint negation) over the given
    /// integer variables.
    fn random_lia_order_atom(arena: &mut TermArena, lcg: &mut Lcg, vars: &[TermId]) -> TermId {
        let mut expr: Option<TermId> = None;
        for &v in vars {
            let c = i128::from(lcg.below(7)) - 3;
            if c == 0 {
                continue;
            }
            let coeff = arena.int_const(c);
            let term = arena.int_mul(coeff, v).expect("c*x");
            expr = Some(match expr {
                None => term,
                Some(acc) => arena.int_add(acc, term).expect("acc+term"),
            });
        }
        let lhs = expr.unwrap_or_else(|| arena.int_const(0));
        let k = arena.int_const(i128::from(lcg.below(11)) - 5);
        match lcg.below(4) {
            0 => arena.int_lt(lhs, k).expect("lt"),
            1 => arena.int_le(lhs, k).expect("le"),
            2 => arena.int_gt(lhs, k).expect("gt"),
            _ => arena.int_ge(lhs, k).expect("ge"),
        }
    }

    /// SOUNDNESS gate for **1-UIP theory-conflict learning** (the LIA mirror): over a
    /// deterministic LCG corpus of random `QF_LIA` formulas with **disjunctive**
    /// assertions (so the driver must branch and learns non-trivial asserting
    /// clauses), drive the online driver and, for EVERY learned asserting clause that
    /// is a pure theory lemma, independently verify with the trusted offline integer
    /// decider that the clause is *entailed* — i.e. `¬clause ∧ level0-facts` is
    /// `check_with_lia_simplex`-UNSAT. A learned clause that isn't implied is a hard
    /// failure (an unsound lemma would corrupt the search). Also proves the 1-UIP
    /// path FIRES and that learned clauses are strictly SHORTER on average than the
    /// full `¬⋀core` conflict clauses the old chronological scheme learned.
    #[test]
    fn learned_clauses_are_entailed_and_shorter() {
        let mut lcg = Lcg(0x1c1c_2b2b_3c3c_4d4d);
        let mut fires_total = 0_usize;
        let mut learned_len_total = 0_u64;
        let mut conflict_len_total = 0_u64;
        let mut clauses_checked = 0_usize;

        for _ in 0..1500 {
            let mut arena = TermArena::new();
            let nvars = 2 + usize::try_from(lcg.below(2)).expect("small");
            let vars: Vec<TermId> = (0..nvars)
                .map(|i| {
                    let s = arena.declare(&format!("v{i}"), Sort::Int).expect("declare");
                    arena.var(s)
                })
                .collect();
            // A pool of order atoms; each assertion is a random *disjunction* of two
            // or three of them (so the driver must decide between them, exercising
            // real 1-UIP backjump learning rather than level-0 unit propagation).
            let pool_n = 6;
            let pool: Vec<TermId> = (0..pool_n)
                .map(|_| random_lia_order_atom(&mut arena, &mut lcg, &vars))
                .collect();
            let pick = |lcg: &mut Lcg| pool[usize::try_from(lcg.below(pool_n)).expect("small")];
            let nclauses = 3 + usize::try_from(lcg.below(4)).expect("small");
            let atoms: Vec<TermId> = (0..nclauses)
                .map(|_| {
                    let width = 2 + usize::try_from(lcg.below(2)).expect("small"); /* 2..=3 */
                    let mut term = pick(&mut lcg);
                    for _ in 1..width {
                        let b = pick(&mut lcg);
                        term = arena.or(term, b).expect("or");
                    }
                    term
                })
                .collect();

            let Some(diag) = run_online_diag(&arena, &atoms) else {
                continue;
            };
            fires_total += diag.analyze_fires;
            learned_len_total += diag.learned_len_total;
            conflict_len_total += diag.conflict_len_total;

            for ((clause, &is_lemma), level0) in diag
                .learned
                .iter()
                .zip(&diag.lemma_flags)
                .zip(&diag.lemma_level0)
            {
                // Only PURE THEORY LEMMAS are entailed by the theory plus the level-0
                // facts — a 1-UIP clause that resolved through Boolean input clauses
                // is entailed by formula+theory, not the theory, so the conjunctive
                // offline decider is not its oracle. Restrict the check to lemmas.
                if !is_lemma {
                    continue;
                }
                // Restrict to atom-only clauses (Tseitin aux vars have no atom term to
                // negate); theory lemmas over the order fragment are these.
                if clause.iter().any(|l| l.var >= diag.atom_count) {
                    continue;
                }
                // ¬clause ∧ level0-facts: every clause literal falsified (atom `var`
                // asserted at `!positive`) together with the unconditional level-0
                // atom assignments the lemma rests on — must be integer-UNSAT. Build
                // in a working clone so polarity `not` terms resolve.
                let mut neg_arena = arena.clone();
                let mut neg_terms: Vec<TermId> = Vec::with_capacity(clause.len() + level0.len());
                for lit in clause {
                    let atom = diag.atom_terms[lit.var];
                    let term = if lit.positive {
                        neg_arena.not(atom).expect("not")
                    } else {
                        atom
                    };
                    neg_terms.push(term);
                }
                for &(atom_idx, value) in level0 {
                    let atom = diag.atom_terms[atom_idx];
                    let term = if value {
                        atom
                    } else {
                        neg_arena.not(atom).expect("not")
                    };
                    neg_terms.push(term);
                }
                match check_with_lia_simplex(&neg_arena, &neg_terms) {
                    Ok(CheckResult::Unsat) => clauses_checked += 1,
                    Ok(CheckResult::Sat(m)) => panic!(
                        "UNSOUND LEARNED CLAUSE: ¬clause is integer-SAT\nclause={clause:?}\n\
                         assertions={atoms:?}\nmodel={m:?}"
                    ),
                    Ok(CheckResult::Unknown(_)) | Err(_) => {}
                }
            }
        }

        eprintln!(
            "LIA 1-UIP gate: fires={fires_total}, clauses_checked={clauses_checked}, \
             learned_len_total={learned_len_total}, conflict_len_total={conflict_len_total}"
        );
        assert!(fires_total > 50, "1-UIP analysis never meaningfully fired");
        assert!(
            clauses_checked > 20,
            "too few learned clauses entailment-checked ({clauses_checked})"
        );
        // The improvement metric: 1-UIP asserting clauses are strictly shorter than
        // the full conflict cores on average.
        assert!(
            learned_len_total < conflict_len_total,
            "learned clauses not shorter on average ({learned_len_total} vs {conflict_len_total})"
        );
    }

    #[test]
    fn rational_only_value_does_not_replay_as_integer() {
        // Guard: a non-integer model value must be rejected by replays_integer.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = iconst(&mut arena, 0);
        let gt = arena.int_gt(x, zero).expect("x>0");
        let s = match arena.node(x) {
            TermNode::Symbol(sym) => *sym,
            _ => unreachable!("ivar is a symbol"),
        };
        let mut model = Model::new();
        model.set(s, Value::Real(Rational::integer(1)));
        assert!(
            !replays_integer(&arena, &[gt], &model),
            "a Real value must not pass the integer replay gate"
        );
    }
}
