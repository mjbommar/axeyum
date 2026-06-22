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
//! - `propagate` is an honest empty under-approximation in this first slice (a
//!   sound choice: the driver still terminates, just with less theory-level
//!   pruning). It is documented as deferred.
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
use crate::lra::check_with_lia_simplex;
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

    /// Theory propagation. The first slice returns no propagations — a sound
    /// under-approximation: the `DPLL(T)` driver still decides correctly, it
    /// simply branches on atoms theory propagation could have forced. Documented
    /// as deferred.
    #[must_use]
    #[allow(clippy::unused_self)]
    pub fn propagate(&self) -> Vec<TheoryProp> {
        Vec::new()
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

/// A self-contained `DPLL(T)` search over the CNF skeleton driving a [`LiaTheory`]
/// online: chronological backtracking with theory-conflict clause learning, the
/// theory pushed on each decision and popped on each backtrack.
struct Dpll {
    var_count: usize,
    atom_count: usize,
    clauses: Vec<Vec<Lit>>,
    value: Vec<Option<bool>>,
    trail: Vec<(usize, bool, Cause)>,
}

impl Dpll {
    fn new(var_count: usize, atom_count: usize, clauses: Vec<Vec<Lit>>) -> Self {
        Self {
            var_count,
            atom_count,
            clauses,
            value: vec![None; var_count],
            trail: Vec::new(),
        }
    }

    fn lit_sat(&self, lit: Lit) -> Option<bool> {
        self.value[lit.var].map(|v| v == lit.positive)
    }

    /// Assigns `var := value`, mirroring a theory atom into [`LiaTheory`].
    fn assign(
        &mut self,
        theory: &mut LiaTheory,
        var: usize,
        value: bool,
        cause: Cause,
    ) -> Result<(), Vec<TheoryLit>> {
        self.value[var] = Some(value);
        self.trail.push((var, value, cause));
        if var < self.atom_count {
            theory.assert(var, value)?;
        }
        Ok(())
    }

    /// Undoes the trail back to (and excluding) the most recent decision, popping
    /// the theory once. `None` if the search is exhausted.
    fn backtrack_to_decision(&mut self, theory: &mut LiaTheory) -> Option<(usize, bool)> {
        loop {
            let (var, value, cause) = self.trail.pop()?;
            self.value[var] = None;
            if cause == Cause::Decision {
                theory.pop();
                return Some((var, value));
            }
        }
    }

    /// Boolean unit propagation to fixpoint. `Err` carries a learned clause on a
    /// Boolean conflict or a forced theory conflict.
    fn unit_propagate(&mut self, theory: &mut LiaTheory) -> Result<(), Vec<Lit>> {
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
                    return Err(self.clauses[ci].iter().map(|l| l.negate()).collect());
                }
                if count == 1 {
                    let lit = unassigned.expect("count == 1 has the unit literal");
                    if let Err(core) = self.assign(theory, lit.var, lit.positive, Cause::Implied) {
                        return Err(Self::theory_conflict_clause(&core));
                    }
                    changed = true;
                }
            }
        }
        Ok(())
    }

    /// Maps a theory conflict core to a learned CNF clause `¬⋀core`.
    fn theory_conflict_clause(core: &[TheoryLit]) -> Vec<Lit> {
        core.iter()
            .map(|l| Lit {
                var: l.atom,
                positive: !l.value,
            })
            .collect()
    }

    /// The lowest-index unassigned variable, or `None` when total.
    fn pick_unassigned(&self) -> Option<usize> {
        (0..self.var_count).find(|&v| self.value[v].is_none())
    }

    /// Runs the search. Returns `true` iff the skeleton is UNSAT under the theory,
    /// `false` on a Boolean- and theory-consistent total assignment.
    fn solve(&mut self, theory: &mut LiaTheory) -> bool {
        loop {
            loop {
                match self.unit_propagate(theory) {
                    Ok(()) => break,
                    Err(clause) => {
                        if !self.learn_and_backtrack(theory, clause) {
                            return true;
                        }
                    }
                }
            }
            match self.pick_unassigned() {
                None => return false,
                Some(var) => {
                    theory.push();
                    if let Err(core) = self.assign(theory, var, true, Cause::Decision) {
                        let clause = Self::theory_conflict_clause(&core);
                        if !self.learn_and_backtrack(theory, clause) {
                            return true;
                        }
                    }
                }
            }
        }
    }

    /// Records the learned clause, backtracks past the most recent decision, and
    /// flips it as an implied assignment. `false` when no decision remains (UNSAT).
    fn learn_and_backtrack(&mut self, theory: &mut LiaTheory, clause: Vec<Lit>) -> bool {
        if !clause.is_empty() {
            self.clauses.push(clause);
        }
        loop {
            let Some((var, value)) = self.backtrack_to_decision(theory) else {
                return false;
            };
            let flipped = !value;
            match self.assign(theory, var, flipped, Cause::Implied) {
                Ok(()) => return true,
                Err(core) => {
                    let learned = Self::theory_conflict_clause(&core);
                    if !learned.is_empty() {
                        self.clauses.push(learned);
                    }
                }
            }
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
