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
//!   emitted as a [`TheoryProp`] whose `reason` is the **asserted-only** core.
//!   Equality atoms use the same conservative probe style: equality is propagated
//!   true only when both strict disequality branches are LP-infeasible, and false
//!   only when asserting the equality is LP-infeasible. An LP-`Feasible` probe is
//!   inconclusive about ℤ → skip (no fabricated propagation). The relaxation
//!   skips integer tightening / Gomory cuts / branch-and-bound, so it stays far
//!   cheaper than the per-`assert` integer feasibility decision.
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

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::time::Instant;

use axeyum_ir::{
    Assignment, Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::euf_egraph::{TheoryLit, TheoryProp, TheorySolver};
#[cfg(test)]
use crate::lra::check_with_lia_simplex;
use crate::lra::{
    LpRelaxation, check_with_lia_opaque_apps_within, check_with_lia_simplex_within,
    lp_relaxation_feasibility, lp_relaxation_feasibility_opaque_apps,
};
use crate::lra_online::{Dpll, Lit};
use crate::model::Model;
use crate::simplex;

/// Above this many LIA atoms, the online driver avoids re-running the full
/// conjunctive integer feasibility check on every single Boolean assignment.
const DEFER_LIA_FEASIBILITY_ATOMS: usize = 128;

/// Clause-count companion to [`DEFER_LIA_FEASIBILITY_ATOMS`] for generated
/// Boolean skeletons with fewer theory atoms but a large Tseitin surface.
const DEFER_LIA_FEASIBILITY_CLAUSES: usize = 4096;

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
    /// If set, [`TheorySolver::assert`] records assignments without re-solving the
    /// whole live conjunction. The next [`TheorySolver::propagate`] call performs
    /// one feasibility check and reports an infeasible core as a conflict
    /// propagation. This is sound because `DPLL` calls theory propagation before
    /// every decision/model return; it only changes when the expensive check runs.
    defer_feasibility_until_propagate: bool,
    /// In the large-query deferred mode, skip LP entailment probes after the single
    /// feasibility check. Returning fewer propagations is a sound
    /// under-approximation and avoids probing hundreds of unassigned atoms against
    /// a thousand-literal live set.
    skip_entailment_propagation: bool,
    /// Treat integer-valued uninterpreted-function applications as opaque integer
    /// variables inside LIA atoms. This is used only by UFLIA combination: it is
    /// sound for infeasibility/conflict learning because the abstraction relaxes
    /// the original problem. Satisfiable opaque abstractions still do not produce
    /// a model through [`integer_model`](Self::integer_model).
    allow_opaque_apps: bool,
    /// Optional wall-clock deadline inherited from the online DPLL(T) caller. A
    /// passed deadline makes feasibility/probe checks inconclusive, never
    /// conflicting, so timeout handling remains sound.
    deadline: Option<Instant>,
    /// Per registered atom: its tableau row and the bound each polarity imposes.
    /// [`AtomRow::None`] for atoms the engine cannot represent — while one of those
    /// is live the engine's view is partial and it decides nothing.
    atom_rows: Vec<AtomRow>,
    /// The warm rational filter in front of the offline integer decider (see the
    /// section comment above [`IntLin`]). `None` when no atom yielded a row or the
    /// dense tableau would exceed [`simplex::MAX_TABLEAU_CELLS`]; the theory then
    /// behaves exactly as it did before the filter existed. Interior mutability
    /// because a check *mutates* the tableau (it warm-starts) while
    /// [`LiaTheory::propagate`] and [`LiaTheory::feasibility`] hold only `&self`.
    simplex: Option<RefCell<IntSimplexEngine>>,
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

// --- The warm rational filter over the live integer system. ------------------
//
// Before the trusted (but expensive) offline branch-and-bound runs, the live set
// is decided over the **rationals** on the warm `simplex::Incremental` — the same
// engine `crate::lra_online::LraTheory` drives. Two facts make that useful without
// weakening any verdict:
//
//   * The rows are an **exact** ℤ-encoding of the atoms, not a relaxation of them.
//     Every coefficient and constant is an `i128` integer by construction, so a
//     strict `Σ aⱼ·xⱼ < b` is rewritten to `Σ aⱼ·xⱼ ≤ b − 1` and **no strict row is
//     ever built**. Dropping *integrality* is therefore the only relaxation, and
//     rational-infeasible ⇒ integer-infeasible: a refutation transfers, and its
//     self-verified Farkas support is a sound integer conflict core.
//   * A rational point that happens to be **integral** satisfies the live
//     conjunction over ℤ outright, so feasibility transfers in that direction too
//     and the branch-and-bound is skipped.
//
// Everything else — a non-integral point, an overflow, a live atom without a row —
// is `Inconclusive` and falls through to the offline decider unchanged. Integer
// feasibility is *not* rational feasibility, and nothing here pretends otherwise:
// the only `Sat` the filter reports carries an integral witness.

/// A linear integer expression `Σ cⱼ·xⱼ + k` over dense variable indices, in exact
/// `i128` integers.
///
/// Integrality is enforced **by construction**: every operation is checked, and a
/// result that would overflow (or an input that is not an integer linear term)
/// yields `None`, which registers the atom as [`AtomRow::None`] and leaves it
/// entirely to the offline decider. This is what licenses the strict-to-non-strict
/// tightening in [`build_int_simplex_engine`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct IntLin {
    coeffs: BTreeMap<usize, i128>,
    constant: i128,
}

impl IntLin {
    fn constant(k: i128) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: k,
        }
    }

    fn var(index: usize) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(index, 1);
        Self {
            coeffs,
            constant: 0,
        }
    }

    fn is_constant(&self) -> bool {
        self.coeffs.values().all(|&c| c == 0)
    }

    fn neg(&self) -> Option<Self> {
        self.scale(-1)
    }

    fn scale(&self, factor: i128) -> Option<Self> {
        let mut coeffs = BTreeMap::new();
        for (&index, &c) in &self.coeffs {
            coeffs.insert(index, c.checked_mul(factor)?);
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_mul(factor)?,
        })
    }

    fn add(&self, other: &Self) -> Option<Self> {
        let mut coeffs = self.coeffs.clone();
        for (&index, &c) in &other.coeffs {
            let slot = coeffs.entry(index).or_insert(0);
            *slot = slot.checked_add(c)?;
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_add(other.constant)?,
        })
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.neg()?)
    }
}

/// How one registered atom translates to a tableau row bound per polarity.
///
/// One row per atom is enough for **both** kinds: an order atom's two polarities
/// are mutually exclusive, so they share the row (upper bound when true, lower
/// bound when false), and an equality atom needs the row only when asserted true,
/// where `Rel::Eq` pins it from both sides at once.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AtomRow {
    /// An order atom: `when_true` / `when_false` are the bounds its two polarities
    /// impose on `row`.
    Order {
        row: usize,
        when_true: (simplex::Rel, Rational),
        when_false: (simplex::Rel, Rational),
    },
    /// An equality atom `Σ cⱼ·xⱼ = rhs`, live only when asserted true (asserted
    /// false it is a disjunction the conjunctive view drops, exactly as
    /// [`LiaTheory::live_lits`] already records). `rhs` also pivots the two strict
    /// branches equality-true propagation probes (`≤ rhs−1` and `≥ rhs+1`).
    Equality { row: usize, rhs: Rational },
    /// No row: the engine cannot see this atom, so it must decide **nothing** while
    /// the atom is live.
    None,
}

/// The warm rational engine plus the bookkeeping that maps its rows back to atoms.
///
/// Structurally identical to [`crate::lra_online`]'s: the tableau is built once
/// over every registered atom's row, and an assert only moves that row's bound, so
/// a re-check warm-starts from the previous basis.
struct IntSimplexEngine {
    inner: simplex::Incremental,
    /// Row → the registered atom that owns it (the conflict-core map).
    row_atom: Vec<usize>,
    /// The bounds currently imposed, positionally aligned with the live set
    /// [`IntSimplexEngine::sync`] reconciles against.
    active: Vec<(usize, simplex::Rel, Rational)>,
    /// Whether each row currently carries a bound. A row holds one bound at a time,
    /// so an attempt to bound an already-bounded row means the live system is not
    /// representable here and `sync` declines rather than dropping the earlier one.
    row_bounded: Vec<bool>,
}

impl IntSimplexEngine {
    /// Brings the engine's bound stack in line with `live`. Diverging suffixes are
    /// retracted and the remainder asserted, so the engine's state is a pure
    /// function of `live` — no hidden coupling to call order.
    ///
    /// Returns `false` if a live bound lands on an already-bounded row, which means
    /// the engine does not see the whole live system; the caller must then **not**
    /// trust a refutation from it.
    fn sync(&mut self, live: &[(usize, simplex::Rel, Rational)]) -> bool {
        // The shared prefix must match on the WHOLE bound, not just the row: an
        // order atom's two polarities ride the same row, so a pop and re-assert at
        // the opposite value keeps the row index and changes only the relation.
        let mut shared = 0usize;
        while shared < self.active.len()
            && shared < live.len()
            && live[shared] == self.active[shared]
        {
            shared += 1;
        }
        while self.active.len() > shared {
            let (row, _, _) = self
                .active
                .pop()
                .expect("non-empty above the shared prefix");
            self.inner.retract(row);
            self.row_bounded[row] = false;
        }
        for &(row, rel, rhs) in &live[shared..] {
            if self.row_bounded[row] {
                return false;
            }
            self.inner.assert_bound(row, rel, rhs);
            self.row_bounded[row] = true;
            self.active.push((row, rel, rhs));
        }
        true
    }
}

/// Outcome of the warm rational filter over the live integer system.
enum RationalFilter {
    /// The relaxation is infeasible, so the integer system is too. The payload is
    /// the Farkas support mapped back to asserted atom literals — a sound conflict
    /// core that needed no deletion minimization.
    Refuted(Vec<TheoryLit>),
    /// The relaxation has an **integral** point, which is an integer solution of the
    /// live conjunction outright.
    IntegralPoint,
    /// Nothing decided here: fall through to the trusted offline integer decider.
    Inconclusive,
}

/// Outcome of one speculative entailment probe on the warm engine.
enum ProbeOutcome {
    /// The probed extension is rationally infeasible, so it is integer-infeasible;
    /// the payload is the **asserted-only** Farkas reason.
    Refuted(Vec<TheoryLit>),
    /// The engine decided, and the extension is not refuted — no propagation, and
    /// no point re-asking the offline relaxation.
    NotRefuted,
    /// The engine could not decide (absent / partial view / overflow): the caller
    /// falls back to the term-level LP probe.
    Undecided,
}

/// Assigns every registered atom a tableau row and builds the warm engine over
/// them, returning the per-atom row map alongside.
///
/// Returns `None` — leaving the theory on the offline decider alone, exactly as
/// before — when no atom yields a row or the dense tableau would exceed
/// [`simplex::MAX_TABLEAU_CELLS`]. Both declines are structural and deterministic.
fn build_int_simplex_engine(
    arena: &TermArena,
    atom_terms: &[TermId],
    allow_opaque_apps: bool,
) -> Option<(Vec<AtomRow>, IntSimplexEngine)> {
    let mut builder = IntRowBuilder::new(allow_opaque_apps);
    let mut atom_rows = Vec::with_capacity(atom_terms.len());
    let mut rows_sparse: Vec<Vec<(usize, Rational)>> = Vec::new();
    let mut row_atom: Vec<usize> = Vec::new();

    for (atom, &term) in atom_terms.iter().enumerate() {
        let row = builder
            .build(arena, term)
            .and_then(|shape| open_row(&shape, atom, &mut rows_sparse, &mut row_atom))
            .unwrap_or(AtomRow::None);
        atom_rows.push(row);
    }
    if rows_sparse.is_empty() {
        return None;
    }
    let inner = simplex::Incremental::new(builder.next_var, rows_sparse)?;
    debug_assert_eq!(inner.rows(), row_atom.len());
    let row_bounded = vec![false; row_atom.len()];
    Some((
        atom_rows,
        IntSimplexEngine {
            inner,
            row_atom,
            active: Vec::new(),
            row_bounded,
        },
    ))
}

/// A normalized atom: the row's variable coefficients plus the bound(s) its
/// polarities impose, before a row index is allocated.
enum RowShape {
    /// `Σ cⱼ·xⱼ ≤ true_rhs` when asserted true, `≥ false_rhs` when asserted false.
    Order {
        coeffs: BTreeMap<usize, i128>,
        true_rhs: i128,
        false_rhs: i128,
    },
    /// `Σ cⱼ·xⱼ = rhs` when asserted true; nothing when asserted false.
    Equality {
        coeffs: BTreeMap<usize, i128>,
        rhs: i128,
    },
}

/// Allocates a tableau row for `shape` and returns the atom's [`AtomRow`].
fn open_row(
    shape: &RowShape,
    atom: usize,
    rows_sparse: &mut Vec<Vec<(usize, Rational)>>,
    row_atom: &mut Vec<usize>,
) -> Option<AtomRow> {
    let sparse: Vec<(usize, Rational)> = match shape {
        RowShape::Order { coeffs, .. } | RowShape::Equality { coeffs, .. } => coeffs,
    }
    .iter()
    .filter(|&(_, &c)| c != 0)
    .map(|(&j, &c)| (j, Rational::integer(c)))
    .collect();
    // A variable-free atom is a ground truth value the offline decider settles;
    // an all-zero tableau row states nothing useful and is not worth the cell.
    if sparse.is_empty() {
        return None;
    }
    let row = rows_sparse.len();
    rows_sparse.push(sparse);
    row_atom.push(atom);
    Some(match *shape {
        RowShape::Order {
            true_rhs,
            false_rhs,
            ..
        } => AtomRow::Order {
            row,
            when_true: (simplex::Rel::Le, Rational::integer(true_rhs)),
            when_false: (simplex::Rel::Ge, Rational::integer(false_rhs)),
        },
        RowShape::Equality { rhs, .. } => AtomRow::Equality {
            row,
            rhs: Rational::integer(rhs),
        },
    })
}

/// Normalizes integer atom terms into [`RowShape`]s over dense variable indices.
struct IntRowBuilder {
    var_index: BTreeMap<SymbolId, usize>,
    opaque_index: BTreeMap<TermId, usize>,
    next_var: usize,
    allow_opaque_apps: bool,
}

impl IntRowBuilder {
    fn new(allow_opaque_apps: bool) -> Self {
        Self {
            var_index: BTreeMap::new(),
            opaque_index: BTreeMap::new(),
            next_var: 0,
            allow_opaque_apps,
        }
    }

    fn index_of(&mut self, symbol: SymbolId) -> usize {
        let next = self.next_var;
        let index = *self.var_index.entry(symbol).or_insert(next);
        if index == next {
            self.next_var += 1;
        }
        index
    }

    fn index_of_opaque(&mut self, term: TermId) -> usize {
        let next = self.next_var;
        let index = *self.opaque_index.entry(term).or_insert(next);
        if index == next {
            self.next_var += 1;
        }
        index
    }

    /// Parses one atom term into its [`RowShape`], or `None` for any shape outside
    /// integer linear arithmetic (which registers as [`AtomRow::None`]).
    ///
    /// This is where the **strict-to-non-strict tightening** happens: with integral
    /// coefficients and constants, `e < 0` over ℤ is exactly `e ≤ −1`, so no strict
    /// row is ever built. That is an equivalence over ℤ, not a relaxation, which is
    /// what keeps a rational refutation of these rows a sound integer refutation —
    /// and it is also what makes the relaxation strong enough to refute the
    /// integer-only `0 < x ∧ x < 1`.
    fn build(&mut self, arena: &TermArena, term: TermId) -> Option<RowShape> {
        match arena.node(term) {
            TermNode::App { op, args }
                if matches!(op, Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe) =>
            {
                let (left, right) = (args[0], args[1]);
                // `e ⋈ 0` with the atom's true-polarity direction folded in, so
                // `true` is always `e ≤ true_target` and `false` is `e ≥ false_target`.
                let (expr, true_target, false_target): (IntLin, i128, i128) = match op {
                    // a < b  ⇔  a−b ≤ −1 ;  ¬  ⇔  a−b ≥ 0
                    Op::IntLt => (
                        self.linearize(arena, left)?
                            .sub(&self.linearize(arena, right)?)?,
                        -1,
                        0,
                    ),
                    // a ≤ b  ⇔  a−b ≤ 0  ;  ¬  ⇔  a−b ≥ 1
                    Op::IntLe => (
                        self.linearize(arena, left)?
                            .sub(&self.linearize(arena, right)?)?,
                        0,
                        1,
                    ),
                    // a > b  ⇔  b−a ≤ −1 ;  ¬  ⇔  b−a ≥ 0
                    Op::IntGt => (
                        self.linearize(arena, right)?
                            .sub(&self.linearize(arena, left)?)?,
                        -1,
                        0,
                    ),
                    // a ≥ b  ⇔  b−a ≤ 0  ;  ¬  ⇔  b−a ≥ 1
                    Op::IntGe => (
                        self.linearize(arena, right)?
                            .sub(&self.linearize(arena, left)?)?,
                        0,
                        1,
                    ),
                    _ => return None,
                };
                if expr.is_constant() {
                    return None;
                }
                Some(RowShape::Order {
                    true_rhs: true_target.checked_sub(expr.constant)?,
                    false_rhs: false_target.checked_sub(expr.constant)?,
                    coeffs: expr.coeffs,
                })
            }
            TermNode::App { op: Op::Eq, args } if is_int(arena, args[0]) => {
                let expr = self
                    .linearize(arena, args[0])?
                    .sub(&self.linearize(arena, args[1])?)?;
                if expr.is_constant() {
                    return None;
                }
                Some(RowShape::Equality {
                    rhs: 0i128.checked_sub(expr.constant)?,
                    coeffs: expr.coeffs,
                })
            }
            _ => None,
        }
    }

    /// Turns an integer term into an [`IntLin`]; `None` on overflow or a non-linear
    /// / non-integer subterm.
    ///
    /// An explicit worklist, not native recursion: an SMT-LIB source controls the
    /// nesting depth directly with a left-associated `(+ (+ (+ n 1) 1) 1)` spine,
    /// and a recursive walk **aborts the process** there instead of declining (the
    /// failure mode fixed in `fcc8760d`, and the reason `crate::lra`'s integer
    /// collector is written the same way).
    fn linearize(&mut self, arena: &TermArena, term: TermId) -> Option<IntLin> {
        enum Step {
            Enter(TermId),
            Build(TermId),
        }
        let mut work = vec![Step::Enter(term)];
        let mut values: Vec<IntLin> = Vec::new();
        while let Some(step) = work.pop() {
            match step {
                Step::Enter(t) => match arena.node(t) {
                    TermNode::IntConst(value) => values.push(IntLin::constant(*value)),
                    TermNode::Symbol(symbol) if is_int(arena, t) => {
                        let index = self.index_of(*symbol);
                        values.push(IntLin::var(index));
                    }
                    TermNode::App {
                        op: Op::Apply(_), ..
                    } if self.allow_opaque_apps && is_int(arena, t) => {
                        let index = self.index_of_opaque(t);
                        values.push(IntLin::var(index));
                    }
                    TermNode::App {
                        op: Op::IntNeg,
                        args,
                    } => {
                        let arg = args[0];
                        work.push(Step::Build(t));
                        work.push(Step::Enter(arg));
                    }
                    TermNode::App {
                        op: Op::IntAdd | Op::IntSub | Op::IntMul,
                        args,
                    } => {
                        let (left, right) = (args[0], args[1]);
                        work.push(Step::Build(t));
                        // Pushed right-first so the left operand lands first.
                        work.push(Step::Enter(right));
                        work.push(Step::Enter(left));
                    }
                    _ => return None,
                },
                Step::Build(t) => {
                    let TermNode::App { op, .. } = arena.node(t) else {
                        return None;
                    };
                    match op {
                        Op::IntNeg => {
                            let inner = values.pop()?;
                            values.push(inner.neg()?);
                        }
                        Op::IntAdd | Op::IntSub | Op::IntMul => {
                            let right = values.pop()?;
                            let left = values.pop()?;
                            let built = match op {
                                Op::IntAdd => left.add(&right)?,
                                Op::IntSub => left.sub(&right)?,
                                // Linear only: one side must be a constant.
                                _ if left.is_constant() => right.scale(left.constant)?,
                                _ if right.is_constant() => left.scale(right.constant)?,
                                _ => return None,
                            };
                            values.push(built);
                        }
                        _ => return None,
                    }
                }
            }
        }
        // Exactly one result for a well-formed walk.
        if values.len() == 1 {
            values.pop()
        } else {
            None
        }
    }
}

impl LiaTheory {
    /// Builds an online `LIA` theory over the given atom terms. Each `(< a b)` /
    /// `(<= a b)` / `(> a b)` / `(>= a b)` and each integer `(= a b)` registers as
    /// a constraint atom; any other atom registers as a no-op so indices stay
    /// aligned with the caller's atom numbering.
    #[must_use]
    pub fn new(arena: &TermArena, atom_terms: &[TermId]) -> Self {
        Self::new_with_options(arena, atom_terms, false)
    }

    /// Builds an online `LIA` theory that treats Int-sorted UF applications as
    /// opaque integer variables. This is an UNSAT-oriented UFLIA combination hook:
    /// opaque-app infeasibility and LP propagation are sound, but satisfiable
    /// opaque abstractions remain model-incomplete and therefore replay as
    /// `Unknown` at the combined layer.
    #[must_use]
    pub(crate) fn new_with_opaque_apps(arena: &TermArena, atom_terms: &[TermId]) -> Self {
        Self::new_with_options(arena, atom_terms, true)
    }

    fn new_with_options(arena: &TermArena, atom_terms: &[TermId], allow_opaque_apps: bool) -> Self {
        let kinds: Vec<AtomKind> = atom_terms.iter().map(|&t| classify(arena, t)).collect();
        let count = atom_terms.len();
        let (atom_rows, simplex) =
            match build_int_simplex_engine(arena, atom_terms, allow_opaque_apps) {
                Some((rows, engine)) => (rows, Some(RefCell::new(engine))),
                None => (vec![AtomRow::None; count], None),
            };
        Self {
            atom_terms: atom_terms.to_vec(),
            kinds,
            assigned: vec![None; count],
            assigned_log: Vec::new(),
            trail: Vec::new(),
            arena: arena.clone(),
            defer_feasibility_until_propagate: false,
            skip_entailment_propagation: false,
            allow_opaque_apps,
            deadline: None,
            atom_rows,
            simplex,
        }
    }

    /// Attaches a wall-clock deadline to this theory. Once the deadline passes,
    /// feasibility and propagation probes return inconclusive results rather than
    /// deriving conflicts or propagations.
    #[must_use]
    pub(crate) fn with_deadline(mut self, deadline: Option<Instant>) -> Self {
        self.deadline = deadline;
        self
    }

    /// Builds the same theory in large-query mode: assertions are recorded cheaply,
    /// one full feasibility check runs at the theory-propagation boundary, and LP
    /// entailment propagation is skipped. This preserves soundness while avoiding
    /// the pathological "hundreds of full LIA solves before the first decision"
    /// shape seen in generated `QF_UFLIA` arithmetic skeletons.
    #[must_use]
    pub(crate) fn new_deferred_for_large_search(arena: &TermArena, atom_terms: &[TermId]) -> Self {
        Self::new_deferred_with_options(arena, atom_terms, false)
    }

    /// Builds the same large-query deferred theory while treating Int-sorted UF
    /// applications as opaque integer variables. This is used by the combined
    /// UFLIA CDCL(T) path: SAT search can record a large opaque-app assignment
    /// cheaply, then surface one conservative feasibility conflict at the
    /// theory-propagation boundary.
    #[must_use]
    pub(crate) fn new_with_opaque_apps_deferred_for_large_search(
        arena: &TermArena,
        atom_terms: &[TermId],
    ) -> Self {
        Self::new_deferred_with_options(arena, atom_terms, true)
    }

    fn new_deferred_with_options(
        arena: &TermArena,
        atom_terms: &[TermId],
        allow_opaque_apps: bool,
    ) -> Self {
        let mut theory = Self::new_with_options(arena, atom_terms, allow_opaque_apps);
        theory.defer_feasibility_until_propagate = true;
        theory.skip_entailment_propagation = true;
        theory
    }

    /// Whether the warm rational filter was built at all. Test-only: it exists so
    /// the filter cannot silently become inert (an engine that stops being built
    /// would leave every measurement below meaningless while every test still
    /// passed, because the offline decider answers identically — just slower).
    #[cfg(test)]
    #[must_use]
    pub(crate) fn uses_simplex(&self) -> bool {
        self.simplex.is_some()
    }

    /// The warm filter's verdict on the *current* live set, as a stable string.
    /// Test-only: the soundness tests need to know **which** path answered, because
    /// the two conclusive ones carry different obligations (a refutation must be a
    /// genuine integer refutation; an integral point must be a genuine integer
    /// model).
    #[cfg(test)]
    #[must_use]
    pub(crate) fn filter_verdict(&self) -> &'static str {
        match self.rational_filter() {
            RationalFilter::Refuted(_) => "refuted",
            RationalFilter::IntegralPoint => "integral",
            RationalFilter::Inconclusive => "inconclusive",
        }
    }

    /// The literals the filter would name as the conflict core, if it refutes.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn filter_core(&self) -> Option<Vec<TheoryLit>> {
        match self.rational_filter() {
            RationalFilter::Refuted(core) => Some(core),
            RationalFilter::IntegralPoint | RationalFilter::Inconclusive => None,
        }
    }

    /// The currently-asserted literals that carry a live constraint. Test-only
    /// mirror of [`Self::live_lits`] for the differential soundness tests.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn live_literals(&self) -> Vec<TheoryLit> {
        self.live_lits()
    }

    /// The polarity-applied conjunctive terms for `lits`, in a working arena — what
    /// the offline decider is handed. Test-only.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn terms_for(&self, lits: &[TheoryLit]) -> Option<(TermArena, Vec<TermId>)> {
        self.live_terms(lits)
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
        self.feasibility_with_core_minimization(true)
    }

    /// Same as [`Self::feasibility`], but lets large-query callers keep the full
    /// infeasible set as the conflict core. A full core is less precise but still
    /// sound; avoiding deletion minimization is critical when the point of the
    /// caller is to avoid hundreds of repeated LIA checks.
    fn feasibility_with_core_minimization(&self, minimize: bool) -> Feasibility {
        if self.deadline_expired() {
            return Feasibility::Unknown;
        }
        let lits = self.live_lits();
        if lits.is_empty() {
            return Feasibility::Sat;
        }
        // The warm rational filter first: it refutes with a small Farkas core, or
        // confirms with an integral witness, without touching the offline decider.
        match self.rational_filter() {
            RationalFilter::Refuted(core) => return Feasibility::Unsat(core),
            RationalFilter::IntegralPoint => return Feasibility::Sat,
            RationalFilter::Inconclusive => {}
        }
        let Some((arena, terms)) = self.live_terms(&lits) else {
            return Feasibility::Unknown;
        };
        match self.check_terms(&arena, &terms) {
            Ok(CheckResult::Sat(_)) => Feasibility::Sat,
            Ok(CheckResult::Unknown(_)) | Err(_) => Feasibility::Unknown,
            Ok(CheckResult::Unsat) if minimize => Feasibility::Unsat(minimize_core(
                &arena,
                &lits,
                &terms,
                self.allow_opaque_apps,
                self.deadline,
            )),
            Ok(CheckResult::Unsat) => Feasibility::Unsat(lits),
        }
    }

    fn check_terms(&self, arena: &TermArena, terms: &[TermId]) -> Result<CheckResult, SolverError> {
        check_terms_with_options(arena, terms, self.allow_opaque_apps, self.deadline)
    }

    fn lp_relaxation(&self, arena: &TermArena, terms: &[TermId]) -> LpRelaxation {
        if self.deadline_expired() {
            return LpRelaxation::Unknown;
        }
        if self.allow_opaque_apps {
            lp_relaxation_feasibility_opaque_apps(arena, terms)
        } else {
            lp_relaxation_feasibility(arena, terms)
        }
    }

    fn deadline_expired(&self) -> bool {
        self.deadline.is_some_and(|d| Instant::now() >= d)
    }

    /// The row bounds the currently-asserted atoms impose, in assert order.
    ///
    /// `None` when a live atom has **no** row. On such a partial view a refutation
    /// would still be sound (a subset of an infeasible set can only be infeasible
    /// because the whole set is), but a *feasible* point would not be: it may
    /// violate the constraint the engine cannot see. Rather than split the two
    /// directions, the filter declines outright and the offline decider runs.
    fn live_bounds(&self) -> Option<Vec<(usize, simplex::Rel, Rational)>> {
        let mut out = Vec::with_capacity(self.assigned_log.len());
        for &atom in &self.assigned_log {
            let Some(value) = self.assigned[atom] else {
                continue;
            };
            match self.kinds[atom] {
                // Contributes no constraint to the conjunctive view either.
                AtomKind::Unsupported => {}
                AtomKind::Equality if !value => {}
                AtomKind::Equality => match self.atom_rows[atom] {
                    AtomRow::Equality { row, rhs } => out.push((row, simplex::Rel::Eq, rhs)),
                    AtomRow::Order { .. } | AtomRow::None => return None,
                },
                AtomKind::Order => match self.atom_rows[atom] {
                    AtomRow::Order {
                        row,
                        when_true,
                        when_false,
                    } => {
                        let (rel, rhs) = if value { when_true } else { when_false };
                        out.push((row, rel, rhs));
                    }
                    AtomRow::Equality { .. } | AtomRow::None => return None,
                },
            }
        }
        Some(out)
    }

    /// Decides the live system's **rational relaxation** on the warm engine.
    ///
    /// See the section comment above [`IntLin`] for why both of its conclusive
    /// answers transfer to ℤ. Every other outcome is [`RationalFilter::Inconclusive`]
    /// and the offline integer decider runs unchanged.
    fn rational_filter(&self) -> RationalFilter {
        let Some(cell) = &self.simplex else {
            return RationalFilter::Inconclusive;
        };
        let Some(bounds) = self.live_bounds() else {
            return RationalFilter::Inconclusive;
        };
        if bounds.is_empty() {
            return RationalFilter::Inconclusive;
        }
        let mut engine = cell.borrow_mut();
        if !engine.sync(&bounds) {
            return RationalFilter::Inconclusive;
        }
        match engine.inner.check(self.deadline) {
            simplex::Status::Infeasible(rows) => {
                // An empty Farkas support means the refutation could not be
                // *explained*; the offline route then produces the core it always
                // did, rather than this path widening to the full asserted set.
                let core = self.rows_to_core(&engine, &rows);
                if core.is_empty() {
                    RationalFilter::Inconclusive
                } else {
                    RationalFilter::Refuted(core)
                }
            }
            simplex::Status::Feasible => match engine.inner.point() {
                Some(point) if point.iter().all(|v| v.is_integer()) => {
                    RationalFilter::IntegralPoint
                }
                // A fractional point says nothing about ℤ — branch-and-bound's job.
                _ => RationalFilter::Inconclusive,
            },
            simplex::Status::Unknown => RationalFilter::Inconclusive,
        }
    }

    /// Maps a self-verified Farkas support (row indices) back to the asserted atom
    /// literals behind it: the conflict core. Rows whose atom is not currently
    /// assigned are skipped defensively (only bounded rows can carry a nonzero
    /// multiplier, and only live atoms are bounded).
    ///
    /// Emitted in **assert order**, matching [`Self::live_lits`]. That matters
    /// downstream: [`Self::core_conflict_propagation`] pivots on the *last* literal,
    /// and the deferred large-query path wants the most recently asserted one there,
    /// not whichever atom happened to own the lowest row index.
    fn rows_to_core(&self, engine: &IntSimplexEngine, rows: &[usize]) -> Vec<TheoryLit> {
        let mut support: BTreeSet<usize> = BTreeSet::new();
        for &row in rows {
            if let Some(&atom) = engine.row_atom.get(row) {
                support.insert(atom);
            }
        }
        self.core_in_assert_order(&support)
    }

    /// The literals of `support` in **assert order**, deduplicated, skipping atoms
    /// that are not currently assigned.
    fn core_in_assert_order(&self, support: &BTreeSet<usize>) -> Vec<TheoryLit> {
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut core = Vec::new();
        for &atom in &self.assigned_log {
            if !support.contains(&atom) {
                continue;
            }
            let Some(value) = self.assigned.get(atom).copied().flatten() else {
                continue;
            };
            if seen.insert(atom) {
                core.push(TheoryLit { atom, value });
            }
        }
        core
    }

    /// Speculatively imposes `extra` on top of the live system and reports whether
    /// the relaxation is refuted, with the **asserted-only** Farkas reason
    /// (`probe_atom`'s own rows excluded — its bound was added speculatively and is
    /// not asserted).
    ///
    /// The speculative bounds are retracted before returning, so the engine's state
    /// stays a pure function of the live set.
    fn engine_probe(
        &self,
        extra: &[(usize, simplex::Rel, Rational)],
        probe_atom: usize,
    ) -> ProbeOutcome {
        let Some(cell) = &self.simplex else {
            return ProbeOutcome::Undecided;
        };
        let Some(bounds) = self.live_bounds() else {
            return ProbeOutcome::Undecided;
        };
        let mut engine = cell.borrow_mut();
        if !engine.sync(&bounds) {
            return ProbeOutcome::Undecided;
        }
        // Every probed row must be free: the probed atom is unassigned, so its row
        // carries no live bound.
        if extra.iter().any(|&(row, _, _)| engine.row_bounded[row]) {
            return ProbeOutcome::Undecided;
        }
        for &(row, rel, rhs) in extra {
            engine.inner.assert_bound(row, rel, rhs);
        }
        let status = engine.inner.check(self.deadline);
        for &(row, _, _) in extra {
            engine.inner.retract(row);
        }
        match status {
            simplex::Status::Infeasible(rows) => {
                // The speculative row's atom is excluded outright: its bound was
                // never asserted, so it may not appear in the reason.
                let mut support: BTreeSet<usize> = BTreeSet::new();
                for &row in &rows {
                    if let Some(&atom) = engine.row_atom.get(row)
                        && atom != probe_atom
                    {
                        support.insert(atom);
                    }
                }
                let core = self.core_in_assert_order(&support);
                // A refutation resting on no asserted atom is not a propagation
                // under the asserted state.
                if core.is_empty() {
                    ProbeOutcome::NotRefuted
                } else {
                    ProbeOutcome::Refuted(core)
                }
            }
            simplex::Status::Feasible => ProbeOutcome::NotRefuted,
            simplex::Status::Unknown => ProbeOutcome::Undecided,
        }
    }

    /// Engine probe for "atom asserted at `probe_value` is infeasible" — so the atom
    /// is entailed at the opposite polarity.
    fn engine_probe_atom(&self, atom: usize, probe_value: bool) -> ProbeOutcome {
        let extra = match self.atom_rows.get(atom) {
            Some(&AtomRow::Order {
                row,
                when_true,
                when_false,
            }) => {
                let (rel, rhs) = if probe_value { when_true } else { when_false };
                vec![(row, rel, rhs)]
            }
            // The equality's false polarity is a disjunction; only `true` is probed.
            Some(&AtomRow::Equality { row, rhs }) if probe_value => {
                vec![(row, simplex::Rel::Eq, rhs)]
            }
            _ => return ProbeOutcome::Undecided,
        };
        self.engine_probe(&extra, atom)
    }

    /// Engine probe for one strict branch of an integer equality atom: `reverse ==
    /// false` is `Σ c·x ≤ rhs − 1` (the left branch `lhs < rhs`), `true` is
    /// `Σ c·x ≥ rhs + 1`. Exact over ℤ, by the same tightening the rows are built
    /// with.
    fn engine_probe_equality_branch(&self, atom: usize, reverse: bool) -> ProbeOutcome {
        let Some(&AtomRow::Equality { row, rhs }) = self.atom_rows.get(atom) else {
            return ProbeOutcome::Undecided;
        };
        let one = Rational::integer(1);
        let extra = if reverse {
            let Some(bound) = rhs.checked_add(one) else {
                return ProbeOutcome::Undecided;
            };
            vec![(row, simplex::Rel::Ge, bound)]
        } else {
            let Some(bound) = rhs.checked_sub(one) else {
                return ProbeOutcome::Undecided;
            };
            vec![(row, simplex::Rel::Le, bound)]
        };
        self.engine_probe(&extra, atom)
    }

    /// Converts a currently-infeasible core into a propagation that contradicts
    /// one asserted core literal. `Dpll::theory_propagate` turns that contradiction
    /// back into the conflict clause `¬core`, so this is the same sound conflict
    /// explanation an eager `assert` would have returned.
    fn core_conflict_propagation(core: &[TheoryLit]) -> Option<TheoryProp> {
        let (&pivot, reason) = core.split_last()?;
        Some(TheoryProp {
            lit: TheoryLit {
                atom: pivot.atom,
                value: !pivot.value,
            },
            reason: reason.to_vec(),
        })
    }

    /// In deferred large-query mode, perform exactly one full feasibility check at
    /// the propagation boundary and surface an infeasible live set as a normal
    /// theory conflict propagation.
    fn deferred_feasibility_conflict(&self) -> Option<TheoryProp> {
        match self.feasibility_with_core_minimization(false) {
            Feasibility::Unsat(core) => Self::core_conflict_propagation(&core),
            Feasibility::Sat | Feasibility::Unknown => None,
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
    /// (and deletion-minimized) core. Equality atoms are handled with two conservative
    /// probes: `eq=false` is propagated when `asserted ∧ eq` is LP-infeasible, and
    /// `eq=true` is propagated only when both strict branches `lhs < rhs` and
    /// `rhs < lhs` are LP-infeasible under the asserted set. An LP-`Feasible` probe is
    /// inconclusive about ℤ, and an `Unknown` (overflow / outside the fragment /
    /// backstop) probe declines: either way nothing is emitted — a sound
    /// under-approximation that **never** fabricates a propagation.
    #[must_use]
    pub fn propagate(&self) -> Vec<TheoryProp> {
        if self.deadline_expired() {
            return Vec::new();
        }
        if self.defer_feasibility_until_propagate {
            if let Some(prop) = self.deferred_feasibility_conflict() {
                return vec![prop];
            }
            if self.skip_entailment_propagation {
                return Vec::new();
            }
        }

        let asserted = self.live_lits();
        let mut out = Vec::new();
        for atom in 0..self.kinds.len() {
            if self.deadline_expired() {
                return out;
            }
            if self.assigned.get(atom).copied().flatten().is_some() {
                continue; // already decided by the search
            }
            match self.kinds[atom] {
                AtomKind::Order => {
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
                AtomKind::Equality => {
                    if let Some(reason) = self.probe_equality_true(&asserted, atom) {
                        out.push(TheoryProp {
                            lit: TheoryLit { atom, value: true },
                            reason,
                        });
                        continue;
                    }
                    // `asserted ∧ eq` LP-infeasible ⇒ equality is false. This probe uses
                    // the ordinary equality-true live term, which the conjunctive LIA
                    // checker already supports.
                    if let Some(reason) = self.probe_entails(&asserted, atom, true) {
                        out.push(TheoryProp {
                            lit: TheoryLit { atom, value: false },
                            reason,
                        });
                    }
                }
                AtomKind::Unsupported => {}
            }
        }
        out
    }

    /// Equality-true propagation. For integer linear terms, `lhs = rhs` follows from
    /// the asserted set when both strict branches `lhs < rhs` and `rhs < lhs` are
    /// infeasible. Each branch is checked independently by the LP relaxation; the union
    /// of the two asserted-only reasons is therefore a sound reason for equality.
    fn probe_equality_true(&self, asserted: &[TheoryLit], atom: usize) -> Option<Vec<TheoryLit>> {
        let left_reason = match self.engine_probe_equality_branch(atom, false) {
            ProbeOutcome::Refuted(core) => core,
            ProbeOutcome::NotRefuted => return None,
            ProbeOutcome::Undecided => {
                if !self.probe_equality_branch_lp_infeasible(asserted, atom, false) {
                    return None;
                }
                self.minimize_equality_branch_reason(asserted, atom, false)
            }
        };
        let right_reason = match self.engine_probe_equality_branch(atom, true) {
            ProbeOutcome::Refuted(core) => core,
            ProbeOutcome::NotRefuted => return None,
            ProbeOutcome::Undecided => {
                if !self.probe_equality_branch_lp_infeasible(asserted, atom, true) {
                    return None;
                }
                self.minimize_equality_branch_reason(asserted, atom, true)
            }
        };

        let mut seen = HashSet::new();
        let mut reason = Vec::new();
        for lit in left_reason.into_iter().chain(right_reason) {
            if seen.insert((lit.atom, lit.value)) {
                reason.push(lit);
            }
        }
        if reason.is_empty() {
            None
        } else {
            Some(reason)
        }
    }

    /// Appends one strict disequality branch for an integer equality atom to the
    /// provided scratch arena. `reverse=false` builds `lhs < rhs`; `reverse=true`
    /// builds `rhs < lhs`.
    fn strict_equality_branch(
        &self,
        arena: &mut TermArena,
        atom: usize,
        reverse: bool,
    ) -> Option<TermId> {
        let eq = self.atom_terms[atom];
        let TermNode::App { op: Op::Eq, args } = self.arena.node(eq) else {
            return None;
        };
        if args.len() != 2 || !is_int(&self.arena, args[0]) || !is_int(&self.arena, args[1]) {
            return None;
        }
        if reverse {
            arena.int_lt(args[1], args[0]).ok()
        } else {
            arena.int_lt(args[0], args[1]).ok()
        }
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
        // The warm engine answers with the Farkas reason directly — no deletion
        // minimization, which on this path cost one full LP *per asserted literal*.
        match self.engine_probe_atom(atom, probe_value) {
            ProbeOutcome::Refuted(core) => return Some(core),
            ProbeOutcome::NotRefuted => return None,
            ProbeOutcome::Undecided => {}
        }
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
        matches!(self.lp_relaxation(&arena, &terms), LpRelaxation::Infeasible)
    }

    /// Same LP-infeasibility probe as [`Self::probe_lp_infeasible`], but for one
    /// temporary strict equality branch that is not a registered atom variable.
    fn probe_equality_branch_lp_infeasible(
        &self,
        asserted: &[TheoryLit],
        atom: usize,
        reverse: bool,
    ) -> bool {
        let Some((arena, mut terms)) = self.live_terms(asserted) else {
            return false;
        };
        let mut arena = arena;
        let Some(extra) = self.strict_equality_branch(&mut arena, atom, reverse) else {
            return false;
        };
        terms.push(extra);
        matches!(self.lp_relaxation(&arena, &terms), LpRelaxation::Infeasible)
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
            if self.deadline_expired() {
                break;
            }
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

    /// Deletion-minimizes an asserted-only reason for one temporary equality branch.
    /// Every retained subset is rechecked by
    /// [`Self::probe_equality_branch_lp_infeasible`], so the returned reason remains
    /// a sound explanation for the propagation.
    fn minimize_equality_branch_reason(
        &self,
        asserted: &[TheoryLit],
        atom: usize,
        reverse: bool,
    ) -> Vec<TheoryLit> {
        let mut keep: Vec<bool> = vec![true; asserted.len()];
        for drop_idx in 0..asserted.len() {
            if self.deadline_expired() {
                break;
            }
            keep[drop_idx] = false;
            let subset: Vec<TheoryLit> = asserted
                .iter()
                .zip(&keep)
                .filter_map(|(&lit, &k)| k.then_some(lit))
                .collect();
            if self.probe_equality_branch_lp_infeasible(&subset, atom, reverse) {
                // Still entailed without this literal — drop it.
            } else {
                keep[drop_idx] = true;
            }
        }
        let core: Vec<TheoryLit> = asserted
            .iter()
            .zip(&keep)
            .filter_map(|(&lit, &k)| k.then_some(lit))
            .collect();
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

        if self.defer_feasibility_until_propagate {
            return Ok(());
        }

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
fn minimize_core(
    arena: &TermArena,
    lits: &[TheoryLit],
    terms: &[TermId],
    allow_opaque_apps: bool,
    deadline: Option<Instant>,
) -> Vec<TheoryLit> {
    // Start from the full asserted set; try removing each literal in turn.
    let mut keep: Vec<bool> = vec![true; lits.len()];
    for drop_idx in 0..lits.len() {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }
        keep[drop_idx] = false;
        let subset: Vec<TermId> = terms
            .iter()
            .zip(&keep)
            .filter_map(|(&t, &k)| k.then_some(t))
            .collect();
        let verdict = check_terms_with_options(arena, &subset, allow_opaque_apps, deadline);
        let still_unsat = subset.len() < terms.len() && matches!(verdict, Ok(CheckResult::Unsat));
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

fn check_terms_with_options(
    arena: &TermArena,
    terms: &[TermId],
    allow_opaque_apps: bool,
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    if deadline.is_some_and(|d| Instant::now() >= d) {
        return Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Timeout,
            detail: "online LIA theory check reached its deadline".to_owned(),
        }));
    }
    if allow_opaque_apps {
        check_with_lia_opaque_apps_within(arena, terms, deadline)
    } else {
        check_with_lia_simplex_within(arena, terms, deadline)
    }
}

// --- The online DPLL(T) driver. ---------------------------------------------
//
// The `QF_LIA` search reuses the shared generic [`Dpll<T: TheorySolver>`] from
// [`crate::lra_online`] (made generic in slice 3a), instantiated at `T =
// LiaTheory`. `LiaTheory` implements [`TheorySolver`] (assert / push / pop /
// propagate), so the generic driver's joint unit + theory propagation, 1-UIP
// theory-conflict learning, and non-chronological backjumping drive the integer
// theory verbatim — the same loop that already drives the `LRA` (`T =
// LraTheory`), `UFLRA` (`T = CombinedIncremental`), and `UFLIA` (`T =
// CombinedIncrementalLia`) paths. There is no longer a `QF_LIA`-specific copy of
// the loop. The Tseitin [`Encoder`] below (over `crate::lra_online::Lit`) and the
// `LiaTheory` setup are the only `QF_LIA`-specific pieces.

/// Tseitin encoder from the typed Boolean IR into a CNF skeleton, with the first
/// `atom_terms.len()` variables reserved for the registered `LIA` atoms (numbered
/// to match [`LiaTheory`]).
///
/// `pub(crate)` so the sibling online CDCL(T) LIA entry point
/// ([`crate::lia_theory::check_qf_lia_online_cdclt`]) can reuse the identical
/// skeleton construction and translate its clauses into the generic driver's own
/// literal type.
pub(crate) struct Encoder {
    pub(crate) term_var: HashMap<TermId, usize>,
    pub(crate) var_count: usize,
}

impl Encoder {
    pub(crate) fn new(atom_terms: &[TermId]) -> Self {
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
    pub(crate) fn encode(
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
pub(crate) fn collect_lia_atoms(
    arena: &TermArena,
    term: TermId,
    out: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
) {
    // Memoize EVERY visited node, not just atoms. The assertion structure is a
    // shared DAG, so a subterm reachable by `k` distinct paths (e.g. a bounded
    // `str.replace` result feeding many `str.in_re` NFA positions) would be
    // re-descended `k` times without this guard — exponential in the sharing
    // depth, a deadline-blind hang before the DPLL loop's timeout ever fires
    // (the str.replace×membership deadline hole). Marking interior nodes visited
    // makes the walk linear in the DAG and is verdict-neutral: `out` still holds
    // exactly the distinct LIA atoms (each pushed on its first, now only, visit).
    if !seen.insert(term) {
        return;
    }
    if is_lia_atom(arena, term) {
        out.push(term);
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
    config: &SolverConfig,
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
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let defer_feasibility = should_defer_online_lia_feasibility(atom_count, clauses.len());
    let mut theory = if defer_feasibility {
        LiaTheory::new_deferred_for_large_search(arena, &atom_terms)
    } else {
        LiaTheory::new(arena, &atom_terms)
    }
    .with_deadline(deadline);

    let mut solver = Dpll::new(enc.var_count, atom_count, clauses);
    match solver.solve_with_deadline(&mut theory, deadline) {
        Some(true) => return Ok(CheckResult::Unsat),
        Some(false) => {}
        None => {
            let stats = solver.stats();
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Timeout,
                detail: format!("online LIA DPLL(T) exhausted the configured timeout ({stats})"),
            }));
        }
    }
    // Theory-consistent total assignment: reconstruct an integer model from the
    // live atoms (via the trusted offline decider), add any Boolean leaves from
    // the final DPLL assignment, and replay it.
    match theory_model(&theory) {
        Some(mut model) => {
            add_boolean_leaf_values(arena, &enc, atom_count, &solver, &mut model);
            if replays_integer(arena, assertions, &model) {
                Ok(CheckResult::Sat(model))
            } else {
                Ok(CheckResult::Unknown(unknown(
                    "online LIA model did not replay (arithmetic outside the incremental engine)",
                )))
            }
        }
        _ => Ok(CheckResult::Unknown(unknown(
            "online LIA model did not replay (arithmetic outside the incremental engine)",
        ))),
    }
}

fn should_defer_online_lia_feasibility(atom_count: usize, clause_count: usize) -> bool {
    atom_count >= DEFER_LIA_FEASIBILITY_ATOMS || clause_count >= DEFER_LIA_FEASIBILITY_CLAUSES
}

fn add_boolean_leaf_values(
    arena: &TermArena,
    enc: &Encoder,
    atom_count: usize,
    solver: &Dpll,
    model: &mut Model,
) {
    for (&term, &var) in &enc.term_var {
        if var < atom_count {
            continue;
        }
        if let TermNode::Symbol(symbol) = arena.node(term)
            && arena.sort_of(term) == Sort::Bool
            && let Some(value) = solver.value_of(var)
        {
            model.set(*symbol, Value::Bool(value));
        }
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
    match theory.check_terms(&arena, &terms) {
        Ok(CheckResult::Sat(model)) => Some(model),
        _ => None,
    }
}

/// Whether `model` satisfies every assertion under the ground evaluator with
/// integer theory values plus optional Boolean skeleton leaves. Any non-`true`,
/// non-Int/non-Bool value, or evaluation error makes it not replay (→ `Unknown`,
/// never a wrong `sat`).
pub(crate) fn replays_integer(arena: &TermArena, assertions: &[TermId], model: &Model) -> bool {
    let mut assignment = Assignment::new();
    for (symbol, value) in model.iter() {
        if !matches!(value, Value::Int(_) | Value::Bool(_)) {
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
    // A per-trial deadline. `Dpll` already has a step budget, but `LiaTheory`
    // without a deadline lets ONE offline branch-and-bound run to its 50 000-node
    // cap, and a debug-build fuzz trial that grinds for minutes is a gate that
    // cannot be run at all: trial 2353 of the corpus below hangs the suite for
    // minutes on a stock build, which is why the trial count could never be raised.
    // Expiry only makes the theory answer "don't know", so it can hide a conflict —
    // never invent one — and every clause the gate does check is still checked.
    let deadline = Instant::now().checked_add(std::time::Duration::from_millis(250));
    let mut theory = LiaTheory::new(arena, &atom_terms).with_deadline(deadline);
    let mut solver = Dpll::new(enc.var_count, atom_count, clauses);
    let _ = solver.solve(&mut theory);
    // Read the learned 1-UIP clauses and their lemma provenance off the shared
    // generic driver via its `pub(crate)` test accessors (the same ones the
    // `QF_UFLRA` gate uses), then unzip into the parallel streams the in-source
    // soundness test consumes.
    let lemmas = solver.learned_lemmas();
    let mut learned = Vec::with_capacity(lemmas.len());
    let mut lemma_flags = Vec::with_capacity(lemmas.len());
    let mut lemma_level0 = Vec::with_capacity(lemmas.len());
    for (clause, is_lemma, level0) in lemmas {
        learned.push(clause);
        lemma_flags.push(is_lemma);
        lemma_level0.push(level0);
    }
    Some(OnlineDiag {
        atom_terms,
        atom_count,
        learned,
        lemma_flags,
        lemma_level0,
        analyze_fires: solver.analyze_fires(),
        learned_len_total: solver.learned_len_total(),
        conflict_len_total: solver.conflict_len_total(),
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
    fn online_lia_timeout_reports_dpll_stats() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = iconst(&mut arena, 0);
        let ge = arena.int_ge(x, zero).expect("x>=0");

        let config = SolverConfig::default().with_timeout(std::time::Duration::ZERO);
        let verdict = check_qf_lia_online(&arena, &[ge], &config).expect("timeout result");
        let CheckResult::Unknown(reason) = verdict else {
            panic!("expected timeout unknown");
        };

        assert_eq!(reason.kind, UnknownKind::Timeout);
        assert!(reason.detail.contains("vars="), "{:?}", reason.detail);
        assert!(
            reason.detail.contains("theory_atoms=1"),
            "{:?}",
            reason.detail
        );
        assert!(reason.detail.contains("decisions=0"), "{:?}", reason.detail);
    }

    #[test]
    fn deferred_lia_feasibility_reports_conflict_from_propagate() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = iconst(&mut arena, 0);
        let one = iconst(&mut arena, 1);
        let gt = arena.int_gt(x, zero).expect("x>0");
        let lt = arena.int_lt(x, one).expect("x<1");
        let atoms = [gt, lt];

        let mut theory = LiaTheory::new_deferred_for_large_search(&arena, &atoms);
        assert!(theory.assert(0, true).is_ok());
        assert!(theory.assert(1, true).is_ok());

        let props = theory.propagate();
        assert_eq!(props.len(), 1, "deferred conflict should surface once");
        let prop = props[0].clone();
        assert_eq!(
            theory.assigned[prop.lit.atom],
            Some(!prop.lit.value),
            "propagation must contradict an asserted core literal"
        );

        let mut core = prop.reason;
        core.push(TheoryLit {
            atom: prop.lit.atom,
            value: !prop.lit.value,
        });
        let mut core_arena = arena.clone();
        let core_terms: Vec<TermId> = core
            .iter()
            .map(|lit| {
                if lit.value {
                    atoms[lit.atom]
                } else {
                    core_arena.not(atoms[lit.atom]).expect("not")
                }
            })
            .collect();
        assert_eq!(
            check_with_lia_simplex(&core_arena, &core_terms).expect("core decidable"),
            CheckResult::Unsat,
            "deferred propagation conflict must encode an unsat core"
        );
    }

    #[test]
    fn large_online_lia_root_conflict_uses_deferred_feasibility() {
        let mut arena = TermArena::new();
        let mut assertions = Vec::new();

        for i in 0..DEFER_LIA_FEASIBILITY_ATOMS {
            let y = ivar(&mut arena, &format!("pad_{i}"));
            let zero = iconst(&mut arena, 0);
            assertions.push(arena.int_ge(y, zero).expect("pad>=0"));
        }

        let x = ivar(&mut arena, "x");
        let zero = iconst(&mut arena, 0);
        let one = iconst(&mut arena, 1);
        assertions.push(arena.int_ge(x, one).expect("x>=1"));
        assertions.push(arena.int_le(x, zero).expect("x<=0"));

        assert!(should_defer_online_lia_feasibility(assertions.len(), 0));
        let verdict =
            check_qf_lia_online(&arena, &assertions, &SolverConfig::default()).expect("decidable");
        assert_eq!(verdict, CheckResult::Unsat);
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
    fn equality_atom_true_propagates_from_paired_bounds() {
        // x >= 3 and x <= 3 entail x = 3. Both strict disequality branches are
        // LP-infeasible, so the online theory solver may propagate equality true.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let three = iconst(&mut arena, 3);
        let ge = arena.int_ge(x, three).expect("x>=3");
        let le = arena.int_le(x, three).expect("x<=3");
        let eq = arena.eq(x, three).expect("x=3");

        let mut theory = LiaTheory::new(&arena, &[ge, le, eq]);
        assert!(theory.assert(0, true).is_ok());
        assert!(theory.assert(1, true).is_ok());

        let props = theory.propagate();
        let prop = props
            .iter()
            .find(|prop| {
                prop.lit
                    == (TheoryLit {
                        atom: 2,
                        value: true,
                    })
            })
            .expect("x=3 should propagate true");
        assert!(
            prop.reason.iter().all(|lit| matches!(
                *lit,
                TheoryLit {
                    atom: 0 | 1,
                    value: true
                }
            )),
            "equality propagation reason must use only asserted bounds"
        );
    }

    #[test]
    fn equality_atom_false_propagates_from_incompatible_bound() {
        // x < 3 excludes x = 3. The equality-true branch is LP-infeasible, so
        // the online theory solver may propagate equality false.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let three = iconst(&mut arena, 3);
        let lt = arena.int_lt(x, three).expect("x<3");
        let eq = arena.eq(x, three).expect("x=3");

        let mut theory = LiaTheory::new(&arena, &[lt, eq]);
        assert!(theory.assert(0, true).is_ok());

        let props = theory.propagate();
        let prop = props
            .iter()
            .find(|prop| {
                prop.lit
                    == (TheoryLit {
                        atom: 1,
                        value: false,
                    })
            })
            .expect("x=3 should propagate false");
        assert_eq!(
            prop.reason,
            vec![TheoryLit {
                atom: 0,
                value: true,
            }],
            "equality-false reason must be the asserted incompatible bound"
        );
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
    fn online_decider_sat_model_replays_with_boolean_leaf() {
        // `p ∧ (x < y ∨ y < x)` needs the final Boolean skeleton assignment for
        // `p`; the arithmetic theory model alone is not enough to replay.
        let mut arena = TermArena::new();
        let p = arena.declare("p", Sort::Bool).expect("declare p");
        let pv = arena.var(p);
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let xy = arena.int_lt(x, y).expect("x<y");
        let yx = arena.int_lt(y, x).expect("y<x");
        let or = arena.or(xy, yx).expect("or");

        let verdict =
            check_qf_lia_online(&arena, &[pv, or], &SolverConfig::default()).expect("decidable");
        match verdict {
            CheckResult::Sat(model) => {
                assert_eq!(model.get(p), Some(Value::Bool(true)));
                assert!(replays_integer(&arena, &[pv, or], &model));
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

        // 4500 trials, not the original 1500, and the driver above carries a
        // per-trial deadline. Both changes are the *same* finding.
        //
        // The warm rational filter propagates far more than the LP-plus-deletion
        // probe it replaced, so the driver reaches the same verdicts through fewer
        // conflicts: measured on this corpus at 1500 trials, `fires` went 88 → 29
        // and `clauses_checked` 84 → 25 with every entailment check still passing.
        // That is a better search, but it under-exercises a gate whose thresholds
        // measure how hard 1-UIP is being driven, so the trial count buys the
        // exercise back rather than the thresholds being lowered to meet a quieter
        // search: 4500 trials give `fires=86`, `clauses_checked=73`.
        //
        // Raising the count needed the deadline first. Trial 2353 hangs this suite
        // for minutes on an untimed theory — pre-existing, and confirmed unrelated
        // to the filter (it hangs identically with the engine forced off), which is
        // why 1500 was as far as this gate could ever be pushed.
        for _ in 0..4500 {
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

    // --- The warm rational filter: soundness. --------------------------------
    //
    // Integer feasibility is NOT rational feasibility, so the filter carries two
    // separate obligations, and these tests pin both against the trusted offline
    // decider:
    //   * it must never call a system with an integer solution `refuted`, and the
    //     core it names must itself be integer-`unsat`; and
    //   * it must never call a system with no integer solution `integral`.

    /// The filter must actually be built for ordinary integer atom sets. Without
    /// this the engine could silently stop being constructed and every measurement
    /// below would be meaningless while every other test still passed — the offline
    /// decider answers identically, just slower.
    #[test]
    fn ordinary_integer_atom_sets_build_the_warm_filter() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let zero = iconst(&mut arena, 0);
        let sum = arena.int_add(x, y).expect("x+y");
        let atoms = [
            arena.int_gt(x, zero).expect("x>0"),
            arena.int_le(sum, zero).expect("x+y<=0"),
            arena.eq(x, y).expect("x=y"),
        ];
        let theory = LiaTheory::new(&arena, &atoms);
        assert!(
            theory.uses_simplex(),
            "the warm rational filter must be the front of an ordinary LIA atom set"
        );
    }

    /// The strict-to-non-strict tightening is what makes the *rational* relaxation
    /// able to refute an integer-only contradiction: `0 < x ∧ x < 1` has a rational
    /// solution (x = 1/2) but no integer one, and the tightened rows `x ≥ 1 ∧ x ≤ 0`
    /// are rationally infeasible. The filter — not the offline decider — must be the
    /// one that refutes it.
    #[test]
    fn the_filter_refutes_the_integer_only_contradiction() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = iconst(&mut arena, 0);
        let one = iconst(&mut arena, 1);
        let atoms = [
            arena.int_gt(x, zero).expect("x>0"),
            arena.int_lt(x, one).expect("x<1"),
        ];
        let mut theory = LiaTheory::new(&arena, &atoms);
        theory.assigned[0] = Some(true);
        theory.assigned_log.push(0);
        theory.assigned[1] = Some(true);
        theory.assigned_log.push(1);
        assert_eq!(
            theory.filter_verdict(),
            "refuted",
            "the tightened rational relaxation must refute 0<x<1 over the integers"
        );
    }

    /// ...and the tightening must not over-tighten: `0 < x ∧ x < 2` has the integer
    /// solution `x = 1`, so the filter must NOT refute it. A branch or cut that
    /// prunes a region containing an integer point is exactly the failure this pins.
    #[test]
    fn the_filter_does_not_prune_a_region_holding_an_integer_point() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = iconst(&mut arena, 0);
        let two = iconst(&mut arena, 2);
        let atoms = [
            arena.int_gt(x, zero).expect("x>0"),
            arena.int_lt(x, two).expect("x<2"),
        ];
        let mut theory = LiaTheory::new(&arena, &atoms);
        assert!(theory.assert(0, true).is_ok(), "0<x is feasible");
        assert!(
            theory.assert(1, true).is_ok(),
            "0<x<2 holds x=1 and must not be refuted"
        );
        let model = theory.integer_model().expect("x=1 is an integer model");
        assert!(
            replays_integer(&arena, &atoms, &model),
            "the reconstructed model must replay: {model:?}"
        );
    }

    /// A rationally-feasible, integer-INFEASIBLE system the tightening cannot see
    /// (`3x + 3y = 5` has the rational point (5/3, 0) and no integer point). The
    /// filter must decline — never `integral` — and the offline decider must still
    /// deliver the refutation, so no `sat` can escape.
    #[test]
    fn rational_feasibility_is_not_integer_feasibility() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let three = iconst(&mut arena, 3);
        let five = iconst(&mut arena, 5);
        let tx = arena.int_mul(three, x).expect("3x");
        let ty = arena.int_mul(three, y).expect("3y");
        let sum = arena.int_add(tx, ty).expect("3x+3y");
        let atom = arena.eq(sum, five).expect("3x+3y=5");

        let mut theory = LiaTheory::new(&arena, &[atom]);
        theory.assigned[0] = Some(true);
        theory.assigned_log.push(0);
        assert_ne!(
            theory.filter_verdict(),
            "integral",
            "a fractional-only relaxation must never be reported as an integer model"
        );

        // And end to end: the query is unsat, never sat.
        let verdict =
            check_qf_lia_online(&arena, &[atom], &SolverConfig::default()).expect("decidable");
        assert_eq!(
            verdict,
            CheckResult::Unsat,
            "3x+3y=5 has no integer solution"
        );
        assert_eq!(
            check_with_lia_simplex(&arena, &[atom]).expect("offline decidable"),
            CheckResult::Unsat,
            "offline route agrees",
        );
    }

    /// The same shape one step up: `2x = 2y + 1` (a parity contradiction). Its
    /// relaxation is feasible for every rational, so only the integer decider can
    /// refute it — the filter must not report `sat` and the route must not either.
    #[test]
    fn parity_contradiction_never_comes_back_sat() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let two = iconst(&mut arena, 2);
        let one = iconst(&mut arena, 1);
        let tx = arena.int_mul(two, x).expect("2x");
        let ty = arena.int_mul(two, y).expect("2y");
        let rhs = arena.int_add(ty, one).expect("2y+1");
        let atom = arena.eq(tx, rhs).expect("2x=2y+1");

        let verdict =
            check_qf_lia_online(&arena, &[atom], &SolverConfig::default()).expect("decidable");
        assert!(
            !matches!(verdict, CheckResult::Sat(_)),
            "a parity contradiction must never be sat: {verdict:?}"
        );
    }

    /// Randomized differential against the trusted offline decider, over the two
    /// conclusive filter answers. For each random conjunction of integer order and
    /// equality atoms:
    ///   * `refuted` ⇒ `check_with_lia_simplex` must agree the live set is `unsat`,
    ///     AND the named core must itself be `unsat` (a core that is not is a wrong
    ///     lemma even when the verdict happens to be right);
    ///   * `integral` ⇒ `check_with_lia_simplex` must NOT say `unsat` — a claimed
    ///     integer model over a system that has none is the wrong-`sat` axis.
    #[test]
    fn filter_verdicts_agree_with_the_offline_integer_decider() {
        let mut seed: u64 = 0x5eed_1a17_2026_0803;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut refuted = 0usize;
        let mut integral = 0usize;

        for _ in 0..400 {
            let mut arena = TermArena::new();
            let vars: Vec<TermId> = (0..3).map(|i| ivar(&mut arena, &format!("v{i}"))).collect();
            let atom_count = 2 + (next() % 4) as usize;
            let mut atoms = Vec::new();
            for _ in 0..atom_count {
                let a = vars[(next() % 3) as usize];
                let b = vars[(next() % 3) as usize];
                // A small linear combination so the atoms are not all differences.
                let scale = 1 + i128::from(next() % 3);
                let k = i128::from(next() % 11) - 5;
                let sk = iconst(&mut arena, scale);
                let kk = iconst(&mut arena, k);
                let Ok(sa) = arena.int_mul(sk, a) else {
                    continue;
                };
                let Ok(lhs) = arena.int_add(sa, kk) else {
                    continue;
                };
                let built = match next() % 5 {
                    0 => arena.int_lt(lhs, b),
                    1 => arena.int_le(lhs, b),
                    2 => arena.int_gt(lhs, b),
                    3 => arena.int_ge(lhs, b),
                    _ => arena.eq(lhs, b),
                };
                if let Ok(atom) = built {
                    atoms.push(atom);
                }
            }
            if atoms.is_empty() {
                continue;
            }

            let mut theory = LiaTheory::new(&arena, &atoms);
            // Assert every atom at a random polarity WITHOUT going through
            // `assert` (which would stop at the first conflict) so the filter is
            // exercised on the whole set.
            for atom in 0..atoms.len() {
                let value = next() % 2 == 0;
                theory.assigned[atom] = Some(value);
                theory.assigned_log.push(atom);
            }
            let lits = theory.live_literals();
            if lits.is_empty() {
                continue;
            }
            let Some((live_arena, live_terms)) = theory.terms_for(&lits) else {
                continue;
            };
            let offline = check_with_lia_simplex(&live_arena, &live_terms);

            match theory.filter_verdict() {
                "refuted" => {
                    refuted += 1;
                    assert_eq!(
                        offline.as_ref().ok(),
                        Some(&CheckResult::Unsat),
                        "the filter refuted a live set the integer decider did not: {live_terms:?}"
                    );
                    // The named core must itself be integer-unsat.
                    let core = theory.filter_core().expect("refuted ⇒ a core");
                    let (core_arena, core_terms) =
                        theory.terms_for(&core).expect("core terms build");
                    assert_eq!(
                        check_with_lia_simplex(&core_arena, &core_terms).ok(),
                        Some(CheckResult::Unsat),
                        "the Farkas core must itself be integer-unsat: {core:?}"
                    );
                }
                "integral" => {
                    integral += 1;
                    assert_ne!(
                        offline.as_ref().ok(),
                        Some(&CheckResult::Unsat),
                        "the filter claimed an integer model for an unsat system: {live_terms:?}"
                    );
                }
                _ => {}
            }
        }
        // The fuzz has to actually reach both conclusive paths, or it proves
        // nothing (the inert-gate failure mode).
        assert!(
            refuted >= 10,
            "the fuzz never exercised the refutation path ({refuted} hits)"
        );
        assert!(
            integral >= 10,
            "the fuzz never exercised the integral-point path ({integral} hits)"
        );
    }

    /// Warm-vs-cold agreement over random assert/pop sequences: the filter's verdict
    /// on a live set must not depend on the order the engine happened to reach it
    /// in. A stale bound left behind by a pop is a wrong-`unsat`, which is exactly
    /// the class `push_assert_pop_restores_feasibility` caught on the LRA side.
    #[test]
    fn warm_filter_matches_a_cold_theory_on_the_same_live_set() {
        let mut seed: u64 = 0xc01d_57a7_2026_0803;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..200 {
            let mut arena = TermArena::new();
            let vars: Vec<TermId> = (0..3).map(|i| ivar(&mut arena, &format!("w{i}"))).collect();
            let mut atoms = Vec::new();
            for _ in 0..5 {
                let a = vars[(next() % 3) as usize];
                let b = vars[(next() % 3) as usize];
                let k = iconst(&mut arena, i128::from(next() % 9) - 4);
                let Ok(lhs) = arena.int_add(a, k) else {
                    continue;
                };
                let built = match next() % 4 {
                    0 => arena.int_lt(lhs, b),
                    1 => arena.int_le(lhs, b),
                    2 => arena.int_gt(lhs, b),
                    _ => arena.int_ge(lhs, b),
                };
                if let Ok(atom) = built {
                    atoms.push(atom);
                }
            }
            if atoms.is_empty() {
                continue;
            }

            // Drive a warm theory through pushes, asserts and pops.
            let mut warm = LiaTheory::new(&arena, &atoms);
            let mut assignment: Vec<(usize, bool)> = Vec::new();
            for _ in 0..8 {
                if next() % 3 == 0 && !assignment.is_empty() {
                    warm.pop();
                    assignment.truncate(assignment.len().saturating_sub(1));
                    continue;
                }
                let atom = usize::try_from(next() % 64).expect("small") % atoms.len();
                if warm.assigned[atom].is_some() {
                    continue;
                }
                let value = next() % 2 == 0;
                warm.push();
                warm.assigned[atom] = Some(value);
                warm.assigned_log.push(atom);
                assignment.push((atom, value));
            }

            // A cold theory reaching the SAME live set in one go.
            let mut cold = LiaTheory::new(&arena, &atoms);
            for &(atom, value) in &assignment {
                cold.assigned[atom] = Some(value);
                cold.assigned_log.push(atom);
            }
            assert_eq!(
                warm.filter_verdict(),
                cold.filter_verdict(),
                "warm and cold engines disagree on {assignment:?}"
            );
        }
    }

    /// A propagation the filter emits must be a genuine entailment: asserting its
    /// reason together with the NEGATION of the propagated literal must be
    /// integer-`unsat` by the trusted offline decider.
    #[test]
    fn filter_propagations_are_entailed_over_the_integers() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let one = iconst(&mut arena, 1);
        let zero = iconst(&mut arena, 0);
        let ge_one = arena.int_ge(x, one).expect("x>=1");
        let gt_zero = arena.int_gt(x, zero).expect("x>0");
        let atoms = [ge_one, gt_zero];

        let mut theory = LiaTheory::new(&arena, &atoms);
        theory.assert(0, true).expect("x>=1 feasible");
        let props = theory.propagate();
        assert!(!props.is_empty(), "x>=1 must entail x>0");
        for prop in &props {
            // reason ∧ ¬propagated must be unsat.
            let mut lits = prop.reason.clone();
            lits.push(TheoryLit {
                atom: prop.lit.atom,
                value: !prop.lit.value,
            });
            let (probe_arena, probe_terms) = theory.terms_for(&lits).expect("probe terms");
            assert_eq!(
                check_with_lia_simplex(&probe_arena, &probe_terms).ok(),
                Some(CheckResult::Unsat),
                "propagation {prop:?} is not entailed by its reason"
            );
        }
    }
}
