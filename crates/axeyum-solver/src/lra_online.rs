//! Online (incremental, backtrackable) linear real arithmetic (`QF_LRA`) theory
//! solver — the first slice of the online theory-combination keystone (Track 1,
//! P1.6).
//!
//! The offline [`crate::lra`] path decides a *conjunction* by a single
//! Fourier–Motzkin elimination, and [`crate::dpll_t::check_with_lra_dpll`] drives
//! it with a cold Boolean abstraction (re-running the whole decision on every
//! refinement round). This module adds the **warm** counterpart: an
//! [`LraTheory`] keeping a backtrackable stack of asserted linear-real atoms that
//! a `DPLL(T)` loop drives via the same [`TheorySolver`] trait the online
//! [`crate::euf_egraph::EufTheory`] implements — `assert` / `push` / `pop` in
//! lockstep with the search's decision levels.
//!
//! [`LraTheory`] implements [`TheorySolver`]:
//! - [`LraTheory::assert`] asserts an order/equality atom (true or false) by
//!   pushing its normalized `expr {<,<=} 0` constraint(s) onto the trail and
//!   re-deciding feasibility by Fourier–Motzkin. On infeasibility it returns the
//!   **explained conflict**: the subset of asserted atoms whose constraints carry
//!   a nonzero Farkas multiplier in the derived contradiction — a genuine,
//!   typically small core (mirroring [`crate::euf_egraph::EufTheory`]'s explained
//!   conflict).
//! - [`LraTheory::push`] / [`LraTheory::pop`] snapshot and restore the trail
//!   length, so a backtrack drops exactly the constraints and atom assignments
//!   added since the matching `push`.
//! - `propagate` is an honest empty under-approximation in this first slice (a
//!   sound choice: the driver still terminates, just with less theory-level
//!   pruning). It is documented as deferred.
//!
//! [`check_qf_lra_online`] wires [`LraTheory`] into a self-contained `DPLL(T)`
//! search over the Boolean skeleton (the same shape as
//! [`crate::euf_egraph::solve_qf_uf_online`], since that driver is hardwired to
//! [`crate::euf_egraph::EufTheory`] and not reusable as-is). It is the warm
//! analogue of [`crate::dpll_t::check_with_lra_dpll`].
//!
//! **Trust.** This is a decision procedure: its soundness is established by the
//! differential gate against the trusted offline [`crate::lra::check_with_lra`]
//! (see `tests/lra_online.rs`) plus model replay, not by a post-hoc re-check.
//! Every `sat` model the driver returns is replayed through the ground evaluator
//! against the *original* assertions before it is handed back, so neither the
//! Boolean search nor the incremental theory can yield an unsound `sat`. Every
//! `unsat` is only ever reported at a root-level conflict whose core is a Farkas
//! combination of asserted atoms. All exact arithmetic is `i128`-`checked_*`;
//! any overflow degrades the *current feasibility check* to "don't know"
//! (treated as feasible — never a wrong `unsat`), and the driver carries that to
//! a conservative [`CheckResult::Unknown`] verdict.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use axeyum_ir::{
    Assignment, Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval,
};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::euf_egraph::{TheoryLit, TheoryProp, TheorySolver};
use crate::model::Model;

/// Hard ceiling on constraints produced by a single Fourier–Motzkin elimination
/// step inside an incremental feasibility check. Mirrors the offline
/// `MAX_FM_CONSTRAINTS`: above it the step declines (feasibility check returns
/// "don't know", treated as feasible — never a wrong `unsat`).
const MAX_FM_CONSTRAINTS: usize = 20_000;

/// A linear expression `Σ coeff_i · x_i + constant` over densely-indexed real
/// variables. A local mirror of the offline `lra::LinExpr` (kept private there);
/// all arithmetic is `i128`-`checked_*`, returning `None` on overflow so the
/// caller degrades to a graceful "don't know".
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct LinExpr {
    coeffs: BTreeMap<usize, Rational>,
    constant: Rational,
}

impl LinExpr {
    fn constant(value: Rational) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: value,
        }
    }

    fn var(index: usize) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(index, Rational::integer(1));
        Self {
            coeffs,
            constant: Rational::zero(),
        }
    }

    fn coeff(&self, index: usize) -> Rational {
        self.coeffs
            .get(&index)
            .copied()
            .unwrap_or_else(Rational::zero)
    }

    fn is_constant(&self) -> bool {
        self.coeffs.values().all(|c| c.is_zero())
    }

    fn neg(&self) -> Option<Self> {
        self.scale(Rational::integer(-1))
    }

    fn scale(&self, factor: Rational) -> Option<Self> {
        if factor.is_zero() {
            return Some(Self::constant(Rational::zero()));
        }
        let mut coeffs = BTreeMap::new();
        for (&i, &c) in &self.coeffs {
            coeffs.insert(i, c.checked_mul(factor)?);
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_mul(factor)?,
        })
    }

    fn add(&self, other: &Self) -> Option<Self> {
        let mut coeffs = self.coeffs.clone();
        for (&i, &c) in &other.coeffs {
            let entry = coeffs.entry(i).or_insert_with(Rational::zero);
            *entry = (*entry).checked_add(c)?;
        }
        coeffs.retain(|_, c| !c.is_zero());
        Some(Self {
            coeffs,
            constant: self.constant.checked_add(other.constant)?,
        })
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.neg()?)
    }
}

/// A normalized constraint `expr <= 0` (or `expr < 0` when `strict`), tagged with
/// the nonnegative combination (`mult`) of the *currently asserted* atom
/// constraints it was derived from. Original constraints carry a unit `mult`;
/// Fourier–Motzkin accumulates `mult` so an infeasible residual constraint names
/// the atom constraints behind it. `atom` is the index, into the theory's
/// registered atoms, that produced this constraint (an equality atom produces two
/// constraints sharing one `atom`).
#[derive(Debug, Clone)]
struct Constraint {
    expr: LinExpr,
    strict: bool,
    /// Nonnegative multiplier per *currently asserted constraint slot* (the row
    /// index in the live constraint list at the time the feasibility check ran).
    mult: Vec<Rational>,
    /// The registered atom index this constraint came from.
    atom: usize,
}

/// Outcome of an incremental feasibility check over the asserted constraints.
enum Feasibility {
    /// The asserted constraints are jointly feasible.
    Sat,
    /// Infeasible; the row indices (into the live constraint list) whose Farkas
    /// multiplier is nonzero — the constraints participating in the refutation.
    Unsat(Vec<usize>),
    /// Overflow or the size guard tripped: the check is inconclusive. Treated as
    /// feasible by the caller (never a wrong `unsat`).
    Unknown,
}

/// A parsed real atom: its normalized constraints for each polarity. An order
/// atom (`<`, `<=`, `>`, `>=`) has exactly one constraint per polarity. An
/// equality atom asserted *true* is two `<=` constraints; asserted *false* it is
/// a disjunction (`a < b ∨ a > b`) which a single conjunctive theory cannot
/// represent — see [`LraTheory::assert`].
#[derive(Debug, Clone)]
enum AtomKind {
    /// An order atom: `when_true` when asserted true, `when_false` when asserted
    /// false (each a single normalized constraint).
    Order {
        when_true: Constraint,
        when_false: Constraint,
    },
    /// An equality atom: two `<=` constraints when asserted true; asserting it
    /// false is a disjunction the theory declines (a sound no-op).
    Equality { when_true: [Constraint; 2] },
    /// A non-LRA atom (BV / disequality / nonlinear / non-real): asserting it is a
    /// no-op, keeping atom indices aligned with the caller's numbering.
    Unsupported,
}

/// Online (incremental, backtrackable) `QF_LRA` theory solver over a stack of
/// asserted linear-real atoms. Implements [`TheorySolver`] so a `DPLL(T)` loop
/// drives it: the SAT search asserts atoms as its trail grows, backtracks in
/// lockstep via [`push`](TheorySolver::push) / [`pop`](TheorySolver::pop), and
/// learns the explained conflict on infeasibility.
///
/// Feasibility is re-decided by an exact-rational Fourier–Motzkin elimination
/// over the currently-asserted constraints; on infeasibility the Farkas
/// multipliers name the participating atoms (the conflict core).
pub struct LraTheory {
    /// Per registered atom: how asserting it true/false translates to
    /// constraints, in the dense variable indexing.
    atoms: Vec<AtomKind>,
    /// Number of distinct real variables seen across all registered atoms.
    nvars: usize,
    /// The constraints currently asserted, each tagged with its source atom — the
    /// live constraint list Fourier–Motzkin runs over.
    live: Vec<Constraint>,
    /// Per atom index: the value it is currently asserted at (`None` if
    /// unassigned), so a re-assert of the same value is idempotent.
    assigned: Vec<Option<bool>>,
    /// Atom indices assigned since the start, in order — the backtrack log for
    /// `assigned`.
    assigned_log: Vec<usize>,
    /// Backtrack trail: per [`push`](TheorySolver::push), the
    /// `(live, assigned_log)` lengths to restore on the matching
    /// [`pop`](TheorySolver::pop).
    trail: Vec<(usize, usize)>,
    /// The real symbols in dense-variable-index order — `builder_vars[i]` is the
    /// symbol of variable `i`. Lets [`LraTheory::real_model`] read a witness back
    /// over the original symbols (used by the online theory-combination path).
    vars: Vec<SymbolId>,
}

impl LraTheory {
    /// Builds an online `LRA` theory over the given atom terms. Each `(< a b)` /
    /// `(<= a b)` / `(> a b)` / `(>= a b)` and each real `(= a b)` registers its
    /// normalized constraints; any other atom registers as a no-op so indices
    /// stay aligned with the caller's atom numbering.
    ///
    /// Variable indices are assigned in first-seen order over the atom terms,
    /// deterministically (a stable scan), so the dense indexing is reproducible.
    #[must_use]
    pub fn new(arena: &TermArena, atom_terms: &[TermId]) -> Self {
        let mut builder = AtomBuilder::default();
        let atoms: Vec<AtomKind> = atom_terms
            .iter()
            .map(|&t| builder.build(arena, t))
            .collect();
        let nvars = builder.vars.len();
        let count = atoms.len();
        Self {
            atoms,
            nvars,
            live: Vec::new(),
            assigned: vec![None; count],
            assigned_log: Vec::new(),
            trail: Vec::new(),
            vars: builder.vars,
        }
    }

    /// A real witness for the currently-asserted constraints, over the original
    /// symbols, or `None` if the live system is infeasible / arithmetic overflowed.
    /// The crate-internal reader the online theory-combination path
    /// ([`crate::uflra_online`]) uses to build the `LRA` half of a combined model at
    /// a consistent leaf — the same reconstruction [`LraTheory::model`] performs, but
    /// keyed by the symbols the theory was built over (so the caller needs no separate
    /// variable list). Soundness rests on the caller replaying the assembled model
    /// against the original assertions.
    #[must_use]
    pub(crate) fn real_model(&self) -> Option<Model> {
        self.model(&self.vars)
    }

    /// Whether atom `index` is an LRA order/equality atom this theory tracks.
    /// (`false` for a registered no-op, e.g. a BV or disequality atom.)
    #[must_use]
    pub fn tracks(&self, index: usize) -> bool {
        self.atoms
            .get(index)
            .is_some_and(|a| !matches!(a, AtomKind::Unsupported))
    }

    /// Re-decides feasibility of the live constraints by Fourier–Motzkin.
    fn feasibility(&self) -> Feasibility {
        if self.live.is_empty() {
            return Feasibility::Sat;
        }
        solve(&self.live, self.nvars)
    }

    /// Maps a set of live row indices (a Farkas-participating constraint subset)
    /// back to the distinct asserted atom literals behind them: the conflict core.
    fn rows_to_core(&self, rows: &[usize]) -> Vec<TheoryLit> {
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut core = Vec::new();
        for &row in rows {
            let Some(c) = self.live.get(row) else {
                continue;
            };
            if seen.insert(c.atom) {
                let value = self.assigned[c.atom].unwrap_or(true);
                core.push(TheoryLit {
                    atom: c.atom,
                    value,
                });
            }
        }
        // If, for any reason, the multipliers named no rows (should not happen for
        // a genuine refutation), fall back to the full set of currently-asserted
        // atoms — a sound, if coarse, conflict.
        if core.is_empty() {
            for &atom in &self.assigned_log {
                if let Some(value) = self.assigned[atom] {
                    core.push(TheoryLit { atom, value });
                }
            }
        }
        core
    }

    /// Maps Farkas-participating row indices (into a *probe* constraint list that
    /// equals the live system plus appended negation constraint(s)) back to the
    /// **asserted-only** literals behind the refutation — explicitly excluding the
    /// probed atom, whose negation was added speculatively and is *not* asserted.
    ///
    /// This is the soundness anchor of [`LraTheory::propagate`]: the explanation a
    /// propagated literal carries must be exactly the currently-asserted literals
    /// (mirroring [`crate::euf_egraph::EufTheory`]'s `explain_*`), so the learned
    /// lemma `¬(reason ∧ ¬entailed)` is entailed by the asserted state alone.
    /// Returns `None` if the refutation rests on no asserted atom (then the probe
    /// is not a sound propagation under the *asserted* state — skip it).
    fn probe_core(
        &self,
        probe: &[Constraint],
        rows: &[usize],
        probe_atom: usize,
    ) -> Option<Vec<TheoryLit>> {
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut core = Vec::new();
        for &row in rows {
            let Some(c) = probe.get(row) else { continue };
            if c.atom == probe_atom {
                // The speculative negation row — never part of the asserted reason.
                continue;
            }
            // Only genuinely-asserted atoms may appear in the reason.
            let Some(value) = self.assigned.get(c.atom).copied().flatten() else {
                continue;
            };
            if seen.insert(c.atom) {
                core.push(TheoryLit {
                    atom: c.atom,
                    value,
                });
            }
        }
        if core.is_empty() {
            return None;
        }
        Some(core)
    }

    /// Builds a candidate model from a feasible live system: each real variable
    /// gets a satisfying rational, returned as a [`Model`] over the original
    /// symbols. Returns `None` if the system is (now) infeasible or arithmetic
    /// overflows — the caller then yields `Unknown`, never a wrong `sat`.
    #[must_use]
    fn model(&self, builder_vars: &[SymbolId]) -> Option<Model> {
        let values = solve_values(&self.live, self.nvars)?;
        let mut model = Model::new();
        for (index, &symbol) in builder_vars.iter().enumerate() {
            model.set(symbol, Value::Real(values[index]));
        }
        Some(model)
    }

    /// Sound `LRA` theory propagation by the **negation probe**: for each
    /// unassigned tracked order atom, snapshot the live Fourier–Motzkin system,
    /// add the constraint for the atom's *opposite* polarity, and re-decide. If
    /// that augmented system is infeasible, the atom is **entailed** at the tested
    /// polarity under the currently-asserted constraints — emit it as a
    /// [`TheoryProp`] whose `reason` is the **asserted-only** Farkas core (the
    /// probed negation excluded). A `DPLL(T)` loop can then assign the entailed
    /// literal without a decision.
    ///
    /// Only genuinely-entailed literals are emitted: an inconclusive probe
    /// (overflow / size guard, or no asserted atom in the core) yields nothing — a
    /// sound under-approximation that **never** fabricates a propagation. Equality
    /// atoms are skipped (their negation is a disjunction the conjunctive probe
    /// cannot represent — the same restriction [`TheorySolver::assert`] makes).
    #[must_use]
    pub fn propagate(&self) -> Vec<TheoryProp> {
        let mut out = Vec::new();
        for atom in 0..self.atoms.len() {
            if self.assigned.get(atom).copied().flatten().is_some() {
                continue; // already decided by the search
            }
            let AtomKind::Order {
                when_true,
                when_false,
            } = &self.atoms[atom]
            else {
                continue; // equality-false is a disjunction; unsupported is a no-op
            };
            // Probe ¬atom (the `when_false` constraint): infeasible ⇒ atom entailed true.
            if let Some(reason) = self.probe_entails(when_false, atom) {
                out.push(TheoryProp {
                    lit: TheoryLit { atom, value: true },
                    reason,
                });
                continue;
            }
            // Probe atom (the `when_true` constraint): infeasible ⇒ ¬atom entailed.
            if let Some(reason) = self.probe_entails(when_true, atom) {
                out.push(TheoryProp {
                    lit: TheoryLit { atom, value: false },
                    reason,
                });
            }
        }
        out
    }

    /// Tests whether adding `probe_constraint` (the opposite polarity of atom
    /// `atom`) to the live system is infeasible. On infeasibility returns the
    /// asserted-only Farkas core (the entailment's explanation); otherwise `None`
    /// (feasible, inconclusive, or no asserted support — never a fabrication).
    fn probe_entails(&self, probe_constraint: &Constraint, atom: usize) -> Option<Vec<TheoryLit>> {
        let mut probe = self.live.clone();
        probe.push(tag(probe_constraint, atom));
        match solve(&probe, self.nvars) {
            Feasibility::Unsat(rows) => self.probe_core(&probe, &rows, atom),
            Feasibility::Sat | Feasibility::Unknown => None,
        }
    }
}

impl TheorySolver for LraTheory {
    /// Asserts atom `index` at `value`, pushing its constraint(s) and re-deciding
    /// feasibility. Returns the explained conflict (a Farkas-minimal subset of
    /// asserted atoms) on infeasibility.
    ///
    /// An equality atom asserted **false** is a disjunction the conjunctive
    /// theory cannot represent; rather than over- or under-constrain, the theory
    /// records the assignment but adds no constraint (a sound no-op — it never
    /// makes a feasible state infeasible, so it cannot cause a wrong `unsat`; the
    /// driver only ever sets equality atoms *true* anyway, since
    /// [`check_qf_lra_online`] does not abstract bare equalities).
    fn assert(&mut self, index: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        // Idempotent re-assert at the same value.
        if self.assigned.get(index).copied().flatten() == Some(value) {
            return Ok(());
        }
        self.assigned[index] = Some(value);
        self.assigned_log.push(index);

        let added: Vec<Constraint> = match (&self.atoms[index], value) {
            (AtomKind::Order { when_true, .. }, true) => vec![tag(when_true, index)],
            (AtomKind::Order { when_false, .. }, false) => vec![tag(when_false, index)],
            (AtomKind::Equality { when_true }, true) => {
                vec![tag(&when_true[0], index), tag(&when_true[1], index)]
            }
            // Equality-false (disjunction) and unsupported atoms add nothing.
            (AtomKind::Equality { .. }, false) | (AtomKind::Unsupported, _) => Vec::new(),
        };
        for c in added {
            self.live.push(c);
        }

        match self.feasibility() {
            Feasibility::Sat | Feasibility::Unknown => Ok(()),
            Feasibility::Unsat(rows) => Err(self.rows_to_core(&rows)),
        }
    }

    /// Saves a backtrack point: the current `(live, assigned_log)` lengths.
    fn push(&mut self) {
        self.trail.push((self.live.len(), self.assigned_log.len()));
    }

    /// Restores to the most recent [`push`](TheorySolver::push): drops every
    /// constraint and atom assignment added since.
    fn pop(&mut self) {
        let Some((live_len, log_len)) = self.trail.pop() else {
            return;
        };
        // Unassign atoms recorded since the marker.
        while self.assigned_log.len() > log_len {
            let atom = self.assigned_log.pop().expect("log non-empty above marker");
            self.assigned[atom] = None;
        }
        self.live.truncate(live_len);
    }

    fn propagate(&self) -> Vec<TheoryProp> {
        LraTheory::propagate(self)
    }
}

/// Attaches an empty `mult` (seeded by [`solve`] once the live row count is known)
/// and the source `atom` to a template constraint.
fn tag(template: &Constraint, atom: usize) -> Constraint {
    Constraint {
        expr: template.expr.clone(),
        strict: template.strict,
        mult: Vec::new(),
        atom,
    }
}

/// Builds the dense-indexed atom translations and tracks the variable order.
#[derive(Default)]
struct AtomBuilder {
    var_index: BTreeMap<SymbolId, usize>,
    vars: Vec<SymbolId>,
}

impl AtomBuilder {
    fn index_of(&mut self, symbol: SymbolId) -> usize {
        if let Some(&index) = self.var_index.get(&symbol) {
            return index;
        }
        let index = self.vars.len();
        self.vars.push(symbol);
        self.var_index.insert(symbol, index);
        index
    }

    /// Parses one atom term into its [`AtomKind`]. Any overflow or non-LRA shape
    /// yields [`AtomKind::Unsupported`] (a registered no-op), never a panic.
    fn build(&mut self, arena: &TermArena, term: TermId) -> AtomKind {
        match arena.node(term) {
            TermNode::App { op, args }
                if matches!(op, Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe) =>
            {
                let (Some(left), Some(right)) = (
                    self.linearize(arena, args[0]),
                    self.linearize(arena, args[1]),
                ) else {
                    return AtomKind::Unsupported;
                };
                match (
                    normalize(*op, &left, &right),
                    normalize(negate_op(*op), &left, &right),
                ) {
                    (Some(when_true), Some(when_false)) => AtomKind::Order {
                        when_true,
                        when_false,
                    },
                    _ => AtomKind::Unsupported,
                }
            }
            TermNode::App { op: Op::Eq, args } if is_real(arena, args[0]) => {
                let (Some(left), Some(right)) = (
                    self.linearize(arena, args[0]),
                    self.linearize(arena, args[1]),
                ) else {
                    return AtomKind::Unsupported;
                };
                // a == b  <=>  a - b <= 0  AND  b - a <= 0.
                let Some(diff) = left.sub(&right) else {
                    return AtomKind::Unsupported;
                };
                let Some(diff_neg) = diff.neg() else {
                    return AtomKind::Unsupported;
                };
                AtomKind::Equality {
                    when_true: [
                        Constraint {
                            expr: diff,
                            strict: false,
                            mult: Vec::new(),
                            atom: 0,
                        },
                        Constraint {
                            expr: diff_neg,
                            strict: false,
                            mult: Vec::new(),
                            atom: 0,
                        },
                    ],
                }
            }
            _ => AtomKind::Unsupported,
        }
    }

    /// Converts a real-sorted term into a [`LinExpr`]; `None` on overflow or a
    /// non-linear / non-real subterm (→ unsupported atom).
    fn linearize(&mut self, arena: &TermArena, term: TermId) -> Option<LinExpr> {
        match arena.node(term) {
            TermNode::RealConst(value) => Some(LinExpr::constant(*value)),
            TermNode::Symbol(symbol) if is_real(arena, term) => {
                Some(LinExpr::var(self.index_of(*symbol)))
            }
            TermNode::App {
                op: Op::RealNeg,
                args,
            } => self.linearize(arena, args[0])?.neg(),
            TermNode::App {
                op: Op::RealAdd,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                a.add(&b)
            }
            TermNode::App {
                op: Op::RealSub,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                a.sub(&b)
            }
            TermNode::App {
                op: Op::RealMul,
                args,
            } => {
                let a = self.linearize(arena, args[0])?;
                let b = self.linearize(arena, args[1])?;
                if a.is_constant() {
                    b.scale(a.constant)
                } else if b.is_constant() {
                    a.scale(b.constant)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

/// Normalizes `left <op> right` to a single `expr {<=,<} 0` [`Constraint`] (with
/// an empty `mult`, `atom = 0` to be filled by [`tag`]). `None` on overflow.
fn normalize(op: Op, left: &LinExpr, right: &LinExpr) -> Option<Constraint> {
    let (expr, strict) = match op {
        Op::RealLt => (left.sub(right)?, true),
        Op::RealLe => (left.sub(right)?, false),
        Op::RealGt => (right.sub(left)?, true),
        Op::RealGe => (right.sub(left)?, false),
        _ => return None,
    };
    Some(Constraint {
        expr,
        strict,
        mult: Vec::new(),
        atom: 0,
    })
}

/// The opposite order relation (`<` ↔ `>=`, `<=` ↔ `>`).
fn negate_op(op: Op) -> Op {
    match op {
        Op::RealLt => Op::RealGe,
        Op::RealLe => Op::RealGt,
        Op::RealGt => Op::RealLe,
        Op::RealGe => Op::RealLt,
        other => other,
    }
}

/// Whether `term` is real-sorted.
fn is_real(arena: &TermArena, term: TermId) -> bool {
    arena.sort_of(term) == Sort::Real
}

/// A unit multiplier vector of length `n` with `1` at position `i`.
fn unit_vec(n: usize, i: usize) -> Vec<Rational> {
    let mut v = vec![Rational::zero(); n];
    v[i] = Rational::integer(1);
    v
}

/// `factor · v`, elementwise; `None` on overflow.
fn scale_vec(v: &[Rational], factor: Rational) -> Option<Vec<Rational>> {
    v.iter().map(|&x| x.checked_mul(factor)).collect()
}

/// `a + b`, elementwise (equal lengths); `None` on overflow.
fn add_vec(a: &[Rational], b: &[Rational]) -> Option<Vec<Rational>> {
    a.iter().zip(b).map(|(&x, &y)| x.checked_add(y)).collect()
}

/// Decides feasibility of `constraints` over `nvars` variables by Fourier–Motzkin
/// elimination, returning (on infeasibility) the row indices whose Farkas
/// multiplier is nonzero. Multipliers are seeded as unit vectors over the input
/// rows and accumulated through elimination, so a residual infeasible constant
/// constraint names the rows behind it.
fn solve(constraints: &[Constraint], nvars: usize) -> Feasibility {
    let n = constraints.len();
    let mut current: Vec<Constraint> = constraints
        .iter()
        .enumerate()
        .map(|(i, c)| Constraint {
            expr: c.expr.clone(),
            strict: c.strict,
            mult: unit_vec(n, i),
            atom: c.atom,
        })
        .collect();

    for v in (0..nvars).rev() {
        match eliminate(&current, v) {
            Some(next) => current = next,
            None => return Feasibility::Unknown,
        }
    }
    for c in &current {
        if !constant_feasible(c) {
            let rows: Vec<usize> = c
                .mult
                .iter()
                .enumerate()
                .filter(|(_, m)| !m.is_zero())
                .map(|(i, _)| i)
                .collect();
            return Feasibility::Unsat(rows);
        }
    }
    Feasibility::Sat
}

/// Reconstructs a feasible assignment for `constraints` over `nvars` variables,
/// or `None` if the system is infeasible / arithmetic overflows. Used only to
/// build a `sat` model (which is then replayed against the originals).
fn solve_values(constraints: &[Constraint], nvars: usize) -> Option<Vec<Rational>> {
    let mut saved: Vec<(usize, Vec<Constraint>)> = Vec::with_capacity(nvars);
    let mut current: Vec<Constraint> = constraints.to_vec();
    for v in (0..nvars).rev() {
        saved.push((v, current.clone()));
        current = eliminate(&current, v)?;
    }
    for c in &current {
        if !constant_feasible(c) {
            return None;
        }
    }
    let mut model = vec![Rational::zero(); nvars];
    for (v, system) in saved.iter().rev() {
        model[*v] = pick_value(system, &model, *v)?;
    }
    Some(model)
}

/// One Fourier–Motzkin elimination of variable `v`, carrying multipliers. `None`
/// on overflow or when the cross product would exceed [`MAX_FM_CONSTRAINTS`].
fn eliminate(system: &[Constraint], v: usize) -> Option<Vec<Constraint>> {
    let mut out = Vec::new();
    let mut pos = Vec::new();
    let mut neg = Vec::new();
    let zero = Rational::zero();
    for c in system {
        let a = c.expr.coeff(v);
        if a.is_zero() {
            out.push(c.clone());
        } else {
            match a.checked_cmp(&zero)? {
                core::cmp::Ordering::Greater => pos.push(c),
                core::cmp::Ordering::Less => neg.push(c),
                core::cmp::Ordering::Equal => out.push(c.clone()),
            }
        }
    }
    if out
        .len()
        .saturating_add(pos.len().saturating_mul(neg.len()))
        > MAX_FM_CONSTRAINTS
    {
        return None;
    }
    // Combine each positive-coefficient bound with each negative-coefficient
    // bound to cancel `v`: `(-qc)·p + pc·q` where pc = p[v] > 0, qc = q[v] < 0,
    // both scale factors positive so the accumulated multipliers stay nonnegative.
    for p in &pos {
        let pc = p.expr.coeff(v); // > 0
        for q in &neg {
            let qc = q.expr.coeff(v); // < 0
            let neg_qc = qc.checked_neg()?; // > 0
            let scaled_p = p.expr.scale(neg_qc)?;
            let scaled_q = q.expr.scale(pc)?;
            let expr = scaled_p.add(&scaled_q)?;
            let mult_p = scale_vec(&p.mult, neg_qc)?;
            let mult_q = scale_vec(&q.mult, pc)?;
            let mult = add_vec(&mult_p, &mult_q)?;
            out.push(Constraint {
                expr,
                strict: p.strict || q.strict,
                mult,
                atom: p.atom,
            });
        }
    }
    Some(out)
}

/// Whether a constant-only constraint `constant {<,<=} 0` is feasible.
fn constant_feasible(c: &Constraint) -> bool {
    let value = c.expr.constant;
    if c.strict {
        value < Rational::zero()
    } else {
        value <= Rational::zero()
    }
}

/// Picks a feasible value for variable `v` given earlier-indexed variables are
/// assigned in `model`; `None` on overflow or no feasible value.
fn pick_value(system: &[Constraint], model: &[Rational], v: usize) -> Option<Rational> {
    use core::cmp::Ordering;
    let zero = Rational::zero();
    let mut lower: Option<(Rational, bool)> = None;
    let mut upper: Option<(Rational, bool)> = None;
    for c in system {
        let a = c.expr.coeff(v);
        let mut rest = c.expr.constant;
        for (&i, &coeff) in &c.expr.coeffs {
            if i != v {
                rest = rest.checked_add(coeff.checked_mul(model[i])?)?;
            }
        }
        if a.is_zero() {
            let ok = if c.strict { rest < zero } else { rest <= zero };
            if !ok {
                return None;
            }
            continue;
        }
        let bound = rest.checked_neg()?.checked_div(a)?;
        match a.cmp(&zero) {
            Ordering::Greater => update_bound(&mut upper, bound, c.strict, false)?,
            Ordering::Less => update_bound(&mut lower, bound, c.strict, true)?,
            Ordering::Equal => unreachable!("a is nonzero in this branch"),
        }
    }
    choose(lower, upper)
}

/// Tightens a bound: `is_lower` true picks the largest lower bound, false the
/// smallest upper bound. `None` propagates overflow.
fn update_bound(
    slot: &mut Option<(Rational, bool)>,
    value: Rational,
    strict: bool,
    is_lower: bool,
) -> Option<()> {
    match slot {
        None => *slot = Some((value, strict)),
        Some((cur, cur_strict)) => {
            let cmp = value.checked_cmp(cur)?;
            let replace = if is_lower {
                cmp == core::cmp::Ordering::Greater
                    || (cmp == core::cmp::Ordering::Equal && strict && !*cur_strict)
            } else {
                cmp == core::cmp::Ordering::Less
                    || (cmp == core::cmp::Ordering::Equal && strict && !*cur_strict)
            };
            if replace {
                *slot = Some((value, strict));
            }
        }
    }
    Some(())
}

/// Picks a value in the (possibly half-open) interval `(lower, upper)` after
/// bound tightening. Returns a representative rational, or `None` if empty (a
/// reconstruction bug, treated as "no value").
fn choose(lower: Option<(Rational, bool)>, upper: Option<(Rational, bool)>) -> Option<Rational> {
    match (lower, upper) {
        (None, None) => Some(Rational::zero()),
        (Some((lo, _)), None) => lo.checked_add(Rational::integer(1)),
        (None, Some((hi, _))) => hi.checked_sub(Rational::integer(1)),
        (Some((lo, lo_strict)), Some((hi, hi_strict))) => {
            let cmp = lo.checked_cmp(&hi)?;
            match cmp {
                core::cmp::Ordering::Less => {
                    // Midpoint lies strictly between.
                    let sum = lo.checked_add(hi)?;
                    sum.checked_div(Rational::integer(2))
                }
                core::cmp::Ordering::Equal => {
                    if lo_strict || hi_strict {
                        None // empty open interval at a point
                    } else {
                        Some(lo)
                    }
                }
                core::cmp::Ordering::Greater => None,
            }
        }
    }
}

// --- The online DPLL(T) driver (a mirror of euf_egraph::Dpll retargeted to
// --- LraTheory, since that one is hardwired to EufTheory). ------------------

/// Learned clauses tolerated before the first [`Dpll::reduce_db`]. Mirrors
/// `axeyum_cnf::proof_sat`'s additive schedule, scaled for the smaller working
/// instances of the online theory loop so reduction actually triggers.
const REDUCE_FIRST: usize = 2_000;
/// Additive growth of the learned-clause budget after each reduction: the budget
/// is `REDUCE_FIRST + REDUCE_INC * reductions`, so reductions become less frequent
/// over time (the standard Glucose/`MiniSat` schedule shape).
const REDUCE_INC: usize = 300;
/// Learned clauses whose literal-block distance (`LBD`) is at or below this are
/// "glue" clauses and are never deleted (the canonical Glucose protection rule).
const GLUE_LBD: usize = 2;

/// `VSIDS` activity decay: after each conflict the bump increment `var_inc` is
/// divided by this, so older activity bumps decay geometrically relative to
/// fresh ones (the `MiniSat` scheme; mirrors `axeyum_cnf::proof_sat`).
const VSIDS_DECAY: f64 = 0.95;
/// Rescale all activities (and `var_inc`) by this when any exceeds the cap, to
/// avoid `f64` overflow without changing their relative order.
const VSIDS_RESCALE: f64 = 1e-100;
/// Activity ceiling that triggers a rescale.
const VSIDS_RESCALE_LIMIT: f64 = 1e100;

/// Conflict-interval unit multiplied by the Luby value to set each restart's
/// length: the `restart_count`-th restart fires after `luby(restart_count) *
/// LUBY_UNIT` conflicts. Mirrors `axeyum_cnf::proof_sat`'s `LUBY_UNIT`.
const LUBY_UNIT: usize = 100;

/// The `i`-th term (1-indexed) of the Luby sequence `1,1,2,1,1,2,4,1,1,2,1,1,2,
/// 4,8,…`, used to space restarts (Knuth's reluctant-doubling formulation,
/// iterative). The schedule is a pure function of the restart index, so it is
/// deterministic: the same query crosses the same restart points and follows
/// the same trajectory. Mirrors `axeyum_cnf::proof_sat`'s `luby`.
fn luby(mut i: u64) -> u64 {
    let mut k = 1_u64;
    loop {
        let pow = 1_u64 << k; // 2^k
        if i == pow - 1 {
            return 1_u64 << (k - 1); // 2^(k-1)
        }
        let half = 1_u64 << (k - 1); // 2^(k-1)
        if half <= i && i < pow - 1 {
            i = i - half + 1;
            k = 1;
        } else {
            k += 1;
        }
    }
}

/// A CNF literal in the online `DPLL(T)` skeleton: a variable index and polarity.
///
/// `pub(crate)` so the `QF_UFLRA` Boolean layer ([`crate::uflra_online`]) can build the
/// extended skeleton (theory atoms ++ interface vars ++ Tseitin auxiliaries) it hands to
/// the generic [`Dpll`] driving a [`crate::combined_theory::CombinedIncremental`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Lit {
    pub(crate) var: usize,
    pub(crate) positive: bool,
}

impl Lit {
    pub(crate) fn negate(self) -> Self {
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

/// A self-contained `DPLL(T)` search over the CNF skeleton driving any online
/// [`TheorySolver`]: **1-UIP** theory-conflict learning with non-chronological
/// backjumping, the theory pushed on each decision and popped once per decision
/// crossed when backjumping. The loop is generic over the theory (its methods
/// take `&mut T` where `T: TheorySolver`); [`check_qf_lra_online`] instantiates
/// it with [`LraTheory`] and the `QF_UFLRA` Boolean layer
/// ([`crate::uflra_online`]) instantiates it with a
/// [`crate::combined_theory::CombinedIncremental`] (the shared-`CDCL(T)`-combination
/// keystone, slice 3c) — hence `pub(crate)`.
pub(crate) struct Dpll {
    var_count: usize,
    atom_count: usize,
    clauses: Vec<Vec<Lit>>,
    value: Vec<Option<bool>>,
    /// The assignment trail: `(var, value, cause)` in assignment order.
    trail: Vec<(usize, bool, Cause)>,
    /// Per variable: the decision level it was assigned at (valid only while the
    /// variable is assigned).
    level: Vec<usize>,
    /// Per variable: the reason clause that forced it (a clause that, once all
    /// its other literals are false, propagates this variable). `None` for a
    /// decision. Valid only while the variable is assigned.
    reason: Vec<Option<Vec<Lit>>>,
    /// Per variable: whether its reason clause is a *theory* clause (a theory
    /// conflict `¬⋀core` or a theory propagation `¬reason ∨ lit`, both entailed by
    /// the theory alone) rather than a Boolean input clause. A 1-UIP clause
    /// resolved only through theory clauses is itself a theory lemma — the test
    /// gate uses this to pick clauses it can independently re-validate with the
    /// trusted conjunctive offline decider.
    reason_theory: Vec<bool>,
    /// Per variable: the clause index in [`Self::clauses`] of the learned clause
    /// that is currently this variable's reason, or `None` if its reason is not a
    /// stored learned clause (a decision, a Boolean input clause, or a synthesized
    /// theory clause). Lets [`Self::reduce_db`] protect a *locked* learned clause
    /// (one currently a reason on the trail) in O(1). Valid only while the variable
    /// is assigned.
    reason_clause: Vec<Option<usize>>,
    /// The current decision level (incremented on every decision, restored on
    /// backjump).
    decision_level: usize,
    /// `VSIDS` activity per variable (higher ⇒ decided sooner). Bumped for every
    /// variable that participates in a conflict's 1-UIP resolution
    /// ([`Self::analyze_conflict`]); decided most-active-first by
    /// [`Self::pick_unassigned`]. Pure search heuristic — never affects sat/unsat.
    activity: Vec<f64>,
    /// Current `VSIDS` bump increment, grown by `1/VSIDS_DECAY` after each conflict
    /// so older bumps decay geometrically relative to fresh ones (the `MiniSat`
    /// trick; mirrors `axeyum_cnf::proof_sat`'s `var_inc`).
    var_inc: f64,
    /// Per variable: the last polarity it was assigned (phase saving). Updated in
    /// [`Self::assign`] on every assignment — both decisions and propagations — so a
    /// variable re-decided after a backjump or restart reuses the polarity it last
    /// settled on (the `MiniSat`/`BatSat` "progress saving" heuristic; mirrors
    /// `axeyum_cnf::proof_sat`'s `phase`). Initialized to `true` so the *first*
    /// decision of each variable matches the prior fixed `true`-first default,
    /// keeping the determinism baseline unchanged. Pure search heuristic: the
    /// polarity of a decision is a free branch choice, so this never affects
    /// sat/unsat, only the search trajectory. Read at the decision in
    /// [`Self::solve`].
    saved_phase: Vec<bool>,
    /// Number of original (input + Tseitin skeleton) clauses. Clause indices
    /// `< num_original` are permanent (never deletion-eligible); learned 1-UIP
    /// asserting clauses are appended at indices `>= num_original`.
    num_original: usize,
    /// Per clause (indexed like [`Self::clauses`]): the literal-block distance
    /// (`LBD`) — the number of distinct decision levels among the clause's literals
    /// at learning time. Meaningful for learned clauses only (`0` for originals).
    lbd: Vec<usize>,
    /// Per clause: a monotone learning-time activity stamp (the deletion
    /// tie-break, fresher = higher = more valuable). `0.0` for originals.
    cla_activity: Vec<f64>,
    /// Per clause: tombstone flag. A deleted learned clause keeps its slot (so the
    /// `clauses[num_original..]` stream stays aligned with the diagnostics and no
    /// index shifts) but is skipped everywhere in propagation. Originals are never
    /// tombstoned.
    deleted: Vec<bool>,
    /// Current clause-activity stamp, advanced on each learned clause so the stamp
    /// is a strictly increasing recency key (deterministic, no clock).
    cla_inc: f64,
    /// Number of [`Self::reduce_db`] reductions performed so far (drives the
    /// growing budget).
    reductions: usize,
    /// Number of live (non-deleted) learned clauses. Drives the reduce trigger.
    learned_live: usize,
    /// Conflicts seen since the last [`Luby`](luby) restart (reset to `0` on each
    /// restart). Bumped once per conflict in [`Self::learn_and_backjump`] and
    /// compared against [`Self::restart_limit`] in [`Self::solve`].
    conflicts_since_restart: usize,
    /// The Luby-sequence index (1-based; advances by one on each restart), so the
    /// next restart fires after `luby(restart_count) * LUBY_UNIT` conflicts.
    /// Restarting is verdict-invariant: it abandons only the current partial
    /// assignment, keeping every learned clause and every `VSIDS` activity.
    restart_count: u64,
    /// Test-only override of [`REDUCE_FIRST`] so a small fixture can cross the
    /// budget and exercise [`Self::reduce_db`] without millions of conflicts.
    /// `None` in production (the standard schedule).
    #[cfg(test)]
    reduce_first_override: Option<usize>,
    /// Test-only override of [`LUBY_UNIT`] so a small conflict-heavy fixture crosses
    /// the Luby restart trigger after a handful of conflicts (rather than hundreds).
    /// `None` in production (the standard `LUBY_UNIT` schedule).
    #[cfg(test)]
    restart_unit_override: Option<usize>,
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
    /// The number of conflicts whose 1-UIP clause lost at least one literal to
    /// self-subsuming minimization.
    minimize_fires: usize,
    /// Summed count of literals dropped by minimization across all conflicts.
    minimize_removed_total: u64,
    /// The number of clauses present before any learning (the encoded skeleton);
    /// every clause at or after this index is a learned 1-UIP asserting clause.
    initial_clauses: usize,
    /// Per stored learned clause (aligned with `clauses[initial_clauses..]`):
    /// whether it is a pure theory lemma (entailed by the theory plus the
    /// level-0 facts), so the test gate can re-validate it with the conjunctive
    /// offline decider.
    lemma_flags: Vec<bool>,
    /// Per stored learned clause: the level-0 atom assignments `(atom, value)` in
    /// force when it was learned — the unconditional facts the lemma rests on, so
    /// the entailment oracle conjoins them with `¬clause`.
    lemma_level0: Vec<Vec<(usize, bool)>>,
}

impl Dpll {
    pub(crate) fn new(var_count: usize, atom_count: usize, clauses: Vec<Vec<Lit>>) -> Self {
        #[cfg(test)]
        let diag = Diagnostics {
            initial_clauses: clauses.len(),
            ..Diagnostics::default()
        };
        let num_original = clauses.len();
        Self {
            var_count,
            atom_count,
            clauses,
            value: vec![None; var_count],
            trail: Vec::new(),
            level: vec![0; var_count],
            reason: vec![None; var_count],
            reason_theory: vec![false; var_count],
            reason_clause: vec![None; var_count],
            decision_level: 0,
            activity: vec![0.0; var_count],
            var_inc: 1.0,
            saved_phase: vec![true; var_count],
            num_original,
            lbd: vec![0; num_original],
            cla_activity: vec![0.0; num_original],
            deleted: vec![false; num_original],
            cla_inc: 1.0,
            reductions: 0,
            learned_live: 0,
            conflicts_since_restart: 0,
            restart_count: 1,
            #[cfg(test)]
            reduce_first_override: None,
            #[cfg(test)]
            restart_unit_override: None,
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

    /// Assigns `var := value` at the current decision level, recording its level
    /// and reason and mirroring a theory atom into [`LraTheory`]. `reason` is the
    /// forcing clause for a propagation, `None` for a decision.
    fn assign<T: TheorySolver>(
        &mut self,
        theory: &mut T,
        var: usize,
        value: bool,
        cause: Cause,
        reason: Option<Vec<Lit>>,
        reason_is_theory: bool,
    ) -> Result<(), Vec<TheoryLit>> {
        self.value[var] = Some(value);
        // Phase saving: remember this polarity so a later re-decision of `var`
        // (after a backjump or restart unassigns it) reuses it. Captured on every
        // assignment — decisions and propagations alike, matching the SAT core's
        // `enqueue`. Heuristic only; never affects the verdict.
        self.saved_phase[var] = value;
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
    fn unit_propagate<T: TheorySolver>(&mut self, theory: &mut T) -> Result<(), Conflict> {
        let mut changed = true;
        while changed {
            changed = false;
            for ci in 0..self.clauses.len() {
                // Skip tombstoned (reduce_db-deleted) learned clauses: they are
                // redundant resolvents, so omitting them only forgoes pruning.
                if self.deleted[ci] {
                    continue;
                }
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
    /// learned theory-conflict clause on a theory conflict, else `Ok(())`. A
    /// mirror of `crate::euf_egraph::Dpll::theory_propagate` retargeted to
    /// [`LraTheory`].
    fn theory_propagate<T: TheorySolver>(&mut self, theory: &mut T) -> Result<(), Conflict> {
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
    /// mirror of `crate::euf_egraph::Dpll::propagate` retargeted to [`LraTheory`].
    fn propagate<T: TheorySolver>(&mut self, theory: &mut T) -> Result<(), Conflict> {
        loop {
            self.unit_propagate(theory)?;
            let before = self.trail.len();
            self.theory_propagate(theory)?;
            if self.trail.len() == before {
                return Ok(());
            }
        }
    }

    /// Maps a theory conflict core to a learned CNF conflict clause `¬⋀core`
    /// (every literal currently false, so it is the falsified clause to analyze).
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

    /// 1-UIP conflict analysis: resolves the falsified `conflict` clause against
    /// the reason clauses of current-decision-level literals (newest-first on the
    /// trail) until a single current-level literal — the first UIP — remains.
    /// Returns the asserting clause (the UIP literal at index 0, the lower-level
    /// literals after it), the backjump level (the second-highest decision level
    /// among the clause's literals, `0` if it has none), and whether the clause is
    /// a pure **theory lemma** — derived by resolving only theory clauses (the
    /// seed conflict and every resolved reason were theory clauses), so it is
    /// entailed by the theory alone. A mirror of `axeyum_cnf::proof_sat`'s
    /// `analyze`, without the VSIDS/LBD/minimization machinery (kept deliberately
    /// minimal for the online theory loop).
    fn analyze_conflict(
        &mut self,
        conflict: &[Lit],
        seed_is_theory: bool,
    ) -> (Vec<Lit>, usize, bool) {
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
                // VSIDS: bump every variable on the conflict side as it is first
                // resolved through, exactly as `axeyum_cnf::proof_sat`'s `analyze`.
                // Heuristic only — does not affect which clauses are learned.
                self.bump_var(v);
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
                // Recursive (self-subsuming) minimization: drop non-asserting
                // literals whose negation is already implied — through their reason
                // chains — by the rest of the clause (`MiniSat` `ccmin_mode = 2`,
                // mirroring `axeyum_cnf::proof_sat`'s `minimize`/`lit_redundant`).
                // At this point `seen[w]` is true exactly for the non-asserting
                // (`lower`) variables and false for the asserting literal's variable
                // — the precondition [`Self::minimize`] relies on. The backjump
                // level is recomputed from the *minimized* clause below, so it stays
                // a valid asserting clause (single current-level literal at index 0).
                #[cfg(test)]
                let pre_min_len = learned.len();
                // Minimization resolves the clause against the reason chains of the
                // dropped literals. A clause is a pure *theory* lemma only if EVERY
                // reason it was resolved through — in 1-UIP *and* in minimization —
                // is a theory clause. `minimize` ANDs the theory-purity of the
                // reasons it traverses into `all_theory`, so a literal removed via a
                // Boolean reason correctly downgrades the lemma flag (the test gate's
                // conjunctive offline oracle is only valid for pure theory lemmas).
                self.minimize(&mut learned, &mut seen, &mut all_theory);
                #[cfg(test)]
                {
                    let removed =
                        u64::try_from(pre_min_len - learned.len()).expect("removed fits u64");
                    if removed > 0 {
                        self.diag.minimize_fires += 1;
                        self.diag.minimize_removed_total += removed;
                    }
                }
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

    /// An abstraction of a variable's decision level as a single-bit mask
    /// (`MiniSat`'s `abstractLevel`). The union of these masks over a clause's
    /// non-asserting literals lets [`Self::lit_redundant`] short-circuit: a reason
    /// literal whose level-bit is absent from the clause's mask comes from a
    /// decision level unrelated to the clause and so cannot be resolved away.
    #[inline]
    fn abstract_level(&self, var: usize) -> u32 {
        1_u32 << (self.level[var] & 31)
    }

    /// Recursive (self-subsuming) minimization of the 1-UIP asserting clause —
    /// `MiniSat` `ccmin_mode = 2`, mirroring `axeyum_cnf::proof_sat`'s `minimize`.
    ///
    /// A non-asserting literal `l` (index `>= 1`) is dropped when its negation is
    /// already entailed by the remaining clause literals through `l`'s reason
    /// chain: every literal in `reason(l)` (other than `l` itself) must be already
    /// in the clause (`seen`), fixed at level 0, or itself recursively redundant.
    /// Resolving the clause against those reason chains keeps it entailed, so the
    /// minimized clause is still implied — verdict-invariant. Decision literals (no
    /// reason) are never redundant, and the asserting literal (index 0, the only
    /// current-level literal) is always kept, so the result is still a valid
    /// asserting clause that forces the same UIP after the recomputed backjump.
    ///
    /// Precondition: `seen[w]` is true exactly for the non-asserting clause
    /// variables and false for the asserting literal's variable. `seen` is the
    /// per-conflict local owned by [`Self::analyze_conflict`] and discarded when
    /// that frame returns, so no state leaks across conflicts; the result depends
    /// only on this conflict's `seen` state, the reason graph, and the input clause
    /// order — hence deterministic (no hash-map iteration).
    ///
    /// `all_theory` is conjoined with the theory-purity of every reason clause the
    /// minimization walk traverses, so a clause flagged a pure theory lemma stays
    /// flagged only if no Boolean reason was resolved through — the test gate's
    /// conjunctive offline oracle is sound only for pure theory lemmas, and a
    /// minimized clause that resolved through a Boolean reason is no longer one.
    fn minimize(&self, learned: &mut Vec<Lit>, seen: &mut [bool], all_theory: &mut bool) {
        if learned.len() <= 1 {
            return;
        }
        // Mask of the decision levels present among the non-asserting literals.
        let mut abstract_levels = 0_u32;
        for lit in &learned[1..] {
            abstract_levels |= self.abstract_level(lit.var);
        }
        let mut stack: Vec<usize> = Vec::new();
        let mut to_clear: Vec<usize> = Vec::new();
        let mut write = 1_usize;
        for read in 1..learned.len() {
            let lit = learned[read];
            // Keep `lit` if it is a decision (no reason) or not redundant.
            if self.reason[lit.var].is_none()
                || !self.lit_redundant(
                    lit.var,
                    abstract_levels,
                    seen,
                    &mut stack,
                    &mut to_clear,
                    all_theory,
                )
            {
                learned[write] = lit;
                write += 1;
            }
        }
        learned.truncate(write);
    }

    /// Can the literal on variable `p` be removed from the learned clause?
    /// Iterative self-subsumption check (an explicit `stack` avoids stack overflow
    /// on deep reason chains), mirroring `axeyum_cnf::proof_sat`'s `lit_redundant`.
    ///
    /// `p` is redundant iff, walking its reason chain, every encountered literal
    /// (other than the propagated literal itself) is fixed at level 0, already in
    /// the clause (`seen`), or has a reason and a level present in
    /// `abstract_levels` (so it can in turn be resolved away). The first literal
    /// that has no reason, or whose level is outside `abstract_levels`, makes `p`
    /// irredundant — and every `seen` mark this call set (recorded in `to_clear`)
    /// is rolled back before returning `false`, so a failed probe leaves no state
    /// behind. On success the marks set during the walk are retained.
    fn lit_redundant(
        &self,
        p: usize,
        abstract_levels: u32,
        seen: &mut [bool],
        stack: &mut Vec<usize>,
        to_clear: &mut Vec<usize>,
        all_theory: &mut bool,
    ) -> bool {
        stack.clear();
        stack.push(p);
        let top = to_clear.len();
        while let Some(qv) = stack.pop() {
            // Conservatively downgrade the theory-lemma flag for every reason this
            // probe walks: resolving through a Boolean reason means the resolvent is
            // no longer a pure theory lemma. Downgrading on a walked-but-failed probe
            // is sound (it only makes the flag `false` more often).
            *all_theory = *all_theory && self.reason_theory[qv];
            let reason = self.reason[qv]
                .as_ref()
                .expect("lit_redundant only walks variables with a reason clause");
            for lit in reason {
                let lv = lit.var;
                // Skip the propagated literal itself (it is the clause member the
                // reason forces, the analogue of `proof_sat`'s reason slot 0).
                if lv == qv || self.level[lv] == 0 || seen[lv] {
                    continue;
                }
                if self.reason[lv].is_some() && (self.abstract_level(lv) & abstract_levels) != 0 {
                    // `l` may itself be redundant: mark it and recurse.
                    seen[lv] = true;
                    stack.push(lv);
                    to_clear.push(lv);
                } else {
                    // `l` has no reason or comes from an unrelated decision level:
                    // `p` cannot be removed. Roll back this probe's marks.
                    for &w in &to_clear[top..] {
                        seen[w] = false;
                    }
                    to_clear.truncate(top);
                    return false;
                }
            }
        }
        true
    }

    /// The backjump level of an asserting clause: the second-highest decision
    /// level among its literals (the asserting literal at index 0 sits at the
    /// highest level), or `0` for a unit asserting clause.
    fn backjump_level(level: &[usize], learned: &[Lit]) -> usize {
        learned
            .iter()
            .skip(1)
            .map(|lit| level[lit.var])
            .max()
            .unwrap_or(0)
    }

    /// Backjumps to `target_level`: pops every trail entry strictly above it,
    /// unassigning each variable and popping the theory **once per decision
    /// crossed** (the theory was pushed once per decision, so this keeps the
    /// push/pop stack in lockstep).
    fn backjump_to<T: TheorySolver>(&mut self, theory: &mut T, target_level: usize) {
        while let Some(&(var, _, _)) = self.trail.last() {
            if self.level[var] <= target_level {
                break;
            }
            let (var, _, cause) = self.trail.pop().expect("non-empty trail");
            self.value[var] = None;
            self.reason[var] = None;
            self.reason_theory[var] = false;
            self.reason_clause[var] = None;
            if cause == Cause::Decision {
                theory.pop();
            }
        }
        self.decision_level = target_level;
    }

    /// The unassigned variable of highest `VSIDS` activity, ties broken by lowest
    /// index, or `None` when every variable is assigned (a total model). A
    /// deterministic `O(n)` max-scan: the best is replaced only on a *strictly*
    /// greater activity, so among equal activities the lowest index wins — the same
    /// total order `axeyum_cnf::proof_sat`'s activity heap uses. No hash-map
    /// iteration, so the same query always picks the same variable.
    ///
    /// This is a pure search heuristic: it changes only the *order* decisions are
    /// taken, never which assignments are consistent, so it cannot change the
    /// sat/unsat verdict (the theory still gates every assignment; every learned
    /// clause is still an entailed resolvent).
    fn pick_unassigned(&self) -> Option<usize> {
        let mut best: Option<usize> = None;
        for v in 0..self.var_count {
            if self.value[v].is_some() {
                continue;
            }
            match best {
                None => best = Some(v),
                Some(b) if self.activity[v] > self.activity[b] => best = Some(v),
                Some(_) => {}
            }
        }
        best
    }

    /// Bumps `var`'s `VSIDS` activity by the current increment, rescaling **all**
    /// activities (and `var_inc`) by [`VSIDS_RESCALE`] when any exceeds
    /// [`VSIDS_RESCALE_LIMIT`], to avoid `f64` overflow. Rescaling multiplies every
    /// activity by the same positive factor, preserving their relative order — and
    /// hence every `pick_unassigned` decision — exactly (mirrors `proof_sat`).
    fn bump_var(&mut self, var: usize) {
        self.activity[var] += self.var_inc;
        if self.activity[var] > VSIDS_RESCALE_LIMIT {
            for a in &mut self.activity {
                *a *= VSIDS_RESCALE;
            }
            self.var_inc *= VSIDS_RESCALE;
        }
    }

    /// Decays activity by growing the bump increment (the `MiniSat` trick): future
    /// bumps weigh more, so older bumps fade geometrically. Called once per
    /// conflict.
    fn decay(&mut self) {
        self.var_inc /= VSIDS_DECAY;
    }

    /// The current Boolean value of `var` (its trail polarity), or `None` if it is
    /// unassigned. `pub(crate)` so the `QF_UFLRA` Boolean layer can read the
    /// theory-atom + interface assignment off a SAT leaf to rebuild and replay-check the
    /// combined model.
    pub(crate) fn value_of(&self, var: usize) -> Option<bool> {
        self.value.get(var).copied().flatten()
    }

    /// Test-only: the number of 1-UIP conflict analyses run (the "the loop fires"
    /// diagnostic for the `QF_UFLRA` real-`CDCL(T)` layer, mirroring the `LRA` driver's
    /// own `analyze_fires` gate).
    #[cfg(test)]
    pub(crate) fn analyze_fires(&self) -> usize {
        self.diag.analyze_fires
    }

    /// Test-only: lowers the first-reduction budget so a small conflict-heavy
    /// fixture exercises [`Self::reduce_db`]. Must be set before [`Self::solve`].
    #[cfg(test)]
    pub(crate) fn set_reduce_first_for_test(&mut self, first: usize) {
        self.reduce_first_override = Some(first);
    }

    /// Test-only: the number of [`Self::reduce_db`] reductions performed.
    #[cfg(test)]
    pub(crate) fn reductions(&self) -> usize {
        self.reductions
    }

    /// Test-only: the number of [`Luby`](luby) restarts performed so far. The index
    /// starts at `1`, so the restart count is `restart_count - 1`.
    #[cfg(test)]
    pub(crate) fn restarts(&self) -> u64 {
        self.restart_count - 1
    }

    /// Test-only: lowers the restart unit so a small conflict-heavy fixture crosses
    /// the Luby trigger and exercises a real restart. Must be set before
    /// [`Self::solve`].
    #[cfg(test)]
    pub(crate) fn force_early_restart_for_test(&mut self) {
        self.restart_unit_override = Some(1);
    }

    /// Test-only: raises the restart unit so the Luby trigger is never crossed — the
    /// never-restart baseline for the verdict-invariance comparison. Must be set
    /// before [`Self::solve`].
    #[cfg(test)]
    pub(crate) fn disable_restarts_for_test(&mut self) {
        self.restart_unit_override = Some(usize::MAX);
    }

    /// Test-only: the number of learned clauses tombstoned by reductions so far
    /// (total stored learned clauses minus the live count).
    #[cfg(test)]
    pub(crate) fn deleted_learned_count(&self) -> usize {
        (self.clauses.len() - self.num_original) - self.learned_live
    }

    /// Test-only soundness check: no tombstoned clause is currently a *locked*
    /// reason on the trail (an active reason clause must never be deleted). Returns
    /// `true` when every assigned variable whose reason is a stored learned clause
    /// points at a live (non-deleted) clause.
    #[cfg(test)]
    pub(crate) fn no_deleted_active_reason(&self) -> bool {
        self.reason_clause
            .iter()
            .enumerate()
            .all(|(var, slot)| match slot {
                Some(cid) => self.value[var].is_none() || !self.deleted[*cid],
                None => true,
            })
    }

    /// Test-only: the summed length of every learned 1-UIP asserting clause.
    /// `pub(crate)` so the `QF_LIA` driver's in-source 1-UIP gate
    /// ([`crate::lia_online`]) can read the shorter-on-average improvement metric
    /// off the shared generic driver, exactly as the in-`LRA` gate does.
    #[cfg(test)]
    pub(crate) fn learned_len_total(&self) -> u64 {
        self.diag.learned_len_total
    }

    /// Test-only: the summed length of the corresponding full conflict clauses
    /// (`¬⋀core`) the old chronological scheme would have learned. Paired with
    /// [`Self::learned_len_total`] for the `QF_LIA` driver's shorter-on-average gate.
    #[cfg(test)]
    pub(crate) fn conflict_len_total(&self) -> u64 {
        self.diag.conflict_len_total
    }

    /// Test-only: the learned 1-UIP asserting clauses (those stored after the initial
    /// skeleton), each paired with `(is_theory_lemma, level0_atom_facts)`. The `QF_UFLRA`
    /// layer's 1-UIP-over-combination soundness gate re-validates every theory lemma with
    /// the trusted conjunctive decider, exactly as the `LRA` driver's gate does.
    #[cfg(test)]
    #[allow(clippy::type_complexity)]
    pub(crate) fn learned_lemmas(&self) -> Vec<(Vec<Lit>, bool, Vec<(usize, bool)>)> {
        let learned = &self.clauses[self.diag.initial_clauses..];
        learned
            .iter()
            .zip(self.diag.lemma_flags.iter())
            .zip(self.diag.lemma_level0.iter())
            .map(|((clause, &lemma), level0)| (clause.clone(), lemma, level0.clone()))
            .collect()
    }

    /// Runs the search. Returns `true` iff the skeleton is UNSAT under the theory,
    /// `false` on a Boolean- and theory-consistent total assignment.
    pub(crate) fn solve<T: TheorySolver>(&mut self, theory: &mut T) -> bool {
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
            // Luby restart: once enough conflicts have accumulated, abandon the
            // current partial assignment and re-decide from the root. We backjump to
            // decision level 0 — undoing the trail, popping `theory` once per crossed
            // decision in lockstep (the same `backjump_to` discipline), so the theory
            // returns to exactly its level-0 (root) state. The learned-clause DB and
            // every `VSIDS` activity are preserved untouched, which is what makes a
            // restart help (better decisions over the accumulated clauses) and what
            // makes it verdict-invariant (the formula + clauses + root theory state
            // are unchanged, so sat/unsat cannot move). Only at a real decision
            // (`decision_level() > 0`) is there a partial assignment worth abandoning.
            if self.decision_level > 0 && self.conflicts_since_restart >= self.restart_limit() {
                self.backjump_to(theory, 0);
                self.conflicts_since_restart = 0;
                self.restart_count += 1;
                continue;
            }
            match self.pick_unassigned() {
                None => return false,
                Some(var) => {
                    self.decision_level += 1;
                    theory.push();
                    // Phase saving: branch on the variable's last-settled polarity
                    // (its `saved_phase`, initialized to `true` so a never-yet-seen
                    // variable keeps the prior fixed `true`-first default). The
                    // variable choice came from VSIDS in `pick_unassigned`; only the
                    // polarity is the saved phase. Either polarity is a valid branch,
                    // so this is verdict-invariant.
                    let polarity = self.saved_phase[var];
                    if let Err(core) =
                        self.assign(theory, var, polarity, Cause::Decision, None, false)
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
    /// non-chronologically to the backjump level, and enqueues the UIP literal as
    /// an implied assignment with the learned clause as its reason. `false` when
    /// the conflict is implied at level 0 (UNSAT) — there is nothing to assert.
    fn learn_and_backjump<T: TheorySolver>(&mut self, theory: &mut T, conflict: &Conflict) -> bool {
        let (learned, backjump, is_theory_lemma) =
            self.analyze_conflict(&conflict.clause, conflict.is_theory);
        // VSIDS decay: one step per conflict, so the activity recency window mirrors
        // `axeyum_cnf::proof_sat`. Heuristic only — does not affect the verdict.
        self.decay();
        // Count this conflict toward the next Luby restart. `learn_and_backjump` is
        // the single chokepoint every conflict (Boolean or theory) routes through,
        // so one bump here counts each conflict exactly once. Heuristic only.
        self.conflicts_since_restart += 1;
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
            // unconditional). The conflict was analyzed against the current trail,
            // so capture the level-0 atom prefix now, before backjumping.
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
        // The clause's LBD is the number of distinct decision levels among its
        // literals, measured *now* (post-backjump): the UIP is at `backjump` and
        // every other literal is at or below it, the standard learning-time LBD.
        let lbd = self.compute_lbd(&learned);
        let clause_id = self.clauses.len();
        // The just-pushed clause is the UIP's reason exactly when it has the other
        // literals to force it (`reason.is_some()`); a unit learned clause asserts
        // the UIP at level 0 with no reason clause, so it is never locked.
        let uip_locked_by_clause = reason.is_some();
        self.clauses.push(learned);
        self.register_learned(lbd);
        // Enqueue the UIP literal. At the backjump level its theory assertion is
        // consistent (the asserting clause is an entailed resolvent), but a
        // *theory* conflict can still surface here — re-analyze that conflict. The
        // learned clause is the UIP's reason, a theory clause iff it is a theory
        // lemma. Record the clause index as the UIP's reason clause so `reduce_db`
        // protects it while it is locked.
        let assigned = self.assign(
            theory,
            uip.var,
            uip.positive,
            Cause::Implied,
            reason,
            is_theory_lemma,
        );
        if uip_locked_by_clause {
            self.reason_clause[uip.var] = Some(clause_id);
        }
        // Database reduction (Glucose/MiniSat schedule): once the live learned
        // count exceeds the growing budget, tombstone the worst half. Sound: every
        // learned clause is a redundant resolvent, so deleting one never changes
        // sat/unsat — see `reduce_db`. Run here (after the backjump + enqueue,
        // before the next propagation) so the trail and reasons are consistent.
        if self.learned_live > self.reduce_budget() {
            self.reduce_db();
            self.reductions += 1;
        }
        match assigned {
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

    /// Literal-block distance of a learned clause: the number of distinct decision
    /// levels among its literals' current assignments. Computed at learning time,
    /// when every literal of the clause is assigned. `LBD <= GLUE_LBD` "glue"
    /// clauses are the most valuable and are kept permanently by [`Self::reduce_db`].
    fn compute_lbd(&self, clause: &[Lit]) -> usize {
        let mut levels: Vec<usize> = clause.iter().map(|lit| self.level[lit.var]).collect();
        levels.sort_unstable();
        levels.dedup();
        levels.len()
    }

    /// Registers a freshly learned clause's deletion metadata: its `LBD`, a fresh
    /// monotone activity stamp, a live (non-deleted) tombstone, and bumps the live
    /// learned count. Keeps the per-clause metadata vectors aligned with
    /// [`Self::clauses`] by index.
    fn register_learned(&mut self, lbd: usize) {
        self.lbd.push(lbd);
        self.cla_activity.push(self.cla_inc);
        self.deleted.push(false);
        self.learned_live += 1;
        // Advance the stamp so the next learned clause is strictly fresher. A tiny
        // additive step keeps the sequence deterministic and overflow-free over any
        // realistic conflict count.
        self.cla_inc += 1.0;
    }

    /// The learned-clause budget for the current reduction round (additive
    /// schedule: grows by [`REDUCE_INC`] after each reduction).
    fn reduce_budget(&self) -> usize {
        #[cfg(test)]
        let first = self.reduce_first_override.unwrap_or(REDUCE_FIRST);
        #[cfg(not(test))]
        let first = REDUCE_FIRST;
        first + REDUCE_INC * self.reductions
    }

    /// Conflicts allowed before the next [`Luby`](luby) restart, namely
    /// `luby(restart_count)` scaled by [`LUBY_UNIT`]. A pure function of
    /// `restart_count`, so the schedule — and hence the trajectory — is deterministic.
    /// Saturates on the (astronomically unreachable) overflow rather than wrapping,
    /// so a huge index never spuriously restarts.
    fn restart_limit(&self) -> usize {
        #[cfg(test)]
        let unit = self.restart_unit_override.unwrap_or(LUBY_UNIT);
        #[cfg(not(test))]
        let unit = LUBY_UNIT;
        usize::try_from(luby(self.restart_count))
            .unwrap_or(usize::MAX)
            .saturating_mul(unit)
    }

    /// Is learned clause `cid` currently *locked* — the reason for an assigned
    /// literal on the trail? A locked learned clause must not be deleted: it is
    /// needed for conflict analysis / backjump over that literal. (Reasons are
    /// stored as cloned literal vectors, so a deletion could not actually dangle a
    /// trail index, but protecting locked clauses keeps the search's implication
    /// graph re-derivable and mirrors the Glucose protocol exactly.)
    fn is_locked(&self, cid: usize) -> bool {
        self.clauses[cid].first().is_some_and(|lit| {
            self.value[lit.var].is_some() && self.reason_clause[lit.var] == Some(cid)
        })
    }

    /// Glucose/MiniSat `reduceDB`: tombstone the worst half of the deletion-eligible
    /// learned clauses, protecting originals, glue (`LBD <= GLUE_LBD`) clauses, and
    /// locked clauses (a current reason on the trail). Worst-first order is by
    /// descending `LBD` (higher = less valuable), then ascending activity (staler
    /// first), then descending clause index — a total, deterministic order (no
    /// hash-map iteration). Deletion is by tombstone (the slot is kept, not
    /// reused), so every clause index — and thus the `clauses[num_original..]`
    /// learned stream the diagnostics align with — stays stable.
    ///
    /// Soundness: every learned clause is a 1-UIP resolvent entailed by the input
    /// clauses plus the theory, so it is redundant; removing a redundant clause
    /// cannot change the formula's models, hence never flips sat/unsat. Only
    /// learned, non-locked clauses are ever removed.
    fn reduce_db(&mut self) {
        let mut candidates: Vec<usize> = (self.num_original..self.clauses.len())
            .filter(|&cid| !self.deleted[cid] && self.lbd[cid] > GLUE_LBD && !self.is_locked(cid))
            .collect();
        if candidates.is_empty() {
            return;
        }
        candidates.sort_by(|&x, &y| {
            self.lbd[y]
                .cmp(&self.lbd[x])
                .then_with(|| {
                    self.cla_activity[x]
                        .partial_cmp(&self.cla_activity[y])
                        .unwrap_or(core::cmp::Ordering::Equal)
                })
                .then_with(|| y.cmp(&x))
        });
        let to_delete = candidates.len() / 2;
        for &cid in candidates.iter().take(to_delete) {
            self.deleted[cid] = true;
            self.learned_live -= 1;
        }
    }
}

/// Tseitin encoder from the typed Boolean IR into a CNF skeleton, with the first
/// `atom_terms.len()` variables reserved for the registered LRA atoms (numbered
/// to match [`LraTheory`]).
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

    /// Encodes Boolean term `t`, returning the variable whose truth equals `t`,
    /// or `None` for structure outside the supported connectives (sound give-up).
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

/// Collects the distinct real order/equality atoms in `term`, in a stable
/// left-to-right scan (so atom indexing is deterministic).
fn collect_lra_atoms(
    arena: &TermArena,
    term: TermId,
    out: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
) {
    if is_lra_atom(arena, term) {
        if seen.insert(term) {
            out.push(term);
        }
        return;
    }
    if let TermNode::App { args, .. } = arena.node(term) {
        for &a in args {
            collect_lra_atoms(arena, a, out, seen);
        }
    }
}

/// Whether `term` is a linear-real order atom (`<,<=,>,>=`) or a real equality
/// atom — the atoms this online theory abstracts.
fn is_lra_atom(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::App {
            op: Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe,
            ..
        } => true,
        TermNode::App { op: Op::Eq, args } => is_real(arena, args[0]),
        _ => false,
    }
}

/// Decides a `QF_LRA` query (an arbitrary Boolean combination of linear real
/// order/equality atoms) by the **online** `DPLL(T)` loop, returning a
/// **replay-checked** model on `sat`. The warm analogue of
/// [`crate::dpll_t::check_with_lra_dpll`].
///
/// The Boolean skeleton (over the distinct real atoms plus any Boolean leaves) is
/// searched by a self-contained `DPLL(T)` driver that keeps one backtrackable
/// [`LraTheory`] in lockstep; on a Boolean- and theory-consistent total
/// assignment it builds a candidate real model and **replays it against the
/// original assertions** — the soundness gate, so a model the incremental theory
/// cannot justify yields [`CheckResult::Unknown`], never a wrong `sat`. `unsat`
/// is a sound refutation (only ever returned at a root-level conflict).
///
/// Returns [`CheckResult::Unknown`] when there are no LRA atoms, the Boolean
/// skeleton has structure the encoder does not cover, or an arithmetic overflow
/// made the feasibility check inconclusive.
///
/// # Errors
///
/// Never returns `Err` in this slice (every give-up is a conservative
/// [`CheckResult::Unknown`]); the [`SolverError`] return type matches
/// [`crate::dpll_t::check_with_lra_dpll`] for interchange so a future stricter
/// variant can surface [`SolverError::Unsupported`].
pub fn check_qf_lra_online(
    arena: &TermArena,
    assertions: &[TermId],
    _config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Distinct real atoms over the whole assertion set become the theory's atom
    // indices and the first `atom_count` skeleton variables.
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_lra_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return Ok(CheckResult::Unknown(unknown(
            "no linear-real atoms for the online LRA path",
        )));
    }

    let mut enc = Encoder::new(&atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    for &assertion in assertions {
        let Some(top) = enc.encode(arena, assertion, &mut clauses) else {
            return Ok(CheckResult::Unknown(unknown(
                "boolean skeleton outside the online LRA encoder",
            )));
        };
        clauses.push(vec![Lit {
            var: top,
            positive: true,
        }]);
    }

    let atom_count = atom_terms.len();
    let mut builder = AtomBuilder::default();
    let atoms: Vec<AtomKind> = atom_terms
        .iter()
        .map(|&t| builder.build(arena, t))
        .collect();
    let builder_vars = builder.vars.clone();
    let nvars = builder.vars.len();
    let mut theory = LraTheory {
        atoms,
        nvars,
        live: Vec::new(),
        assigned: vec![None; atom_count],
        assigned_log: Vec::new(),
        trail: Vec::new(),
        vars: builder.vars,
    };

    let mut solver = Dpll::new(enc.var_count, atom_count, clauses);
    if solver.solve(&mut theory) {
        return Ok(CheckResult::Unsat);
    }
    // Theory-consistent total assignment: build a model and replay it.
    match theory.model(&builder_vars) {
        Some(model) if replays(arena, assertions, &model) => Ok(CheckResult::Sat(model)),
        _ => Ok(CheckResult::Unknown(unknown(
            "online LRA model did not replay (arithmetic outside the incremental engine)",
        ))),
    }
}

/// Whether `model` satisfies every assertion under the ground evaluator. Any
/// non-`true` or evaluation error makes it not replay (→ `Unknown`, never a
/// wrong `sat`).
fn replays(arena: &TermArena, assertions: &[TermId], model: &Model) -> bool {
    let mut assignment = Assignment::new();
    for (symbol, value) in model.iter() {
        assignment.set(symbol, value);
    }
    assertions
        .iter()
        .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))))
}

/// Test-only diagnostic run of the online LRA driver over a conjunction of
/// `assertions`: returns the verdict (`true` = UNSAT), the registered atom terms,
/// the atom count, the learned 1-UIP asserting clauses, and the fires/length
/// diagnostics. Mirrors the setup of [`check_qf_lra_online`]. Used by the
/// in-source soundness tests to confirm each learned clause is entailed and that
/// 1-UIP fired and shrank the learned clauses below the full conflict cores.
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
    minimize_fires: usize,
    minimize_removed_total: u64,
}

#[cfg(test)]
fn run_online_diag(arena: &TermArena, assertions: &[TermId]) -> Option<OnlineDiag> {
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_lra_atoms(arena, a, &mut atom_terms, &mut seen);
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
    let mut builder = AtomBuilder::default();
    let atoms: Vec<AtomKind> = atom_terms
        .iter()
        .map(|&t| builder.build(arena, t))
        .collect();
    let nvars = builder.vars.len();
    let mut theory = LraTheory {
        atoms,
        nvars,
        live: Vec::new(),
        assigned: vec![None; atom_count],
        assigned_log: Vec::new(),
        trail: Vec::new(),
        vars: builder.vars,
    };
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
        minimize_fires: solver.diag.minimize_fires,
        minimize_removed_total: solver.diag.minimize_removed_total,
    })
}

/// A classified `unknown` reason for the online LRA path.
fn unknown(detail: &str) -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: detail.to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rconst(arena: &mut TermArena, n: i128) -> TermId {
        arena.real_const(Rational::integer(n))
    }

    fn rvar(arena: &mut TermArena, name: &str) -> TermId {
        let s = arena.declare(name, Sort::Real).expect("declare real");
        arena.var(s)
    }

    #[test]
    fn infeasible_set_yields_check_with_lra_unsat_core() {
        // x > 1 and x < 0: infeasible.
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let one = rconst(&mut arena, 1);
        let zero = rconst(&mut arena, 0);
        let gt = arena.real_gt(x, one).expect("x>1");
        let lt = arena.real_lt(x, zero).expect("x<0");

        let mut theory = LraTheory::new(&arena, &[gt, lt]);
        assert!(theory.assert(0, true).is_ok());
        let core = theory.assert(1, true).expect_err("infeasible");
        assert!(!core.is_empty(), "conflict core must be non-empty");
        // The core's atoms, asserted at their polarities, must be
        // check_with_lra-unsat.
        let core_terms: Vec<TermId> = core
            .iter()
            .map(|l| if l.atom == 0 { gt } else { lt })
            .collect();
        let verdict = crate::lra::check_with_lra(&arena, &core_terms).expect("decidable");
        assert_eq!(verdict, CheckResult::Unsat, "explained core must be unsat");
    }

    #[test]
    fn push_assert_pop_restores_feasibility() {
        // Start feasible (x >= 0). Push, add x <= -1 (infeasible), pop, feasible
        // again.
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let neg1 = rconst(&mut arena, -1);
        let ge = arena.real_ge(x, zero).expect("x>=0");
        let le = arena.real_le(x, neg1).expect("x<=-1");

        let mut theory = LraTheory::new(&arena, &[ge, le]);
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
    fn non_lra_atom_is_a_no_op() {
        // A BV equality atom registers as Unsupported (no-op), never panics.
        let mut arena = TermArena::new();
        let bv = arena.declare("b", Sort::BitVec(8)).expect("declare bv");
        let v = arena.var(bv);
        let k = arena.bv_const(8, 5).expect("bv const");
        let eq = arena.eq(v, k).expect("bv eq");

        let mut theory = LraTheory::new(&arena, &[eq]);
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
        let x = rvar(&mut arena, "x");
        let three = rconst(&mut arena, 3);
        let two = rconst(&mut arena, 2);
        let eq = arena.eq(x, three).expect("x=3");
        let lt = arena.real_lt(x, two).expect("x<2");

        let mut theory = LraTheory::new(&arena, &[eq, lt]);
        assert!(theory.tracks(0) && theory.tracks(1));
        assert!(theory.assert(0, true).is_ok());
        assert!(theory.assert(1, true).is_err(), "x=3 and x<2 infeasible");
    }

    #[test]
    fn online_decider_agrees_on_a_small_unsat() {
        // (x < y) and (y < x): unsat.
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let y = rvar(&mut arena, "y");
        let xy = arena.real_lt(x, y).expect("x<y");
        let yx = arena.real_lt(y, x).expect("y<x");
        let verdict =
            check_qf_lra_online(&arena, &[xy, yx], &SolverConfig::default()).expect("decidable");
        assert_eq!(verdict, CheckResult::Unsat);
    }

    #[test]
    fn online_decider_sat_model_replays() {
        // (x < y) or (y < x): sat, model must replay.
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let y = rvar(&mut arena, "y");
        let xy = arena.real_lt(x, y).expect("x<y");
        let yx = arena.real_lt(y, x).expect("y<x");
        let or = arena.or(xy, yx).expect("or");
        let verdict =
            check_qf_lra_online(&arena, &[or], &SolverConfig::default()).expect("decidable");
        match verdict {
            CheckResult::Sat(model) => assert!(replays(&arena, &[or], &model)),
            other => panic!("expected sat, got {other:?}"),
        }
    }

    /// `VSIDS` mechanism gate: a hand-built conflict trail must (1) bump *exactly*
    /// the variables resolved through 1-UIP analysis, leaving the rest at zero
    /// activity (so the activity vector is non-uniform after a conflict), (2) make
    /// [`Dpll::pick_unassigned`] prefer a bumped variable over a lower-index
    /// un-bumped one (`VSIDS` genuinely changes the decision order from the old
    /// static lowest-index pick), and (3) be fully deterministic — the same trail
    /// analyzed twice yields byte-identical activities and the same learned clause.
    /// A no-op (`NoTheory`) theory keeps this focused on the Boolean `VSIDS` core.
    #[test]
    fn vsids_bumps_conflict_vars_and_reorders_decisions() {
        // Build the conflict scenario once on a fresh `Dpll` and return its post-
        // analysis activity vector + learned clause, so we can run it twice and
        // compare for determinism.
        fn run() -> (Vec<f64>, Vec<Lit>) {
            // Four Boolean vars; no clauses needed (we drive `analyze_conflict`
            // directly with a hand-built trail).
            let mut dpll = Dpll::new(4, 0, Vec::new());
            // Decision: v0 := true at level 1.
            dpll.decision_level = 1;
            dpll.value[0] = Some(true);
            dpll.level[0] = 1;
            dpll.trail.push((0, true, Cause::Decision));
            // Implied: v1 := true at level 1, forced by (¬v0 ∨ v1).
            dpll.value[1] = Some(true);
            dpll.level[1] = 1;
            dpll.reason[1] = Some(vec![
                Lit {
                    var: 0,
                    positive: false,
                },
                Lit {
                    var: 1,
                    positive: true,
                },
            ]);
            dpll.trail.push((1, true, Cause::Implied));
            // Conflict clause (¬v0 ∨ ¬v1): both literals false under the trail.
            let conflict = vec![
                Lit {
                    var: 0,
                    positive: false,
                },
                Lit {
                    var: 1,
                    positive: false,
                },
            ];
            let (learned, _backjump, _theory) = dpll.analyze_conflict(&conflict, false);
            (dpll.activity, learned)
        }

        let (activity, learned) = run();
        // (1) Exactly v0 and v1 (resolved through) are bumped; v2, v3 stay zero.
        // Activity only ever increases from 0.0, so "not positive" ⇔ "never bumped".
        assert!(activity[0] > 0.0, "v0 (UIP) must be bumped");
        assert!(activity[1] > 0.0, "v1 (resolved) must be bumped");
        assert!(activity[2] <= 0.0, "untouched v2 stays at zero activity");
        assert!(activity[3] <= 0.0, "untouched v3 stays at zero activity");
        // The learned 1-UIP asserting clause is the unit (¬v0).
        assert_eq!(learned.len(), 1, "1-UIP learns a unit here");
        assert_eq!(learned[0].var, 0);
        assert!(!learned[0].positive, "asserts ¬v0");

        // (2) `pick_unassigned` now prefers a bumped var over a lower-index zero one.
        // Construct a fresh `Dpll`, bump only v2 (a higher index), and confirm the
        // pick is v2 — NOT v0, which the old static lowest-index rule would return.
        let mut picker = Dpll::new(4, 0, Vec::new());
        picker.bump_var(2);
        assert_eq!(
            picker.pick_unassigned(),
            Some(2),
            "VSIDS must pick the most-active var (2), not the lowest index (0)"
        );
        // Ties (all zero) break to the lowest index — the deterministic fallback.
        let plain = Dpll::new(4, 0, Vec::new());
        assert_eq!(
            plain.pick_unassigned(),
            Some(0),
            "all-equal activities tie-break to the lowest index"
        );

        // (3) Determinism: the identical trail analyzed again is byte-identical.
        let (activity2, learned2) = run();
        assert_eq!(
            activity, activity2,
            "VSIDS activities must be deterministic"
        );
        assert_eq!(learned, learned2, "learned clause must be deterministic");
    }

    /// Self-subsuming **minimization** mechanism gate on a hand-built conflict.
    /// The 1-UIP asserting clause is `(¬v0 ∨ ¬v1 ∨ ¬v2)`, but `v2`'s reason is
    /// `(¬v1 ∨ v2)` — so `¬v2` is implied by `¬v1` (already in the clause) and is
    /// redundant. Minimization must drop it, yielding the strictly shorter
    /// `(¬v0 ∨ ¬v1)`. That shorter clause is still a valid resolvent of the
    /// pre-minimization clause against `reason(v2)` on `v2`, hence still entailed —
    /// verdict-invariant. Determinism: the identical trail analyzed twice yields the
    /// identical minimized clause. A no-op theory keeps this on the Boolean core.
    #[test]
    fn minimization_removes_a_self_subsumed_literal() {
        // Reason clauses here all contain the propagated literal as a member (the
        // `Dpll` convention), distinguishing it inside `lit_redundant` by variable.
        fn run() -> (Vec<Lit>, usize) {
            let mut dpll = Dpll::new(5, 0, Vec::new());
            // Level 1: decision v1 := true.
            dpll.decision_level = 1;
            dpll.value[1] = Some(true);
            dpll.level[1] = 1;
            dpll.trail.push((1, true, Cause::Decision));
            // Level 1: implied v2 := true by reason (¬v1 ∨ v2).
            dpll.value[2] = Some(true);
            dpll.level[2] = 1;
            dpll.reason[2] = Some(vec![
                Lit {
                    var: 1,
                    positive: false,
                },
                Lit {
                    var: 2,
                    positive: true,
                },
            ]);
            dpll.trail.push((2, true, Cause::Implied));
            // Level 2: decision v3 := true (an intervening level, unused by the
            // conflict — present so the trail spans several levels).
            dpll.decision_level = 2;
            dpll.value[3] = Some(true);
            dpll.level[3] = 2;
            dpll.trail.push((3, true, Cause::Decision));
            // Level 3 (current): decision v0 := true — the sole current-level
            // literal of the conflict, hence the 1-UIP.
            dpll.decision_level = 3;
            dpll.value[0] = Some(true);
            dpll.level[0] = 3;
            dpll.trail.push((0, true, Cause::Decision));
            // Conflict (¬v0 ∨ ¬v1 ∨ ¬v2): all three literals false under the trail.
            let conflict = vec![
                Lit {
                    var: 0,
                    positive: false,
                },
                Lit {
                    var: 1,
                    positive: false,
                },
                Lit {
                    var: 2,
                    positive: false,
                },
            ];
            let (learned, backjump, _theory) = dpll.analyze_conflict(&conflict, false);
            (learned, backjump)
        }

        let (learned, backjump) = run();
        // Minimization dropped ¬v2 (self-subsumed by ¬v1 via reason(v2)).
        assert_eq!(
            learned.len(),
            2,
            "minimized clause must be shorter than the 3-literal 1-UIP clause: {learned:?}"
        );
        // The asserting (UIP) literal ¬v0 stays at index 0 — the only current-level
        // literal, so still a valid asserting clause.
        assert_eq!(learned[0].var, 0, "UIP literal kept at index 0");
        assert!(!learned[0].positive, "asserts ¬v0");
        // The surviving non-asserting literal is ¬v1 (v2 was removed).
        assert_eq!(learned[1].var, 1, "¬v1 survives, ¬v2 removed");
        assert!(!learned[1].positive, "asserts ¬v1");
        assert!(
            !learned.iter().any(|l| l.var == 2),
            "the self-subsumed literal ¬v2 must be gone: {learned:?}"
        );
        // Backjump is recomputed from the MINIMIZED clause: only ¬v1 (level 1)
        // remains besides the UIP, so the backjump level is 1.
        assert_eq!(backjump, 1, "backjump recomputed from the minimized clause");

        // Still-entailed (resolvent) check: {¬v0, ¬v1} is the resolvent of the
        // pre-minimization {¬v0, ¬v1, ¬v2} with reason(v2) = {¬v1, v2} on v2, so it
        // is logically implied — minimization is verdict-invariant.
        // Determinism: the same hand-built trail minimizes identically.
        let (learned2, backjump2) = run();
        assert_eq!(learned, learned2, "minimized clause must be deterministic");
        assert_eq!(backjump, backjump2, "backjump must be deterministic");
    }

    /// Phase-saving mechanism gate (verdict-invariant heuristic). Three claims:
    /// (1) `saved_phase` initializes to `true` so a never-seen variable's first
    /// decision matches the prior fixed `true`-first default (the determinism
    /// baseline); (2) [`Dpll::assign`] updates `saved_phase[var]` to the assigned
    /// value on *every* assignment (decision or propagation); (3) after that
    /// polarity is recorded, a re-decision genuinely reuses the saved phase rather
    /// than the fixed default — here `false`, the opposite of the old default.
    /// With `atom_count == 0`, [`Dpll::assign`]'s `var < atom_count` guard never
    /// touches the theory, so a no-op theory keeps this on the Boolean core.
    #[test]
    fn phase_saving_updates_on_assign_and_steers_redecision() {
        /// No-op theory: every variable is a pure Boolean (no atom is mirrored,
        /// since `atom_count == 0`), so these are never called — they exist only to
        /// satisfy the [`TheorySolver`] bound.
        struct NoTheory;
        impl TheorySolver for NoTheory {
            fn assert(&mut self, _atom: usize, _value: bool) -> Result<(), Vec<TheoryLit>> {
                Ok(())
            }
            fn push(&mut self) {}
            fn pop(&mut self) {}
            fn propagate(&self) -> Vec<TheoryProp> {
                Vec::new()
            }
        }

        let mut theory = NoTheory;
        let mut dpll = Dpll::new(3, 0, Vec::new());
        // (1) Fresh init: every saved phase is the `true`-first default.
        assert_eq!(
            dpll.saved_phase,
            vec![true, true, true],
            "saved_phase initializes to the true-first default"
        );

        // (2) Assign v0 := false (as if a decision had branched false). `assign`
        // must record that polarity into saved_phase.
        dpll.decision_level = 1;
        dpll.assign(&mut theory, 0, false, Cause::Decision, None, false)
            .expect("no-theory assign cannot fail");
        assert!(
            !dpll.saved_phase[0],
            "assign must save the assigned polarity (false here)"
        );
        // A propagation polarity is saved too: v1 := false, implied.
        dpll.assign(&mut theory, 1, false, Cause::Implied, None, false)
            .expect("no-theory assign cannot fail");
        assert!(
            !dpll.saved_phase[1],
            "assign saves the polarity of propagations as well as decisions"
        );

        // (3) Unassign v0 (as a backjump would) — saved_phase must survive — then a
        // re-decision reuses the saved `false`, not the fixed `true` default.
        dpll.value[0] = None;
        assert!(
            !dpll.saved_phase[0],
            "saved_phase outlives the variable being unassigned"
        );
        let redecision_polarity = dpll.saved_phase[0];
        assert!(
            !redecision_polarity,
            "re-decision uses the saved phase (false), not the old true-first default"
        );
        // v2 was never assigned, so it would still decide at the default `true`.
        assert!(
            dpll.saved_phase[2],
            "an untouched variable still decides at the true-first default"
        );
    }

    /// End-to-end determinism through the public driver: the same `QF_LRA` query
    /// decided twice must yield the same verdict and the same `sat` model (the
    /// `VSIDS` decision order is a deterministic function of the encoding, so the
    /// whole search trajectory — and thus the witness — is reproducible).
    #[test]
    fn driver_is_deterministic_across_repeated_runs() {
        // A mixed sat instance with disjunction (forces branching, hence VSIDS).
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let y = rvar(&mut arena, "y");
        let zero = rconst(&mut arena, 0);
        let lt = arena.real_lt(x, y).expect("x<y");
        let ge = arena.real_ge(y, zero).expect("y>=0");
        let or = arena.or(lt, ge).expect("or");
        let cfg = SolverConfig::default();

        let first = check_qf_lra_online(&arena, &[or, ge], &cfg).expect("decidable");
        let second = check_qf_lra_online(&arena, &[or, ge], &cfg).expect("decidable");
        match (first, second) {
            (CheckResult::Sat(m1), CheckResult::Sat(m2)) => {
                assert!(replays(&arena, &[or, ge], &m1));
                assert_eq!(
                    m1.get(symbol_of(&arena, x)),
                    m2.get(symbol_of(&arena, x)),
                    "repeated runs must yield the same model for x"
                );
                assert_eq!(
                    m1.get(symbol_of(&arena, y)),
                    m2.get(symbol_of(&arena, y)),
                    "repeated runs must yield the same model for y"
                );
            }
            (a, b) => assert_eq!(a, b, "repeated runs must yield the same verdict"),
        }
    }

    /// The [`SymbolId`] backing a declared variable term (for model lookups).
    fn symbol_of(arena: &TermArena, var: TermId) -> SymbolId {
        match arena.node(var) {
            TermNode::Symbol(s) => *s,
            _ => panic!("expected a symbol term"),
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

    /// Builds a random linear order/equality atom `Σ c_i·x_i + k REL 0` over the
    /// given real variables.
    fn random_lra_atom(arena: &mut TermArena, lcg: &mut Lcg, vars: &[TermId]) -> TermId {
        let mut expr: Option<TermId> = None;
        for &v in vars {
            let c = i128::from(lcg.below(7)) - 3;
            if c == 0 {
                continue;
            }
            let coeff = arena.real_const(Rational::integer(c));
            let term = arena.real_mul(coeff, v).expect("c*x");
            expr = Some(match expr {
                None => term,
                Some(acc) => arena.real_add(acc, term).expect("acc+term"),
            });
        }
        let k = i128::from(lcg.below(11)) - 5;
        let kconst = arena.real_const(Rational::integer(k));
        let lhs = match expr {
            None => kconst,
            Some(acc) => arena.real_add(acc, kconst).expect("acc+k"),
        };
        let zero = arena.real_const(Rational::zero());
        match lcg.below(5) {
            0 => arena.real_lt(lhs, zero).expect("lt"),
            1 => arena.real_le(lhs, zero).expect("le"),
            2 => arena.real_gt(lhs, zero).expect("gt"),
            3 => arena.real_ge(lhs, zero).expect("ge"),
            _ => arena.eq(lhs, zero).expect("eq"),
        }
    }

    /// For one solved instance: independently re-validate every **pure theory
    /// lemma** learned clause with the trusted offline decider — `¬clause` together
    /// with the level-0 facts it rests on must be `check_with_lra`-UNSAT (the
    /// clause is genuinely entailed). This runs AFTER minimization, so it certifies
    /// the *minimized* clauses are still implied. Returns how many clauses were
    /// successfully entailment-checked; panics on an unsound (non-entailed) clause.
    fn check_learned_clauses_entailed(
        arena: &mut TermArena,
        atoms: &[TermId],
        diag: &OnlineDiag,
    ) -> usize {
        let mut checked = 0_usize;
        for ((clause, &is_lemma), level0) in diag
            .learned
            .iter()
            .zip(&diag.lemma_flags)
            .zip(&diag.lemma_level0)
        {
            // Only PURE THEORY LEMMAS are entailed by the theory plus the level-0
            // facts — a 1-UIP clause that resolved (in analysis OR minimization)
            // through Boolean input clauses is entailed by formula+theory, not the
            // theory, so the conjunctive offline decider is not its oracle.
            if !is_lemma {
                continue;
            }
            // Restrict to atom-only clauses (Tseitin aux vars have no atom term to
            // negate); theory lemmas over the order/eq fragment are these.
            if clause.iter().any(|l| l.var >= diag.atom_count) {
                continue;
            }
            // ¬clause ∧ level0-facts: every clause literal falsified (atom `var`
            // asserted at `!positive`) together with the unconditional level-0 atom
            // assignments the lemma rests on — must be theory UNSAT.
            let mut neg_terms: Vec<TermId> = Vec::with_capacity(clause.len() + level0.len());
            for lit in clause {
                let atom = diag.atom_terms[lit.var];
                let term = if lit.positive {
                    arena.not(atom).expect("not")
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
                    arena.not(atom).expect("not")
                };
                neg_terms.push(term);
            }
            // The offline decider may decline a negated equality (real disequality is
            // out of its conjunctive scope) — a sound skip, not a clause defect.
            match crate::lra::check_with_lra(arena, &neg_terms) {
                Ok(CheckResult::Unsat) => checked += 1,
                Ok(CheckResult::Sat(m)) => panic!(
                    "UNSOUND LEARNED CLAUSE: ¬clause is SAT\nclause={clause:?}\n\
                     assertions={atoms:?}\nmodel={m:?}"
                ),
                Ok(CheckResult::Unknown(_)) | Err(_) => {}
            }
        }
        checked
    }

    /// SOUNDNESS gate for **1-UIP theory-conflict learning + self-subsuming
    /// minimization**: over a deterministic LCG corpus of random `QF_LRA` formulas
    /// with **disjunctive** assertions (so the driver must branch and learns
    /// non-trivial asserting clauses), drive the online driver and, for EVERY
    /// learned asserting clause whose literals are all theory atoms, independently
    /// verify with the trusted offline decider that the (minimized) clause is
    /// *entailed* — i.e. `¬clause` is `check_with_lra`-UNSAT. A learned clause that
    /// isn't implied is a hard failure (an unsound lemma would corrupt the search).
    /// Also proves the 1-UIP path FIRES, that minimization FIRES (removes ≥1
    /// literal on some conflict), and that learned clauses are strictly SHORTER on
    /// average than the full `¬⋀core` conflict clauses.
    #[test]
    fn learned_clauses_are_entailed_and_shorter() {
        let mut lcg = Lcg(0x1c1c_2b2b_3c3c_4d4d);
        let mut fires_total = 0_usize;
        let mut learned_len_total = 0_u64;
        let mut conflict_len_total = 0_u64;
        let mut clauses_checked = 0_usize;
        let mut minimize_fires_total = 0_usize;
        let mut minimize_removed_total = 0_u64;

        for _ in 0..4000 {
            let mut arena = TermArena::new();
            let nvars = 2 + usize::try_from(lcg.below(2)).expect("small");
            let vars: Vec<TermId> = (0..nvars)
                .map(|i| {
                    let s = arena
                        .declare(&format!("v{i}"), Sort::Real)
                        .expect("declare");
                    arena.var(s)
                })
                .collect();
            // A pool of order/eq atoms; each assertion is a random *disjunction*
            // of two or three of them (so the driver must decide between them,
            // exercising real 1-UIP backjump learning rather than level-0 unit
            // propagation). A wider pool and wider clauses drive deeper search.
            let pool_n = 6;
            let pool: Vec<TermId> = (0..pool_n)
                .map(|_| random_lra_atom(&mut arena, &mut lcg, &vars))
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
            minimize_fires_total += diag.minimize_fires;
            minimize_removed_total += diag.minimize_removed_total;
            clauses_checked += check_learned_clauses_entailed(&mut arena, &atoms, &diag);
        }

        eprintln!(
            "1-UIP gate: fires={fires_total}, clauses_checked={clauses_checked}, \
             learned_len_total={learned_len_total}, conflict_len_total={conflict_len_total}, \
             minimize_fires={minimize_fires_total}, minimize_removed={minimize_removed_total}"
        );
        assert!(fires_total > 50, "1-UIP analysis never meaningfully fired");
        assert!(
            clauses_checked > 20,
            "too few learned clauses entailment-checked ({clauses_checked})"
        );
        // The improvement metric: 1-UIP asserting clauses are strictly shorter
        // than the full conflict cores on average.
        assert!(
            learned_len_total < conflict_len_total,
            "learned clauses not shorter on average ({learned_len_total} vs {conflict_len_total})"
        );
        // Minimization must FIRE: at least one conflict had a 1-UIP literal removed
        // by self-subsuming minimization (and the entailment check above already
        // re-validated every learned clause is STILL implied AFTER minimization).
        assert!(
            minimize_fires_total > 0 && minimize_removed_total > 0,
            "self-subsuming minimization never removed a literal \
             (fires={minimize_fires_total}, removed={minimize_removed_total})"
        );
    }

    /// Builds a `Dpll` + `LraTheory` over a conjunction of `assertions` exactly as
    /// [`check_qf_lra_online`] does, for the in-source reduce-database tests.
    /// Returns the wired solver and theory (un-run), plus the registered atom
    /// terms, so a test can lower the reduce budget before `solve`.
    fn build_solver(arena: &TermArena, assertions: &[TermId]) -> (Dpll, LraTheory) {
        let mut atom_terms: Vec<TermId> = Vec::new();
        let mut seen = HashSet::new();
        for &a in assertions {
            collect_lra_atoms(arena, a, &mut atom_terms, &mut seen);
        }
        let mut enc = Encoder::new(&atom_terms);
        let mut clauses: Vec<Vec<Lit>> = Vec::new();
        for &assertion in assertions {
            let top = enc
                .encode(arena, assertion, &mut clauses)
                .expect("encodable");
            clauses.push(vec![Lit {
                var: top,
                positive: true,
            }]);
        }
        let atom_count = atom_terms.len();
        let mut builder = AtomBuilder::default();
        let atoms: Vec<AtomKind> = atom_terms
            .iter()
            .map(|&t| builder.build(arena, t))
            .collect();
        let nvars = builder.vars.len();
        let theory = LraTheory {
            atoms,
            nvars,
            live: Vec::new(),
            assigned: vec![None; atom_count],
            assigned_log: Vec::new(),
            trail: Vec::new(),
            vars: builder.vars,
        };
        let solver = Dpll::new(enc.var_count, atom_count, clauses);
        (solver, theory)
    }

    /// A Boolean-**pigeonhole** `QF_LRA` formula whose `pigeons × holes` atoms are
    /// *independent* real order atoms (`x_{p,h} < 0`, each over its own real
    /// variable — so every Boolean assignment is trivially theory-feasible and the
    /// feasibility check stays cheap). The Boolean skeleton — "each pigeon in some
    /// hole" ∧ "no two pigeons share a hole" — is purely-Boolean **UNSAT** whenever
    /// `pigeons > holes`, forcing the `Dpll` to learn many 1-UIP asserting clauses
    /// quickly. This is the cheap-theory / hard-Boolean shape that exercises
    /// [`Dpll::reduce_db`] without slow Fourier–Motzkin work. Returns the arena and
    /// the assertion list.
    fn pigeonhole_real_formula(pigeons: usize, holes: usize) -> (TermArena, Vec<TermId>) {
        let mut arena = TermArena::new();
        let zero = arena.real_const(Rational::zero());
        // atom[p][h] is `x_{p,h} < 0` over a fresh real variable.
        let mut atom = vec![vec![arena.bool_const(false); holes]; pigeons];
        for (p, row) in atom.iter_mut().enumerate() {
            for (h, slot) in row.iter_mut().enumerate() {
                let s = arena
                    .declare(&format!("x_{p}_{h}"), Sort::Real)
                    .expect("declare");
                let v = arena.var(s);
                *slot = arena.real_lt(v, zero).expect("x<0");
            }
        }
        let mut assertions: Vec<TermId> = Vec::new();
        // Each pigeon occupies at least one hole: OR over its holes.
        for row in &atom {
            let mut clause = row[0];
            for &a in &row[1..] {
                clause = arena.or(clause, a).expect("or");
            }
            assertions.push(clause);
        }
        // No two pigeons share a hole: for each pigeon pair, forbid them sharing
        // any single hole — ¬(atom[p1][h] ∧ atom[p2][h]) over the zipped columns.
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                for (&a1, &a2) in atom[p1].iter().zip(&atom[p2]) {
                    let both = arena.and(a1, a2).expect("and");
                    assertions.push(arena.not(both).expect("not"));
                }
            }
        }
        (arena, assertions)
    }

    /// Cross-checks the online verdict against running the *same* `Dpll` driver
    /// with reduction disabled (the never-delete baseline) — the cleanest
    /// verdict-invariance oracle, since the formulas here are disjunctive (outside
    /// the conjunctive offline decider's scope). Deletion only forgoes pruning, so
    /// both runs must reach the same sat/unsat. Returns `(unsat, deleted_count,
    /// reductions, no_stale_reason)` for the reduced run.
    fn reduced_vs_baseline(
        arena: &TermArena,
        assertions: &[TermId],
        reduce_first: usize,
    ) -> (bool, usize, usize, bool) {
        // Baseline: no reduction (budget stays astronomically high).
        let (mut base_solver, mut base_theory) = build_solver(arena, assertions);
        base_solver.set_reduce_first_for_test(usize::MAX);
        let base_unsat = base_solver.solve(&mut base_theory);
        // Reduced: a low budget so reduce_db fires.
        let (mut solver, mut theory) = build_solver(arena, assertions);
        solver.set_reduce_first_for_test(reduce_first);
        let unsat = solver.solve(&mut theory);
        assert_eq!(
            unsat, base_unsat,
            "reduce_db FLIPPED the verdict vs the never-delete baseline \
             (reduced={unsat}, baseline={base_unsat})"
        );
        (
            unsat,
            solver.deleted_learned_count(),
            solver.reductions(),
            solver.no_deleted_active_reason(),
        )
    }

    /// `reduce_db` must FIRE on conflict-heavy instances once the learned count
    /// crosses a (lowered) budget — deletions actually happen — AND the verdict is
    /// unchanged vs the never-delete baseline (verdict invariance), AND no
    /// tombstoned clause is ever an active reason on the trail (the stale-reason
    /// guard), AND every `sat` model still replays against the original assertions.
    #[test]
    fn reduce_db_fires_and_keeps_the_verdict() {
        let mut total_deleted = 0_usize;
        let mut total_reductions = 0_usize;
        // A handful of pigeonhole sizes; each is purely-Boolean UNSAT and forces
        // many learned clauses, crossing the lowered budget repeatedly.
        for &(pigeons, holes) in &[(5_usize, 4_usize), (6, 5), (7, 6)] {
            let (arena, assertions) = pigeonhole_real_formula(pigeons, holes);
            let (unsat, deleted, reductions, no_stale) =
                reduced_vs_baseline(&arena, &assertions, 3);
            assert!(unsat, "pigeonhole {pigeons}->{holes} must be UNSAT");
            assert!(
                no_stale,
                "a deleted learned clause is still an active reason (stale reason!)"
            );
            total_deleted += deleted;
            total_reductions += reductions;
        }
        eprintln!("reduce_db gate: reductions={total_reductions}, deleted_total={total_deleted}");
        assert!(
            total_reductions > 0 && total_deleted > 0,
            "reduce_db never fired / deleted nothing (reductions={total_reductions}, \
             deleted={total_deleted})"
        );
    }

    /// Luby restarts must FIRE on conflict-heavy instances (with the unit lowered so
    /// a small fixture crosses the trigger) AND be verdict-invariant: a restart
    /// abandons only the current partial assignment, keeping every learned clause and
    /// activity, so the verdict matches the never-restart baseline. After every
    /// restart — and after the whole solve — the theory is popped back to its root
    /// (its push/pop stack is balanced: empty trail), the guard against a restart
    /// that pops too few/many theory levels and corrupts the theory.
    #[test]
    fn restarts_fire_and_keep_the_verdict() {
        let mut total_restarts = 0_u64;
        for &(pigeons, holes) in &[(5_usize, 4_usize), (6, 5), (7, 6)] {
            let (arena, assertions) = pigeonhole_real_formula(pigeons, holes);

            // Baseline: restarts disabled (the trigger is never crossed), the
            // clean never-restart verdict oracle.
            let (mut base_solver, mut base_theory) = build_solver(&arena, &assertions);
            base_solver.disable_restarts_for_test();
            let base_unsat = base_solver.solve(&mut base_theory);
            assert_eq!(
                base_solver.restarts(),
                0,
                "baseline unexpectedly restarted — the comparison is no longer clean"
            );
            assert!(
                base_theory.trail.is_empty(),
                "baseline theory push/pop imbalance ({} stray level(s))",
                base_theory.trail.len()
            );

            // Restart-enabled: lower the unit so the Luby trigger crosses repeatedly.
            let (mut solver, mut theory) = build_solver(&arena, &assertions);
            solver.force_early_restart_for_test();
            let unsat = solver.solve(&mut theory);

            assert_eq!(
                unsat, base_unsat,
                "restarts FLIPPED the verdict vs the never-restart baseline \
                 (restarted={unsat}, baseline={base_unsat}) on pigeonhole {pigeons}->{holes}"
            );
            assert!(unsat, "pigeonhole {pigeons}->{holes} must be UNSAT");
            assert!(
                solver.restarts() > 0,
                "restarts never fired on pigeonhole {pigeons}->{holes} (count={})",
                solver.restarts()
            );
            // Theory push/pop balance: after the solve returns the theory has been
            // popped back to its root state (no decision levels left on its stack).
            // A restart that popped too few/many levels would leave a residue here.
            assert!(
                theory.trail.is_empty(),
                "theory push/pop IMBALANCE after restarts: {} stray level(s) left on \
                 the theory trail (pigeonhole {pigeons}->{holes})",
                theory.trail.len()
            );
            total_restarts += solver.restarts();
        }
        eprintln!("restart gate: total_restarts={total_restarts}");
        assert!(
            total_restarts > 0,
            "Luby restarts never fired across the fixtures (total={total_restarts})"
        );
    }

    /// Determinism: the same query solved twice yields the identical verdict and the
    /// identical restart trajectory (count). The Luby schedule is a pure function of
    /// the restart index, so the restart points — and the whole search trajectory —
    /// are reproducible.
    #[test]
    fn restarts_are_deterministic() {
        let (arena, assertions) = pigeonhole_real_formula(6, 5);

        let run = || {
            let (mut solver, mut theory) = build_solver(&arena, &assertions);
            solver.force_early_restart_for_test();
            let unsat = solver.solve(&mut theory);
            (unsat, solver.restarts())
        };

        let first = run();
        let second = run();
        assert_eq!(
            first, second,
            "non-deterministic restart trajectory: \
             (unsat, restarts) {first:?} != {second:?}"
        );
        assert!(first.1 > 0, "expected restarts to fire (count={})", first.1);
    }
}
