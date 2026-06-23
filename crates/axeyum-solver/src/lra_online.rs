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

/// A self-contained `DPLL(T)` search over the CNF skeleton driving an
/// [`LraTheory`] online: chronological backtracking with theory-conflict clause
/// learning, the theory pushed on each decision and popped on each backtrack.
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

    /// Assigns `var := value`, mirroring a theory atom into [`LraTheory`].
    fn assign(
        &mut self,
        theory: &mut LraTheory,
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
    fn backtrack_to_decision(&mut self, theory: &mut LraTheory) -> Option<(usize, bool)> {
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
    fn unit_propagate(&mut self, theory: &mut LraTheory) -> Result<(), Vec<Lit>> {
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

    /// Applies sound theory propagations to the trail until fixpoint. Returns the
    /// learned clause on a theory conflict, else `Ok(())`. A mirror of
    /// `crate::euf_egraph::Dpll::theory_propagate` retargeted to [`LraTheory`].
    fn theory_propagate(&mut self, theory: &mut LraTheory) -> Result<(), Vec<Lit>> {
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
                        return Err(Self::theory_conflict_clause(&core));
                    }
                    None => {
                        if let Err(c) = self.assign(theory, var, prop.lit.value, Cause::Implied) {
                            return Err(Self::theory_conflict_clause(&c));
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
    fn propagate(&mut self, theory: &mut LraTheory) -> Result<(), Vec<Lit>> {
        loop {
            self.unit_propagate(theory)?;
            let before = self.trail.len();
            self.theory_propagate(theory)?;
            if self.trail.len() == before {
                return Ok(());
            }
        }
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
    fn solve(&mut self, theory: &mut LraTheory) -> bool {
        loop {
            loop {
                match self.propagate(theory) {
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
    fn learn_and_backtrack(&mut self, theory: &mut LraTheory, clause: Vec<Lit>) -> bool {
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
}
