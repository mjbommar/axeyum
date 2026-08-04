//! Online (incremental, backtrackable) **difference-logic** theory solver
//! (`QF_IDL` / `QF_RDL`) driven by the generic CDCL(T) spine
//! [`crate::cdclt::CdclT`].
//!
//! ## Why this module exists
//! Difference logic — every atom of the form `x - y ⋈ c` — is decidable in
//! polynomial time by *negative-cycle detection* on a constraint graph. Before
//! this module the stack had no difference-logic decision procedure at all: a
//! `QF_RDL` or `QF_IDL` query fell through to the generic linear-arithmetic
//! cores, whose Fourier–Motzkin / simplex conflict explanations are large and
//! whose lazy loops therefore grind through thousands of blocking rounds. A
//! negative cycle, by contrast, is a *minimal* explanation by construction: it
//! names exactly the constraints that close the cycle and nothing else.
//!
//! ## The representation
//! A constraint `x_u - x_v ≤ w` is the graph edge `v → u` with weight `w`
//! (read: `d[u] ≤ d[v] + w`). A conjunction of such constraints is satisfiable
//! **iff** the graph has no negative-weight cycle, and any feasible potential
//! function `π` with `π[u] - π[v] ≤ w` for every edge *is* a model.
//!
//! - **Vertices.** One per numeric symbol, plus a distinguished *zero vertex*
//!   (a freshly declared internal symbol) so single-variable bounds `x ⋈ c`
//!   become `x - zero ⋈ c`. The reconstructed model reports every value
//!   relative to the zero vertex, which is pinned to `0`, so this is an exact
//!   encoding rather than a relaxation.
//! - **Weights.** Scaled exact integers plus an infinitesimal component:
//!   `Weight { c, d }` denotes `c/scale + d·δ`. All rational bounds in the
//!   query are scaled by the least common multiple of their denominators, so
//!   weight arithmetic is exact `i128` (any overflow declines the solve — never
//!   a verdict). Lexicographic `(c, d)` comparison is exactly the standard
//!   `δ`-rational order.
//! - **Strictness.** Over the **reals** `x - y < c` is the edge weight
//!   `(c·scale, -1)`: the `δ` component makes the strict/non-strict boundary
//!   exact without any epsilon guessing. Over the **integers** it is instead
//!   *tightened* to `x - y ≤ ⌈c⌉ - 1`, which is where integer difference logic
//!   gets its extra strength (`x - y < 1 ∧ y - x < 0` is real-feasible and
//!   integer-infeasible).
//!
//! ## Incremental detection (Cotton–Maler)
//! [`DlGraph`] keeps a feasible potential `π` at all times. Adding an edge
//! `v → u` with weight `w` whose *reduced cost* `w + π[v] - π[u]` is already
//! nonnegative is free. Otherwise a Dijkstra-style propagation over reduced
//! costs (all nonnegative, because `π` is feasible) either reaches `v` with a
//! negative accumulated value — a negative cycle through the new edge — or
//! terminates with a correction that restores feasibility. The edge trail is
//! append-only and `pop` truncates it; potentials are *not* restored on `pop`
//! because dropping edges can only preserve feasibility.
//!
//! ## Soundness posture
//! - **Every theory conflict is Farkas-checked before it is reported.** A
//!   negative cycle is precisely a Farkas refutation with **unit multipliers**
//!   (a cycle enters and leaves each vertex exactly once, so every variable
//!   cancels and the constant sum is the cycle weight). [`cycle_certificate`]
//!   builds the existing [`FarkasCertificate`] — no new evidence format — and
//!   [`FarkasCertificate::verify`], the independent exact-rational re-checker,
//!   must accept it. A cycle that does not verify is **discarded** (the assert
//!   returns `Ok`): that costs completeness, never soundness, and the `sat`
//!   side is replay-gated below.
//! - **`sat` is never trusted from the search.** The candidate model is derived
//!   from the vertex potentials, lifted to `Value::Int` / `Value::Real`, and
//!   **replayed through the ground evaluator against the original assertions**.
//!   Any non-replay is [`CheckResult::Unknown`].
//! - **Anything not provably difference-shaped is refused up front.**
//!   [`scan_dl`] returns `None` — the dispatcher then falls through to the
//!   existing routes — for a coefficient other than `±1`, a product, a
//!   `div`/`mod`, a mixed `Int`/`Real` query, an uninterpreted application, a
//!   connective the skeleton encoder does not cover, or any arithmetic overflow
//!   while normalizing.
//!
//! ## Equalities live in the skeleton, not in the theory
//! A numeric `a = b` is expanded into the two difference atoms `a ≤ b` and
//! `a ≥ b` joined by a Tseitin `and` gate, so its *negation* is the ordinary
//! clause `¬(a ≤ b) ∨ ¬(a ≥ b)` that the CDCL search case-splits on — the
//! theory never has to reason about a disequality, which is not a difference
//! constraint. A **Boolean** `p = q` gets an `XNOR` gate for the same reason:
//! the skeleton encoder has no equality case, and without the gate every query
//! carrying Boolean frame axioms (the `fischer` family) would fall through.
//! - Deterministic throughout: vertices are numbered in first-seen term order,
//!   atoms in collection order, and every container is a `Vec`/`BTreeMap`.
//!   Deadlines are polled in the detection and propagation loops.

use std::cmp::{Ordering, Reverse};
use std::collections::{BTreeMap, BinaryHeap, HashMap, HashSet};
use std::time::Instant;

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

use crate::backend::{CheckResult, SolverConfig, UnknownKind, UnknownReason};
use crate::cdclt::{CdclT, Lit as CdcltLit, Outcome};
use crate::euf_egraph::{TheoryLit, TheoryProp, TheorySolver};
use crate::lra::{FarkasAtom, FarkasCertificate};
use crate::lra_online::{Encoder, Lit};
use crate::model::Model;

/// Ceiling on the least common multiple of rational-bound denominators. Above
/// it the scaled weights lose the `i128` headroom a path sum needs, so the
/// route declines rather than risk an overflow-driven miss.
const MAX_SCALE: i128 = 1 << 40;

/// Ceiling on distinct difference atoms.
const MAX_DL_ATOMS: usize = 1 << 20;

/// How many unassigned atoms one [`DlTheory::propagate`] call may probe. Each
/// probe is a bounded reduced-cost search, and propagation is a pruning layer
/// only (completeness comes from per-assert cycle detection), so truncating the
/// scan is a sound under-approximation.
const MAX_PROPAGATION_PROBES: usize = 64;

/// Ceiling on the vertex count for which propagation probing runs at all.
/// Beyond it the per-probe search would dominate the search loop.
const MAX_PROPAGATION_VERTICES: usize = 256;

/// Defense-in-depth ceiling on parent-pointer walks when extracting a cycle.
const MAX_CYCLE_WALK: usize = 1 << 20;

/// The vertex standing for the constant `0`. Every single-variable bound
/// `x ⋈ c` is expressed as `x - zero ⋈ c`, and every reconstructed value is
/// reported relative to it.
const ZERO_VERTEX: usize = 0;

// ---------------------------------------------------------------------------
// Weights
// ---------------------------------------------------------------------------

/// An edge weight `c/scale + d·δ` with `δ` an infinitesimal. Derived `Ord` is
/// lexicographic on `(c, d)`, which is exactly the `δ`-rational order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
struct Weight {
    /// The scaled rational part (`scale` is the common denominator).
    c: i128,
    /// The coefficient of the infinitesimal `δ`. Always `0` in integer mode.
    d: i64,
}

impl Weight {
    const ZERO: Self = Self { c: 0, d: 0 };

    fn checked_add(self, other: Self) -> Option<Self> {
        Some(Self {
            c: self.c.checked_add(other.c)?,
            d: self.d.checked_add(other.d)?,
        })
    }

    fn checked_sub(self, other: Self) -> Option<Self> {
        Some(Self {
            c: self.c.checked_sub(other.c)?,
            d: self.d.checked_sub(other.d)?,
        })
    }

    fn is_negative(self) -> bool {
        self < Self::ZERO
    }
}

// ---------------------------------------------------------------------------
// Atom normalization
// ---------------------------------------------------------------------------

/// One difference constraint as the theory stores it: the graph edge plus the
/// exact-rational relation the edge stands for, kept so a conflict can be
/// re-expressed as a [`FarkasAtom`] and independently re-checked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EdgeSpec {
    /// Tail vertex `v` of `x_to - x_from ≤ w`.
    from: usize,
    /// Head vertex `u` of `x_to - x_from ≤ w`.
    to: usize,
    /// The scaled weight the graph actually uses.
    w: Weight,
    /// The exact-rational bound of the relation this edge encodes.
    bound: Rational,
    /// Whether that relation is strict (`<`) rather than `≤`. Always `false` in
    /// integer mode, where strictness is folded into `bound` by tightening.
    strict: bool,
}

/// A registered theory atom: either a genuine difference constraint (with the
/// edge set for each polarity) or a constant whose truth normalization already
/// settled (`x - x ⋈ c`).
#[derive(Debug, Clone)]
enum AtomKind {
    /// Edges implied by asserting the atom true, and by asserting it false.
    Diff {
        /// Asserted **true**.
        pos: EdgeSpec,
        /// Asserted **false**.
        neg: EdgeSpec,
    },
    /// The atom's truth value is fixed by normalization alone.
    Const(bool),
}

/// A linear form over vertices: `Σ coeff·x_vertex + constant`.
#[derive(Debug, Clone, Default)]
struct LinForm {
    coeffs: BTreeMap<usize, Rational>,
    constant: Rational,
}

impl LinForm {
    fn checked_add(mut self, other: &Self) -> Option<Self> {
        for (&index, &coeff) in &other.coeffs {
            let entry = self.coeffs.entry(index).or_insert_with(Rational::zero);
            *entry = entry.checked_add(coeff)?;
        }
        self.constant = self.constant.checked_add(other.constant)?;
        Some(self)
    }

    fn checked_neg(mut self) -> Option<Self> {
        for coeff in self.coeffs.values_mut() {
            *coeff = coeff.checked_neg()?;
        }
        self.constant = self.constant.checked_neg()?;
        Some(self)
    }

    fn checked_sub(self, other: &Self) -> Option<Self> {
        self.checked_add(&other.clone().checked_neg()?)
    }

    /// Accumulates `±value` into the constant in place.
    ///
    /// The in-place accumulators exist so [`ScanState::linear`] can flatten an
    /// additive spine with an explicit worklist instead of native recursion;
    /// they carry the sign rather than building an intermediate form per node.
    fn add_constant(&mut self, value: Rational, negated: bool) -> Option<()> {
        let delta = if negated { value.checked_neg()? } else { value };
        self.constant = self.constant.checked_add(delta)?;
        Some(())
    }

    /// Accumulates `±1` into the coefficient of `index` in place.
    fn add_vertex(&mut self, index: usize, negated: bool) -> Option<()> {
        let delta = Rational::integer(if negated { -1 } else { 1 });
        let entry = self.coeffs.entry(index).or_insert_with(Rational::zero);
        *entry = entry.checked_add(delta)?;
        Some(())
    }
}

/// The numeric sort the whole query lives in. Mixed queries are refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// `QF_IDL`: strict bounds tighten to non-strict integer bounds.
    Integer,
    /// `QF_RDL`: strict bounds carry an infinitesimal `δ` component.
    Real,
}

/// The relation an atom normalizes to (`x_head - x_tail ⋈ bound`).
///
/// There is no equality variant: a numeric `=` is **expanded in the skeleton**
/// into `a ≤ b ∧ a ≥ b` by [`ScanState::expand_equality`], so its negation
/// becomes a plain propositional disjunction of two difference atoms rather
/// than a disequality the theory would have to case-split on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Rel {
    /// `<`.
    Lt,
    /// `≤`.
    Le,
}

/// A normalized atom before scaling.
#[derive(Debug, Clone, Copy)]
struct RawAtom {
    head: usize,
    tail: usize,
    bound: Rational,
    rel: Rel,
}

/// The result of the up-front conservative scan.
struct DlScan {
    mode: Mode,
    /// Distinct atom terms in collection order — the theory's atom indices and
    /// the skeleton's first variables.
    atom_terms: Vec<TermId>,
    /// Per atom index, its normalized form.
    atoms: Vec<AtomKind>,
    /// Per atom index, the **untightened** exact-rational normalization
    /// `x_head - x_tail ⋈ bound`. [`AtomKind`] carries the graph's *tightened*
    /// integer form, which is an `ℤ`-consequence of the query rather than the
    /// query's own constraint; the query-level certificate export
    /// ([`conjunctive_farkas_certificate`]) cites these verbatim relations
    /// instead, so the emitted [`FarkasAtom`]s really are the asserted ones.
    raw: Vec<RawAtom>,
    /// Vertex index → symbol; `symbols[ZERO_VERTEX]` is the fresh zero symbol.
    symbols: Vec<SymbolId>,
    /// The common denominator every [`Weight::c`] is expressed in.
    scale: i128,
    /// Numeric equality terms expanded into `(≤ atom, ≥ atom)` pairs. The
    /// skeleton gets a Tseitin `and` gate for each, so the equality's negation
    /// is an ordinary clause over two difference atoms.
    eq_gates: Vec<(TermId, usize, usize)>,
    /// Boolean equality terms `(= a b)` over `Bool` operands, in **post-order**
    /// (children before parents) so each can be encoded once its operands are.
    /// The skeleton encoder has no `Eq` case, so these carry their own `XNOR`
    /// gate rather than making the query fall through.
    bool_eq_gates: Vec<(TermId, TermId, TermId)>,
}

/// Mutable state threaded through the scan.
struct ScanState {
    mode: Mode,
    /// Numeric leaf term → vertex index.
    vertex_of: HashMap<TermId, usize>,
    symbols: Vec<SymbolId>,
    raw: Vec<RawAtom>,
    atom_terms: Vec<TermId>,
    atom_index: HashMap<TermId, usize>,
    eq_gates: Vec<(TermId, usize, usize)>,
    bool_eq_gates: Vec<(TermId, TermId, TermId)>,
}

impl ScanState {
    fn new(mode: Mode, zero: SymbolId) -> Self {
        Self {
            mode,
            vertex_of: HashMap::new(),
            symbols: vec![zero],
            raw: Vec::new(),
            atom_terms: Vec::new(),
            atom_index: HashMap::new(),
            eq_gates: Vec::new(),
            bool_eq_gates: Vec::new(),
        }
    }

    /// The vertex for a numeric leaf term, allocating on first sight. Returns
    /// `None` for anything that is not a plain declared symbol of the query's
    /// numeric sort.
    fn vertex(&mut self, arena: &TermArena, term: TermId) -> Option<usize> {
        if let Some(&index) = self.vertex_of.get(&term) {
            return Some(index);
        }
        let TermNode::Symbol(symbol) = arena.node(term) else {
            return None;
        };
        let expected = match self.mode {
            Mode::Integer => Sort::Int,
            Mode::Real => Sort::Real,
        };
        if arena.sort_of(term) != expected {
            return None;
        }
        let index = self.symbols.len();
        self.symbols.push(*symbol);
        self.vertex_of.insert(term, index);
        Some(index)
    }

    /// Parses a numeric term into a linear form over vertices, refusing every
    /// operator outside `+ - neg` and plain leaves. Deliberately narrow: a term
    /// this cannot parse makes the whole query fall through to another route.
    ///
    /// # Why this is an explicit worklist and not native recursion
    ///
    /// The `+`/`-`/`neg` spine's depth is copied verbatim from the SMT-LIB
    /// source — `(+ (+ (+ … ) 1) 2)` nests once per summand, which
    /// symbolic-execution and BMC front ends emit by the thousand. A recursive
    /// descent therefore aborted the process with a stack overflow instead of
    /// returning the first-class `unknown` the caller is owed (the same failure
    /// class as `crates/axeyum-solver/src/term_walk.rs` documents). The sign is
    /// carried on the worklist and accumulated in place, so the whole spine
    /// costs one `LinForm`.
    fn linear(&mut self, arena: &TermArena, term: TermId) -> Option<LinForm> {
        let mut acc = LinForm::default();
        // `(term, negated)`; order of accumulation is irrelevant because the
        // result is a sum, so a plain stack is enough.
        let mut work = vec![(term, false)];
        while let Some((current, negated)) = work.pop() {
            match arena.node(current) {
                TermNode::IntConst(value) => {
                    acc.add_constant(Rational::integer(*value), negated)?;
                }
                TermNode::RealConst(value) if self.mode == Mode::Real => {
                    acc.add_constant(*value, negated)?;
                }
                TermNode::Symbol(_) => {
                    let index = self.vertex(arena, current)?;
                    acc.add_vertex(index, negated)?;
                }
                TermNode::App { op, args } => match op {
                    Op::IntAdd | Op::RealAdd => {
                        for &arg in &**args {
                            work.push((arg, negated));
                        }
                    }
                    Op::IntSub | Op::RealSub if !args.is_empty() => {
                        work.push((args[0], negated));
                        for &arg in &args[1..] {
                            work.push((arg, !negated));
                        }
                    }
                    Op::IntNeg | Op::RealNeg if args.len() == 1 => {
                        work.push((args[0], !negated));
                    }
                    _ => return None,
                },
                _ => return None,
            }
        }
        Some(acc)
    }

    /// Normalizes a form `Σ coeff·x + constant ⋈ 0` into
    /// `x_head - x_tail ⋈ bound`. Returns `None` unless the difference part is
    /// exactly `x_head - x_tail` with unit coefficients (a single `±x` uses the
    /// zero vertex for the other side).
    fn difference(form: &LinForm) -> Option<(usize, usize, Rational)> {
        let one = Rational::integer(1);
        let minus_one = Rational::integer(-1);
        let mut positive: Option<usize> = None;
        let mut negative: Option<usize> = None;
        for (&index, &coeff) in &form.coeffs {
            if coeff.is_zero() {
                continue;
            }
            if coeff == one {
                if positive.replace(index).is_some() {
                    return None;
                }
            } else if coeff == minus_one {
                if negative.replace(index).is_some() {
                    return None;
                }
            } else {
                // Any coefficient other than ±1 is outside difference logic.
                return None;
            }
        }
        let head = positive.unwrap_or(ZERO_VERTEX);
        let tail = negative.unwrap_or(ZERO_VERTEX);
        // `bound` is the right-hand side of `x_head - x_tail ⋈ bound`: the
        // negated constant of `x_head - x_tail + constant ⋈ 0`.
        Some((head, tail, form.constant.checked_neg()?))
    }

    /// Registers `term` as a difference atom, returning its index. Returns
    /// `None` for anything not provably difference-shaped.
    fn atom(&mut self, arena: &TermArena, term: TermId) -> Option<usize> {
        if let Some(&index) = self.atom_index.get(&term) {
            return Some(index);
        }
        let TermNode::App { op, args } = arena.node(term) else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let op = *op;
        let (left, right) = (args[0], args[1]);
        // Orient to `lo - hi ⋈ 0` with `⋈ ∈ {<, ≤}`. Equality never reaches
        // here: `collect` routes it to `expand_equality` first.
        let (rel, lo, hi) = match op {
            Op::IntLt | Op::RealLt => (Rel::Lt, left, right),
            Op::IntLe | Op::RealLe => (Rel::Le, left, right),
            Op::IntGt | Op::RealGt => (Rel::Lt, right, left),
            Op::IntGe | Op::RealGe => (Rel::Le, right, left),
            _ => return None,
        };
        let lf = self.linear(arena, lo)?;
        let rf = self.linear(arena, hi)?;
        let diff = lf.checked_sub(&rf)?;
        let (head, tail, bound) = Self::difference(&diff)?;
        if self.raw.len() >= MAX_DL_ATOMS {
            return None;
        }
        let index = self.raw.len();
        self.raw.push(RawAtom {
            head,
            tail,
            bound,
            rel,
        });
        self.atom_terms.push(term);
        self.atom_index.insert(term, index);
        Some(index)
    }

    /// Expands a numeric equality `a = b` into the two difference atoms
    /// `a ≤ b` and `a ≥ b`, registering both and recording the pair so the
    /// skeleton can carry a Tseitin `and` gate for the equality term.
    ///
    /// This is what makes equality *supported* rather than refused. The theory
    /// itself still only ever asserts difference constraints: the equality's
    /// negation becomes the clause `¬(a ≤ b) ∨ ¬(a ≥ b)`, a plain
    /// propositional disjunction the CDCL search case-splits on, instead of a
    /// disequality the theory would have to split on itself. Both new terms are
    /// interned in the arena, so a query that already mentions `a ≤ b`
    /// structurally shares that atom.
    ///
    /// `collect`'s `seen` set already guarantees one call per distinct term, so
    /// this does no de-duplication scan of its own (which would be quadratic on
    /// a query with thousands of equalities).
    fn expand_equality(&mut self, arena: &mut TermArena, term: TermId) -> bool {
        let TermNode::App { args, .. } = arena.node(term) else {
            return false;
        };
        if args.len() != 2 {
            return false;
        }
        let (left, right) = (args[0], args[1]);
        let (le, ge) = match self.mode {
            Mode::Integer => (arena.int_le(left, right), arena.int_ge(left, right)),
            Mode::Real => (arena.real_le(left, right), arena.real_ge(left, right)),
        };
        let (Ok(le), Ok(ge)) = (le, ge) else {
            return false;
        };
        let (Some(le_index), Some(ge_index)) = (self.atom(arena, le), self.atom(arena, ge)) else {
            return false;
        };
        self.eq_gates.push((term, le_index, ge_index));
        true
    }
}

/// Whether `term` is a relational application over a **numeric** sort — the
/// atoms this theory abstracts (a numeric `Op::Eq` included, which [`collect`]
/// routes to [`ScanState::expand_equality`]). A **Boolean** equality is not
/// numeric and is handled as skeleton structure with its own `XNOR` gate.
fn is_numeric_relational(arena: &TermArena, term: TermId) -> bool {
    let TermNode::App { op, args } = arena.node(term) else {
        return false;
    };
    if !matches!(
        op,
        Op::IntLt
            | Op::IntLe
            | Op::IntGt
            | Op::IntGe
            | Op::RealLt
            | Op::RealLe
            | Op::RealGt
            | Op::RealGe
            | Op::Eq
    ) {
        return false;
    }
    args.first()
        .is_some_and(|&arg| matches!(arena.sort_of(arg), Sort::Int | Sort::Real))
}

/// The propositional connectives the skeleton encoder covers. Anything else
/// above the atoms makes the query fall through.
fn is_skeleton_op(op: Op) -> bool {
    matches!(
        op,
        Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolImplies | Op::BoolXor | Op::Ite
    )
}

/// Walks the assertion DAG registering every numeric relational atom. Returns
/// `false` as soon as one is not difference-shaped, or the structure above the
/// atoms leaves the propositional skeleton — the conservative refusal that
/// leaves the query to the established routes.
fn collect(
    arena: &mut TermArena,
    term: TermId,
    state: &mut ScanState,
    seen: &mut HashSet<TermId>,
) -> bool {
    if !seen.insert(term) {
        return true;
    }
    if is_numeric_relational(arena, term) {
        return if matches!(arena.node(term), TermNode::App { op: Op::Eq, .. }) {
            state.expand_equality(arena, term)
        } else {
            state.atom(arena, term).is_some()
        };
    }
    // A Boolean equality is pure skeleton: descend both operands first, then
    // record the gate, so `bool_eq_gates` is in post-order and each gate can be
    // encoded once its operands already have skeleton variables.
    if let TermNode::App { op: Op::Eq, args } = arena.node(term)
        && args.len() == 2
        && arena.sort_of(args[0]) == Sort::Bool
    {
        let (lhs, rhs) = (args[0], args[1]);
        if !collect(arena, lhs, state, seen) || !collect(arena, rhs, state, seen) {
            return false;
        }
        state.bool_eq_gates.push((term, lhs, rhs));
        return true;
    }
    let TermNode::App { op, args } = arena.node(term) else {
        return matches!(
            arena.node(term),
            TermNode::Symbol(_) | TermNode::BoolConst(_)
        ) && arena.sort_of(term) == Sort::Bool;
    };
    if !is_skeleton_op(*op) || arena.sort_of(term) != Sort::Bool {
        return false;
    }
    let args = args.clone();
    for &arg in &*args {
        if !collect(arena, arg, state, seen) {
            return false;
        }
    }
    true
}

/// Scales a rational bound into the graph's integer units.
fn scaled(bound: Rational, scale: i128) -> Option<i128> {
    let numerator = bound.numerator().checked_mul(scale)?;
    let denominator = bound.denominator();
    if denominator == 0 || numerator % denominator != 0 {
        return None;
    }
    Some(numerator / denominator)
}

/// `⌊bound⌋` as an exact integer.
fn floor_of(bound: Rational) -> Option<i128> {
    let (n, d) = (bound.numerator(), bound.denominator());
    if d <= 0 {
        return None;
    }
    let q = n.checked_div(d)?;
    let r = n.checked_rem(d)?;
    if r < 0 { q.checked_sub(1) } else { Some(q) }
}

/// `⌈bound⌉` as an exact integer.
fn ceil_of(bound: Rational) -> Option<i128> {
    let (n, d) = (bound.numerator(), bound.denominator());
    if d <= 0 {
        return None;
    }
    let q = n.checked_div(d)?;
    let r = n.checked_rem(d)?;
    if r > 0 { q.checked_add(1) } else { Some(q) }
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn lcm(a: i128, b: i128) -> Option<i128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let g = gcd(a, b);
    (a / g).checked_mul(b)
}

/// Builds the edge for `x_head - x_tail ⋈ bound` (`⋈` strict or not) in `mode`.
///
/// Integer mode **tightens**: `≤ c` becomes `≤ ⌊c⌋` and `< c` becomes
/// `≤ ⌈c⌉ - 1`. Both are exact over the integers, and the certificate cites the
/// tightened non-strict relation — which is what makes the negative cycle a
/// genuine Farkas refutation of the *edge system* the graph actually holds.
fn edge_for(
    mode: Mode,
    head: usize,
    tail: usize,
    bound: Rational,
    strict: bool,
    scale: i128,
) -> Option<EdgeSpec> {
    match mode {
        Mode::Integer => {
            let tightened = if strict {
                ceil_of(bound)?.checked_sub(1)?
            } else {
                floor_of(bound)?
            };
            Some(EdgeSpec {
                from: tail,
                to: head,
                w: Weight { c: tightened, d: 0 },
                bound: Rational::checked_new(tightened, 1)?,
                strict: false,
            })
        }
        Mode::Real => Some(EdgeSpec {
            from: tail,
            to: head,
            w: Weight {
                c: scaled(bound, scale)?,
                d: if strict { -1 } else { 0 },
            },
            bound,
            strict,
        }),
    }
}

/// A name in the internal namespace that no symbol currently occupies.
fn fresh_zero_name(arena: &TermArena) -> String {
    let mut suffix = 0_u32;
    loop {
        let candidate = format!("!dl_zero_{suffix}");
        if arena.find_internal_symbol(&candidate).is_none() {
            return candidate;
        }
        suffix += 1;
    }
}

/// The conservative front gate. Returns the normalized problem, or `None` when
/// the query is not provably pure difference logic.
fn scan_dl(arena: &mut TermArena, assertions: &[TermId]) -> Option<DlScan> {
    // Decide the mode from the declared sorts alone, and refuse mixed queries
    // and every non-arithmetic theory.
    let mut has_int = false;
    let mut has_real = false;
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut visited: HashSet<TermId> = HashSet::new();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match arena.sort_of(term) {
            Sort::Int => has_int = true,
            Sort::Real => has_real = true,
            Sort::Bool => {}
            _ => return None,
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Apply(_)) {
                return None;
            }
            for &arg in &**args {
                stack.push(arg);
            }
        }
    }
    let mode = match (has_int, has_real) {
        (true, false) => Mode::Integer,
        (false, true) => Mode::Real,
        // No numeric sort is pure SAT (another route's job); both is outside
        // this fragment.
        _ => return None,
    };

    let zero_sort = match mode {
        Mode::Integer => Sort::Int,
        Mode::Real => Sort::Real,
    };
    let zero = arena
        .declare_internal(&fresh_zero_name(arena), zero_sort)
        .ok()?;

    let mut state = ScanState::new(mode, zero);
    let mut seen = HashSet::new();
    for &assertion in assertions {
        if arena.sort_of(assertion) != Sort::Bool {
            return None;
        }
        if !collect(arena, assertion, &mut state, &mut seen) {
            return None;
        }
    }
    if state.raw.is_empty() {
        return None;
    }

    // The common denominator for real mode; integer mode tightens to whole
    // numbers and needs no scaling.
    let scale = match mode {
        Mode::Integer => 1,
        Mode::Real => {
            let mut acc: i128 = 1;
            for raw in &state.raw {
                acc = lcm(acc, raw.bound.denominator())?;
                if acc > MAX_SCALE || acc <= 0 {
                    return None;
                }
            }
            acc
        }
    };

    let mut atoms = Vec::with_capacity(state.raw.len());
    for raw in &state.raw {
        let RawAtom {
            head,
            tail,
            bound,
            rel,
        } = *raw;
        if head == tail {
            // `x - x ⋈ c`: the relation is a constant, and so is its negation.
            let cmp = bound.checked_cmp(&Rational::zero())?;
            let value = match rel {
                Rel::Lt => cmp == Ordering::Greater,
                Rel::Le => cmp != Ordering::Less,
            };
            atoms.push(AtomKind::Const(value));
            continue;
        }
        let strict = rel == Rel::Lt;
        // Asserted true: `x_head - x_tail ⋈ bound`.
        let pos = edge_for(mode, head, tail, bound, strict, scale)?;
        // Asserted false: `¬(a - b ≤ c)` is `b - a < -c`, and
        // `¬(a - b < c)` is `b - a ≤ -c`.
        let neg = edge_for(mode, tail, head, bound.checked_neg()?, !strict, scale)?;
        atoms.push(AtomKind::Diff { pos, neg });
    }

    Some(DlScan {
        mode,
        atom_terms: state.atom_terms,
        atoms,
        raw: state.raw,
        symbols: state.symbols,
        scale,
        eq_gates: state.eq_gates,
        bool_eq_gates: state.bool_eq_gates,
    })
}

// ---------------------------------------------------------------------------
// The constraint graph
// ---------------------------------------------------------------------------

/// An edge currently on the trail.
#[derive(Debug, Clone, Copy)]
struct ActiveEdge {
    spec: EdgeSpec,
    /// The theory literal that put it there.
    lit: TheoryLit,
}

/// One step of an extracted cycle: the constraint plus, for a trail edge, its
/// index (so its literal is an `O(1)` lookup rather than a scan).
#[derive(Debug, Clone, Copy)]
struct CycleStep {
    spec: EdgeSpec,
    /// `None` for the edge being added (which is not yet on the trail).
    index: Option<usize>,
}

/// The backtrackable difference-constraint graph with Cotton–Maler incremental
/// negative-cycle detection over a maintained feasible potential.
struct DlGraph {
    /// Feasible potential: `π[to] - π[from] ≤ w` for every active edge.
    pi: Vec<Weight>,
    /// Append-only edge trail; `pop` truncates it.
    edges: Vec<ActiveEdge>,
    /// Per vertex, indices of active edges leaving it. Suffix-truncatable
    /// because edge indices only ever increase.
    out: Vec<Vec<usize>>,
}

/// The outcome of adding one edge.
enum AddOutcome {
    /// Accepted (or already implied); `π` is feasible.
    Ok,
    /// A negative cycle closed through the new edge, which was **not**
    /// committed. Steps are in cycle order with the new edge last.
    Cycle(Vec<CycleStep>),
    /// Exact arithmetic overflowed; the caller must decline, never decide.
    Overflow,
}

/// The outcome of one `γ` propagation. The `γ` values, parent pointers, and
/// touched list all live in the caller's [`Scratch`], so a detection run
/// allocates nothing.
enum GammaOutcome {
    /// Feasibility can be restored by applying `scratch.gamma` to `π`.
    Feasible,
    /// A negative cycle exists; `scratch.parent` describes it.
    Cycle,
    Overflow,
    Budget,
}

/// Reusable working memory for one `γ` propagation.
///
/// Detection runs on every theory assert that is not already implied, so a
/// fresh `vec![_; vertices]` pair per call would make each assert `O(|V|)` in
/// allocation alone — the dominant cost on the large planning and job-shop
/// families. Instead the buffers are allocated once and reset by walking only
/// the vertices the previous run actually touched.
struct Scratch {
    gamma: Vec<Weight>,
    parent: Vec<Option<usize>>,
    touched: Vec<usize>,
    heap: BinaryHeap<Reverse<(Weight, usize)>>,
}

impl Scratch {
    fn new(vertices: usize) -> Self {
        Self {
            gamma: vec![Weight::ZERO; vertices],
            parent: vec![None; vertices],
            touched: Vec::new(),
            heap: BinaryHeap::new(),
        }
    }

    /// Clears exactly the entries the previous run wrote.
    fn reset(&mut self) {
        for &vertex in &self.touched {
            self.gamma[vertex] = Weight::ZERO;
            self.parent[vertex] = None;
        }
        self.touched.clear();
        self.heap.clear();
    }
}

impl DlGraph {
    fn new(vertices: usize) -> Self {
        Self {
            pi: vec![Weight::ZERO; vertices],
            edges: Vec::new(),
            out: vec![Vec::new(); vertices],
        }
    }

    fn trail_len(&self) -> usize {
        self.edges.len()
    }

    /// Drops every edge added after `len`. Potentials are deliberately left
    /// alone: a feasible potential for a superset of edges is feasible for any
    /// subset.
    fn truncate(&mut self, len: usize) {
        while self.edges.len() > len {
            let edge = self.edges.pop().expect("non-empty by the loop guard");
            // Edge indices are appended in increasing order, so the edge being
            // dropped is the last one recorded for its tail.
            let popped = self.out[edge.spec.from].pop();
            debug_assert_eq!(popped, Some(self.edges.len()));
        }
    }

    /// Reduced cost of `from → to` at weight `w`; nonnegative for every active
    /// edge because `π` is feasible.
    fn reduced(&self, from: usize, to: usize, w: Weight) -> Option<Weight> {
        w.checked_add(self.pi[from])?.checked_sub(self.pi[to])
    }

    /// Adds `spec` under `lit`, detecting a negative cycle.
    fn add(
        &mut self,
        spec: EdgeSpec,
        lit: TheoryLit,
        deadline: Option<Instant>,
        scratch: &mut Scratch,
    ) -> AddOutcome {
        if spec.from == spec.to {
            // A self-loop is a length-one cycle: infeasible exactly when its
            // weight is negative.
            return if spec.w.is_negative() {
                AddOutcome::Cycle(vec![CycleStep { spec, index: None }])
            } else {
                AddOutcome::Ok
            };
        }
        let Some(rc) = self.reduced(spec.from, spec.to, spec.w) else {
            return AddOutcome::Overflow;
        };
        if !rc.is_negative() {
            self.commit(spec, lit);
            return AddOutcome::Ok;
        }
        match self.propagate_gamma(spec, rc, deadline, scratch) {
            GammaOutcome::Feasible => {
                for &vertex in &scratch.touched {
                    let Some(updated) = self.pi[vertex].checked_add(scratch.gamma[vertex]) else {
                        return AddOutcome::Overflow;
                    };
                    self.pi[vertex] = updated;
                }
                self.commit(spec, lit);
                AddOutcome::Ok
            }
            GammaOutcome::Cycle => match self.extract_cycle(&scratch.parent, spec) {
                Some(steps) => AddOutcome::Cycle(steps),
                // Cycle reconstruction failed (unreachable in principle). Treat
                // it as "no conflict found": costs completeness, never
                // soundness, since `sat` is replay-gated.
                None => AddOutcome::Ok,
            },
            GammaOutcome::Overflow => AddOutcome::Overflow,
            // Out of budget mid-detection: report no conflict. The driver's own
            // deadline ends the search as `Unknown`.
            GammaOutcome::Budget => AddOutcome::Ok,
        }
    }

    fn commit(&mut self, spec: EdgeSpec, lit: TheoryLit) {
        let index = self.edges.len();
        self.edges.push(ActiveEdge { spec, lit });
        self.out[spec.from].push(index);
    }

    /// The Dijkstra-style propagation over reduced costs. Only negative `γ`
    /// values are ever recorded, so the work is proportional to the part of the
    /// graph the new edge actually perturbs.
    fn propagate_gamma(
        &self,
        spec: EdgeSpec,
        rc: Weight,
        deadline: Option<Instant>,
        scratch: &mut Scratch,
    ) -> GammaOutcome {
        scratch.reset();
        scratch.gamma[spec.to] = rc;
        scratch.touched.push(spec.to);
        scratch.heap.push(Reverse((rc, spec.to)));
        let mut steps: usize = 0;
        while let Some(Reverse((value, vertex))) = scratch.heap.pop() {
            steps += 1;
            if steps.is_multiple_of(1024) && past_deadline(deadline) {
                return GammaOutcome::Budget;
            }
            if value != scratch.gamma[vertex] {
                continue; // stale heap entry
            }
            if !value.is_negative() {
                break; // every remaining entry is nonnegative: nothing left to fix
            }
            if vertex == spec.from {
                return GammaOutcome::Cycle;
            }
            for &edge_index in &self.out[vertex] {
                let edge = self.edges[edge_index].spec;
                let Some(cost) = self.reduced(edge.from, edge.to, edge.w) else {
                    return GammaOutcome::Overflow;
                };
                let Some(candidate) = value.checked_add(cost) else {
                    return GammaOutcome::Overflow;
                };
                if candidate < scratch.gamma[edge.to] {
                    if scratch.gamma[edge.to] == Weight::ZERO {
                        scratch.touched.push(edge.to);
                    }
                    scratch.gamma[edge.to] = candidate;
                    scratch.parent[edge.to] = Some(edge_index);
                    scratch.heap.push(Reverse((candidate, edge.to)));
                }
            }
        }
        GammaOutcome::Feasible
    }

    /// Walks parent pointers from the new edge's tail back to its head,
    /// producing the cycle with the new edge last. Returns `None` if the walk
    /// does not close (defense in depth; the caller then reports no conflict).
    fn extract_cycle(&self, parent: &[Option<usize>], spec: EdgeSpec) -> Option<Vec<CycleStep>> {
        let mut path: Vec<CycleStep> = Vec::new();
        let mut vertex = spec.from;
        let mut guard = 0_usize;
        while vertex != spec.to {
            guard += 1;
            if guard > MAX_CYCLE_WALK {
                return None;
            }
            let index = parent[vertex]?;
            let edge = self.edges[index].spec;
            path.push(CycleStep {
                spec: edge,
                index: Some(index),
            });
            vertex = edge.from;
        }
        path.reverse();
        path.push(CycleStep { spec, index: None });
        Some(path)
    }
}

fn past_deadline(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}

// ---------------------------------------------------------------------------
// Farkas certificates from negative cycles
// ---------------------------------------------------------------------------

/// Turns a negative cycle into the existing [`FarkasCertificate`] with **unit
/// multipliers**.
///
/// Each cycle edge `x_to - x_from ≤ bound` is the atom
/// `x_to - x_from - bound ≤ 0`. Summing with multiplier `1` cancels every
/// variable (a cycle enters and leaves each vertex exactly once) and leaves the
/// constant `-Σ bound`, so the derived relation is false exactly when the cycle
/// weight is negative — the detection condition, re-derived independently.
///
/// `origins[i]` is the position of edge `i` in the cycle: a theory conflict
/// refutes a set of theory literals, not top-level assertions, so a per-cycle
/// position is the meaningful provenance here.
fn cycle_certificate(steps: &[CycleStep], symbols: &[SymbolId]) -> Option<FarkasCertificate> {
    let mut atoms = Vec::with_capacity(steps.len());
    for step in steps {
        let edge = step.spec;
        let mut coeffs: Vec<(usize, Rational)> = Vec::new();
        if edge.to != edge.from {
            coeffs.push((edge.to, Rational::integer(1)));
            coeffs.push((edge.from, Rational::integer(-1)));
            coeffs.sort_by_key(|(index, _)| *index);
        }
        atoms.push(FarkasAtom {
            coeffs,
            constant: edge.bound.checked_neg()?,
            strict: edge.strict,
        });
    }
    Some(FarkasCertificate {
        multipliers: vec![Rational::integer(1); atoms.len()],
        origins: (0..atoms.len()).collect(),
        atoms,
        vars: symbols.to_vec(),
    })
}

// ---------------------------------------------------------------------------
// Query-level certificate export (conjunctive fragment)
// ---------------------------------------------------------------------------

/// One top-level conjunct of a purely conjunctive difference-logic query: the
/// atom it asserts, the polarity it asserts it at, and the index of the
/// assertion it came from.
#[derive(Debug, Clone, Copy)]
struct Unit {
    atom: usize,
    value: bool,
    /// Index into the caller's `assertions` slice — the [`FarkasCertificate`]
    /// `origins` contract.
    origin: usize,
}

/// The **verbatim** [`FarkasAtom`] a unit asserts, in the exact rationals of the
/// query (never the integer-tightened form the graph searches over).
///
/// - Asserted **true**: `x_head - x_tail ⋈ bound`.
/// - Asserted **false**: `¬(a - b ≤ c)` is `b - a < -c`, and `¬(a - b < c)` is
///   `b - a ≤ -c`.
///
/// A `FarkasAtom` is normalized to `Σ coeff·x + constant ⋈ 0`, so the constant is
/// the negated bound. The zero vertex is **dropped** rather than emitted as a
/// variable: a single-variable bound `x ⋈ c` is the query's own constraint, not
/// `x - z ⋈ c` for an internal `z`. Dropping it cannot break the cancellation a
/// Farkas check needs — an extracted cycle is simple, so it passes through the
/// zero vertex at most once and that vertex's `+1`/`-1` pair vanishes with or
/// without the column.
fn exact_farkas_atom(raw: RawAtom, value: bool) -> Option<FarkasAtom> {
    let (head, tail, bound, strict) = if value {
        (raw.head, raw.tail, raw.bound, raw.rel == Rel::Lt)
    } else {
        (
            raw.tail,
            raw.head,
            raw.bound.checked_neg()?,
            raw.rel == Rel::Le,
        )
    };
    let mut coeffs: Vec<(usize, Rational)> = Vec::with_capacity(2);
    if head != ZERO_VERTEX {
        coeffs.push((head, Rational::integer(1)));
    }
    if tail != ZERO_VERTEX {
        coeffs.push((tail, Rational::integer(-1)));
    }
    coeffs.sort_by_key(|(index, _)| *index);
    Some(FarkasAtom {
        coeffs,
        constant: bound.checked_neg()?,
        strict,
    })
}

/// Flattens `term` into the units of a purely **conjunctive** difference-logic
/// query, returning `false` as soon as it meets Boolean structure that is not a
/// conjunction of literals.
///
/// `positive` is the polarity the term is asserted at, so `not` is handled by
/// flipping it rather than by rewriting. A numeric equality is a conjunction of
/// its two expanded bounds when asserted positively, and a *disjunction* when
/// asserted negatively — the negative case declines.
fn collect_units(
    arena: &TermArena,
    term: TermId,
    positive: bool,
    origin: usize,
    atom_index: &HashMap<TermId, usize>,
    eq_pairs: &HashMap<TermId, (usize, usize)>,
    units: &mut Vec<Unit>,
) -> bool {
    if let Some(&(le, ge)) = eq_pairs.get(&term) {
        if !positive {
            return false; // `a ≠ b` is a disjunction, not a conjunctive unit
        }
        units.push(Unit {
            atom: le,
            value: true,
            origin,
        });
        units.push(Unit {
            atom: ge,
            value: true,
            origin,
        });
        return true;
    }
    if let Some(&atom) = atom_index.get(&term) {
        units.push(Unit {
            atom,
            value: positive,
            origin,
        });
        return true;
    }
    let (op, args) = match arena.node(term) {
        TermNode::BoolConst(value) => return *value == positive,
        TermNode::App { op, args } => (*op, args.clone()),
        _ => return false,
    };
    // `and` under a positive polarity (and `or` under a negative one, by De
    // Morgan) keeps the query conjunctive; every other connective does not.
    let children_positive = match op {
        Op::BoolNot if args.len() == 1 => {
            return collect_units(
                arena, args[0], !positive, origin, atom_index, eq_pairs, units,
            );
        }
        Op::BoolAnd if positive => true,
        Op::BoolOr if !positive => false,
        _ => return false,
    };
    for &arg in &*args {
        if !collect_units(
            arena,
            arg,
            children_positive,
            origin,
            atom_index,
            eq_pairs,
            units,
        ) {
            return false;
        }
    }
    true
}

/// Exports a **conjunctive** difference-logic refutation as a query-level
/// [`FarkasCertificate`] — the same shape `QF_LRA` already emits, never a new
/// evidence format.
///
/// Returns `Some` only when all of the following hold, and `None` (a clean
/// decline, leaving every other evidence route byte-identical) otherwise:
///
/// 1. [`scan_dl`] accepts the query as pure difference logic;
/// 2. every assertion flattens into a **conjunction of difference literals** —
///    no disjunction, implication, `xor`, `ite`, Boolean variable, or Boolean
///    equality survives (see [`collect_units`]);
/// 3. asserting those units in order closes a negative cycle; and
/// 4. the cycle, re-expressed over the **verbatim** query relations, passes the
///    independent [`FarkasCertificate::verify`].
///
/// # Why conjunctive only
///
/// With Boolean structure the refutation is a *resolution* over many theory
/// lemmas, not one Farkas combination; `FarkasCertificate` cannot express that,
/// and inventing a format for it is a separate decision. Scoping to the
/// conjunctive case is what is soundly achievable in this shape today.
///
/// # Why step 4 is the honest gate, not a formality
///
/// In integer mode the graph searches over *tightened* edges (`< c` becomes
/// `≤ ⌈c⌉ - 1`), which are `ℤ`-consequences of the query rather than the query's
/// own constraints. The certificate therefore cites [`DlScan::raw`] — the
/// untightened relations — so a refutation that genuinely *needs* the integer
/// tightening does not verify and is declined rather than misdescribed. The
/// certificate that comes back is always a real-arithmetic refutation of the
/// literal asserted constraints.
pub(crate) fn conjunctive_farkas_certificate(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<FarkasCertificate> {
    let scan = scan_dl(arena, assertions)?;
    let atom_index: HashMap<TermId, usize> = scan
        .atom_terms
        .iter()
        .enumerate()
        .map(|(index, &term)| (term, index))
        .collect();
    let eq_pairs: HashMap<TermId, (usize, usize)> = scan
        .eq_gates
        .iter()
        .map(|&(term, le, ge)| (term, (le, ge)))
        .collect();

    let mut units: Vec<Unit> = Vec::new();
    for (origin, &assertion) in assertions.iter().enumerate() {
        if !collect_units(
            arena,
            assertion,
            true,
            origin,
            &atom_index,
            &eq_pairs,
            &mut units,
        ) {
            return None;
        }
    }

    let mut graph = DlGraph::new(scan.symbols.len());
    let mut scratch = Scratch::new(scan.symbols.len());
    for (position, unit) in units.iter().enumerate() {
        let spec = match &scan.atoms[unit.atom] {
            // A conjunct fixed false by normalization alone (`x - x < -1`) is an
            // `unsat` with nothing linear to certify: decline to the bare route.
            AtomKind::Const(fixed) => {
                if *fixed == unit.value {
                    continue;
                }
                return None;
            }
            AtomKind::Diff { pos, neg } => {
                if unit.value {
                    *pos
                } else {
                    *neg
                }
            }
        };
        // The trail literal carries the unit's **position**, not a theory atom
        // index: that is what recovers both the verbatim relation and the origin
        // assertion when a cycle closes. `value` is unused on this path.
        let lit = TheoryLit {
            atom: position,
            value: true,
        };
        match graph.add(spec, lit, None, &mut scratch) {
            AddOutcome::Ok => {}
            // Exact arithmetic ran out of headroom: never a verdict.
            AddOutcome::Overflow => return None,
            AddOutcome::Cycle(steps) => {
                let mut atoms = Vec::with_capacity(steps.len());
                let mut origins = Vec::with_capacity(steps.len());
                for step in &steps {
                    let at = step
                        .index
                        .map_or(position, |index| graph.edges[index].lit.atom);
                    let unit = *units.get(at)?;
                    atoms.push(exact_farkas_atom(*scan.raw.get(unit.atom)?, unit.value)?);
                    origins.push(unit.origin);
                }
                let certificate = FarkasCertificate {
                    multipliers: vec![Rational::integer(1); atoms.len()],
                    origins,
                    atoms,
                    vars: scan.symbols.clone(),
                };
                return certificate.verify().then_some(certificate);
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// The theory solver
// ---------------------------------------------------------------------------

/// The online difference-logic [`TheorySolver`].
struct DlTheory {
    atoms: Vec<AtomKind>,
    graph: DlGraph,
    symbols: Vec<SymbolId>,
    assigned: Vec<Option<bool>>,
    assigned_log: Vec<usize>,
    scopes: Vec<(usize, usize)>,
    deadline: Option<Instant>,
    /// Reusable detection working memory (see [`Scratch`]).
    scratch: Scratch,
}

impl DlTheory {
    fn new(scan: &DlScan, deadline: Option<Instant>) -> Self {
        let n = scan.atoms.len();
        Self {
            atoms: scan.atoms.clone(),
            graph: DlGraph::new(scan.symbols.len()),
            symbols: scan.symbols.clone(),
            assigned: vec![None; n],
            assigned_log: Vec::new(),
            scopes: Vec::new(),
            deadline,
            scratch: Scratch::new(scan.symbols.len()),
        }
    }

    /// The literals a cycle's steps stand for, in cycle order and de-duplicated.
    /// `trigger` labels the one step that is not yet on the trail.
    fn cycle_literals(&self, steps: &[CycleStep], trigger: TheoryLit) -> Vec<TheoryLit> {
        let mut lits: Vec<TheoryLit> = Vec::with_capacity(steps.len());
        for step in steps {
            let lit = step
                .index
                .map_or(trigger, |index| self.graph.edges[index].lit);
            if !lits
                .iter()
                .any(|l| l.atom == lit.atom && l.value == lit.value)
            {
                lits.push(lit);
            }
        }
        lits
    }

    /// Farkas-checks a candidate cycle: the conflict is reported only if the
    /// independent exact-rational re-checker accepts it.
    ///
    /// The certificate is built with an **empty** `vars` map. That map is a
    /// dense-index-to-`SymbolId` labelling for downstream consumers;
    /// [`FarkasCertificate::verify`] is a pure function of `atoms` and
    /// `multipliers` over the dense indices and never reads it. Cloning the
    /// full symbol table on every conflict would make each refutation
    /// `O(|V|)`, which on these corpora is the same order as the detection
    /// itself. Tests build the fully-labelled certificate.
    fn verified(steps: &[CycleStep]) -> bool {
        cycle_certificate(steps, &[]).is_some_and(|c| c.verify())
    }

    /// Whether asserting `atom` at `value` would close a negative cycle,
    /// without mutating any state. Used by [`Self::propagate`].
    fn would_conflict(&self, atom: usize, value: bool) -> Option<Vec<TheoryLit>> {
        let lit = TheoryLit { atom, value };
        match &self.atoms[atom] {
            AtomKind::Const(fixed) => (*fixed != value).then(|| vec![lit]),
            AtomKind::Diff { pos, neg } => {
                let spec = if value { *pos } else { *neg };
                if spec.from == spec.to {
                    return (spec.w.is_negative()
                        && Self::verified(&[CycleStep { spec, index: None }]))
                    .then(|| vec![lit]);
                }
                let rc = self.graph.reduced(spec.from, spec.to, spec.w)?;
                if !rc.is_negative() {
                    return None;
                }
                // `propagate` runs behind `&self`, so a probe cannot borrow the
                // theory's scratch mutably; it allocates its own. Probing is
                // capped by `MAX_PROPAGATION_PROBES` and only enabled on small
                // graphs, so this stays off the hot path.
                let mut scratch = Scratch::new(self.graph.pi.len());
                let GammaOutcome::Cycle =
                    self.graph
                        .propagate_gamma(spec, rc, self.deadline, &mut scratch)
                else {
                    return None;
                };
                let steps = self.graph.extract_cycle(&scratch.parent, spec)?;
                if !Self::verified(&steps) {
                    return None;
                }
                let mut lits = self.cycle_literals(&steps, lit);
                if !lits.iter().any(|l| l.atom == atom && l.value == value) {
                    lits.push(lit);
                }
                Some(lits)
            }
        }
    }
}

impl TheorySolver for DlTheory {
    fn assert(&mut self, atom: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        if self.assigned[atom].is_none() {
            self.assigned[atom] = Some(value);
            self.assigned_log.push(atom);
        }
        let lit = TheoryLit { atom, value };
        let spec = match &self.atoms[atom] {
            AtomKind::Const(fixed) => {
                if *fixed == value {
                    return Ok(());
                }
                // A normalization-settled atom asserted against its truth value.
                // The unit lemma `¬lit` is valid by construction and trivially
                // carries the trigger literal the driver requires.
                return Err(vec![lit]);
            }
            AtomKind::Diff { pos, neg } => {
                if value {
                    *pos
                } else {
                    *neg
                }
            }
        };
        match self.graph.add(spec, lit, self.deadline, &mut self.scratch) {
            // Overflow: report no conflict. Missing a constraint can only cost
            // completeness; a `sat` built on this graph is caught by replay.
            AddOutcome::Ok | AddOutcome::Overflow => Ok(()),
            AddOutcome::Cycle(steps) => {
                if !Self::verified(&steps) {
                    // The independent Farkas re-check rejected the cycle: report
                    // no conflict rather than a lemma we cannot justify.
                    return Ok(());
                }
                let mut lits = self.cycle_literals(&steps, lit);
                // The driver's trigger-literal precondition: the conflict must
                // name the literal just asserted (it sits at the current
                // decision level). The cycle closes *through* the new edge, so
                // this holds by construction; the guard makes it unconditional.
                if !lits.iter().any(|l| l.atom == atom && l.value == value) {
                    lits.push(lit);
                }
                Err(lits)
            }
        }
    }

    fn push(&mut self) {
        self.scopes
            .push((self.graph.trail_len(), self.assigned_log.len()));
    }

    fn pop(&mut self) {
        let Some((edges, log)) = self.scopes.pop() else {
            return;
        };
        self.graph.truncate(edges);
        while self.assigned_log.len() > log {
            let atom = self.assigned_log.pop().expect("non-empty by the guard");
            self.assigned[atom] = None;
        }
    }

    fn propagate(&self) -> Vec<TheoryProp> {
        // Sound under-approximation: an unassigned atom is entailed when
        // asserting its *negation* would close a negative cycle, and that
        // cycle's other literals are the explanation. The scan is capped and
        // deadline-bounded, so a large graph simply propagates nothing.
        if self.symbols.len() > MAX_PROPAGATION_VERTICES || past_deadline(self.deadline) {
            return Vec::new();
        }
        let mut out = Vec::new();
        let mut probes = 0_usize;
        for atom in 0..self.atoms.len() {
            if probes >= MAX_PROPAGATION_PROBES || past_deadline(self.deadline) {
                break;
            }
            if self.assigned[atom].is_some() {
                continue;
            }
            probes += 1;
            for value in [true, false] {
                if let Some(reason) = self.would_conflict(atom, !value) {
                    let filtered: Vec<TheoryLit> =
                        reason.into_iter().filter(|l| l.atom != atom).collect();
                    out.push(TheoryProp {
                        lit: TheoryLit { atom, value },
                        reason: filtered,
                    });
                    break;
                }
            }
        }
        out
    }
}

// ---------------------------------------------------------------------------
// Model reconstruction
// ---------------------------------------------------------------------------

/// Picks a positive `δ` small enough that every active strict constraint still
/// holds once the infinitesimal is instantiated.
fn choose_delta(graph: &DlGraph, scale: i128) -> Option<Rational> {
    let mut delta = Rational::integer(1);
    for edge in &graph.edges {
        let lhs = graph.pi[edge.spec.to].checked_sub(graph.pi[edge.spec.from])?;
        let slack_c = edge.spec.w.c.checked_sub(lhs.c)?;
        let slack_d = edge.spec.w.d.checked_sub(lhs.d)?;
        // Constraint: `slack_c/scale + δ·slack_d ≥ 0`. Only a negative δ-slack
        // bounds δ from above.
        if slack_d >= 0 {
            continue;
        }
        if slack_c <= 0 {
            // Lexicographic feasibility rules this out; bail rather than emit a
            // value we cannot justify.
            return None;
        }
        let bound = Rational::checked_new(slack_c, scale.checked_mul(i128::from(-slack_d))?)?;
        if bound.checked_cmp(&delta)? == Ordering::Less {
            delta = bound;
        }
    }
    // Halve it so every bounding constraint stays strictly satisfied.
    delta.checked_div(Rational::integer(2))
}

/// Lifts the vertex potentials into a model over the query's symbols, with the
/// zero vertex pinned to `0`.
fn lift_model(scan: &DlScan, graph: &DlGraph) -> Option<Model> {
    let mut model = Model::new();
    let delta = match scan.mode {
        Mode::Integer => Rational::zero(),
        Mode::Real => choose_delta(graph, scan.scale)?,
    };
    let base = graph.pi[ZERO_VERTEX];
    for (vertex, &symbol) in scan.symbols.iter().enumerate() {
        let raw = graph.pi[vertex].checked_sub(base)?;
        match scan.mode {
            Mode::Integer => {
                // Integer mode never scales and never uses δ, so the potential
                // difference is already the value.
                if raw.d != 0 || scan.scale != 1 {
                    return None;
                }
                model.set(symbol, Value::Int(raw.c));
            }
            Mode::Real => {
                let rational = Rational::checked_new(raw.c, scan.scale)?;
                let infinitesimal = delta.checked_mul(Rational::integer(i128::from(raw.d)))?;
                model.set(symbol, Value::Real(rational.checked_add(infinitesimal)?));
            }
        }
    }
    Some(model)
}

/// Injects each Boolean skeleton leaf (a skeleton variable that is not a
/// registered difference atom) from the driver trail. Additive and replay-gated
/// by the caller, so it can never manufacture a wrong `sat`. Visited in sorted
/// `(TermId, var)` order for determinism.
fn add_boolean_leaves(
    arena: &TermArena,
    enc: &Encoder,
    atom_count: usize,
    solver: &CdclT,
    model: &mut Model,
) {
    let mut term_vars: Vec<(TermId, usize)> = enc.term_var.iter().map(|(&t, &v)| (t, v)).collect();
    term_vars.sort_by_key(|(term, _)| *term);
    for (term, var) in term_vars {
        if var < atom_count {
            continue;
        }
        if let TermNode::Symbol(symbol) = arena.node(term)
            && arena.sort_of(term) == Sort::Bool
            && let Some(value) = solver.value(var)
        {
            model.set(*symbol, Value::Bool(value));
        }
    }
}

/// The standing discipline: a candidate model is only a `sat` after it replays
/// through the ground evaluator against the **original** assertions.
fn replays(arena: &TermArena, assertions: &[TermId], model: &Model) -> bool {
    let assignment = model.to_assignment();
    assertions
        .iter()
        .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))))
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn unknown(detail: &str) -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: detail.to_owned(),
    }
}

/// Decides a **pure difference-logic** query (`QF_IDL` / `QF_RDL`) through the
/// generic CDCL(T) driver with negative-cycle detection as the theory.
///
/// Returns `Ok(None)` — leaving the query to the established routes — unless
/// every relational atom is provably difference-shaped and the whole query is
/// single-sorted numeric plus a propositional skeleton the encoder covers. See
/// the module docs for the exact refusal conditions.
///
/// There is deliberately no error channel: every give-up is either `None` (not
/// our fragment) or a conservative [`CheckResult::Unknown`].
pub(crate) fn try_check_qf_dl(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Option<CheckResult> {
    let scan = scan_dl(arena, assertions)?;

    let mut enc = Encoder::new(&scan.atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    // Tseitin `g ⟺ le ∧ ge` for every expanded numeric equality, so the
    // skeleton — not the theory — owns the disjunctive negation. Gate variables
    // follow the registered atoms, leaving atom indices aligned with the
    // theory's numbering.
    for &(term, le_index, ge_index) in &scan.eq_gates {
        let gate = enc.var_count;
        enc.var_count += 1;
        let g = Lit {
            var: gate,
            positive: true,
        };
        let le = Lit {
            var: le_index,
            positive: true,
        };
        let ge = Lit {
            var: ge_index,
            positive: true,
        };
        clauses.push(vec![g.negate(), le]);
        clauses.push(vec![g.negate(), ge]);
        clauses.push(vec![le.negate(), ge.negate(), g]);
        enc.term_var.insert(term, gate);
    }
    // Tseitin `g ⟺ (a ⟺ b)` for every Boolean equality, in the post-order the
    // scan recorded, so a nested equality already has its variable.
    for &(term, lhs, rhs) in &scan.bool_eq_gates {
        let a = Lit {
            var: enc.encode(arena, lhs, &mut clauses)?,
            positive: true,
        };
        let b = Lit {
            var: enc.encode(arena, rhs, &mut clauses)?,
            positive: true,
        };
        let g = Lit {
            var: enc.var_count,
            positive: true,
        };
        enc.var_count += 1;
        clauses.push(vec![g.negate(), a.negate(), b]);
        clauses.push(vec![g.negate(), a, b.negate()]);
        clauses.push(vec![g, a, b]);
        clauses.push(vec![g, a.negate(), b.negate()]);
        enc.term_var.insert(term, g.var);
    }
    for &assertion in assertions {
        let top = enc.encode(arena, assertion, &mut clauses)?;
        clauses.push(vec![Lit {
            var: top,
            positive: true,
        }]);
    }
    let driver_clauses: Vec<Vec<CdcltLit>> = clauses
        .iter()
        .map(|clause| {
            clause
                .iter()
                .map(|l| CdcltLit {
                    var: l.var,
                    positive: l.positive,
                })
                .collect()
        })
        .collect();

    let atom_count = scan.atom_terms.len();
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let mut theory = DlTheory::new(&scan, deadline);
    let mut solver = CdclT::new(enc.var_count, atom_count, driver_clauses, deadline);
    match solver.solve(&mut theory) {
        Outcome::Unsat => Some(CheckResult::Unsat),
        Outcome::Unknown => Some(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Timeout,
            detail: "budget exhausted in the online difference-logic driver".to_owned(),
        })),
        Outcome::Sat => {
            let Some(mut model) = lift_model(&scan, &theory.graph) else {
                return Some(CheckResult::Unknown(unknown(
                    "difference-logic potentials did not lift to an exact model",
                )));
            };
            add_boolean_leaves(arena, &enc, atom_count, &solver, &mut model);
            if replays(arena, assertions, &model) {
                Some(CheckResult::Sat(model))
            } else {
                Some(CheckResult::Unknown(unknown(
                    "difference-logic model did not replay against the original assertions",
                )))
            }
        }
    }
}

#[cfg(test)]
mod tests;
