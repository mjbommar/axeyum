//! The `F-Split` / `Len-Split` **arrangement search** (slice T-B.4a) — the layer
//! that turns the T-B.2/T-B.3 substrate into the first word-equation **models**.
//!
//! [`solve_word_equations`] runs a deterministic depth-first search over
//! arrangement choices for a caller-supplied set of `Seq`-sorted equalities and
//! disequalities, and returns either a concrete satisfying [`Assignment`]
//! ([`SearchOutcome::Sat`]) or a first-class [`SearchOutcome::Unknown`]. There is
//! **no `Unsat` variant**: a wrong `unsat` is made *unrepresentable in the type*.
//! Word-level unsat waits for the checkable-derivation slice (T-B.7); an
//! exhausted or over-budget search is [`SearchOutcome::Unknown`], never `unsat`
//! (ADR-0053).
//!
//! # The trust anchor: mandatory replay
//!
//! A model is returned **only** after every original equality and disequality
//! evaluates to `true` under it through the [`axeyum_ir::eval`] ground evaluator
//! (the executable semantic reference). This replay is not a debug assertion — it
//! is the sole gate on [`SearchOutcome::Sat`]. A candidate assignment whose replay
//! fails is discarded and the search continues; if nothing replays, the outcome
//! is [`SearchOutcome::Unknown`]. Consequently **no wrong `sat` is possible by
//! construction** regardless of any bug in the search itself.
//!
//! # The search
//!
//! At every node the [T-B.3 inference fixpoint](mod@crate::infer) runs first: its
//! derived facts prune the search (they are asserted as extra equalities for the
//! child view), and a [`Conflict`](crate::Conflict) kills the branch — a dead
//! branch is *backtracked*, never reported as global unsat. When every class's
//! members cell-reconcile (no declined front anywhere) the node is a leaf and a
//! model is instantiated (smallest lengths first). Otherwise the first declined
//! alignment *front* is found and branched:
//!
//! * **`F-Split`** — a variable component `u` facing another variable `v` of
//!   unknown relative length branches on `u ≈ ε`, `v ≈ ε`, `u ≈ v ++ k`, and
//!   `v ≈ u ++ k` with a **fresh Skolem** `k` (a new `Seq`-sorted arena symbol,
//!   projected out of the returned assignment — the search binds only original
//!   symbols).
//! * a variable `u` facing a constant *character* `c` branches on `u ≈ ε`
//!   (**`Len-Split`**, the ε case) and `u ≈ c ++ k` with a fresh Skolem (the
//!   `|u| ≥ 1` case). Constant blocks are aligned **character by character**, so a
//!   variable is only ever split against a single character at a time and the
//!   deterministic constant-split cases fall out uniformly.
//!
//! # Termination
//!
//! Every entry point takes an explicit [`SearchBudget`] (a maximum number of
//! branch nodes and — on native targets — an absolute deadline) and honors it at
//! **every** node, so the deadline-hole bug class is designed out. Fresh Skolem
//! introduction is additionally capped per search path ([`MAX_SKOLEMS`]): a
//! looping equation such as `x ≈ a ++ x` burns the cap and yields
//! [`SearchOutcome::Unknown`] (`F-Loop` regularization is T-B.5). Every observable
//! output is deterministic: branch order, class iteration, and instantiation
//! order are all fixed (`BTreeSet`/`TermId` order).
//!
//! # WebAssembly
//!
//! The absolute-deadline field is `#[cfg]`-gated to native targets (the crate
//! depends only on [`axeyum_ir`]; it pulls in no wall-clock shim). Under
//! `wasm32` termination rests entirely on the node budget, which every node
//! decrements unconditionally.

use std::collections::{BTreeMap, BTreeSet};

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;

use axeyum_ir::{ArraySortKey, Assignment, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value};

use crate::classes::Classes;
use crate::infer::infer;
use crate::normal_form::{concat_components, normalize};

/// The maximum number of fresh Skolems introduced along any single search path
/// before the path yields [`SearchOutcome::Unknown`].
///
/// Each `F-Split` (or `|u| ≥ 1` character split) introduces one Skolem, and a
/// looping equation would introduce them without bound. Capping the *path* depth
/// (not the global count) bounds recursion depth — hence termination — while
/// leaving sibling branches free to each spend the full budget. A path that hits
/// the cap is reported as [`UnknownReason::SkolemCap`]: honest `unknown`, never a
/// silent decline.
pub const MAX_SKOLEMS: usize = 48;

/// The maximum number of concrete instantiations tried when reconciling
/// disequalities at a reconciled leaf. Bounds the smallest-lengths-first
/// enumeration so a leaf with many free variables cannot spin; exceeding it
/// simply means no model is found *at this leaf* (the search continues, and an
/// exhausted search is `unknown`).
const MAX_MODEL_ATTEMPTS: u64 = 8_192;

/// The budget every arrangement search honors: a hard cap on branch nodes and,
/// on native targets, an absolute wall-clock deadline. Both are checked at every
/// node (ADR-0053: the deadline-hole bug class is designed out).
#[derive(Debug, Clone)]
pub struct SearchBudget {
    /// The maximum number of branch nodes to visit before returning
    /// [`UnknownReason::NodeBudget`]. This is the sole termination guard under
    /// `wasm32`.
    pub max_nodes: u64,
    /// An absolute deadline; the search returns [`UnknownReason::Deadline`] at
    /// the first node reached at or after it. Native-only — see the module docs
    /// for the WebAssembly story.
    #[cfg(not(target_arch = "wasm32"))]
    pub deadline: Option<Instant>,
}

impl SearchBudget {
    /// A budget of `max_nodes` branch nodes and no deadline.
    #[must_use]
    pub fn new(max_nodes: u64) -> Self {
        Self {
            max_nodes,
            #[cfg(not(target_arch = "wasm32"))]
            deadline: None,
        }
    }

    /// A budget of `max_nodes` branch nodes with an absolute `deadline` (native
    /// targets only).
    #[cfg(not(target_arch = "wasm32"))]
    #[must_use]
    pub fn with_deadline(max_nodes: u64, deadline: Instant) -> Self {
        Self {
            max_nodes,
            deadline: Some(deadline),
        }
    }

    /// Whether the deadline has passed. Always `false` under `wasm32` (no
    /// deadline field there — node budget governs termination). Public so the
    /// T-B.7 [`refute_word_equations`](crate::refute_word_equations) arm honors
    /// the same deadline discipline every solve does.
    #[must_use]
    pub fn past_deadline(&self) -> bool {
        #[cfg(not(target_arch = "wasm32"))]
        {
            self.deadline.is_some_and(|d| Instant::now() >= d)
        }
        #[cfg(target_arch = "wasm32")]
        {
            false
        }
    }
}

/// Why an arrangement search stopped without a model. First-class `unknown`
/// (ADR-0053): none of these is `unsat`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnknownReason {
    /// The search tree was fully explored without finding a replaying model. The
    /// instance may be genuinely unsat, but this slice never *claims* unsat.
    Exhausted,
    /// The node budget ([`SearchBudget::max_nodes`]) was exhausted.
    NodeBudget,
    /// The absolute deadline passed (native targets only).
    Deadline,
    /// The [T-B.3 inference fixpoint](mod@crate::infer) hit its own round budget on
    /// some branch, so propagation was incomplete.
    InferBudget,
    /// A search path reached the [`MAX_SKOLEMS`] cap (a loop the T-B.5 `F-Loop`
    /// device would regularize).
    SkolemCap,
    /// A containment cycle survived inference (an unbroken loop; `F-Loop` is
    /// T-B.5).
    UnbrokenLoop,
    /// An input endpoint was not `Seq`-sorted, so the word-equation search does
    /// not apply.
    NonSequence,
}

impl core::fmt::Display for UnknownReason {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self {
            UnknownReason::Exhausted => "search exhausted without a model",
            UnknownReason::NodeBudget => "node budget exhausted",
            UnknownReason::Deadline => "deadline reached",
            UnknownReason::InferBudget => "inference round budget hit",
            UnknownReason::SkolemCap => "fresh-Skolem cap reached (loop)",
            UnknownReason::UnbrokenLoop => "containment cycle survived inference (loop)",
            UnknownReason::NonSequence => "a non-sequence endpoint was supplied",
        };
        f.write_str(s)
    }
}

/// The verdict of an arrangement search. **No `Unsat` variant** — a wrong
/// `unsat` is unrepresentable (ADR-0053).
#[derive(Debug, Clone)]
pub enum SearchOutcome {
    /// A concrete satisfying assignment that has **replayed** through the ground
    /// evaluator against every original equality and disequality. Skolems are
    /// projected out (only original symbols are bound).
    Sat(Assignment),
    /// No model was produced; the reason is first-class `unknown`.
    Unknown {
        /// Why the search stopped.
        reason: UnknownReason,
    },
}

/// Searches for a satisfying assignment of `equalities ∧ ¬disequalities` over
/// unbounded `Seq`-sorted terms, using the `F-Split` / `Len-Split` arrangement
/// procedure.
///
/// Returns [`SearchOutcome::Sat`] with a replay-checked model, or
/// [`SearchOutcome::Unknown`] when the search is exhausted or hits the supplied
/// [`SearchBudget`] / [`MAX_SKOLEMS`] cap. Never returns `unsat` (the outcome
/// type has no such variant). Deterministic for a fixed input and budget.
#[must_use]
pub fn solve_word_equations(
    arena: &mut TermArena,
    equalities: &[(TermId, TermId)],
    disequalities: &[(TermId, TermId)],
    budget: &SearchBudget,
) -> SearchOutcome {
    // Validate: every endpoint must be a sequence.
    for &(a, b) in equalities.iter().chain(disequalities) {
        if !matches!(arena.sort_of(a), Sort::Seq(_)) || !matches!(arena.sort_of(b), Sort::Seq(_)) {
            return SearchOutcome::Unknown {
                reason: UnknownReason::NonSequence,
            };
        }
    }

    // The original `Seq` symbols that a model must bind (skolems are excluded by
    // construction: they never appear in the original terms).
    let orig_symbols = collect_seq_symbols(arena, equalities, disequalities);

    let mut ctx = Ctx {
        budget,
        nodes: 0,
        skolem_names: 0,
        orig_equalities: equalities,
        orig_disequalities: disequalities,
        orig_symbols,
    };

    match search(&mut ctx, arena, equalities, 0) {
        Node::Sat(asg) => SearchOutcome::Sat(*asg),
        Node::Unknown(reason) => SearchOutcome::Unknown { reason },
        // A cleanly-exhausted tree is `unknown`, NEVER `unsat` (ADR-0053).
        Node::Dead => SearchOutcome::Unknown {
            reason: UnknownReason::Exhausted,
        },
    }
}

/// Mutable search context threaded through the DFS.
struct Ctx<'a> {
    budget: &'a SearchBudget,
    /// Branch nodes visited so far (against [`SearchBudget::max_nodes`]).
    nodes: u64,
    /// Monotonic counter for unique fresh-Skolem names.
    skolem_names: usize,
    /// The original assertions — the replay trust anchor.
    orig_equalities: &'a [(TermId, TermId)],
    orig_disequalities: &'a [(TermId, TermId)],
    /// The original `Seq` symbols a model binds.
    orig_symbols: Vec<(SymbolId, TermId)>,
}

/// A search node's three-valued result. `Dead` means "no model found in this
/// subtree, cleanly" — it does **not** assert unsat; the top level maps a fully
/// `Dead` tree to [`UnknownReason::Exhausted`].
enum Node {
    /// A replay-checked model (boxed to keep the enum small).
    Sat(Box<Assignment>),
    /// No model and no uncertainty in this subtree.
    Dead,
    /// Uncertainty was encountered (budget / deadline / cap / loop).
    Unknown(UnknownReason),
}

/// One DFS node: propagate with inference, then either instantiate a model at a
/// reconciled leaf or branch on the first declined front.
fn search(ctx: &mut Ctx, arena: &mut TermArena, eqs: &[(TermId, TermId)], skolems: usize) -> Node {
    ctx.nodes += 1;
    if ctx.nodes > ctx.budget.max_nodes {
        return Node::Unknown(UnknownReason::NodeBudget);
    }
    if ctx.budget.past_deadline() {
        return Node::Unknown(UnknownReason::Deadline);
    }

    // (1) Propagate. A conflict kills this branch (backtrack — not global unsat).
    let inf = infer(arena, eqs);
    if inf.hit_budget {
        return Node::Unknown(UnknownReason::InferBudget);
    }
    if inf.is_conflict() {
        return Node::Dead;
    }
    // Assert derived facts into the propagated view.
    let mut propagated = eqs.to_vec();
    for f in inf.facts() {
        propagated.push(f.equality);
    }
    let classes = Classes::new(&propagated);

    // (2) Leaf or branch. A leaf is a state in which every class's members
    // cell-reconcile (no declined front anywhere).
    match find_any_front(arena, &classes, &propagated) {
        Some(front) => branch_on(ctx, arena, eqs, &classes, front, skolems),
        None => match try_model(ctx, arena, &classes, &propagated) {
            Some(asg) => Node::Sat(Box::new(asg)),
            None => Node::Dead,
        },
    }
}

/// The first declined front across every equivalence class of `propagated`, or
/// `None` when every class fully cell-reconciles (a leaf).
fn find_any_front(
    arena: &mut TermArena,
    classes: &Classes,
    propagated: &[(TermId, TermId)],
) -> Option<Front> {
    for rep in class_reps(classes, propagated) {
        if let Some(front) = find_front(arena, classes, rep) {
            return Some(front);
        }
    }
    None
}

/// The sorted, deduplicated class representatives touched by `propagated`.
fn class_reps(classes: &Classes, propagated: &[(TermId, TermId)]) -> Vec<TermId> {
    let mut set: BTreeSet<TermId> = BTreeSet::new();
    for &(a, b) in propagated {
        set.insert(classes.representative(a));
        set.insert(classes.representative(b));
    }
    set.into_iter().collect()
}

/// Enumerates the arrangement branches for `front`, recursing into each in a
/// fixed order and returning the first [`Node::Sat`]. A branch that would exceed
/// the Skolem cap is suppressed and surfaced as [`UnknownReason::SkolemCap`].
fn branch_on(
    ctx: &mut Ctx,
    arena: &mut TermArena,
    eqs: &[(TermId, TermId)],
    classes: &Classes,
    front: Front,
    skolems: usize,
) -> Node {
    let (branches, suppressed_skolem) = gen_branches(ctx, arena, front, skolems);

    let mut worst: Option<UnknownReason> = if suppressed_skolem {
        Some(UnknownReason::SkolemCap)
    } else {
        None
    };

    for br in branches {
        // Skip a branch that makes no progress (already-ε target).
        if !br.introduces_skolem
            && already_epsilon(classes, arena, br.eq.0)
            && is_epsilon(arena, br.eq.1)
        {
            continue;
        }
        let mut child = eqs.to_vec();
        child.push(br.eq);
        let child_skolems = skolems + usize::from(br.introduces_skolem);
        match search(ctx, arena, &child, child_skolems) {
            Node::Sat(a) => return Node::Sat(a),
            Node::Dead => {}
            Node::Unknown(r) => worst = Some(pick_reason(worst, r)),
        }
    }

    match worst {
        Some(r) => Node::Unknown(r),
        None => Node::Dead,
    }
}

/// Prefers the more decisive uncertainty when several branches disagree
/// (global stop conditions dominate local caps).
fn pick_reason(current: Option<UnknownReason>, incoming: UnknownReason) -> UnknownReason {
    fn rank(r: UnknownReason) -> u8 {
        match r {
            UnknownReason::Deadline => 6,
            UnknownReason::NodeBudget => 5,
            UnknownReason::InferBudget => 4,
            UnknownReason::UnbrokenLoop => 3,
            UnknownReason::SkolemCap => 2,
            UnknownReason::NonSequence => 1,
            UnknownReason::Exhausted => 0,
        }
    }
    match current {
        Some(c) if rank(c) >= rank(incoming) => c,
        _ => incoming,
    }
}

// ----- arrangement fronts -----------------------------------------------------

/// A declined alignment front between two members of one equivalence class.
#[derive(Debug, Clone, Copy)]
enum Front {
    /// Two variable components of unknown relative length (`F-Split`).
    TwoVars(TermId, TermId),
    /// A variable component facing a single constant character `ch` (a length-1
    /// `seq.unit` constant term). Splits `var ≈ ε ∥ var ≈ ch ++ k`.
    CharSplit {
        /// The variable class representative.
        var: TermId,
        /// The length-1 constant `seq.unit` term at the facing position.
        ch: TermId,
    },
    /// A leftover variable that must reconcile to ε (one side of the alignment
    /// ran out). Branches on `var ≈ ε` only.
    TailEps(TermId),
}

/// A cell in a member's aligned view: a single constant character or a variable
/// class of unknown length.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cell {
    /// A length-1 constant `seq.unit` term.
    Char(TermId),
    /// A variable class representative (a `Seq` term of unknown length).
    Var(TermId),
}

/// Finds the first declined front in the members of the class rooted at `rep`,
/// scanning member pairs and positions in deterministic order. Each member is
/// expanded through its atoms' class decompositions (so a variable already
/// constrained to start with a constant surfaces that constant, and the search
/// advances past it instead of re-splitting forever).
fn find_front(arena: &mut TermArena, classes: &Classes, rep: TermId) -> Option<Front> {
    let members = classes.class_members(rep);
    // Precompute each member's expanded cell view once. Seeding the `visiting`
    // set with `rep` keeps a member's own class opaque (no self-expansion). A
    // member that expands to just the class's own opaque variable (`[Var(rep)]`)
    // carries no alignment information — it *is* the whole class — so it is
    // dropped: only members that genuinely decompose can declare a front.
    let cells: Vec<Vec<Cell>> = members
        .iter()
        .filter_map(|&m| {
            let mut visiting = BTreeSet::from([rep]);
            let c = expand_member(arena, classes, m, &mut visiting);
            (c.as_slice() != [Cell::Var(rep)]).then_some(c)
        })
        .collect();

    for i in 0..cells.len() {
        for j in (i + 1)..cells.len() {
            if let Some(front) = front_of_pair(arena, &cells[i], &cells[j]) {
                return Some(front);
            }
        }
    }
    None
}

/// The first branchable divergence between two aligned cell vectors, if any.
fn front_of_pair(arena: &TermArena, a: &[Cell], b: &[Cell]) -> Option<Front> {
    let (mut i, mut j) = (0usize, 0usize);
    while i < a.len() && j < b.len() {
        if cells_equal(arena, a[i], b[j]) {
            i += 1;
            j += 1;
            continue;
        }
        return front_from(a[i], b[j]);
    }
    // One side exhausted: the remaining side must reconcile to ε. A leftover
    // variable is a Len-Split target; a leftover character is a genuine
    // length clash (no branch — inference already had its chance).
    let leftover = if i < a.len() { &a[i..] } else { &b[j..] };
    for cell in leftover {
        if let Cell::Var(v) = *cell {
            return Some(Front::TailEps(v));
        }
    }
    None
}

/// The branch front for a divergent `(a, b)` cell pair.
fn front_from(a: Cell, b: Cell) -> Option<Front> {
    match (a, b) {
        (Cell::Var(u), Cell::Var(v)) => Some(Front::TwoVars(u, v)),
        (Cell::Var(u), Cell::Char(c)) | (Cell::Char(c), Cell::Var(u)) => {
            Some(Front::CharSplit { var: u, ch: c })
        }
        // Two distinct characters: a length-1 constant clash inference should have
        // reported. No variable to branch — treat as no model here.
        (Cell::Char(_), Cell::Char(_)) => None,
    }
}

/// The expanded cell view of one member: each atom replaced by its class's
/// decomposition ([`class_cells`]), ε-class atoms dropped. `visiting` guards
/// against expanding a class back into itself.
fn expand_member(
    arena: &mut TermArena,
    classes: &Classes,
    member: TermId,
    visiting: &mut BTreeSet<TermId>,
) -> Vec<Cell> {
    let norm = normalize(arena, member);
    let atoms = concat_components(arena, norm);
    let mut cells = Vec::new();
    for atom in atoms {
        let rep = classes.representative(atom);
        if class_is_epsilon(classes, arena, rep) {
            continue;
        }
        cells.extend(class_cells(arena, classes, rep, visiting));
    }
    cells
}

/// The decomposed cell view of the equivalence class rooted at `rep`: a
/// constant class's characters, else its most-decomposed member expanded
/// recursively, else the free self-variable `[Var(rep)]`. `visiting` bounds the
/// recursion (a class already on the stack stays an opaque `Var`).
fn class_cells(
    arena: &mut TermArena,
    classes: &Classes,
    rep: TermId,
    visiting: &mut BTreeSet<TermId>,
) -> Vec<Cell> {
    // A constant member fixes the class to literal characters (checked first, so
    // even a class currently on the recursion stack resolves).
    if let Some(cterm) = class_constant_atom(classes, arena, rep) {
        return char_units(arena, cterm)
            .into_iter()
            .map(Cell::Char)
            .collect();
    }
    if !visiting.insert(rep) {
        return vec![Cell::Var(rep)]; // on the stack: opaque, breaks recursion
    }
    let members = classes.class_members(rep);
    // Prefer the most-decomposed member, breaking ties toward the most concrete
    // (most `Char` cells) so a variable forced to a constant is not left opaque.
    let mut best: Vec<Cell> = vec![Cell::Var(rep)];
    let mut best_key = cell_key(&best);
    for &m in &members {
        let cells = expand_member(arena, classes, m, visiting);
        let key = cell_key(&cells);
        if key > best_key {
            best = cells;
            best_key = key;
        }
    }
    visiting.remove(&rep);
    best
}

/// The preference key for a cell decomposition: more cells first, then more
/// literal characters (a concrete decomposition beats an opaque self-variable
/// of equal length).
fn cell_key(cells: &[Cell]) -> (usize, usize) {
    let chars = cells.iter().filter(|c| matches!(c, Cell::Char(_))).count();
    (cells.len(), chars)
}

/// Whether two cells denote the same thing: identical variable reps, or equal
/// constant characters.
fn cells_equal(arena: &TermArena, a: Cell, b: Cell) -> bool {
    match (a, b) {
        (Cell::Var(x), Cell::Var(y)) => x == y,
        (Cell::Char(x), Cell::Char(y)) => value_of(arena, x) == value_of(arena, y),
        _ => false,
    }
}

// ----- branch generation ------------------------------------------------------

/// One materialized arrangement branch: an extra equality plus whether it
/// introduced a fresh Skolem (which deepens the path's Skolem count).
struct Branch {
    eq: (TermId, TermId),
    introduces_skolem: bool,
}

/// Materializes the branches for `front`. Returns the branch list and whether a
/// Skolem branch was **suppressed** because the path Skolem cap was reached.
fn gen_branches(
    ctx: &mut Ctx,
    arena: &mut TermArena,
    front: Front,
    skolems: usize,
) -> (Vec<Branch>, bool) {
    let mut out = Vec::new();
    let mut suppressed = false;
    let can_skolem = skolems < MAX_SKOLEMS;

    match front {
        Front::TailEps(t) => {
            if let Some(eps) = epsilon_like(arena, t) {
                out.push(Branch {
                    eq: (t, eps),
                    introduces_skolem: false,
                });
            }
        }
        Front::CharSplit { var, ch } => {
            if let Some(eps) = epsilon_like(arena, var) {
                out.push(Branch {
                    eq: (var, eps),
                    introduces_skolem: false,
                });
            }
            // var ≈ ch ++ k  (|var| ≥ 1)
            if can_skolem {
                if let Some(cat) = skolem_tail(ctx, arena, var, ch) {
                    out.push(Branch {
                        eq: (var, cat),
                        introduces_skolem: true,
                    });
                }
            } else {
                suppressed = true;
            }
        }
        Front::TwoVars(t, u) => {
            if let Some(eps) = epsilon_like(arena, t) {
                out.push(Branch {
                    eq: (t, eps),
                    introduces_skolem: false,
                });
            }
            if let Some(eps) = epsilon_like(arena, u) {
                out.push(Branch {
                    eq: (u, eps),
                    introduces_skolem: false,
                });
            }
            if can_skolem {
                // t ≈ u ++ k  and  u ≈ t ++ k
                if let Some(cat) = skolem_tail(ctx, arena, t, u) {
                    out.push(Branch {
                        eq: (t, cat),
                        introduces_skolem: true,
                    });
                }
                if let Some(cat) = skolem_tail(ctx, arena, u, t) {
                    out.push(Branch {
                        eq: (u, cat),
                        introduces_skolem: true,
                    });
                }
            } else {
                suppressed = true;
            }
        }
    }
    (out, suppressed)
}

/// Builds `head ++ k` for a fresh Skolem `k` of `owner`'s element sort (the
/// Skolem represents the unknown remainder). `head` is the leading known piece
/// (a character or the other variable).
fn skolem_tail(
    ctx: &mut Ctx,
    arena: &mut TermArena,
    owner: TermId,
    head: TermId,
) -> Option<TermId> {
    let key = seq_key(arena, owner)?;
    let k = fresh_skolem(ctx, arena, key);
    arena.seq_concat(head, k).ok()
}

/// Declares a fresh, uniquely-named `Seq`-sorted Skolem symbol and returns its
/// variable term.
fn fresh_skolem(ctx: &mut Ctx, arena: &mut TermArena, key: ArraySortKey) -> TermId {
    loop {
        let name = format!("!wesk!{}", ctx.skolem_names);
        ctx.skolem_names += 1;
        // Mint on the internal-symbol namespace (disjoint from user `declare`),
        // so a crafted `(declare-fun !wesk!N …)` can never alias this fresh
        // word-equation Skolem. The freshness guard checks the same internal
        // namespace we mint into.
        if arena.find_internal_symbol(&name).is_none() {
            let s = arena
                .declare_internal(&name, Sort::Seq(key))
                .expect("fresh skolem name is unique");
            return arena.var(s);
        }
    }
}

// ----- leaf model construction ------------------------------------------------

/// Attempts to instantiate a replay-checked model at a reconciled leaf: assigns
/// free variables smallest-lengths-first, retries over a bounded alphabet to
/// satisfy disequalities, and returns the assignment only if **every** original
/// equality and disequality replays true.
fn try_model(
    ctx: &Ctx,
    arena: &mut TermArena,
    classes: &Classes,
    propagated: &[(TermId, TermId)],
) -> Option<Assignment> {
    let free_atoms: Vec<TermId> = collect_free_atoms(arena, classes, ctx, propagated)
        .into_iter()
        .collect();
    let candidates = candidate_values(arena, ctx, propagated);

    // Odometer over free-atom instantiations, smallest first.
    let n = free_atoms.len();
    let radix = candidates.len().max(1);
    let mut odometer = vec![0usize; n];
    let mut attempts = 0u64;

    loop {
        if attempts >= MAX_MODEL_ATTEMPTS {
            return None;
        }
        attempts += 1;

        let chosen: BTreeMap<TermId, Value> = free_atoms
            .iter()
            .zip(&odometer)
            .map(|(&atom, &idx)| (atom, candidates[idx].clone()))
            .collect();

        if let Some(asg) = build_and_replay(arena, classes, ctx, &chosen) {
            return Some(asg);
        }

        // Advance the odometer (least-significant = first free atom).
        if n == 0 {
            return None;
        }
        let mut k = 0;
        loop {
            if k == n {
                return None; // all combinations exhausted
            }
            odometer[k] += 1;
            if odometer[k] < radix {
                break;
            }
            odometer[k] = 0;
            k += 1;
        }
    }
}

/// Builds the assignment for one `chosen` free-atom instantiation and replays it
/// against the original assertions; returns it only on a fully-true replay.
fn build_and_replay(
    arena: &mut TermArena,
    classes: &Classes,
    ctx: &Ctx,
    chosen: &BTreeMap<TermId, Value>,
) -> Option<Assignment> {
    let mut asg = Assignment::new();
    for &(sym, symterm) in &ctx.orig_symbols {
        let rep = classes.representative(symterm);
        let v = class_value(arena, classes, chosen, rep)?;
        asg.set(sym, v);
    }

    // Mandatory replay — the trust anchor.
    for &(a, b) in ctx.orig_equalities {
        if value_eval(arena, a, &asg)? != value_eval(arena, b, &asg)? {
            return None;
        }
    }
    for &(a, b) in ctx.orig_disequalities {
        if value_eval(arena, a, &asg)? == value_eval(arena, b, &asg)? {
            return None;
        }
    }
    Some(asg)
}

/// The concrete `Seq` value of the class rooted at `rep` under `chosen`,
/// computed from its fully-expanded cell view: characters are literal and each
/// free variable leaf takes its `chosen` value (ε when unbound). A residual
/// opaque cycle leaf resolves to its `chosen`/ε value too — the mandatory replay
/// remains the sole gate, so this can never yield a wrong model.
fn class_value(
    arena: &mut TermArena,
    classes: &Classes,
    chosen: &BTreeMap<TermId, Value>,
    rep: TermId,
) -> Option<Value> {
    let cells = class_cells(arena, classes, rep, &mut BTreeSet::new());
    let mut elems: Vec<Value> = Vec::new();
    for cell in cells {
        match cell {
            Cell::Char(c) => {
                let Some(Value::Seq(v)) = value_of(arena, c) else {
                    return None;
                };
                elems.extend(v);
            }
            Cell::Var(sub) => {
                let Value::Seq(v) = chosen.get(&sub).cloned().unwrap_or(Value::Seq(Vec::new()))
                else {
                    return None;
                };
                elems.extend(v);
            }
        }
    }
    Some(Value::Seq(elems))
}

/// The free (undetermined) variable atoms a model must instantiate: every
/// `Cell::Var` leaf of the expanded cell view of every relevant class.
fn collect_free_atoms(
    arena: &mut TermArena,
    classes: &Classes,
    ctx: &Ctx,
    propagated: &[(TermId, TermId)],
) -> BTreeSet<TermId> {
    // Scan every class touched by an equality plus every original symbol's class
    // (a disequality-only variable appears in no equality but is still free).
    let mut reps: BTreeSet<TermId> = class_reps(classes, propagated).into_iter().collect();
    for &(_, symterm) in &ctx.orig_symbols {
        reps.insert(classes.representative(symterm));
    }

    let mut free = BTreeSet::new();
    for rep in reps {
        for cell in class_cells(arena, classes, rep, &mut BTreeSet::new()) {
            if let Cell::Var(r) = cell {
                free.insert(r);
            }
        }
    }
    free
}

/// The candidate values a free atom may take, smallest first: ε, then each
/// single-character sequence over the instance alphabet (constants present plus
/// a couple of fresh characters, to satisfy disequalities).
fn candidate_values(arena: &TermArena, ctx: &Ctx, propagated: &[(TermId, TermId)]) -> Vec<Value> {
    let mut out = vec![Value::Seq(Vec::new())]; // ε is always the smallest choice
    for elem in alphabet(arena, ctx, propagated) {
        out.push(Value::Seq(vec![elem]));
    }
    out
}

/// The instance alphabet as element [`Value`]s: distinct characters observed in
/// the assertions, plus up to two fresh characters (for disequality
/// separation). Deterministic order.
fn alphabet(arena: &TermArena, ctx: &Ctx, propagated: &[(TermId, TermId)]) -> Vec<Value> {
    let mut used: BTreeSet<u128> = BTreeSet::new();
    let mut observed: Vec<Value> = Vec::new();

    // Gather observed characters from every constant `seq.unit` subterm.
    for &(a, b) in ctx.orig_equalities.iter().chain(ctx.orig_disequalities) {
        for endpoint in [a, b] {
            collect_chars(arena, endpoint, &mut used, &mut observed);
        }
    }
    let _ = propagated; // propagated equalities add no new characters beyond the originals

    // Fresh characters for disequality separation, drawn from the element sort.
    if let Some(key) = any_seq_key(arena, ctx) {
        let mut fresh = 0;
        match key {
            ArraySortKey::BitVec(w) => {
                let mut code = 0u128;
                let cap = if w >= 64 { u128::MAX } else { (1u128 << w) - 1 };
                while fresh < 2 && code <= cap {
                    if !used.contains(&code) {
                        observed.push(Value::Bv {
                            width: w,
                            value: code,
                        });
                        used.insert(code);
                        fresh += 1;
                    }
                    if code == cap {
                        break;
                    }
                    code += 1;
                }
            }
            ArraySortKey::Bool => {
                for b in [false, true] {
                    let code = u128::from(b);
                    if fresh < 2 && used.insert(code) {
                        observed.push(Value::Bool(b));
                        fresh += 1;
                    }
                }
            }
            // Other element sorts: rely on observed constants only (no synthesized
            // fresh character). Sound — just fewer disequality options.
            _ => {}
        }
    }
    observed
}

// ----- ground-evaluator + structural helpers ---------------------------------

/// Every `Seq`-sorted symbol appearing in the assertions, as `(id, term)`,
/// deduplicated and in first-appearance order.
fn collect_seq_symbols(
    arena: &TermArena,
    equalities: &[(TermId, TermId)],
    disequalities: &[(TermId, TermId)],
) -> Vec<(SymbolId, TermId)> {
    let mut seen: BTreeSet<SymbolId> = BTreeSet::new();
    let mut out: Vec<(SymbolId, TermId)> = Vec::new();
    let mut stack: Vec<TermId> = Vec::new();
    for &(a, b) in equalities.iter().chain(disequalities) {
        stack.push(a);
        stack.push(b);
    }
    let mut visited: BTreeSet<TermId> = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        if let TermNode::Symbol(s) = *arena.node(t)
            && matches!(arena.sort_of(t), Sort::Seq(_))
            && seen.insert(s)
        {
            out.push((s, t));
        }
        if let TermNode::App { args, .. } = arena.node(t) {
            for &a in args {
                stack.push(a);
            }
        }
    }
    out
}

/// The element key of a `Seq`-sorted term, if any.
fn seq_key(arena: &TermArena, t: TermId) -> Option<ArraySortKey> {
    match arena.sort_of(t) {
        Sort::Seq(k) => Some(k),
        _ => None,
    }
}

/// Any element key present in the instance (from the first original symbol, else
/// an assertion endpoint).
fn any_seq_key(arena: &TermArena, ctx: &Ctx) -> Option<ArraySortKey> {
    if let Some(&(_, t)) = ctx.orig_symbols.first() {
        return seq_key(arena, t);
    }
    ctx.orig_equalities
        .iter()
        .chain(ctx.orig_disequalities)
        .find_map(|&(a, _)| seq_key(arena, a))
}

/// The empty sequence over `t`'s element key, or `None` if `t` is not a
/// sequence.
fn epsilon_like(arena: &mut TermArena, t: TermId) -> Option<TermId> {
    let key = seq_key(arena, t)?;
    Some(arena.seq_empty(key))
}

/// The scalar code of an element value, if it is scalar (for alphabet dedup).
fn scalar_code_of(v: &Value) -> Option<u128> {
    match v {
        Value::Bool(_) | Value::Bv { .. } => Some(v.scalar_code()),
        _ => None,
    }
}

/// The closed value of `term`, or `None` if it does not evaluate closed.
fn value_of(arena: &TermArena, term: TermId) -> Option<Value> {
    axeyum_ir::eval(arena, term, &Assignment::new()).ok()
}

/// Evaluates `term` under `asg`, mapping any evaluation error to `None` so a
/// replay never panics.
fn value_eval(arena: &TermArena, term: TermId, asg: &Assignment) -> Option<Value> {
    axeyum_ir::eval(arena, term, asg).ok()
}

/// Whether `term` evaluates closed (the constancy test).
fn is_constant(arena: &TermArena, term: TermId) -> bool {
    value_of(arena, term).is_some()
}

/// Whether `term` is the (constant) empty sequence.
fn is_epsilon(arena: &TermArena, term: TermId) -> bool {
    matches!(value_of(arena, term), Some(Value::Seq(v)) if v.is_empty())
        || matches!(
            arena.node(term),
            TermNode::App {
                op: Op::SeqEmpty(_),
                ..
            }
        )
}

/// Whether `rep`'s class contains an ε member.
fn class_is_epsilon(classes: &Classes, arena: &TermArena, rep: TermId) -> bool {
    classes
        .class_members(rep)
        .into_iter()
        .any(|m| is_epsilon(arena, m))
}

/// Whether `rep`'s class is already the ε class (a target already forced empty).
fn already_epsilon(classes: &Classes, arena: &TermArena, t: TermId) -> bool {
    class_is_epsilon(classes, arena, classes.representative(t)) || is_epsilon(arena, t)
}

/// A non-ε constant member of `rep`'s class (the class's forced constant value),
/// if any.
fn class_constant_atom(classes: &Classes, arena: &TermArena, rep: TermId) -> Option<TermId> {
    classes
        .class_members(rep)
        .into_iter()
        .find(|&m| is_constant(arena, m) && !is_epsilon(arena, m))
}

/// The per-character `seq.unit` terms of a constant sequence term: normalizes,
/// then flattens the concatenation spine into its non-ε length-1 leaves.
fn char_units(arena: &mut TermArena, cterm: TermId) -> Vec<TermId> {
    let norm = normalize(arena, cterm);
    flatten_units(arena, norm)
}

/// Flattens a `Seq` term's concatenation spine into its non-ε leaf components,
/// left to right.
fn flatten_units(arena: &TermArena, term: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    // Push right then left so the left subtree pops first (left-to-right order).
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        match arena.node(t) {
            TermNode::App {
                op: Op::SeqConcat,
                args,
            } => {
                stack.push(args[1]);
                stack.push(args[0]);
            }
            TermNode::App {
                op: Op::SeqEmpty(_),
                ..
            } => {}
            _ => out.push(t),
        }
    }
    out
}

/// Collects the distinct scalar element values of every constant `seq.unit`
/// subterm of `term` into `observed` (deduplicated by scalar code via `used`).
fn collect_chars(
    arena: &TermArena,
    term: TermId,
    used: &mut BTreeSet<u128>,
    observed: &mut Vec<Value>,
) {
    let mut visited: BTreeSet<TermId> = BTreeSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        // A constant `seq.unit` evaluates to a one-element sequence.
        if matches!(
            arena.node(t),
            TermNode::App {
                op: Op::SeqUnit,
                ..
            }
        ) && let Some(Value::Seq(v)) = value_of(arena, t)
            && let Some(e) = v.into_iter().next()
            && let Some(code) = scalar_code_of(&e)
            && used.insert(code)
        {
            observed.push(e);
        }
        if let TermNode::App { args, .. } = arena.node(t) {
            for &a in args {
                stack.push(a);
            }
        }
    }
}
