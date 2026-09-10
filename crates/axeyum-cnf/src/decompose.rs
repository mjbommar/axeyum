//! Equivalent-literal substitution over the binary implication graph
//! (`CaDiCaL`'s `decompose.cpp`), as a **proof-carrying** pass.
//!
//! # What it does
//!
//! Every binary clause `(a ∨ b)` is two implications, `¬a → b` and `¬b → a`. Run
//! Tarjan over the resulting graph on `2n` literal nodes and every strongly
//! connected component is a set of *equivalent* literals: each implies every
//! other. Pick one representative per component, rewrite every clause through
//! it, and the formula loses one variable per non-representative member — plus
//! whatever clauses collapse to tautologies or to duplicates of each other.
//!
//! Two structural facts do the work and both are used below:
//!
//! * The graph is **skew-symmetric**: `u → v` is an edge exactly when `¬v → ¬u`
//!   is. So `u ~ v` iff `¬u ~ ¬v`, and the component of `¬l` is precisely the
//!   negation of the component of `l`. Choosing each component's representative
//!   as its **minimum-variable literal** therefore makes `repr(¬l) = ¬repr(l)`
//!   fall out rather than having to be imposed — the two dual components hold
//!   the two polarities of the same minimum variable.
//! * A component holding both `x` and `¬x` means `x → ¬x` and `¬x → x`, which is
//!   a refutation. That case is **not** a substitution; it is `unsat`, and this
//!   module emits the three-step `DRAT` derivation of the empty clause for it.
//!
//! # Why this pass and not another
//!
//! It is the cheapest of the inprocessing passes we lack — one linear pass over
//! the binary clauses — and it is the one every other pass *feeds*: subsumption,
//! vivification and BVE all shorten clauses, and a clause shortened to two
//! literals is a new edge in this graph. `CaDiCaL` re-runs `decompose()` five
//! times per `inprobe` round for exactly that reason.
//!
//! # The proof obligation, which is the hard part
//!
//! Substituting `y := x` because `x ↔ y` rewrites clauses, and a rewritten
//! clause that no checker can justify turns an accepted certificate into a
//! decoration. Every step this pass emits is plain **`RUP`** — no `RAT`, no
//! extension variable — and the emission **order** is what makes each one
//! derivable from what precedes it:
//!
//! 1. **First**, for each substituted variable `v` with representative `r`, the
//!    two equivalence binaries `(¬v ∨ r)` and `(v ∨ ¬r)`. Each is `RUP`: assume
//!    its negation and unit propagation walks the implication path that put `v`
//!    and `r` in one component. This happens while **every original binary
//!    clause is still live**, which is what those propagations need.
//! 2. **Then**, per rewritten clause, `Add(C')` followed by `Delete(C)`. `C'` is
//!    `RUP` against the equivalence binaries alone: falsifying every literal of
//!    `C'` propagates each literal of `C` false through one binary from step 1,
//!    so the still-live `C` is the conflict.
//!
//! The equivalence binaries are **never deleted**. They are not part of the
//! reduced formula the search runs over, but leaving them live in the checker's
//! clause set costs nothing and keeps every later `Add(C')` justified no matter
//! how the deletions interleave. A `DRAT` active set that is a superset of the
//! reduced formula is exactly what [`crate::ReductionLink::check_unsat`] needs
//! when it concatenates the search's own steps onto this prefix.
//!
//! # The model direction
//!
//! Substitution is **equisatisfiable, not model-preserving**: a substituted
//! variable does not occur in the reduced formula at all, so a model of the
//! reduced formula says nothing about it. [`EquivalenceMap::extend`] fills those
//! slots from their representatives, and a caller that forgets to call it ships
//! an unreplayable model. That is why the map is returned rather than being an
//! implementation detail, and why [`crate::ScheduledInprocess::lift_model`]
//! exists to apply the whole lift stack in one call and in the right order.
//!
//! # Admission
//!
//! This pass carries no valve of its own. Roadmap item 1.5's
//! [`crate::ticks::TickValveAccount`] is the shared admission rule — accumulate
//! a per-mille slice of the ticks the SEARCH has spent since this pass last ran,
//! refuse below `threshold x clauses`, back off exponentially on a round that
//! finds nothing — and `crate::inprocess`'s `TickValve` drives it through
//! [`crate::InprocessObserver::decompose_grant`]. A [`DecomposeOptions`] budget
//! is what comes out the other side.
//!
//! # Determinism
//!
//! Node order, edge order, component order and the representative rule are all
//! index-ordered, and the work meter is [`crate::pass_work::PassWork`] — a
//! deterministic step count, not a clock. A fixed formula and fixed
//! [`DecomposeOptions`] give a fixed reduced formula and a fixed step sequence
//! on any host.

use crate::pass_work::PassWork;
use crate::{CnfClause, CnfFormula, CnfLit, CnfVar, DratStep};

/// Sentinel for "no index yet" in the Tarjan arrays.
const NONE: u32 = u32::MAX;

/// Literal code: `2 * var + (negated as 1)`. Increasing code order is increasing
/// variable order, which is what makes the minimum-variable representative rule
/// a single forward scan.
#[inline]
fn code_of(lit: CnfLit) -> usize {
    lit.var().index() * 2 + if lit.is_negated() { 1 } else { 0 }
}

/// Inverse of [`code_of`]. Infallible for any code produced from a literal of a
/// formula this pass was handed.
#[inline]
fn lit_of(code: usize) -> CnfLit {
    let positive = CnfLit::positive(CnfVar::new(code / 2).expect("code came from a literal"));
    if code % 2 == 1 {
        positive.negated()
    } else {
        positive
    }
}

/// How hard the pass may work, and when it declines outright.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecomposeOptions {
    /// Occurrence-graph steps the pass may spend; `None` is unbounded.
    ///
    /// Charged in the same unit as [`crate::pass_work`]'s other consumers: one
    /// per node visited, one per edge traversed, one per literal rewritten. A
    /// budget below the graph's construction cost stops the pass after setup,
    /// which is reported as [`DecomposeStats::work_exhausted`] rather than
    /// silently producing a partial substitution — a partial Tarjan is not a
    /// partial answer, so the pass returns the formula unchanged instead.
    pub work_budget: Option<u64>,
    /// Rounds of substitute-then-rebuild. A rewrite can shorten a clause to two
    /// literals, which is a new edge, so a second round can find components the
    /// first could not. One round is the common case; the cap bounds the rest.
    pub max_rounds: usize,
}

impl DecomposeOptions {
    /// Unbudgeted, four rounds.
    pub const DEFAULT: Self = Self {
        work_budget: None,
        max_rounds: 4,
    };
}

impl Default for DecomposeOptions {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// What a [`decompose_within_recorded`] run did. Every field is a plain count,
/// so a test can state the expected value in advance rather than read it off the
/// output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct DecomposeStats {
    /// Whether the pass ran at all (false when the formula has no binary clause
    /// or the budget did not cover graph construction).
    pub ran: bool,
    /// Rounds that built a graph and ran Tarjan. The last of these is normally
    /// the round that found nothing — a round is what *establishes* that there
    /// is no further equivalence, so counting only fruitful ones would report a
    /// pass that stopped early and one that reached its fixpoint identically.
    pub rounds: usize,
    /// Binary clauses in the **first** round's graph. The first round is the
    /// one whose graph describes the caller's formula; a later round's count
    /// describes a formula only this pass has ever seen.
    pub binary_clauses: usize,
    /// Equivalence classes with more than one variable, summed over rounds.
    /// This is the *k* an exit criterion counts.
    pub classes: usize,
    /// Variables that no longer occur in the reduced formula. For `k` classes of
    /// sizes `s_1..s_k` this is `sum(s_i) - k`.
    pub variables_substituted: usize,
    /// Clauses whose literals changed and which survived (`Add`+`Delete`).
    pub clauses_rewritten: usize,
    /// Clauses dropped as tautologies after substitution (`Delete` only).
    pub clauses_removed: usize,
    /// `DRAT` steps emitted.
    pub proof_steps: usize,
    /// Work charged, setup included.
    pub work_spent: u64,
    /// Whether the budget stopped the pass.
    pub work_exhausted: bool,
    /// Whether a component held both polarities of one variable — a refutation.
    pub unsat: bool,
}

/// The literal each substituted variable is equal to, and the model lift that
/// undoes the substitution.
///
/// `repr[v] == Some(l)` means variable `v` was replaced by literal `l` and no
/// longer occurs in the reduced formula. `l`'s own variable may itself have been
/// substituted in a **later** round, so [`Self::extend`] follows the chain
/// rather than reading one hop.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EquivalenceMap {
    repr: Vec<Option<CnfLit>>,
}

impl EquivalenceMap {
    /// An empty map over `variable_count` variables: nothing was substituted.
    #[must_use]
    pub fn identity(variable_count: usize) -> Self {
        Self {
            repr: vec![None; variable_count],
        }
    }

    /// Whether no variable was substituted, in which case [`Self::extend`] is
    /// the identity and a caller that skips it is still correct.
    #[must_use]
    pub fn is_identity(&self) -> bool {
        self.repr.iter().all(Option::is_none)
    }

    /// How many variables were substituted away.
    #[must_use]
    pub fn substituted_count(&self) -> usize {
        self.repr.iter().filter(|slot| slot.is_some()).count()
    }

    /// The literal `var` was replaced by, one hop, or `None` if it survived.
    #[must_use]
    pub fn representative(&self, var: CnfVar) -> Option<CnfLit> {
        self.repr.get(var.index()).copied().flatten()
    }

    /// Records `var == lit`.
    ///
    /// # Panics
    ///
    /// Panics if `var` already has a representative. A substituted variable does
    /// not occur in the reduced formula, so a later round cannot see it — a
    /// second write means the rounds disagree about which formula they ran over,
    /// and continuing would produce a map whose chain does not terminate.
    fn substitute(&mut self, var: CnfVar, lit: CnfLit) {
        assert!(
            self.repr[var.index()].is_none(),
            "variable {} substituted twice",
            var.index()
        );
        self.repr[var.index()] = Some(lit);
    }

    /// Extends a model of the reduced formula to one of the pre-substitution
    /// formula, filling every substituted slot from its representative.
    ///
    /// `reduced_model` is indexed by zero-based CNF variable, as
    /// [`crate::CnfAssignment::values`]. Substituted slots may hold arbitrary
    /// placeholders on input — they are overwritten.
    ///
    /// Chains are followed to their end, so the order rounds ran in does not
    /// matter to the caller. The walk is bounded by the map's own length, which
    /// it cannot exceed: each hop moves to a variable substituted in a strictly
    /// later round, and the rounds are finite.
    #[must_use]
    pub fn extend(&self, reduced_model: &[bool]) -> Vec<bool> {
        let mut full = reduced_model.to_vec();
        full.resize(self.repr.len().max(reduced_model.len()), false);
        for index in 0..self.repr.len() {
            if self.repr[index].is_none() {
                continue;
            }
            let mut cursor = CnfLit::positive(CnfVar::new(index).expect("index is in range"));
            let mut hops = 0usize;
            while let Some(next) = self.repr[cursor.var().index()] {
                cursor = if cursor.is_negated() {
                    next.negated()
                } else {
                    next
                };
                hops += 1;
                assert!(
                    hops <= self.repr.len(),
                    "equivalence chain does not terminate"
                );
            }
            let value = full[cursor.var().index()] != cursor.is_negated();
            full[index] = value;
        }
        full
    }
}

/// The reduced formula, the model lift, and the accounting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecomposeOutcome {
    /// The reduced formula. Same `variable_count` as the input — this pass
    /// substitutes but never renumbers, so a `DRAT` step over it is literally
    /// about the caller's variables. `crate::compact` is what turns a
    /// substituted variable into a smaller `variable_count`.
    ///
    /// When [`DecomposeStats::unsat`] is set this is the input formula verbatim:
    /// the refutation is in the emitted proof, not in the formula.
    pub formula: CnfFormula,
    /// Lifts a model of [`Self::formula`] to a model of the input formula.
    pub equivalences: EquivalenceMap,
    /// What the pass did.
    pub stats: DecomposeStats,
}

impl DecomposeOutcome {
    /// The outcome of **not running** the pass: the formula verbatim, an
    /// identity map, all-zero stats.
    #[must_use]
    pub fn skipped(formula: &CnfFormula) -> Self {
        Self {
            formula: formula.clone(),
            equivalences: EquivalenceMap::identity(formula.variable_count()),
            stats: DecomposeStats::default(),
        }
    }

    /// How many variables still occur in [`Self::formula`].
    ///
    /// The number an exit criterion means by "the variable count", as opposed to
    /// `variable_count`, which this pass does not move.
    #[must_use]
    pub fn occurring_variables(&self) -> usize {
        occurring_variables(&self.formula)
    }
}

/// Variables with at least one occurrence in `formula`.
fn occurring_variables(formula: &CnfFormula) -> usize {
    let mut seen = vec![false; formula.variable_count()];
    for clause in formula.clauses() {
        for lit in clause.lits() {
            seen[lit.var().index()] = true;
        }
    }
    seen.iter().filter(|s| **s).count()
}

/// Runs the pass with [`DecomposeOptions::DEFAULT`] and no proof recording.
#[must_use]
pub fn decompose(formula: &CnfFormula) -> DecomposeOutcome {
    decompose_within_recorded(formula, DecomposeOptions::DEFAULT, None)
}

/// Runs equivalent-literal substitution, appending the pass's `RUP` derivation
/// to `proof` in derivation order.
///
/// The derivation order is the contract stated in the module docs: all
/// equivalence binaries first, while the original binaries that justify them are
/// still live; then `Add(C')` before `Delete(C)` for each rewritten clause.
///
/// A [`DecomposeStats::unsat`] outcome means a component held both polarities of
/// one variable. The proof then holds a complete refutation — `Add([¬x])`,
/// `Add([x])`, `Add([])` — and the returned formula is the input unchanged, so a
/// caller that ignores the flag loses the refutation but cannot act on a wrong
/// formula.
#[must_use]
pub fn decompose_within_recorded(
    formula: &CnfFormula,
    options: DecomposeOptions,
    mut proof: Option<&mut Vec<DratStep>>,
) -> DecomposeOutcome {
    let mut equivalences = EquivalenceMap::identity(formula.variable_count());
    let mut stats = DecomposeStats::default();
    let mut current = formula.clone();

    for _ in 0..options.max_rounds {
        let round = decompose_round(
            &current,
            options.work_budget,
            &mut equivalences,
            proof.as_deref_mut(),
        );
        stats.ran |= round.ran;
        if stats.rounds == 0 {
            stats.binary_clauses = round.binary_clauses;
        }
        stats.classes += round.classes;
        stats.variables_substituted += round.variables_substituted;
        stats.clauses_rewritten += round.clauses_rewritten;
        stats.clauses_removed += round.clauses_removed;
        stats.proof_steps += round.proof_steps;
        stats.work_spent = stats.work_spent.saturating_add(round.work_spent);
        stats.work_exhausted |= round.work_exhausted;
        if round.ran {
            stats.rounds += 1;
        }
        if round.unsat {
            stats.unsat = true;
            // The refutation is in the proof. Hand back the formula this round
            // started from: it is the one the proof's `Add`s were checked
            // against, and a partially rewritten formula would not be.
            return DecomposeOutcome {
                formula: current,
                equivalences,
                stats,
            };
        }
        if round.variables_substituted == 0 {
            break;
        }
        current = round.formula;
    }

    DecomposeOutcome {
        formula: current,
        equivalences,
        stats,
    }
}

/// One round's result. Private: the public shape is [`DecomposeOutcome`].
struct RoundOutcome {
    formula: CnfFormula,
    ran: bool,
    binary_clauses: usize,
    classes: usize,
    variables_substituted: usize,
    clauses_rewritten: usize,
    clauses_removed: usize,
    proof_steps: usize,
    work_spent: u64,
    work_exhausted: bool,
    unsat: bool,
}

impl RoundOutcome {
    fn nothing(formula: &CnfFormula, work: &PassWork, ran: bool, binary_clauses: usize) -> Self {
        Self {
            formula: formula.clone(),
            ran,
            binary_clauses,
            classes: 0,
            variables_substituted: 0,
            clauses_rewritten: 0,
            clauses_removed: 0,
            proof_steps: 0,
            work_spent: work.spent(),
            work_exhausted: work.exhausted(),
            unsat: false,
        }
    }
}

/// The binary implication graph in CSR form, over `2 * variable_count` nodes.
struct ImplicationGraph {
    /// `start[c]..start[c + 1]` indexes `edges` for literal code `c`.
    start: Vec<u32>,
    edges: Vec<u32>,
    binary_clauses: usize,
}

/// Builds the implication graph, charging `work` per clause scanned and per edge
/// written. Returns `None` when the budget ran out during construction — a
/// partial graph would give a partial Tarjan, which is not a partial answer.
fn build_graph(formula: &CnfFormula, work: &mut PassWork) -> Option<ImplicationGraph> {
    let nodes = formula.variable_count() * 2;
    let mut degree = vec![0u32; nodes + 1];
    let mut binary_clauses = 0usize;
    for clause in formula.clauses() {
        work.charge(1);
        let lits = clause.lits();
        if lits.len() != 2 {
            continue;
        }
        // A binary clause with a repeated literal `(a ∨ a)` is the unit `a`, not
        // an implication; a tautological `(a ∨ ¬a)` is no constraint at all.
        // Both would put a self-loop in the graph and neither is an equivalence.
        if lits[0].var() == lits[1].var() {
            continue;
        }
        binary_clauses += 1;
        // (a ∨ b) is ¬a → b and ¬b → a.
        degree[code_of(lits[0].negated())] += 1;
        degree[code_of(lits[1].negated())] += 1;
    }
    if work.must_stop() {
        return None;
    }

    let mut start = vec![0u32; nodes + 1];
    let mut running = 0u32;
    for node in 0..nodes {
        start[node] = running;
        running += degree[node];
    }
    start[nodes] = running;

    let mut cursor = start.clone();
    let mut edges = vec![0u32; running as usize];
    for clause in formula.clauses() {
        let lits = clause.lits();
        if lits.len() != 2 || lits[0].var() == lits[1].var() {
            continue;
        }
        work.charge(2);
        for (from, to) in [(0usize, 1usize), (1, 0)] {
            let tail = code_of(lits[from].negated());
            let head = code_of(lits[to]);
            edges[cursor[tail] as usize] = u32::try_from(head).expect("literal code fits u32");
            cursor[tail] += 1;
        }
    }
    if work.must_stop() {
        return None;
    }

    Some(ImplicationGraph {
        start,
        edges,
        binary_clauses,
    })
}

/// Iterative Tarjan over the implication graph.
///
/// Iterative rather than recursive on purpose: the graph has one node per
/// literal, so a corpus-scale instance is millions of nodes and a recursive
/// depth-first search on it is a stack overflow, not a slow run. Returns
/// `comp[code]` for every literal code and the component count, or `None` if the
/// budget ran out mid-walk.
fn strongly_connected(graph: &ImplicationGraph, work: &mut PassWork) -> Option<(Vec<u32>, u32)> {
    let nodes = graph.start.len() - 1;
    let mut index = vec![NONE; nodes];
    let mut lowlink = vec![NONE; nodes];
    let mut on_stack = vec![false; nodes];
    let mut comp = vec![NONE; nodes];
    let mut stack: Vec<u32> = Vec::new();
    // (node, next edge slot to examine)
    let mut frames: Vec<(u32, u32)> = Vec::new();
    let mut next_index = 0u32;
    let mut comp_count = 0u32;

    for root in 0..nodes {
        if index[root] != NONE {
            continue;
        }
        work.charge(1);
        if work.must_stop() {
            return None;
        }
        index[root] = next_index;
        lowlink[root] = next_index;
        next_index += 1;
        stack.push(u32::try_from(root).expect("node fits u32"));
        on_stack[root] = true;
        frames.push((
            u32::try_from(root).expect("node fits u32"),
            graph.start[root],
        ));

        while let Some(&mut (node, ref mut edge_cursor)) = frames.last_mut() {
            let v = node as usize;
            if *edge_cursor < graph.start[v + 1] {
                let w = graph.edges[*edge_cursor as usize] as usize;
                *edge_cursor += 1;
                work.charge(1);
                if work.must_stop() {
                    return None;
                }
                if index[w] == NONE {
                    index[w] = next_index;
                    lowlink[w] = next_index;
                    next_index += 1;
                    stack.push(u32::try_from(w).expect("node fits u32"));
                    on_stack[w] = true;
                    frames.push((u32::try_from(w).expect("node fits u32"), graph.start[w]));
                } else if on_stack[w] {
                    lowlink[v] = lowlink[v].min(index[w]);
                }
                continue;
            }

            if lowlink[v] == index[v] {
                loop {
                    let popped = stack.pop().expect("component member on the stack") as usize;
                    on_stack[popped] = false;
                    comp[popped] = comp_count;
                    if popped == v {
                        break;
                    }
                }
                comp_count += 1;
            }
            frames.pop();
            if let Some(&mut (parent, _)) = frames.last_mut() {
                let p = parent as usize;
                lowlink[p] = lowlink[p].min(lowlink[v]);
            }
        }
    }

    Some((comp, comp_count))
}

/// One substitution round: build the graph, find the components, emit the
/// derivation, rewrite the clauses.
fn decompose_round(
    formula: &CnfFormula,
    budget: Option<u64>,
    equivalences: &mut EquivalenceMap,
    mut proof: Option<&mut Vec<DratStep>>,
) -> RoundOutcome {
    // Setup is charged up front, for the reason `PassWork::with_setup` gives:
    // an admission test reading a meter that started at zero after setup would
    // be comparing a budget against a cost it had excluded.
    let setup =
        u64::try_from(formula.clauses().len() + formula.variable_count()).unwrap_or(u64::MAX);
    let mut work = PassWork::with_setup(setup, budget);

    let Some(graph) = build_graph(formula, &mut work) else {
        return RoundOutcome::nothing(formula, &work, false, 0);
    };
    let binary_clauses = graph.binary_clauses;
    if binary_clauses == 0 {
        // No edges, so every component is a singleton and no substitution is
        // possible. This is the cheap refusal path: one scan, no Tarjan.
        return RoundOutcome::nothing(formula, &work, false, 0);
    }

    let Some((comp, comp_count)) = strongly_connected(&graph, &mut work) else {
        return RoundOutcome::nothing(formula, &work, true, binary_clauses);
    };

    // --- x and ¬x in one component is a refutation, not a substitution -------
    for var in 0..formula.variable_count() {
        work.charge(1);
        if comp[var * 2] == comp[var * 2 + 1] {
            let positive = CnfLit::positive(CnfVar::new(var).expect("var is in range"));
            let mut steps = 0usize;
            if let Some(sink) = proof.as_deref_mut() {
                // `x → ¬x` makes `(¬x)` RUP: assume `x`, propagate the path,
                // reach `¬x`. `¬x → x` makes `(x)` RUP the same way. The two
                // units then conflict, so the empty clause is RUP.
                sink.push(DratStep::Add(vec![positive.negated()]));
                sink.push(DratStep::Add(vec![positive]));
                sink.push(DratStep::Add(Vec::new()));
                steps = 3;
            }
            return RoundOutcome {
                formula: formula.clone(),
                ran: true,
                binary_clauses,
                classes: 0,
                variables_substituted: 0,
                clauses_rewritten: 0,
                clauses_removed: 0,
                proof_steps: steps,
                work_spent: work.spent(),
                work_exhausted: work.exhausted(),
                unsat: true,
            };
        }
    }

    // --- representatives: the minimum-variable literal of each component -----
    // Scanning codes in increasing order visits variables in increasing order,
    // so the first literal seen for a component is its minimum-variable one.
    // Duality (`repr(¬l) = ¬repr(l)`) follows: the dual component holds the
    // other polarity of the same minimum variable, and the `x`/`¬x` scan above
    // has already ruled out a component holding both.
    let nodes = formula.variable_count() * 2;
    let mut repr_of_comp = vec![NONE; comp_count as usize];
    for code in 0..nodes {
        let c = comp[code] as usize;
        if repr_of_comp[c] == NONE {
            repr_of_comp[c] = u32::try_from(code).expect("code fits u32");
        }
    }
    let repr_code = |code: usize| repr_of_comp[comp[code] as usize] as usize;
    debug_assert!(
        (0..nodes).all(|code| repr_code(code ^ 1) == repr_code(code) ^ 1),
        "representatives must respect duality"
    );

    // --- emit the equivalence binaries, then substitute ----------------------
    let mut proof_steps = 0usize;
    let mut classes = 0usize;
    let mut substituted: Vec<(CnfVar, CnfLit)> = Vec::new();
    let mut counted_comp = vec![false; comp_count as usize];
    for var in 0..formula.variable_count() {
        work.charge(1);
        let positive_code = var * 2;
        let target = repr_code(positive_code);
        if target == positive_code {
            continue;
        }
        let component = comp[positive_code] as usize;
        if !counted_comp[component] {
            counted_comp[component] = true;
            classes += 1;
        }
        let v = CnfLit::positive(CnfVar::new(var).expect("var is in range"));
        let r = lit_of(target);
        substituted.push((v.var(), r));
        if let Some(sink) = proof.as_deref_mut() {
            sink.push(DratStep::Add(vec![v.negated(), r]));
            sink.push(DratStep::Add(vec![v, r.negated()]));
            proof_steps += 2;
        }
        work.note_progress();
    }

    if substituted.is_empty() {
        return RoundOutcome::nothing(formula, &work, true, binary_clauses);
    }

    // --- rewrite every clause through the representatives --------------------
    let mut reduced = CnfFormula::new(formula.variable_count());
    let mut clauses_rewritten = 0usize;
    let mut clauses_removed = 0usize;
    let mut mapped: Vec<CnfLit> = Vec::new();
    for clause in formula.clauses() {
        let lits = clause.lits();
        work.charge(u64::try_from(lits.len()).unwrap_or(1));
        mapped.clear();
        let mut changed = false;
        let mut tautology = false;
        for &lit in lits {
            let image = lit_of(repr_code(code_of(lit)));
            if image != lit {
                changed = true;
            }
            if mapped.iter().any(|&seen| seen == image.negated()) {
                tautology = true;
                break;
            }
            if mapped.iter().any(|&seen| seen == image) {
                // A duplicate literal is a change even when the image is not:
                // the checker propagates literals verbatim, so `(b ∨ b)` and
                // `(b)` are different clauses to it.
                changed = true;
                continue;
            }
            mapped.push(image);
        }

        if tautology {
            if let Some(sink) = proof.as_deref_mut() {
                sink.push(DratStep::Delete(lits.to_vec()));
                proof_steps += 1;
            }
            clauses_removed += 1;
            continue;
        }
        if !changed {
            reduced
                .add_clause(clause.clone())
                .expect("literals are unchanged");
            continue;
        }
        if let Some(sink) = proof.as_deref_mut() {
            sink.push(DratStep::Add(mapped.clone()));
            sink.push(DratStep::Delete(lits.to_vec()));
            proof_steps += 2;
        }
        reduced
            .add_clause(CnfClause::new(mapped.clone()))
            .expect("images are variables of the same formula");
        clauses_rewritten += 1;
    }

    for (var, lit) in &substituted {
        equivalences.substitute(*var, *lit);
    }

    RoundOutcome {
        formula: reduced,
        ran: true,
        binary_clauses,
        classes,
        variables_substituted: substituted.len(),
        clauses_rewritten,
        clauses_removed,
        proof_steps,
        work_spent: work.spent(),
        work_exhausted: work.exhausted(),
        unsat: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{check_drat, check_drat_backward};

    fn v(i: usize) -> CnfVar {
        CnfVar::new(i).expect("var")
    }
    fn p(i: usize) -> CnfLit {
        CnfLit::positive(v(i))
    }
    fn n(i: usize) -> CnfLit {
        CnfLit::positive(v(i)).negated()
    }
    fn formula(nvars: usize, clauses: &[&[CnfLit]]) -> CnfFormula {
        let mut f = CnfFormula::new(nvars);
        for c in clauses {
            f.add_clause(CnfClause::new(c.to_vec())).expect("in range");
        }
        f
    }

    /// `x0 ↔ x1` written as the two binaries, plus payload clauses that survive
    /// the substitution without creating a *new* equivalence — so a second round
    /// finds nothing and every count below is the first round's.
    fn one_class() -> CnfFormula {
        formula(
            4,
            &[
                &[n(0), p(1)],
                &[p(0), n(1)],
                &[p(0), p(1), p(2)],
                &[n(1), p(2), p(3)],
                &[p(2), n(3)],
            ],
        )
    }

    #[test]
    fn a_single_equivalence_substitutes_one_variable() {
        let f = one_class();
        let out = decompose(&f);
        assert!(out.stats.ran);
        assert_eq!(out.stats.classes, 1);
        assert_eq!(out.stats.variables_substituted, 1);
        assert_eq!(out.equivalences.substituted_count(), 1);
        // x1 is substituted by x0: the minimum-variable representative.
        assert_eq!(out.equivalences.representative(v(1)), Some(p(0)));
        assert_eq!(out.equivalences.representative(v(0)), None);
        // Two rounds ran: the substitution shortened `(x0 ∨ x1 ∨ x2)` to a
        // binary, so a second graph was worth building. It found no new
        // component, which is why `variables_substituted` is still 1.
        assert_eq!(out.stats.rounds, 2);
        // Both equivalence binaries became tautologies and left.
        assert_eq!(out.stats.clauses_removed, 2);
        assert_eq!(out.stats.clauses_rewritten, 2);
        // 4 variables, 1 substituted.
        assert_eq!(out.occurring_variables(), 3);
    }

    #[test]
    fn the_derivation_checks_forward_and_backward_against_the_original() {
        let f = one_class();
        let mut proof = Vec::new();
        let out = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut proof));
        assert!(out.stats.proof_steps > 0);
        assert_eq!(out.stats.proof_steps, proof.len());
        // `Ok(false)` is the right answer here: every step verifies, and the
        // pass did not derive the empty clause because the formula is
        // satisfiable. Only `Err` is a soundness alarm.
        assert_eq!(check_drat(&f, &proof), Ok(false));
        assert_eq!(check_drat_backward(&f, &proof), Ok(false));
    }

    #[test]
    fn every_added_clause_is_rup_in_the_order_it_was_emitted() {
        // The ordering claim in the module docs, checked step by step: each
        // prefix of the proof must verify on its own, which is exactly what
        // `check_drat` does when it walks the steps in order.
        let f = one_class();
        let mut proof = Vec::new();
        let _ = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut proof));
        for cut in 1..=proof.len() {
            assert!(
                check_drat(&f, &proof[..cut]).is_ok(),
                "prefix of {cut} steps failed to verify"
            );
        }
    }

    #[test]
    fn a_substituted_model_lifts_back_to_the_original_formula() {
        let f = one_class();
        let out = decompose(&f);
        // Enumerate every model of the reduced formula; each must lift to a
        // model of the original.
        let width = f.variable_count();
        let mut lifted_any = false;
        for mask in 0u32..(1 << width) {
            let assignment: Vec<bool> = (0..width).map(|i| mask >> i & 1 == 1).collect();
            if !out.formula.evaluate(&assignment).expect("width") {
                continue;
            }
            let full = out.equivalences.extend(&assignment);
            assert!(
                f.evaluate(&full).expect("width"),
                "lifted model {full:?} does not satisfy the original"
            );
            lifted_any = true;
        }
        assert!(lifted_any, "the reduced formula must have a model");
    }

    #[test]
    fn a_component_holding_both_polarities_refutes_the_formula() {
        // x0 → x1 → ¬x0 and ¬x0 → ¬x1 → x0: one component with x0 and ¬x0.
        let f = formula(
            2,
            &[&[n(0), p(1)], &[n(1), n(0)], &[p(0), n(1)], &[p(1), p(0)]],
        );
        let mut proof = Vec::new();
        let out = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut proof));
        assert!(out.stats.unsat);
        assert_eq!(out.stats.variables_substituted, 0);
        assert_eq!(proof.len(), 3);
        assert_eq!(proof[2], DratStep::Add(Vec::new()));
        // A complete refutation of the original formula: `Ok(true)` is the
        // checker saying the empty clause was derived, not merely that the
        // steps verified.
        assert_eq!(check_drat(&f, &proof), Ok(true));
        assert_eq!(check_drat_backward(&f, &proof), Ok(true));
    }

    #[test]
    fn a_formula_with_no_equivalence_is_left_byte_identical_and_costs_little() {
        // Binaries, but no cycle: no component has two members.
        let f = formula(
            4,
            &[&[n(0), p(1)], &[n(1), p(2)], &[p(2), p(3)], &[n(3), p(0)]],
        );
        let mut proof = Vec::new();
        let out = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut proof));
        assert!(proof.is_empty(), "nothing to justify, so nothing emitted");
        assert_eq!(out.formula, f, "the formula must come back untouched");
        assert!(out.equivalences.is_identity());
        assert_eq!(out.stats.variables_substituted, 0);
        assert_eq!(out.stats.rounds, 1, "one round, then it stops");
        // Cost is linear in the formula, not in the variable space.
        assert!(
            out.stats.work_spent < 200,
            "no-equivalence run spent {} units on a 4-clause formula",
            out.stats.work_spent
        );
    }

    #[test]
    fn a_second_round_finds_what_the_first_round_created() {
        // (x0 ∨ x1 ∨ x2) with x1 ≡ x2 becomes binary after substitution, which
        // is a new edge. Pair it so the new binary closes a cycle with x0.
        let f = formula(
            3,
            &[
                &[n(1), p(2)],
                &[p(1), n(2)],
                // becomes (¬x0 ∨ x1) once x2 := x1
                &[n(0), p(1), p(2)],
                &[p(0), n(1)],
                &[p(0), p(1), p(2)],
            ],
        );
        let mut proof = Vec::new();
        let out = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut proof));
        assert_eq!(
            out.stats.rounds, 2,
            "the second round must find the new edge"
        );
        assert_eq!(out.stats.variables_substituted, 2);
        assert_eq!(out.occurring_variables(), 1);
        assert!(check_drat(&f, &proof).is_ok());
        assert!(check_drat_backward(&f, &proof).is_ok());
    }

    #[test]
    fn chained_substitutions_lift_a_model_through_every_hop() {
        let f = formula(
            3,
            &[
                &[n(1), p(2)],
                &[p(1), n(2)],
                &[n(0), p(1), p(2)],
                &[p(0), n(1)],
                &[p(0), p(1), p(2)],
            ],
        );
        let out = decompose(&f);
        let width = f.variable_count();
        let mut models = 0usize;
        for mask in 0u32..(1 << width) {
            let assignment: Vec<bool> = (0..width).map(|i| mask >> i & 1 == 1).collect();
            if !out.formula.evaluate(&assignment).expect("width") {
                continue;
            }
            let full = out.equivalences.extend(&assignment);
            assert!(f.evaluate(&full).expect("width"), "chain lift {full:?}");
            models += 1;
        }
        assert!(models > 0);
    }

    #[test]
    fn a_budget_below_setup_declines_rather_than_substituting_partially() {
        let f = one_class();
        let mut proof = Vec::new();
        let out = decompose_within_recorded(
            &f,
            DecomposeOptions {
                work_budget: Some(1),
                ..DecomposeOptions::DEFAULT
            },
            Some(&mut proof),
        );
        assert!(!out.stats.ran);
        assert!(out.stats.work_exhausted);
        assert_eq!(out.stats.variables_substituted, 0);
        assert!(proof.is_empty());
        assert_eq!(out.formula, f);
    }

    #[test]
    fn representatives_respect_duality_on_a_multi_class_instance() {
        // Two independent classes: {x0, x1} and {x2, x3}.
        let f = formula(
            5,
            &[
                &[n(0), p(1)],
                &[p(0), n(1)],
                &[n(2), p(3)],
                &[p(2), n(3)],
                &[p(1), p(3), p(4)],
                &[n(1), n(3)],
            ],
        );
        let out = decompose(&f);
        assert_eq!(out.stats.classes, 2);
        assert_eq!(out.stats.variables_substituted, 2);
        assert_eq!(out.equivalences.representative(v(1)), Some(p(0)));
        assert_eq!(out.equivalences.representative(v(3)), Some(p(2)));
        assert_eq!(out.occurring_variables(), 3);
    }

    #[test]
    fn an_inverted_class_substitutes_the_negation() {
        // x0 ≡ ¬x1: (x0 ∨ x1) and (¬x0 ∨ ¬x1).
        let f = formula(
            3,
            &[&[p(0), p(1)], &[n(0), n(1)], &[p(1), p(2)], &[n(2), p(0)]],
        );
        let mut proof = Vec::new();
        let out = decompose_within_recorded(&f, DecomposeOptions::DEFAULT, Some(&mut proof));
        assert_eq!(out.equivalences.representative(v(1)), Some(n(0)));
        assert_eq!(check_drat(&f, &proof), Ok(false));
        let width = f.variable_count();
        for mask in 0u32..(1 << width) {
            let assignment: Vec<bool> = (0..width).map(|i| mask >> i & 1 == 1).collect();
            if !out.formula.evaluate(&assignment).expect("width") {
                continue;
            }
            let full = out.equivalences.extend(&assignment);
            assert!(f.evaluate(&full).expect("width"), "inverted lift {full:?}");
        }
    }
}
