//! Unconstrained-variable elimination (Track 1, P1.2 / T1.2.4).
//!
//! A variable that occurs **exactly once** in the whole assertion forest is
//! *unconstrained* — Brummayer's definition verbatim: *"a variable is
//! unconstrained in an SMT formula `φ` if it has only one parent in the abstract
//! syntax DAG representation of `φ`. We assume that structural hashing is
//! enabled."* Nothing else pins it, so if its sole parent `p = op(…, x, …)` can
//! be inverted for `x`, then `p` itself ranges over everything `p`'s sort
//! allows: replace `p` by a single fresh variable `u`, drop the operation, and
//! record `x := op⁻¹(u, …)` so a model of the reduced problem still rebuilds
//! `x`. This is Z3's `elim_unconstrained` / `elim_uncnstr_tactic` — it peels
//! expensive operator layers off single-use variables before bit-blasting, and
//! the workload where it pays most is symbolic execution over SSA code, where
//! most program variables are written once and read at most once.
//!
//! # Two things this module deliberately separates
//!
//! * **Which variable is unconstrained** — the occurrence analysis, here.
//! * **What may replace its parent** — the inversion rules, in
//!   [`crate::inverter`], as a per-theory plugin registry with the
//!   unconstrained-ness predicate *injected*. A new theory registers an
//!   [`Inverter`] rather than editing a function in this file.
//!
//! # Model soundness
//!
//! Every elimination appends `x := def` to a [`ModelReconstructionTrail`].
//! Reverse replay (defaults appended last ⇒ reconstructed first) resolves every
//! dependency, exactly as for [`crate::solve_eqs`]. An operand that survives
//! nowhere in the reduced problem (it only fed the eliminated layer) is
//! genuinely unconstrained and is defaulted; the recorded inverse is computed
//! against that default, so the inversion identity still holds. **Model
//! generation is never gated off**: unlike Boolector, which ships with "model
//! generation with unconstrained optimization enabled is not yet supported",
//! reconstruction is threaded through every rule and is the pass's admission
//! criterion — a rule that cannot define what it consumes is not a rule.
//!
//! # Cost
//!
//! The occurrence graph is derived **once per round**, not once per
//! elimination. Within a round the cascade transplants a replaced node's parent
//! edges onto its fresh replacement, so a stack of peelable layers
//! (`(bvadd (bvneg x) 5)`, or the `x ≤ y, y ≤ z, z ≤ u` chain Z3's design note
//! calls out) collapses in one walk. That is the fix Z3 wrote its second
//! implementation for; the header of `elim_unconstrained.cpp` describes the
//! recompute-the-world shape — which this module had — as the problem.
//!
//! # Quantifiers
//!
//! A binder's variable can look single-use while being anything but: in
//! `(forall ((x S)) (bvult (bvadd x y) 5))`, `x` has one parent, yet replacing
//! the `bvadd` by a free `u` turns a universal claim into an existential one.
//! The pass therefore refuses any assertion forest containing a binder and
//! returns it unchanged ([`ElimUnconstrainedStats::skipped_quantified`]).

use std::collections::{BTreeMap, HashMap, HashSet};

use axeyum_ir::{IrError, Op, SymbolId, TermArena, TermId, TermNode};

use crate::canonical::replace_subterms;
use crate::inverter::{
    Inversion, InverterCtx, InverterRegistry, free_symbols, is_defaultable_sort,
};
use crate::reconstruct::ModelReconstructionTrail;

/// Maximum number of occurrence-graph rebuilds. A round that eliminates nothing
/// ends the pass, so this is a safety valve rather than the normal exit; Z3 caps
/// the equivalent loop at 3.
const MAX_ROUNDS: usize = 8;

/// Opt-in, clock-free instrumentation for one run of the pass.
///
/// Nobody has published a pass-level ablation for a modern bit-vector
/// preprocessor, so these counters are the raw material for one: which rule
/// fired how often, how many graph rebuilds it took, and how much of the
/// candidate set was even examined. Like [`crate::PassSize`] the counters are
/// free — they are plain increments on a struct the caller may ignore — and
/// carry no clock, so a measurement is reproducible.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ElimUnconstrainedStats {
    /// Occurrence-graph rebuilds performed (rounds entered).
    pub rounds: u64,
    /// Operator layers eliminated (one per successful inversion).
    pub eliminations: u64,
    /// Symbol definitions recorded, excluding orphan defaults. Larger than
    /// [`Self::eliminations`] whenever a rule consumed several operands.
    pub defs_recorded: u64,
    /// Operands that survived nowhere and were defaulted.
    pub orphans_defaulted: u64,
    /// Single-use candidates pulled off the worklist.
    pub candidates_examined: u64,
    /// Candidates whose parent reached the inverter registry.
    pub inversion_attempts: u64,
    /// Inversions whose replacement was a compound term rather than a bare
    /// fresh variable; each ends its cascade and buys another round.
    pub compound_replacements: u64,
    /// Set when the pass declined the whole forest because it contains a
    /// quantifier binder.
    pub skipped_quantified: bool,
    /// Firing count per rule name, in rule-name order.
    rules: BTreeMap<&'static str, u64>,
}

impl ElimUnconstrainedStats {
    /// Firing counts per rule name, deterministically ordered.
    #[must_use]
    pub fn rule_counts(&self) -> Vec<(&'static str, u64)> {
        self.rules.iter().map(|(&k, &v)| (k, v)).collect()
    }

    /// How often the named rule fired.
    #[must_use]
    pub fn rule_count(&self, rule: &str) -> u64 {
        self.rules.get(rule).copied().unwrap_or(0)
    }

    fn record(&mut self, rule: &'static str) {
        *self.rules.entry(rule).or_insert(0) += 1;
    }
}

/// The result of [`elim_unconstrained`]: the operator-reduced assertions plus the
/// trail that rebuilds the eliminated (and incidentally-orphaned) variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnconstrainedElimination {
    assertions: Vec<TermId>,
    trail: ModelReconstructionTrail,
    eliminated: usize,
    stats: ElimUnconstrainedStats,
}

impl UnconstrainedElimination {
    /// The reduced assertions (unconstrained operator layers replaced).
    #[must_use]
    pub fn assertions(&self) -> &[TermId] {
        &self.assertions
    }

    /// The model-reconstruction trail for the eliminated/orphaned variables.
    #[must_use]
    pub fn trail(&self) -> &ModelReconstructionTrail {
        &self.trail
    }

    /// Number of unconstrained operator layers eliminated (excludes the default
    /// assignments appended for orphaned operands).
    #[must_use]
    pub fn eliminated(&self) -> usize {
        self.eliminated
    }

    /// Per-rule and per-round instrumentation for this run.
    #[must_use]
    pub fn stats(&self) -> &ElimUnconstrainedStats {
        &self.stats
    }

    /// Consumes into `(reduced assertions, trail)`.
    #[must_use]
    pub fn into_parts(self) -> (Vec<TermId>, ModelReconstructionTrail) {
        (self.assertions, self.trail)
    }
}

/// Reference counts and parent edges of every term reachable from `roots`.
///
/// `refs` counts root slots **and** argument slots, so a term that is also a
/// top-level assertion is never single-use. `parents` records argument edges
/// only, so a term that is *only* a root has no parent and is never a
/// candidate.
struct Occurrences {
    refs: HashMap<TermId, usize>,
    parents: HashMap<TermId, Vec<(TermId, usize)>>,
    quantified: bool,
    nodes: usize,
}

/// Walks the shared DAG from the roots once.
fn occurrences(arena: &TermArena, roots: &[TermId]) -> Occurrences {
    let mut refs: HashMap<TermId, usize> = HashMap::new();
    let mut parents: HashMap<TermId, Vec<(TermId, usize)>> = HashMap::new();
    let mut visited: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = Vec::new();
    let mut quantified = false;

    for &root in roots {
        *refs.entry(root).or_insert(0) += 1;
        if visited.insert(root) {
            stack.push(root);
        }
    }
    while let Some(term) = stack.pop() {
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                quantified = true;
            }
            let args = args.clone();
            for (i, arg) in args.iter().enumerate() {
                *refs.entry(*arg).or_insert(0) += 1;
                parents.entry(*arg).or_default().push((term, i));
                if visited.insert(*arg) {
                    stack.push(*arg);
                }
            }
        }
    }
    let nodes = visited.len();
    Occurrences {
        refs,
        parents,
        quantified,
        nodes,
    }
}

/// Marks `start` and every node above it dirty: their subtrees now contain a
/// term this round has replaced, so they may not be baked into a definition.
fn mark_dirty(occ: &Occurrences, start: TermId, dirty: &mut HashSet<TermId>) {
    let mut stack = vec![start];
    while let Some(t) = stack.pop() {
        if !dirty.insert(t) {
            continue;
        }
        if let Some(edges) = occ.parents.get(&t) {
            for &(parent, _) in edges {
                stack.push(parent);
            }
        }
    }
}

/// Eliminates unconstrained operator layers using the default inverter registry
/// (core, bit-vector and arithmetic rules).
///
/// # Errors
///
/// Returns [`IrError`] only if rebuilding an inverse or substituted term fails
/// sort checking, which the rules' width/sort preconditions rule out.
pub fn elim_unconstrained(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<UnconstrainedElimination, IrError> {
    let registry = InverterRegistry::with_defaults();
    elim_unconstrained_with(arena, assertions, &registry)
}

/// [`elim_unconstrained`] against a caller-supplied [`InverterRegistry`] — the
/// entry point a consumer uses to add or withhold theories (an empty registry
/// makes the pass a no-op, which is how the ablation is run).
///
/// # Errors
///
/// As [`elim_unconstrained`].
pub fn elim_unconstrained_with(
    arena: &mut TermArena,
    assertions: &[TermId],
    registry: &InverterRegistry,
) -> Result<UnconstrainedElimination, IrError> {
    let mut current: Vec<TermId> = assertions.to_vec();
    let mut state = PassState::default();

    for _round in 0..MAX_ROUNDS {
        let mut occ = occurrences(arena, &current);
        if occ.quantified {
            // A binder's variable can have one parent without being
            // unconstrained; decline the whole forest rather than guess.
            state.stats.skipped_quantified = true;
            return Ok(UnconstrainedElimination {
                assertions: assertions.to_vec(),
                trail: ModelReconstructionTrail::new(),
                eliminated: 0,
                stats: state.stats,
            });
        }
        state.stats.rounds += 1;
        let mut round = Round::new(arena, &occ);
        round.run(arena, &mut occ, registry, &mut state)?;
        if round.eliminations == 0 {
            break;
        }
        let mut memo: HashMap<TermId, TermId> = HashMap::new();
        for a in &mut current {
            *a = replace_subterms(arena, *a, &round.image, &mut memo)?;
        }
    }

    // Default every symbol the rewrite dropped: one that survives nowhere in the
    // reduced problem and is not itself an eliminated variable is either an
    // operand that only fed an eliminated layer (its value is pinned by the
    // recorded inverse, computed against this default) or one whose value the
    // replacement made irrelevant — an `ite` condition whose branches both
    // became the same fresh variable, say. Both must still be BOUND, because a
    // `sat` is only checkable by evaluating the ORIGINAL assertions, which
    // mention them. Appended last ⇒ reconstructed first, so every definition
    // that mentions one sees a value.
    let mut survivors: HashSet<SymbolId> = HashSet::new();
    let mut seen = HashSet::new();
    for &a in &current {
        free_symbols(arena, a, &mut survivors, &mut seen);
    }
    let mut needed: HashSet<SymbolId> = HashSet::new();
    let mut def_seen = HashSet::new();
    for &def in &state.definition_terms {
        free_symbols(arena, def, &mut needed, &mut def_seen);
    }
    for &a in assertions {
        free_symbols(arena, a, &mut needed, &mut def_seen);
    }
    let mut orphans: Vec<SymbolId> = needed
        .into_iter()
        .filter(|s| !survivors.contains(s) && !state.defined.contains(s))
        .collect();
    orphans.sort_by_key(|s| s.index());
    for sym in orphans {
        let var = arena.var(sym);
        let sort = arena.sort_of(var);
        let default = {
            let predicate = |_: TermId| false;
            let mut ctx = InverterCtx::new(arena, &predicate, &mut state.next_fresh);
            ctx.default_value(sort)?
        };
        if let Some(default) = default {
            state.trail.define(sym, default);
            state.stats.orphans_defaulted += 1;
        }
    }

    state.stats.eliminations = state.eliminated as u64;
    Ok(UnconstrainedElimination {
        assertions: current,
        trail: state.trail,
        eliminated: state.eliminated,
        stats: state.stats,
    })
}

/// The state the pass threads across rounds.
#[derive(Default)]
struct PassState {
    trail: ModelReconstructionTrail,
    stats: ElimUnconstrainedStats,
    next_fresh: u64,
    eliminated: usize,
    defined: HashSet<SymbolId>,
    definition_terms: Vec<TermId>,
}

/// One round's cascade: the candidate set, the worklist, the node → replacement
/// image the round accumulates, and the upward dirty closure that keeps a stale
/// subterm out of a recorded definition.
struct Round {
    candidates: HashSet<TermId>,
    queue: Vec<TermId>,
    image: HashMap<TermId, TermId>,
    dirty: HashSet<TermId>,
    eliminations: usize,
    budget: usize,
}

impl Round {
    /// Seeds the worklist with every single-use variable node, ordered by
    /// `TermId` so the round is deterministic.
    fn new(arena: &TermArena, occ: &Occurrences) -> Self {
        let candidates: HashSet<TermId> = occ
            .refs
            .iter()
            .filter_map(|(&t, &n)| {
                let single_parent = occ.parents.get(&t).is_some_and(|p| p.len() == 1);
                (n == 1 && single_parent && matches!(arena.node(t), TermNode::Symbol(_)))
                    .then_some(t)
            })
            .collect();
        let mut queue: Vec<TermId> = candidates.iter().copied().collect();
        queue.sort_by_key(|t| t.index());
        Self {
            candidates,
            queue,
            image: HashMap::new(),
            dirty: HashSet::new(),
            eliminations: 0,
            // Each elimination consumes at least one candidate and mints at
            // most one; the budget bounds the compound rules, whose
            // replacements are larger than what they replace.
            budget: 4 * occ.nodes + 64,
        }
    }

    /// Drains the worklist, cascading into each fresh replacement.
    fn run(
        &mut self,
        arena: &mut TermArena,
        occ: &mut Occurrences,
        registry: &InverterRegistry,
        state: &mut PassState,
    ) -> Result<(), IrError> {
        let mut cursor = 0usize;
        while cursor < self.queue.len() && self.eliminations < self.budget {
            let var = self.queue[cursor];
            cursor += 1;
            self.step(arena, occ, registry, state, var)?;
        }
        Ok(())
    }

    /// Attempts one candidate. Returns without effect whenever the candidate is
    /// stale, its parent is not invertible, or no rule applies.
    fn step(
        &mut self,
        arena: &mut TermArena,
        occ: &mut Occurrences,
        registry: &InverterRegistry,
        state: &mut PassState,
        var: TermId,
    ) -> Result<(), IrError> {
        if !self.candidates.contains(&var) {
            return Ok(());
        }
        state.stats.candidates_examined += 1;
        let Some(parent_edges) = occ.parents.get(&var) else {
            return Ok(());
        };
        if parent_edges.len() != 1 {
            return Ok(());
        }
        let (parent, idx) = parent_edges[0];
        if self.image.contains_key(&parent) {
            return Ok(());
        }
        let TermNode::App { op, args } = arena.node(parent) else {
            return Ok(());
        };
        let (op, args) = (*op, args.clone());
        if idx >= args.len() {
            return Ok(());
        }
        let Some(args_now) = self.rewritten_args(&args, idx, var) else {
            return Ok(());
        };
        // Sort guard: every operand (and the result) must be a sort this module
        // can default, so an orphaned operand always has a value.
        let result_sort = arena.sort_of(parent);
        if !is_defaultable_sort(result_sort)
            || !args_now
                .iter()
                .all(|&a| is_defaultable_sort(arena.sort_of(a)))
        {
            return Ok(());
        }

        state.stats.inversion_attempts += 1;
        let inversion = {
            let predicate = |t: TermId| self.candidates.contains(&t);
            let mut ctx = InverterCtx::new(arena, &predicate, &mut state.next_fresh);
            registry.invert(&mut ctx, op, &args_now, idx, result_sort)?
        };
        let Some(inversion) = inversion else {
            return Ok(());
        };
        if !self.definable(arena, &inversion, &args_now, state) {
            return Ok(());
        }
        self.apply(arena, occ, state, parent, &inversion, &args_now);
        Ok(())
    }

    /// The parent's arguments with the one slot the cascade already rewrote
    /// substituted, or `None` when any *other* operand's subtree contains a
    /// replacement — its recorded definition would then reference a term this
    /// round is deleting, and the stale node can be arbitrarily deep, so
    /// checking only the direct arguments is not enough.
    fn rewritten_args(&self, args: &[TermId], idx: usize, var: TermId) -> Option<Vec<TermId>> {
        let mut args_now = args.to_vec();
        for (i, arg) in args.iter().enumerate() {
            if i == idx {
                if let Some(&mapped) = self.image.get(arg) {
                    args_now[i] = mapped;
                }
            } else if self.dirty.contains(arg) {
                return None;
            }
        }
        (args_now[idx] == var).then_some(args_now)
    }

    /// Contract check: a rule may only define operands the analysis already
    /// certified unconstrained, and never one an earlier elimination defined.
    fn definable(
        &self,
        arena: &TermArena,
        inversion: &Inversion,
        args_now: &[TermId],
        state: &PassState,
    ) -> bool {
        inversion.defs.iter().all(|&(sym, _)| {
            !state.defined.contains(&sym)
                && args_now.iter().any(|&a| {
                    self.candidates.contains(&a)
                        && matches!(arena.node(a), TermNode::Symbol(s) if *s == sym)
                })
        })
    }

    /// Records the inversion and updates the round's bookkeeping.
    fn apply(
        &mut self,
        arena: &TermArena,
        occ: &mut Occurrences,
        state: &mut PassState,
        parent: TermId,
        inversion: &Inversion,
        args_now: &[TermId],
    ) {
        for &(sym, def) in &inversion.defs {
            state.trail.define(sym, def);
            state.defined.insert(sym);
            state.definition_terms.push(def);
            state.stats.defs_recorded += 1;
        }
        state.stats.record(inversion.rule);
        state.eliminated += 1;
        self.eliminations += 1;
        self.image.insert(parent, inversion.replacement);
        mark_dirty(occ, parent, &mut self.dirty);

        // Every operand of the inverted node leaves the candidate set: the ones
        // the rule defined are gone from the formula, and the ones it dropped
        // are about to be.
        for &arg in args_now {
            self.candidates.remove(&arg);
        }

        if inversion.compound {
            // The replacement puts existing subterms back into the formula, so
            // the round's occurrence counts no longer describe it below this
            // node. Retire every symbol it mentions and let the next round
            // re-derive the graph.
            state.stats.compound_replacements += 1;
            let mut mentioned = HashSet::new();
            let mut seen = HashSet::new();
            free_symbols(arena, inversion.replacement, &mut mentioned, &mut seen);
            self.candidates.retain(|&t| match arena.node(t) {
                TermNode::Symbol(s) => !mentioned.contains(s),
                _ => true,
            });
            return;
        }

        // Cascade: the fresh replacement inherits the replaced node's parent
        // edges, so a peelable stack collapses without rebuilding the graph.
        let inherited = occ.parents.get(&parent).cloned().unwrap_or_default();
        let inherited_refs = occ.refs.get(&parent).copied().unwrap_or(0);
        let single = inherited_refs == 1 && inherited.len() == 1;
        occ.refs.insert(inversion.replacement, inherited_refs);
        occ.parents.insert(inversion.replacement, inherited);
        if single && matches!(arena.node(inversion.replacement), TermNode::Symbol(_)) {
            self.candidates.insert(inversion.replacement);
            self.queue.push(inversion.replacement);
        }
    }
}

/// The registry the pass uses by default — exposed so a caller can start from
/// it, add a theory, and pass the result to [`elim_unconstrained_with`].
#[must_use]
pub fn default_inverters() -> InverterRegistry {
    InverterRegistry::with_defaults()
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::{Assignment, Sort, Value, eval};

    /// A deep operand spine must not blow the stack in the free-symbol scan.
    ///
    /// `free_symbols` runs over every assertion this pass sees, and its walk
    /// depth is the term DAG's depth — which an SMT-LIB source controls
    /// directly with a left-associated `(bvadd (bvadd (bvadd x 1) 1) 1)` spine.
    /// A natively recursive walk aborts the process with a stack overflow
    /// instead of letting the solver report a first-class `unknown`, so a
    /// regression aborts the test binary rather than failing quietly.
    #[test]
    fn free_symbols_survives_a_deep_operand_spine() {
        const DEPTH: usize = 100_000;
        let mut arena = TermArena::new();
        let x = arena.declare("deep_x", Sort::BitVec(8)).expect("declare x");
        let mut acc = arena.var(x);
        let one = arena.bv_const(8, 1).expect("const");
        for _ in 0..DEPTH {
            acc = arena.bv_add(acc, one).expect("bvadd");
        }

        let mut out = HashSet::new();
        let mut seen = HashSet::new();
        free_symbols(&arena, acc, &mut out, &mut seen);

        assert_eq!(out.len(), 1, "only `deep_x` occurs free");
        assert!(out.contains(&x));
    }

    fn bv8(v: u128) -> Value {
        Value::Bv { width: 8, value: v }
    }

    fn assert_satisfies(arena: &TermArena, originals: &[TermId], model: &Assignment) {
        for &a in originals {
            assert_eq!(
                eval(arena, a, model).unwrap(),
                Value::Bool(true),
                "reconstructed model must satisfy original assertion #{}",
                a.index()
            );
        }
    }

    /// Free symbols of the reduced assertions (the survivors a backend models).
    fn survivors(arena: &TermArena, assertions: &[TermId]) -> Vec<SymbolId> {
        let mut out = HashSet::new();
        let mut seen = HashSet::new();
        for &a in assertions {
            free_symbols(arena, a, &mut out, &mut seen);
        }
        let mut v: Vec<_> = out.into_iter().collect();
        v.sort_by_key(|s| s.index());
        v
    }

    /// Assigns every surviving symbol a sort-appropriate value and
    /// reconstructs the eliminated ones.
    fn reconstruct_with(
        arena: &mut TermArena,
        out: &UnconstrainedElimination,
        bv_value: u128,
    ) -> Assignment {
        let mut reduced = Assignment::new();
        for sym in survivors(arena, out.assertions()) {
            let var = arena.var(sym);
            let value = match arena.sort_of(var) {
                Sort::Bool => Value::Bool(true),
                Sort::BitVec(w) => Value::Bv {
                    width: w,
                    value: bv_value & ((1u128 << w) - 1),
                },
                other => panic!("unexpected surviving sort {other:?}"),
            };
            reduced.set(sym, value);
        }
        out.trail().reconstruct(arena, &reduced).unwrap()
    }

    #[test]
    fn eliminates_single_use_under_add_and_reconstructs() {
        // (bvult (bvadd x y) 200) ∧ (bvugt y 1): x occurs once (inside the add),
        // y survives in the second assertion. The add is unconstrained ⇒ replaced
        // by a fresh u; x := u - y. The comparison layer above it then peels too
        // (the fresh u is itself single-use under `bvult`).
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let sum = arena.bv_add(xv, yv).unwrap();
        let c = arena.bv_const(8, 200).unwrap();
        let a1 = arena.bv_ult(sum, c).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a2 = arena.bv_ugt(yv, one).unwrap();
        let originals = [a1, a2];

        let out = elim_unconstrained(&mut arena, &originals).unwrap();
        assert!(out.eliminated() >= 1);
        assert_eq!(out.stats().rule_count("bv/add"), 1);
        assert!(
            !survivors(&arena, out.assertions()).contains(&x),
            "x is eliminated"
        );

        // Any assignment of the survivors that satisfies the reduced problem
        // must reconstruct to a model of the original.
        let full = reconstruct_with(&mut arena, &out, 3);
        for &a in out.assertions() {
            assert_eq!(eval(&arena, a, &full).unwrap(), Value::Bool(true));
        }
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn orphaned_operand_is_defaulted_and_reconstructs() {
        // (bvult (bvadd x y) 200): BOTH x and y occur once, so the add is
        // unconstrained and y survives nowhere after the rewrite — it must be
        // defaulted (to 0) so x := u - y still reconstructs.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let sum = arena.bv_add(xv, yv).unwrap();
        let c = arena.bv_const(8, 200).unwrap();
        let a1 = arena.bv_ult(sum, c).unwrap();
        let originals = [a1];

        let out = elim_unconstrained(&mut arena, &originals).unwrap();
        assert!(out.eliminated() >= 1);
        let surv = survivors(&arena, out.assertions());
        assert!(
            !surv.contains(&x) && !surv.contains(&y),
            "both eliminated/orphaned"
        );
        assert!(out.stats().orphans_defaulted >= 1);

        let full = reconstruct_with(&mut arena, &out, 3);
        assert_eq!(full.get(y), Some(bv8(0)), "orphan operand defaulted to 0");
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn does_not_fire_on_a_twice_used_variable() {
        // (bvult x (bvadd x 1)): x occurs twice, so it is not unconstrained, and
        // no other node has a single-use variable operand.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let one = arena.bv_const(8, 1).unwrap();
        let sum = arena.bv_add(xv, one).unwrap();
        let a1 = arena.bv_ult(xv, sum).unwrap();

        let out = elim_unconstrained(&mut arena, &[a1]).unwrap();
        assert_eq!(out.eliminated(), 0);
        assert_eq!(out.assertions(), &[a1]);
    }

    #[test]
    fn does_not_fire_when_the_other_multiplicand_is_a_live_variable() {
        // (bvult (bvmul x y) 200) ∧ (bvugt y 1): x is single-use but y is not,
        // so neither the all-unconstrained rule nor the constant rule applies.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let prod = arena.bv_mul(xv, yv).unwrap();
        let c = arena.bv_const(8, 200).unwrap();
        let a1 = arena.bv_ult(prod, c).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a2 = arena.bv_ugt(yv, one).unwrap();

        let out = elim_unconstrained(&mut arena, &[a1, a2]).unwrap();
        assert_eq!(out.stats().rule_count("bv/mul-all"), 0);
        assert_eq!(out.stats().rule_count("bv/mul-odd-const"), 0);
        assert_eq!(out.stats().rule_count("bv/mul-even-const"), 0);
    }

    #[test]
    fn peels_a_nested_invertible_stack_in_one_round() {
        // (= (bvadd (bvneg x) 5) 200): x single-use under bvneg, whose result is
        // single-use under bvadd — both layers peel, and the cascade does it
        // without rebuilding the occurrence graph.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let negx = arena.bv_neg(xv).unwrap();
        let five = arena.bv_const(8, 5).unwrap();
        let inner = arena.bv_add(negx, five).unwrap();
        let c = arena.bv_const(8, 200).unwrap();
        let a1 = arena.eq(inner, c).unwrap();
        let originals = [a1];

        let out = elim_unconstrained(&mut arena, &originals).unwrap();
        assert!(out.eliminated() >= 2, "both invertible layers peel");
        assert_eq!(
            out.stats().rounds,
            2,
            "one productive round plus the round that finds nothing"
        );

        let full = reconstruct_with(&mut arena, &out, 3);
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn eliminates_single_use_under_odd_constant_multiply() {
        // (= (bvmul 3 x) 30): x single-use, 3 odd ⇒ x := 3⁻¹·u (3⁻¹ = 171 mod
        // 256). The multiplier layer is peeled with no bit-blasting.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let xv = arena.var(x);
        let three = arena.bv_const(8, 3).unwrap();
        let prod = arena.bv_mul(three, xv).unwrap();
        let thirty = arena.bv_const(8, 30).unwrap();
        let a1 = arena.eq(prod, thirty).unwrap();
        let originals = [a1];

        let out = elim_unconstrained(&mut arena, &originals).unwrap();
        assert_eq!(out.stats().rule_count("bv/mul-odd-const"), 1);
        let full = reconstruct_with(&mut arena, &out, 3);
        assert_satisfies(&arena, &originals, &full);
    }

    #[test]
    fn quantified_forest_is_declined_whole() {
        // (forall ((q Bv8)) (= (bvadd q y) 3)): `q` has one parent but is bound;
        // replacing the `bvadd` by a free variable would turn the universal into
        // an existential. A positive control follows in the same test so an
        // always-decline regression cannot hide here.
        let mut arena = TermArena::new();
        let q = arena.declare("q", Sort::BitVec(8)).unwrap();
        let y = arena.declare("qy", Sort::BitVec(8)).unwrap();
        let (qv, yv) = (arena.var(q), arena.var(y));
        let sum = arena.bv_add(qv, yv).unwrap();
        let three = arena.bv_const(8, 3).unwrap();
        let body = arena.eq(sum, three).unwrap();
        let quantified = arena.forall(q, body).unwrap();

        let out = elim_unconstrained(&mut arena, &[quantified]).unwrap();
        assert!(out.stats().skipped_quantified);
        assert_eq!(out.eliminated(), 0);
        assert_eq!(out.assertions(), &[quantified]);
        assert!(out.trail().is_empty());

        // Positive control: the same body without the binder does fire.
        let out = elim_unconstrained(&mut arena, &[body]).unwrap();
        assert!(!out.stats().skipped_quantified);
        assert!(out.eliminated() >= 1);
    }

    #[test]
    fn an_empty_registry_is_a_no_op() {
        // The ablation control: same input, no registered theory, nothing moves.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::BitVec(8)).unwrap();
        let y = arena.declare("y", Sort::BitVec(8)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let sum = arena.bv_add(xv, yv).unwrap();
        let c = arena.bv_const(8, 200).unwrap();
        let a1 = arena.bv_ult(sum, c).unwrap();

        let empty = InverterRegistry::new();
        let out = elim_unconstrained_with(&mut arena, &[a1], &empty).unwrap();
        assert_eq!(out.eliminated(), 0);
        assert_eq!(out.assertions(), &[a1]);
        assert!(out.stats().candidates_examined > 0, "candidates were found");
        assert!(out.stats().inversion_attempts > 0, "the registry was asked");
    }
}
