//! Cycle detection + normal-form **inference rules** (slice T-B.3) — the
//! derivation layer that sits on top of the T-B.2 [`Classes`] substrate and
//! turns some of its declines into progress.
//!
//! Given the arena and a caller-supplied slice of asserted `Seq`-sorted
//! equalities (each positionally indexed as its *premise ID*, exactly as
//! [`Classes`] indexes them), [`infer`] runs a budget-guarded fixpoint that
//! produces a deterministic list of [`Inference`]s. Each inference is either a
//! derived equality that is a **theory consequence** of its cited premises
//! (a [`Fact`]), or a set of premises that are **jointly unsatisfiable** by a
//! self-evident rule instance (a [`Conflict`]). This is the derivation
//! substrate T-B.7 will re-check.
//!
//! # The rules
//!
//! ## `a`. Cycle ε-inference ([`Rule::CycleEpsilon`])
//!
//! The class-containment order (`e₁ < e₂` when `e₁`'s class appears in the
//! flat form of a member of `e₂`'s class) may contain a cycle — e.g.
//! `x ≈ y ++ x` (a self-loop) or a mutual `x ≈ y ++ a`, `a ≈ z ++ x`. On a
//! containment cycle the sequence lengths satisfy
//! `|r₀| = |r₀| + Σ|Oᵢ|`, where `Oᵢ` is every component of the `i`-th edge's
//! witness **except** the one that continues the cycle. Hence `Σ|Oᵢ| = 0`, so
//! **every off-cycle component is ε** (CAV-2014). We derive those `c ≈ ε`
//! equalities, and adding them breaks the cycle for the next round (T-B.2's
//! [`Declined::Cycle`](crate::Declined) becomes a decidable class).
//!
//! ## `b`. `INFER_UNIFY` ([`Rule::InferUnify`])
//!
//! Two members of one class are equal sequences, so their component vectors
//! align. When a common-length prefix has been consumed and the two components
//! at the current position have **provably equal length from structure alone**
//! (both length-1 `seq.unit`s, both equal-length constant blocks, …), those
//! components must be equal. Length reasoning **via LIA is out of scope** — it
//! arrives with the Phase-A `LenAbs` link at routing time; here a length must
//! be structurally evident or the rule declines (the [`Rule::InferUnify`] path
//! only fires on structurally-known equal lengths).
//!
//! ## `c`. `INFER_ENDPOINT_EQ` / `INFER_ENDPOINT_EMP`
//!
//! When one member's vector is a component-wise-equal **strict prefix** of
//! another's, the two members being equal forces the longer's remaining tail to
//! concatenate to ε ⇒ each remaining component is ε
//! ([`Rule::InferEndpointEmp`]). The two-sided variant — exactly one component
//! remaining on each side after an aligned prefix — forces those two remainders
//! equal ([`Rule::InferEndpointEq`]).
//!
//! # What this slice declines (bounded, on purpose)
//!
//! * **arrangement branching** (`F-Split` / `Len-Split`) is T-B.4: two
//!   components of *unequal or unknown* length at an aligned position (e.g. a
//!   variable facing a two-component remainder) **stop** the alignment rather
//!   than branch or introduce a Skolem;
//! * **length-compatible constant splitting** (`"ab"` facing `"abc"`) is left
//!   to T-B.4 — only the *incompatible* constant case (a genuine clash) is
//!   reported here as a [`Conflict`];
//! * **`F-Loop` / regex** is T-B.5 — the cycle rule infers ε (which terminates
//!   on the decidable fragment) but never regularizes an unbroken loop.
//!
//! # Soundness bar
//!
//! Every [`Fact`] is entailed by its cited premises under SMT-LIB `Seq`
//! semantics; every [`Conflict`]'s premises are jointly unsatisfiable by the
//! self-evident rule its [`ConflictReason`] records. We never fire a rule we
//! cannot justify — we decline. The property tests enforce both directions.
//!
//! # Determinism & premise provenance
//!
//! Every observable output is deterministic (ADR-0053): classes iterate in
//! sorted representative order, members and components in sorted / left-to-right
//! order, and every premise set is a [`BTreeSet<usize>`]. Derived equalities are
//! fed back into a fresh [`Classes`] each round, but every published premise set
//! cites **original** premise indices only: an internally derived equality
//! carries the full closure of the original indices that entail it, and any
//! downstream citation of it is expanded through that closure
//! ([`map_closure`]).

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Assignment, Op, Sort, TermArena, TermId, TermNode, Value, eval};

use crate::classes::Classes;
use crate::normal_form::{concat_components, normalize};

/// The maximum number of fixpoint rounds before [`infer`] returns what it has
/// derived so far with [`Inferences::hit_budget`] set.
///
/// Each productive round strictly merges two classes or forces a class to ε, so
/// the fixpoint converges in at most `O(#endpoints)` rounds on well-behaved
/// input; the budget is a hard guard against any pathology (never loop forever,
/// never guess).
pub const MAX_ROUNDS: usize = 256;

/// The named derivation rule that produced a [`Fact`] — recorded so a checker
/// (T-B.7) can re-verify the specific inference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rule {
    /// Cycle ε-inference: an off-cycle component forced to ε by a containment
    /// cycle (rule `a`).
    CycleEpsilon,
    /// `INFER_UNIFY`: two structurally equal-length components at an aligned
    /// position must be equal (rule `b`).
    InferUnify,
    /// `INFER_ENDPOINT_EQ`: the single remaining component on each side after an
    /// aligned prefix must be equal (rule `c`).
    InferEndpointEq,
    /// `INFER_ENDPOINT_EMP`: a component in the remaining tail of the longer
    /// member must be ε (rule `c`).
    InferEndpointEmp,
}

/// A derived equality that is a theory consequence of `premises`.
///
/// `equality` is unordered (stored smallest [`TermId`] first for determinism);
/// `premises` cites **original** premise indices only.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fact {
    /// The rule that derived this equality.
    pub rule: Rule,
    /// The derived equality `lhs ≈ rhs`, stored `(min, max)` by [`TermId`].
    pub equality: (TermId, TermId),
    /// A sufficient set of **original** premise indices entailing the equality.
    pub premises: BTreeSet<usize>,
}

/// Why a [`Conflict`] holds — enough for a checker to re-verify the rule
/// instance is jointly unsatisfiable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConflictReason {
    /// The rule name (e.g. `"const-clash"`, `"const-prefix-mismatch"`).
    pub rule: &'static str,
    /// The first class member whose component vector participates.
    pub member_a: TermId,
    /// The second class member whose component vector participates.
    pub member_b: TermId,
    /// The aligned position (index into `member_a`'s component vector).
    pub position_a: usize,
    /// The aligned position (index into `member_b`'s component vector).
    pub position_b: usize,
    /// The clashing constant component from `member_a`.
    pub const_a: TermId,
    /// The clashing constant component from `member_b`.
    pub const_b: TermId,
}

/// A set of premises that are jointly unsatisfiable by the rule its
/// [`ConflictReason`] records.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Conflict {
    /// A subset of **original** premise indices that are jointly unsatisfiable.
    pub premises: BTreeSet<usize>,
    /// The self-evident rule instance witnessing unsatisfiability.
    pub reason: ConflictReason,
}

/// A single inference: a derived [`Fact`] or a [`Conflict`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Inference {
    /// A derived equality (theory consequence of its premises).
    Fact(Fact),
    /// A jointly-unsatisfiable premise set.
    Conflict(Conflict),
}

/// The result of the inference fixpoint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Inferences {
    /// The derived inferences, in deterministic derivation order. At most one
    /// [`Inference::Conflict`] appears, always last (the fixpoint stops on the
    /// first conflict).
    pub items: Vec<Inference>,
    /// Whether the [`MAX_ROUNDS`] budget was hit before the fixpoint converged.
    pub hit_budget: bool,
}

impl Inferences {
    /// The derived [`Fact`]s, skipping any conflict.
    pub fn facts(&self) -> impl Iterator<Item = &Fact> {
        self.items.iter().filter_map(|i| match i {
            Inference::Fact(f) => Some(f),
            Inference::Conflict(_) => None,
        })
    }

    /// The first [`Conflict`], if any was derived.
    #[must_use]
    pub fn conflict(&self) -> Option<&Conflict> {
        self.items.iter().find_map(|i| match i {
            Inference::Conflict(c) => Some(c),
            Inference::Fact(_) => None,
        })
    }

    /// Whether a conflict was derived (the premise set is jointly unsat).
    #[must_use]
    pub fn is_conflict(&self) -> bool {
        self.conflict().is_some()
    }
}

/// Runs the T-B.3 inference fixpoint over `equalities`, returning every derived
/// [`Fact`] / [`Conflict`] with original-premise provenance.
///
/// The pass is deterministic and always terminates (budget-guarded by
/// [`MAX_ROUNDS`]). Declines — where an arrangement branch (`F-Split`,
/// `Len-Split`, `F-Loop`) would be required — simply produce no inference for
/// that alignment, never a guess.
#[must_use]
pub fn infer(arena: &mut TermArena, equalities: &[(TermId, TermId)]) -> Inferences {
    let mut state = Derived::new(equalities);
    let mut hit_budget = false;

    for round in 0.. {
        if round >= MAX_ROUNDS {
            hit_budget = true;
            break;
        }

        let classes = Classes::new(&state.eqs);
        let reps = class_reps(&classes, &state.eqs);
        let (rep_forms, align_forms) = build_forms(arena, &classes, &reps);

        // Rule a first: cycle ε-inference breaks loops before alignment.
        if cycle_phase(arena, &classes, &rep_forms, &mut state) {
            continue;
        }
        // Rules b/c: normal-form inference over aligned member pairs.
        if let RoundStep::Conflict | RoundStep::Fixpoint =
            align_phase(arena, &classes, &reps, &align_forms, &mut state)
        {
            break;
        }
    }

    Inferences {
        items: state.items,
        hit_budget,
    }
}

/// The mutable state threaded across fixpoint rounds: the growing equality list,
/// each equality's original-premise closure, the published inferences, and the
/// cross-round dedup set.
struct Derived {
    eqs: Vec<(TermId, TermId)>,
    closures: Vec<BTreeSet<usize>>,
    items: Vec<Inference>,
    emitted: BTreeSet<(TermId, TermId)>,
}

impl Derived {
    fn new(equalities: &[(TermId, TermId)]) -> Self {
        Self {
            eqs: equalities.to_vec(),
            closures: (0..equalities.len()).map(|i| BTreeSet::from([i])).collect(),
            items: Vec::new(),
            emitted: BTreeSet::new(),
        }
    }

    /// Publishes a derived fact (deduped across rounds) and feeds it back into
    /// the equality list carrying its original-premise closure. Returns whether
    /// it was newly added.
    fn add_fact(&mut self, rule: Rule, lhs: TermId, rhs: TermId, orig: BTreeSet<usize>) -> bool {
        let equality = canon(lhs, rhs);
        if !self.emitted.insert(equality) {
            return false;
        }
        self.items.push(Inference::Fact(Fact {
            rule,
            equality,
            premises: orig.clone(),
        }));
        self.eqs.push((lhs, rhs));
        self.closures.push(orig);
        true
    }
}

/// The outcome of one fixpoint round's alignment phase.
enum RoundStep {
    /// At least one new fact was derived — run another round.
    Progressed,
    /// A conflict was recorded — stop.
    Conflict,
    /// No new fact — the fixpoint has converged.
    Fixpoint,
}

/// Builds the rep-substituted view (cycle detection) and the raw-atom view
/// (alignment) for every class member, in the single `&mut` phase.
#[allow(clippy::type_complexity)]
fn build_forms(
    arena: &mut TermArena,
    classes: &Classes,
    reps: &[TermId],
) -> (
    BTreeMap<TermId, Vec<RepForm>>,
    BTreeMap<TermId, Vec<MemberForm>>,
) {
    let mut rep_forms: BTreeMap<TermId, Vec<RepForm>> = BTreeMap::new();
    let mut align_forms: BTreeMap<TermId, Vec<MemberForm>> = BTreeMap::new();
    for &r in reps {
        let members = classes.class_members(r);
        let mut rfv = Vec::with_capacity(members.len());
        let mut afv = Vec::with_capacity(members.len());
        for &m in &members {
            rfv.push(build_rep_form(arena, classes, r, m));
            afv.push(build_member_form(arena, classes, r, m));
        }
        rep_forms.insert(r, rfv);
        align_forms.insert(r, afv);
    }
    (rep_forms, align_forms)
}

/// Rule a: detect one containment cycle and force its off-cycle components to ε.
/// Returns whether any new ε fact was derived (in which case the round restarts).
fn cycle_phase(
    arena: &mut TermArena,
    classes: &Classes,
    rep_forms: &BTreeMap<TermId, Vec<RepForm>>,
    state: &mut Derived,
) -> bool {
    let Some(cycle) = find_cycle(rep_forms) else {
        return false;
    };
    let (targets, prem) = cycle_epsilon(rep_forms, &cycle);
    let orig = map_closure(&state.closures, &prem);
    let mut progressed = false;
    for t in targets {
        if class_is_epsilon(classes, arena, t) {
            continue;
        }
        let Some(eps) = make_epsilon(arena, t) else {
            continue;
        };
        progressed |= state.add_fact(Rule::CycleEpsilon, t, eps, orig.clone());
    }
    progressed
}

/// Rules b/c: align every member pair of every class, materializing the derived
/// facts (or recording the first conflict).
fn align_phase(
    arena: &mut TermArena,
    classes: &Classes,
    reps: &[TermId],
    align_forms: &BTreeMap<TermId, Vec<MemberForm>>,
    state: &mut Derived,
) -> RoundStep {
    let mut pending: Vec<PendingFact> = Vec::new();
    for &r in reps {
        let forms = &align_forms[&r];
        // Every unordered pair — a constant member pair is how a clash is seen
        // even when a variable member absorbs both endpoints.
        for i in 0..forms.len() {
            for j in (i + 1)..forms.len() {
                match align(classes, arena, &forms[i], &forms[j]) {
                    Aligned::Conflict { reason, premises } => {
                        state.items.push(Inference::Conflict(Conflict {
                            premises: map_closure(&state.closures, &premises),
                            reason,
                        }));
                        return RoundStep::Conflict;
                    }
                    Aligned::Facts(fs) => pending.extend(fs),
                }
            }
        }
    }

    let mut progressed = false;
    for pf in pending {
        let rhs = match pf.rhs {
            FactTarget::Term(t) => t,
            FactTarget::Epsilon => match make_epsilon(arena, pf.lhs) {
                Some(eps) => eps,
                None => continue,
            },
        };
        // Only add if it actually merges two distinct classes (new info).
        if classes.representative(pf.lhs) == classes.representative(rhs) {
            continue;
        }
        let orig = map_closure(&state.closures, &pf.premises);
        progressed |= state.add_fact(pf.rule, pf.lhs, rhs, orig);
    }

    if progressed {
        RoundStep::Progressed
    } else {
        RoundStep::Fixpoint
    }
}

// ----- premise provenance -----------------------------------------------------

/// Expands a premise set over the *current* equality indexing into a set of
/// **original** premise indices, by unioning each index's closure.
#[must_use]
pub fn map_closure(closures: &[BTreeSet<usize>], premises: &BTreeSet<usize>) -> BTreeSet<usize> {
    let mut out = BTreeSet::new();
    for &p in premises {
        if let Some(c) = closures.get(p) {
            out.extend(c.iter().copied());
        }
    }
    out
}

/// The sorted set of class representatives touched by `eqs`.
fn class_reps(classes: &Classes, eqs: &[(TermId, TermId)]) -> Vec<TermId> {
    let mut set: BTreeSet<TermId> = BTreeSet::new();
    for &(a, b) in eqs {
        set.insert(classes.representative(a));
        set.insert(classes.representative(b));
    }
    set.into_iter().collect()
}

// ----- per-member views -------------------------------------------------------

/// The rep-substituted, ε-class-filtered component vector of a member — the view
/// the containment graph (cycle detection) is built over.
#[derive(Debug, Clone)]
struct RepForm {
    /// Component class representatives (ε classes dropped).
    comps: Vec<TermId>,
    /// Premises justifying this decomposition (base link + component + ε-drop
    /// premises) — cited when this member witnesses a cycle edge.
    cycle_prem: BTreeSet<usize>,
}

/// The raw-atom, ε-class-filtered component vector of a member — the view the
/// alignment rules operate over. Constants stay visible as their own terms
/// (they are **not** substituted by a possibly-variable class representative),
/// which is what lets an equal-length constant clash be seen.
#[derive(Debug, Clone)]
struct MemberForm {
    /// The member term this vector decomposes.
    member: TermId,
    /// The normalized atoms (variables, `seq.unit`s, fused constant blocks),
    /// with ε-class atoms dropped.
    atoms: Vec<TermId>,
    /// The base premise set: the member↔representative link plus the premises
    /// justifying every ε-class atom dropped from `atoms`.
    base: BTreeSet<usize>,
}

fn build_rep_form(arena: &mut TermArena, classes: &Classes, rep: TermId, m: TermId) -> RepForm {
    let ff = classes.flat_form(arena, m);
    let mut cycle_prem = classes.explain(rep, m).unwrap_or_default();
    let mut comps = Vec::with_capacity(ff.components.len());
    for (c, p) in ff.components.iter().zip(&ff.component_premises) {
        cycle_prem.extend(p.iter().copied());
        if class_is_epsilon(classes, arena, *c) {
            extend_epsilon_reason(classes, arena, *c, &mut cycle_prem);
            continue;
        }
        comps.push(*c);
    }
    cycle_prem.extend(ff.premises.iter().copied());
    RepForm { comps, cycle_prem }
}

fn build_member_form(
    arena: &mut TermArena,
    classes: &Classes,
    rep: TermId,
    m: TermId,
) -> MemberForm {
    let norm = normalize(arena, m);
    let raw = concat_components(arena, norm);
    let mut base = classes.explain(rep, m).unwrap_or_default();
    let mut atoms = Vec::with_capacity(raw.len());
    for c in raw {
        if class_is_epsilon(classes, arena, c) {
            extend_epsilon_reason(classes, arena, c, &mut base);
            continue;
        }
        atoms.push(c);
    }
    MemberForm {
        member: m,
        atoms,
        base,
    }
}

/// Adds to `prem` the premises justifying that `c`'s class is the ε class.
fn extend_epsilon_reason(
    classes: &Classes,
    arena: &TermArena,
    c: TermId,
    prem: &mut BTreeSet<usize>,
) {
    if let Some(e) = epsilon_member(classes, arena, c)
        && let Some(ex) = classes.explain(c, e)
    {
        prem.extend(ex);
    }
}

// ----- cycle detection (rule a) -----------------------------------------------

/// DFS coloring for [`find_cycle`].
#[derive(Clone, Copy, PartialEq, Eq)]
enum Color {
    White,
    Gray,
    Black,
}

/// Finds one containment cycle (self-loops first, then a DFS back-edge), as an
/// ordered node list `[v, …, u]` whose edges are `v→…→u` plus the closing
/// `u→v`. Deterministic: nodes and adjacency iterate in sorted order.
fn find_cycle(rep_forms: &BTreeMap<TermId, Vec<RepForm>>) -> Option<Vec<TermId>> {
    // Adjacency `from → to → (from, form-index)`; the first witness wins.
    let mut adj: BTreeMap<TermId, BTreeMap<TermId, (TermId, usize)>> = BTreeMap::new();
    for (&r, rfv) in rep_forms {
        for (fi, rf) in rfv.iter().enumerate() {
            // An atomic self-member (`comps == [r]`) is just `r ≈ r`: no edge.
            if rf.comps.len() == 1 && rf.comps[0] == r {
                continue;
            }
            for &c in &rf.comps {
                adj.entry(r).or_default().entry(c).or_insert((r, fi));
            }
        }
    }

    let nodes: Vec<TermId> = rep_forms.keys().copied().collect();
    // Only class representatives can lie on a containment cycle; a component that
    // is not itself an endpoint is a leaf (no outgoing edges).
    let node_set: BTreeSet<TermId> = nodes.iter().copied().collect();

    // Self-loops (`x ≈ … x …`) first — the common, cheapest case.
    for &r in &nodes {
        if adj.get(&r).is_some_and(|m| m.contains_key(&r)) {
            return Some(vec![r]);
        }
    }

    // Iterative DFS for a multi-node cycle.
    let mut color: BTreeMap<TermId, Color> = nodes.iter().map(|&n| (n, Color::White)).collect();
    let mut parent: BTreeMap<TermId, TermId> = BTreeMap::new();

    for &start in &nodes {
        if color[&start] != Color::White {
            continue;
        }
        // Stack frames: (node, sorted neighbours, next-neighbour cursor).
        let mut stack: Vec<(TermId, Vec<TermId>, usize)> = Vec::new();
        color.insert(start, Color::Gray);
        stack.push((start, neighbours(&adj, &node_set, start), 0));

        while let Some(&(u, _, _)) = stack.last() {
            let cursor = stack.last().map(|f| f.2).unwrap_or_default();
            let neigh_len = stack.last().map_or(0, |f| f.1.len());
            if cursor < neigh_len {
                let v = stack.last().expect("frame").1[cursor];
                stack.last_mut().expect("frame").2 += 1;
                match color[&v] {
                    Color::White => {
                        parent.insert(v, u);
                        color.insert(v, Color::Gray);
                        stack.push((v, neighbours(&adj, &node_set, v), 0));
                    }
                    Color::Gray => {
                        // Back-edge u→v closes a cycle; reconstruct v..u.
                        return Some(reconstruct(v, u, &parent));
                    }
                    Color::Black => {}
                }
            } else {
                color.insert(u, Color::Black);
                stack.pop();
            }
        }
    }
    None
}

fn neighbours(
    adj: &BTreeMap<TermId, BTreeMap<TermId, (TermId, usize)>>,
    node_set: &BTreeSet<TermId>,
    u: TermId,
) -> Vec<TermId> {
    adj.get(&u)
        .map(|m| m.keys().copied().filter(|v| node_set.contains(v)).collect())
        .unwrap_or_default()
}

/// Reconstructs the cycle node list `[v, …, u]` from the DFS tree parents.
fn reconstruct(v: TermId, u: TermId, parent: &BTreeMap<TermId, TermId>) -> Vec<TermId> {
    let mut path = vec![u];
    let mut cur = u;
    while cur != v {
        cur = parent[&cur];
        path.push(cur);
    }
    path.reverse();
    path
}

/// Given a cycle node list, computes the ε targets (every off-cycle component of
/// every edge witness) and the shared cycle premise set.
fn cycle_epsilon(
    rep_forms: &BTreeMap<TermId, Vec<RepForm>>,
    cycle: &[TermId],
) -> (Vec<TermId>, BTreeSet<usize>) {
    // Rebuild adjacency to recover an edge witness per (from, to).
    let mut adj: BTreeMap<TermId, BTreeMap<TermId, (TermId, usize)>> = BTreeMap::new();
    for (&r, rfv) in rep_forms {
        for (fi, rf) in rfv.iter().enumerate() {
            if rf.comps.len() == 1 && rf.comps[0] == r {
                continue;
            }
            for &c in &rf.comps {
                adj.entry(r).or_default().entry(c).or_insert((r, fi));
            }
        }
    }

    let k = cycle.len();
    let mut targets: BTreeSet<TermId> = BTreeSet::new();
    let mut premises: BTreeSet<usize> = BTreeSet::new();
    for idx in 0..k {
        let from = cycle[idx];
        let to = cycle[(idx + 1) % k];
        let Some(&(_, fi)) = adj.get(&from).and_then(|m| m.get(&to)) else {
            continue;
        };
        let rf = &rep_forms[&from][fi];
        premises.extend(rf.cycle_prem.iter().copied());
        // The continuation component links to the next cycle node; the rest are
        // off-cycle and must be ε.
        let cont = rf
            .comps
            .iter()
            .position(|&c| c == to)
            .expect("edge witness contains the target");
        for (p, &c) in rf.comps.iter().enumerate() {
            if p != cont {
                targets.insert(c);
            }
        }
    }
    (targets.into_iter().collect(), premises)
}

// ----- alignment (rules b/c) --------------------------------------------------

/// Where the right-hand side of a pending fact points.
#[derive(Debug, Clone, Copy)]
enum FactTarget {
    /// A concrete term.
    Term(TermId),
    /// The empty sequence (built with the arena at materialization time).
    Epsilon,
}

/// A fact discovered during alignment, before ε materialization / dedup.
#[derive(Debug, Clone)]
struct PendingFact {
    rule: Rule,
    lhs: TermId,
    rhs: FactTarget,
    premises: BTreeSet<usize>,
}

/// The outcome of aligning two members' component vectors.
enum Aligned {
    /// A self-evident joint-unsatisfiability.
    Conflict {
        reason: ConflictReason,
        premises: BTreeSet<usize>,
    },
    /// Zero or more derived facts (an empty vector = fully consistent, or a
    /// declined arrangement).
    Facts(Vec<PendingFact>),
}

/// Aligns the component vectors of two members of one class (they denote the
/// same sequence). Consumes a provably-equal-length prefix left-to-right,
/// deriving `INFER_UNIFY` / `INFER_ENDPOINT_EQ` / `INFER_ENDPOINT_EMP` facts and
/// reporting a constant clash as a [`Aligned::Conflict`]; declines (stops) where
/// an arrangement branch would be needed.
fn align(classes: &Classes, arena: &TermArena, a: &MemberForm, b: &MemberForm) -> Aligned {
    // Running premise set: bases plus the asserted links used to advance.
    let mut prem = a.base.clone();
    prem.extend(b.base.iter().copied());

    let mut facts: Vec<PendingFact> = Vec::new();
    let (na, nb) = (a.atoms.len(), b.atoms.len());
    let (mut i, mut j) = (0usize, 0usize);

    while i < na && j < nb {
        let ca = a.atoms[i];
        let cb = b.atoms[j];

        // (1) genuinely equal (identical handle or equal-value constants).
        if terminal_equal(arena, ca, cb) {
            i += 1;
            j += 1;
            continue;
        }

        // (2) two distinct constants — the constant-facing rules / clash.
        let a_is_const = is_constant(arena, ca);
        let b_is_const = is_constant(arena, cb);
        if a_is_const && b_is_const {
            let la = structural_len(arena, ca).expect("constant has a length");
            let lb = structural_len(arena, cb).expect("constant has a length");
            if la == lb {
                return Aligned::Conflict {
                    reason: ConflictReason {
                        rule: "const-clash",
                        member_a: a.member,
                        member_b: b.member,
                        position_a: i,
                        position_b: j,
                        const_a: ca,
                        const_b: cb,
                    },
                    premises: prem,
                };
            }
            if !const_prefix_compatible(arena, ca, cb) {
                return Aligned::Conflict {
                    reason: ConflictReason {
                        rule: "const-prefix-mismatch",
                        member_a: a.member,
                        member_b: b.member,
                        position_a: i,
                        position_b: j,
                        const_a: ca,
                        const_b: cb,
                    },
                    premises: prem,
                };
            }
            // Length-compatible unequal constants: a deterministic constant split
            // (T-B.4). Decline the remainder.
            break;
        }

        // (3) asserted equal via the classes (at least one non-constant): advance
        // citing the link that makes the prefix lengths line up.
        if classes.representative(ca) == classes.representative(cb) {
            if let Some(e) = classes.explain(ca, cb) {
                prem.extend(e);
            }
            i += 1;
            j += 1;
            continue;
        }

        // (4) structural length reasoning (no LIA).
        match (structural_len(arena, ca), structural_len(arena, cb)) {
            (Some(la), Some(lb)) if la == lb => {
                // INFER_UNIFY: equal known length, not both constant.
                facts.push(PendingFact {
                    rule: Rule::InferUnify,
                    lhs: ca,
                    rhs: FactTarget::Term(cb),
                    premises: prem.clone(),
                });
                i += 1;
                j += 1;
            }
            (Some(_), Some(_)) => break, // known unequal length ⇒ F-Split (T-B.4).
            _ => {
                // Unknown length on some side.
                let a_last = i + 1 == na;
                let b_last = j + 1 == nb;
                if a_last && b_last {
                    // INFER_ENDPOINT_EQ: single remainder each side ⇒ equal.
                    facts.push(PendingFact {
                        rule: Rule::InferEndpointEq,
                        lhs: ca,
                        rhs: FactTarget::Term(cb),
                        premises: prem.clone(),
                    });
                    i += 1;
                    j += 1;
                } else {
                    break; // needs F-Split / Len-Split (T-B.4).
                }
            }
        }
    }

    // Endpoint tail: one side exhausted after an aligned prefix ⇒ the other
    // side's remaining components concatenate to ε (INFER_ENDPOINT_EMP).
    if i == na && j < nb {
        endpoint_empty(arena, &b.atoms[j..], &prem, &mut facts);
    } else if j == nb && i < na {
        endpoint_empty(arena, &a.atoms[i..], &prem, &mut facts);
    }

    Aligned::Facts(facts)
}

/// Emits an `INFER_ENDPOINT_EMP` fact for each non-ε remaining component.
fn endpoint_empty(
    arena: &TermArena,
    remaining: &[TermId],
    prem: &BTreeSet<usize>,
    facts: &mut Vec<PendingFact>,
) {
    for &c in remaining {
        if is_epsilon(arena, c) {
            continue;
        }
        facts.push(PendingFact {
            rule: Rule::InferEndpointEmp,
            lhs: c,
            rhs: FactTarget::Epsilon,
            premises: prem.clone(),
        });
    }
}

// ----- ground-evaluator helpers -----------------------------------------------

/// A structurally-determined length for `t`, or `None` when it depends on an
/// opaque sequence (a bare variable, a symbolic `substr`, …). This is the
/// *structure-only* length reasoning the rules are allowed to use — LIA length
/// entailment is out of scope for T-B.3.
#[must_use]
fn structural_len(arena: &TermArena, t: TermId) -> Option<u128> {
    if let Ok(Value::Seq(v)) = eval(arena, t, &Assignment::new()) {
        return u128::try_from(v.len()).ok();
    }
    match arena.node(t) {
        TermNode::App {
            op: Op::SeqUnit, ..
        } => Some(1),
        TermNode::App {
            op: Op::SeqEmpty(_),
            ..
        } => Some(0),
        TermNode::App {
            op: Op::SeqConcat,
            args,
        } => {
            let la = structural_len(arena, args[0])?;
            let lb = structural_len(arena, args[1])?;
            la.checked_add(lb)
        }
        _ => None,
    }
}

/// Whether the shorter of two constant sequences is a component-wise prefix of
/// the longer (so a deterministic constant split is possible rather than a
/// clash). `false` if either does not evaluate closed.
#[must_use]
fn const_prefix_compatible(arena: &TermArena, a: TermId, b: TermId) -> bool {
    let (Ok(Value::Seq(va)), Ok(Value::Seq(vb))) = (
        eval(arena, a, &Assignment::new()),
        eval(arena, b, &Assignment::new()),
    ) else {
        return false;
    };
    let (short, long) = if va.len() <= vb.len() {
        (&va, &vb)
    } else {
        (&vb, &va)
    };
    short.iter().zip(long.iter()).all(|(x, y)| x == y)
}

/// Whether two components are equal: identical handle, or both closed constants
/// of equal value.
#[must_use]
fn terminal_equal(arena: &TermArena, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    match (
        eval(arena, a, &Assignment::new()),
        eval(arena, b, &Assignment::new()),
    ) {
        (Ok(va), Ok(vb)) => va == vb,
        _ => false,
    }
}

/// Whether `t` evaluates closed under the ground evaluator (the constancy test).
#[must_use]
fn is_constant(arena: &TermArena, t: TermId) -> bool {
    eval(arena, t, &Assignment::new()).is_ok()
}

/// Whether `t` is the (constant) empty sequence.
#[must_use]
fn is_epsilon(arena: &TermArena, t: TermId) -> bool {
    if matches!(
        arena.node(t),
        TermNode::App {
            op: Op::SeqEmpty(_),
            ..
        }
    ) {
        return true;
    }
    matches!(eval(arena, t, &Assignment::new()), Ok(Value::Seq(v)) if v.is_empty())
}

/// Whether `rep`'s class contains an ε member (robust across representative
/// choice — a variable rep whose class also contains ε still counts).
#[must_use]
fn class_is_epsilon(classes: &Classes, arena: &TermArena, rep: TermId) -> bool {
    classes
        .class_members(rep)
        .into_iter()
        .any(|m| is_epsilon(arena, m))
}

/// The first ε member of `rep`'s class, if any.
#[must_use]
fn epsilon_member(classes: &Classes, arena: &TermArena, rep: TermId) -> Option<TermId> {
    classes
        .class_members(rep)
        .into_iter()
        .find(|&m| is_epsilon(arena, m))
}

/// The empty sequence over `t`'s element key, or `None` if `t` is not a
/// sequence.
#[must_use]
fn make_epsilon(arena: &mut TermArena, t: TermId) -> Option<TermId> {
    match arena.sort_of(t) {
        Sort::Seq(key) => Some(arena.seq_empty(key)),
        _ => None,
    }
}

/// Canonicalizes an unordered equality as `(min, max)` by [`TermId`].
#[must_use]
fn canon(a: TermId, b: TermId) -> (TermId, TermId) {
    if a <= b { (a, b) } else { (b, a) }
}
