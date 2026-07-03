//! Equivalence classes, **flat forms**, **normal forms**, and **explanation
//! tracking** (slice T-B.2) — the CAV-2014 (Liang–Reynolds–Tinelli) substrate
//! the word-equation core computes over.
//!
//! Given a caller-supplied slice of asserted `Seq`-sorted equalities, this
//! module builds a deterministic union-find over the endpoint terms, then
//! computes — bottom-up over an acyclic containment ordering — the CAV-2014
//! normal form of every equivalence class: a vector of sub-class
//! representatives such that concatenating them denotes the same sequence as
//! every member of the class.
//!
//! # What this slice computes, and what it declines
//!
//! T-B.2 is the *bookkeeping* slice: it computes flat/normal forms and tracks,
//! for every derived fact, the exact set of premise indices it depends on
//! (cvc5's `d_expDep`). It deliberately does **not** perform the T-B.3 / T-B.4
//! inference and arrangement rules (`INFER_UNIFY`, `F-Split`, `F-Loop`, constant
//! splitting). Where those would be required it **declines** rather than guess:
//!
//! * a **containment cycle** among classes (e.g. `x ≈ x ++ y`, which is a loop
//!   the later `F-Loop` machinery regularizes) yields [`Declined::Cycle`] —
//!   never an infinite loop;
//! * a class whose members' decompositions disagree in a way T-B.2 cannot
//!   reconcile by exact-vector-equality (unequal constant blocks, a
//!   constant-vs-variable position, differing component counts) yields
//!   [`Declined::Unreconciled`] — arrangement splitting is T-B.4's job.
//!
//! Declining is always sound: we never publish a wrong normal form.
//!
//! # Congruence boundary
//!
//! The union-find is over the *asserted* equalities only. It is **not** a
//! congruence closure: it does not infer `a ++ b ≈ a ++ c` from `b ≈ c`. That
//! congruence over `str.++` is the e-graph's responsibility
//! ([P1.4](../../plan/track-1-engine/P1.4-egraph.md)); this slice consumes an
//! equality set, it does not close one.
//!
//! # Determinism
//!
//! Every observable output is deterministic (ADR-0053, a public API promise).
//! The class representative is the **smallest [`TermId`] in the class** (a
//! structural consequence of union-by-minimum, documented on
//! [`Classes::representative`]); explanations are [`BTreeSet<usize>`]s;
//! normal-form maps are [`BTreeMap`]s keyed by representative; and every
//! internal traversal iterates in sorted [`TermId`] order. No hash-map
//! iteration order escapes into any result.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use axeyum_ir::{Assignment, Op, TermArena, TermId, TermNode, Value, eval};

use crate::normal_form::{concat_components, normalize};

/// Union-find `find` with path-halving over a `BTreeMap` parent forest. The
/// root is the smallest [`TermId`] in the class (union is always by minimum),
/// so path-halving cannot disturb the min-root invariant.
fn uf_find(parent: &mut BTreeMap<TermId, TermId>, t: TermId) -> TermId {
    let mut root = t;
    while let Some(&p) = parent.get(&root) {
        if p == root {
            break;
        }
        root = p;
    }
    let mut cur = t;
    while let Some(&p) = parent.get(&cur) {
        if p == root {
            break;
        }
        parent.insert(cur, root);
        cur = p;
    }
    root
}

/// A deterministic union-find over the endpoints of a set of asserted
/// `Seq`-sorted equalities, together with an equality graph for explanation
/// tracking.
///
/// Construct with [`Classes::new`] from `&[(TermId, TermId)]`; each pair is
/// implicitly indexed by its **position**, and that index is the *premise ID*
/// carried by every explanation. Every endpoint is expected to be a
/// `Sort::Seq` term over a shared [`TermArena`]; passing non-sequence terms is
/// a caller error (the structural union-find still runs, but flat/normal forms
/// are only meaningful for sequences).
#[derive(Debug, Clone)]
pub struct Classes {
    /// Number of asserted equalities (premise IDs are `0..n_premises`).
    n_premises: usize,
    /// Representative (smallest [`TermId`]) of every endpoint's class.
    rep_of: BTreeMap<TermId, TermId>,
    /// Endpoint members of each class, keyed by representative.
    members: BTreeMap<TermId, BTreeSet<TermId>>,
    /// Undirected equality graph: `t → { neighbour → premise index }`. The
    /// smallest premise index is kept for a repeated neighbour pair so
    /// explanations are deterministic and minimal per edge.
    adj: BTreeMap<TermId, BTreeMap<TermId, usize>>,
}

/// The **flat form** of a sequence term: its [`normalize`]d component vector
/// with each component replaced by its class representative, ε components
/// dropped, and adjacent constant blocks re-fused.
///
/// Each component carries the premise indices that justify replacing the
/// original component by the representative shown here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlatForm {
    /// The flat component vector (class representatives, no ε, no two adjacent
    /// constants).
    pub components: Vec<TermId>,
    /// Per-component premise dependencies, aligned with `components`.
    pub component_premises: Vec<BTreeSet<usize>>,
    /// The union of all component dependencies — a sufficient premise set for
    /// "this term's flat form is `components`".
    pub premises: BTreeSet<usize>,
}

/// The **normal form** of an equivalence class: the CAV-2014 vector of
/// sub-class representatives, anchored on the class representative
/// (`base`).
///
/// The derived fact is `base ≈ components₀ ++ … ++ componentsₙ`; `premises` is
/// a **sufficient** premise set for that fact (re-running the computation with
/// only those premises re-derives the same vector — this is the
/// soundness-relevant guarantee a later UNSAT derivation cites).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalForm {
    /// The class representative this normal form is anchored on.
    pub base: TermId,
    /// The normal-form vector of sub-class representatives (empty for the
    /// ε class).
    pub components: Vec<TermId>,
    /// Per-component premise dependencies, aligned with `components`.
    pub component_premises: Vec<BTreeSet<usize>>,
    /// The union of all dependencies — a sufficient premise set for
    /// `base ≈ concat(components)`.
    pub premises: BTreeSet<usize>,
}

/// The normal forms of every equivalence class, keyed by representative.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormalForms {
    by_rep: BTreeMap<TermId, NormalForm>,
}

/// A structured decline: T-B.2 will not guess where the later inference /
/// arrangement rules are required.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Declined {
    /// The class containment relation has a cycle (some class occurs in the
    /// flat form of a member of a class it transitively contains, e.g.
    /// `x ≈ x ++ y`). The involved class representatives are listed, sorted.
    /// Cycle-breaking is the later `F-Loop` device (T-B.5); T-B.2 refuses to
    /// unfold a loop.
    Cycle {
        /// The representatives of the classes participating in the cycle.
        classes: Vec<TermId>,
    },
    /// A class's members decompose to vectors T-B.2 cannot reconcile without
    /// the T-B.3 inference rules or T-B.4 arrangement splitting.
    Unreconciled {
        /// The representative of the offending class.
        class: TermId,
        /// Why reconciliation failed.
        kind: Unreconciled,
    },
}

/// The reason a class could not be reconciled by T-B.2's exact-vector rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Unreconciled {
    /// Two members reduce to different constant blocks at the same position
    /// (a genuine contradiction, e.g. `x ≈ "a"` and `x ≈ "b"`).
    ConstantClash,
    /// Two members reduce to vectors of differing shape (different lengths, or
    /// a constant facing a variable) that only arrangement splitting (T-B.4)
    /// could align.
    ShapeMismatch,
}

impl Classes {
    /// Builds the equivalence classes from `equalities`, each pair positionally
    /// indexed as its premise ID.
    ///
    /// The union-find uses **union by minimum [`TermId`]**, so the root — and
    /// therefore the representative — of every class is the smallest
    /// [`TermId`] it contains. Reflexive pairs (`a ≈ a`) and non-sequence
    /// endpoints are accepted; the former are no-ops, the latter simply form
    /// structural classes whose flat/normal forms are not meaningful.
    #[must_use]
    pub fn new(equalities: &[(TermId, TermId)]) -> Self {
        // Union-find with union-by-minimum: the root is always the smallest id.
        let mut parent: BTreeMap<TermId, TermId> = BTreeMap::new();
        let mut adj: BTreeMap<TermId, BTreeMap<TermId, usize>> = BTreeMap::new();
        for (idx, &(a, b)) in equalities.iter().enumerate() {
            parent.entry(a).or_insert(a);
            parent.entry(b).or_insert(b);
            if a != b {
                // Keep the smallest premise index for a repeated pair.
                adj.entry(a).or_default().entry(b).or_insert(idx);
                adj.entry(b).or_default().entry(a).or_insert(idx);
                let ra = uf_find(&mut parent, a);
                let rb = uf_find(&mut parent, b);
                if ra != rb {
                    let (root, child) = if ra < rb { (ra, rb) } else { (rb, ra) };
                    parent.insert(child, root);
                }
            }
        }

        // Materialize representatives and members for every endpoint.
        let mut rep_of: BTreeMap<TermId, TermId> = BTreeMap::new();
        let endpoints: BTreeSet<TermId> = parent.keys().copied().collect();
        for &t in &endpoints {
            let r = uf_find(&mut parent, t);
            rep_of.insert(t, r);
        }
        let mut members: BTreeMap<TermId, BTreeSet<TermId>> = BTreeMap::new();
        for (&t, &r) in &rep_of {
            members.entry(r).or_default().insert(t);
        }

        Self {
            n_premises: equalities.len(),
            rep_of,
            members,
            adj,
        }
    }

    /// The number of asserted equalities (valid premise IDs are
    /// `0..self.premise_count()`).
    #[must_use]
    pub fn premise_count(&self) -> usize {
        self.n_premises
    }

    /// The representative of `t`'s class — the **smallest [`TermId`]** in the
    /// class. A term that appears in no asserted equality is its own singleton
    /// class, so it is its own representative.
    #[must_use]
    pub fn representative(&self, t: TermId) -> TermId {
        self.rep_of.get(&t).copied().unwrap_or(t)
    }

    /// The members of `t`'s class among the asserted endpoints, sorted. A term
    /// in no equality yields the singleton `[t]`.
    #[must_use]
    pub fn class_members(&self, t: TermId) -> Vec<TermId> {
        let r = self.representative(t);
        match self.members.get(&r) {
            Some(m) => m.iter().copied().collect(),
            None => vec![t],
        }
    }

    /// A **sufficient** premise set explaining `a ≈ b`, or `None` if they are
    /// in different classes.
    ///
    /// Returns the empty set for `a == b`. Otherwise this is the set of premise
    /// indices along a shortest path between `a` and `b` in the equality graph
    /// — sufficient (each edge is an asserted equality, so their conjunction
    /// entails `a ≈ b`) though not necessarily globally minimal.
    #[must_use]
    pub fn explain(&self, a: TermId, b: TermId) -> Option<BTreeSet<usize>> {
        if a == b {
            return Some(BTreeSet::new());
        }
        // BFS with deterministic (sorted) neighbour iteration.
        let mut prev: BTreeMap<TermId, (TermId, usize)> = BTreeMap::new();
        let mut seen: BTreeSet<TermId> = BTreeSet::new();
        let mut queue: VecDeque<TermId> = VecDeque::new();
        seen.insert(a);
        queue.push_back(a);
        while let Some(cur) = queue.pop_front() {
            if cur == b {
                let mut out = BTreeSet::new();
                let mut node = b;
                while node != a {
                    let (p, idx) = prev[&node];
                    out.insert(idx);
                    node = p;
                }
                return Some(out);
            }
            if let Some(neigh) = self.adj.get(&cur) {
                for (&next, &idx) in neigh {
                    if seen.insert(next) {
                        prev.insert(next, (cur, idx));
                        queue.push_back(next);
                    }
                }
            }
        }
        None
    }

    /// The [`FlatForm`] of `term`: its [`normalize`]d components, each replaced
    /// by its class representative, ε dropped, adjacent constants re-fused.
    #[must_use]
    pub fn flat_form(&self, arena: &mut TermArena, term: TermId) -> FlatForm {
        let norm = normalize(arena, term);
        let raw = concat_components(arena, norm);

        // Substitute each component by its representative, dropping ε reps.
        let mut subbed: Vec<(TermId, BTreeSet<usize>)> = Vec::new();
        for c in raw {
            let r = self.representative(c);
            if is_epsilon(arena, r) {
                continue;
            }
            let prem = self.explain(c, r).unwrap_or_default();
            subbed.push((r, prem));
        }

        let fused = fuse_adjacent_constants(arena, subbed);
        let mut premises = BTreeSet::new();
        let mut components = Vec::with_capacity(fused.len());
        let mut component_premises = Vec::with_capacity(fused.len());
        for (t, p) in fused {
            premises.extend(p.iter().copied());
            components.push(t);
            component_premises.push(p);
        }
        FlatForm {
            components,
            component_premises,
            premises,
        }
    }

    /// Computes the normal form of every equivalence class, bottom-up over the
    /// acyclic class-containment ordering.
    ///
    /// Returns [`Declined::Cycle`] on a containment cycle and
    /// [`Declined::Unreconciled`] on a class whose members disagree beyond
    /// T-B.2's exact-vector reconciliation. On success, every class reachable
    /// from an asserted endpoint (and every singleton sub-class referenced by a
    /// flat form) has a normal form.
    ///
    /// # Errors
    ///
    /// See [`Declined`].
    pub fn normal_forms(&self, arena: &mut TermArena) -> Result<NormalForms, Declined> {
        // ---- discovery: flat forms, class members, containment deps ---------
        let mut flat_cache: BTreeMap<TermId, FlatForm> = BTreeMap::new();
        let mut ext_members: BTreeMap<TermId, BTreeSet<TermId>> = self.members.clone();
        let mut deps: BTreeMap<TermId, BTreeSet<TermId>> = BTreeMap::new();
        let mut self_cycles: BTreeSet<TermId> = BTreeSet::new();

        let mut visited: BTreeSet<TermId> = BTreeSet::new();
        let mut work: VecDeque<TermId> = ext_members.keys().copied().collect();
        // Also seed every endpoint's representative explicitly.
        for r in self.members.keys() {
            deps.entry(*r).or_default();
        }

        while let Some(rc) = work.pop_front() {
            if !visited.insert(rc) {
                continue;
            }
            deps.entry(rc).or_default();
            // Snapshot members so we can mutate ext_members while iterating.
            let members: Vec<TermId> = ext_members
                .get(&rc)
                .map_or_else(|| vec![rc], |m| m.iter().copied().collect());
            for m in members {
                let ff = flat_cache
                    .entry(m)
                    .or_insert_with(|| self.flat_form(arena, m))
                    .clone();
                // Atomic self-member: contributes nothing, creates no edge.
                if ff.components == [rc] {
                    continue;
                }
                for &c in &ff.components {
                    let d = self.representative(c);
                    ext_members.entry(d).or_default().insert(c);
                    if !visited.contains(&d) {
                        work.push_back(d);
                    }
                    if d == rc {
                        // Self-containment: a loop for the later F-Loop device.
                        self_cycles.insert(rc);
                    } else {
                        deps.entry(rc).or_default().insert(d);
                    }
                }
            }
        }

        if !self_cycles.is_empty() {
            return Err(Declined::Cycle {
                classes: self_cycles.into_iter().collect(),
            });
        }

        // ---- topological order (Kahn), deterministic by rep --------------
        let order =
            topo_order(&deps).map_err(|remaining| Declined::Cycle { classes: remaining })?;

        // ---- bottom-up normal-form computation ---------------------------
        let mut by_rep: BTreeMap<TermId, NormalForm> = BTreeMap::new();
        for rc in order {
            let nf = self.normalize_class(arena, rc, &ext_members, &flat_cache, &by_rep)?;
            by_rep.insert(rc, nf);
        }

        Ok(NormalForms { by_rep })
    }

    /// Computes the normal form of a single class, given the normal forms of
    /// every class it depends on (all strictly smaller in the containment
    /// order, hence already in `computed`).
    fn normalize_class(
        &self,
        arena: &mut TermArena,
        rc: TermId,
        ext_members: &BTreeMap<TermId, BTreeSet<TermId>>,
        flat_cache: &BTreeMap<TermId, FlatForm>,
        computed: &BTreeMap<TermId, NormalForm>,
    ) -> Result<NormalForm, Declined> {
        let members: Vec<TermId> = ext_members
            .get(&rc)
            .map_or_else(|| vec![rc], |m| m.iter().copied().collect());

        // Each informative member yields a candidate terminal vector.
        let mut candidates: Vec<Candidate> = Vec::new();
        for m in members {
            if is_constant(arena, m) {
                // A constant member fixes the class to that constant block.
                let base_link = self.explain(rc, m).unwrap_or_default();
                if is_epsilon(arena, m) {
                    candidates.push(Candidate {
                        components: Vec::new(),
                        component_premises: Vec::new(),
                        premises: base_link,
                    });
                } else {
                    candidates.push(Candidate {
                        components: vec![m],
                        component_premises: vec![base_link.clone()],
                        premises: base_link,
                    });
                }
                continue;
            }
            let Some(ff) = flat_cache.get(&m) else {
                continue;
            };
            if ff.components == [rc] {
                // Atomic self-member: no decomposition information.
                continue;
            }
            let base_link = self.explain(rc, m).unwrap_or_default();
            let mut components = Vec::new();
            let mut component_premises = Vec::new();
            let mut premises = base_link.clone();
            for (c, cprem) in ff.components.iter().zip(&ff.component_premises) {
                // `c` is a class representative; splice in its normal form.
                let sub = computed
                    .get(c)
                    .expect("dependency normal form computed before dependent");
                for (sc, scprem) in sub.components.iter().zip(&sub.component_premises) {
                    let mut here = base_link.clone();
                    here.extend(cprem.iter().copied());
                    here.extend(scprem.iter().copied());
                    premises.extend(here.iter().copied());
                    components.push(*sc);
                    component_premises.push(here);
                }
                premises.extend(cprem.iter().copied());
                premises.extend(sub.premises.iter().copied());
            }
            candidates.push(Candidate {
                components,
                component_premises,
                premises,
            });
        }

        // Purely self-referential (variable) atomic class.
        if candidates.is_empty() {
            return Ok(NormalForm {
                base: rc,
                components: vec![rc],
                component_premises: vec![BTreeSet::new()],
                premises: BTreeSet::new(),
            });
        }

        // Canonicalize each candidate (fuse adjacent constants) and reconcile
        // by exact terminal-vector equality. The first (smallest source
        // member; `members` is sorted) anchors the published vector and its
        // per-component dependencies.
        let canon: Vec<Candidate> = candidates
            .into_iter()
            .map(|c| c.canonicalize(arena))
            .collect();
        let base_candidate = &canon[0];
        for other in &canon[1..] {
            if !terminal_vectors_equal(arena, &base_candidate.components, &other.components) {
                let kind = classify_mismatch(arena, &base_candidate.components, &other.components);
                return Err(Declined::Unreconciled { class: rc, kind });
            }
        }

        // The class-level premise set is the union over *every* reconciled
        // member's derivation. This is sufficient (a superset of the anchor's
        // own chain) and — crucially — self-contained: re-running the
        // computation on exactly these premises re-derives the same vector,
        // because every member that the premises connect into the class still
        // carries its own alignment evidence and reconciles to it. (The
        // explain path to the anchor can traverse a sibling decomposing member;
        // citing only the anchor's chain would import that sibling without its
        // evidence.)
        let mut premises = BTreeSet::new();
        for c in &canon {
            premises.extend(c.premises.iter().copied());
        }

        Ok(NormalForm {
            base: rc,
            components: base_candidate.components.clone(),
            component_premises: base_candidate.component_premises.clone(),
            premises,
        })
    }
}

impl NormalForms {
    /// The normal form anchored on class representative `rep`, if computed.
    #[must_use]
    pub fn get(&self, rep: TermId) -> Option<&NormalForm> {
        self.by_rep.get(&rep)
    }

    /// Iterates `(representative, normal form)` pairs in sorted representative
    /// order.
    pub fn iter(&self) -> impl Iterator<Item = (TermId, &NormalForm)> {
        self.by_rep.iter().map(|(&r, nf)| (r, nf))
    }

    /// The number of classes with a computed normal form.
    #[must_use]
    pub fn len(&self) -> usize {
        self.by_rep.len()
    }

    /// Whether no class has a normal form.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.by_rep.is_empty()
    }
}

/// A per-member candidate terminal vector during class normalization.
#[derive(Debug, Clone)]
struct Candidate {
    components: Vec<TermId>,
    component_premises: Vec<BTreeSet<usize>>,
    premises: BTreeSet<usize>,
}

impl Candidate {
    /// Fuses adjacent constant components (denotation-preserving) so vectors
    /// from differently-shaped members become directly comparable.
    fn canonicalize(self, arena: &mut TermArena) -> Self {
        let items: Vec<(TermId, BTreeSet<usize>)> = self
            .components
            .into_iter()
            .zip(self.component_premises)
            .collect();
        let fused = fuse_adjacent_constants(arena, items);
        let mut components = Vec::with_capacity(fused.len());
        let mut component_premises = Vec::with_capacity(fused.len());
        for (t, p) in fused {
            components.push(t);
            component_premises.push(p);
        }
        Self {
            components,
            component_premises,
            premises: self.premises,
        }
    }
}

// ----- containment ordering ---------------------------------------------------

/// Kahn topological sort over the class-containment graph, iterating in sorted
/// representative order for determinism. On a cycle, returns the sorted set of
/// representatives that could not be ordered.
fn topo_order(deps: &BTreeMap<TermId, BTreeSet<TermId>>) -> Result<Vec<TermId>, Vec<TermId>> {
    // `deps[c]` = classes that must precede `c`. Build the dependents map and
    // the in-degree (number of prerequisites) for every node.
    let mut indeg: BTreeMap<TermId, usize> = BTreeMap::new();
    let mut dependents: BTreeMap<TermId, BTreeSet<TermId>> = BTreeMap::new();
    for (&c, pre) in deps {
        indeg.entry(c).or_insert(0);
        for &p in pre {
            indeg.entry(p).or_insert(0);
        }
    }
    for (&c, pre) in deps {
        *indeg.get_mut(&c).expect("node has in-degree") = pre.len();
        for &p in pre {
            dependents.entry(p).or_default().insert(c);
        }
    }

    let mut ready: BTreeSet<TermId> = indeg
        .iter()
        .filter_map(|(&c, &d)| (d == 0).then_some(c))
        .collect();
    let mut order = Vec::with_capacity(indeg.len());
    while let Some(&c) = ready.iter().next() {
        ready.remove(&c);
        order.push(c);
        if let Some(deps_on_c) = dependents.get(&c) {
            for &k in deps_on_c {
                let e = indeg.get_mut(&k).expect("dependent has in-degree");
                *e -= 1;
                if *e == 0 {
                    ready.insert(k);
                }
            }
        }
    }

    if order.len() == indeg.len() {
        Ok(order)
    } else {
        let ordered: BTreeSet<TermId> = order.into_iter().collect();
        let remaining: Vec<TermId> = indeg
            .keys()
            .copied()
            .filter(|c| !ordered.contains(c))
            .collect();
        Err(remaining)
    }
}

// ----- constant fusion / comparison ------------------------------------------

/// Fuses each maximal run of ≥2 adjacent constant components into a single
/// right-associated constant block (denotation-preserving); premises of a fused
/// block are the union of the run's premises. ε components are dropped.
fn fuse_adjacent_constants(
    arena: &mut TermArena,
    items: Vec<(TermId, BTreeSet<usize>)>,
) -> Vec<(TermId, BTreeSet<usize>)> {
    // Drop ε first so runs are of non-empty constants.
    let items: Vec<(TermId, BTreeSet<usize>)> = items
        .into_iter()
        .filter(|(t, _)| !is_epsilon(arena, *t))
        .collect();

    let mut out: Vec<(TermId, BTreeSet<usize>)> = Vec::new();
    let mut i = 0;
    while i < items.len() {
        if is_constant(arena, items[i].0) {
            let start = i;
            while i < items.len() && is_constant(arena, items[i].0) {
                i += 1;
            }
            let run = &items[start..i];
            if run.len() == 1 {
                out.push(run[0].clone());
            } else {
                // Fold into one constant block; if the builder ever declines,
                // keep the run unfused (sound — just less canonical).
                match fold_concat(arena, run.iter().map(|(t, _)| *t)) {
                    Some(block) => {
                        let mut prem = BTreeSet::new();
                        for (_, p) in run {
                            prem.extend(p.iter().copied());
                        }
                        out.push((block, prem));
                    }
                    None => out.extend(run.iter().cloned()),
                }
            }
        } else {
            out.push(items[i].clone());
            i += 1;
        }
    }
    out
}

/// Right-associated `str.++` of a non-empty sequence of terms, or `None` on a
/// builder error.
fn fold_concat(arena: &mut TermArena, parts: impl IntoIterator<Item = TermId>) -> Option<TermId> {
    let parts: Vec<TermId> = parts.into_iter().collect();
    let mut acc = *parts.last()?;
    for &part in parts[..parts.len() - 1].iter().rev() {
        acc = arena.seq_concat(part, acc).ok()?;
    }
    Some(acc)
}

/// Whether two terminal vectors denote the same sequence *structurally* under
/// T-B.2's rules: equal length, and at each position either the same
/// [`TermId`] or two constants of equal value.
fn terminal_vectors_equal(arena: &TermArena, a: &[TermId], b: &[TermId]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter().zip(b).all(|(&x, &y)| terminal_equal(arena, x, y))
}

/// Whether two terminal components are equal: identical handles, or both
/// constant with equal value.
fn terminal_equal(arena: &TermArena, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    match (eval_closed(arena, a), eval_closed(arena, b)) {
        (Some(va), Some(vb)) => va == vb,
        _ => false,
    }
}

/// Classifies why two terminal vectors differ, for the [`Declined::Unreconciled`]
/// reason.
fn classify_mismatch(arena: &TermArena, a: &[TermId], b: &[TermId]) -> Unreconciled {
    let n = a.len().min(b.len());
    for i in 0..n {
        if terminal_equal(arena, a[i], b[i]) {
            continue;
        }
        let ca = is_constant(arena, a[i]);
        let cb = is_constant(arena, b[i]);
        if ca && cb {
            return Unreconciled::ConstantClash;
        }
        return Unreconciled::ShapeMismatch;
    }
    // Equal up to the shorter length but different lengths.
    Unreconciled::ShapeMismatch
}

// ----- ground-evaluator helpers ----------------------------------------------

/// The closed value of `term` (no free symbols), or `None` if it does not
/// evaluate closed.
fn eval_closed(arena: &TermArena, term: TermId) -> Option<Value> {
    eval(arena, term, &Assignment::new()).ok()
}

/// Whether `term` evaluates closed — the constancy test.
fn is_constant(arena: &TermArena, term: TermId) -> bool {
    // A cheap syntactic short-circuit for the ubiquitous ε / unit / concat
    // shapes avoids an eval where possible, but eval is authoritative.
    matches!(
        arena.node(term),
        TermNode::App {
            op: Op::SeqEmpty(_),
            ..
        }
    ) || eval_closed(arena, term).is_some()
}

/// Whether `term` is the (constant) empty sequence.
fn is_epsilon(arena: &TermArena, term: TermId) -> bool {
    if matches!(
        arena.node(term),
        TermNode::App {
            op: Op::SeqEmpty(_),
            ..
        }
    ) {
        return true;
    }
    matches!(eval_closed(arena, term), Some(Value::Seq(v)) if v.is_empty())
}
