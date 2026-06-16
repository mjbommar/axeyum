//! Incremental congruence-closure e-graph (Track 1, P1.4 — keystone).
//!
//! This is the shared **equality bus** for the reasoning stack: a backtrackable
//! union-find over e-nodes plus a signature (hash-cons) table that closes
//! congruence incrementally. Almost every eager→lazy theory upgrade in Track 2
//! (EUF, lazy arrays, datatypes, arithmetic equality propagation, and all
//! quantifier work) is built on it, so it is the keystone the reference review
//! flagged as "do first".
//!
//! Phase P1.4 is complete: e-node creation with hash-consing + a union-find
//! `find` and the deferred-merge cascade that closes transitive congruence
//! (T1.4.1/T1.4.2); a Nieuwenhuis–Oliveras proof forest with `explain`-to-LCA
//! (T1.4.3); a backtrackable [`EGraph::push`]/[`EGraph::pop`] trail (T1.4.4); the
//! independent [`check_congruence`] re-validator (T1.4.5); and per-class
//! theory-variable lists for the equality bus (T1.4.6). Next is the CDCL(T) loop
//! (P1.5) that drives this structure from the SAT core.
//!
//! ## Model
//!
//! An e-node is a function symbol (`decl`, a caller-assigned `u32`) applied to
//! argument e-nodes. A **leaf** (variable or constant) is a nullary application
//! with a unique `decl`. Two nodes are **congruent** — and therefore in the same
//! class — iff they have the same `decl` and their arguments are pairwise in the
//! same class. [`EGraph::merge`] asserts two classes equal; the cascade propagates
//! the consequences (`f(a) ~ f(b)` once `a ~ b`).
//!
//! Handles are lifetime-free `Copy` ids ([`ENodeId`]) per the project rule; never
//! pointers or borrows.

#![forbid(unsafe_code)]

use std::collections::HashMap;

/// A lifetime-free `Copy` handle to an e-node.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ENodeId(u32);

impl ENodeId {
    /// The zero-based index of this node.
    #[must_use]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A hash-cons key: a function symbol applied to the **current class roots** of
/// its arguments. Two e-nodes are congruent iff they share this key.
type Signature = (u32, Vec<ENodeId>);

/// The justification of one edge in the proof forest (T1.4.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Edge {
    /// An input equality the caller asserted, tagged with its reason id (e.g. the
    /// SAT literal that asserted it). `explain` returns these.
    Input(u32),
    /// The two endpoints became equal by congruence (same `decl`, pairwise-equal
    /// arguments); `explain` recovers the premises from the argument explanations.
    Congruence,
}

/// One e-node: a `decl` applied to `args`, with its union-find root, class size,
/// the parent nodes that reference its class, and its edge in the **proof forest**
/// (a structure separate from the union-find, used only for explanations).
#[derive(Debug, Clone)]
struct ENode {
    decl: u32,
    args: Vec<ENodeId>,
    /// Union-find parent; a root points to itself.
    root: ENodeId,
    /// Union-by-size weight (meaningful on roots).
    size: u32,
    /// Nodes that have this node's class among their arguments (use list).
    parents: Vec<ENodeId>,
    /// Proof-forest parent (independent of the union-find); `None` at a tree root.
    proof_parent: Option<ENodeId>,
    /// Justification of the edge to [`Self::proof_parent`].
    proof_edge: Option<Edge>,
    /// Theory variables attached to this node's class (meaningful on roots; a child
    /// keeps its own list, which is restored when a union is backtracked).
    th_vars: Vec<u32>,
}

/// One reversible mutation recorded on the backtracking trail (T1.4.4).
#[derive(Debug, Clone)]
enum Undo {
    /// A node was pushed; undo pops it.
    NodeAdded,
    /// `node`'s `parents` had one entry pushed; undo pops it.
    ParentPushed { node: ENodeId },
    /// `node`'s entire `parents` vector was replaced; undo restores the old one.
    ParentsTaken { node: ENodeId, old: Vec<ENodeId> },
    /// `child` (then its own root) was unioned into `root`, whose size grew by
    /// `child_size`; undo detaches `child` and restores the size.
    Unioned {
        child: ENodeId,
        root: ENodeId,
        child_size: u32,
    },
    /// A signature-table key was inserted; undo removes it.
    TableInserted { key: Signature },
    /// A signature-table key was removed (it mapped to `value`); undo re-inserts.
    TableRemoved { key: Signature, value: ENodeId },
    /// Proof-forest pointers were rewritten (re-rooting + a new edge); undo restores
    /// each saved `(node, old_parent, old_edge)`.
    ProofRewritten {
        saved: Vec<(ENodeId, Option<ENodeId>, Option<Edge>)>,
    },
    /// One theory variable was attached to `node`'s class; undo pops it.
    ThVarAttached { node: ENodeId },
    /// `count` theory variables were appended to `node`'s class on a union; undo
    /// truncates them back.
    ThVarsMerged { node: ENodeId, count: usize },
}

/// An incremental, **backtrackable** congruence-closure e-graph.
#[derive(Debug, Default)]
pub struct EGraph {
    nodes: Vec<ENode>,
    /// Signature table: a canonical signature maps to the node that owns it.
    table: HashMap<Signature, ENodeId>,
    /// Pending equalities to process (deferred-merge worklist), each carrying the
    /// justification for the proof forest.
    pending: Vec<(ENodeId, ENodeId, Edge)>,
    /// Reversible mutations since the start, for `pop`.
    trail: Vec<Undo>,
    /// Trail lengths at each `push`; `pop` rewinds to the last.
    scopes: Vec<usize>,
}

impl EGraph {
    /// Creates an empty e-graph.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of e-nodes created (distinct congruence-merged terms share a node).
    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the e-graph has no e-nodes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// The function symbol (`decl`) of node `id` — immutable term structure, used
    /// by the independent checker [`check_congruence`].
    #[must_use]
    pub fn decl(&self, id: ENodeId) -> u32 {
        self.nodes[id.index()].decl
    }

    /// The argument nodes of `id` — immutable term structure.
    #[must_use]
    pub fn args(&self, id: ENodeId) -> &[ENodeId] {
        &self.nodes[id.index()].args
    }

    /// Attaches theory variable `th_var` to the class of `node` (T1.4.6). When two
    /// classes merge their theory-variable lists are concatenated, so a theory can
    /// detect that two of its variables have become equal (the interface-equality
    /// bus for Nelson–Oppen / CDCL(T)). Reversed by [`Self::pop`].
    pub fn attach_th_var(&mut self, node: ENodeId, th_var: u32) {
        let root = self.root(node);
        self.nodes[root.index()].th_vars.push(th_var);
        self.trail.push(Undo::ThVarAttached { node: root });
    }

    /// The theory variables attached to the class of `node`.
    #[must_use]
    pub fn th_vars(&self, node: ENodeId) -> &[u32] {
        let root = self.root(node);
        &self.nodes[root.index()].th_vars
    }

    /// Adds the application `decl(args)`, returning its class representative. If a
    /// congruent node already exists it is returned (hash-consing); otherwise a
    /// fresh node is created. Leaves are `add(unique_decl, &[])`.
    ///
    /// # Panics
    ///
    /// Panics if any argument id was not produced by this e-graph.
    pub fn add(&mut self, decl: u32, args: &[ENodeId]) -> ENodeId {
        let sig = self.signature(decl, args);
        if let Some(&existing) = self.table.get(&sig) {
            return self.find(existing);
        }
        let id = ENodeId(u32::try_from(self.nodes.len()).expect("e-node count fits in u32"));
        self.nodes.push(ENode {
            decl,
            args: args.to_vec(),
            root: id,
            size: 1,
            parents: Vec::new(),
            proof_parent: None,
            proof_edge: None,
            th_vars: Vec::new(),
        });
        self.trail.push(Undo::NodeAdded);
        for &arg in args {
            let root = self.find(arg);
            self.nodes[root.index()].parents.push(id);
            self.trail.push(Undo::ParentPushed { node: root });
        }
        self.table.insert(sig.clone(), id);
        self.trail.push(Undo::TableInserted { key: sig });
        id
    }

    /// The current class representative of `id`.
    ///
    /// Path compression is deliberately omitted so the union-find is cheaply
    /// **backtrackable** (a union is undone by a single record); union-by-size
    /// keeps `find` at `O(log n)`. Takes `&mut self` for call-site symmetry with
    /// the mutating operations.
    pub fn find(&mut self, id: ENodeId) -> ENodeId {
        self.root(id)
    }

    /// The class representative (non-mutating walk to the union-find root).
    #[must_use]
    pub fn root(&self, mut id: ENodeId) -> ENodeId {
        while self.nodes[id.index()].root != id {
            id = self.nodes[id.index()].root;
        }
        id
    }

    /// Whether `a` and `b` are in the same class.
    #[must_use]
    pub fn equal(&self, a: ENodeId, b: ENodeId) -> bool {
        self.root(a) == self.root(b)
    }

    /// Asserts `a = b` (justified by the caller's `reason` id) and closes
    /// congruence over the consequences. The `reason` is what [`Self::explain`]
    /// returns for equalities that depend on this assertion.
    pub fn merge(&mut self, a: ENodeId, b: ENodeId, reason: u32) {
        self.pending.push((a, b, Edge::Input(reason)));
        self.process_pending();
    }

    /// Opens a new backtracking scope. Every node, equality, and congruence added
    /// after this is undone by the matching [`Self::pop`].
    pub fn push(&mut self) {
        self.scopes.push(self.trail.len());
    }

    /// The current scope depth (number of open [`Self::push`]es).
    #[must_use]
    pub fn scope_depth(&self) -> usize {
        self.scopes.len()
    }

    /// Closes the most recent scope, reverting every mutation since its
    /// [`Self::push`]. No-op if no scope is open.
    pub fn pop(&mut self) {
        let Some(mark) = self.scopes.pop() else {
            return;
        };
        while self.trail.len() > mark {
            if let Some(undo) = self.trail.pop() {
                self.revert(undo);
            }
        }
    }

    /// Reverts a single trailed mutation.
    fn revert(&mut self, undo: Undo) {
        match undo {
            Undo::NodeAdded => {
                self.nodes.pop();
            }
            Undo::ParentPushed { node } => {
                self.nodes[node.index()].parents.pop();
            }
            Undo::ParentsTaken { node, old } => {
                self.nodes[node.index()].parents = old;
            }
            Undo::Unioned {
                child,
                root,
                child_size,
            } => {
                self.nodes[child.index()].root = child;
                self.nodes[root.index()].size -= child_size;
            }
            Undo::TableInserted { key } => {
                self.table.remove(&key);
            }
            Undo::TableRemoved { key, value } => {
                self.table.insert(key, value);
            }
            Undo::ProofRewritten { saved } => {
                for (node, parent, edge) in saved {
                    self.nodes[node.index()].proof_parent = parent;
                    self.nodes[node.index()].proof_edge = edge;
                }
            }
            Undo::ThVarAttached { node } => {
                self.nodes[node.index()].th_vars.pop();
            }
            Undo::ThVarsMerged { node, count } => {
                let new_len = self.nodes[node.index()].th_vars.len() - count;
                self.nodes[node.index()].th_vars.truncate(new_len);
            }
        }
    }

    /// The hash-cons signature of `decl(args)` under the current union-find.
    fn signature(&mut self, decl: u32, args: &[ENodeId]) -> Signature {
        let roots = args.iter().map(|&a| self.find(a)).collect();
        (decl, roots)
    }

    /// The hash-cons signature of an existing node `id`.
    fn signature_of(&mut self, id: ENodeId) -> Signature {
        let decl = self.nodes[id.index()].decl;
        let args = self.nodes[id.index()].args.clone();
        self.signature(decl, &args)
    }

    /// Drains the merge worklist, re-canonicalizing parents to cascade congruence.
    fn process_pending(&mut self) {
        while let Some((a, b, edge)) = self.pending.pop() {
            let ra = self.find(a);
            let rb = self.find(b);
            if ra == rb {
                continue;
            }

            // Record the proof-forest edge between the *original* endpoints (not
            // the union-find roots): re-root `a`'s proof tree at `a`, then link
            // a → b with this justification. The proof forest stays separate from
            // the union-find and is used only by `explain`.
            self.add_proof_edge(a, b, edge);

            // Union by size: keep the larger class as the new root.
            let (root, child) = if self.nodes[ra.index()].size >= self.nodes[rb.index()].size {
                (ra, rb)
            } else {
                (rb, ra)
            };

            // Detach the child's parents and remove their *pre-union* signatures
            // from the table (the keys still reflect the old roots).
            let child_parents = std::mem::take(&mut self.nodes[child.index()].parents);
            self.trail.push(Undo::ParentsTaken {
                node: child,
                old: child_parents.clone(),
            });
            for &p in &child_parents {
                let key = self.signature_of(p);
                if self.table.get(&key) == Some(&p) {
                    self.table.remove(&key);
                    self.trail.push(Undo::TableRemoved { key, value: p });
                }
            }

            // Union.
            self.nodes[child.index()].root = root;
            let child_size = self.nodes[child.index()].size;
            self.nodes[root.index()].size += child_size;
            self.trail.push(Undo::Unioned {
                child,
                root,
                child_size,
            });

            // Move the child class's theory variables onto the new root (the child
            // keeps its own copy, restored if this union is backtracked).
            let child_th_vars = self.nodes[child.index()].th_vars.clone();
            if !child_th_vars.is_empty() {
                let count = child_th_vars.len();
                self.nodes[root.index()].th_vars.extend(child_th_vars);
                self.trail.push(Undo::ThVarsMerged { node: root, count });
            }

            // Re-insert the parents under their *post-union* signatures; a collision
            // means two parents are now congruent, so enqueue their merge with a
            // congruence justification.
            for &p in &child_parents {
                let key = self.signature_of(p);
                if let Some(&rep) = self.table.get(&key) {
                    if self.find(rep) != self.find(p) {
                        self.pending.push((rep, p, Edge::Congruence));
                    }
                } else {
                    self.table.insert(key.clone(), p);
                    self.trail.push(Undo::TableInserted { key });
                }
                self.nodes[root.index()].parents.push(p);
                self.trail.push(Undo::ParentPushed { node: root });
            }
        }
    }

    /// Re-roots `x`'s proof tree at `x`, then adds the undirected proof edge
    /// `x — y` with justification `edge`. Because `x` and `y` were in different
    /// union-find classes (the caller checks), they are in different proof trees,
    /// so this never creates a cycle.
    fn add_proof_edge(&mut self, x: ENodeId, y: ENodeId, edge: Edge) {
        // Save the proof state of `x` and every ancestor before rewriting them
        // (re-rooting reverses the whole chain; the link then rewrites `x`). `y` is
        // not mutated — the forest is parent-pointer based.
        let mut saved = Vec::new();
        let mut cur = Some(x);
        while let Some(n) = cur {
            saved.push((
                n,
                self.nodes[n.index()].proof_parent,
                self.nodes[n.index()].proof_edge,
            ));
            cur = self.nodes[n.index()].proof_parent;
        }
        self.trail.push(Undo::ProofRewritten { saved });

        self.reroot_proof_tree(x);
        self.nodes[x.index()].proof_parent = Some(y);
        self.nodes[x.index()].proof_edge = Some(edge);
    }

    /// Makes `x` the root of its proof tree by reversing the parent/edge chain from
    /// `x` up to its current root.
    fn reroot_proof_tree(&mut self, x: ENodeId) {
        let mut current = x;
        let mut parent = self.nodes[x.index()].proof_parent;
        let mut edge = self.nodes[x.index()].proof_edge;
        self.nodes[x.index()].proof_parent = None;
        self.nodes[x.index()].proof_edge = None;
        while let Some(p) = parent {
            let next_parent = self.nodes[p.index()].proof_parent;
            let next_edge = self.nodes[p.index()].proof_edge;
            self.nodes[p.index()].proof_parent = Some(current);
            self.nodes[p.index()].proof_edge = edge;
            current = p;
            parent = next_parent;
            edge = next_edge;
        }
    }

    /// Explains why `a` and `b` are equal: a set of input `reason` ids whose
    /// asserted equalities, with congruence, entail `a = b`. Returns an empty set
    /// when `a == b`.
    ///
    /// # Panics
    ///
    /// Panics if `a` and `b` are not in the same class (there is nothing to
    /// explain — call only when [`Self::equal`] holds).
    #[must_use]
    pub fn explain(&self, a: ENodeId, b: ENodeId) -> Vec<u32> {
        let mut reasons = Vec::new();
        self.explain_into(a, b, &mut reasons);
        reasons.sort_unstable();
        reasons.dedup();
        reasons
    }

    /// Accumulates the input reasons explaining `a = b` into `reasons` (recursive
    /// for congruence edges; may contain duplicates until the caller dedups).
    fn explain_into(&self, a: ENodeId, b: ENodeId, reasons: &mut Vec<u32>) {
        if a == b {
            return;
        }
        // Path from `a` up to its proof-tree root.
        let mut a_path = Vec::new();
        let mut a_seen = std::collections::HashSet::new();
        let mut cur = Some(a);
        while let Some(n) = cur {
            a_path.push(n);
            a_seen.insert(n);
            cur = self.nodes[n.index()].proof_parent;
        }
        // Walk `b` up until it meets `a`'s path: that node is the LCA.
        let mut b_path = Vec::new();
        let mut cur = Some(b);
        let mut lca = None;
        while let Some(n) = cur {
            if a_seen.contains(&n) {
                lca = Some(n);
                break;
            }
            b_path.push(n);
            cur = self.nodes[n.index()].proof_parent;
        }
        let lca = lca.expect("explain called on unequal nodes");

        // Collect the edges from `a` up to the LCA and from `b` up to the LCA.
        for &n in &a_path {
            if n == lca {
                break;
            }
            self.collect_edge(n, reasons);
        }
        for &n in &b_path {
            self.collect_edge(n, reasons);
        }
    }

    /// Adds the input reasons justifying the proof edge from `n` to its parent.
    fn collect_edge(&self, n: ENodeId, reasons: &mut Vec<u32>) {
        match self.nodes[n.index()].proof_edge {
            Some(Edge::Input(r)) => reasons.push(r),
            Some(Edge::Congruence) => {
                let p = self.nodes[n.index()].proof_parent.expect("congruence edge");
                // `n` and `p` are congruent: same `decl`, pairwise-equal arguments.
                // Recover the premises from the argument explanations.
                let n_args = &self.nodes[n.index()].args;
                let p_args = &self.nodes[p.index()].args;
                for (&na, &pa) in n_args.iter().zip(p_args) {
                    self.explain_into(na, pa, reasons);
                }
            }
            None => {}
        }
    }
}

/// Independent congruence checker (T1.4.5): the EUF analogue of `check_drat`.
///
/// Re-validates a claimed equality `a = b` from a set of `premises` (input
/// equalities — e.g. the pairs an [`EGraph::explain`] result names) using a
/// **fresh** union-find and its own congruence-closure fixpoint over the e-graph's
/// immutable term structure (`decl`/`args` only — never the e-graph's own derived
/// union-find or proof forest). Returns `true` iff the premises, closed under
/// reflexivity/symmetry/transitivity/congruence, entail `a = b`.
///
/// This keeps equality reasoning inside the project's "untrusted search, trusted
/// small checking" identity: a bug in the e-graph's incremental machinery cannot
/// make a wrong explanation pass this check, which shares no state with it.
///
/// # Panics
///
/// Panics only if `graph` somehow holds more than `u32::MAX` nodes, which
/// [`EGraph::add`] prevents at creation time (so this does not happen in practice).
#[must_use]
pub fn check_congruence(
    graph: &EGraph,
    premises: &[(ENodeId, ENodeId)],
    a: ENodeId,
    b: ENodeId,
) -> bool {
    let n = graph.len();
    let mut parent: Vec<usize> = (0..n).collect();

    for &(x, y) in premises {
        cc_union(&mut parent, x.index(), y.index());
    }

    // Congruence-closure fixpoint: two nodes with the same `decl` and pairwise-equal
    // arguments are merged, until nothing changes.
    loop {
        let mut changed = false;
        for i in 0..n {
            for j in (i + 1)..n {
                if cc_find(&mut parent, i) == cc_find(&mut parent, j) {
                    continue;
                }
                let id_i = ENodeId(u32::try_from(i).expect("index fits u32"));
                let id_j = ENodeId(u32::try_from(j).expect("index fits u32"));
                let ai = graph.args(id_i);
                let aj = graph.args(id_j);
                if graph.decl(id_i) == graph.decl(id_j)
                    && ai.len() == aj.len()
                    && ai.iter().zip(aj).all(|(&x, &y)| {
                        cc_find(&mut parent, x.index()) == cc_find(&mut parent, y.index())
                    })
                {
                    cc_union(&mut parent, i, j);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    cc_find(&mut parent, a.index()) == cc_find(&mut parent, b.index())
}

/// Path-compressing find for the checker's private union-find.
fn cc_find(parent: &mut [usize], mut i: usize) -> usize {
    while parent[i] != i {
        parent[i] = parent[parent[i]];
        i = parent[i];
    }
    i
}

/// Union for the checker's private union-find.
fn cc_union(parent: &mut [usize], a: usize, b: usize) {
    let ra = cc_find(parent, a);
    let rb = cc_find(parent, b);
    if ra != rb {
        parent[ra] = rb;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn congruence_propagates_through_one_function() {
        // a, b leaves; f(a), f(b). After a = b, f(a) = f(b).
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        let fa = g.add(2, &[a]);
        let fb = g.add(2, &[b]);
        assert!(!g.equal(fa, fb));
        g.merge(a, b, 0);
        assert!(g.equal(a, b));
        assert!(g.equal(fa, fb), "f(a) must equal f(b) after a = b");
    }

    #[test]
    fn hash_consing_returns_the_same_node() {
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let fa1 = g.add(1, &[a]);
        let fa2 = g.add(1, &[a]);
        assert_eq!(fa1, fa2, "structurally identical terms share a node");
        assert_eq!(g.len(), 2);
    }

    #[test]
    fn nested_congruence_cascades() {
        // g(f(a)) vs g(f(b)); a = b must close all the way up.
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        let fa = g.add(2, &[a]);
        let fb = g.add(2, &[b]);
        let gfa = g.add(3, &[fa]);
        let gfb = g.add(3, &[fb]);
        assert!(!g.equal(gfa, gfb));
        g.merge(a, b, 0);
        assert!(g.equal(gfa, gfb), "g(f(a)) = g(f(b)) after a = b");
    }

    #[test]
    fn two_argument_congruence() {
        // h(a, c) and h(b, c); a = b ⇒ h(a,c) = h(b,c). c shared.
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        let c = g.add(2, &[]);
        let hac = g.add(3, &[a, c]);
        let hbc = g.add(3, &[b, c]);
        assert!(!g.equal(hac, hbc));
        g.merge(a, b, 0);
        assert!(g.equal(hac, hbc));
        // But h(a, c) and h(c, a) need not be equal (order matters).
        let hca = g.add(3, &[c, a]);
        assert!(!g.equal(hac, hca));
    }

    #[test]
    fn explains_a_direct_merge() {
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        g.merge(a, b, 7);
        assert_eq!(g.explain(a, b), vec![7]);
        assert!(g.explain(a, a).is_empty(), "a = a needs no reason");
    }

    #[test]
    fn explains_a_congruence_via_its_premise() {
        // f(a) = f(b) holds because a = b (reason 3); the explanation is just {3}.
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        let fa = g.add(2, &[a]);
        let fb = g.add(2, &[b]);
        g.merge(a, b, 3);
        assert_eq!(g.explain(fa, fb), vec![3]);
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn explanation_names_only_the_needed_merges() {
        // a=b (r0), b=c (r1), and an unrelated d=e (r2). explain(a,c) needs r0,r1
        // but not r2.
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        let c = g.add(2, &[]);
        let d = g.add(3, &[]);
        let e = g.add(4, &[]);
        g.merge(a, b, 0);
        g.merge(b, c, 1);
        g.merge(d, e, 2);
        let reasons = g.explain(a, c);
        assert_eq!(reasons, vec![0, 1]);
        assert!(!reasons.contains(&2), "unrelated merge must not appear");
    }

    #[test]
    fn explanation_passes_the_independent_checker() {
        // f(a) = f(b) explained by a=b (reason 5); the independent checker confirms
        // the premise (a,b) entails f(a)=f(b), and rejects the empty premise set.
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        let fa = g.add(2, &[a]);
        let fb = g.add(2, &[b]);
        g.merge(a, b, 5);
        assert_eq!(g.explain(fa, fb), vec![5]);
        assert!(
            check_congruence(&g, &[(a, b)], fa, fb),
            "premise entails it"
        );
        assert!(
            !check_congruence(&g, &[], fa, fb),
            "no premises must not entail f(a)=f(b)"
        );
    }

    #[test]
    fn explains_nested_congruence_chain() {
        // g(f(a)) = g(f(b)) from a = b (reason 9), through two congruence levels.
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        let fa = g.add(2, &[a]);
        let fb = g.add(2, &[b]);
        let gfa = g.add(3, &[fa]);
        let gfb = g.add(3, &[fb]);
        g.merge(a, b, 9);
        assert_eq!(g.explain(gfa, gfb), vec![9]);
    }

    #[test]
    fn push_merge_pop_restores_equality() {
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        g.push();
        g.merge(a, b, 0);
        assert!(g.equal(a, b));
        g.pop();
        assert!(!g.equal(a, b), "pop must undo the merge");
        assert_eq!(g.scope_depth(), 0);
    }

    #[test]
    fn pop_restores_congruence() {
        // f(a), f(b); merge inside a scope makes f(a)=f(b); pop reverts the cascade.
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        let fa = g.add(2, &[a]);
        let fb = g.add(2, &[b]);
        g.push();
        g.merge(a, b, 0);
        assert!(g.equal(fa, fb));
        g.pop();
        assert!(!g.equal(a, b));
        assert!(!g.equal(fa, fb), "congruence consequence must be undone");
        // The e-graph is reusable: a fresh merge still works after pop.
        g.merge(a, b, 1);
        assert!(g.equal(fa, fb));
        assert_eq!(g.explain(fa, fb), vec![1]);
    }

    #[test]
    fn nested_scopes_unwind_in_order() {
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        let c = g.add(2, &[]);
        g.push();
        g.merge(a, b, 0);
        g.push();
        g.merge(b, c, 1);
        assert!(g.equal(a, c));
        g.pop(); // undo b = c
        assert!(g.equal(a, b));
        assert!(!g.equal(a, c));
        g.pop(); // undo a = b
        assert!(!g.equal(a, b));
        assert_eq!(g.scope_depth(), 0);
    }

    #[test]
    fn add_inside_scope_is_undone() {
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let base_len = g.len();
        g.push();
        let b = g.add(1, &[]);
        let _fab = g.add(2, &[a, b]);
        assert!(g.len() > base_len);
        g.pop();
        assert_eq!(g.len(), base_len, "nodes added in the scope are removed");
    }

    #[test]
    fn theory_vars_merge_on_union_and_backtrack() {
        // Attach theory vars to two classes; merging unions their lists, and a
        // theory reading `th_vars` after the merge sees both (an interface
        // equality). pop restores the per-class lists.
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        g.attach_th_var(a, 100);
        g.attach_th_var(b, 200);
        assert_eq!(g.th_vars(a), &[100]);
        assert_eq!(g.th_vars(b), &[200]);

        g.push();
        g.merge(a, b, 0);
        let mut shared = g.th_vars(a).to_vec();
        shared.sort_unstable();
        assert_eq!(
            shared,
            vec![100, 200],
            "merged class holds both theory vars"
        );
        // Both nodes see the same class list.
        assert_eq!(g.th_vars(a), g.th_vars(b));

        g.pop();
        assert!(!g.equal(a, b));
        assert_eq!(g.th_vars(a), &[100], "theory-var lists restored on pop");
        assert_eq!(g.th_vars(b), &[200]);
    }

    #[test]
    fn theory_vars_propagate_through_congruence() {
        // A theory var on f(a)'s class is visible from f(b) once a = b makes them
        // congruent — the equality bus carrying an interface equality.
        let mut g = EGraph::new();
        let a = g.add(0, &[]);
        let b = g.add(1, &[]);
        let fa = g.add(2, &[a]);
        let fb = g.add(2, &[b]);
        g.attach_th_var(fa, 7);
        assert!(g.th_vars(fb).is_empty());
        g.merge(a, b, 0);
        assert_eq!(
            g.th_vars(fb),
            &[7],
            "f(b) joins f(a)'s class and its th_vars"
        );
    }

    /// Deterministic xorshift PRNG (no clock / `Math.random`).
    fn xorshift(state: &mut u64) -> u64 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *state = x;
        x
    }

    fn rand_usize(state: &mut u64) -> usize {
        usize::try_from(xorshift(state)).unwrap_or(usize::MAX)
    }

    fn rand_u32(state: &mut u64) -> u32 {
        u32::try_from(xorshift(state) & 0xFFFF_FFFF).unwrap_or(0)
    }

    /// A brute-force congruence-closure oracle over a fixed term set: union-find
    /// plus a naive fixpoint that merges same-decl terms with pairwise-equal args.
    struct Oracle {
        decls: Vec<u32>,
        args: Vec<Vec<usize>>,
        uf: Vec<usize>,
    }

    impl Oracle {
        fn new(decls: Vec<u32>, args: Vec<Vec<usize>>) -> Self {
            let n = decls.len();
            Self {
                decls,
                args,
                uf: (0..n).collect(),
            }
        }
        fn find(&mut self, mut i: usize) -> usize {
            while self.uf[i] != i {
                self.uf[i] = self.uf[self.uf[i]];
                i = self.uf[i];
            }
            i
        }
        fn union(&mut self, a: usize, b: usize) {
            let (ra, rb) = (self.find(a), self.find(b));
            if ra != rb {
                self.uf[ra] = rb;
            }
        }
        /// Close congruence to a fixpoint.
        fn close(&mut self) {
            loop {
                let mut changed = false;
                let n = self.decls.len();
                for i in 0..n {
                    for j in (i + 1)..n {
                        if self.find(i) == self.find(j) {
                            continue;
                        }
                        let ai = self.args[i].clone();
                        let aj = self.args[j].clone();
                        if self.decls[i] == self.decls[j]
                            && ai.len() == aj.len()
                            && ai
                                .iter()
                                .zip(&aj)
                                .all(|(&x, &y)| self.find(x) == self.find(y))
                        {
                            self.union(i, j);
                            changed = true;
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
        }
    }

    #[test]
    fn random_push_pop_matches_rebuilt_state() {
        // Build a fixed term DAG, then drive a random push/pop/merge sequence. After
        // each step the e-graph's equality relation must match a *fresh* e-graph
        // built from the same terms with only the currently in-scope merges applied.
        let mut state = 0x1357_9BDF_2468_ACE0u64;
        for _ in 0..150 {
            // Recipe: leaves then unary/binary apps referencing earlier terms.
            let n_leaves = 3 + rand_usize(&mut state) % 3;
            let n_apps = 3 + rand_usize(&mut state) % 5;
            let mut recipe: Vec<(u32, Vec<usize>)> = Vec::new();
            for leaf in 0..n_leaves {
                recipe.push((1000 + u32::try_from(leaf).unwrap(), Vec::new()));
            }
            for _ in 0..n_apps {
                let arity = 1 + rand_usize(&mut state) % 2;
                let decl = rand_u32(&mut state) % 3;
                let args = (0..arity)
                    .map(|_| rand_usize(&mut state) % recipe.len())
                    .collect();
                recipe.push((decl, args));
            }
            let build = |merges: &[(usize, usize)]| -> (EGraph, Vec<ENodeId>) {
                let mut g = EGraph::new();
                let mut ids = Vec::new();
                for (decl, args) in &recipe {
                    let arg_ids: Vec<ENodeId> = args.iter().map(|&i| ids[i]).collect();
                    ids.push(g.add(*decl, &arg_ids));
                }
                for (i, &(mi, mj)) in merges.iter().enumerate() {
                    g.merge(ids[mi], ids[mj], u32::try_from(i).unwrap());
                }
                (g, ids)
            };

            let (mut g, ids) = build(&[]);
            // Stack of per-scope merge lists; the flattened concatenation is "active".
            let mut scopes: Vec<Vec<(usize, usize)>> = vec![Vec::new()];

            for _ in 0..20 {
                match rand_usize(&mut state) % 3 {
                    0 => {
                        g.push();
                        scopes.push(Vec::new());
                    }
                    1 if scopes.len() > 1 => {
                        g.pop();
                        scopes.pop();
                    }
                    _ => {
                        let i = rand_usize(&mut state) % ids.len();
                        let j = rand_usize(&mut state) % ids.len();
                        let active: usize = scopes.iter().map(Vec::len).sum();
                        g.merge(ids[i], ids[j], u32::try_from(active).unwrap());
                        scopes.last_mut().unwrap().push((i, j));
                    }
                }

                // Compare against a fresh build from the active merges.
                let active: Vec<(usize, usize)> = scopes.iter().flatten().copied().collect();
                let (reference, ref_ids) = build(&active);
                for a in 0..ids.len() {
                    for b in 0..ids.len() {
                        assert_eq!(
                            g.equal(ids[a], ids[b]),
                            reference.equal(ref_ids[a], ref_ids[b]),
                            "backtracked state disagrees with rebuild on ({a}, {b})"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn random_merges_agree_with_brute_force() {
        let mut state = 0xC0FF_EE12_3456_789Au64;
        for _ in 0..300 {
            // Build a random DAG of terms: a handful of leaves, then applications
            // referencing earlier terms. decls drawn from a tiny alphabet so
            // congruences actually arise.
            let n_leaves = 2 + rand_usize(&mut state) % 4;
            let n_apps = 3 + rand_usize(&mut state) % 8;

            let mut g = EGraph::new();
            let mut decls: Vec<u32> = Vec::new();
            let mut args: Vec<Vec<usize>> = Vec::new();
            let mut ids: Vec<ENodeId> = Vec::new();

            for leaf in 0..n_leaves {
                // Each leaf gets a unique decl (distinct symbols).
                let decl = 1000 + u32::try_from(leaf).unwrap();
                ids.push(g.add(decl, &[]));
                decls.push(decl);
                args.push(Vec::new());
            }
            for _ in 0..n_apps {
                let arity = 1 + rand_usize(&mut state) % 2; // 1 or 2
                let decl = rand_u32(&mut state) % 3; // shared function symbols
                let mut arg_indices = Vec::new();
                let mut arg_ids = Vec::new();
                for _ in 0..arity {
                    let pick = rand_usize(&mut state) % ids.len();
                    arg_indices.push(pick);
                    arg_ids.push(ids[pick]);
                }
                // Hash-consing may return an existing node; mirror its term index.
                let id = g.add(decl, &arg_ids);
                if let Some(existing) = ids.iter().position(|&e| e == id) {
                    // Already known term; reuse its oracle index.
                    ids.push(ids[existing]);
                    decls.push(decls[existing]);
                    args.push(args[existing].clone());
                } else {
                    ids.push(id);
                    decls.push(decl);
                    args.push(arg_indices);
                }
            }

            // Oracle term set is indexed the same as `ids`/`decls`/`args`.
            let mut oracle = Oracle::new(decls.clone(), args.clone());

            // Apply a few random merges to both, tagging each with a unique reason
            // id so explanations can be checked. `input_merges[reason]` records the
            // asserted term-index pair.
            let n_merges = 1 + rand_usize(&mut state) % 4;
            let mut input_merges: Vec<(usize, usize)> = Vec::new();
            for _ in 0..n_merges {
                let i = rand_usize(&mut state) % ids.len();
                let j = rand_usize(&mut state) % ids.len();
                let reason = u32::try_from(input_merges.len()).unwrap();
                g.merge(ids[i], ids[j], reason);
                oracle.union(i, j);
                input_merges.push((i, j));
            }
            oracle.close();

            for i in 0..ids.len() {
                for j in 0..ids.len() {
                    let equal = g.equal(ids[i], ids[j]);
                    assert_eq!(
                        equal,
                        oracle.find(i) == oracle.find(j),
                        "disagreement on terms {i} and {j}"
                    );
                    if equal && i != j {
                        // Explanation soundness: applying ONLY the input merges the
                        // explanation names must make i and j equal (with congruence).
                        let reasons = g.explain(ids[i], ids[j]);
                        let mut check = Oracle::new(decls.clone(), args.clone());
                        for &r in &reasons {
                            let (mi, mj) = input_merges[r as usize];
                            check.union(mi, mj);
                        }
                        check.close();
                        assert_eq!(
                            check.find(i),
                            check.find(j),
                            "explanation {reasons:?} does not entail {i} = {j}"
                        );
                        // The same explanation must also pass the in-tree
                        // independent congruence checker (T1.4.5).
                        let premises: Vec<(ENodeId, ENodeId)> = reasons
                            .iter()
                            .map(|&r| {
                                let (mi, mj) = input_merges[r as usize];
                                (ids[mi], ids[mj])
                            })
                            .collect();
                        assert!(
                            check_congruence(&g, &premises, ids[i], ids[j]),
                            "independent checker rejected a sound explanation"
                        );
                    }
                }
            }
        }
    }
}
