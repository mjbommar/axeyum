//! Incremental congruence-closure e-graph (Track 1, P1.4 — keystone).
//!
//! This is the shared **equality bus** for the reasoning stack: a backtrackable
//! union-find over e-nodes plus a signature (hash-cons) table that closes
//! congruence incrementally. Almost every eager→lazy theory upgrade in Track 2
//! (EUF, lazy arrays, datatypes, arithmetic equality propagation, and all
//! quantifier work) is built on it, so it is the keystone the reference review
//! flagged as "do first".
//!
//! This first slice (tasks T1.4.1 + T1.4.2) is the structural core: e-node
//! creation with hash-consing, a union-find `find` with path compression, and the
//! deferred-merge cascade that re-canonicalizes parents so transitive congruence
//! closes. Explanations (proof forest), the backtrackable trail, the independent
//! congruence checker, and theory-variable lists are the follow-up tasks
//! (T1.4.3–T1.4.6).
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
}

/// An incremental congruence-closure e-graph.
#[derive(Debug, Default)]
pub struct EGraph {
    nodes: Vec<ENode>,
    /// Signature table: a canonical signature maps to the node that owns it.
    table: HashMap<Signature, ENodeId>,
    /// Pending equalities to process (deferred-merge worklist), each carrying the
    /// justification for the proof forest.
    pending: Vec<(ENodeId, ENodeId, Edge)>,
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
        });
        for &arg in args {
            let root = self.find(arg);
            self.nodes[root.index()].parents.push(id);
        }
        self.table.insert(sig, id);
        id
    }

    /// The current class representative of `id` (path-compressing union-find).
    pub fn find(&mut self, id: ENodeId) -> ENodeId {
        let parent = self.nodes[id.index()].root;
        if parent == id {
            return id;
        }
        let root = self.find(parent);
        // Path compression.
        self.nodes[id.index()].root = root;
        root
    }

    /// The class representative without mutating (no path compression).
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
            for &p in &child_parents {
                let key = self.signature_of(p);
                if self.table.get(&key) == Some(&p) {
                    self.table.remove(&key);
                }
            }

            // Union.
            self.nodes[child.index()].root = root;
            let child_size = self.nodes[child.index()].size;
            self.nodes[root.index()].size += child_size;

            // Re-insert the parents under their *post-union* signatures; a collision
            // means two parents are now congruent, so enqueue their merge with a
            // congruence justification.
            for &p in &child_parents {
                let key = self.signature_of(p);
                match self.table.get(&key) {
                    Some(&rep) => {
                        if self.find(rep) != self.find(p) {
                            self.pending.push((rep, p, Edge::Congruence));
                        }
                    }
                    None => {
                        self.table.insert(key, p);
                    }
                }
                self.nodes[root.index()].parents.push(p);
            }
        }
    }

    /// Re-roots `x`'s proof tree at `x`, then adds the undirected proof edge
    /// `x — y` with justification `edge`. Because `x` and `y` were in different
    /// union-find classes (the caller checks), they are in different proof trees,
    /// so this never creates a cycle.
    fn add_proof_edge(&mut self, x: ENodeId, y: ENodeId, edge: Edge) {
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
                    }
                }
            }
        }
    }
}
