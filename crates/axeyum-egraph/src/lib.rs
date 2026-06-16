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

/// One e-node: a `decl` applied to `args`, with its union-find root, class size,
/// and the parent nodes that reference its class.
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
}

/// An incremental congruence-closure e-graph.
#[derive(Debug, Default)]
pub struct EGraph {
    nodes: Vec<ENode>,
    /// Signature table: a canonical signature maps to the node that owns it.
    table: HashMap<Signature, ENodeId>,
    /// Pending equalities to process (deferred-merge worklist).
    pending: Vec<(ENodeId, ENodeId)>,
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

    /// Asserts `a = b` and closes congruence over the consequences.
    pub fn merge(&mut self, a: ENodeId, b: ENodeId) {
        self.pending.push((a, b));
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
        while let Some((a, b)) = self.pending.pop() {
            let ra = self.find(a);
            let rb = self.find(b);
            if ra == rb {
                continue;
            }
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
            // means two parents are now congruent, so enqueue their merge.
            for &p in &child_parents {
                let key = self.signature_of(p);
                match self.table.get(&key) {
                    Some(&rep) => {
                        if self.find(rep) != self.find(p) {
                            self.pending.push((rep, p));
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
        g.merge(a, b);
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
        g.merge(a, b);
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
        g.merge(a, b);
        assert!(g.equal(hac, hbc));
        // But h(a, c) and h(c, a) need not be equal (order matters).
        let hca = g.add(3, &[c, a]);
        assert!(!g.equal(hac, hca));
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

            // Apply a few random merges to both, then compare all pairs.
            let n_merges = 1 + rand_usize(&mut state) % 4;
            for _ in 0..n_merges {
                let i = rand_usize(&mut state) % ids.len();
                let j = rand_usize(&mut state) % ids.len();
                g.merge(ids[i], ids[j]);
                oracle.union(i, j);
            }
            oracle.close();

            for i in 0..ids.len() {
                for j in 0..ids.len() {
                    assert_eq!(
                        g.equal(ids[i], ids[j]),
                        oracle.find(i) == oracle.find(j),
                        "disagreement on terms {i} and {j}"
                    );
                }
            }
        }
    }
}
