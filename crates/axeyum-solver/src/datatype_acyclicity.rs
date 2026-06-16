//! Datatype **acyclicity** (occurs-check) refutation (Track 2, P2.9).
//!
//! Inductive (algebraic) datatype values are *well-founded*: `cons(1, cons(2,
//! nil))` is finite, and no value can strictly contain itself. So a conjunction
//! that forces a datatype value to be a proper subterm of itself — e.g.
//! `x = cons(h, x)`, or the chain `x = cons(h, y) ∧ y = cons(g, x)` — is
//! **unsatisfiable**, a fact the eager tag/field expansion
//! ([`crate::check_with_datatype_native`]) does not catch on its own.
//!
//! [`prove_datatype_unsat_by_acyclicity`] decides this from the top-level
//! (definite) equalities: it unions datatype-variable aliases (`x = y`) and adds
//! a **strict-containment** edge `x ⊐ y` whenever `x = c(… y …)` (the value of `x`
//! is a constructor application whose fields contain the value of `y`, so `x`
//! strictly contains `y`). A directed cycle in that graph forces some value to
//! strictly contain itself, which is impossible — hence `unsat`.
//!
//! **Sound, incomplete.** Every edge is a real strict-containment forced by a
//! definite equality, so a cycle is a genuine contradiction (regardless of the
//! datatype's other axioms): proving `unsat` this way is sound. It is silent
//! (returns `false`) when there is no cycle — satisfiability is left to the
//! native datatype path.

use std::collections::HashMap;

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};

/// Tries to prove `assertions` `unsat` by datatype acyclicity. Returns `true`
/// only when a strict-containment cycle is found (a sound refutation); `false`
/// otherwise (no claim about satisfiability).
#[must_use]
pub fn prove_datatype_unsat_by_acyclicity(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut graph = ContainmentGraph::default();

    for &assertion in assertions {
        // Only definite top-level equalities `(= a b)` over a datatype sort
        // contribute a forced containment/alias.
        let TermNode::App { op: Op::Eq, args } = arena.node(assertion) else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let (a, b) = (args[0], args[1]);
        if !is_datatype(arena, a) {
            continue;
        }
        match (as_variable(arena, a), as_variable(arena, b)) {
            // `x = y`: the two datatype variables are the same value — union them.
            (Some(x), Some(y)) => graph.union(x, y),
            // `x = c(args)`: `x` strictly contains every datatype variable under
            // the constructor term.
            (Some(x), None) => graph.add_construction(arena, x, b),
            (None, Some(y)) => graph.add_construction(arena, y, a),
            // `c(..) = c'(..)`: no variable to anchor a containment edge here
            // (injectivity/distinctness is a different refutation); skip.
            (None, None) => {}
        }
    }

    graph.has_cycle()
}

/// Whether `term` is datatype-sorted.
fn is_datatype(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.sort_of(term), Sort::Datatype(_))
}

/// The symbol of `term` if it is a plain variable, else `None`.
fn as_variable(arena: &TermArena, term: TermId) -> Option<SymbolId> {
    match arena.node(term) {
        TermNode::Symbol(symbol) => Some(*symbol),
        _ => None,
    }
}

/// A union-find over datatype variables plus strict-containment edges between
/// their representatives; `has_cycle` reports whether a value is forced to
/// contain itself.
#[derive(Default)]
struct ContainmentGraph {
    /// Dense index per datatype variable (interned on first use).
    index: HashMap<SymbolId, usize>,
    /// Union-find parent pointers (by dense index).
    parent: Vec<usize>,
    /// Strict-containment edges `from ⊐ to`, as `(from_index, to_index)` over the
    /// *raw* indices (resolved to representatives in `has_cycle`).
    edges: Vec<(usize, usize)>,
}

impl ContainmentGraph {
    /// The dense index of `symbol`, interning it (as its own union-find root) on
    /// first use.
    fn intern(&mut self, symbol: SymbolId) -> usize {
        if let Some(&i) = self.index.get(&symbol) {
            return i;
        }
        let i = self.parent.len();
        self.parent.push(i);
        self.index.insert(symbol, i);
        i
    }

    /// Union-find find with path halving.
    fn find(&mut self, mut i: usize) -> usize {
        while self.parent[i] != i {
            self.parent[i] = self.parent[self.parent[i]];
            i = self.parent[i];
        }
        i
    }

    /// Unions the classes of two datatype variables (`x = y`).
    fn union(&mut self, x: SymbolId, y: SymbolId) {
        let xi = self.intern(x);
        let yi = self.intern(y);
        let (rx, ry) = (self.find(xi), self.find(yi));
        if rx != ry {
            self.parent[rx] = ry;
        }
    }

    /// Records `container = constructor_term`: adds `container ⊐ y` for every
    /// datatype variable `y` occurring under the constructor term.
    fn add_construction(&mut self, arena: &TermArena, container: SymbolId, term: TermId) {
        let ci = self.intern(container);
        let mut inner = Vec::new();
        collect_datatype_vars(arena, term, &mut inner);
        for y in inner {
            let yi = self.intern(y);
            self.edges.push((ci, yi));
        }
    }

    /// Whether the strict-containment graph (over union-find representatives) has
    /// a directed cycle — i.e. some value must strictly contain itself.
    fn has_cycle(&mut self) -> bool {
        let n = self.parent.len();
        // Adjacency over representatives.
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
        let edges = self.edges.clone();
        for (from, to) in edges {
            let (rf, rt) = (self.find(from), self.find(to));
            // A self-edge after unioning is already a self-containment cycle.
            adj[rf].push(rt);
        }
        // Iterative DFS with three colors (0 = white, 1 = grey/on-stack, 2 = black).
        let mut color = vec![0u8; n];
        for start in 0..n {
            if color[start] != 0 {
                continue;
            }
            // Stack of (node, whether we are entering or finishing it).
            let mut stack: Vec<(usize, bool)> = vec![(start, false)];
            while let Some((node, finishing)) = stack.pop() {
                if finishing {
                    color[node] = 2;
                    continue;
                }
                if color[node] != 0 {
                    // Already grey (on the current path) or black (finished): a
                    // duplicate entry from a second parent — do not reprocess.
                    continue;
                }
                color[node] = 1;
                stack.push((node, true));
                for &next in &adj[node] {
                    match color[next] {
                        1 => return true, // back-edge to a grey node ⇒ cycle
                        0 => stack.push((next, false)),
                        _ => {}
                    }
                }
            }
        }
        false
    }
}

/// Collects the symbols of every datatype-sorted **variable** occurring in
/// `term` (descending through constructor applications and any other operators).
fn collect_datatype_vars(arena: &TermArena, term: TermId, out: &mut Vec<SymbolId>) {
    match arena.node(term) {
        TermNode::Symbol(symbol) if is_datatype(arena, term) => out.push(*symbol),
        TermNode::App { args, .. } => {
            let args = args.clone();
            for arg in args {
                collect_datatype_vars(arena, arg, out);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
#[allow(clippy::many_single_char_names)]
mod tests {
    use super::prove_datatype_unsat_by_acyclicity;
    use axeyum_ir::{Sort, TermArena};

    /// `IntList = nil | cons(head: BitVec(8), tail: IntList)`.
    fn int_list(arena: &mut TermArena) -> (axeyum_ir::DatatypeId, [axeyum_ir::ConstructorId; 2]) {
        let dt = arena.declare_datatype("IntList");
        let nil = arena.add_constructor(dt, "nil", &[]);
        let cons = arena.add_constructor(
            dt,
            "cons",
            &[
                ("head".to_owned(), Sort::BitVec(8)),
                ("tail".to_owned(), Sort::Datatype(dt)),
            ],
        );
        (dt, [nil, cons])
    }

    #[test]
    fn direct_self_cycle_is_unsat() {
        // x = cons(h, x): x strictly contains itself ⇒ UNSAT.
        let mut arena = TermArena::new();
        let (dt, [_nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let xv = arena.var(x);
        let h = arena.bv_var("h", 8).unwrap();
        let consed = arena.construct(cons, &[h, xv]).unwrap();
        let eq = arena.eq(xv, consed).unwrap();
        assert!(prove_datatype_unsat_by_acyclicity(&arena, &[eq]));
    }

    #[test]
    fn two_step_cycle_through_alias_is_unsat() {
        // x = cons(h, y) ∧ y = cons(g, x): x ⊐ y ⊐ x ⇒ UNSAT.
        let mut arena = TermArena::new();
        let (dt, [_nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let y = arena.declare("y", Sort::Datatype(dt)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let h = arena.bv_var("h", 8).unwrap();
        let g = arena.bv_var("g", 8).unwrap();
        let cx = arena.construct(cons, &[h, yv]).unwrap();
        let cy = arena.construct(cons, &[g, xv]).unwrap();
        let e1 = arena.eq(xv, cx).unwrap();
        let e2 = arena.eq(yv, cy).unwrap();
        assert!(prove_datatype_unsat_by_acyclicity(&arena, &[e1, e2]));
    }

    #[test]
    fn cycle_via_variable_equality_is_unsat() {
        // x = cons(h, y) ∧ y = x: union(x,y) closes the self-cycle ⇒ UNSAT.
        let mut arena = TermArena::new();
        let (dt, [_nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let y = arena.declare("y", Sort::Datatype(dt)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let h = arena.bv_var("h", 8).unwrap();
        let cx = arena.construct(cons, &[h, yv]).unwrap();
        let e1 = arena.eq(xv, cx).unwrap();
        let e2 = arena.eq(yv, xv).unwrap();
        assert!(prove_datatype_unsat_by_acyclicity(&arena, &[e1, e2]));
    }

    #[test]
    fn diamond_sharing_is_not_a_cycle() {
        // x = cons(h, z) ∧ y = cons(g, z): z has two parents but there is no
        // cycle — the acyclicity check must NOT refute (no false UNSAT from the
        // shared-child DFS path).
        let mut arena = TermArena::new();
        let (dt, [_nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let y = arena.declare("y", Sort::Datatype(dt)).unwrap();
        let z = arena.declare("z", Sort::Datatype(dt)).unwrap();
        let (xv, yv, zv) = (arena.var(x), arena.var(y), arena.var(z));
        let h = arena.bv_var("h", 8).unwrap();
        let g = arena.bv_var("g", 8).unwrap();
        let cx = arena.construct(cons, &[h, zv]).unwrap();
        let cy = arena.construct(cons, &[g, zv]).unwrap();
        let e1 = arena.eq(xv, cx).unwrap();
        let e2 = arena.eq(yv, cy).unwrap();
        assert!(!prove_datatype_unsat_by_acyclicity(&arena, &[e1, e2]));
    }

    #[test]
    fn finite_list_is_not_refuted() {
        // x = cons(h, y) ∧ y = nil: a genuine finite list ⇒ no cycle (not UNSAT here).
        let mut arena = TermArena::new();
        let (dt, [nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let y = arena.declare("y", Sort::Datatype(dt)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let h = arena.bv_var("h", 8).unwrap();
        let cx = arena.construct(cons, &[h, yv]).unwrap();
        let niled = arena.construct(nil, &[]).unwrap();
        let e1 = arena.eq(xv, cx).unwrap();
        let e2 = arena.eq(yv, niled).unwrap();
        assert!(!prove_datatype_unsat_by_acyclicity(&arena, &[e1, e2]));
    }
}
