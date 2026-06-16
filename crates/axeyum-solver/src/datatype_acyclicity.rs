//! Structural datatype refutation (Track 2, P2.9): acyclicity (occurs-check),
//! constructor distinctness, and constructor injectivity, over the top-level
//! (dis)equalities.
//!
//! Algebraic datatypes obey three structural axioms that make many conjunctions
//! unsatisfiable on shape alone, independent of the field theories:
//!
//! - **Acyclicity.** Inductive values are well-founded: no value strictly
//!   contains itself, so `x = cons(h, x)` (or any containment cycle) is `unsat`.
//! - **Distinctness.** Distinct constructors build distinct values:
//!   `x = nil ∧ x = cons(h, t)` is `unsat`.
//! - **Injectivity.** A constructor is injective: `cons(a, b) = cons(c, d)` forces
//!   `a = c ∧ b = d`, so `cons(h, x) = cons(h, y) ∧ x ≠ y` is `unsat` — a fact the
//!   eager tag/field expansion misses, since it relaxes (skips) *datatype-typed*
//!   fields when comparing.
//!
//! [`prove_datatype_unsat_structurally`] decides these by a small term-level
//! union-find: it unions the sides of every definite equality, closes under
//! injectivity (same-class same-constructor ⇒ union corresponding arguments) while
//! checking distinctness (same-class different-constructor ⇒ `unsat`), then reports
//! `unsat` if any asserted disequality has its two sides in one class, or the
//! strict-containment graph (`t ⊐ field` for every `t = c(… field …)`) has a cycle.
//!
//! **Sound, incomplete.** Every union/edge is forced by a definite (dis)equality
//! and a datatype axiom, so a reported conflict is genuine; the check is silent
//! (`false`) otherwise — satisfiability and the field theories are left to the
//! native datatype path.

use std::collections::HashMap;

use axeyum_ir::{ConstructorId, Op, Sort, TermArena, TermId, TermNode};

/// Tries to prove `assertions` `unsat` by the datatype structural axioms
/// (acyclicity, distinctness, injectivity). Returns `true` only on a genuine
/// structural conflict (a sound refutation); `false` otherwise (no claim about
/// satisfiability).
#[must_use]
pub fn prove_datatype_unsat_structurally(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut s = Structural::default();
    let mut diseqs: Vec<(TermId, TermId)> = Vec::new();

    for &assertion in assertions {
        match arena.node(assertion) {
            // Definite equality `(= a b)` over a datatype sort: union the sides.
            TermNode::App { op: Op::Eq, args }
                if args.len() == 2 && is_datatype(arena, args[0]) =>
            {
                let (a, b) = (args[0], args[1]);
                s.union(arena, a, b);
            }
            // Disequality `(not (= a b))` over a datatype sort: record it.
            TermNode::App {
                op: Op::BoolNot,
                args,
            } if args.len() == 1 => {
                if let TermNode::App {
                    op: Op::Eq,
                    args: eq_args,
                } = arena.node(args[0])
                {
                    if eq_args.len() == 2 && is_datatype(arena, eq_args[0]) {
                        let (p, q) = (eq_args[0], eq_args[1]);
                        s.intern(arena, p);
                        s.intern(arena, q);
                        diseqs.push((p, q));
                    }
                }
            }
            _ => {}
        }
    }

    // Close under injectivity while checking distinctness.
    if s.close(arena) {
        return true; // distinctness conflict: one class, two constructors
    }
    // A disequality whose sides are forced into one class is contradictory.
    for &(p, q) in &diseqs {
        if s.same_class(p, q) {
            return true;
        }
    }
    // Acyclicity: a value forced to strictly contain itself.
    s.has_containment_cycle(arena)
}

/// Whether `term` is datatype-sorted.
fn is_datatype(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.sort_of(term), Sort::Datatype(_))
}

/// The constructor and field arguments of `term` if it is a constructor
/// application, else `None`.
fn as_construction(arena: &TermArena, term: TermId) -> Option<(ConstructorId, Vec<TermId>)> {
    match arena.node(term) {
        TermNode::App {
            op: Op::DtConstruct { constructor, .. },
            args,
        } => Some((*constructor, args.to_vec())),
        _ => None,
    }
}

/// A term-level union-find with the datatype constructor terms tracked, for
/// closing under injectivity and reporting distinctness / containment cycles.
#[derive(Default)]
struct Structural {
    /// Dense index per interned term.
    index: HashMap<TermId, usize>,
    /// Union-find parent pointers (by dense index).
    parent: Vec<usize>,
    /// The term each dense index interns (for inspecting its constructor / args).
    term_of: Vec<TermId>,
    /// Dense indices that intern a **constructor application**.
    ctor_nodes: Vec<usize>,
}

impl Structural {
    /// Interns `term` and all its subterms, returning `term`'s dense index. A
    /// constructor application is recorded in `ctor_nodes`.
    fn intern(&mut self, arena: &TermArena, term: TermId) -> usize {
        if let Some(&i) = self.index.get(&term) {
            return i;
        }
        let i = self.parent.len();
        self.parent.push(i);
        self.term_of.push(term);
        self.index.insert(term, i);
        if as_construction(arena, term).is_some() {
            self.ctor_nodes.push(i);
        }
        // Intern subterms so injectivity unions and containment edges can reach
        // every constructor application in the query.
        if let TermNode::App { args, .. } = arena.node(term) {
            let args = args.clone();
            for arg in args {
                self.intern(arena, arg);
            }
        }
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

    /// Unions the classes of two terms; returns `true` if they were distinct.
    fn union(&mut self, arena: &TermArena, a: TermId, b: TermId) -> bool {
        let ia = self.intern(arena, a);
        let ib = self.intern(arena, b);
        let (ra, rb) = (self.find(ia), self.find(ib));
        if ra == rb {
            return false;
        }
        self.parent[ra] = rb;
        true
    }

    /// Whether two interned terms are in the same class.
    fn same_class(&mut self, a: TermId, b: TermId) -> bool {
        let (Some(&ia), Some(&ib)) = (self.index.get(&a), self.index.get(&b)) else {
            return false;
        };
        self.find(ia) == self.find(ib)
    }

    /// Closes the partition under **injectivity** (same class + same constructor ⇒
    /// union corresponding arguments) to a fixpoint, checking **distinctness** along
    /// the way. Returns `true` on a distinctness conflict (one class, two distinct
    /// constructors).
    fn close(&mut self, arena: &TermArena) -> bool {
        loop {
            let mut changed = false;
            let ctors = self.ctor_nodes.clone();
            for a in 0..ctors.len() {
                for b in (a + 1)..ctors.len() {
                    let (na, nb) = (ctors[a], ctors[b]);
                    if self.find(na) != self.find(nb) {
                        continue;
                    }
                    let (ca, args_a) = as_construction(arena, self.term_of[na])
                        .expect("ctor_nodes holds constructor terms");
                    let (cb, args_b) = as_construction(arena, self.term_of[nb])
                        .expect("ctor_nodes holds constructor terms");
                    if ca != cb {
                        return true; // distinctness: same value, two constructors
                    }
                    // Injectivity: equal constructor applications have equal fields.
                    for (&x, &y) in args_a.iter().zip(&args_b) {
                        if self.union(arena, x, y) {
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                return false;
            }
        }
    }

    /// Whether the strict-containment graph has a cycle. Edge `find(t) → find(arg)`
    /// for every constructor term `t = c(args)` and datatype-sorted `arg` (the value
    /// of `t` strictly contains the value of each datatype field).
    fn has_containment_cycle(&mut self, arena: &TermArena) -> bool {
        let n = self.parent.len();
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
        let ctors = self.ctor_nodes.clone();
        for node in ctors {
            let (_c, args) = as_construction(arena, self.term_of[node])
                .expect("ctor_nodes holds constructor terms");
            let from = self.find(node);
            for arg in args {
                if !is_datatype(arena, arg) {
                    continue;
                }
                let ai = self.intern(arena, arg);
                let to = self.find(ai);
                adj[from].push(to);
            }
        }
        // Iterative three-colour DFS (0 = white, 1 = grey/on-path, 2 = black).
        let mut color = vec![0u8; n];
        for start in 0..n {
            if color[start] != 0 {
                continue;
            }
            let mut stack: Vec<(usize, bool)> = vec![(start, false)];
            while let Some((node, finishing)) = stack.pop() {
                if finishing {
                    color[node] = 2;
                    continue;
                }
                if color[node] != 0 {
                    continue; // grey (on path) or black (done): skip re-entry
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

#[cfg(test)]
#[allow(clippy::many_single_char_names)]
mod tests {
    use super::prove_datatype_unsat_structurally;
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
        assert!(prove_datatype_unsat_structurally(&arena, &[eq]));
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
        assert!(prove_datatype_unsat_structurally(&arena, &[e1, e2]));
    }

    #[test]
    fn cycle_via_variable_equality_is_unsat() {
        // x = cons(h, y) ∧ y = x ⇒ UNSAT.
        let mut arena = TermArena::new();
        let (dt, [_nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let y = arena.declare("y", Sort::Datatype(dt)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let h = arena.bv_var("h", 8).unwrap();
        let cx = arena.construct(cons, &[h, yv]).unwrap();
        let e1 = arena.eq(xv, cx).unwrap();
        let e2 = arena.eq(yv, xv).unwrap();
        assert!(prove_datatype_unsat_structurally(&arena, &[e1, e2]));
    }

    #[test]
    fn distinct_constructors_on_one_value_is_unsat() {
        // x = nil ∧ x = cons(h, t) ⇒ UNSAT (distinctness).
        let mut arena = TermArena::new();
        let (dt, [nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let t = arena.declare("t", Sort::Datatype(dt)).unwrap();
        let (xv, tv) = (arena.var(x), arena.var(t));
        let h = arena.bv_var("h", 8).unwrap();
        let niled = arena.construct(nil, &[]).unwrap();
        let consed = arena.construct(cons, &[h, tv]).unwrap();
        let e1 = arena.eq(xv, niled).unwrap();
        let e2 = arena.eq(xv, consed).unwrap();
        assert!(prove_datatype_unsat_structurally(&arena, &[e1, e2]));
    }

    #[test]
    fn injectivity_over_datatype_field_is_unsat() {
        // cons(h, x) = cons(h, y) ∧ x ≠ y ⇒ UNSAT (injectivity on the tail field —
        // exactly the case the eager expansion relaxes away).
        let mut arena = TermArena::new();
        let (dt, [_nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let y = arena.declare("y", Sort::Datatype(dt)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let h = arena.bv_var("h", 8).unwrap();
        let cx = arena.construct(cons, &[h, xv]).unwrap();
        let cy = arena.construct(cons, &[h, yv]).unwrap();
        let eq = arena.eq(cx, cy).unwrap();
        let xy = arena.eq(xv, yv).unwrap();
        let ne = arena.not(xy).unwrap();
        assert!(prove_datatype_unsat_structurally(&arena, &[eq, ne]));
    }

    #[test]
    fn diamond_sharing_is_not_a_cycle() {
        // x = cons(h, z) ∧ y = cons(g, z): no cycle ⇒ NOT refuted.
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
        assert!(!prove_datatype_unsat_structurally(&arena, &[e1, e2]));
    }

    #[test]
    fn finite_list_with_distinct_tails_is_not_refuted() {
        // cons(h, x) = cons(h, y) with no x ≠ y: consistent (x = y) ⇒ NOT refuted.
        let mut arena = TermArena::new();
        let (dt, [_nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let y = arena.declare("y", Sort::Datatype(dt)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let h = arena.bv_var("h", 8).unwrap();
        let cx = arena.construct(cons, &[h, xv]).unwrap();
        let cy = arena.construct(cons, &[h, yv]).unwrap();
        let eq = arena.eq(cx, cy).unwrap();
        assert!(!prove_datatype_unsat_structurally(&arena, &[eq]));
    }
}
