//! Structural datatype refutation (Track 2, P2.9): acyclicity (occurs-check),
//! constructor distinctness, constructor injectivity, and constructor
//! exhaustiveness, over the top-level Boolean structure and (dis)equalities.
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
//! - **Exhaustiveness.** Every datatype value was built by exactly one
//!   constructor, so excluding every constructor for one value is `unsat`.
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

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{ConstructorId, Op, Sort, TermArena, TermId, TermNode};

/// A self-checking datatype structural refutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DatatypeStructuralRefutationCertificate {
    /// Number of branch conjunctions independently refuted. Direct top-level
    /// structural conflicts use `1`; top-level `or` refutations use one case per
    /// disjunct.
    pub branches: u64,
}

/// Tries to prove `assertions` `unsat` by the datatype structural axioms
/// (acyclicity, distinctness, injectivity). Returns `true` only on a genuine
/// structural conflict (a sound refutation); `false` otherwise (no claim about
/// satisfiability).
#[must_use]
pub fn prove_datatype_unsat_structurally(arena: &TermArena, assertions: &[TermId]) -> bool {
    datatype_structural_refutation(arena, assertions).is_some()
}

/// Returns a certificate when datatype structural axioms refute the conjunction.
///
/// Besides direct top-level structural conflicts, this handles the common cvc5
/// acyclicity shape `or(branch_1, ..., branch_n)`: if every disjunct branch,
/// conjoined with the remaining top-level assertions, is structurally refutable,
/// then the original assertion is also unsatisfiable.
#[must_use]
pub fn datatype_structural_refutation(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<DatatypeStructuralRefutationCertificate> {
    let mut flattened = Vec::new();
    for &assertion in assertions {
        collect_and_leaves(arena, assertion, &mut flattened);
    }

    if conjunction_structural_conflict(arena, &flattened) {
        return Some(DatatypeStructuralRefutationCertificate { branches: 1 });
    }

    for (idx, &assertion) in flattened.iter().enumerate() {
        let mut disjuncts = Vec::new();
        collect_or_leaves(arena, assertion, &mut disjuncts);
        if disjuncts.len() < 2 {
            continue;
        }
        let mut proved = 0_u64;
        let mut all_refuted = true;
        for disjunct in disjuncts {
            let mut branch = Vec::new();
            branch.extend(
                flattened
                    .iter()
                    .enumerate()
                    .filter_map(|(other_idx, &other)| (other_idx != idx).then_some(other)),
            );
            collect_and_leaves(arena, disjunct, &mut branch);
            if conjunction_structural_conflict(arena, &branch) {
                proved += 1;
            } else {
                all_refuted = false;
                break;
            }
        }
        if all_refuted && proved > 0 {
            return Some(DatatypeStructuralRefutationCertificate { branches: proved });
        }
    }

    None
}

fn collect_or_leaves(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolOr,
            args,
        } if args.len() == 2 => {
            collect_or_leaves(arena, args[0], out);
            collect_or_leaves(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

fn collect_and_leaves(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolAnd,
            args,
        } if args.len() == 2 => {
            collect_and_leaves(arena, args[0], out);
            collect_and_leaves(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

fn conjunction_structural_conflict(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut s = Structural::default();
    let mut diseqs: Vec<(TermId, TermId)> = Vec::new();
    let mut excluded_ctors: BTreeMap<TermId, BTreeSet<ConstructorId>> = BTreeMap::new();
    let mut positive_testers: Vec<(TermId, ConstructorId)> = Vec::new();

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
                        record_nullary_constructor_exclusion(arena, p, q, &mut excluded_ctors);
                        record_nullary_constructor_exclusion(arena, q, p, &mut excluded_ctors);
                    }
                } else if let TermNode::App {
                    op: Op::DtTest(ctor),
                    args: test_args,
                } = arena.node(args[0])
                    && test_args.len() == 1
                {
                    let value = test_args[0];
                    s.intern(arena, value);
                    excluded_ctors.entry(value).or_default().insert(*ctor);
                }
            }
            TermNode::App {
                op: Op::DtTest(ctor),
                args,
            } if args.len() == 1 => {
                let value = args[0];
                s.intern(arena, value);
                positive_testers.push((value, *ctor));
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
    // Constructor exhaustiveness: a class cannot exclude every constructor of
    // its datatype, and a positive constructor fact cannot be excluded.
    if s.has_constructor_coverage_conflict(arena, &excluded_ctors, &positive_testers) {
        return true;
    }
    // Acyclicity: a value forced to strictly contain itself.
    s.has_containment_cycle(arena)
}

fn record_nullary_constructor_exclusion(
    arena: &TermArena,
    maybe_value: TermId,
    maybe_ctor: TermId,
    excluded_ctors: &mut BTreeMap<TermId, BTreeSet<ConstructorId>>,
) {
    let Some((ctor, args)) = as_construction(arena, maybe_ctor) else {
        return;
    };
    if !args.is_empty()
        || arena.sort_of(maybe_value) != Sort::Datatype(arena.constructor_datatype(ctor))
    {
        return;
    }
    excluded_ctors.entry(maybe_value).or_default().insert(ctor);
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

    /// Closes the partition under **congruence** (equal arguments ⇒ equal
    /// applications) and **injectivity** (equal applications ⇒ equal arguments) to a
    /// fixpoint, checking **distinctness** along the way. Returns `true` on a
    /// distinctness conflict (one class, two distinct constructors).
    fn close(&mut self, arena: &TermArena) -> bool {
        loop {
            let mut changed = false;
            let ctors = self.ctor_nodes.clone();
            for a in 0..ctors.len() {
                for b in (a + 1)..ctors.len() {
                    let (na, nb) = (ctors[a], ctors[b]);
                    let (ca, args_a) = as_construction(arena, self.term_of[na])
                        .expect("ctor_nodes holds constructor terms");
                    let (cb, args_b) = as_construction(arena, self.term_of[nb])
                        .expect("ctor_nodes holds constructor terms");
                    if self.find(na) == self.find(nb) {
                        if ca != cb {
                            return true; // distinctness: same value, two constructors
                        }
                        // Injectivity: equal constructor applications ⇒ equal fields.
                        for (&x, &y) in args_a.iter().zip(&args_b) {
                            if self.union(arena, x, y) {
                                changed = true;
                            }
                        }
                    } else if ca == cb
                        && args_a.len() == args_b.len()
                        && args_a
                            .iter()
                            .zip(&args_b)
                            .all(|(&x, &y)| self.same_class(x, y))
                    {
                        // Congruence: same constructor with pairwise-equal arguments
                        // ⇒ the two applications denote the same value.
                        if self.union(arena, self.term_of[na], self.term_of[nb]) {
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

    fn has_constructor_coverage_conflict(
        &mut self,
        arena: &TermArena,
        excluded_ctors: &BTreeMap<TermId, BTreeSet<ConstructorId>>,
        positive_testers: &[(TermId, ConstructorId)],
    ) -> bool {
        let mut excluded_by_class: BTreeMap<
            (usize, axeyum_ir::DatatypeId),
            BTreeSet<ConstructorId>,
        > = BTreeMap::new();
        for (&term, ctors) in excluded_ctors {
            let Sort::Datatype(dt) = arena.sort_of(term) else {
                continue;
            };
            let Some(root) = self.class_of(term) else {
                continue;
            };
            excluded_by_class
                .entry((root, dt))
                .or_default()
                .extend(ctors.iter().copied());
        }

        let mut positive_by_class: BTreeMap<
            (usize, axeyum_ir::DatatypeId),
            BTreeSet<ConstructorId>,
        > = BTreeMap::new();
        for &(term, ctor) in positive_testers {
            let dt = arena.constructor_datatype(ctor);
            let Some(root) = self.class_of(term) else {
                continue;
            };
            positive_by_class
                .entry((root, dt))
                .or_default()
                .insert(ctor);
        }
        for node in self.ctor_nodes.clone() {
            let (ctor, _args) = as_construction(arena, self.term_of[node])
                .expect("ctor_nodes holds constructor terms");
            let dt = arena.constructor_datatype(ctor);
            let root = self.find(node);
            positive_by_class
                .entry((root, dt))
                .or_default()
                .insert(ctor);
        }

        for ((class, dt), excluded) in &excluded_by_class {
            let constructors = arena.datatype_constructors(*dt);
            if !constructors.is_empty() && constructors.iter().all(|ctor| excluded.contains(ctor)) {
                return true;
            }
            if let Some(positive) = positive_by_class.get(&(*class, *dt))
                && positive.iter().any(|ctor| excluded.contains(ctor))
            {
                return true;
            }
        }

        positive_by_class
            .values()
            .any(|constructors| constructors.len() > 1)
    }

    fn class_of(&mut self, term: TermId) -> Option<usize> {
        self.index.get(&term).copied().map(|i| self.find(i))
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
    #[allow(clippy::many_single_char_names)]
    fn congruence_derives_equality_then_disequality_is_unsat() {
        // x = cons(h, a) ∧ y = cons(h, b) ∧ a = b ∧ x ≠ y ⇒ UNSAT: congruence gives
        // cons(h, a) = cons(h, b) from a = b, so x = y, contradicting x ≠ y. (The
        // injectivity-only closure missed this — it needs the forward congruence.)
        let mut arena = TermArena::new();
        let (dt, [_nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let y = arena.declare("y", Sort::Datatype(dt)).unwrap();
        let a = arena.declare("a", Sort::Datatype(dt)).unwrap();
        let b = arena.declare("b", Sort::Datatype(dt)).unwrap();
        let (xv, yv, av, bv) = (arena.var(x), arena.var(y), arena.var(a), arena.var(b));
        let h = arena.bv_var("h", 8).unwrap();
        let cxa = arena.construct(cons, &[h, av]).unwrap();
        let cyb = arena.construct(cons, &[h, bv]).unwrap();
        let e1 = arena.eq(xv, cxa).unwrap();
        let e2 = arena.eq(yv, cyb).unwrap();
        let e3 = arena.eq(av, bv).unwrap();
        let ne = {
            let xy = arena.eq(xv, yv).unwrap();
            arena.not(xy).unwrap()
        };
        assert!(prove_datatype_unsat_structurally(&arena, &[e1, e2, e3, ne]));
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
    fn or_of_structurally_unsat_branches_is_unsat() {
        // (x = cons(h, x)) OR (y = cons(g, y)): every branch violates datatype
        // acyclicity, so the disjunction is unsat.
        let mut arena = TermArena::new();
        let (dt, [_nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let y = arena.declare("y", Sort::Datatype(dt)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let h = arena.bv_var("h", 8).unwrap();
        let g = arena.bv_var("g", 8).unwrap();
        let cx = arena.construct(cons, &[h, xv]).unwrap();
        let cy = arena.construct(cons, &[g, yv]).unwrap();
        let e1 = arena.eq(xv, cx).unwrap();
        let e2 = arena.eq(yv, cy).unwrap();
        let disj = arena.or(e1, e2).unwrap();
        let cert = super::datatype_structural_refutation(&arena, &[disj])
            .expect("both datatype branches are structurally unsat");
        assert_eq!(cert.branches, 2);
    }

    #[test]
    fn or_with_one_non_refuted_branch_is_not_refuted() {
        // The second branch is satisfiable, so the disjunction must not be
        // refuted merely because the first branch contains a cycle.
        let mut arena = TermArena::new();
        let (dt, [_nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let y = arena.declare("y", Sort::Datatype(dt)).unwrap();
        let (xv, yv) = (arena.var(x), arena.var(y));
        let h = arena.bv_var("h", 8).unwrap();
        let cx = arena.construct(cons, &[h, xv]).unwrap();
        let cyclic = arena.eq(xv, cx).unwrap();
        let non_refuted = arena.eq(yv, yv).unwrap();
        let disj = arena.or(cyclic, non_refuted).unwrap();
        assert!(super::datatype_structural_refutation(&arena, &[disj]).is_none());
    }

    #[test]
    fn constructor_coverage_over_selector_is_unsat() {
        // cvc5 regression shape:
        //   (and (not (= nil (tail x))) (not (is-cons (tail x))))
        // A datatype value with every constructor excluded is impossible.
        let mut arena = TermArena::new();
        let (dt, [nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let xv = arena.var(x);
        let tail = arena.dt_select(cons, 1, xv).unwrap();
        let nil_value = arena.construct(nil, &[]).unwrap();
        let eq_nil = arena.eq(nil_value, tail).unwrap();
        let not_nil = arena.not(eq_nil).unwrap();
        let is_cons = arena.dt_test(cons, tail).unwrap();
        let not_cons = arena.not(is_cons).unwrap();
        let conjunction = arena.and(not_nil, not_cons).unwrap();
        let cert = super::datatype_structural_refutation(&arena, &[conjunction])
            .expect("both constructors are excluded");
        assert_eq!(cert.branches, 1);
    }

    #[test]
    fn one_constructor_exclusion_is_not_refuted() {
        let mut arena = TermArena::new();
        let (dt, [nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let xv = arena.var(x);
        let nil_value = arena.construct(nil, &[]).unwrap();
        let eq_nil = arena.eq(nil_value, xv).unwrap();
        let not_nil = arena.not(eq_nil).unwrap();
        assert!(super::datatype_structural_refutation(&arena, &[not_nil]).is_none());
        let is_cons = arena.dt_test(cons, xv).unwrap();
        assert!(super::datatype_structural_refutation(&arena, &[is_cons]).is_none());
    }

    #[test]
    fn positive_and_negative_tester_conflict_is_unsat() {
        let mut arena = TermArena::new();
        let (dt, [_nil, cons]) = int_list(&mut arena);
        let x = arena.declare("x", Sort::Datatype(dt)).unwrap();
        let xv = arena.var(x);
        let is_cons = arena.dt_test(cons, xv).unwrap();
        let not_cons = arena.not(is_cons).unwrap();
        assert!(super::datatype_structural_refutation(&arena, &[is_cons, not_cons]).is_some());
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
