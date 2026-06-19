//! Theory combination (Nelson–Oppen / interface equalities), Track 1 **P1.6**.
//!
//! axeyum's current multi-theory composition is reduction-stacked and eager (e.g.
//! `QF_UFBV` via Ackermann): the only coupling between theories is propositional.
//! Real combination exchanges **interface equalities** between the **shared terms**
//! of two theories — the terms a Nelson–Oppen / model-based combination must agree
//! on. This module begins that work; [`shared_terms`] is **T1.6.1**: identify the
//! shared terms between the **uninterpreted-function (EUF)** theory and the
//! **bit-vector** theory on a query.
//!
//! A term is **shared** between EUF and BV when it is bit-vector-sorted and it is
//! both
//! - **EUF-relevant** — an argument to, or the result of, an uninterpreted-function
//!   application ([`Op::Apply`]); and
//! - **BV-relevant** — an operand to, or the result of, an *interpreted* bit-vector
//!   operation (`bvadd`, `bvult`, `concat`, …).
//!
//! These are exactly the terms across which the two theories must reconcile (the
//! purification interface): a value the bit-vector solver assigns to such a term has
//! to be consistent with the equalities the congruence closure derives over it, and
//! vice versa. Downstream tasks (T1.6.2 `th_eq` bus, T1.6.3 interface-equality
//! case-splitting) propose and split on equalities *between* these shared terms.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_egraph::{EGraph, ENodeId};
use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode, Value, eval};

use crate::model::Model;

/// Which theory owns an operator, for EUF + bit-vector combination.
#[derive(Clone, Copy, PartialEq, Eq)]
enum OpTheory {
    /// An uninterpreted-function application (`Op::Apply`).
    Euf,
    /// An interpreted operator over bit-vectors (everything else that touches a
    /// bit-vector and is not a boundary connective).
    BitVec,
    /// A sort-polymorphic boundary connective (`=`, `ite`) — it connects operands
    /// but belongs to no single theory, so it assigns membership to neither side.
    Boundary,
}

fn op_theory(op: &Op) -> OpTheory {
    match op {
        Op::Apply(_) => OpTheory::Euf,
        Op::Eq | Op::Ite => OpTheory::Boundary,
        // Every other interpreted operator is treated as bit-vector-theory; the
        // bit-vector-sortedness filter in `shared_terms` restricts what counts (so a
        // purely Boolean connective contributes nothing — its operands are `Bool`).
        _ => OpTheory::BitVec,
    }
}

/// The bit-vector-sorted terms **shared** between the EUF and bit-vector theories on
/// `assertions` — the Nelson–Oppen interface terms (P1.6, T1.6.1).
///
/// A term qualifies when it is `BitVec`-sorted and appears both as an
/// argument/result of an uninterpreted-function application **and** as an
/// operand/result of an interpreted bit-vector operation. The result is sorted by
/// [`TermId`] (deterministic — no hash-map iteration order in output).
///
/// This is pure structural discovery over the term DAG; it asserts nothing and is
/// independent of any solver state, so it composes with either the eager Ackermann
/// path or a future online combination loop.
#[must_use]
pub fn shared_terms(arena: &TermArena, assertions: &[TermId]) -> Vec<TermId> {
    let is_bv = |t: TermId| matches!(arena.sort_of(t), Sort::BitVec(_));
    let mut euf: BTreeSet<TermId> = BTreeSet::new();
    let mut bv: BTreeSet<TermId> = BTreeSet::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();

    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            let theory = op_theory(op);
            let bucket = match theory {
                OpTheory::Euf => Some(&mut euf),
                OpTheory::BitVec => Some(&mut bv),
                OpTheory::Boundary => None,
            };
            if let Some(set) = bucket {
                if is_bv(t) {
                    set.insert(t);
                }
                for &a in args {
                    if is_bv(a) {
                        set.insert(a);
                    }
                }
            }
            for &a in args {
                stack.push(a);
            }
        }
    }
    euf.intersection(&bv).copied().collect()
}

/// Propose **interface equalities** between `shared` terms that take the **same
/// value** in `model` — the *propose* step of Z3-style model-based combination
/// (P1.6, toward T1.6.3).
///
/// Given a model produced by one theory (e.g. the bit-vector solver assigning a
/// value to each shared term), two shared terms with equal model values are
/// candidate equalities the **other** theory (the congruence closure) should be
/// asked to confirm or refute — by asserting them and re-checking, or case-splitting
/// when undetermined. We return a **spanning chain** within each equal-value group
/// (consecutive pairs of the group's [`TermId`]-sorted members), which is enough:
/// transitivity over the chain induces every pairwise equality in the group, so a
/// quadratic blow-up is avoided. The result is deterministic (groups keyed by the
/// `(width, value)` bit pattern, members and groups sorted).
///
/// Terms that do not evaluate to a bit-vector value under `model` are skipped (a
/// complete model over the bit-vector-sorted shared terms evaluates them all).
#[must_use]
pub fn propose_interface_equalities(
    arena: &TermArena,
    shared: &[TermId],
    model: &Model,
) -> Vec<(TermId, TermId)> {
    let assignment = model.to_assignment();
    // Group the shared terms by their concrete value (the bit pattern is the key).
    let mut by_value: BTreeMap<(u32, u128), Vec<TermId>> = BTreeMap::new();
    for &t in shared {
        if let Ok(Value::Bv { width, value }) = eval(arena, t, &assignment) {
            by_value.entry((width, value)).or_default().push(t);
        }
    }
    let mut pairs = Vec::new();
    for members in by_value.values() {
        // `members` is in insertion order; sort for determinism, then chain.
        let mut sorted = members.clone();
        sorted.sort_unstable();
        for window in sorted.windows(2) {
            pairs.push((window[0], window[1]));
        }
    }
    pairs
}

/// The congruence closure's verdict on a proposed interface equality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterfaceStatus {
    /// Already entailed — the two terms are in the same congruence class, so the
    /// other theory's equality is consistent with the EUF side (no split needed).
    Entailed,
    /// Refuted — the EUF side has a disequality forcing the two classes apart, so
    /// the other theory's equality is inconsistent (a conflict / lemma to learn).
    Refuted,
    /// Neither entailed nor refuted by the current EUF assertions — a genuine
    /// interface equality to **case-split** on.
    Undetermined,
}

/// A minimal term→e-node interner: assigns a stable decl id per symbol / constant /
/// operator and hash-conses the term DAG into an [`EGraph`], so congruence holds.
struct Interner {
    egraph: EGraph,
    decls: HashMap<String, u32>,
    nodes: HashMap<TermId, ENodeId>,
}

impl Interner {
    fn new() -> Self {
        Self {
            egraph: EGraph::new(),
            decls: HashMap::new(),
            nodes: HashMap::new(),
        }
    }

    fn decl(&mut self, key: String) -> u32 {
        let next = u32::try_from(self.decls.len()).expect("decl count fits u32");
        *self.decls.entry(key).or_insert(next)
    }

    fn node(&mut self, arena: &TermArena, term: TermId) -> ENodeId {
        if let Some(&n) = self.nodes.get(&term) {
            return n;
        }
        let n = match arena.node(term) {
            TermNode::App { op, args } => {
                let args: Vec<TermId> = args.to_vec();
                let kids: Vec<ENodeId> = args.iter().map(|&a| self.node(arena, a)).collect();
                let decl = self.decl(format!("op:{op:?}"));
                self.egraph.add(decl, &kids)
            }
            TermNode::Symbol(s) => {
                let decl = self.decl(format!("sym:{}", s.index()));
                self.egraph.add(decl, &[])
            }
            other => {
                // Each distinct literal value is a distinct nullary constant.
                let decl = self.decl(format!("const:{other:?}"));
                self.egraph.add(decl, &[])
            }
        };
        self.nodes.insert(term, n);
        n
    }
}

/// Classify each `proposed` interface equality against the **congruence closure** of
/// `euf_assertions` — the confirm/refute step of model-based combination (P1.6,
/// toward T1.6.3).
///
/// `euf_assertions` are the EUF-side literals (a conjunctive theory state); top-level
/// `(= a b)` merge classes (congruence cascades), and `(not (= a b))` record
/// disequalities. A proposed equality `(x, y)` is then [`InterfaceStatus::Entailed`]
/// if congruence already makes them equal, [`InterfaceStatus::Refuted`] if an
/// asserted disequality separates their classes, else
/// [`InterfaceStatus::Undetermined`]. Sound: it uses the same backtrackable e-graph
/// as the EUF theory, so an `Entailed`/`Refuted` verdict is a genuine congruence
/// fact, and `Undetermined` is the safe default (a split, never a guess).
#[must_use]
pub fn classify_interface_equalities(
    arena: &TermArena,
    euf_assertions: &[TermId],
    proposed: &[(TermId, TermId)],
) -> Vec<((TermId, TermId), InterfaceStatus)> {
    let mut intern = Interner::new();
    let mut diseqs: Vec<(ENodeId, ENodeId)> = Vec::new();

    for &assertion in euf_assertions {
        if let TermNode::App { op, args } = arena.node(assertion) {
            match op {
                Op::Eq => {
                    let (l, r) = (args[0], args[1]);
                    let nl = intern.node(arena, l);
                    let nr = intern.node(arena, r);
                    intern.egraph.merge(nl, nr, 0);
                }
                Op::BoolNot => {
                    let inner = args[0];
                    if let TermNode::App {
                        op: Op::Eq,
                        args: eq_args,
                    } = arena.node(inner)
                    {
                        let (l, r) = (eq_args[0], eq_args[1]);
                        let nl = intern.node(arena, l);
                        let nr = intern.node(arena, r);
                        diseqs.push((nl, nr));
                    }
                }
                _ => {}
            }
        }
    }

    proposed
        .iter()
        .map(|&(x, y)| {
            let nx = intern.node(arena, x);
            let ny = intern.node(arena, y);
            let (rx, ry) = (intern.egraph.root(nx), intern.egraph.root(ny));
            let status = if rx == ry {
                InterfaceStatus::Entailed
            } else if diseqs.iter().any(|&(a, b)| {
                let (ra, rb) = (intern.egraph.root(a), intern.egraph.root(b));
                (ra == rx && rb == ry) || (ra == ry && rb == rx)
            }) {
                InterfaceStatus::Refuted
            } else {
                InterfaceStatus::Undetermined
            };
            ((x, y), status)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Sort;

    fn bv(arena: &mut TermArena, name: &str, w: u32) -> TermId {
        let s = arena.declare(name, Sort::BitVec(w)).unwrap();
        arena.var(s)
    }

    #[test]
    fn interface_term_between_uf_and_bv_is_shared() {
        // f(x) = y ∧ x + 1 = z. x is a UF argument AND a bvadd operand → shared.
        // y is only a UF result; z only a bvadd result; neither is shared.
        let mut arena = TermArena::new();
        let x = bv(&mut arena, "x", 8);
        let y = bv(&mut arena, "y", 8);
        let z = bv(&mut arena, "z", 8);
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let fx = arena.apply(f, &[x]).unwrap();
        let e1 = arena.eq(fx, y).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let sum = arena.bv_add(x, one).unwrap();
        let e2 = arena.eq(sum, z).unwrap();

        assert_eq!(shared_terms(&arena, &[e1, e2]), vec![x]);
    }

    #[test]
    fn uf_result_feeding_bv_op_is_also_shared() {
        // g(x) used inside bvadd: both the UF arg x and the UF result g(x) are
        // shared (g(x) is a UF result AND a bvadd operand).
        let mut arena = TermArena::new();
        let x = bv(&mut arena, "x", 8);
        let g = arena
            .declare_fun("g", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let gx = arena.apply(g, &[x]).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let sum = arena.bv_add(gx, one).unwrap(); // g(x) is a bvadd operand
        let zero = arena.bv_const(8, 0).unwrap();
        let e = arena.eq(sum, zero).unwrap();
        // x is a UF arg but never a BV operand here, so only g(x) is shared.
        assert_eq!(shared_terms(&arena, &[e]), vec![gx]);
    }

    #[test]
    fn pure_bv_query_has_no_shared_terms() {
        // No uninterpreted functions ⇒ nothing is EUF-relevant ⇒ no shared terms.
        let mut arena = TermArena::new();
        let x = bv(&mut arena, "x", 8);
        let y = bv(&mut arena, "y", 8);
        let sum = arena.bv_add(x, y).unwrap();
        let z = bv(&mut arena, "z", 8);
        let e = arena.eq(sum, z).unwrap();
        assert!(shared_terms(&arena, &[e]).is_empty());
    }

    #[test]
    fn pure_uf_query_has_no_shared_terms() {
        // Uninterpreted functions but no interpreted BV op ⇒ nothing BV-relevant.
        let mut arena = TermArena::new();
        let x = bv(&mut arena, "x", 8);
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let fx = arena.apply(f, &[x]).unwrap();
        let ffx = arena.apply(f, &[fx]).unwrap();
        let e = arena.eq(fx, ffx).unwrap();
        assert!(shared_terms(&arena, &[e]).is_empty());
    }

    #[test]
    fn proposes_equalities_between_equal_valued_shared_terms() {
        let mut arena = TermArena::new();
        let xs = arena.declare("x", Sort::BitVec(8)).unwrap();
        let ys = arena.declare("y", Sort::BitVec(8)).unwrap();
        let zs = arena.declare("z", Sort::BitVec(8)).unwrap();
        let ws = arena.declare("w", Sort::BitVec(8)).unwrap();
        let (x, y, z, w) = (arena.var(xs), arena.var(ys), arena.var(zs), arena.var(ws));
        // Model: x = y = z = 5, w = 3.
        let mut model = Model::new();
        model.set(xs, Value::Bv { width: 8, value: 5 });
        model.set(ys, Value::Bv { width: 8, value: 5 });
        model.set(zs, Value::Bv { width: 8, value: 5 });
        model.set(ws, Value::Bv { width: 8, value: 3 });

        // The 5-group {x,y,z} yields the spanning chain (x,y),(y,z); w is alone.
        assert_eq!(
            propose_interface_equalities(&arena, &[x, y, z, w], &model),
            vec![(x, y), (y, z)],
        );

        // All-distinct values → no proposed equalities.
        let mut distinct = Model::new();
        distinct.set(xs, Value::Bv { width: 8, value: 1 });
        distinct.set(ys, Value::Bv { width: 8, value: 2 });
        assert!(propose_interface_equalities(&arena, &[x, y], &distinct).is_empty());
    }

    #[test]
    fn classifies_proposed_equalities_against_congruence() {
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 8);
        let b = bv(&mut arena, "b", 8);
        let c = bv(&mut arena, "c", 8);
        let d = bv(&mut arena, "d", 8);
        let f = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();

        // EUF state: a = b, and c ≠ d.
        let eq_ab = arena.eq(a, b).unwrap();
        let ne_cd = {
            let e = arena.eq(c, d).unwrap();
            arena.not(e).unwrap()
        };

        let result = classify_interface_equalities(
            &arena,
            &[eq_ab, ne_cd],
            &[(a, b), (c, d), (a, c), (fa, fb)],
        );
        assert_eq!(
            result,
            vec![
                ((a, b), InterfaceStatus::Entailed),     // asserted directly
                ((c, d), InterfaceStatus::Refuted),      // asserted disequality
                ((a, c), InterfaceStatus::Undetermined), // neither
                ((fa, fb), InterfaceStatus::Entailed),   // by CONGRUENCE (a=b ⇒ f a=f b)
            ],
        );
    }
}
