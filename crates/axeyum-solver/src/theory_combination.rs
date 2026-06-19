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

use std::collections::{BTreeMap, BTreeSet};

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
}
