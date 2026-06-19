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

use std::collections::BTreeSet;

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};

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
}
