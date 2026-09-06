//! Tests for [`super`] — `AlgS.Index.*`.
//!
//! Every `Definition` here is checked by **evaluation at concrete, small,
//! discriminating arguments**: the trusted gate cannot tell you a definition
//! computes the wrong value, only that it type-checks, and `removeAt` /
//! `insertAt` / `le` all have the right type with the index shifted by one.

use super::*;
use crate::build_logic_prelude;
use crate::nat_prelude::structures_setoid::intern_structures_s_names;

struct Fixture {
    lg: LogicPrelude,
    ix: IndexNames,
}

fn build(k: &mut Kernel) -> Fixture {
    let lg = build_logic_prelude(k).expect("logic prelude must build");
    let p = intern_structures_s_names(k);
    let ix = declare_index_surgery(k, &lg, p.algs).expect("AlgS.Index must admit");
    Fixture { lg, ix }
}

/// `Nat.succ^n Nat.zero`. Kept to single digits: every `Nat` numeral at this
/// build position is unary.
fn nat_lit(k: &mut Kernel, lg: &LogicPrelude, n: usize) -> ExprId {
    let mut e = k.const_(lg.nat_zero, vec![]);
    let s = k.const_(lg.nat_succ, vec![]);
    for _ in 0..n {
        e = k.app(s, e);
    }
    e
}

/// The identity family `fun t : Nat => t`.
fn id_family(k: &mut Kernel, lg: &LogicPrelude) -> ExprId {
    let nat = k.const_(lg.nat, vec![]);
    let t = k.fvar(90_100);
    lam_over(k, 90_100, nat, t)
}

fn le_at(k: &mut Kernel, f: &Fixture, a: usize, b: usize) -> ExprId {
    let c = k.const_(f.ix.le, vec![]);
    let x = nat_lit(k, &f.lg, a);
    let y = nat_lit(k, &f.lg, b);
    t_app(k, c, &[x, y])
}

fn remove_at(k: &mut Kernel, f: &Fixture, i: usize, fam: ExprId, j: usize) -> ExprId {
    let c = k.const_(f.ix.remove_at, vec![]);
    let nat = k.const_(f.lg.nat, vec![]);
    let iv = nat_lit(k, &f.lg, i);
    let jv = nat_lit(k, &f.lg, j);
    t_app(k, c, &[nat, iv, fam, jv])
}

fn insert_at(k: &mut Kernel, f: &Fixture, i: usize, w: ExprId, fam: ExprId, j: usize) -> ExprId {
    let c = k.const_(f.ix.insert_at, vec![]);
    let nat = k.const_(f.lg.nat, vec![]);
    let iv = nat_lit(k, &f.lg, i);
    let jv = nat_lit(k, &f.lg, j);
    t_app(k, c, &[nat, iv, w, fam, jv])
}

#[test]
fn the_index_layer_admits() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for name in f.ix.owned_names() {
        assert!(
            k.environment().get(name).is_some(),
            "declaration missing from the environment"
        );
    }
}

/// The headline claim, read from `Kernel::axiom_footprint` — after
/// `Environment::contains`, because a MISSING name also returns an empty
/// footprint.
#[test]
fn the_index_layer_is_axiom_free() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for name in f.ix.owned_names() {
        assert!(
            k.environment().get(name).is_some(),
            "the name must exist before its footprint means anything"
        );
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "axiom footprint must be empty, got {} entries",
            footprint.len()
        );
    }
}

/// **Evaluation test for `AlgS.Index.le`.** `le a b` must reduce to `True`
/// exactly when `a <= b` and to `False` otherwise, at the boundary pairs
/// where an off-by-one would show.
#[test]
fn le_decides_the_small_pairs() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let true_ = k.const_(f.lg.true_, vec![]);
    let false_ = k.const_(f.lg.false_, vec![]);

    for (a, b) in [(0usize, 0usize), (0, 1), (1, 1), (2, 3), (3, 3), (0, 4)] {
        let e = le_at(&mut k, &f, a, b);
        assert!(k.def_eq(e, true_), "le {a} {b} must reduce to True");
        let e = le_at(&mut k, &f, a, b);
        assert!(
            !k.def_eq(e, false_),
            "le {a} {b} must not also reduce to False"
        );
    }
    for (a, b) in [(1usize, 0usize), (2, 1), (3, 2), (4, 0)] {
        let e = le_at(&mut k, &f, a, b);
        assert!(k.def_eq(e, false_), "le {a} {b} must reduce to False");
        let e = le_at(&mut k, &f, a, b);
        assert!(
            !k.def_eq(e, true_),
            "le {a} {b} must not also reduce to True"
        );
    }
}

/// **Evaluation test for `AlgS.Index.removeAt`.** At the identity family
/// `fun t => t`, `removeAt 2` must enumerate `0, 1, 3, 4` — the value at
/// index 2 is `3`, which is exactly where an off-by-one in either direction
/// changes the answer.
#[test]
fn remove_at_deletes_the_named_index_and_shifts_down() {
    let mut k = Kernel::new();
    let f = build(&mut k);

    // `removeAt 0 id = 1, 2, 3, …`
    for (j, want) in [(0usize, 1usize), (1, 2), (2, 3)] {
        let fam = id_family(&mut k, &f.lg);
        let got = remove_at(&mut k, &f, 0, fam, j);
        let expect = nat_lit(&mut k, &f.lg, want);
        assert!(k.def_eq(got, expect), "removeAt 0 id {j} must be {want}");
    }
    // `removeAt 2 id = 0, 1, 3, 4`
    for (j, want) in [(0usize, 0usize), (1, 1), (2, 3), (3, 4)] {
        let fam = id_family(&mut k, &f.lg);
        let got = remove_at(&mut k, &f, 2, fam, j);
        let expect = nat_lit(&mut k, &f.lg, want);
        assert!(k.def_eq(got, expect), "removeAt 2 id {j} must be {want}");
    }
    // Discriminating negative: the deleted index is really gone.
    let fam = id_family(&mut k, &f.lg);
    let got = remove_at(&mut k, &f, 2, fam, 2);
    let two = nat_lit(&mut k, &f.lg, 2);
    assert!(
        !k.def_eq(got, two),
        "removeAt 2 id 2 must NOT be 2 — index 2 is the one that was deleted"
    );
}

/// **Evaluation test for `AlgS.Index.insertAt`.** `insertAt 2 3 id` must
/// enumerate `0, 1, 3, 2, 3`: the inserted value sits at index 2 and the old
/// tail is shifted up. The inserted value `3` is deliberately equal to a
/// value the family already takes, so the test cannot pass by matching the
/// wrong occurrence — index 3 must be `2`, which no shift-free or
/// shift-by-two reading produces.
#[test]
fn insert_at_places_the_value_and_shifts_up() {
    let mut k = Kernel::new();
    let f = build(&mut k);

    // `insertAt 0 3 id = 3, 0, 1, 2, …`
    for (j, want) in [(0usize, 3usize), (1, 0), (2, 1)] {
        let fam = id_family(&mut k, &f.lg);
        let w = nat_lit(&mut k, &f.lg, 3);
        let got = insert_at(&mut k, &f, 0, w, fam, j);
        let expect = nat_lit(&mut k, &f.lg, want);
        assert!(k.def_eq(got, expect), "insertAt 0 3 id {j} must be {want}");
    }
    // `insertAt 2 3 id = 0, 1, 3, 2, 3`
    for (j, want) in [(0usize, 0usize), (1, 1), (2, 3), (3, 2), (4, 3)] {
        let fam = id_family(&mut k, &f.lg);
        let w = nat_lit(&mut k, &f.lg, 3);
        let got = insert_at(&mut k, &f, 2, w, fam, j);
        let expect = nat_lit(&mut k, &f.lg, want);
        assert!(k.def_eq(got, expect), "insertAt 2 3 id {j} must be {want}");
    }
    // Discriminating negative: index 3 is the shifted `2`, not the old `3`.
    let fam = id_family(&mut k, &f.lg);
    let w = nat_lit(&mut k, &f.lg, 3);
    let got = insert_at(&mut k, &f, 2, w, fam, 3);
    let three = nat_lit(&mut k, &f.lg, 3);
    assert!(
        !k.def_eq(got, three),
        "insertAt 2 3 id 3 must be the shifted 2, not 3"
    );
}

/// The two surgeries are inverse at the concrete level, definitionally:
/// `removeAt i (insertAt i w v) j` computes back to `v j`. This is the
/// arithmetic content the exchange lemma above needs, checked before any
/// theorem asserts it.
#[test]
fn remove_undoes_insert_at_small_indices() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let nat = k.const_(f.lg.nat, vec![]);
    for i in 0usize..3 {
        for j in 0usize..4 {
            let fam = id_family(&mut k, &f.lg);
            let w = nat_lit(&mut k, &f.lg, 3);
            let inserted = {
                let c = k.const_(f.ix.insert_at, vec![]);
                let iv = nat_lit(&mut k, &f.lg, i);
                let e = t_app(&mut k, c, &[nat, iv, w, fam]);
                // eta-expand back to a family so `removeAt` receives a
                // `Nat -> Nat`, not a partially applied constant.
                let t = k.fvar(90_200);
                let b = k.app(e, t);
                lam_over(&mut k, 90_200, nat, b)
            };
            let got = remove_at(&mut k, &f, i, inserted, j);
            let expect = nat_lit(&mut k, &f.lg, j);
            assert!(
                k.def_eq(got, expect),
                "removeAt {i} (insertAt {i} 3 id) {j} must be {j}"
            );
        }
    }
}
