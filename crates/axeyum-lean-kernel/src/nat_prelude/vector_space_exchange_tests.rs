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
    algs: NameId,
}

fn build(k: &mut Kernel) -> Fixture {
    let lg = build_logic_prelude(k).expect("logic prelude must build");
    let p = intern_structures_s_names(k);
    let ix = declare_index_surgery(k, &lg, p.algs).expect("AlgS.Index must admit");
    Fixture {
        lg,
        ix,
        algs: p.algs,
    }
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

/// The eight lemmas are `Theorem`s — the kernel checked their proof terms —
/// and the three surgeries are `Definition`s.
#[test]
fn the_index_lemmas_are_checked_theorems() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for name in [
        f.ix.le_zero_eq,
        f.ix.le_refl,
        f.ix.le_dichotomy,
        f.ix.le_succ_cases,
        f.ix.insert_at_at,
        f.ix.insert_at_below,
        f.ix.insert_at_above,
        f.ix.remove_at_insert_at,
    ] {
        let decl = k.environment().get(name).expect("must exist").clone();
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{name:?} must be a Theorem"
        );
    }
    for name in [f.ix.le, f.ix.remove_at, f.ix.insert_at] {
        let decl = k.environment().get(name).expect("must exist").clone();
        assert!(
            matches!(decl, Declaration::Definition { .. }),
            "{name:?} must be a Definition"
        );
    }
}

/// **The inventory for ADR-1657's fact ledger entries.** Prints every
/// declaration this module owns as `INDEX-INVENTORY|<name>|<rendered type>`,
/// read from `Kernel::environment` — so a fact's `formal.statement` is
/// transcribed from the KERNEL and never from source text.
///
/// The count is derived from `owned_names`, the authority, not from a
/// literal in this test.
#[test]
fn the_index_declaration_inventory() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let expected = f.ix.owned_names().len();
    let mut printed = 0usize;
    for name in f.ix.owned_names() {
        let decl = k
            .environment()
            .get(name)
            .expect("declaration must exist")
            .clone();
        let ty = match &decl {
            Declaration::Definition { ty, .. } | Declaration::Theorem { ty, .. } => *ty,
            _ => panic!("unexpected declaration kind"),
        };
        let rendered = k.render_lean(ty);
        assert!(!rendered.trim().is_empty(), "{name:?} rendered empty");
        assert!(
            rendered.contains("Nat"),
            "every AlgS.Index type is indexed by Nat, got: {rendered}"
        );
        println!("INDEX-INVENTORY|{name:?}|{rendered}");
        printed += 1;
    }
    assert_eq!(printed, expected, "every owned name must have printed");
}

/// The four order lemmas must mention `AlgS.Index.le` in their rendered
/// types, and the four surgery lemmas must mention the surgery they are
/// about — a lemma about the wrong constant would render differently.
#[test]
fn the_lemma_types_are_about_what_they_claim() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let render = |k: &mut Kernel, name| {
        let decl = k.environment().get(name).expect("must exist").clone();
        let ty = match &decl {
            Declaration::Definition { ty, .. } | Declaration::Theorem { ty, .. } => *ty,
            _ => panic!("unexpected declaration kind"),
        };
        k.render_lean(ty)
    };
    for name in [
        f.ix.le_zero_eq,
        f.ix.le_refl,
        f.ix.le_dichotomy,
        f.ix.le_succ_cases,
    ] {
        let r = render(&mut k, name);
        assert!(
            r.contains("AlgS.Index.le"),
            "an order lemma must be about AlgS.Index.le, got: {r}"
        );
    }
    for name in [
        f.ix.insert_at_at,
        f.ix.insert_at_below,
        f.ix.insert_at_above,
    ] {
        let r = render(&mut k, name);
        assert!(
            r.contains("AlgS.Index.insertAt"),
            "an insertion lemma must be about AlgS.Index.insertAt, got: {r}"
        );
    }
    let r = render(&mut k, f.ix.remove_at_insert_at);
    assert!(
        r.contains("AlgS.Index.removeAt") && r.contains("AlgS.Index.insertAt"),
        "the inverse lemma must mention BOTH surgeries, got: {r}"
    );
    // `le_dichotomy` must really be a disjunction, not one half of one.
    let r = render(&mut k, f.ix.le_dichotomy);
    assert!(
        r.contains("Or"),
        "le_dichotomy must conclude an Or, got: {r}"
    );
    // `removeAt_insertAt` must carry NO hypothesis: it holds at every index.
    let r = render(&mut k, f.ix.remove_at_insert_at);
    assert!(
        !r.contains("AlgS.Index.le"),
        "removeAt_insertAt is unconditional — it must not take an order hypothesis, got: {r}"
    );
}

/// **Negative control for `le_dichotomy`.** The successor branch returns the
/// induction hypothesis `ih n'` because `Or (le (succ m') (succ n'))
/// (le (succ (succ n')) (succ m'))` ι-reduces to `Or (le m' n')
/// (le (succ n') m')`. Feeding `ih` at the WRONG index — `ih` applied to
/// `succ n'` rather than `n'` — must be refused: it proves
/// `Or (le m' (succ n')) (le (succ (succ n')) m')`, which is a different
/// proposition.
#[test]
fn control_le_dichotomy_needs_the_hypothesis_at_the_predecessor() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let nat = k.const_(f.lg.nat, vec![]);
    let succ = k.const_(f.lg.nat_succ, vec![]);
    let or_c = k.const_(f.lg.or, vec![]);

    let mp = k.fvar(91_000);
    let np = k.fvar(91_001);
    let smp = k.app(succ, mp);
    let snp = k.app(succ, np);

    let goal = {
        let le = k.const_(f.ix.le, vec![]);
        let a = t_app(&mut k, le, &[smp, snp]);
        let le = k.const_(f.ix.le, vec![]);
        let ssnp = k.app(succ, snp);
        let b = t_app(&mut k, le, &[ssnp, smp]);
        app2(&mut k, or_c, a, b)
    };
    let ih_ty = {
        let n = k.fvar(91_002);
        let le = k.const_(f.ix.le, vec![]);
        let a = t_app(&mut k, le, &[mp, n]);
        let le = k.const_(f.ix.le, vec![]);
        let sn = k.app(succ, n);
        let b = t_app(&mut k, le, &[sn, mp]);
        let g = app2(&mut k, or_c, a, b);
        pi_over(&mut k, 91_002, nat, g)
    };
    let ih = k.fvar(91_003);
    // MUTATION: `ih (succ n')` where `ih n'` is required.
    let bad = k.app(ih, snp);
    let value = lam_over(&mut k, 91_003, ih_ty, bad);
    let value = lam_over(&mut k, 91_001, nat, value);
    let value = lam_over(&mut k, 91_000, nat, value);
    let ty = arrow(&mut k, ih_ty, goal);
    let ty = pi_over(&mut k, 91_001, nat, ty);
    let ty = pi_over(&mut k, 91_000, nat, ty);

    let ns = k.name_str(f.algs, "IndexControl");
    let name = k.name_str(ns, "dichotomy_at_the_wrong_index");
    let got = k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        got.is_err(),
        "the induction hypothesis at `succ n'` proves a different disjunction"
    );
    // Positive twin: the real lemma is present.
    assert!(
        k.environment().get(f.ix.le_dichotomy).is_some(),
        "the real le_dichotomy must be present"
    );
}

/// **Negative control for `removeAt_insertAt`.** Its successor step is the
/// induction hypothesis at the SHIFTED family `fun t => v (succ t)`. Passing
/// the unshifted `v` — a one-token change — must be refused.
#[test]
fn control_remove_at_insert_at_needs_the_shifted_family() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let nat = k.const_(f.lg.nat, vec![]);
    let succ = k.const_(f.lg.nat_succ, vec![]);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let fam_ty = arrow(&mut k, nat, nat);

    let w = k.fvar(92_000);
    let ip = k.fvar(92_001);
    let v = k.fvar(92_002);
    let jp = k.fvar(92_003);
    let sip = k.app(succ, ip);
    let sjp = k.app(succ, jp);

    let stmt = |k: &mut Kernel, i: ExprId, v: ExprId, j: ExprId| {
        let c = k.const_(f.ix.insert_at, vec![]);
        let ins = t_app(k, c, &[nat, i, w, v]);
        let c = k.const_(f.ix.remove_at, vec![]);
        let lhs = t_app(k, c, &[nat, i, ins, j]);
        let rhs = k.app(v, j);
        eq_of(k, &f.lg, l1, nat, lhs, rhs)
    };

    let ih_ty = {
        let vv = k.fvar(92_004);
        let jj = k.fvar(92_005);
        let s = stmt(&mut k, ip, vv, jj);
        let b = pi_over(&mut k, 92_005, nat, s);
        pi_over(&mut k, 92_004, fam_ty, b)
    };
    let ih = k.fvar(92_006);
    let goal = stmt(&mut k, sip, v, sjp);
    // MUTATION: the unshifted family `v` where `fun t => v (succ t)` belongs.
    let bad = {
        let e = k.app(ih, v);
        k.app(e, jp)
    };
    let value = lam_over(&mut k, 92_006, ih_ty, bad);
    let value = lam_over(&mut k, 92_003, nat, value);
    let value = lam_over(&mut k, 92_002, fam_ty, value);
    let value = lam_over(&mut k, 92_001, nat, value);
    let value = lam_over(&mut k, 92_000, nat, value);
    let ty = arrow(&mut k, ih_ty, goal);
    let ty = pi_over(&mut k, 92_003, nat, ty);
    let ty = pi_over(&mut k, 92_002, fam_ty, ty);
    let ty = pi_over(&mut k, 92_001, nat, ty);
    let ty = pi_over(&mut k, 92_000, nat, ty);

    let ns = k.name_str(f.algs, "IndexControl");
    let name = k.name_str(ns, "remove_insert_unshifted_family");
    let got = k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        got.is_err(),
        "the induction hypothesis at the UNSHIFTED family proves the wrong equation"
    );
    assert!(
        k.environment().get(f.ix.remove_at_insert_at).is_some(),
        "the real removeAt_insertAt must be present"
    );
}
