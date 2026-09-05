//! Tests for the `Sigma` residue of ADR-1620. Every assertion reads the
//! KERNEL: admission, `Kernel::axiom_footprint`, the `Declaration` kind, the
//! rendered type, `def_eq` in BOTH directions, and four mutations each of
//! which is a SMALL term change carrying a positive twin in the same test.

use super::*;
use crate::build_logic_prelude;
use crate::nat_prelude::structures as algeq;
use crate::nat_prelude::structures_setoid::{
    StructuresSRecordNames, declare_structures_s_all, declare_structures_s_extra,
    intern_structures_s_names,
};

struct Fixture {
    lg: LogicPrelude,
    st: StructuresSRecordNames,
    recs: CategoryRecords,
    cs: CategoryNames,
    grp_recs: GroupCatRecords,
    gs: GroupCatNames,
}

fn build(k: &mut Kernel) -> Fixture {
    let lg = build_logic_prelude(k).expect("logic prelude must build");
    let alg_p = algeq::intern_structures_names(k);
    let alg_st = algeq::declare_structures_all(k, &alg_p, &lg).expect("Alg spine builds");
    let p = intern_structures_s_names(k);
    let st = declare_structures_s_all(k, &p, &lg).expect("AlgS spine builds");
    let extra = declare_structures_s_extra(k, &lg, &p, &st, &alg_p, &alg_st)
        .expect("the AlgS extras must build");
    let deps = GroupCatDeps {
        map_one: extra.hom_map_one,
    };
    let (recs, cs, grp_recs, gs, _ps) =
        super::super::declare_category_setoid(k, &lg, &st.monoid, &st.group, deps)
            .expect("the Sigma-residue layer must admit");
    Fixture {
        lg,
        st,
        recs,
        cs,
        grp_recs,
        gs,
    }
}

/// Rebuild the `PtAlg` vocabulary from the declared names, so the tests reach
/// the same accessors production code does.
fn pt_ctx(k: &mut Kernel, lg: &LogicPrelude, gs: &GroupCatNames) -> PtCtx {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let sort1 = k.sort(l1);
    let outer_beta = {
        let n = k.fvar(99_900);
        let ib = inner_beta(k, n);
        let body = sig_ty(k, lg, l0, l0, n, ib);
        lam_over(k, 99_900, sort1, body)
    };
    PtCtx {
        outer_alpha: sort1,
        outer_beta,
        l0,
        l1,
        pt: k.const_(gs.pt_alg, vec![]),
        carrier: k.const_(gs.pt_carrier, vec![]),
        zero: k.const_(gs.pt_zero, vec![]),
        succ: k.const_(gs.pt_succ, vec![]),
    }
}

fn decl_ty(k: &Kernel, name: NameId) -> ExprId {
    match k.environment().get(name).expect("declaration exists") {
        Declaration::Definition { ty, .. } | Declaration::Theorem { ty, .. } => *ty,
        other => panic!("unexpected declaration kind: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Admission, footprint, kind.
// ---------------------------------------------------------------------------

#[test]
fn the_sigma_residue_admits_and_is_axiom_free() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let names = f.gs.all();
    assert_eq!(names.len(), 25, "twenty-five declarations");
    for name in names {
        assert!(
            k.environment().get(name).is_some(),
            "declaration {name:?} missing from the environment"
        );
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "axiom footprint of {name:?} must be empty, got {} entries",
            footprint.len()
        );
    }
    let fl = f.grp_recs.functor_large;
    assert!(
        k.environment().get(fl.ind).is_some(),
        "FunctorLarge missing"
    );
    assert_eq!(fl.field_count(), 7, "FunctorLarge has seven fields");
    for i in 0..fl.field_count() {
        assert!(
            k.environment().get(fl.sel(i)).is_some(),
            "FunctorLarge selector {i} missing"
        );
        assert!(
            k.axiom_footprint(fl.sel(i)).is_empty(),
            "FunctorLarge selector {i} must be axiom-free"
        );
    }
}

/// The three headline results must be **checked `Theorem`s**, not definitions
/// dressed up as such.
#[test]
fn the_three_results_are_checked_theorems() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let mut n = 0;
    for name in [
        f.gs.is_grp_hom_congr,
        f.gs.is_mon_hom_id,
        f.gs.is_mon_hom_comp,
        f.gs.is_mon_hom_congr,
        f.gs.functor_large_is_functor,
        f.gs.forget_grp_mon_is_functor,
        f.gs.nat_pt_alg_is_initial,
    ] {
        let d = k.environment().get(name).expect("exists").clone();
        assert!(
            matches!(d, Declaration::Theorem { .. }),
            "{name:?} must be a checked Theorem, got {d:?}"
        );
        n += 1;
    }
    assert_eq!(n, 7, "seven checked theorems");
    for name in [f.gs.grp, f.gs.mon, f.gs.pt_cat, f.gs.forget_grp_mon] {
        let d = k.environment().get(name).expect("exists").clone();
        assert!(
            matches!(d, Declaration::Definition { .. }),
            "{name:?} must be a Definition"
        );
    }
}

/// Prints every rendered type so a referee reads the statements out of the
/// suite, and pins each construction's universe **in both directions**.
#[test]
fn the_types_render_and_pin_their_universes() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for name in f.gs.all() {
        let ty = decl_ty(&k, name);
        println!("decl {name:?} :\n  {}\n", k.render_lean(ty));
    }
    let Declaration::Inductive { ty: fl_ty, .. } = k
        .environment()
        .get(f.grp_recs.functor_large.ind)
        .expect("exists")
        .clone()
    else {
        panic!("FunctorLarge must be an inductive");
    };
    println!("record FunctorLarge : {}", k.render_lean(fl_ty));

    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let l2 = k.level_succ(l1);
    let l3 = k.level_succ(l2);
    let sort1 = k.sort(l1);
    let sort2 = k.sort(l2);
    let sort3 = k.sort(l3);

    // `CatS.FunctorLarge : Sort 3`, and NOT Sort 2.
    assert!(k.def_eq(fl_ty, sort3), "FunctorLarge must live at Sort 3");
    assert!(
        !k.def_eq(fl_ty, sort2),
        "FunctorLarge must NOT live at Sort 2"
    );

    // `CatS.grp` / `CatS.mon` / `CatS.ptAlg` are `CategoryLarge`, not
    // `Category` -- the objects are `Sort 2`, so the small record cannot hold
    // them. This is a level fact, not the ADR-1495 guard.
    let large = k.const_(f.recs.category_large.ind, vec![]);
    let small = k.const_(f.recs.category.ind, vec![]);
    for name in [f.gs.grp, f.gs.mon, f.gs.pt_cat] {
        let ty = decl_ty(&k, name);
        assert!(k.def_eq(ty, large), "{name:?} must be a CatS.CategoryLarge");
        assert!(!k.def_eq(ty, small), "{name:?} must NOT be a CatS.Category");
    }

    // `CatS.PtAlg : Sort 2` -- and neither Sort 1 nor Sort 3.
    let pt_ty = decl_ty(&k, f.gs.pt_alg);
    assert!(k.def_eq(pt_ty, sort2), "PtAlg must live at Sort 2");
    assert!(!k.def_eq(pt_ty, sort1), "PtAlg must NOT live at Sort 1");
    assert!(!k.def_eq(pt_ty, sort3), "PtAlg must NOT live at Sort 3");
}

// ---------------------------------------------------------------------------
// Evaluation tests. Every new `Definition` gets one, with a discriminating
// negative twin.
// ---------------------------------------------------------------------------

/// **The measurement ADR-1620 was one `Subtype` short of.** The objects of
/// `CatS.grp` are `AlgS.Group`, and the hom-family is the BUNDLED pair --
/// explicitly NOT the bare function space, which is the escape ADR-1620
/// measured as making `compCongr` false.
#[test]
fn the_group_category_has_bundled_morphisms() {
    use algs::group::CARRIER;
    let mut k = Kernel::new();
    let f = build(&mut k);
    let grp = k.const_(f.gs.grp, vec![]);
    let c = cat_of(&mut k, &f.recs.category_large, grp);

    let group_ty = k.const_(f.st.group.ind, vec![]);
    let monoid_ty = k.const_(f.st.monoid.ind, vec![]);
    assert!(k.def_eq(c.obj, group_ty), "grp.obj must be AlgS.Group");
    assert!(
        !k.def_eq(c.obj, monoid_ty),
        "grp.obj must NOT be AlgS.Monoid"
    );

    let g = k.fvar(98_000);
    let h = k.fvar(98_001);
    let hom = c.hom_ty(&mut k, g, h);
    let gc = sel(&mut k, &f.st.group, CARRIER, g);
    let hc = sel(&mut k, &f.st.group, CARRIER, h);
    let fn_ty = arrow(&mut k, gc, hc);
    let igh = k.const_(f.cs.is_grp_hom, vec![]);
    let pred = app2(&mut k, igh, g, h);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let bundled = sub_ty(&mut k, &f.lg, l1, fn_ty, pred);
    assert!(
        k.def_eq(hom, bundled),
        "grp.hom G H must be Subtype (G.carrier -> H.carrier) (IsGrpHom G H)"
    );
    assert!(
        !k.def_eq(hom, fn_ty),
        "grp.hom G H must NOT be the BARE function space -- that is the \
         hom-family ADR-1620 measured as making compCongr false"
    );
}

/// **The composition order is pinned.** `comp a b c g f` applies `f` first;
/// the swapped twin is refused. Both are well typed because every object is
/// the same group.
#[test]
fn the_group_composition_applies_the_inner_morphism_first() {
    use algs::group::CARRIER;
    let mut k = Kernel::new();
    let f = build(&mut k);
    let grp = k.const_(f.gs.grp, vec![]);
    let c = cat_of(&mut k, &f.recs.category_large, grp);
    let g = k.fvar(98_010);
    let gc = sel(&mut k, &f.st.group, CARRIER, g);
    let igh = k.const_(f.cs.is_grp_hom, vec![]);
    let pred = app2(&mut k, igh, g, g);
    let fn_ty = arrow(&mut k, gc, gc);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);

    let u = k.fvar(98_011);
    let v = k.fvar(98_012);
    let uf = sub_val(&mut k, &f.lg, l1, fn_ty, pred, u);
    let vf = sub_val(&mut k, &f.lg, l1, fn_ty, pred, v);
    let x = k.fvar(98_013);

    let cmp = c.cmp(&mut k, g, g, g, v, u);
    let cmpf = sub_val(&mut k, &f.lg, l1, fn_ty, pred, cmp);
    let got = k.app(cmpf, x);
    let ux = k.app(uf, x);
    let want = k.app(vf, ux);
    let vx = k.app(vf, x);
    let swapped = k.app(uf, vx);
    assert!(k.def_eq(got, want), "comp v u applies u first");
    assert!(
        !k.def_eq(got, swapped),
        "comp v u must NOT apply v first -- the order is what makes the \
         functor laws hold"
    );

    // The identity's underlying function is the identity function.
    let ident = c.ident(&mut k, g);
    let identf = sub_val(&mut k, &f.lg, l1, fn_ty, pred, ident);
    let id_x = k.app(identf, x);
    assert!(k.def_eq(id_x, x), "grp.id's function must be fun a => a");
    let ux2 = k.app(uf, x);
    assert!(
        !k.def_eq(id_x, ux2),
        "grp.id's function must NOT be an arbitrary morphism"
    );
}

/// **`AlgS.Group.toMonoidS` is free**: every monoid field reduces to the
/// group's own selector. It is NOT a prefix projection -- monoid field 8 is
/// `assoc` and group field 8 is `inv` -- so the reordering is what this test
/// pins.
#[test]
fn the_forgetful_projection_is_the_group_s_own_fields() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let to_mon = k.const_(f.gs.to_monoid_s, vec![]);
    let g = k.fvar(98_020);
    let h = k.fvar(98_021);
    let mg = k.app(to_mon, g);
    let mh = k.app(to_mon, h);

    let pairs: [(usize, usize, &str); 8] = [
        (algs::monoid::CARRIER, algs::group::CARRIER, "carrier"),
        (algs::monoid::EQUIV, algs::group::EQUIV, "equiv"),
        (algs::monoid::EQUIV_REFL, algs::group::EQUIV_REFL, "refl"),
        (algs::monoid::EQUIV_SYMM, algs::group::EQUIV_SYMM, "symm"),
        (algs::monoid::EQUIV_TRANS, algs::group::EQUIV_TRANS, "trans"),
        (algs::monoid::OP, algs::group::OP, "op"),
        (algs::monoid::OP_CONGR, algs::group::OP_CONGR, "opCongr"),
        (algs::monoid::E, algs::group::E, "e"),
    ];
    for (mi, gi, what) in pairs {
        let got = sel(&mut k, &f.st.monoid, mi, mg);
        let want = sel(&mut k, &f.st.group, gi, g);
        assert!(
            k.def_eq(got, want),
            "(toMonoidS G).{what} must reduce to G.{what}"
        );
        let other = sel(&mut k, &f.st.monoid, mi, mh);
        assert!(
            !k.def_eq(got, other),
            "(toMonoidS G).{what} must NOT reduce to a DIFFERENT group's {what}"
        );
    }
    // The three reordered law fields: monoid 8/9/10 are group 10/11/12.
    for (mi, gi, what) in [
        (algs::monoid::ASSOC, algs::group::ASSOC, "assoc"),
        (algs::monoid::IDENT_L, algs::group::IDENT_L, "identL"),
        (algs::monoid::IDENT_R, algs::group::IDENT_R, "identR"),
    ] {
        let got = sel(&mut k, &f.st.monoid, mi, mg);
        let want = sel(&mut k, &f.st.group, gi, g);
        assert!(
            k.def_eq(got, want),
            "(toMonoidS G).{what} must reduce to G.{what} -- the field \
             INDEX moves ({mi} vs {gi}), the statement does not"
        );
    }
}

/// The forgetful functor's three components, read from the record.
#[test]
fn the_forgetful_functor_names_its_two_categories() {
    use algs::group::CARRIER;
    use idx::functor::{MAP, OBJ as F_OBJ, SRC, TGT};
    let mut k = Kernel::new();
    let f = build(&mut k);
    let fl = f.grp_recs.functor_large;
    let fg = k.const_(f.gs.forget_grp_mon, vec![]);
    let src = sel(&mut k, &fl, SRC, fg);
    let tgt = sel(&mut k, &fl, TGT, fg);
    let fo = sel(&mut k, &fl, F_OBJ, fg);

    let grp = k.const_(f.gs.grp, vec![]);
    let mon = k.const_(f.gs.mon, vec![]);
    let to_mon = k.const_(f.gs.to_monoid_s, vec![]);
    assert!(k.def_eq(src, grp), "forgetGrpMon.src must be CatS.grp");
    assert!(!k.def_eq(src, mon), "forgetGrpMon.src must NOT be CatS.mon");
    assert!(k.def_eq(tgt, mon), "forgetGrpMon.tgt must be CatS.mon");
    assert!(!k.def_eq(tgt, grp), "forgetGrpMon.tgt must NOT be CatS.grp");
    assert!(
        k.def_eq(fo, to_mon),
        "forgetGrpMon.obj must be AlgS.Group.toMonoidS"
    );

    // The morphism map keeps the underlying function -- that is why the three
    // functor laws are reflexivity.
    let g = k.fvar(98_030);
    let h = k.fvar(98_031);
    let gc = sel(&mut k, &f.st.group, CARRIER, g);
    let hc = sel(&mut k, &f.st.group, CARRIER, h);
    let fn_ty = arrow(&mut k, gc, hc);
    let igh = k.const_(f.cs.is_grp_hom, vec![]);
    let pred = app2(&mut k, igh, g, h);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let u = k.fvar(98_032);
    let uf = sub_val(&mut k, &f.lg, l1, fn_ty, pred, u);

    let fm = sel(&mut k, &fl, MAP, fg);
    let mapped = t_app(&mut k, fm, &[g, h, u]);
    let mg = k.app(to_mon, g);
    let mh = k.app(to_mon, h);
    let imh = k.const_(f.gs.is_mon_hom, vec![]);
    let mpred = app2(&mut k, imh, mg, mh);
    let mapped_f = sub_val(&mut k, &f.lg, l1, fn_ty, mpred, mapped);
    let x = k.fvar(98_033);
    let got = k.app(mapped_f, x);
    let want = k.app(uf, x);
    assert!(
        k.def_eq(got, want),
        "the forgotten morphism's function is the SAME function"
    );
    let idx_ = x;
    assert!(
        !k.def_eq(got, idx_),
        "it must NOT collapse to the identity function"
    );
}

/// **A monoid morphism carries a third conjunct a group morphism does not.**
/// `IsMonHom` unfolds to `congr ∧ (op ∧ unit)`; without the unit conjunct it
/// would be a semigroup morphism, and the test refuses that shape.
#[test]
fn a_monoid_morphism_preserves_the_unit() {
    use algs::monoid::{CARRIER, E, EQUIV, OP};
    let mut k = Kernel::new();
    let f = build(&mut k);
    let m = k.fvar(98_040);
    let n = k.fvar(98_041);
    let mc = sel(&mut k, &f.st.monoid, CARRIER, m);
    let nc = sel(&mut k, &f.st.monoid, CARRIER, n);
    let m_eq = sel(&mut k, &f.st.monoid, EQUIV, m);
    let n_eq = sel(&mut k, &f.st.monoid, EQUIV, n);
    let m_op = sel(&mut k, &f.st.monoid, OP, m);
    let n_op = sel(&mut k, &f.st.monoid, OP, n);
    let m_e = sel(&mut k, &f.st.monoid, E, m);
    let n_e = sel(&mut k, &f.st.monoid, E, n);
    let fn_ = k.fvar(98_042);

    let congr_p = {
        let a = k.fvar(98_043);
        let b = k.fvar(98_044);
        let hyp = app2(&mut k, m_eq, a, b);
        let fa = k.app(fn_, a);
        let fb = k.app(fn_, b);
        let concl = app2(&mut k, n_eq, fa, fb);
        let t = arrow(&mut k, hyp, concl);
        let t = pi_over(&mut k, 98_044, mc, t);
        pi_over(&mut k, 98_043, mc, t)
    };
    let op_p = {
        let a = k.fvar(98_043);
        let b = k.fvar(98_044);
        let ab = app2(&mut k, m_op, a, b);
        let lhs = k.app(fn_, ab);
        let fa = k.app(fn_, a);
        let fb = k.app(fn_, b);
        let rhs = app2(&mut k, n_op, fa, fb);
        let body = app2(&mut k, n_eq, lhs, rhs);
        let t = pi_over(&mut k, 98_044, mc, body);
        pi_over(&mut k, 98_043, mc, t)
    };
    let unit_p = {
        let fe = k.app(fn_, m_e);
        app2(&mut k, n_eq, fe, n_e)
    };

    let and_c = k.const_(f.lg.and, vec![]);
    let tail = app2(&mut k, and_c, op_p, unit_p);
    let and_c2 = k.const_(f.lg.and, vec![]);
    let want = app2(&mut k, and_c2, congr_p, tail);
    let and_c3 = k.const_(f.lg.and, vec![]);
    let semigroup_only = app2(&mut k, and_c3, congr_p, op_p);

    let imh = k.const_(f.gs.is_mon_hom, vec![]);
    let got = t_app(&mut k, imh, &[m, n, fn_]);
    assert!(
        k.def_eq(got, want),
        "IsMonHom must unfold to congr AND (op AND unit)"
    );
    assert!(
        !k.def_eq(got, semigroup_only),
        "IsMonHom must NOT drop the unit conjunct -- that is a SEMIGROUP \
         morphism, and it is the one thing AlgS.Hom.mapOne is needed for"
    );
    let _ = nc;
}

/// **The object of a pointed unary algebra is a triple**, and at
/// `CatS.natPtAlg` its three components reduce to `Nat`, `Nat.zero` and
/// `Nat.succ`.
#[test]
fn the_nat_pointed_algebra_projects_to_nat_zero_succ() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let ctx = pt_ctx(&mut k, &f.lg, &f.gs);
    let npa = k.const_(f.gs.nat_pt_alg, vec![]);

    let nat = k.const_(f.lg.nat, vec![]);
    let z = k.const_(f.lg.nat_zero, vec![]);
    let s = k.const_(f.lg.nat_succ, vec![]);

    let c = ctx.carrier_of(&mut k, npa);
    assert!(k.def_eq(c, nat), "carrier natPtAlg must reduce to Nat");
    let l0 = k.level_zero();
    let prop = k.sort(l0);
    assert!(
        !k.def_eq(c, prop),
        "carrier natPtAlg must NOT reduce to Prop"
    );

    let zero = ctx.zero_of(&mut k, npa);
    assert!(k.def_eq(zero, z), "zero natPtAlg must reduce to Nat.zero");
    let one = k.app(s, z);
    assert!(
        !k.def_eq(zero, one),
        "zero natPtAlg must NOT reduce to Nat.succ Nat.zero"
    );

    let succ = ctx.succ_of(&mut k, npa, z);
    assert!(
        k.def_eq(succ, one),
        "succ natPtAlg Nat.zero must reduce to Nat.succ Nat.zero"
    );
    assert!(
        !k.def_eq(succ, z),
        "succ natPtAlg Nat.zero must NOT reduce to Nat.zero"
    );

    // The whole object type is the nested `Sigma`, not the carrier alone.
    let pt_body = sig_ty(
        &mut k,
        &f.lg,
        ctx.l1,
        ctx.l0,
        ctx.outer_alpha,
        ctx.outer_beta,
    );
    let pt = k.const_(f.gs.pt_alg, vec![]);
    assert!(
        k.def_eq(pt, pt_body),
        "PtAlg must unfold to the nested Sigma"
    );
    let sort1 = k.sort(ctx.l1);
    assert!(
        !k.def_eq(pt, sort1),
        "PtAlg must NOT collapse to its first component's type"
    );
}

/// **The mediating map computes.** `CatS.natMed` at the algebra
/// `(Nat, zero, succ)` is the identity on numerals, so `med 2` reduces to
/// `2` -- a discriminating value with a small magnitude.
#[test]
fn the_mediating_map_out_of_nat_computes() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let ctx = pt_ctx(&mut k, &f.lg, &f.gs);
    let ops = PtHomOps {
        is_pt_hom: f.gs.is_pt_hom,
    };
    let npa = k.const_(f.gs.nat_pt_alg, vec![]);
    let med = k.const_(f.gs.nat_med, vec![]);
    let med_q = k.app(med, npa);
    let medf = ops.val(&mut k, &f.lg, &ctx, npa, npa, med_q);

    let z = k.const_(f.lg.nat_zero, vec![]);
    let s = k.const_(f.lg.nat_succ, vec![]);
    let one = k.app(s, z);
    let two = k.app(s, one);

    let got0 = k.app(medf, z);
    assert!(k.def_eq(got0, z), "med 0 must reduce to 0");
    assert!(!k.def_eq(got0, one), "med 0 must NOT reduce to 1");

    let got2 = k.app(medf, two);
    assert!(k.def_eq(got2, two), "med 2 must reduce to 2");
    assert!(!k.def_eq(got2, one), "med 2 must NOT reduce to 1");
}

// ---------------------------------------------------------------------------
// The mutation table. Each entry changes ONE small term and requires the
// trusted gate to REFUSE it, with the positive twin admitted in the same test.
// ---------------------------------------------------------------------------

/// **N1** -- `CatS.grp`'s `compCongr` concludes about `comp v' u'`. Naming
/// `comp v u'` instead (one selector argument) must be refused.
#[test]
fn n1_the_congruence_concludes_about_both_replaced_morphisms() {
    use algs::group::CARRIER;
    use idx::COMP_CONGR;
    let mut k = Kernel::new();
    let f = build(&mut k);
    let anon = k.anon();
    let grp = k.const_(f.gs.grp, vec![]);
    let c = cat_of(&mut k, &f.recs.category_large, grp);
    let cc = sel(&mut k, &f.recs.category_large, COMP_CONGR, grp);

    let g = k.fvar(97_100);
    let g_ty = k.const_(f.st.group.ind, vec![]);
    let gc = sel(&mut k, &f.st.group, CARRIER, g);
    let _ = gc;
    let hom = c.hom_ty(&mut k, g, g);
    let v = k.fvar(97_101);
    let v2 = k.fvar(97_102);
    let u = k.fvar(97_103);
    let u2 = k.fvar(97_104);
    let hv_ty = c.eqv(&mut k, g, g, v, v2);
    let hu_ty = c.eqv(&mut k, g, g, u, u2);
    let hv = k.fvar(97_105);
    let hu = k.fvar(97_106);
    let proof = t_app(&mut k, cc, &[g, g, g, v, v2, u, u2, hv, hu]);

    let lhs = c.cmp(&mut k, g, g, g, v, u);
    let good_rhs = c.cmp(&mut k, g, g, g, v2, u2);
    let bad_rhs = c.cmp(&mut k, g, g, g, v, u2);
    let good_stmt = c.eqv(&mut k, g, g, lhs, good_rhs);
    let bad_stmt = c.eqv(&mut k, g, g, lhs, bad_rhs);

    let close_ty = |k: &mut Kernel, e: ExprId| -> ExprId {
        let t = pi_over(k, 97_106, hu_ty, e);
        let t = pi_over(k, 97_105, hv_ty, t);
        let t = pi_over(k, 97_104, hom, t);
        let t = pi_over(k, 97_103, hom, t);
        let t = pi_over(k, 97_102, hom, t);
        let t = pi_over(k, 97_101, hom, t);
        pi_over(k, 97_100, g_ty, t)
    };
    let close_val = |k: &mut Kernel, e: ExprId| -> ExprId {
        let t = lam_over(k, 97_106, hu_ty, e);
        let t = lam_over(k, 97_105, hv_ty, t);
        let t = lam_over(k, 97_104, hom, t);
        let t = lam_over(k, 97_103, hom, t);
        let t = lam_over(k, 97_102, hom, t);
        let t = lam_over(k, 97_101, hom, t);
        lam_over(k, 97_100, g_ty, t)
    };

    let good_ty = close_ty(&mut k, good_stmt);
    let good_val = close_val(&mut k, proof);
    let good = k.name_str(anon, "n1Positive");
    k.add_declaration(Declaration::Theorem {
        name: good,
        uparams: vec![],
        ty: good_ty,
        value: good_val,
    })
    .expect("compCongr DOES conclude about comp v' u'");

    let bad_ty = close_ty(&mut k, bad_stmt);
    let bad_val = close_val(&mut k, proof);
    let bad = k.name_str(anon, "n1Negative");
    let err = k
        .add_declaration(Declaration::Theorem {
            name: bad,
            uparams: vec![],
            ty: bad_ty,
            value: bad_val,
        })
        .expect_err("compCongr must NOT conclude about comp v u'");
    println!("n1 rejection: {err:?}");
}

/// **N2** -- `CatS.isMonHom_comp` proves the composite `fun a => g (f a)`.
/// The swapped composite (one application order) must be refused.
#[test]
fn n2_the_composite_monoid_hom_is_ordered() {
    use algs::monoid::CARRIER;
    let mut k = Kernel::new();
    let f = build(&mut k);
    let anon = k.anon();
    let m_ty = k.const_(f.st.monoid.ind, vec![]);
    let m = k.fvar(97_200);
    let mc = sel(&mut k, &f.st.monoid, CARRIER, m);
    let fn_ty = arrow(&mut k, mc, mc);
    let f1 = k.fvar(97_201);
    let f2 = k.fvar(97_202);
    let imh = k.const_(f.gs.is_mon_hom, vec![]);
    let h1_ty = t_app(&mut k, imh, &[m, m, f1]);
    let imh2 = k.const_(f.gs.is_mon_hom, vec![]);
    let h2_ty = t_app(&mut k, imh2, &[m, m, f2]);
    let hh1 = k.fvar(97_203);
    let hh2 = k.fvar(97_204);

    let good_comp = {
        let x = k.fvar(97_210);
        let inner = k.app(f1, x);
        let body = k.app(f2, inner);
        lam_over(&mut k, 97_210, mc, body)
    };
    let bad_comp = {
        let x = k.fvar(97_210);
        let inner = k.app(f2, x);
        let body = k.app(f1, inner);
        lam_over(&mut k, 97_210, mc, body)
    };
    let imhc = k.const_(f.gs.is_mon_hom_comp, vec![]);
    let proof = t_app(&mut k, imhc, &[m, m, m, f1, f2, hh1, hh2]);

    let close_ty = |k: &mut Kernel, e: ExprId| -> ExprId {
        let t = pi_over(k, 97_204, h2_ty, e);
        let t = pi_over(k, 97_203, h1_ty, t);
        let t = pi_over(k, 97_202, fn_ty, t);
        let t = pi_over(k, 97_201, fn_ty, t);
        pi_over(k, 97_200, m_ty, t)
    };
    let close_val = |k: &mut Kernel, e: ExprId| -> ExprId {
        let t = lam_over(k, 97_204, h2_ty, e);
        let t = lam_over(k, 97_203, h1_ty, t);
        let t = lam_over(k, 97_202, fn_ty, t);
        let t = lam_over(k, 97_201, fn_ty, t);
        lam_over(k, 97_200, m_ty, t)
    };

    let imh3 = k.const_(f.gs.is_mon_hom, vec![]);
    let good_stmt = t_app(&mut k, imh3, &[m, m, good_comp]);
    let good_ty = close_ty(&mut k, good_stmt);
    let good_val = close_val(&mut k, proof);
    let good = k.name_str(anon, "n2Positive");
    k.add_declaration(Declaration::Theorem {
        name: good,
        uparams: vec![],
        ty: good_ty,
        value: good_val,
    })
    .expect("f2 . f1 IS a monoid homomorphism when both are");

    let imh4 = k.const_(f.gs.is_mon_hom, vec![]);
    let bad_stmt = t_app(&mut k, imh4, &[m, m, bad_comp]);
    let bad_ty = close_ty(&mut k, bad_stmt);
    let bad_val = close_val(&mut k, proof);
    let bad = k.name_str(anon, "n2Negative");
    let err = k
        .add_declaration(Declaration::Theorem {
            name: bad,
            uparams: vec![],
            ty: bad_ty,
            value: bad_val,
        })
        .expect_err("the SWAPPED composite is not what isMonHom_comp proves");
    println!("n2 rejection: {err:?}");
}

/// **N3** -- `CatS.natMed`'s zero equation holds by ι-reduction, so `Eq.refl`
/// proves it. Shifting the right-hand side by one `succ` must be refused.
#[test]
fn n3_the_mediating_map_hits_the_base_point() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let anon = k.anon();
    let ctx = pt_ctx(&mut k, &f.lg, &f.gs);
    let ops = PtHomOps {
        is_pt_hom: f.gs.is_pt_hom,
    };
    let npa = k.const_(f.gs.nat_pt_alg, vec![]);
    let med = k.const_(f.gs.nat_med, vec![]);
    let q = k.fvar(97_300);
    let cq = ctx.carrier_of(&mut k, q);
    let med_q = k.app(med, q);
    let medf = ops.val(&mut k, &f.lg, &ctx, npa, q, med_q);
    let z = k.const_(f.lg.nat_zero, vec![]);
    let lhs = k.app(medf, z);
    let zq = ctx.zero_of(&mut k, q);
    let good_stmt = eq_of(&mut k, &f.lg, ctx.l1, cq, lhs, zq);
    let shifted = ctx.succ_of(&mut k, q, zq);
    let bad_stmt = eq_of(&mut k, &f.lg, ctx.l1, cq, lhs, shifted);
    let proof = refl_of(&mut k, &f.lg, ctx.l1, cq, zq);

    let good_ty = pi_over(&mut k, 97_300, ctx.pt, good_stmt);
    let good_val = lam_over(&mut k, 97_300, ctx.pt, proof);
    let good = k.name_str(anon, "n3Positive");
    k.add_declaration(Declaration::Theorem {
        name: good,
        uparams: vec![],
        ty: good_ty,
        value: good_val,
    })
    .expect("med 0 IS the base point, by iota-reduction");

    let bad_ty = pi_over(&mut k, 97_300, ctx.pt, bad_stmt);
    let bad_val = lam_over(&mut k, 97_300, ctx.pt, proof);
    let bad = k.name_str(anon, "n3Negative");
    let err = k
        .add_declaration(Declaration::Theorem {
            name: bad,
            uparams: vec![],
            ty: bad_ty,
            value: bad_val,
        })
        .expect_err("med 0 must NOT be the base point's successor");
    println!("n3 rejection: {err:?}");
}

/// **N4** -- `CatS.natPtAlg_isInitial` says every structure-preserving map out
/// of ℕ EQUALS the mediating one. Shifting one side by a `succ` must be
/// refused.
#[test]
fn n4_initiality_is_equality_not_a_shift() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let anon = k.anon();
    let ctx = pt_ctx(&mut k, &f.lg, &f.gs);
    let ops = PtHomOps {
        is_pt_hom: f.gs.is_pt_hom,
    };
    let npa = k.const_(f.gs.nat_pt_alg, vec![]);
    let med = k.const_(f.gs.nat_med, vec![]);
    let init = k.const_(f.gs.nat_pt_alg_is_initial, vec![]);
    let nat = k.const_(f.lg.nat, vec![]);

    let q = k.fvar(97_400);
    let cq = ctx.carrier_of(&mut k, q);
    let pt_hom = k.const_(f.gs.pt_hom, vec![]);
    let g_ty = app2(&mut k, pt_hom, npa, q);
    let g = k.fvar(97_401);
    let gf = ops.val(&mut k, &f.lg, &ctx, npa, q, g);
    let med_q = k.app(med, q);
    let medf = ops.val(&mut k, &f.lg, &ctx, npa, q, med_q);

    let n = k.fvar(97_402);
    let mn = k.app(medf, n);
    let gn = k.app(gf, n);
    let good_body = eq_of(&mut k, &f.lg, ctx.l1, cq, mn, gn);
    let shifted = ctx.succ_of(&mut k, q, gn);
    let bad_body = eq_of(&mut k, &f.lg, ctx.l1, cq, mn, shifted);
    let proof = t_app(&mut k, init, &[q, g, n]);

    let close_ty = |k: &mut Kernel, e: ExprId| -> ExprId {
        let t = pi_over(k, 97_402, nat, e);
        let t = pi_over(k, 97_401, g_ty, t);
        pi_over(k, 97_400, ctx.pt, t)
    };
    let close_val = |k: &mut Kernel, e: ExprId| -> ExprId {
        let t = lam_over(k, 97_402, nat, e);
        let t = lam_over(k, 97_401, g_ty, t);
        lam_over(k, 97_400, ctx.pt, t)
    };

    let good_ty = close_ty(&mut k, good_body);
    let good_val = close_val(&mut k, proof);
    let good = k.name_str(anon, "n4Positive");
    k.add_declaration(Declaration::Theorem {
        name: good,
        uparams: vec![],
        ty: good_ty,
        value: good_val,
    })
    .expect("initiality gives med n = g n at every n");

    let bad_ty = close_ty(&mut k, bad_body);
    let bad_val = close_val(&mut k, proof);
    let bad = k.name_str(anon, "n4Negative");
    let err = k
        .add_declaration(Declaration::Theorem {
            name: bad,
            uparams: vec![],
            ty: bad_ty,
            value: bad_val,
        })
        .expect_err("initiality must NOT give med n = succ (g n)");
    println!("n4 rejection: {err:?}");
}

/// **The universe guard, measured on the fourth record.** `CatS.FunctorLarge`
/// holds two `CatS.CategoryLarge` fields, whose type lives at level 3, so the
/// same seven-field list at `Sort 2` is refused by ADR-1495's
/// `ConstructorFieldUniverseTooBig` on field 0 — and the positive twin at
/// `Sort 3` admits. This is ADR-1620's measurement 2a ("a record CAN hold a
/// record") one level up, and it is the ONLY guard interaction in this layer:
/// nothing here was blocked by it.
#[test]
fn the_functor_large_record_is_forced_up_to_sort_3() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let l2 = k.level_succ(l1);
    let l3 = k.level_succ(l2);
    let anon = k.anon();

    let specs = functor_fields(f.recs.category_large);
    let mut ctor_fields: Vec<(u64, ExprId)> = Vec::new();
    let mut vals: Vec<ExprId> = Vec::new();
    for (i, spec) in specs.iter().enumerate() {
        let ty = (spec.build)(&mut k, &f.lg, l2, &vals);
        let fv = 10_000 + i as u64;
        ctor_fields.push((fv, ty));
        let v = k.fvar(fv);
        vals.push(v);
    }

    let bad = k.name_str(anon, "FunctorLargeSort2Control");
    let bad_mk = k.name_str(bad, "mk");
    let bad_const = k.const_(bad, vec![]);
    let bad_ctor = crate::nat_prelude::structures::close_pi(&mut k, &ctor_fields, bad_const);
    let sort2 = k.sort(l2);
    let err = k
        .add_inductive(bad, &[], 0, sort2, &[(bad_mk, bad_ctor)])
        .expect_err("a Sort-2 FunctorLarge record must be REFUSED");
    println!("FunctorLarge rejection at Sort 2: {err:?}");
    assert!(
        matches!(
            err,
            KernelError::ConstructorFieldUniverseTooBig { field_index: 0, .. }
        ),
        "expected ConstructorFieldUniverseTooBig on field 0, got {err:?}"
    );

    let good = k.name_str(anon, "FunctorLargeSort3Control");
    let good_mk = k.name_str(good, "mk");
    let good_const = k.const_(good, vec![]);
    let good_ctor = crate::nat_prelude::structures::close_pi(&mut k, &ctor_fields, good_const);
    let sort3 = k.sort(l3);
    k.add_inductive(good, &[], 0, sort3, &[(good_mk, good_ctor)])
        .expect("the same seven fields at Sort 3 must ADMIT");
}
