//! Tests for the product/coproduct layer (ADR-1632). Every assertion reads the
//! KERNEL: admission, `Kernel::axiom_footprint`, the `Declaration` kind, the
//! rendered type, `def_eq` in BOTH directions, and — for `CatS.grpProd` — an
//! evaluation at a CONCRETE pair of groups whose two `op`s, two `e`s and two
//! `inv`s differ, so a swapped projection is a failing test and not a passing
//! one.

use super::*;
use crate::build_logic_prelude;
use crate::nat_prelude::structures as algeq;
use crate::nat_prelude::structures::eq_of;
use crate::nat_prelude::structures_setoid::{
    StructuresSRecordNames, declare_structures_s_all, declare_structures_s_extra,
    intern_structures_s_names,
};

struct Fixture {
    lg: LogicPrelude,
    st: StructuresSRecordNames,
    recs: CategoryRecords,
    cs: CategoryNames,
    gs: GroupCatNames,
    ps: ProductNames,
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
    let (recs, cs, _grp_recs, gs, ps) =
        super::super::declare_category_setoid(k, &lg, &st.monoid, &st.group, deps)
            .expect("the product layer must admit");
    Fixture {
        lg,
        st,
        recs,
        cs,
        gs,
        ps,
    }
}

fn decl_ty(k: &Kernel, name: NameId) -> ExprId {
    match k.environment().get(name).expect("declaration exists") {
        Declaration::Definition { ty, .. } | Declaration::Theorem { ty, .. } => *ty,
        other => panic!("unexpected declaration kind: {other:?}"),
    }
}

/// A unary `Nat` numeral. Kept SMALL everywhere below: this kernel has no
/// binary literal fast path in the prelude, so cost is superlinear in the
/// largest magnitude formed.
fn num(k: &mut Kernel, lg: &LogicPrelude, n: u32) -> ExprId {
    let mut e = k.const_(lg.nat_zero, vec![]);
    let succ = k.const_(lg.nat_succ, vec![]);
    for _ in 0..n {
        e = k.app(succ, e);
    }
    e
}

/// A CONCRETE `AlgS.Group` on `Nat` whose `equiv` is the total relation
/// `fun _ _ => True`. Every law field is `True.intro`, so the *operations*
/// are unconstrained — which is exactly what makes it a discriminating test
/// fixture: `op`, `e` and `inv` can be chosen to differ between the two
/// factors, and a product that swapped its components would compute a
/// different value.
///
/// `which = 0` gives `op a b = a`, `e = 0`, `inv a = a`;
/// `which = 1` gives `op a b = b`, `e = 1`, `inv a = succ a`.
fn chaotic_group(k: &mut Kernel, lg: &LogicPrelude, rec: &RecordNames, which: u32) -> ExprId {
    let nat = k.const_(lg.nat, vec![]);
    let true_c = k.const_(lg.true_, vec![]);
    let ti = k.const_(lg.true_intro, vec![]);

    let a_fv = 97_000;
    let b_fv = 97_001;
    let c_fv = 97_002;
    let d_fv = 97_003;
    let h1_fv = 97_010;
    let h2_fv = 97_011;

    let equiv = {
        let t = lam_over(k, b_fv, nat, true_c);
        lam_over(k, a_fv, nat, t)
    };
    let triv = |k: &mut Kernel, binders: &[(u64, ExprId)]| -> ExprId {
        let mut e = ti;
        for (fv, ty) in binders.iter().rev() {
            e = lam_over(k, *fv, *ty, e);
        }
        e
    };
    let refl = triv(k, &[(a_fv, nat)]);
    let symm = triv(k, &[(a_fv, nat), (b_fv, nat), (h1_fv, true_c)]);
    let trans = triv(
        k,
        &[
            (a_fv, nat),
            (b_fv, nat),
            (c_fv, nat),
            (h1_fv, true_c),
            (h2_fv, true_c),
        ],
    );
    let op = {
        let a = k.fvar(a_fv);
        let b = k.fvar(b_fv);
        let body = if which == 0 { a } else { b };
        let t = lam_over(k, b_fv, nat, body);
        lam_over(k, a_fv, nat, t)
    };
    let op_congr = triv(
        k,
        &[
            (a_fv, nat),
            (b_fv, nat),
            (c_fv, nat),
            (d_fv, nat),
            (h1_fv, true_c),
            (h2_fv, true_c),
        ],
    );
    let e = num(k, lg, which);
    let inv = {
        let a = k.fvar(a_fv);
        let body = if which == 0 {
            a
        } else {
            let succ = k.const_(lg.nat_succ, vec![]);
            k.app(succ, a)
        };
        lam_over(k, a_fv, nat, body)
    };
    let inv_congr = triv(k, &[(a_fv, nat), (b_fv, nat), (h1_fv, true_c)]);
    let assoc = triv(k, &[(a_fv, nat), (b_fv, nat), (c_fv, nat)]);
    let one = triv(k, &[(a_fv, nat)]);
    let ident_l = one;
    let ident_r = triv(k, &[(a_fv, nat)]);
    let inv_l = triv(k, &[(a_fv, nat)]);
    let inv_r = triv(k, &[(a_fv, nat)]);

    mk_instance(
        k,
        rec,
        &[
            nat, equiv, refl, symm, trans, op, op_congr, e, inv, inv_congr, assoc, ident_l,
            ident_r, inv_l, inv_r,
        ],
    )
}

// ---------------------------------------------------------------------------
// Admission, footprint, kind.
// ---------------------------------------------------------------------------

#[test]
fn the_product_layer_admits_and_is_axiom_free() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let names = f.ps.all();
    assert_eq!(names.len(), 12, "twelve declarations");
    let mut seen = 0;
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
        seen += 1;
    }
    assert_eq!(seen, 12, "every declaration examined");
}

/// The four results must be **checked `Theorem`s**; the eight constructions
/// must be `Definition`s. Reading the kind from the environment is what
/// distinguishes "we proved it" from "we asserted it".
#[test]
fn the_results_are_checked_theorems_and_the_rest_are_definitions() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let mut n = 0;
    for name in f.ps.theorems() {
        let d = k.environment().get(name).expect("exists").clone();
        assert!(
            matches!(d, Declaration::Theorem { .. }),
            "{name:?} must be a checked Theorem, got {d:?}"
        );
        n += 1;
    }
    assert_eq!(n, 4, "four checked theorems");
    for name in [
        f.ps.is_product,
        f.ps.is_coproduct,
        f.ps.is_product_large,
        f.ps.iso,
        f.ps.grp_prod,
        f.ps.grp_prod_fst,
        f.ps.grp_prod_snd,
        f.ps.grp_prod_med,
    ] {
        let d = k.environment().get(name).expect("exists").clone();
        assert!(
            matches!(d, Declaration::Definition { .. }),
            "{name:?} must be a Definition"
        );
    }
}

/// Prints every rendered type so a referee reads the statements out of the
/// suite rather than out of a doc comment.
#[test]
fn the_product_types_render() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for name in f.ps.all() {
        let ty = decl_ty(&k, name);
        println!("decl {name:?} :\n  {}\n", k.render_lean(ty));
    }
}

// ---------------------------------------------------------------------------
// What `CatS.IsProduct` says, read back from the kernel.
// ---------------------------------------------------------------------------

/// **`IsProduct` unfolds to the three conjuncts, and the third one is not
/// implied by the first two.** The positive twin pins the statement; the two
/// negative twins pin that the two-conjunct and the uniqueness-only forms are
/// DIFFERENT propositions, which is the whole reason the definition has three
/// legs.
#[test]
fn is_product_is_two_triangles_and_uniqueness() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let cat = f.recs.category;
    let cv = k.fvar(96_000);
    let c = cat_of(&mut k, &cat, cv);
    let a = k.fvar(96_001);
    let b = k.fvar(96_002);
    let p = k.fvar(96_003);
    let pr1 = k.fvar(96_004);
    let pr2 = k.fvar(96_005);
    let med = k.fvar(96_006);

    let isp = k.const_(f.ps.is_product, vec![]);
    let got = t_app(&mut k, isp, &[cv, a, b, p, pr1, pr2, med]);
    let props = product_conjuncts(&mut k, &c, false, a, b, p, pr1, pr2, med);
    let want = and3(&mut k, &f.lg, &props);
    assert!(
        k.def_eq(got, want),
        "IsProduct must unfold to triangle ∧ (triangle ∧ uniqueness)"
    );

    // Negative twin 1: the two triangles alone.
    let and_c = k.const_(f.lg.and, vec![]);
    let triangles = app2(&mut k, and_c, props[0], props[1]);
    assert!(
        !k.def_eq(got, triangles),
        "IsProduct must NOT be the two triangles alone -- dropping uniqueness \
         makes every object with a pair of maps a 'product'"
    );

    // Negative twin 2: the SWAPPED pair of triangles, which is what a
    // projection swap in the factorisation proof would need.
    let swapped = product_conjuncts(&mut k, &c, false, a, b, p, pr2, pr1, med);
    let swapped_all = and3(&mut k, &f.lg, &swapped);
    assert!(
        !k.def_eq(got, swapped_all),
        "IsProduct with the two projections swapped must be a DIFFERENT \
         proposition"
    );
}

/// **`IsCoproduct` is the dual, not a copy.** Each composite is written on the
/// other side, so the two are not `def_eq` even at the same arguments — which
/// is only expressible because both are stated over the same category record.
#[test]
fn is_coproduct_composes_on_the_other_side() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let cat = f.recs.category;
    let cv = k.fvar(96_010);
    let c = cat_of(&mut k, &cat, cv);
    let a = k.fvar(96_011);
    let b = k.fvar(96_012);
    let s = k.fvar(96_013);
    let i1 = k.fvar(96_014);
    let i2 = k.fvar(96_015);
    let med = k.fvar(96_016);

    let isc = k.const_(f.ps.is_coproduct, vec![]);
    let got = t_app(&mut k, isc, &[cv, a, b, s, i1, i2, med]);
    let props = product_conjuncts(&mut k, &c, true, a, b, s, i1, i2, med);
    let want = and3(&mut k, &f.lg, &props);
    assert!(
        k.def_eq(got, want),
        "IsCoproduct must unfold to its dual form"
    );

    let prod_props = product_conjuncts(&mut k, &c, false, a, b, s, i1, i2, med);
    let prod = and3(&mut k, &f.lg, &prod_props);
    assert!(
        !k.def_eq(got, prod),
        "IsCoproduct must NOT be IsProduct -- the composites are on opposite \
         sides"
    );
}

/// `CatS.Iso` is the two round trips, and it is NOT the one-sided statement.
#[test]
fn iso_is_both_round_trips() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let cat = f.recs.category;
    let cv = k.fvar(96_020);
    let c = cat_of(&mut k, &cat, cv);
    let a = k.fvar(96_021);
    let b = k.fvar(96_022);
    let u = k.fvar(96_023);
    let v = k.fvar(96_024);

    let isoc = k.const_(f.ps.iso, vec![]);
    let got = t_app(&mut k, isoc, &[cv, a, b, u, v]);

    let uv = c.cmp(&mut k, b, a, b, u, v);
    let vu = c.cmp(&mut k, a, b, a, v, u);
    let ib = c.ident(&mut k, b);
    let ia = c.ident(&mut k, a);
    let p1 = c.eqv(&mut k, b, b, uv, ib);
    let p2 = c.eqv(&mut k, a, a, vu, ia);
    let and_c = k.const_(f.lg.and, vec![]);
    let want = app2(&mut k, and_c, p1, p2);
    assert!(k.def_eq(got, want), "Iso must be both round trips");
    assert!(
        !k.def_eq(got, p1),
        "Iso must NOT be the single round trip -- a split epi is not an iso"
    );
}

// ---------------------------------------------------------------------------
// `CatS.grpProd` — evaluated at CONCRETE, DISCRIMINATING, SMALL arguments.
// ---------------------------------------------------------------------------

/// **The product group computes componentwise, and its two components do not
/// commute.** The fixture's two factors have `op a b = a` / `op a b = b`,
/// `e = 0` / `e = 1`, `inv a = a` / `inv a = a+1`, so every assertion below
/// has a negative twin that differs by a SWAP.
#[test]
fn the_product_group_computes_componentwise() {
    use algs::group::{CARRIER, E, INV, OP};
    let mut k = Kernel::new();
    let f = build(&mut k);
    let rec = f.st.group;
    let gv = chaotic_group(&mut k, &f.lg, &rec, 0);
    let hv = chaotic_group(&mut k, &f.lg, &rec, 1);
    let gpc = k.const_(f.ps.grp_prod, vec![]);
    let pv = app2(&mut k, gpc, gv, hv);

    let nat = k.const_(f.lg.nat, vec![]);
    let pr = Pair { ca: nat, cb: nat };

    // carrier = Sigma Nat (fun _ => Nat), and NOT Nat.
    let carrier = sel(&mut k, &rec, CARRIER, pv);
    let want_carrier = pr.ty(&mut k, &f.lg);
    assert!(
        k.def_eq(carrier, want_carrier),
        "grpProd's carrier must be the Sigma pair"
    );
    assert!(
        !k.def_eq(carrier, nat),
        "grpProd's carrier must NOT be a single factor's carrier"
    );

    let n0 = num(&mut k, &f.lg, 0);
    let n1 = num(&mut k, &f.lg, 1);
    let n2 = num(&mut k, &f.lg, 2);
    let n3 = num(&mut k, &f.lg, 3);
    let n4 = num(&mut k, &f.lg, 4);

    // op (1,2) (3,4) = (G.op 1 3, H.op 2 4) = (1, 4).
    let p12 = pr.mk(&mut k, &f.lg, n1, n2);
    let p34 = pr.mk(&mut k, &f.lg, n3, n4);
    let op = sel(&mut k, &rec, OP, pv);
    let got = t_app(&mut k, op, &[p12, p34]);
    let want = pr.mk(&mut k, &f.lg, n1, n4);
    assert!(k.def_eq(got, want), "op (1,2) (3,4) must be (1,4)");
    for (x, y, why) in [
        (n3, n2, "components swapped"),
        (n1, n2, "second component taken from the wrong argument"),
        (n3, n4, "first component taken from the wrong argument"),
        (n4, n1, "both components swapped"),
    ] {
        let bad = pr.mk(&mut k, &f.lg, x, y);
        assert!(
            !k.def_eq(got, bad),
            "op (1,2) (3,4) must NOT be that value -- {why}"
        );
    }

    // e = (G.e, H.e) = (0, 1), and NOT (1, 0).
    let e = sel(&mut k, &rec, E, pv);
    let want_e = pr.mk(&mut k, &f.lg, n0, n1);
    let bad_e = pr.mk(&mut k, &f.lg, n1, n0);
    assert!(k.def_eq(e, want_e), "grpProd's unit must be (0,1)");
    assert!(
        !k.def_eq(e, bad_e),
        "grpProd's unit must NOT be (1,0) -- the factors are not symmetric"
    );

    // inv (1,2) = (G.inv 1, H.inv 2) = (1, 3), and NOT (2, 2) or (1, 2).
    let inv = sel(&mut k, &rec, INV, pv);
    let got_inv = k.app(inv, p12);
    let want_inv = pr.mk(&mut k, &f.lg, n1, n3);
    assert!(k.def_eq(got_inv, want_inv), "inv (1,2) must be (1,3)");
    for (x, y, why) in [
        (n2, n2, "inv applied to the wrong component"),
        (n1, n2, "inv not applied at all"),
        (n3, n1, "components swapped"),
    ] {
        let bad = pr.mk(&mut k, &f.lg, x, y);
        assert!(
            !k.def_eq(got_inv, bad),
            "inv (1,2) must NOT be that value -- {why}"
        );
    }
}

/// **The two projections read the two components, and neither reads the
/// other's.** This is the test a "swap the projections" mutant dies on.
#[test]
fn the_projections_read_their_own_component() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let rec = f.st.group;
    let gv = chaotic_group(&mut k, &f.lg, &rec, 0);
    let hv = chaotic_group(&mut k, &f.lg, &rec, 1);
    let gpc = k.const_(f.ps.grp_prod, vec![]);
    let pv = app2(&mut k, gpc, gv, hv);

    let nat = k.const_(f.lg.nat, vec![]);
    let pr = Pair { ca: nat, cb: nat };
    let n1 = num(&mut k, &f.lg, 1);
    let n2 = num(&mut k, &f.lg, 2);
    let p12 = pr.mk(&mut k, &f.lg, n1, n2);

    let carrier = {
        use algs::group::CARRIER;
        sel(&mut k, &rec, CARRIER, pv)
    };
    let ihc = k.const_(f.cs.is_grp_hom, vec![]);

    for (name, want, other) in [(f.ps.grp_prod_fst, n1, n2), (f.ps.grp_prod_snd, n2, n1)] {
        let tgt_v = if name == f.ps.grp_prod_fst { gv } else { hv };
        let tgt_carrier = {
            use algs::group::CARRIER;
            sel(&mut k, &rec, CARRIER, tgt_v)
        };
        let alpha = arrow(&mut k, carrier, tgt_carrier);
        let pred = app2(&mut k, ihc, pv, tgt_v);
        let projc = k.const_(name, vec![]);
        let proj = app2(&mut k, projc, gv, hv);
        let fnv = sub1_val(&mut k, &f.lg, alpha, pred, proj);
        let got = k.app(fnv, p12);
        assert!(
            k.def_eq(got, want),
            "{name:?} applied to (1,2) must read its own component"
        );
        assert!(
            !k.def_eq(got, other),
            "{name:?} applied to (1,2) must NOT read the OTHER component"
        );
    }
}

/// **The mediating map is the pairing**, symbolically: `med X u v x` is
/// `(u x, v x)` and not either component alone. This is the test a mutant
/// that drops one half of the pairing dies on.
#[test]
fn the_mediating_map_is_the_pairing() {
    use algs::group::CARRIER;
    let mut k = Kernel::new();
    let f = build(&mut k);
    let rec = f.st.group;
    let gv = k.fvar(95_000);
    let hv = k.fvar(95_001);
    let xv = k.fvar(95_002);
    let gc = sel(&mut k, &rec, CARRIER, gv);
    let hc = sel(&mut k, &rec, CARRIER, hv);
    let xc = sel(&mut k, &rec, CARRIER, xv);
    let gpc = k.const_(f.ps.grp_prod, vec![]);
    let pv = app2(&mut k, gpc, gv, hv);
    let pc = sel(&mut k, &rec, CARRIER, pv);

    let ihc = k.const_(f.cs.is_grp_hom, vec![]);
    let u_pred = app2(&mut k, ihc, xv, gv);
    let ihc2 = k.const_(f.cs.is_grp_hom, vec![]);
    let v_pred = app2(&mut k, ihc2, xv, hv);
    let u_alpha = arrow(&mut k, xc, gc);
    let v_alpha = arrow(&mut k, xc, hc);
    let u = k.fvar(95_003);
    let v = k.fvar(95_004);
    let x = k.fvar(95_005);
    let uf = sub1_val(&mut k, &f.lg, u_alpha, u_pred, u);
    let vf = sub1_val(&mut k, &f.lg, v_alpha, v_pred, v);

    let medc = k.const_(f.ps.grp_prod_med, vec![]);
    let med = t_app(&mut k, medc, &[gv, hv, xv, u, v]);
    let p_alpha = arrow(&mut k, xc, pc);
    let ihc3 = k.const_(f.cs.is_grp_hom, vec![]);
    let p_pred = app2(&mut k, ihc3, xv, pv);
    let medf = sub1_val(&mut k, &f.lg, p_alpha, p_pred, med);
    let got = k.app(medf, x);

    let pr = Pair { ca: gc, cb: hc };
    let ux = k.app(uf, x);
    let vx = k.app(vf, x);
    let want = pr.mk(&mut k, &f.lg, ux, vx);
    assert!(k.def_eq(got, want), "med u v x must be (u x, v x)");

    let swapped = {
        let pr2 = Pair { ca: gc, cb: hc };
        pr2.mk(&mut k, &f.lg, ux, ux)
    };
    assert!(
        !k.def_eq(got, swapped),
        "med u v x must NOT drop v -- the pairing uses BOTH morphisms"
    );
}

/// **The two triangles of `CatS.grp_isProduct` are `equivRefl`, not a
/// calculation** — the measurement the module header prices. Read back from
/// the kernel: the composite's underlying function, at an element, IS the
/// component morphism's value.
#[test]
fn the_group_products_triangles_are_free_by_iota() {
    use algs::group::CARRIER;
    let mut k = Kernel::new();
    let f = build(&mut k);
    let rec = f.st.group;
    let grp = k.const_(f.gs.grp, vec![]);
    let c = cat_of(&mut k, &f.recs.category_large, grp);

    let gv = k.fvar(94_000);
    let hv = k.fvar(94_001);
    let xv = k.fvar(94_002);
    let gc = sel(&mut k, &rec, CARRIER, gv);
    let hc = sel(&mut k, &rec, CARRIER, hv);
    let xc = sel(&mut k, &rec, CARRIER, xv);
    let gpc = k.const_(f.ps.grp_prod, vec![]);
    let pv = app2(&mut k, gpc, gv, hv);

    let ihc = k.const_(f.cs.is_grp_hom, vec![]);
    let u_pred = app2(&mut k, ihc, xv, gv);
    let ihc2 = k.const_(f.cs.is_grp_hom, vec![]);
    let v_pred = app2(&mut k, ihc2, xv, hv);
    let u_alpha = arrow(&mut k, xc, gc);
    let v_alpha = arrow(&mut k, xc, hc);
    let u = k.fvar(94_003);
    let v = k.fvar(94_004);
    let x = k.fvar(94_005);
    let uf = sub1_val(&mut k, &f.lg, u_alpha, u_pred, u);
    let vf = sub1_val(&mut k, &f.lg, v_alpha, v_pred, v);

    let medc = k.const_(f.ps.grp_prod_med, vec![]);
    let med = t_app(&mut k, medc, &[gv, hv, xv, u, v]);
    let f1c = k.const_(f.ps.grp_prod_fst, vec![]);
    let pr1 = app2(&mut k, f1c, gv, hv);
    let f2c = k.const_(f.ps.grp_prod_snd, vec![]);
    let pr2 = app2(&mut k, f2c, gv, hv);

    for (proj, want_fn, other_fn, which) in [(pr1, uf, vf, "first"), (pr2, vf, uf, "second")] {
        let tgt_v = if which == "first" { gv } else { hv };
        let tgt_c = if which == "first" { gc } else { hc };
        let cmp = c.cmp(&mut k, xv, pv, tgt_v, proj, med);
        let alpha = arrow(&mut k, xc, tgt_c);
        let ihc3 = k.const_(f.cs.is_grp_hom, vec![]);
        let pred = app2(&mut k, ihc3, xv, tgt_v);
        let cmpf = sub1_val(&mut k, &f.lg, alpha, pred, cmp);
        let got = k.app(cmpf, x);
        let want = k.app(want_fn, x);
        assert!(
            k.def_eq(got, want),
            "the {which} triangle must ι-reduce to the {which} morphism"
        );
        let bad = k.app(other_fn, x);
        assert!(
            !k.def_eq(got, bad),
            "the {which} triangle must NOT reduce to the OTHER morphism -- \
             that is the projection swap this test exists to kill"
        );
    }
}

/// **The uniqueness conjunct really is a hypothesis-consuming statement.**
/// Reading `IsProductLarge`'s third conjunct back at `CatS.grp` pins that
/// `homEquiv` there is pointwise on `Subtype.val`, so dropping either
/// hypothesis leaves an underivable goal.
#[test]
fn the_group_products_uniqueness_conjunct_is_pointwise() {
    use algs::group::{CARRIER, EQUIV};
    let mut k = Kernel::new();
    let f = build(&mut k);
    let rec = f.st.group;
    let grp = k.const_(f.gs.grp, vec![]);
    let c = cat_of(&mut k, &f.recs.category_large, grp);

    let gv = k.fvar(93_000);
    let hv = k.fvar(93_001);
    let xv = k.fvar(93_002);
    let gc = sel(&mut k, &rec, CARRIER, gv);
    let hc = sel(&mut k, &rec, CARRIER, hv);
    let xc = sel(&mut k, &rec, CARRIER, xv);
    let gpc = k.const_(f.ps.grp_prod, vec![]);
    let pv = app2(&mut k, gpc, gv, hv);

    let m = k.fvar(93_003);
    let el = k.fvar(93_004);
    let pc = sel(&mut k, &rec, CARRIER, pv);
    let p_alpha = arrow(&mut k, xc, pc);
    let ihc = k.const_(f.cs.is_grp_hom, vec![]);
    let p_pred = app2(&mut k, ihc, xv, pv);
    let mf = sub1_val(&mut k, &f.lg, p_alpha, p_pred, m);
    let m_el = k.app(mf, el);

    let f1c = k.const_(f.ps.grp_prod_fst, vec![]);
    let pr1 = app2(&mut k, f1c, gv, hv);
    let cmp = c.cmp(&mut k, xv, pv, gv, pr1, m);
    let alpha = arrow(&mut k, xc, gc);
    let ihc2 = k.const_(f.cs.is_grp_hom, vec![]);
    let pred = app2(&mut k, ihc2, xv, gv);
    let cmpf = sub1_val(&mut k, &f.lg, alpha, pred, cmp);
    let got = k.app(cmpf, el);

    let pr = Pair { ca: gc, cb: hc };
    let want = pr.fst(&mut k, &f.lg, m_el);
    assert!(
        k.def_eq(got, want),
        "the uniqueness hypothesis at an element is about m's FIRST component"
    );
    let bad = pr.snd(&mut k, &f.lg, m_el);
    assert!(
        !k.def_eq(got, bad),
        "it must NOT be about m's second component"
    );

    // And the product's own `equiv` at two elements really is the CONJUNCTION.
    let p_equiv = sel(&mut k, &rec, EQUIV, pv);
    let q = k.fvar(93_005);
    let got_eq = app2(&mut k, p_equiv, m_el, q);
    let (q1, q2) = pr.split(&mut k, &f.lg, q);
    let (m1, m2) = pr.split(&mut k, &f.lg, m_el);
    let g_equiv = sel(&mut k, &rec, EQUIV, gv);
    let h_equiv = sel(&mut k, &rec, EQUIV, hv);
    let e1 = app2(&mut k, g_equiv, m1, q1);
    let e2 = app2(&mut k, h_equiv, m2, q2);
    let and_c = k.const_(f.lg.and, vec![]);
    let want_eq = app2(&mut k, and_c, e1, e2);
    assert!(
        k.def_eq(got_eq, want_eq),
        "grpProd's equiv must be the conjunction of the two component equivs"
    );
    assert!(
        !k.def_eq(got_eq, e1),
        "grpProd's equiv must NOT be the first component's alone -- dropping \
         one conjunct is exactly the mutation this pins"
    );
}

// ---------------------------------------------------------------------------
// The ℤ-structure object type: measured, not argued.
// ---------------------------------------------------------------------------

/// **The object type of ℤ-structures FITS.** The handoff this lane inherited
/// recorded ℤ-initiality as blocked because the object mixes `PSigma` and
/// `Subtype`. It does mix them, and the mix lands at exactly the level
/// `CatS.CategoryLarge.obj` takes:
///
/// ```text
/// Sigma.{1,0} (Sort 1) (fun R =>
///   Subtype.{1} (Sigma.{0,0} R (fun _ => Sigma.{0,0} (R → R) (fun _ => R → R)))
///               (fun d => (∀ x, down d (up d x) = x) ∧ (∀ x, up d (down d x) = x)))
///   : Sort 2
/// ```
///
/// This test BUILDS that type in the kernel and reads its own type back, in
/// both directions. It declares nothing: the remaining blocker is build order
/// (`Int` lives in `int_prelude`, whose builder calls `build_nat_prelude`
/// first, so there is no `Int` at this position to state initiality about),
/// and a type that cannot be used yet is not public surface.
#[test]
fn the_z_structure_object_type_fits_at_sort_2() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let lg = f.lg;
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let l2 = k.level_succ(l1);
    let l3 = k.level_succ(l2);
    let sort1 = k.sort(l1);
    let sort2 = k.sort(l2);
    let sort3 = k.sort(l3);

    let r_fv = 92_000;

    // Subtype.{1} (data over R) (the two inverse laws) — the FIBRE. Built at
    // an arbitrary carrier, so it can be checked at a CLOSED one (`Nat`) and
    // then abstracted over a free one for the outer `Sigma`.
    fn z_fibre(k: &mut Kernel, lg: &LogicPrelude, r: ExprId) -> ExprId {
        let d_fv = 92_001;
        let x_fv = 92_002;
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let endo = arrow(k, r, r);
        let inner = Pair { ca: endo, cb: endo };
        let inner_ty = inner.ty(k, lg);
        let outer = Pair {
            ca: r,
            cb: inner_ty,
        };
        let data_ty = outer.ty(k, lg);

        let d = k.fvar(d_fv);
        let maps = outer.snd(k, lg, d);
        let up = inner.fst(k, lg, maps);
        let down = inner.snd(k, lg, maps);
        let x = k.fvar(x_fv);
        let law1 = {
            let ux = k.app(up, x);
            let dux = k.app(down, ux);
            let body = eq_of(k, lg, l1, r, dux, x);
            pi_over(k, x_fv, r, body)
        };
        let law2 = {
            let dx = k.app(down, x);
            let udx = k.app(up, dx);
            let body = eq_of(k, lg, l1, r, udx, x);
            pi_over(k, x_fv, r, body)
        };
        let and_c = k.const_(lg.and, vec![]);
        let laws = app2(k, and_c, law1, law2);
        let pred = lam_over(k, d_fv, data_ty, laws);
        let sub_head = k.const_(lg.sigma.subtype, vec![l1]);
        app2(k, sub_head, data_ty, pred)
    }

    // At the CLOSED carrier `Nat`, the fibre type-checks and lands at Sort 1
    // — `Subtype.{1} : … → Sort (max 1 1)`.
    let nat = k.const_(lg.nat, vec![]);
    let fibre_nat = z_fibre(&mut k, &lg, nat);
    let fibre_ty = k.infer(fibre_nat).expect("the fibre must type-check");
    assert!(
        k.def_eq(fibre_ty, sort1),
        "Subtype.{{1}} over the data must land at Sort 1"
    );
    assert!(
        !k.def_eq(fibre_ty, sort2),
        "the fibre must NOT already be at Sort 2 -- that would be the level \
         that blocks the outer Sigma"
    );

    // Sigma.{1,0} (Sort 1) (fun R => …) : Type (max 1 0) = Sort 2.
    let r = k.fvar(r_fv);
    let on_r = z_fibre(&mut k, &lg, r);
    let family = lam_over(&mut k, r_fv, sort1, on_r);
    let sig_head = k.const_(lg.sigma.sigma, vec![l1, l0]);
    let z_struct = app2(&mut k, sig_head, sort1, family);
    let z_ty = k.infer(z_struct).expect("ZStruct must type-check");
    assert!(
        k.def_eq(z_ty, sort2),
        "the ℤ-structure object type must live at Sort 2 -- the level \
         CatS.CategoryLarge.obj takes"
    );
    assert!(
        !k.def_eq(z_ty, sort1),
        "it must NOT be at Sort 1 -- CatS.Category could not hold it"
    );
    assert!(
        !k.def_eq(z_ty, sort3),
        "it must NOT be at Sort 3 -- that is where CatS.FunctorLarge lives, \
         and it would need a fifth record"
    );
    println!("ZStruct : {}", k.render_lean(z_ty));

    // Positive control OF THE SAME KIND, read from the kernel: `CatS.PtAlg`,
    // which ADR-1626 landed, is at the SAME level by the same construction
    // with the Subtype layer omitted.
    let pt = k.const_(f.gs.pt_alg, vec![]);
    let pt_ty = k.infer(pt).expect("PtAlg exists");
    assert!(
        k.def_eq(pt_ty, sort2),
        "control: CatS.PtAlg is at Sort 2 too"
    );

    // And the blocker that DOES remain: there is no `Int` at this position.
    // `LogicPrelude` carries `nat`, which is why ADR-1626 could re-prove ℕ
    // initiality in place; it carries no integer type.
    let nat_ty = k.infer(nat).expect("Nat exists");
    assert!(
        k.def_eq(nat_ty, sort1),
        "Nat IS available here (this is the asymmetry: ℕ could be re-proved \
         in place, ℤ cannot)"
    );
}
