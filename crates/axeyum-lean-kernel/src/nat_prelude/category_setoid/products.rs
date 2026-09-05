//! **Products and coproducts as universal properties** in the setoid-enriched
//! category layer (roadmap W3-4), plus the two instances that make the
//! statement worth having: the (degenerate) product in `CatS.indiscrete` and
//! the **product of two groups** in `CatS.grp`.
//!
//! # The shape of the statement, and why it has three conjuncts
//!
//! `docs/research/08-planning/universal-property-template.md` part 2 is
//! already the house style for `CatS.IsInitial`: the mediating map is a
//! **given** — a `med` argument, computed, never extracted from an `Exists` —
//! and uniqueness is stated *up to the hom-equivalence*, which is the
//! strongest form available in a kernel with no `funext` (ADR-1595). A
//! product needs one thing initiality does not: the mediating map has to
//! *commute with the projections*, and that is not implied by uniqueness. So
//! `CatS.IsProduct` is three conjuncts, not one:
//!
//! ```text
//! CatS.IsProduct C a b p pr1 pr2 med :=
//!   (∀ x f g, C.homEquiv x a (C.comp x p a pr1 (med x f g)) f)
//! ∧ (∀ x f g, C.homEquiv x b (C.comp x p b pr2 (med x f g)) g)
//! ∧ (∀ x f g m, C.homEquiv x a (C.comp x p a pr1 m) f
//!             → C.homEquiv x b (C.comp x p b pr2 m) g
//!             → C.homEquiv x p m (med x f g))
//! ```
//!
//! The first two are the triangles; the third is uniqueness, and it is the
//! conjunct that carries the content — drop it and every object with a pair of
//! maps out of it "is" a product. `CatS.IsCoproduct` is the same builder with
//! every hom reversed and every composite written on the other side, which is
//! why one function with a `dual` flag produces both.
//!
//! # `CatS.Iso` did not exist and had to be defined
//!
//! `CatS.initial_unique` states its conclusion as a bare conjunction of two
//! round-trip equivalences — there was no `Iso` in the module (verified ABSENT
//! against a fresh `shape_search` index at 3,093 declarations; positive
//! control `CatS.isGrpHom_congr` FOUND). So `CatS.Iso` is declared here, in
//! exactly the shape `initial_unique` already produces by hand, and
//! `CatS.product_unique_upto_iso` is stated against it.
//!
//! # The one real proof in the abstract half
//!
//! `product_unique_upto_iso` is not free the way `initial_unique` is.
//! Initiality gives `med b ~ g` for **every** `g`, so both round trips
//! collapse in one `homTrans`. A product's uniqueness clause has two
//! hypotheses, and discharging them for `m := v ∘ u` needs the category's
//! `assoc` and `compCongr` — the two fields `super::Cat` does not carry and
//! this module reads by selector index. Each triangle obligation is
//!
//! ```text
//! pr1 ∘ (v ∘ u) ~ (pr1 ∘ v) ∘ u      -- assoc, symm
//!               ~ qr1 ∘ u             -- compCongr on q's triangle, homRefl u
//!               ~ pr1                 -- p's triangle
//! ```
//!
//! four steps; two obligations per side and two sides gives **sixteen**
//! hom-equivalence steps in the theorem. That is the measured setoid price of
//! the uniqueness statement, and every one of them is `assoc`/`compCongr`
//! bookkeeping — nothing in it is about groups, sets or elements.
//!
//! # The setoid price of the product of two groups
//!
//! `CatS.grpProd G H` is an `AlgS.Group` on `Sigma.{0,0} G.carrier
//! (fun _ => H.carrier)` with the pointwise operations. The `Sigma` is the
//! ADR-1613 family again, at the same levels `IntSpace.Bundled` uses: both
//! carriers are `Sort 1 = Type 0`, so `u = v = 0` and the pair lands back at
//! `Sort 1`, which is what `AlgS.Group.carrier` demands.
//!
//! | where | fields | new proofs | free |
//! |---|---|---|---|
//! | `CatS.grpProd` (the object) | 15 | 10 | 5 (`carrier`, `equiv`, `op`, `e`, `inv` are data) |
//! | `CatS.grpProdFst` / `Snd` | 2 conjuncts each | 1 each (`And.left`/`And.right`) | 1 each (`equivRefl`) |
//! | `CatS.grpProdMed` | 2 conjuncts | 2 | 0 |
//! | `CatS.grp_isProduct` | 3 conjuncts | 1 (`And.intro`) | 2 (`equivRefl`) |
//!
//! Each of the ten object proofs is literally `And.intro (G.<law> …)
//! (H.<law> …)`: the product setoid's `equiv` is the conjunction of the two
//! component `equiv`s, so **every law of the product is the pair of the
//! component laws and nothing else**. There is no congruence bookkeeping at
//! all, because `Sigma.fst (Sigma.mk a b)` ι-reduces — the same mechanism
//! ADR-1626 measured for `Subtype.val` at `idL`/`idR`/`assoc`.
//!
//! Two of the four `grp_isProduct` conjuncts are free *because of that same
//! ι-reduction*: `pr1 ∘ (pair f g)` is `fun x => Sigma.fst (Sigma.mk (f x)
//! (g x))`, which reduces to `f`, so the triangle is `G.equivRefl` and not a
//! calculation. Under `Eq` the object would be identical but the *category*
//! would not exist (ADR-1626), so there is no `Eq`-flavoured counterfactual to
//! price against.

use super::*;

// ---------------------------------------------------------------------------
// Free variables. Disjoint from `category_setoid`'s 25_000..25_130 block and
// from `groups.rs`'s 25_200..25_263 block.
// ---------------------------------------------------------------------------

const PC_FV: u64 = 25_300;
const PA_FV: u64 = 25_301;
const PB_FV: u64 = 25_302;
const PP_FV: u64 = 25_303;
const PQ_FV: u64 = 25_304;
const PX_FV: u64 = 25_305;

const PR1_FV: u64 = 25_310;
const PR2_FV: u64 = 25_311;
const QR1_FV: u64 = 25_312;
const QR2_FV: u64 = 25_313;
const PMED_FV: u64 = 25_314;
const QMED_FV: u64 = 25_315;

const PF_FV: u64 = 25_320;
const PG_FV: u64 = 25_321;
const PM_FV: u64 = 25_322;

const PH1_FV: u64 = 25_330;
const PH2_FV: u64 = 25_331;
const PHP_FV: u64 = 25_332;
const PHQ_FV: u64 = 25_333;

// The group-product half.
const GP_G_FV: u64 = 25_340;
const GP_H_FV: u64 = 25_341;
const GP_X_FV: u64 = 25_342;
const GP_P_FV: u64 = 25_343;
const GP_Q_FV: u64 = 25_344;
const GP_R_FV: u64 = 25_345;
const GP_PP_FV: u64 = 25_346;
const GP_QP_FV: u64 = 25_347;
const GP_HY1_FV: u64 = 25_350;
const GP_HY2_FV: u64 = 25_351;
const GP_U_FV: u64 = 25_352;
const GP_V_FV: u64 = 25_353;
const GP_EL_FV: u64 = 25_355;
const GP_DUMMY_FV: u64 = 25_356;

// ---------------------------------------------------------------------------
// The two category fields `Cat` does not carry.
// ---------------------------------------------------------------------------

/// `C.compCongr` and `C.assoc`, applied to a category VALUE. `Cat` stops at
/// `comp` because initiality never needs either; a product needs both.
#[derive(Clone, Copy)]
struct CatLaws {
    comp_congr: ExprId,
    assoc: ExprId,
}

fn laws_of(k: &mut Kernel, rn: &RecordNames, c: ExprId) -> CatLaws {
    CatLaws {
        comp_congr: sel(k, rn, idx::COMP_CONGR, c),
        assoc: sel(k, rn, idx::ASSOC, c),
    }
}

impl CatLaws {
    /// `C.compCongr a b c g g' f f' hg hf`.
    #[allow(clippy::too_many_arguments)]
    fn congr(
        &self,
        k: &mut Kernel,
        objs: [ExprId; 3],
        gs: [ExprId; 2],
        fs: [ExprId; 2],
        hg: ExprId,
        hf: ExprId,
    ) -> ExprId {
        t_app(
            k,
            self.comp_congr,
            &[
                objs[0], objs[1], objs[2], gs[0], gs[1], fs[0], fs[1], hg, hf,
            ],
        )
    }

    /// `C.assoc a b c d h g f`.
    fn assoc4(&self, k: &mut Kernel, objs: [ExprId; 4], h: ExprId, g: ExprId, f: ExprId) -> ExprId {
        t_app(
            k,
            self.assoc,
            &[objs[0], objs[1], objs[2], objs[3], h, g, f],
        )
    }
}

/// `C.idR a b f : C.homEquiv a b (C.comp a a b f (C.id a)) f`.
fn id_r_at(
    k: &mut Kernel,
    rn: &RecordNames,
    cv: ExprId,
    a: ExprId,
    b: ExprId,
    f: ExprId,
) -> ExprId {
    let idr = sel(k, rn, ID_R, cv);
    t_app(k, idr, &[a, b, f])
}

// ---------------------------------------------------------------------------
// `CatS.IsProduct` / `CatS.IsCoproduct`.
// ---------------------------------------------------------------------------

/// The mediating map's type for a product: `forall (x : obj), hom x a ->
/// hom x b -> hom x p`; dualised, `forall x, hom a x -> hom b x -> hom p x`.
fn med_pair_ty(k: &mut Kernel, c: &Cat, a: ExprId, b: ExprId, p: ExprId, dual: bool) -> ExprId {
    let x = k.fvar(PX_FV);
    let (fa, gb, mp) = if dual {
        let fa = c.hom_ty(k, a, x);
        let gb = c.hom_ty(k, b, x);
        let mp = c.hom_ty(k, p, x);
        (fa, gb, mp)
    } else {
        let fa = c.hom_ty(k, x, a);
        let gb = c.hom_ty(k, x, b);
        let mp = c.hom_ty(k, x, p);
        (fa, gb, mp)
    };
    let t = arrow(k, gb, mp);
    let t = arrow(k, fa, t);
    pi_over(k, PX_FV, c.obj, t)
}

/// One leg's triangle for a chosen `m : hom x p` (product) / `hom p x`
/// (coproduct): `homEquiv (pr ∘ m) f`, on the correct side.
#[allow(clippy::too_many_arguments)]
fn leg_eq(
    k: &mut Kernel,
    c: &Cat,
    dual: bool,
    x: ExprId,
    p: ExprId,
    tgt: ExprId,
    pr: ExprId,
    m: ExprId,
    f: ExprId,
) -> ExprId {
    if dual {
        // pr : hom tgt p, m : hom p x, so m ∘ pr : hom tgt x.
        let lhs = c.cmp(k, tgt, p, x, m, pr);
        c.eqv(k, tgt, x, lhs, f)
    } else {
        // pr : hom p tgt, m : hom x p, so pr ∘ m : hom x tgt.
        let lhs = c.cmp(k, x, p, tgt, pr, m);
        c.eqv(k, x, tgt, lhs, f)
    }
}

/// The three conjuncts of `IsProduct C a b p pr1 pr2 med`, built from
/// ARBITRARY argument terms. `declare_is_product` calls it on free variables
/// and then abstracts; `product_unique_upto_iso` calls it on the actual
/// arguments so [`project3`] has the exact props to project against.
#[allow(clippy::too_many_arguments)]
fn product_conjuncts(
    k: &mut Kernel,
    c: &Cat,
    dual: bool,
    a: ExprId,
    b: ExprId,
    p: ExprId,
    pr1: ExprId,
    pr2: ExprId,
    med: ExprId,
) -> [ExprId; 3] {
    let x = k.fvar(PX_FV);
    let f_ty = if dual {
        c.hom_ty(k, a, x)
    } else {
        c.hom_ty(k, x, a)
    };
    let g_ty = if dual {
        c.hom_ty(k, b, x)
    } else {
        c.hom_ty(k, x, b)
    };
    let m_ty = if dual {
        c.hom_ty(k, p, x)
    } else {
        c.hom_ty(k, x, p)
    };
    let f = k.fvar(PF_FV);
    let g = k.fvar(PG_FV);
    let med_x = {
        let t = k.app(med, x);
        let t = k.app(t, f);
        k.app(t, g)
    };
    let close_xfg = |k: &mut Kernel, body: ExprId| {
        let t = pi_over(k, PG_FV, g_ty, body);
        let t = pi_over(k, PF_FV, f_ty, t);
        pi_over(k, PX_FV, c.obj, t)
    };

    let c1 = {
        let body = leg_eq(k, c, dual, x, p, a, pr1, med_x, f);
        close_xfg(k, body)
    };
    let c2 = {
        let body = leg_eq(k, c, dual, x, p, b, pr2, med_x, g);
        close_xfg(k, body)
    };
    let c3 = {
        let m = k.fvar(PM_FV);
        let h1 = leg_eq(k, c, dual, x, p, a, pr1, m, f);
        let h2 = leg_eq(k, c, dual, x, p, b, pr2, m, g);
        let concl = if dual {
            c.eqv(k, p, x, m, med_x)
        } else {
            c.eqv(k, x, p, m, med_x)
        };
        let body = arrow(k, h2, concl);
        let body = arrow(k, h1, body);
        let body = pi_over(k, PM_FV, m_ty, body);
        close_xfg(k, body)
    };
    [c1, c2, c3]
}

/// `CatS.IsProduct` (and, dualised, `CatS.IsCoproduct`) — the mediating map is
/// GIVEN, the two triangles commute up to the hom-equivalence, and any map
/// making both triangles commute is hom-equivalent to it.
fn declare_is_product(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cat: &RecordNames,
    ns: NameId,
    dual: bool,
    suffix: &str,
) -> Result<NameId, KernelError> {
    let cat_ty = k.const_(cat.ind, vec![]);
    let cv = k.fvar(PC_FV);
    let c = cat_of(k, cat, cv);

    let a = k.fvar(PA_FV);
    let b = k.fvar(PB_FV);
    let p = k.fvar(PP_FV);

    let pr1_ty = if dual {
        c.hom_ty(k, a, p)
    } else {
        c.hom_ty(k, p, a)
    };
    let pr2_ty = if dual {
        c.hom_ty(k, b, p)
    } else {
        c.hom_ty(k, p, b)
    };
    let med_ty = med_pair_ty(k, &c, a, b, p, dual);

    let pr1 = k.fvar(PR1_FV);
    let pr2 = k.fvar(PR2_FV);
    let med = k.fvar(PMED_FV);

    let props = product_conjuncts(k, &c, dual, a, b, p, pr1, pr2, med);
    let body = and3(k, lg, &props);
    let value = lam_over(k, PMED_FV, med_ty, body);
    let value = lam_over(k, PR2_FV, pr2_ty, value);
    let value = lam_over(k, PR1_FV, pr1_ty, value);
    let value = lam_over(k, PP_FV, c.obj, value);
    let value = lam_over(k, PB_FV, c.obj, value);
    let value = lam_over(k, PA_FV, c.obj, value);
    let value = lam_over(k, PC_FV, cat_ty, value);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = pi_over(k, PMED_FV, med_ty, prop);
    let ty = pi_over(k, PR2_FV, pr2_ty, ty);
    let ty = pi_over(k, PR1_FV, pr1_ty, ty);
    let ty = pi_over(k, PP_FV, c.obj, ty);
    let ty = pi_over(k, PB_FV, c.obj, ty);
    let ty = pi_over(k, PA_FV, c.obj, ty);
    let ty = pi_over(k, PC_FV, cat_ty, ty);

    let name = k.name_str(ns, suffix);
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// `CatS.Iso`.
// ---------------------------------------------------------------------------

/// `CatS.Iso C a b f g := C.homEquiv b b (f ∘ g) (C.id b)
///  ∧ C.homEquiv a a (g ∘ f) (C.id a)` — exactly the conjunction
/// `CatS.initial_unique` already produces by hand, given a name.
fn declare_iso(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cat: &RecordNames,
    ns: NameId,
    suffix: &str,
) -> Result<NameId, KernelError> {
    let cat_ty = k.const_(cat.ind, vec![]);
    let cv = k.fvar(PC_FV);
    let c = cat_of(k, cat, cv);
    let a = k.fvar(PA_FV);
    let b = k.fvar(PB_FV);
    let f_ty = c.hom_ty(k, a, b);
    let g_ty = c.hom_ty(k, b, a);
    let f = k.fvar(PF_FV);
    let g = k.fvar(PG_FV);

    let fg = c.cmp(k, b, a, b, f, g);
    let gf = c.cmp(k, a, b, a, g, f);
    let ib = c.ident(k, b);
    let ia = c.ident(k, a);
    let p1 = c.eqv(k, b, b, fg, ib);
    let p2 = c.eqv(k, a, a, gf, ia);
    let and_c = k.const_(lg.and, vec![]);
    let body = app2(k, and_c, p1, p2);

    let value = lam_over(k, PG_FV, g_ty, body);
    let value = lam_over(k, PF_FV, f_ty, value);
    let value = lam_over(k, PB_FV, c.obj, value);
    let value = lam_over(k, PA_FV, c.obj, value);
    let value = lam_over(k, PC_FV, cat_ty, value);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = pi_over(k, PG_FV, g_ty, prop);
    let ty = pi_over(k, PF_FV, f_ty, ty);
    let ty = pi_over(k, PB_FV, c.obj, ty);
    let ty = pi_over(k, PA_FV, c.obj, ty);
    let ty = pi_over(k, PC_FV, cat_ty, ty);

    let name = k.name_str(ns, suffix);
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// `CatS.product_unique_upto_iso`.
// ---------------------------------------------------------------------------

/// One side of a product's data: the apex, its two projections, its mediating
/// map, and the three conjuncts of its `IsProduct` proof.
#[derive(Clone, Copy)]
struct ProdSide {
    apex: ExprId,
    pr1: ExprId,
    pr2: ExprId,
    med: ExprId,
    props: [ExprId; 3],
    proof: ExprId,
}

impl ProdSide {
    /// `med apex' pr1' pr2'` — the mediating map INTO this apex out of the
    /// other side's apex.
    fn med_at(&self, k: &mut Kernel, other: &ProdSide) -> ExprId {
        let t = k.app(self.med, other.apex);
        let t = k.app(t, other.pr1);
        k.app(t, other.pr2)
    }

    /// The triangle for leg `leg` (0 or 1) at test object `x` with the pair
    /// `(f, g)`.
    fn triangle(
        &self,
        k: &mut Kernel,
        lg: &LogicPrelude,
        leg: usize,
        x: ExprId,
        f: ExprId,
        g: ExprId,
    ) -> ExprId {
        let cj = project3(k, lg, &self.props, self.proof, leg);
        t_app(k, cj, &[x, f, g])
    }
}

/// `homEquiv home.apex home.apex (vv ∘ uu) (id home.apex)`, where
/// `uu := other.med home.apex home.pr1 home.pr2` and
/// `vv := home.med other.apex other.pr1 other.pr2`.
///
/// This is the whole content of `product_unique_upto_iso`: eight
/// hom-equivalence steps per direction, all of them `assoc`/`compCongr`
/// bookkeeping.
fn round_trip(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cat: &RecordNames,
    cv: ExprId,
    c: &Cat,
    laws: &CatLaws,
    a: ExprId,
    b: ExprId,
    home: &ProdSide,
    other: &ProdSide,
) -> ExprId {
    let hp = home.apex;
    let hq = other.apex;
    let uu = other.med_at(k, home); // hom hp hq
    let vv = home.med_at(k, other); // hom hq hp
    let m = c.cmp(k, hp, hq, hp, vv, uu); // hom hp hp

    // One leg's obligation: homEquiv hp tgt (comp hp hp tgt pr (vv ∘ uu)) pr.
    let leg = |k: &mut Kernel, leg_idx: usize, tgt: ExprId, pr: ExprId, qr: ExprId| -> ExprId {
        // assoc hp hq hp tgt pr vv uu
        //   : homEquiv hp tgt (comp hp hq tgt (comp hq hp tgt pr vv) uu)
        //                     (comp hp hp tgt pr (comp hp hq hp vv uu))
        let a1 = laws.assoc4(k, [hp, hq, hp, tgt], pr, vv, uu);
        let lhs = {
            let inner = c.cmp(k, hq, hp, tgt, pr, vv);
            c.cmp(k, hp, hq, tgt, inner, uu)
        };
        let rhs = c.cmp(k, hp, hp, tgt, pr, m);
        let a1s = c.sy(k, hp, tgt, lhs, rhs, a1);

        // home's own triangle at the OTHER apex: comp hq hp tgt pr vv ~ qr.
        let t_other = home.triangle(k, lg, leg_idx, hq, other.pr1, other.pr2);
        let refl_u = c.rfl(k, hp, hq, uu);
        let mid = c.cmp(k, hp, hq, tgt, qr, uu);
        let inner = c.cmp(k, hq, hp, tgt, pr, vv);
        let a2 = laws.congr(k, [hp, hq, tgt], [inner, qr], [uu, uu], t_other, refl_u);

        // other's triangle at home's apex: comp hp hq tgt qr uu ~ pr.
        let t_home = other.triangle(k, lg, leg_idx, hp, home.pr1, home.pr2);

        let s1 = c.tr(k, hp, tgt, rhs, lhs, mid, a1s, a2);
        c.tr(k, hp, tgt, rhs, mid, pr, s1, t_home)
    };

    let ob1 = leg(k, 0, a, home.pr1, other.pr1);
    let ob2 = leg(k, 1, b, home.pr2, other.pr2);

    // home's uniqueness clause at x := hp, f := pr1, g := pr2.
    let uniq = project3(k, lg, &home.props, home.proof, 2);
    let med_home = {
        let t = k.app(home.med, hp);
        let t = k.app(t, home.pr1);
        k.app(t, home.pr2)
    };
    let u_m = t_app(k, uniq, &[hp, home.pr1, home.pr2, m, ob1, ob2]);

    // and at x := hp, m := id hp, whose two obligations are `idR`.
    let ident = c.ident(k, hp);
    let idr1 = id_r_at(k, cat, cv, hp, a, home.pr1);
    let idr2 = id_r_at(k, cat, cv, hp, b, home.pr2);
    let uniq2 = project3(k, lg, &home.props, home.proof, 2);
    let u_id = t_app(k, uniq2, &[hp, home.pr1, home.pr2, ident, idr1, idr2]);
    let u_ids = c.sy(k, hp, hp, ident, med_home, u_id);

    c.tr(k, hp, hp, m, med_home, ident, u_m, u_ids)
}

/// `CatS.product_unique_upto_iso` — two products of the same pair are
/// isomorphic, by the two mediating maps, and the isomorphism is the one the
/// universal property names (not merely "there exists one").
fn declare_product_unique_upto_iso(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cat: &RecordNames,
    is_product: NameId,
    iso: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let cat_ty = k.const_(cat.ind, vec![]);
    let cv = k.fvar(PC_FV);
    let c = cat_of(k, cat, cv);
    let laws = laws_of(k, cat, cv);

    let a = k.fvar(PA_FV);
    let b = k.fvar(PB_FV);
    let p = k.fvar(PP_FV);
    let q = k.fvar(PQ_FV);

    let pr1_ty = c.hom_ty(k, p, a);
    let pr2_ty = c.hom_ty(k, p, b);
    let qr1_ty = c.hom_ty(k, q, a);
    let qr2_ty = c.hom_ty(k, q, b);
    let pmed_ty = med_pair_ty(k, &c, a, b, p, false);
    let qmed_ty = med_pair_ty(k, &c, a, b, q, false);

    let pr1 = k.fvar(PR1_FV);
    let pr2 = k.fvar(PR2_FV);
    let qr1 = k.fvar(QR1_FV);
    let qr2 = k.fvar(QR2_FV);
    let pmed = k.fvar(PMED_FV);
    let qmed = k.fvar(QMED_FV);

    let isp = k.const_(is_product, vec![]);
    let hp_ty = t_app(k, isp, &[cv, a, b, p, pr1, pr2, pmed]);
    let isp2 = k.const_(is_product, vec![]);
    let hq_ty = t_app(k, isp2, &[cv, a, b, q, qr1, qr2, qmed]);
    let hp = k.fvar(PHP_FV);
    let hq = k.fvar(PHQ_FV);

    let p_side = ProdSide {
        apex: p,
        pr1,
        pr2,
        med: pmed,
        props: product_conjuncts(k, &c, false, a, b, p, pr1, pr2, pmed),
        proof: hp,
    };
    let q_side = ProdSide {
        apex: q,
        pr1: qr1,
        pr2: qr2,
        med: qmed,
        props: product_conjuncts(k, &c, false, a, b, q, qr1, qr2, qmed),
        proof: hq,
    };

    // u : hom p q, v : hom q p.
    let u = q_side.med_at(k, &p_side);
    let v = p_side.med_at(k, &q_side);

    let rt_q = round_trip(k, lg, cat, cv, &c, &laws, a, b, &q_side, &p_side);
    let rt_p = round_trip(k, lg, cat, cv, &c, &laws, a, b, &p_side, &q_side);

    let uv = c.cmp(k, q, p, q, u, v);
    let vu = c.cmp(k, p, q, p, v, u);
    let iq = c.ident(k, q);
    let ip = c.ident(k, p);
    let g1 = c.eqv(k, q, q, uv, iq);
    let g2 = c.eqv(k, p, p, vu, ip);
    let ai = k.const_(lg.and_intro, vec![]);
    let value = t_app(k, ai, &[g1, g2, rt_q, rt_p]);

    let value = lam_over(k, PHQ_FV, hq_ty, value);
    let value = lam_over(k, PHP_FV, hp_ty, value);
    let value = lam_over(k, QMED_FV, qmed_ty, value);
    let value = lam_over(k, QR2_FV, qr2_ty, value);
    let value = lam_over(k, QR1_FV, qr1_ty, value);
    let value = lam_over(k, PQ_FV, c.obj, value);
    let value = lam_over(k, PMED_FV, pmed_ty, value);
    let value = lam_over(k, PR2_FV, pr2_ty, value);
    let value = lam_over(k, PR1_FV, pr1_ty, value);
    let value = lam_over(k, PP_FV, c.obj, value);
    let value = lam_over(k, PB_FV, c.obj, value);
    let value = lam_over(k, PA_FV, c.obj, value);
    let value = lam_over(k, PC_FV, cat_ty, value);

    let isoc = k.const_(iso, vec![]);
    let concl = t_app(k, isoc, &[cv, p, q, u, v]);
    let ty = arrow(k, hq_ty, concl);
    let ty = arrow(k, hp_ty, ty);
    let ty = pi_over(k, QMED_FV, qmed_ty, ty);
    let ty = pi_over(k, QR2_FV, qr2_ty, ty);
    let ty = pi_over(k, QR1_FV, qr1_ty, ty);
    let ty = pi_over(k, PQ_FV, c.obj, ty);
    let ty = pi_over(k, PMED_FV, pmed_ty, ty);
    let ty = pi_over(k, PR2_FV, pr2_ty, ty);
    let ty = pi_over(k, PR1_FV, pr1_ty, ty);
    let ty = pi_over(k, PP_FV, c.obj, ty);
    let ty = pi_over(k, PB_FV, c.obj, ty);
    let ty = pi_over(k, PA_FV, c.obj, ty);
    let ty = pi_over(k, PC_FV, cat_ty, ty);

    thm(k, ns, "product_unique_upto_iso", ty, value)
}

// ---------------------------------------------------------------------------
// The instance in the module's first concrete category.
// ---------------------------------------------------------------------------

/// `CatS.indiscrete_isProduct` / `CatS.indiscrete_isCoproduct` — in the
/// indiscrete category **every** object, with any pair of maps, is a product
/// (and a coproduct) of any two objects, because `homEquiv` is `True`. The
/// twin of `CatS.indiscrete_isInitial`/`isTerminal`, and the honest measure of
/// how much a universal property says when the hom-equivalence is total: it
/// pins the object down to nothing at all.
fn declare_indiscrete_is_product(
    k: &mut Kernel,
    lg: &LogicPrelude,
    cat: &RecordNames,
    indiscrete: NameId,
    pred: NameId,
    ns: NameId,
    dual: bool,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let sort1 = k.sort(l1);
    let a_ty = k.fvar(TA_FV);
    let ind = k.const_(indiscrete, vec![]);
    let cv = k.app(ind, a_ty);
    let c = cat_of(k, cat, cv);

    let a = k.fvar(PA_FV);
    let b = k.fvar(PB_FV);
    let p = k.fvar(PP_FV);
    let pr1_ty = if dual {
        c.hom_ty(k, a, p)
    } else {
        c.hom_ty(k, p, a)
    };
    let pr2_ty = if dual {
        c.hom_ty(k, b, p)
    } else {
        c.hom_ty(k, p, b)
    };
    let pr1 = k.fvar(PR1_FV);
    let pr2 = k.fvar(PR2_FV);

    // The binder types the mediating map and every conjunct share.
    let x = k.fvar(PX_FV);
    let f_ty = if dual {
        c.hom_ty(k, a, x)
    } else {
        c.hom_ty(k, x, a)
    };
    let g_ty = if dual {
        c.hom_ty(k, b, x)
    } else {
        c.hom_ty(k, x, b)
    };
    let m_ty = if dual {
        c.hom_ty(k, p, x)
    } else {
        c.hom_ty(k, x, p)
    };

    // med := fun x f g => f. Well-typed only because every hom-set of the
    // indiscrete category is the SAME type `A`.
    let med = {
        let f = k.fvar(PF_FV);
        let t = lam_over(k, PG_FV, g_ty, f);
        let t = lam_over(k, PF_FV, f_ty, t);
        lam_over(k, PX_FV, c.obj, t)
    };

    let props = product_conjuncts(k, &c, dual, a, b, p, pr1, pr2, med);
    let ti = k.const_(lg.true_intro, vec![]);
    let triv_xfg = |k: &mut Kernel| {
        let t = lam_over(k, PG_FV, g_ty, ti);
        let t = lam_over(k, PF_FV, f_ty, t);
        lam_over(k, PX_FV, c.obj, t)
    };
    let v1 = triv_xfg(k);
    let v2 = triv_xfg(k);
    let v3 = {
        let m = k.fvar(PM_FV);
        let f = k.fvar(PF_FV);
        let g = k.fvar(PG_FV);
        let h1 = leg_eq(k, &c, dual, x, p, a, pr1, m, f);
        let h2 = leg_eq(k, &c, dual, x, p, b, pr2, m, g);
        let t = lam_over(k, PH2_FV, h2, ti);
        let t = lam_over(k, PH1_FV, h1, t);
        let t = lam_over(k, PM_FV, m_ty, t);
        let t = lam_over(k, PG_FV, g_ty, t);
        let t = lam_over(k, PF_FV, f_ty, t);
        lam_over(k, PX_FV, c.obj, t)
    };
    let value = intro3(k, lg, &props, &[v1, v2, v3]);
    let value = lam_over(k, PR2_FV, pr2_ty, value);
    let value = lam_over(k, PR1_FV, pr1_ty, value);
    let value = lam_over(k, PP_FV, c.obj, value);
    let value = lam_over(k, PB_FV, c.obj, value);
    let value = lam_over(k, PA_FV, c.obj, value);
    let value = lam_over(k, TA_FV, sort1, value);

    let pc = k.const_(pred, vec![]);
    let concl = t_app(k, pc, &[cv, a, b, p, pr1, pr2, med]);
    let ty = pi_over(k, PR2_FV, pr2_ty, concl);
    let ty = pi_over(k, PR1_FV, pr1_ty, ty);
    let ty = pi_over(k, PP_FV, c.obj, ty);
    let ty = pi_over(k, PB_FV, c.obj, ty);
    let ty = pi_over(k, PA_FV, c.obj, ty);
    let ty = pi_over(k, TA_FV, sort1, ty);

    thm(
        k,
        ns,
        if dual {
            "indiscrete_isCoproduct"
        } else {
            "indiscrete_isProduct"
        },
        ty,
        value,
    )
}

// ---------------------------------------------------------------------------
// The pair type: `Sigma` at (0,0), which is where two `Sort 1` carriers land.
// ---------------------------------------------------------------------------

/// The two carriers of a product, and the `Sigma` vocabulary over them.
/// `Sigma.{0,0} α (fun _ => β) : Type 0 = Sort 1`, exactly what
/// `AlgS.Group.carrier` demands — the same levels `IntSpace.Bundled` uses.
/// `PSigma` would also fit; `Sigma` is chosen because it is the half of the
/// ADR-1613 family that carries `fst_mk`/`snd_mk`/`mk_eta`, and because at
/// these levels the two are the same type.
#[derive(Clone, Copy)]
struct Pair {
    ca: ExprId,
    cb: ExprId,
}

impl Pair {
    /// `fun _ : α => β` — the constant family that makes the dependent pair a
    /// plain one.
    fn beta(&self, k: &mut Kernel) -> ExprId {
        lam_over(k, GP_DUMMY_FV, self.ca, self.cb)
    }

    fn ty(&self, k: &mut Kernel, lg: &LogicPrelude) -> ExprId {
        let l0 = k.level_zero();
        let head = k.const_(lg.sigma.sigma, vec![l0, l0]);
        let b = self.beta(k);
        app2(k, head, self.ca, b)
    }

    fn mk(&self, k: &mut Kernel, lg: &LogicPrelude, x: ExprId, y: ExprId) -> ExprId {
        let l0 = k.level_zero();
        let head = k.const_(lg.sigma.sigma_mk, vec![l0, l0]);
        let b = self.beta(k);
        t_app(k, head, &[self.ca, b, x, y])
    }

    fn fst(&self, k: &mut Kernel, lg: &LogicPrelude, s: ExprId) -> ExprId {
        let l0 = k.level_zero();
        let head = k.const_(lg.sigma.sigma_fst, vec![l0, l0]);
        let b = self.beta(k);
        t_app(k, head, &[self.ca, b, s])
    }

    fn snd(&self, k: &mut Kernel, lg: &LogicPrelude, s: ExprId) -> ExprId {
        let l0 = k.level_zero();
        let head = k.const_(lg.sigma.sigma_snd, vec![l0, l0]);
        let b = self.beta(k);
        t_app(k, head, &[self.ca, b, s])
    }

    /// `(fst s, snd s)` in one call, which is how every law below opens its
    /// arguments.
    fn split(&self, k: &mut Kernel, lg: &LogicPrelude, s: ExprId) -> (ExprId, ExprId) {
        let f = self.fst(k, lg, s);
        let g = self.snd(k, lg, s);
        (f, g)
    }
}

// ---------------------------------------------------------------------------
// `Subtype` vocabulary at level 1, for the bundled `CatS.GrpHom`.
// ---------------------------------------------------------------------------

fn sub1_val(k: &mut Kernel, lg: &LogicPrelude, alpha: ExprId, pred: ExprId, s: ExprId) -> ExprId {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let head = k.const_(lg.sigma.subtype_val, vec![l1]);
    t_app(k, head, &[alpha, pred, s])
}

fn sub1_prop(k: &mut Kernel, lg: &LogicPrelude, alpha: ExprId, pred: ExprId, s: ExprId) -> ExprId {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let head = k.const_(lg.sigma.subtype_property, vec![l1]);
    t_app(k, head, &[alpha, pred, s])
}

fn sub1_mk(
    k: &mut Kernel,
    lg: &LogicPrelude,
    alpha: ExprId,
    pred: ExprId,
    v: ExprId,
    p: ExprId,
) -> ExprId {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let head = k.const_(lg.sigma.subtype_mk, vec![l1]);
    t_app(k, head, &[alpha, pred, v, p])
}

// ---------------------------------------------------------------------------
// The fifteen selectors of an `AlgS.Group`.
// ---------------------------------------------------------------------------

/// Every field of an `AlgS.Group`, applied to one group VALUE. `groups.rs`'s
/// `Ob` stops at the seven `AlgS.Monoid` and `AlgS.Group` share; a product
/// object has to fill all fifteen.
#[derive(Clone, Copy)]
struct Grp {
    carrier: ExprId,
    equiv: ExprId,
    refl: ExprId,
    symm: ExprId,
    trans: ExprId,
    op: ExprId,
    op_congr: ExprId,
    e: ExprId,
    inv: ExprId,
    inv_congr: ExprId,
    assoc: ExprId,
    ident_l: ExprId,
    ident_r: ExprId,
    inv_l: ExprId,
    inv_r: ExprId,
}

fn grp_of(k: &mut Kernel, rec: &RecordNames, v: ExprId) -> Grp {
    use algs::group::{
        ASSOC, CARRIER, E, EQUIV, EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, IDENT_L, IDENT_R, INV,
        INV_CONGR, INV_L, INV_R, OP, OP_CONGR,
    };
    Grp {
        carrier: sel(k, rec, CARRIER, v),
        equiv: sel(k, rec, EQUIV, v),
        refl: sel(k, rec, EQUIV_REFL, v),
        symm: sel(k, rec, EQUIV_SYMM, v),
        trans: sel(k, rec, EQUIV_TRANS, v),
        op: sel(k, rec, OP, v),
        op_congr: sel(k, rec, OP_CONGR, v),
        e: sel(k, rec, E, v),
        inv: sel(k, rec, INV, v),
        inv_congr: sel(k, rec, INV_CONGR, v),
        assoc: sel(k, rec, ASSOC, v),
        ident_l: sel(k, rec, IDENT_L, v),
        ident_r: sel(k, rec, IDENT_R, v),
        inv_l: sel(k, rec, INV_L, v),
        inv_r: sel(k, rec, INV_R, v),
    }
}

/// `∀ x y, A.equiv x y -> B.equiv (f x) (f y)` — `CatS.IsGrpHom`'s first
/// conjunct, rebuilt here so `And.intro`/`And.left` can name it.
fn hom_congr_stmt(k: &mut Kernel, a: &Grp, b: &Grp, f: ExprId) -> ExprId {
    let x = k.fvar(GP_P_FV);
    let y = k.fvar(GP_Q_FV);
    let hyp = app2(k, a.equiv, x, y);
    let fx = k.app(f, x);
    let fy = k.app(f, y);
    let concl = app2(k, b.equiv, fx, fy);
    let t = arrow(k, hyp, concl);
    let t = pi_over(k, GP_Q_FV, a.carrier, t);
    pi_over(k, GP_P_FV, a.carrier, t)
}

/// `∀ x y, B.equiv (f (A.op x y)) (B.op (f x) (f y))` — the second conjunct.
fn hom_op_stmt(k: &mut Kernel, a: &Grp, b: &Grp, f: ExprId) -> ExprId {
    let x = k.fvar(GP_P_FV);
    let y = k.fvar(GP_Q_FV);
    let xy = app2(k, a.op, x, y);
    let lhs = k.app(f, xy);
    let fx = k.app(f, x);
    let fy = k.app(f, y);
    let rhs = app2(k, b.op, fx, fy);
    let body = app2(k, b.equiv, lhs, rhs);
    let t = pi_over(k, GP_Q_FV, a.carrier, body);
    pi_over(k, GP_P_FV, a.carrier, t)
}

fn and_intro2(
    k: &mut Kernel,
    lg: &LogicPrelude,
    p: ExprId,
    q: ExprId,
    u: ExprId,
    v: ExprId,
) -> ExprId {
    let ai = k.const_(lg.and_intro, vec![]);
    t_app(k, ai, &[p, q, u, v])
}

fn and_left2(k: &mut Kernel, lg: &LogicPrelude, p: ExprId, q: ExprId, h: ExprId) -> ExprId {
    let al = k.const_(lg.and_left, vec![]);
    t_app(k, al, &[p, q, h])
}

fn and_right2(k: &mut Kernel, lg: &LogicPrelude, p: ExprId, q: ExprId, h: ExprId) -> ExprId {
    let ar = k.const_(lg.and_right, vec![]);
    t_app(k, ar, &[p, q, h])
}

// ---------------------------------------------------------------------------
// `CatS.grpProd` — the product of two groups, as an object.
// ---------------------------------------------------------------------------

/// `CatS.grpProd : AlgS.Group -> AlgS.Group -> AlgS.Group`. Carrier the
/// `Sigma` pair, every operation componentwise, and **every one of the ten
/// law fields literally `And.intro (G.law …) (H.law …)`** — see the module
/// header for why there is no congruence bookkeeping at all.
fn declare_grp_prod(
    k: &mut Kernel,
    lg: &LogicPrelude,
    group: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let o_ty = k.const_(group.ind, vec![]);
    let gv = k.fvar(GP_G_FV);
    let hv = k.fvar(GP_H_FV);
    let g = grp_of(k, group, gv);
    let h = grp_of(k, group, hv);
    let pr = Pair {
        ca: g.carrier,
        cb: h.carrier,
    };
    let carrier = pr.ty(k, lg);

    // equiv := fun p q => G.equiv p.1 q.1 ∧ H.equiv p.2 q.2.
    let equiv = {
        let p = k.fvar(GP_P_FV);
        let q = k.fvar(GP_Q_FV);
        let (p1, p2) = pr.split(k, lg, p);
        let (q1, q2) = pr.split(k, lg, q);
        let e1 = app2(k, g.equiv, p1, q1);
        let e2 = app2(k, h.equiv, p2, q2);
        let and_c = k.const_(lg.and, vec![]);
        let body = app2(k, and_c, e1, e2);
        let t = lam_over(k, GP_Q_FV, carrier, body);
        lam_over(k, GP_P_FV, carrier, t)
    };

    let equiv_refl = {
        let p = k.fvar(GP_P_FV);
        let (p1, p2) = pr.split(k, lg, p);
        let e1 = app2(k, g.equiv, p1, p1);
        let e2 = app2(k, h.equiv, p2, p2);
        let v1 = k.app(g.refl, p1);
        let v2 = k.app(h.refl, p2);
        let body = and_intro2(k, lg, e1, e2, v1, v2);
        lam_over(k, GP_P_FV, carrier, body)
    };

    let equiv_symm = {
        let p = k.fvar(GP_P_FV);
        let q = k.fvar(GP_Q_FV);
        let (p1, p2) = pr.split(k, lg, p);
        let (q1, q2) = pr.split(k, lg, q);
        let e1 = app2(k, g.equiv, p1, q1);
        let e2 = app2(k, h.equiv, p2, q2);
        let and_c = k.const_(lg.and, vec![]);
        let hyp = app2(k, and_c, e1, e2);
        let hh = k.fvar(GP_HY1_FV);
        let l = and_left2(k, lg, e1, e2, hh);
        let r = and_right2(k, lg, e1, e2, hh);
        let s1 = t_app(k, g.symm, &[p1, q1, l]);
        let s2 = t_app(k, h.symm, &[p2, q2, r]);
        let f1 = app2(k, g.equiv, q1, p1);
        let f2 = app2(k, h.equiv, q2, p2);
        let body = and_intro2(k, lg, f1, f2, s1, s2);
        let t = lam_over(k, GP_HY1_FV, hyp, body);
        let t = lam_over(k, GP_Q_FV, carrier, t);
        lam_over(k, GP_P_FV, carrier, t)
    };

    let equiv_trans = {
        let p = k.fvar(GP_P_FV);
        let q = k.fvar(GP_Q_FV);
        let r = k.fvar(GP_R_FV);
        let (p1, p2) = pr.split(k, lg, p);
        let (q1, q2) = pr.split(k, lg, q);
        let (r1, r2) = pr.split(k, lg, r);
        let e1 = app2(k, g.equiv, p1, q1);
        let e2 = app2(k, h.equiv, p2, q2);
        let f1 = app2(k, g.equiv, q1, r1);
        let f2 = app2(k, h.equiv, q2, r2);
        let and_c = k.const_(lg.and, vec![]);
        let hyp1 = app2(k, and_c, e1, e2);
        let and_c2 = k.const_(lg.and, vec![]);
        let hyp2 = app2(k, and_c2, f1, f2);
        let h1 = k.fvar(GP_HY1_FV);
        let h2 = k.fvar(GP_HY2_FV);
        let l1 = and_left2(k, lg, e1, e2, h1);
        let r1p = and_right2(k, lg, e1, e2, h1);
        let l2 = and_left2(k, lg, f1, f2, h2);
        let r2p = and_right2(k, lg, f1, f2, h2);
        let t1 = t_app(k, g.trans, &[p1, q1, r1, l1, l2]);
        let t2 = t_app(k, h.trans, &[p2, q2, r2, r1p, r2p]);
        let c1 = app2(k, g.equiv, p1, r1);
        let c2 = app2(k, h.equiv, p2, r2);
        let body = and_intro2(k, lg, c1, c2, t1, t2);
        let t = lam_over(k, GP_HY2_FV, hyp2, body);
        let t = lam_over(k, GP_HY1_FV, hyp1, t);
        let t = lam_over(k, GP_R_FV, carrier, t);
        let t = lam_over(k, GP_Q_FV, carrier, t);
        lam_over(k, GP_P_FV, carrier, t)
    };

    let op = {
        let p = k.fvar(GP_P_FV);
        let q = k.fvar(GP_Q_FV);
        let (p1, p2) = pr.split(k, lg, p);
        let (q1, q2) = pr.split(k, lg, q);
        let o1 = app2(k, g.op, p1, q1);
        let o2 = app2(k, h.op, p2, q2);
        let body = pr.mk(k, lg, o1, o2);
        let t = lam_over(k, GP_Q_FV, carrier, body);
        lam_over(k, GP_P_FV, carrier, t)
    };

    let op_congr = {
        let a = k.fvar(GP_P_FV);
        let ap = k.fvar(GP_PP_FV);
        let b = k.fvar(GP_Q_FV);
        let bp = k.fvar(GP_QP_FV);
        let (a1, a2) = pr.split(k, lg, a);
        let (ap1, ap2) = pr.split(k, lg, ap);
        let (b1, b2) = pr.split(k, lg, b);
        let (bp1, bp2) = pr.split(k, lg, bp);
        let e1 = app2(k, g.equiv, a1, ap1);
        let e2 = app2(k, h.equiv, a2, ap2);
        let f1 = app2(k, g.equiv, b1, bp1);
        let f2 = app2(k, h.equiv, b2, bp2);
        let and_c = k.const_(lg.and, vec![]);
        let hyp1 = app2(k, and_c, e1, e2);
        let and_c2 = k.const_(lg.and, vec![]);
        let hyp2 = app2(k, and_c2, f1, f2);
        let h1 = k.fvar(GP_HY1_FV);
        let h2 = k.fvar(GP_HY2_FV);
        let l1 = and_left2(k, lg, e1, e2, h1);
        let r1 = and_right2(k, lg, e1, e2, h1);
        let l2 = and_left2(k, lg, f1, f2, h2);
        let r2 = and_right2(k, lg, f1, f2, h2);
        let u = t_app(k, g.op_congr, &[a1, ap1, b1, bp1, l1, l2]);
        let v = t_app(k, h.op_congr, &[a2, ap2, b2, bp2, r1, r2]);
        let lhs1 = app2(k, g.op, a1, b1);
        let rhs1 = app2(k, g.op, ap1, bp1);
        let lhs2 = app2(k, h.op, a2, b2);
        let rhs2 = app2(k, h.op, ap2, bp2);
        let c1 = app2(k, g.equiv, lhs1, rhs1);
        let c2 = app2(k, h.equiv, lhs2, rhs2);
        let body = and_intro2(k, lg, c1, c2, u, v);
        let t = lam_over(k, GP_HY2_FV, hyp2, body);
        let t = lam_over(k, GP_HY1_FV, hyp1, t);
        let t = lam_over(k, GP_QP_FV, carrier, t);
        let t = lam_over(k, GP_Q_FV, carrier, t);
        let t = lam_over(k, GP_PP_FV, carrier, t);
        lam_over(k, GP_P_FV, carrier, t)
    };

    let unit = pr.mk(k, lg, g.e, h.e);

    let inv = {
        let p = k.fvar(GP_P_FV);
        let (p1, p2) = pr.split(k, lg, p);
        let i1 = k.app(g.inv, p1);
        let i2 = k.app(h.inv, p2);
        let body = pr.mk(k, lg, i1, i2);
        lam_over(k, GP_P_FV, carrier, body)
    };

    let inv_congr = {
        let a = k.fvar(GP_P_FV);
        let ap = k.fvar(GP_PP_FV);
        let (a1, a2) = pr.split(k, lg, a);
        let (ap1, ap2) = pr.split(k, lg, ap);
        let e1 = app2(k, g.equiv, a1, ap1);
        let e2 = app2(k, h.equiv, a2, ap2);
        let and_c = k.const_(lg.and, vec![]);
        let hyp = app2(k, and_c, e1, e2);
        let hh = k.fvar(GP_HY1_FV);
        let l = and_left2(k, lg, e1, e2, hh);
        let r = and_right2(k, lg, e1, e2, hh);
        let u = t_app(k, g.inv_congr, &[a1, ap1, l]);
        let v = t_app(k, h.inv_congr, &[a2, ap2, r]);
        let ia1 = k.app(g.inv, a1);
        let iap1 = k.app(g.inv, ap1);
        let ia2 = k.app(h.inv, a2);
        let iap2 = k.app(h.inv, ap2);
        let c1 = app2(k, g.equiv, ia1, iap1);
        let c2 = app2(k, h.equiv, ia2, iap2);
        let body = and_intro2(k, lg, c1, c2, u, v);
        let t = lam_over(k, GP_HY1_FV, hyp, body);
        let t = lam_over(k, GP_PP_FV, carrier, t);
        lam_over(k, GP_P_FV, carrier, t)
    };

    let assoc = {
        let a = k.fvar(GP_P_FV);
        let b = k.fvar(GP_Q_FV);
        let c = k.fvar(GP_R_FV);
        let (a1, a2) = pr.split(k, lg, a);
        let (b1, b2) = pr.split(k, lg, b);
        let (c1, c2) = pr.split(k, lg, c);
        let u = t_app(k, g.assoc, &[a1, b1, c1]);
        let v = t_app(k, h.assoc, &[a2, b2, c2]);
        let ab1 = app2(k, g.op, a1, b1);
        let l1 = app2(k, g.op, ab1, c1);
        let bc1 = app2(k, g.op, b1, c1);
        let r1 = app2(k, g.op, a1, bc1);
        let ab2 = app2(k, h.op, a2, b2);
        let l2 = app2(k, h.op, ab2, c2);
        let bc2 = app2(k, h.op, b2, c2);
        let r2 = app2(k, h.op, a2, bc2);
        let p1 = app2(k, g.equiv, l1, r1);
        let p2 = app2(k, h.equiv, l2, r2);
        let body = and_intro2(k, lg, p1, p2, u, v);
        let t = lam_over(k, GP_R_FV, carrier, body);
        let t = lam_over(k, GP_Q_FV, carrier, t);
        lam_over(k, GP_P_FV, carrier, t)
    };

    // The four one-argument laws share a shape: `And.intro (G.law a.1)
    // (H.law a.2)`, whose conclusion ι-reduces because `e` and `inv` are
    // themselves `Sigma.mk`s.
    let one_arg_law = |k: &mut Kernel, which: usize| -> ExprId {
        let a = k.fvar(GP_P_FV);
        let (a1, a2) = pr.split(k, lg, a);
        let (gl, hl) = match which {
            0 => (g.ident_l, h.ident_l),
            1 => (g.ident_r, h.ident_r),
            2 => (g.inv_l, h.inv_l),
            _ => (g.inv_r, h.inv_r),
        };
        let u = k.app(gl, a1);
        let v = k.app(hl, a2);
        let (l1, r1, l2, r2) = match which {
            0 => {
                let l1 = app2(k, g.op, g.e, a1);
                let l2 = app2(k, h.op, h.e, a2);
                (l1, a1, l2, a2)
            }
            1 => {
                let l1 = app2(k, g.op, a1, g.e);
                let l2 = app2(k, h.op, a2, h.e);
                (l1, a1, l2, a2)
            }
            2 => {
                let i1 = k.app(g.inv, a1);
                let i2 = k.app(h.inv, a2);
                let l1 = app2(k, g.op, i1, a1);
                let l2 = app2(k, h.op, i2, a2);
                (l1, g.e, l2, h.e)
            }
            _ => {
                let i1 = k.app(g.inv, a1);
                let i2 = k.app(h.inv, a2);
                let l1 = app2(k, g.op, a1, i1);
                let l2 = app2(k, h.op, a2, i2);
                (l1, g.e, l2, h.e)
            }
        };
        let p1 = app2(k, g.equiv, l1, r1);
        let p2 = app2(k, h.equiv, l2, r2);
        let body = and_intro2(k, lg, p1, p2, u, v);
        lam_over(k, GP_P_FV, carrier, body)
    };
    let ident_l = one_arg_law(k, 0);
    let ident_r = one_arg_law(k, 1);
    let inv_l = one_arg_law(k, 2);
    let inv_r = one_arg_law(k, 3);

    let body = mk_instance(
        k,
        group,
        &[
            carrier,
            equiv,
            equiv_refl,
            equiv_symm,
            equiv_trans,
            op,
            op_congr,
            unit,
            inv,
            inv_congr,
            assoc,
            ident_l,
            ident_r,
            inv_l,
            inv_r,
        ],
    );
    let value = lam_over(k, GP_H_FV, o_ty, body);
    let value = lam_over(k, GP_G_FV, o_ty, value);
    let ty = arrow(k, o_ty, o_ty);
    let ty = arrow(k, o_ty, ty);

    let name = k.name_str(ns, "grpProd");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// The two projections and the pairing, as BUNDLED `CatS.GrpHom`s.
// ---------------------------------------------------------------------------

/// `CatS.grpProdFst` / `CatS.grpProdSnd`. The congruence conjunct is
/// `And.left`/`And.right` of the product's own `equiv` — the projection is
/// congruent *by definition of the product setoid* — and the `op` conjunct is
/// `equivRefl`, free because `Sigma.fst (Sigma.mk a b)` ι-reduces.
fn declare_grp_prod_proj(
    k: &mut Kernel,
    lg: &LogicPrelude,
    group: &RecordNames,
    is_grp_hom: NameId,
    grp_hom: NameId,
    grp_prod: NameId,
    ns: NameId,
    second: bool,
    suffix: &str,
) -> Result<NameId, KernelError> {
    let o_ty = k.const_(group.ind, vec![]);
    let gv = k.fvar(GP_G_FV);
    let hv = k.fvar(GP_H_FV);
    let g = grp_of(k, group, gv);
    let h = grp_of(k, group, hv);
    let pr = Pair {
        ca: g.carrier,
        cb: h.carrier,
    };
    let gpc = k.const_(grp_prod, vec![]);
    let pv = app2(k, gpc, gv, hv);
    let p = grp_of(k, group, pv);
    let tgt_v = if second { hv } else { gv };
    let tgt = if second { h } else { g };

    let f_ty = arrow(k, p.carrier, tgt.carrier);
    let ihc = k.const_(is_grp_hom, vec![]);
    let pred = app2(k, ihc, pv, tgt_v);

    // fun x => x.1  /  fun x => x.2
    let fnv = {
        let x = k.fvar(GP_P_FV);
        let body = if second {
            pr.snd(k, lg, x)
        } else {
            pr.fst(k, lg, x)
        };
        lam_over(k, GP_P_FV, p.carrier, body)
    };

    let congr_p = hom_congr_stmt(k, &p, &tgt, fnv);
    let op_p = hom_op_stmt(k, &p, &tgt, fnv);

    let congr_v = {
        let x = k.fvar(GP_P_FV);
        let y = k.fvar(GP_Q_FV);
        let (x1, x2) = pr.split(k, lg, x);
        let (y1, y2) = pr.split(k, lg, y);
        let e1 = app2(k, g.equiv, x1, y1);
        let e2 = app2(k, h.equiv, x2, y2);
        let hyp = app2(k, p.equiv, x, y);
        let hh = k.fvar(GP_HY1_FV);
        let body = if second {
            and_right2(k, lg, e1, e2, hh)
        } else {
            and_left2(k, lg, e1, e2, hh)
        };
        let t = lam_over(k, GP_HY1_FV, hyp, body);
        let t = lam_over(k, GP_Q_FV, p.carrier, t);
        lam_over(k, GP_P_FV, p.carrier, t)
    };

    let op_v = {
        let x = k.fvar(GP_P_FV);
        let y = k.fvar(GP_Q_FV);
        let (x1, x2) = pr.split(k, lg, x);
        let (y1, y2) = pr.split(k, lg, y);
        let rhs = if second {
            app2(k, h.op, x2, y2)
        } else {
            app2(k, g.op, x1, y1)
        };
        let body = k.app(tgt.refl, rhs);
        let t = lam_over(k, GP_Q_FV, p.carrier, body);
        lam_over(k, GP_P_FV, p.carrier, t)
    };

    let proof = and_intro2(k, lg, congr_p, op_p, congr_v, op_v);
    let body = sub1_mk(k, lg, f_ty, pred, fnv, proof);
    let value = lam_over(k, GP_H_FV, o_ty, body);
    let value = lam_over(k, GP_G_FV, o_ty, value);

    let ghc = k.const_(grp_hom, vec![]);
    let concl = app2(k, ghc, pv, tgt_v);
    let ty = pi_over(k, GP_H_FV, o_ty, concl);
    let ty = pi_over(k, GP_G_FV, o_ty, ty);

    let name = k.name_str(ns, suffix);
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `CatS.grpProdMed : Π (G H X : AlgS.Group), CatS.GrpHom X G -> CatS.GrpHom
/// X H -> CatS.GrpHom X (CatS.grpProd G H)` — the mediating map, GIVEN as
/// data (universal-property template part 2), not extracted from an `Exists`.
fn declare_grp_prod_med(
    k: &mut Kernel,
    lg: &LogicPrelude,
    group: &RecordNames,
    is_grp_hom: NameId,
    is_grp_hom_congr: NameId,
    grp_hom: NameId,
    grp_prod: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let o_ty = k.const_(group.ind, vec![]);
    let gv = k.fvar(GP_G_FV);
    let hv = k.fvar(GP_H_FV);
    let xv = k.fvar(GP_X_FV);
    let g = grp_of(k, group, gv);
    let h = grp_of(k, group, hv);
    let x = grp_of(k, group, xv);
    let pr = Pair {
        ca: g.carrier,
        cb: h.carrier,
    };
    let gpc = k.const_(grp_prod, vec![]);
    let pv = app2(k, gpc, gv, hv);
    let p = grp_of(k, group, pv);

    let ghc = k.const_(grp_hom, vec![]);
    let u_ty = app2(k, ghc, xv, gv);
    let ghc2 = k.const_(grp_hom, vec![]);
    let v_ty = app2(k, ghc2, xv, hv);
    let u = k.fvar(GP_U_FV);
    let v = k.fvar(GP_V_FV);

    let u_alpha = arrow(k, x.carrier, g.carrier);
    let ihc = k.const_(is_grp_hom, vec![]);
    let u_pred = app2(k, ihc, xv, gv);
    let v_alpha = arrow(k, x.carrier, h.carrier);
    let ihc2 = k.const_(is_grp_hom, vec![]);
    let v_pred = app2(k, ihc2, xv, hv);

    let uf = sub1_val(k, lg, u_alpha, u_pred, u);
    let vf = sub1_val(k, lg, v_alpha, v_pred, v);
    let up = sub1_prop(k, lg, u_alpha, u_pred, u);
    let vp = sub1_prop(k, lg, v_alpha, v_pred, v);

    // fun z => (u z, v z)
    let fnv = {
        let z = k.fvar(GP_EL_FV);
        let uz = k.app(uf, z);
        let vz = k.app(vf, z);
        let body = pr.mk(k, lg, uz, vz);
        lam_over(k, GP_EL_FV, x.carrier, body)
    };

    let ihcc = k.const_(is_grp_hom_congr, vec![]);
    let u_congr = t_app(k, ihcc, &[xv, gv, uf, up]);
    let ihcc2 = k.const_(is_grp_hom_congr, vec![]);
    let v_congr = t_app(k, ihcc2, &[xv, hv, vf, vp]);
    let u_op = {
        let cs = hom_congr_stmt(k, &x, &g, uf);
        let os = hom_op_stmt(k, &x, &g, uf);
        and_right2(k, lg, cs, os, up)
    };
    let v_op = {
        let cs = hom_congr_stmt(k, &x, &h, vf);
        let os = hom_op_stmt(k, &x, &h, vf);
        and_right2(k, lg, cs, os, vp)
    };

    let congr_p = hom_congr_stmt(k, &x, &p, fnv);
    let op_p = hom_op_stmt(k, &x, &p, fnv);

    let congr_v = {
        let a = k.fvar(GP_P_FV);
        let b = k.fvar(GP_Q_FV);
        let hyp = app2(k, x.equiv, a, b);
        let hh = k.fvar(GP_HY1_FV);
        let ua = k.app(uf, a);
        let ub = k.app(uf, b);
        let va = k.app(vf, a);
        let vb = k.app(vf, b);
        let e1 = app2(k, g.equiv, ua, ub);
        let e2 = app2(k, h.equiv, va, vb);
        let w1 = t_app(k, u_congr, &[a, b, hh]);
        let w2 = t_app(k, v_congr, &[a, b, hh]);
        let body = and_intro2(k, lg, e1, e2, w1, w2);
        let t = lam_over(k, GP_HY1_FV, hyp, body);
        let t = lam_over(k, GP_Q_FV, x.carrier, t);
        lam_over(k, GP_P_FV, x.carrier, t)
    };

    let op_v = {
        let a = k.fvar(GP_P_FV);
        let b = k.fvar(GP_Q_FV);
        let ab = app2(k, x.op, a, b);
        let u_ab = k.app(uf, ab);
        let v_ab = k.app(vf, ab);
        let ua = k.app(uf, a);
        let ub = k.app(uf, b);
        let va = k.app(vf, a);
        let vb = k.app(vf, b);
        let r1 = app2(k, g.op, ua, ub);
        let r2 = app2(k, h.op, va, vb);
        let e1 = app2(k, g.equiv, u_ab, r1);
        let e2 = app2(k, h.equiv, v_ab, r2);
        let w1 = t_app(k, u_op, &[a, b]);
        let w2 = t_app(k, v_op, &[a, b]);
        let body = and_intro2(k, lg, e1, e2, w1, w2);
        let t = lam_over(k, GP_Q_FV, x.carrier, body);
        lam_over(k, GP_P_FV, x.carrier, t)
    };

    let proof = and_intro2(k, lg, congr_p, op_p, congr_v, op_v);
    let alpha = arrow(k, x.carrier, p.carrier);
    let ihc3 = k.const_(is_grp_hom, vec![]);
    let pred = app2(k, ihc3, xv, pv);
    let body = sub1_mk(k, lg, alpha, pred, fnv, proof);

    let value = lam_over(k, GP_V_FV, v_ty, body);
    let value = lam_over(k, GP_U_FV, u_ty, value);
    let value = lam_over(k, GP_X_FV, o_ty, value);
    let value = lam_over(k, GP_H_FV, o_ty, value);
    let value = lam_over(k, GP_G_FV, o_ty, value);

    let ghc3 = k.const_(grp_hom, vec![]);
    let concl = app2(k, ghc3, xv, pv);
    let ty = arrow(k, v_ty, concl);
    let ty = arrow(k, u_ty, ty);
    let ty = pi_over(k, GP_X_FV, o_ty, ty);
    let ty = pi_over(k, GP_H_FV, o_ty, ty);
    let ty = pi_over(k, GP_G_FV, o_ty, ty);

    let name = k.name_str(ns, "grpProdMed");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `CatS.grp_isProduct` — **the product of two groups**, as the universal
/// property in `CatS.grp`. Both triangles are `equivRefl` (ι-reduction on
/// `Sigma.fst`/`Sigma.snd` of a `Sigma.mk`); uniqueness is one `And.intro`,
/// because the product setoid's `equiv` IS the conjunction of the two
/// hypotheses.
fn declare_grp_is_product(
    k: &mut Kernel,
    lg: &LogicPrelude,
    large: &RecordNames,
    group: &RecordNames,
    is_grp_hom: NameId,
    is_product_large: NameId,
    grp: NameId,
    grp_prod: NameId,
    grp_prod_fst: NameId,
    grp_prod_snd: NameId,
    grp_prod_med: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let o_ty = k.const_(group.ind, vec![]);
    let gv = k.fvar(GP_G_FV);
    let hv = k.fvar(GP_H_FV);
    let g = grp_of(k, group, gv);
    let h = grp_of(k, group, hv);
    let gpc = k.const_(grp_prod, vec![]);
    let pv = app2(k, gpc, gv, hv);

    let grpc = k.const_(grp, vec![]);
    let c = cat_of(k, large, grpc);

    let f1c = k.const_(grp_prod_fst, vec![]);
    let pr1 = app2(k, f1c, gv, hv);
    let f2c = k.const_(grp_prod_snd, vec![]);
    let pr2 = app2(k, f2c, gv, hv);
    let medc = k.const_(grp_prod_med, vec![]);
    let med = app2(k, medc, gv, hv);

    let props = product_conjuncts(k, &c, false, gv, hv, pv, pr1, pr2, med);

    // Binder types, exactly as `product_conjuncts` states them.
    let xv = k.fvar(PX_FV);
    let f_ty = c.hom_ty(k, xv, gv);
    let g_ty = c.hom_ty(k, xv, hv);
    let m_ty = c.hom_ty(k, xv, pv);
    let x = grp_of(k, group, xv);

    let ihc = k.const_(is_grp_hom, vec![]);
    let f_pred = app2(k, ihc, xv, gv);
    let f_alpha = arrow(k, x.carrier, g.carrier);
    let ihc2 = k.const_(is_grp_hom, vec![]);
    let g_pred = app2(k, ihc2, xv, hv);
    let g_alpha = arrow(k, x.carrier, h.carrier);

    let fm = k.fvar(PF_FV);
    let gm = k.fvar(PG_FV);
    let ff = sub1_val(k, lg, f_alpha, f_pred, fm);
    let gf = sub1_val(k, lg, g_alpha, g_pred, gm);

    // Triangle values: `fun x f g el => <tgt>.equivRefl (val f el)`.
    let triangle = |k: &mut Kernel, second: bool| -> ExprId {
        let el = k.fvar(GP_EL_FV);
        let (refl, fv) = if second { (h.refl, gf) } else { (g.refl, ff) };
        let body = {
            let at = k.app(fv, el);
            k.app(refl, at)
        };
        let t = lam_over(k, GP_EL_FV, x.carrier, body);
        let t = lam_over(k, PG_FV, g_ty, t);
        let t = lam_over(k, PF_FV, f_ty, t);
        lam_over(k, PX_FV, c.obj, t)
    };
    let v1 = triangle(k, false);
    let v2 = triangle(k, true);

    let v3 = {
        let m = k.fvar(PM_FV);
        let h1_ty = leg_eq(k, &c, false, xv, pv, gv, pr1, m, fm);
        let h2_ty = leg_eq(k, &c, false, xv, pv, hv, pr2, m, gm);
        let h1 = k.fvar(PH1_FV);
        let h2 = k.fvar(PH2_FV);
        let el = k.fvar(GP_EL_FV);

        let p_alpha = {
            let p = grp_of(k, group, pv);
            arrow(k, x.carrier, p.carrier)
        };
        let ihc3 = k.const_(is_grp_hom, vec![]);
        let p_pred = app2(k, ihc3, xv, pv);
        let mf = sub1_val(k, lg, p_alpha, p_pred, m);
        let m_el = k.app(mf, el);
        let pr = Pair {
            ca: g.carrier,
            cb: h.carrier,
        };
        let (m1, m2) = pr.split(k, lg, m_el);
        let f_el = k.app(ff, el);
        let g_el = k.app(gf, el);
        let e1 = app2(k, g.equiv, m1, f_el);
        let e2 = app2(k, h.equiv, m2, g_el);
        let w1 = k.app(h1, el);
        let w2 = k.app(h2, el);
        let body = and_intro2(k, lg, e1, e2, w1, w2);
        let t = lam_over(k, GP_EL_FV, x.carrier, body);
        let t = lam_over(k, PH2_FV, h2_ty, t);
        let t = lam_over(k, PH1_FV, h1_ty, t);
        let t = lam_over(k, PM_FV, m_ty, t);
        let t = lam_over(k, PG_FV, g_ty, t);
        let t = lam_over(k, PF_FV, f_ty, t);
        lam_over(k, PX_FV, c.obj, t)
    };

    let value = intro3(k, lg, &props, &[v1, v2, v3]);
    let value = lam_over(k, GP_H_FV, o_ty, value);
    let value = lam_over(k, GP_G_FV, o_ty, value);

    let iplc = k.const_(is_product_large, vec![]);
    let concl = t_app(k, iplc, &[grpc, gv, hv, pv, pr1, pr2, med]);
    let ty = pi_over(k, GP_H_FV, o_ty, concl);
    let ty = pi_over(k, GP_G_FV, o_ty, ty);

    thm(k, ns, "grp_isProduct", ty, value)
}

// ---------------------------------------------------------------------------
// Names.
// ---------------------------------------------------------------------------

/// Everything this module declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProductNames {
    /// `CatS.IsProduct` — over `CatS.Category`.
    pub is_product: NameId,
    /// `CatS.IsCoproduct` — the dual, over `CatS.Category`.
    pub is_coproduct: NameId,
    /// `CatS.IsProductLarge` — over `CatS.CategoryLarge`, which is where
    /// `CatS.grp` lives.
    pub is_product_large: NameId,
    /// `CatS.Iso` — over `CatS.Category`.
    pub iso: NameId,
    /// `CatS.product_unique_upto_iso`.
    pub product_unique_upto_iso: NameId,
    /// `CatS.indiscrete_isProduct`.
    pub indiscrete_is_product: NameId,
    /// `CatS.indiscrete_isCoproduct`.
    pub indiscrete_is_coproduct: NameId,
    /// `CatS.grpProd : AlgS.Group -> AlgS.Group -> AlgS.Group`.
    pub grp_prod: NameId,
    /// `CatS.grpProdFst`.
    pub grp_prod_fst: NameId,
    /// `CatS.grpProdSnd`.
    pub grp_prod_snd: NameId,
    /// `CatS.grpProdMed` — the bundled pairing.
    pub grp_prod_med: NameId,
    /// `CatS.grp_isProduct` — **the product of two groups**.
    pub grp_is_product: NameId,
}

#[cfg(test)]
impl ProductNames {
    #[must_use]
    pub fn all(&self) -> [NameId; 12] {
        [
            self.is_product,
            self.is_coproduct,
            self.is_product_large,
            self.iso,
            self.product_unique_upto_iso,
            self.indiscrete_is_product,
            self.indiscrete_is_coproduct,
            self.grp_prod,
            self.grp_prod_fst,
            self.grp_prod_snd,
            self.grp_prod_med,
            self.grp_is_product,
        ]
    }

    #[must_use]
    pub fn theorems(&self) -> [NameId; 4] {
        [
            self.product_unique_upto_iso,
            self.indiscrete_is_product,
            self.indiscrete_is_coproduct,
            self.grp_is_product,
        ]
    }
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

/// Everything the group half of this module borrows from its two neighbours.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ProductDeps {
    /// `CatS.IsGrpHom` (from `category_setoid.rs`).
    pub is_grp_hom: NameId,
    /// `CatS.isGrpHom_congr` (from `groups.rs`).
    pub is_grp_hom_congr: NameId,
    /// `CatS.GrpHom` (from `groups.rs`).
    pub grp_hom: NameId,
    /// `CatS.grp` (from `groups.rs`).
    pub grp: NameId,
}

/// Declare the whole product/coproduct layer.
pub(crate) fn declare_products(
    k: &mut Kernel,
    lg: &LogicPrelude,
    recs: &CategoryRecords,
    group: &RecordNames,
    indiscrete: NameId,
    deps: ProductDeps,
    ns: NameId,
) -> Result<ProductNames, KernelError> {
    let is_product = declare_is_product(k, lg, &recs.category, ns, false, "IsProduct")?;
    let is_coproduct = declare_is_product(k, lg, &recs.category, ns, true, "IsCoproduct")?;
    let is_product_large =
        declare_is_product(k, lg, &recs.category_large, ns, false, "IsProductLarge")?;
    let iso = declare_iso(k, lg, &recs.category, ns, "Iso")?;
    let product_unique_upto_iso =
        declare_product_unique_upto_iso(k, lg, &recs.category, is_product, iso, ns)?;
    let indiscrete_is_product =
        declare_indiscrete_is_product(k, lg, &recs.category, indiscrete, is_product, ns, false)?;
    let indiscrete_is_coproduct =
        declare_indiscrete_is_product(k, lg, &recs.category, indiscrete, is_coproduct, ns, true)?;

    let grp_prod = declare_grp_prod(k, lg, group, ns)?;
    let grp_prod_fst = declare_grp_prod_proj(
        k,
        lg,
        group,
        deps.is_grp_hom,
        deps.grp_hom,
        grp_prod,
        ns,
        false,
        "grpProdFst",
    )?;
    let grp_prod_snd = declare_grp_prod_proj(
        k,
        lg,
        group,
        deps.is_grp_hom,
        deps.grp_hom,
        grp_prod,
        ns,
        true,
        "grpProdSnd",
    )?;
    let grp_prod_med = declare_grp_prod_med(
        k,
        lg,
        group,
        deps.is_grp_hom,
        deps.is_grp_hom_congr,
        deps.grp_hom,
        grp_prod,
        ns,
    )?;
    let grp_is_product = declare_grp_is_product(
        k,
        lg,
        &recs.category_large,
        group,
        deps.is_grp_hom,
        is_product_large,
        deps.grp,
        grp_prod,
        grp_prod_fst,
        grp_prod_snd,
        grp_prod_med,
        ns,
    )?;

    Ok(ProductNames {
        is_product,
        is_coproduct,
        is_product_large,
        iso,
        product_unique_upto_iso,
        indiscrete_is_product,
        indiscrete_is_coproduct,
        grp_prod,
        grp_prod_fst,
        grp_prod_snd,
        grp_prod_med,
        grp_is_product,
    })
}

#[cfg(test)]
mod products_tests;
