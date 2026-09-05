//! **The `Sigma` residue of ADR-1620**: the category of groups, the category
//! of monoids, the forgetful functor between them, and ℕ as an initial object
//! — the three things ADR-1620 measured as blocked on one missing kernel
//! feature, which ADR-1613 then landed.
//!
//! ADR-1620's measurement 3 is worth restating, because it is the reason this
//! module is a separate file rather than a patch to the one beside it. What
//! blocked the category of `AlgS.Group` objects was **not** the universe
//! layer: `CatS.grpIndiscrete : CatS.CategoryLarge` already had
//! `obj ≡ AlgS.Group`, read from the kernel. What blocked it was the
//! *hom-family*, and the two escapes that avoid a dependent pair were each
//! measured to fail:
//!
//! 1. `hom G H := G.carrier -> H.carrier` (all functions) makes `compCongr`
//!    **false** — from `g ~ g'` and `f ~ f'` pointwise, `g (f a) ~ g' (f' a)`
//!    needs `g'` to respect `G.equiv`, which an arbitrary function does not;
//! 2. the *respectful relation* is only a partial equivalence, so `homRefl`
//!    cannot be a field.
//!
//! Bundling repairs exactly (1): if the hom carries its own congruence proof,
//! `compCongr` is one `equivTrans` away. So the hom-family here is
//!
//! ```text
//! CatS.GrpHom G H := Subtype.{1} (G.carrier -> H.carrier) (CatS.IsGrpHom G H)
//! ```
//!
//! and `Subtype` is the right half of the ADR-1613 family — **not** `Sigma`,
//! for a reason the levels decide rather than taste: `Subtype.{u}` lands at
//! `Sort (max 1 u)`, so at `u := 1` it lands at `Sort 1`, which is exactly
//! what `CatS.CategoryLarge`'s `hom` field demands. `Sigma.{u,v}` lands one
//! universe higher (`Sort (max u v + 1)`) and would not fit.
//!
//! ## What each construction costs over setoids
//!
//! Every algebra lane since ADR-1595 reports this, because ADR-1595 is
//! reversible on the evidence. For a bundled-hom category the count is
//! **one real proof per category and three pointwise liftings**:
//!
//! | category field | how it is filled | new proof? |
//! |---|---|---|
//! | `homEquiv` | pointwise `B.equiv` on `Subtype.val`, ignoring the proof | — |
//! | `homRefl`/`homSymm`/`homTrans` | `B.equivRefl`/`Symm`/`Trans` under one binder | 3 liftings |
//! | `id`/`comp` | `Subtype.mk` over `isXHom_id`/`isXHom_comp` | — |
//! | `compCongr` | `B.equivTrans (uCongr … (hu x)) (hv …)` | **1** |
//! | `idL`/`idR`/`assoc` | `B.equivRefl`, free by ι-reduction on `Subtype.val` | — |
//!
//! `idL`, `idR` and `assoc` are free *because* `Subtype.val (Subtype.mk f h)`
//! ι-reduces: both sides of each law reduce to the same function, so the law
//! is reflexivity of the object's own `equiv`. That is the same mechanism
//! ADR-1613 measured at the image group (fourteen of fifteen fields free).
//!
//! The `Eq`-flavoured counterfactual does not exist: over `Eq` the hom-setoid
//! would need `Eq` between functions, which is `funext` (ADR-1595, still
//! out).
//!
//! ## Three universe findings
//!
//! - **`CatS.grp` and `CatS.mon` need `CatS.CategoryLarge`, not
//!   `CatS.Category`.** `AlgS.Group : Sort 2`, and `CatS.Category.obj` is a
//!   `Sort 1`. The guard is not involved; the small record simply cannot hold
//!   these objects. `declare_record`'s own `sort1Control` still fires for
//!   every record declared here.
//! - **`CatS.FunctorLarge` is a fourth record at `Sort 3`**, because
//!   `CatS.Functor`'s `src`/`tgt` fields are `CatS.Category`-typed and a
//!   record's field types are fixed at declaration. It is the SAME seven-field
//!   list ([`super::functor_fields`]) at `l1 := 2`, `l2 := 3` — ADR-1620's
//!   measurement 2a (a record CAN hold a record) applied one level up, and it
//!   admits.
//! - **The objects of pointed unary algebras are `Sort 2`**, so that category
//!   is `CategoryLarge` too. `CatS.PtAlg := Sigma.{1,0} (Sort 1) (fun N =>
//!   Sigma.{0,0} N (fun _ => N -> N))` lands at `Sort (max 1 0 + 1) = Sort 2`.
//!   Here it IS `Sigma` and not `Subtype`, because the second component is
//!   data and not a proof.
//!
//! ## ℕ as an initial object, and what it is not
//!
//! [`CatS.natPtAlg_isInitial`] is the categorical form of ADR-1610's
//! `Nat.Peano.initial`. It is **re-proved here, not cited**, and the reason is
//! build order rather than mathematics: `Nat.Peano.iter`/`Nat.Peano.initial`
//! live in the `characterization` package, which is built ON TOP of this
//! prelude, while `CatS.*` lands at the `AlgS` position inside it. The
//! mediating map here is `Nat.rec` at the constant motive `fun _ => Q.carrier`
//! — definitionally the same map `Nat.Peano.iter` is — and its two structure
//! equations are `Eq.refl`, exactly as ADR-1610 reported.
//!
//! Uniqueness is `Nat.rec` induction: the zero case is `Eq.symm` of the
//! morphism's own zero law, and the successor case is one `congrArg` plus one
//! `Eq.trans`. Two steps, no axioms.

#![allow(clippy::too_many_arguments, clippy::similar_names)]

use super::*;
use crate::level::LevelId;
#[allow(unused_imports)]
use crate::nat_prelude::structures::{eq_of, refl_of, symm_of, trans_of};

// ---------------------------------------------------------------------------
// Free variables. Disjoint from `category_setoid`'s own 25_000..25_130 block.
// ---------------------------------------------------------------------------

const G_A_FV: u64 = 25_200;
const G_B_FV: u64 = 25_201;
const G_C_FV: u64 = 25_202;
const G_D_FV: u64 = 25_203;

const H_U_FV: u64 = 25_210;
const H_V_FV: u64 = 25_211;
const H_W_FV: u64 = 25_212;
const H_U2_FV: u64 = 25_213;
const H_V2_FV: u64 = 25_214;

const P_1_FV: u64 = 25_220;
const P_2_FV: u64 = 25_221;

const X_A_FV: u64 = 25_230;
const X_B_FV: u64 = 25_231;

const F_1_FV: u64 = 25_240;
const F_2_FV: u64 = 25_241;
const PF_1_FV: u64 = 25_242;
const PF_2_FV: u64 = 25_243;

const SCR_FV: u64 = 25_250;

const N_FV: u64 = 25_260;
const IH_FV: u64 = 25_261;
const Q_FV: u64 = 25_262;
const GH_FV: u64 = 25_263;

// ---------------------------------------------------------------------------
// `Subtype` vocabulary at one level.
// ---------------------------------------------------------------------------

/// `Subtype.{l} alpha pred`.
fn sub_ty(k: &mut Kernel, lg: &LogicPrelude, l: LevelId, alpha: ExprId, pred: ExprId) -> ExprId {
    let head = k.const_(lg.sigma.subtype, vec![l]);
    app2(k, head, alpha, pred)
}

/// `Subtype.val.{l} alpha pred s`.
fn sub_val(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l: LevelId,
    alpha: ExprId,
    pred: ExprId,
    s: ExprId,
) -> ExprId {
    let head = k.const_(lg.sigma.subtype_val, vec![l]);
    t_app(k, head, &[alpha, pred, s])
}

/// `Subtype.property.{l} alpha pred s`.
fn sub_prop(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l: LevelId,
    alpha: ExprId,
    pred: ExprId,
    s: ExprId,
) -> ExprId {
    let head = k.const_(lg.sigma.subtype_property, vec![l]);
    t_app(k, head, &[alpha, pred, s])
}

/// `Subtype.mk.{l} alpha pred v p`.
fn sub_mk(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l: LevelId,
    alpha: ExprId,
    pred: ExprId,
    v: ExprId,
    p: ExprId,
) -> ExprId {
    let head = k.const_(lg.sigma.subtype_mk, vec![l]);
    t_app(k, head, &[alpha, pred, v, p])
}

// ---------------------------------------------------------------------------
// The three statements a bundled algebra morphism makes.
// ---------------------------------------------------------------------------

/// The `AlgS` selectors of one object, at the five indices `AlgS.Monoid` and
/// `AlgS.Group` share (`carrier`, `equiv`, its three laws, `op`, `e`).
#[derive(Clone, Copy)]
struct Ob {
    carrier: ExprId,
    equiv: ExprId,
    refl: ExprId,
    symm: ExprId,
    trans: ExprId,
    op: ExprId,
    e: ExprId,
}

/// `AlgS.Monoid` and `AlgS.Group` agree on indices 0-5 and on `e := 7`; only
/// what follows `e` differs. That is why one builder serves both categories.
fn ob_of(k: &mut Kernel, rec: &RecordNames, v: ExprId) -> Ob {
    use algs::group::{CARRIER, E, EQUIV, EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, OP};
    Ob {
        carrier: sel(k, rec, CARRIER, v),
        equiv: sel(k, rec, EQUIV, v),
        refl: sel(k, rec, EQUIV_REFL, v),
        symm: sel(k, rec, EQUIV_SYMM, v),
        trans: sel(k, rec, EQUIV_TRANS, v),
        op: sel(k, rec, OP, v),
        e: sel(k, rec, E, v),
    }
}

/// `forall a b, A.equiv a b -> B.equiv (f a) (f b)`.
fn congr_stmt(k: &mut Kernel, a: &Ob, b: &Ob, f: ExprId) -> ExprId {
    let x = k.fvar(X_A_FV);
    let y = k.fvar(X_B_FV);
    let hyp = app2(k, a.equiv, x, y);
    let fx = k.app(f, x);
    let fy = k.app(f, y);
    let concl = app2(k, b.equiv, fx, fy);
    let t = arrow(k, hyp, concl);
    let t = pi_over(k, X_B_FV, a.carrier, t);
    pi_over(k, X_A_FV, a.carrier, t)
}

/// `forall a b, B.equiv (f (A.op a b)) (B.op (f a) (f b))`.
fn op_stmt(k: &mut Kernel, a: &Ob, b: &Ob, f: ExprId) -> ExprId {
    let x = k.fvar(X_A_FV);
    let y = k.fvar(X_B_FV);
    let xy = app2(k, a.op, x, y);
    let lhs = k.app(f, xy);
    let fx = k.app(f, x);
    let fy = k.app(f, y);
    let rhs = app2(k, b.op, fx, fy);
    let body = app2(k, b.equiv, lhs, rhs);
    let t = pi_over(k, X_B_FV, a.carrier, body);
    pi_over(k, X_A_FV, a.carrier, t)
}

/// `B.equiv (f A.e) B.e` — the conjunct a MONOID morphism carries and a group
/// morphism does not need to (`AlgS.Hom.mapOne` derives it).
fn unit_stmt(k: &mut Kernel, a: &Ob, b: &Ob, f: ExprId) -> ExprId {
    let fe = k.app(f, a.e);
    app2(k, b.equiv, fe, b.e)
}

// ---------------------------------------------------------------------------
// `CatS.IsMonHom` and its two laws.
// ---------------------------------------------------------------------------

/// `CatS.IsMonHom M N f := congr ∧ (op ∧ unit)` — a monoid morphism is a group
/// morphism's two conjuncts PLUS unit preservation, which is not derivable
/// without inverses.
fn declare_is_mon_hom(
    k: &mut Kernel,
    lg: &LogicPrelude,
    monoid: &RecordNames,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let m_ty = k.const_(monoid.ind, vec![]);
    let mv = k.fvar(G_A_FV);
    let nv = k.fvar(G_B_FV);
    let a = ob_of(k, monoid, mv);
    let b = ob_of(k, monoid, nv);
    let f_ty = arrow(k, a.carrier, b.carrier);
    let f = k.fvar(F_1_FV);

    let props = [
        congr_stmt(k, &a, &b, f),
        op_stmt(k, &a, &b, f),
        unit_stmt(k, &a, &b, f),
    ];
    let body = and3(k, lg, &props);
    let value = lam_over(k, F_1_FV, f_ty, body);
    let value = lam_over(k, G_B_FV, m_ty, value);
    let value = lam_over(k, G_A_FV, m_ty, value);

    let l0 = k.level_zero();
    let prop = k.sort(l0);
    let ty = pi_over(k, F_1_FV, f_ty, prop);
    let ty = pi_over(k, G_B_FV, m_ty, ty);
    let ty = pi_over(k, G_A_FV, m_ty, ty);

    let name = k.name_str(ns, "IsMonHom");
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;
    Ok(name)
}

/// `CatS.isMonHom_id : forall M, IsMonHom M M (fun a => a)`.
fn declare_is_mon_hom_id(
    k: &mut Kernel,
    lg: &LogicPrelude,
    monoid: &RecordNames,
    is_mon_hom: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let m_ty = k.const_(monoid.ind, vec![]);
    let mv = k.fvar(G_A_FV);
    let a = ob_of(k, monoid, mv);
    let idf = {
        let x = k.fvar(X_A_FV);
        lam_over(k, X_A_FV, a.carrier, x)
    };
    let imh = k.const_(is_mon_hom, vec![]);
    let concl = t_app(k, imh, &[mv, mv, idf]);
    let ty = pi_over(k, G_A_FV, m_ty, concl);

    let props = [
        congr_stmt(k, &a, &a, idf),
        op_stmt(k, &a, &a, idf),
        unit_stmt(k, &a, &a, idf),
    ];
    let v_congr = {
        let x = k.fvar(X_A_FV);
        let y = k.fvar(X_B_FV);
        let hyp = app2(k, a.equiv, x, y);
        let hh = k.fvar(P_1_FV);
        let t = lam_over(k, P_1_FV, hyp, hh);
        let t = lam_over(k, X_B_FV, a.carrier, t);
        lam_over(k, X_A_FV, a.carrier, t)
    };
    let v_op = {
        let x = k.fvar(X_A_FV);
        let y = k.fvar(X_B_FV);
        let xy = app2(k, a.op, x, y);
        let body = k.app(a.refl, xy);
        let t = lam_over(k, X_B_FV, a.carrier, body);
        lam_over(k, X_A_FV, a.carrier, t)
    };
    let v_unit = k.app(a.refl, a.e);
    let value = intro3(k, lg, &props, &[v_congr, v_op, v_unit]);
    let value = lam_over(k, G_A_FV, m_ty, value);

    thm(k, ns, "isMonHom_id", ty, value)
}

/// `CatS.isMonHom_comp` — monoid morphisms compose. The unit conjunct is the
/// only one a group morphism gets for free: `g (f e) ~ g e' ~ e''`.
fn declare_is_mon_hom_comp(
    k: &mut Kernel,
    lg: &LogicPrelude,
    monoid: &RecordNames,
    is_mon_hom: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let m_ty = k.const_(monoid.ind, vec![]);
    let mv = k.fvar(G_A_FV);
    let nv = k.fvar(G_B_FV);
    let pv = k.fvar(G_C_FV);
    let a = ob_of(k, monoid, mv);
    let b = ob_of(k, monoid, nv);
    let c = ob_of(k, monoid, pv);

    let f_ty = arrow(k, a.carrier, b.carrier);
    let g_ty = arrow(k, b.carrier, c.carrier);
    let f = k.fvar(F_1_FV);
    let g = k.fvar(F_2_FV);

    let imh = k.const_(is_mon_hom, vec![]);
    let hf_ty = t_app(k, imh, &[mv, nv, f]);
    let imh2 = k.const_(is_mon_hom, vec![]);
    let hg_ty = t_app(k, imh2, &[nv, pv, g]);
    let hf = k.fvar(PF_1_FV);
    let hg = k.fvar(PF_2_FV);

    let comp_fn = {
        let x = k.fvar(X_A_FV);
        let fx = k.app(f, x);
        let body = k.app(g, fx);
        lam_over(k, X_A_FV, a.carrier, body)
    };

    let f_props = [
        congr_stmt(k, &a, &b, f),
        op_stmt(k, &a, &b, f),
        unit_stmt(k, &a, &b, f),
    ];
    let g_props = [
        congr_stmt(k, &b, &c, g),
        op_stmt(k, &b, &c, g),
        unit_stmt(k, &b, &c, g),
    ];
    let f_congr = project3(k, lg, &f_props, hf, 0);
    let f_op = project3(k, lg, &f_props, hf, 1);
    let f_unit = project3(k, lg, &f_props, hf, 2);
    let g_congr = project3(k, lg, &g_props, hg, 0);
    let g_op = project3(k, lg, &g_props, hg, 1);
    let g_unit = project3(k, lg, &g_props, hg, 2);

    let v_congr = {
        let x = k.fvar(X_A_FV);
        let y = k.fvar(X_B_FV);
        let hyp = app2(k, a.equiv, x, y);
        let hh = k.fvar(P_1_FV);
        let inner = t_app(k, f_congr, &[x, y, hh]);
        let fx = k.app(f, x);
        let fy = k.app(f, y);
        let body = t_app(k, g_congr, &[fx, fy, inner]);
        let t = lam_over(k, P_1_FV, hyp, body);
        let t = lam_over(k, X_B_FV, a.carrier, t);
        lam_over(k, X_A_FV, a.carrier, t)
    };
    let v_op = {
        let x = k.fvar(X_A_FV);
        let y = k.fvar(X_B_FV);
        let xy = app2(k, a.op, x, y);
        let f_xy = k.app(f, xy);
        let fx = k.app(f, x);
        let fy = k.app(f, y);
        let b_fx_fy = app2(k, b.op, fx, fy);
        let step1 = {
            let h = t_app(k, f_op, &[x, y]);
            t_app(k, g_congr, &[f_xy, b_fx_fy, h])
        };
        let step2 = t_app(k, g_op, &[fx, fy]);
        let p = k.app(g, f_xy);
        let q = k.app(g, b_fx_fy);
        let gx = k.app(g, fx);
        let gy = k.app(g, fy);
        let r = app2(k, c.op, gx, gy);
        let body = t_app(k, c.trans, &[p, q, r, step1, step2]);
        let t = lam_over(k, X_B_FV, a.carrier, body);
        lam_over(k, X_A_FV, a.carrier, t)
    };
    // `g (f A.e) ~ g B.e` by `g`'s congruence on `f`'s unit law, then
    // `g B.e ~ C.e` is `g`'s own unit law.
    let v_unit = {
        let f_e = k.app(f, a.e);
        let step1 = t_app(k, g_congr, &[f_e, b.e, f_unit]);
        let p = k.app(g, f_e);
        let q = k.app(g, b.e);
        t_app(k, c.trans, &[p, q, c.e, step1, g_unit])
    };

    let c_props = [
        congr_stmt(k, &a, &c, comp_fn),
        op_stmt(k, &a, &c, comp_fn),
        unit_stmt(k, &a, &c, comp_fn),
    ];
    let value = intro3(k, lg, &c_props, &[v_congr, v_op, v_unit]);
    let value = lam_over(k, PF_2_FV, hg_ty, value);
    let value = lam_over(k, PF_1_FV, hf_ty, value);
    let value = lam_over(k, F_2_FV, g_ty, value);
    let value = lam_over(k, F_1_FV, f_ty, value);
    let value = lam_over(k, G_C_FV, m_ty, value);
    let value = lam_over(k, G_B_FV, m_ty, value);
    let value = lam_over(k, G_A_FV, m_ty, value);

    let imh3 = k.const_(is_mon_hom, vec![]);
    let concl = t_app(k, imh3, &[mv, pv, comp_fn]);
    let ty = arrow(k, hg_ty, concl);
    let ty = arrow(k, hf_ty, ty);
    let ty = pi_over(k, F_2_FV, g_ty, ty);
    let ty = pi_over(k, F_1_FV, f_ty, ty);
    let ty = pi_over(k, G_C_FV, m_ty, ty);
    let ty = pi_over(k, G_B_FV, m_ty, ty);
    let ty = pi_over(k, G_A_FV, m_ty, ty);

    thm(k, ns, "isMonHom_comp", ty, value)
}

// ---------------------------------------------------------------------------
// The congruence projection each bundled category's `compCongr` consumes.
// ---------------------------------------------------------------------------

/// `CatS.isGrpHom_congr : forall G H f, IsGrpHom G H f -> forall a b,
///  G.equiv a b -> H.equiv (f a) (f b)` (and its `IsMonHom` twin) — the first
/// conjunct, named, because `compCongr` is the ONE proof a bundled-hom
/// category owes and this is the only thing it needs from the bundle.
fn declare_hom_congr(
    k: &mut Kernel,
    lg: &LogicPrelude,
    rec: &RecordNames,
    is_hom: NameId,
    monoidal: bool,
    ns: NameId,
    suffix: &str,
) -> Result<NameId, KernelError> {
    let o_ty = k.const_(rec.ind, vec![]);
    let av = k.fvar(G_A_FV);
    let bv = k.fvar(G_B_FV);
    let a = ob_of(k, rec, av);
    let b = ob_of(k, rec, bv);
    let f_ty = arrow(k, a.carrier, b.carrier);
    let f = k.fvar(F_1_FV);
    let ih = k.const_(is_hom, vec![]);
    let h_ty = t_app(k, ih, &[av, bv, f]);
    let h = k.fvar(PF_1_FV);

    let congr_p = congr_stmt(k, &a, &b, f);
    let op_p = op_stmt(k, &a, &b, f);
    let value = if monoidal {
        let unit_p = unit_stmt(k, &a, &b, f);
        project3(k, lg, &[congr_p, op_p, unit_p], h, 0)
    } else {
        let al = k.const_(lg.and_left, vec![]);
        t_app(k, al, &[congr_p, op_p, h])
    };
    let value = lam_over(k, PF_1_FV, h_ty, value);
    let value = lam_over(k, F_1_FV, f_ty, value);
    let value = lam_over(k, G_B_FV, o_ty, value);
    let value = lam_over(k, G_A_FV, o_ty, value);

    let ty = arrow(k, h_ty, congr_p);
    let ty = pi_over(k, F_1_FV, f_ty, ty);
    let ty = pi_over(k, G_B_FV, o_ty, ty);
    let ty = pi_over(k, G_A_FV, o_ty, ty);

    thm(k, ns, suffix, ty, value)
}

// ---------------------------------------------------------------------------
// The bundled hom-family, and the category over it.
// ---------------------------------------------------------------------------

/// `CatS.GrpHom G H := Subtype.{1} (G.carrier -> H.carrier) (IsGrpHom G H)`
/// (and the `Mon` twin). **This is the declaration ADR-1620 was one `Sigma`
/// short of.** `Subtype.{1} : ... -> Sort (max 1 1)`, which is the `Sort 1`
/// `CatS.CategoryLarge.hom` demands.
fn declare_bundled_hom(
    k: &mut Kernel,
    lg: &LogicPrelude,
    rec: &RecordNames,
    is_hom: NameId,
    ns: NameId,
    suffix: &str,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let sort1 = k.sort(l1);
    let o_ty = k.const_(rec.ind, vec![]);
    let av = k.fvar(G_A_FV);
    let bv = k.fvar(G_B_FV);
    let a = ob_of(k, rec, av);
    let b = ob_of(k, rec, bv);
    let f_ty = arrow(k, a.carrier, b.carrier);
    let ih = k.const_(is_hom, vec![]);
    let pred = app2(k, ih, av, bv);

    let value = sub_ty(k, lg, l1, f_ty, pred);
    let value = lam_over(k, G_B_FV, o_ty, value);
    let value = lam_over(k, G_A_FV, o_ty, value);

    let ty = pi_over(k, G_B_FV, o_ty, sort1);
    let ty = pi_over(k, G_A_FV, o_ty, ty);

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

/// Everything one bundled-hom category needs, so `CatS.grp` and `CatS.mon`
/// are one function called twice.
struct BundledCat {
    /// The `AlgS` record whose values are the objects.
    rec: RecordNames,
    /// `CatS.IsGrpHom` / `CatS.IsMonHom`.
    is_hom: NameId,
    /// `CatS.GrpHom` / `CatS.MonHom`.
    hom: NameId,
    /// `CatS.isGrpHom_id` / `CatS.isMonHom_id`.
    hom_id: NameId,
    /// `CatS.isGrpHom_comp` / `CatS.isMonHom_comp`.
    hom_comp: NameId,
    /// `CatS.isGrpHom_congr` / `CatS.isMonHom_congr`.
    hom_congr: NameId,
}

impl BundledCat {
    /// `Subtype.{1} (A.carrier -> B.carrier) (IsHom A B)`'s two arguments.
    fn sub_args(&self, k: &mut Kernel, av: ExprId, bv: ExprId) -> (ExprId, ExprId) {
        let a = ob_of(k, &self.rec, av);
        let b = ob_of(k, &self.rec, bv);
        let f_ty = arrow(k, a.carrier, b.carrier);
        let ih = k.const_(self.is_hom, vec![]);
        let pred = app2(k, ih, av, bv);
        (f_ty, pred)
    }

    /// `Subtype.val` of a morphism `u : hom A B`.
    fn val(&self, k: &mut Kernel, lg: &LogicPrelude, av: ExprId, bv: ExprId, u: ExprId) -> ExprId {
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let (f_ty, pred) = self.sub_args(k, av, bv);
        sub_val(k, lg, l1, f_ty, pred, u)
    }

    /// `Subtype.property` of a morphism `u : hom A B`.
    fn prop(&self, k: &mut Kernel, lg: &LogicPrelude, av: ExprId, bv: ExprId, u: ExprId) -> ExprId {
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let (f_ty, pred) = self.sub_args(k, av, bv);
        sub_prop(k, lg, l1, f_ty, pred, u)
    }

    /// `Subtype.mk` at `hom A B`.
    fn mk(
        &self,
        k: &mut Kernel,
        lg: &LogicPrelude,
        av: ExprId,
        bv: ExprId,
        v: ExprId,
        p: ExprId,
    ) -> ExprId {
        let l0 = k.level_zero();
        let l1 = k.level_succ(l0);
        let (f_ty, pred) = self.sub_args(k, av, bv);
        sub_mk(k, lg, l1, f_ty, pred, v, p)
    }
}

/// Build `CatS.grp` / `CatS.mon` — a `CatS.CategoryLarge` whose objects are
/// `AlgS` structures and whose morphisms are the BUNDLED structure-preserving
/// functions. See this module's header for the setoid cost table.
fn declare_bundled_cat(
    k: &mut Kernel,
    lg: &LogicPrelude,
    large: &RecordNames,
    bc: &BundledCat,
    ns: NameId,
    suffix: &str,
) -> Result<NameId, KernelError> {
    let o_ty = k.const_(bc.rec.ind, vec![]);
    let hom = k.const_(bc.hom, vec![]);

    // homEquiv := fun A B u v => forall x : A.carrier, B.equiv (u x) (v x).
    let hom_equiv = {
        let av = k.fvar(G_A_FV);
        let bv = k.fvar(G_B_FV);
        let a = ob_of(k, &bc.rec, av);
        let b = ob_of(k, &bc.rec, bv);
        let hty = app2(k, hom, av, bv);
        let u = k.fvar(H_U_FV);
        let v = k.fvar(H_V_FV);
        let uv = bc.val(k, lg, av, bv, u);
        let vv = bc.val(k, lg, av, bv, v);
        let x = k.fvar(X_A_FV);
        let ux = k.app(uv, x);
        let vx = k.app(vv, x);
        let body = app2(k, b.equiv, ux, vx);
        let body = pi_over(k, X_A_FV, a.carrier, body);
        let t = lam_over(k, H_V_FV, hty, body);
        let t = lam_over(k, H_U_FV, hty, t);
        let t = lam_over(k, G_B_FV, o_ty, t);
        lam_over(k, G_A_FV, o_ty, t)
    };

    // The three pointwise liftings of the object's own equivalence.
    let hom_refl = {
        let av = k.fvar(G_A_FV);
        let bv = k.fvar(G_B_FV);
        let a = ob_of(k, &bc.rec, av);
        let b = ob_of(k, &bc.rec, bv);
        let hty = app2(k, hom, av, bv);
        let u = k.fvar(H_U_FV);
        let uv = bc.val(k, lg, av, bv, u);
        let x = k.fvar(X_A_FV);
        let ux = k.app(uv, x);
        let body = k.app(b.refl, ux);
        let body = lam_over(k, X_A_FV, a.carrier, body);
        let t = lam_over(k, H_U_FV, hty, body);
        let t = lam_over(k, G_B_FV, o_ty, t);
        lam_over(k, G_A_FV, o_ty, t)
    };
    let hom_symm = {
        let av = k.fvar(G_A_FV);
        let bv = k.fvar(G_B_FV);
        let a = ob_of(k, &bc.rec, av);
        let b = ob_of(k, &bc.rec, bv);
        let hty = app2(k, hom, av, bv);
        let u = k.fvar(H_U_FV);
        let v = k.fvar(H_V_FV);
        let uv = bc.val(k, lg, av, bv, u);
        let vv = bc.val(k, lg, av, bv, v);
        let hyp = {
            let x = k.fvar(X_A_FV);
            let ux = k.app(uv, x);
            let vx = k.app(vv, x);
            let body = app2(k, b.equiv, ux, vx);
            pi_over(k, X_A_FV, a.carrier, body)
        };
        let h = k.fvar(P_1_FV);
        let x = k.fvar(X_A_FV);
        let ux = k.app(uv, x);
        let vx = k.app(vv, x);
        let hx = k.app(h, x);
        let body = t_app(k, b.symm, &[ux, vx, hx]);
        let body = lam_over(k, X_A_FV, a.carrier, body);
        let t = lam_over(k, P_1_FV, hyp, body);
        let t = lam_over(k, H_V_FV, hty, t);
        let t = lam_over(k, H_U_FV, hty, t);
        let t = lam_over(k, G_B_FV, o_ty, t);
        lam_over(k, G_A_FV, o_ty, t)
    };
    let hom_trans = {
        let av = k.fvar(G_A_FV);
        let bv = k.fvar(G_B_FV);
        let a = ob_of(k, &bc.rec, av);
        let b = ob_of(k, &bc.rec, bv);
        let hty = app2(k, hom, av, bv);
        let u = k.fvar(H_U_FV);
        let v = k.fvar(H_V_FV);
        let w = k.fvar(H_W_FV);
        let uv = bc.val(k, lg, av, bv, u);
        let vv = bc.val(k, lg, av, bv, v);
        let wv = bc.val(k, lg, av, bv, w);
        let mk_hyp = |k: &mut Kernel, p: ExprId, q: ExprId| {
            let x = k.fvar(X_A_FV);
            let px = k.app(p, x);
            let qx = k.app(q, x);
            let body = app2(k, b.equiv, px, qx);
            pi_over(k, X_A_FV, a.carrier, body)
        };
        let hyp1 = mk_hyp(k, uv, vv);
        let hyp2 = mk_hyp(k, vv, wv);
        let h1 = k.fvar(P_1_FV);
        let h2 = k.fvar(P_2_FV);
        let x = k.fvar(X_A_FV);
        let ux = k.app(uv, x);
        let vx = k.app(vv, x);
        let wx = k.app(wv, x);
        let h1x = k.app(h1, x);
        let h2x = k.app(h2, x);
        let body = t_app(k, b.trans, &[ux, vx, wx, h1x, h2x]);
        let body = lam_over(k, X_A_FV, a.carrier, body);
        let t = lam_over(k, P_2_FV, hyp2, body);
        let t = lam_over(k, P_1_FV, hyp1, t);
        let t = lam_over(k, H_W_FV, hty, t);
        let t = lam_over(k, H_V_FV, hty, t);
        let t = lam_over(k, H_U_FV, hty, t);
        let t = lam_over(k, G_B_FV, o_ty, t);
        lam_over(k, G_A_FV, o_ty, t)
    };

    // id := fun A => mk (fun x => x) (isHom_id A).
    let ident = {
        let av = k.fvar(G_A_FV);
        let a = ob_of(k, &bc.rec, av);
        let idf = {
            let x = k.fvar(X_A_FV);
            lam_over(k, X_A_FV, a.carrier, x)
        };
        let hid = k.const_(bc.hom_id, vec![]);
        let p = k.app(hid, av);
        let body = bc.mk(k, lg, av, av, idf, p);
        lam_over(k, G_A_FV, o_ty, body)
    };

    // comp := fun A B C v u => mk (fun x => v (u x)) (isHom_comp …).
    let comp = {
        let av = k.fvar(G_A_FV);
        let bv = k.fvar(G_B_FV);
        let cv = k.fvar(G_C_FV);
        let a = ob_of(k, &bc.rec, av);
        let hbc = app2(k, hom, bv, cv);
        let hab = app2(k, hom, av, bv);
        let v = k.fvar(H_V_FV);
        let u = k.fvar(H_U_FV);
        let uf = bc.val(k, lg, av, bv, u);
        let vf = bc.val(k, lg, bv, cv, v);
        let up = bc.prop(k, lg, av, bv, u);
        let vp = bc.prop(k, lg, bv, cv, v);
        let fn_ = {
            let x = k.fvar(X_A_FV);
            let ux = k.app(uf, x);
            let body = k.app(vf, ux);
            lam_over(k, X_A_FV, a.carrier, body)
        };
        let hc = k.const_(bc.hom_comp, vec![]);
        let p = t_app(k, hc, &[av, bv, cv, uf, vf, up, vp]);
        let body = bc.mk(k, lg, av, cv, fn_, p);
        let t = lam_over(k, H_U_FV, hab, body);
        let t = lam_over(k, H_V_FV, hbc, t);
        let t = lam_over(k, G_C_FV, o_ty, t);
        let t = lam_over(k, G_B_FV, o_ty, t);
        lam_over(k, G_A_FV, o_ty, t)
    };

    // compCongr — THE one proof. `v (u x) ~ v (u' x) ~ v' (u' x)`: the first
    // step is where the BUNDLED congruence is spent, and it is exactly the
    // step ADR-1620 measured as impossible for an unbundled hom-family.
    let comp_congr = {
        let av = k.fvar(G_A_FV);
        let bv = k.fvar(G_B_FV);
        let cv = k.fvar(G_C_FV);
        let a = ob_of(k, &bc.rec, av);
        let b = ob_of(k, &bc.rec, bv);
        let c = ob_of(k, &bc.rec, cv);
        let hbc = app2(k, hom, bv, cv);
        let hab = app2(k, hom, av, bv);
        let v = k.fvar(H_V_FV);
        let v2 = k.fvar(H_V2_FV);
        let u = k.fvar(H_U_FV);
        let u2 = k.fvar(H_U2_FV);
        let uf = bc.val(k, lg, av, bv, u);
        let u2f = bc.val(k, lg, av, bv, u2);
        let vf = bc.val(k, lg, bv, cv, v);
        let v2f = bc.val(k, lg, bv, cv, v2);
        let vp = bc.prop(k, lg, bv, cv, v);

        let hyp_v = {
            let x = k.fvar(X_A_FV);
            let p = k.app(vf, x);
            let q = k.app(v2f, x);
            let body = app2(k, c.equiv, p, q);
            pi_over(k, X_A_FV, b.carrier, body)
        };
        let hyp_u = {
            let x = k.fvar(X_A_FV);
            let p = k.app(uf, x);
            let q = k.app(u2f, x);
            let body = app2(k, b.equiv, p, q);
            pi_over(k, X_A_FV, a.carrier, body)
        };
        let hv = k.fvar(P_1_FV);
        let hu = k.fvar(P_2_FV);

        let hcongr = k.const_(bc.hom_congr, vec![]);
        let v_congr = t_app(k, hcongr, &[bv, cv, vf, vp]);

        let x = k.fvar(X_A_FV);
        let ux = k.app(uf, x);
        let u2x = k.app(u2f, x);
        let hux = k.app(hu, x);
        let step1 = t_app(k, v_congr, &[ux, u2x, hux]);
        let step2 = k.app(hv, u2x);
        let p = k.app(vf, ux);
        let q = k.app(vf, u2x);
        let r = k.app(v2f, u2x);
        let body = t_app(k, c.trans, &[p, q, r, step1, step2]);
        let body = lam_over(k, X_A_FV, a.carrier, body);

        let t = lam_over(k, P_2_FV, hyp_u, body);
        let t = lam_over(k, P_1_FV, hyp_v, t);
        let t = lam_over(k, H_U2_FV, hab, t);
        let t = lam_over(k, H_U_FV, hab, t);
        let t = lam_over(k, H_V2_FV, hbc, t);
        let t = lam_over(k, H_V_FV, hbc, t);
        let t = lam_over(k, G_C_FV, o_ty, t);
        let t = lam_over(k, G_B_FV, o_ty, t);
        lam_over(k, G_A_FV, o_ty, t)
    };

    // idL / idR — free: `Subtype.val (Subtype.mk f h)` ι-reduces, so both
    // sides of the law are the SAME function and the law is `B.equivRefl`.
    let unit_law = |k: &mut Kernel| {
        let av = k.fvar(G_A_FV);
        let bv = k.fvar(G_B_FV);
        let a = ob_of(k, &bc.rec, av);
        let b = ob_of(k, &bc.rec, bv);
        let hab = app2(k, hom, av, bv);
        let u = k.fvar(H_U_FV);
        let uf = bc.val(k, lg, av, bv, u);
        let x = k.fvar(X_A_FV);
        let ux = k.app(uf, x);
        let body = k.app(b.refl, ux);
        let body = lam_over(k, X_A_FV, a.carrier, body);
        let t = lam_over(k, H_U_FV, hab, body);
        let t = lam_over(k, G_B_FV, o_ty, t);
        lam_over(k, G_A_FV, o_ty, t)
    };
    let id_l = unit_law(k);
    let id_r = unit_law(k);

    // assoc — free for the same reason.
    let assoc = {
        let av = k.fvar(G_A_FV);
        let bv = k.fvar(G_B_FV);
        let cv = k.fvar(G_C_FV);
        let dv = k.fvar(G_D_FV);
        let a = ob_of(k, &bc.rec, av);
        let d = ob_of(k, &bc.rec, dv);
        let hcd = app2(k, hom, cv, dv);
        let hbc = app2(k, hom, bv, cv);
        let hab = app2(k, hom, av, bv);
        let hm = k.fvar(H_W_FV);
        let gm = k.fvar(H_V_FV);
        let fm = k.fvar(H_U_FV);
        let hf = bc.val(k, lg, cv, dv, hm);
        let gf = bc.val(k, lg, bv, cv, gm);
        let ff = bc.val(k, lg, av, bv, fm);
        let x = k.fvar(X_A_FV);
        let fx = k.app(ff, x);
        let gfx = k.app(gf, fx);
        let hgfx = k.app(hf, gfx);
        let body = k.app(d.refl, hgfx);
        let body = lam_over(k, X_A_FV, a.carrier, body);
        let t = lam_over(k, H_U_FV, hab, body);
        let t = lam_over(k, H_V_FV, hbc, t);
        let t = lam_over(k, H_W_FV, hcd, t);
        let t = lam_over(k, G_D_FV, o_ty, t);
        let t = lam_over(k, G_C_FV, o_ty, t);
        let t = lam_over(k, G_B_FV, o_ty, t);
        lam_over(k, G_A_FV, o_ty, t)
    };

    let value = mk_instance(
        k,
        large,
        &[
            o_ty, hom, hom_equiv, hom_refl, hom_symm, hom_trans, ident, comp, comp_congr, id_l,
            id_r, assoc,
        ],
    );
    let ty = k.const_(large.ind, vec![]);

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
// `AlgS.Group.toMonoidS` — the object half of the forgetful functor.
// ---------------------------------------------------------------------------

/// `AlgS.Group.toMonoidS : AlgS.Group -> AlgS.Monoid`. NOT a prefix
/// projection (unlike `AlgS.CommGroup.toGroupS`): `AlgS.Monoid`'s field 8 is
/// `assoc` and `AlgS.Group`'s is `inv`, so the eleven monoid fields are
/// gathered from group indices 0-7, 10, 11, 12. Free — every field is a
/// selector, and the three law fields are literally the same statement
/// because `carrier`, `equiv` and `op` are carried across unchanged.
fn declare_to_monoid_s(
    k: &mut Kernel,
    monoid: &RecordNames,
    group: &RecordNames,
) -> Result<NameId, KernelError> {
    use algs::group::{ASSOC, IDENT_L, IDENT_R};
    let g_ty = k.const_(group.ind, vec![]);
    let gv = k.fvar(G_A_FV);
    let o = ob_of(k, group, gv);
    let op_congr = sel(k, group, algs::group::OP_CONGR, gv);
    let assoc = sel(k, group, ASSOC, gv);
    let ident_l = sel(k, group, IDENT_L, gv);
    let ident_r = sel(k, group, IDENT_R, gv);
    let body = mk_instance(
        k,
        monoid,
        &[
            o.carrier, o.equiv, o.refl, o.symm, o.trans, o.op, op_congr, o.e, assoc, ident_l,
            ident_r,
        ],
    );
    let value = lam_over(k, G_A_FV, g_ty, body);
    let m_ty = k.const_(monoid.ind, vec![]);
    let ty = pi_over(k, G_A_FV, g_ty, m_ty);

    let name = k.name_str(group.ind, "toMonoidS");
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
// The forgetful functor `Grp -> Mon`.
// ---------------------------------------------------------------------------

/// `CatS.forgetGrpMon : CatS.FunctorLarge` — **the reviewer's item 4**. The
/// object map is `AlgS.Group.toMonoidS`; the morphism map keeps the same
/// underlying function and rebuilds the property, whose third conjunct (unit
/// preservation) is `AlgS.Hom.mapOne`. The three functor laws are free,
/// because the morphism map does not touch `Subtype.val`.
fn declare_forget_grp_mon(
    k: &mut Kernel,
    lg: &LogicPrelude,
    large: &RecordNames,
    functor_large: &RecordNames,
    grp: &BundledCat,
    mon: &BundledCat,
    grp_cat: NameId,
    mon_cat: NameId,
    to_monoid_s: NameId,
    map_one: NameId,
    ns: NameId,
) -> Result<NameId, KernelError> {
    let g_ty = k.const_(grp.rec.ind, vec![]);
    let grp_c = k.const_(grp_cat, vec![]);
    let mon_c = k.const_(mon_cat, vec![]);
    let src = cat_of(k, large, grp_c);
    let tgt = cat_of(k, large, mon_c);
    let fo = k.const_(to_monoid_s, vec![]);

    // The morphism map.
    let fm = {
        let av = k.fvar(G_A_FV);
        let bv = k.fvar(G_B_FV);
        let hab = src.hom_ty(k, av, bv);
        let u = k.fvar(H_U_FV);
        let uf = grp.val(k, lg, av, bv, u);
        let up = grp.prop(k, lg, av, bv, u);

        let ma = k.app(fo, av);
        let mb = k.app(fo, bv);
        let a = ob_of(k, &grp.rec, av);
        let b = ob_of(k, &grp.rec, bv);
        let ma_o = ob_of(k, &mon.rec, ma);
        let mb_o = ob_of(k, &mon.rec, mb);

        let g_congr_p = congr_stmt(k, &a, &b, uf);
        let g_op_p = op_stmt(k, &a, &b, uf);
        let al = k.const_(lg.and_left, vec![]);
        let u_congr = t_app(k, al, &[g_congr_p, g_op_p, up]);
        let ar = k.const_(lg.and_right, vec![]);
        let u_op = t_app(k, ar, &[g_congr_p, g_op_p, up]);
        let mo = k.const_(map_one, vec![]);
        let u_unit = t_app(k, mo, &[av, bv, uf, u_congr, u_op]);

        let props = [
            congr_stmt(k, &ma_o, &mb_o, uf),
            op_stmt(k, &ma_o, &mb_o, uf),
            unit_stmt(k, &ma_o, &mb_o, uf),
        ];
        let p = intro3(k, lg, &props, &[u_congr, u_op, u_unit]);
        let body = mon.mk(k, lg, ma, mb, uf, p);
        let t = lam_over(k, H_U_FV, hab, body);
        let t = lam_over(k, G_B_FV, g_ty, t);
        lam_over(k, G_A_FV, g_ty, t)
    };

    // mapCongr := fun A B u v h => h -- the hypothesis IS the conclusion,
    // because `Subtype.val (map u)` ι-reduces back to `Subtype.val u`.
    let map_congr = {
        let av = k.fvar(G_A_FV);
        let bv = k.fvar(G_B_FV);
        let hab = src.hom_ty(k, av, bv);
        let u = k.fvar(H_U_FV);
        let v = k.fvar(H_V_FV);
        let hyp = src.eqv(k, av, bv, u, v);
        let h = k.fvar(P_1_FV);
        let t = lam_over(k, P_1_FV, hyp, h);
        let t = lam_over(k, H_V_FV, hab, t);
        let t = lam_over(k, H_U_FV, hab, t);
        let t = lam_over(k, G_B_FV, g_ty, t);
        lam_over(k, G_A_FV, g_ty, t)
    };

    let map_id = {
        let av = k.fvar(G_A_FV);
        let a = ob_of(k, &grp.rec, av);
        let x = k.fvar(X_A_FV);
        let body = k.app(a.refl, x);
        let body = lam_over(k, X_A_FV, a.carrier, body);
        lam_over(k, G_A_FV, g_ty, body)
    };

    let map_comp = {
        let av = k.fvar(G_A_FV);
        let bv = k.fvar(G_B_FV);
        let cv = k.fvar(G_C_FV);
        let a = ob_of(k, &grp.rec, av);
        let c = ob_of(k, &grp.rec, cv);
        let hbc = src.hom_ty(k, bv, cv);
        let hab = src.hom_ty(k, av, bv);
        let v = k.fvar(H_V_FV);
        let u = k.fvar(H_U_FV);
        let uf = grp.val(k, lg, av, bv, u);
        let vf = grp.val(k, lg, bv, cv, v);
        let x = k.fvar(X_A_FV);
        let ux = k.app(uf, x);
        let vux = k.app(vf, ux);
        let body = k.app(c.refl, vux);
        let body = lam_over(k, X_A_FV, a.carrier, body);
        let t = lam_over(k, H_U_FV, hab, body);
        let t = lam_over(k, H_V_FV, hbc, t);
        let t = lam_over(k, G_C_FV, g_ty, t);
        let t = lam_over(k, G_B_FV, g_ty, t);
        lam_over(k, G_A_FV, g_ty, t)
    };

    let _ = tgt;
    let value = mk_instance(
        k,
        functor_large,
        &[grp_c, mon_c, fo, fm, map_congr, map_id, map_comp],
    );
    let ty = k.const_(functor_large.ind, vec![]);

    let name = k.name_str(ns, "forgetGrpMon");
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
// Names and the entry point.
// ---------------------------------------------------------------------------

/// The `Sigma`-residue layer's records: one more functor record, at the level
/// `CatS.CategoryLarge` forces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GroupCatRecords {
    /// `CatS.FunctorLarge : Sort 3` — [`super::functor_fields`] again over
    /// `CatS.CategoryLarge`.
    pub functor_large: RecordNames,
}

/// Everything this module declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GroupCatNames {
    /// `CatS.GrpHom` — the bundled hom-family of the category of groups.
    pub grp_hom: NameId,
    /// `CatS.isGrpHom_congr` — the first conjunct, named.
    pub is_grp_hom_congr: NameId,
    /// `CatS.grp : CatS.CategoryLarge` — **the category of groups**.
    pub grp: NameId,
    /// `CatS.IsMonHom` — congruence, `op`-preservation AND unit preservation.
    pub is_mon_hom: NameId,
    /// `CatS.isMonHom_id`.
    pub is_mon_hom_id: NameId,
    /// `CatS.isMonHom_comp`.
    pub is_mon_hom_comp: NameId,
    /// `CatS.isMonHom_congr`.
    pub is_mon_hom_congr: NameId,
    /// `CatS.MonHom` — the bundled hom-family of the category of monoids.
    pub mon_hom: NameId,
    /// `CatS.mon : CatS.CategoryLarge` — the category of monoids.
    pub mon: NameId,
    /// `AlgS.Group.toMonoidS` — the forgetful projection, as a definition.
    pub to_monoid_s: NameId,
    /// `CatS.IsFunctorLarge`.
    pub is_functor_large: NameId,
    /// `CatS.functorLarge_isFunctor`.
    pub functor_large_is_functor: NameId,
    /// `CatS.forgetGrpMon : CatS.FunctorLarge` — the forgetful functor.
    pub forget_grp_mon: NameId,
    /// `CatS.forgetGrpMon_isFunctor` — its three laws, as the predicate.
    pub forget_grp_mon_is_functor: NameId,
}

#[cfg(test)]
impl GroupCatNames {
    #[must_use]
    pub fn all(&self) -> [NameId; 14] {
        [
            self.grp_hom,
            self.is_grp_hom_congr,
            self.grp,
            self.is_mon_hom,
            self.is_mon_hom_id,
            self.is_mon_hom_comp,
            self.is_mon_hom_congr,
            self.mon_hom,
            self.mon,
            self.to_monoid_s,
            self.is_functor_large,
            self.functor_large_is_functor,
            self.forget_grp_mon,
            self.forget_grp_mon_is_functor,
        ]
    }
}

/// The one `AlgS.Hom.*` name this module needs: unit preservation, which a
/// group morphism satisfies but a monoid morphism must carry.
#[derive(Debug, Clone, Copy)]
pub(crate) struct GroupCatDeps {
    /// `AlgS.Hom.mapOne : forall G H f fCongr fMul, H.equiv (f G.e) H.e`.
    pub map_one: NameId,
}

/// Declare the whole `Sigma`-residue layer.
pub(crate) fn declare_group_categories(
    k: &mut Kernel,
    lg: &LogicPrelude,
    recs: &CategoryRecords,
    monoid: &RecordNames,
    group: &RecordNames,
    is_grp_hom: NameId,
    is_grp_hom_id: NameId,
    is_grp_hom_comp: NameId,
    deps: &GroupCatDeps,
    ns: NameId,
) -> Result<(GroupCatRecords, GroupCatNames), KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let l2 = k.level_succ(l1);
    let l3 = k.level_succ(l2);

    // --- the category of groups -------------------------------------------
    let is_grp_hom_congr =
        declare_hom_congr(k, lg, group, is_grp_hom, false, ns, "isGrpHom_congr")?;
    let grp_hom = declare_bundled_hom(k, lg, group, is_grp_hom, ns, "GrpHom")?;
    let grp_bc = BundledCat {
        rec: *group,
        is_hom: is_grp_hom,
        hom: grp_hom,
        hom_id: is_grp_hom_id,
        hom_comp: is_grp_hom_comp,
        hom_congr: is_grp_hom_congr,
    };
    let grp = declare_bundled_cat(k, lg, &recs.category_large, &grp_bc, ns, "grp")?;

    // --- the category of monoids ------------------------------------------
    let is_mon_hom = declare_is_mon_hom(k, lg, monoid, ns)?;
    let is_mon_hom_id = declare_is_mon_hom_id(k, lg, monoid, is_mon_hom, ns)?;
    let is_mon_hom_comp = declare_is_mon_hom_comp(k, lg, monoid, is_mon_hom, ns)?;
    let is_mon_hom_congr =
        declare_hom_congr(k, lg, monoid, is_mon_hom, true, ns, "isMonHom_congr")?;
    let mon_hom = declare_bundled_hom(k, lg, monoid, is_mon_hom, ns, "MonHom")?;
    let mon_bc = BundledCat {
        rec: *monoid,
        is_hom: is_mon_hom,
        hom: mon_hom,
        hom_id: is_mon_hom_id,
        hom_comp: is_mon_hom_comp,
        hom_congr: is_mon_hom_congr,
    };
    let mon = declare_bundled_cat(k, lg, &recs.category_large, &mon_bc, ns, "mon")?;

    // --- the forgetful functor --------------------------------------------
    let to_monoid_s = declare_to_monoid_s(k, monoid, group)?;
    let functor_large_name = k.name_str(ns, "FunctorLarge");
    let functor_large = declare_record(
        k,
        lg,
        l0,
        l2,
        l3,
        functor_large_name,
        &functor_fields(recs.category_large),
    )?;
    let is_functor_large = declare_is_functor(k, lg, &recs.category_large, ns, "IsFunctorLarge")?;
    let functor_large_is_functor = declare_functor_is_functor(
        k,
        lg,
        &recs.category_large,
        &functor_large,
        is_functor_large,
        ns,
        "functorLarge_isFunctor",
    )?;
    let forget_grp_mon = declare_forget_grp_mon(
        k,
        lg,
        &recs.category_large,
        &functor_large,
        &grp_bc,
        &mon_bc,
        grp,
        mon,
        to_monoid_s,
        deps.map_one,
        ns,
    )?;
    let forget_grp_mon_is_functor = {
        use idx::functor::{MAP, OBJ as F_OBJ, SRC, TGT};
        let fv = k.const_(forget_grp_mon, vec![]);
        let flif = k.const_(functor_large_is_functor, vec![]);
        let value = k.app(flif, fv);
        let src = sel(k, &functor_large, SRC, fv);
        let tgt = sel(k, &functor_large, TGT, fv);
        let fo = sel(k, &functor_large, F_OBJ, fv);
        let fm = sel(k, &functor_large, MAP, fv);
        let isf = k.const_(is_functor_large, vec![]);
        let ty = t_app(k, isf, &[src, tgt, fo, fm]);
        thm(k, ns, "forgetGrpMon_isFunctor", ty, value)?
    };

    Ok((
        GroupCatRecords { functor_large },
        GroupCatNames {
            grp_hom,
            is_grp_hom_congr,
            grp,
            is_mon_hom,
            is_mon_hom_id,
            is_mon_hom_comp,
            is_mon_hom_congr,
            mon_hom,
            mon,
            to_monoid_s,
            is_functor_large,
            functor_large_is_functor,
            forget_grp_mon,
            forget_grp_mon_is_functor,
        },
    ))
}
