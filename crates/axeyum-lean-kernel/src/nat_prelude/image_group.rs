//! `AlgS.Hom.imageGroup` and `AlgS.Hom.firstIsoClassical` — **the image of a
//! homomorphism is a group object, and the first isomorphism theorem is now a
//! statement about two of them** (ADR-1613, closing what ADR-1595 measured).
//!
//! # What ADR-1595 could not say
//!
//! `AlgS.Hom.firstIso` (`structures_setoid.rs`) is a right-nested `And` of
//! three conjuncts about `G`, `H` and `f` — the quotient's equivalence is the
//! kernel congruence, the induced map is multiplicative, and it hits every
//! `f a`. That is the *content* of the first isomorphism theorem, but it is not
//! its *statement*: classically it says `G/ker f ≅ Im f`, an isomorphism
//! between two **group objects**. ADR-1595 found the quotient side already
//! available (`AlgS.Hom.quotient` keeps `G.carrier` and changes only `equiv`,
//! so no `Quot.sound` is needed) and the image side blocked, for one reason
//! recorded verbatim in that file:
//!
//! > The second needs a carrier `{y : H.carrier // ∃ a, H.equiv (f a) y}` — a
//! > subtype. This kernel has no `Subtype` and no `Sigma`.
//!
//! It has both now. `AlgS.Hom.image G H f : H.carrier → Prop` was always there;
//! it just had nowhere to go.
//!
//! # The construction, and why fourteen of fifteen fields are free
//!
//! ```text
//! AlgS.Hom.imageCarrier G H f := Subtype.{1} H.carrier (AlgS.Hom.image G H f)
//! AlgS.Hom.imageGroup   G H f fCongr fMul : AlgS.Group
//!   carrier := AlgS.Hom.imageCarrier G H f
//!   equiv   := fun x y => H.equiv x.val y.val
//!   op      := fun x y => ⟨H.op x.val y.val, _⟩
//!   e       := ⟨H.e, _⟩
//!   inv     := fun x => ⟨H.inv x.val, _⟩
//!   …every law field is H's own law at `x.val`, `y.val`, `z.val`.
//! ```
//!
//! `Subtype.val` ι-reduces on `Subtype.mk`, so `(op x y).val` is
//! *definitionally* `H.op x.val y.val`, `e.val` is `H.e`, and `(inv x).val` is
//! `H.inv x.val`. Every one of `assoc`, `identL`, `identR`, `invL`, `invR`,
//! `opCongr`, `invCongr` and the three `equiv` laws therefore reduces to
//! exactly the statement `H`'s own field already proves. The subtype carries
//! the group structure for free — which is the reason `Subtype` was the missing
//! piece and not, say, a bespoke "image" inductive.
//!
//! **The whole cost is three membership proofs**, one per operation, and each
//! is one `Exists` elimination plus one `H.equivTrans`:
//!
//! | slot | obligation | proof |
//! | --- | --- | --- |
//! | `e` | `∃ a, H.equiv (f a) H.e` | witness `G.e`, by `AlgS.Hom.mapOne` |
//! | `op` | `∃ a, H.equiv (f a) (H.op x.val y.val)` | witness `G.op a b`, by `fMul` then `H.opCongr` |
//! | `inv` | `∃ a, H.equiv (f a) (H.inv x.val)` | witness `G.inv a`, by `AlgS.Hom.mapInv` then `H.invCongr` |
//!
//! The `Exists` eliminations are all legal here because every target is a
//! `Prop` — `AlgS.Hom.image` is `Prop`-valued, so nothing needs `Exists` to
//! eliminate into data. That is the same reason `Metric.creal_complete`'s three
//! eliminations are free, and it is worth stating because it is *not* free in
//! general: `Exists` in this kernel has no large elimination.
//!
//! # The classical statement
//!
//! ```text
//! AlgS.Hom.induced G H f fCongr fMul : G.carrier → AlgS.Hom.imageCarrier G H f
//!   := fun a => ⟨f a, AlgS.Hom.image_mem G H f fCongr fMul a⟩
//!
//! AlgS.Hom.firstIsoClassical G H f fCongr fMul :
//!   (∀ a b, Q.equiv a b ↔ I.equiv (induced a) (induced b))        -- well-defined AND injective
//!   ∧ (∀ a b, I.equiv (induced (Q.op a b)) (I.op (induced a) (induced b)))  -- a homomorphism
//!   ∧ (∀ y : I.carrier, ∃ a : Q.carrier, I.equiv (induced a) y)   -- surjective
//! ```
//!
//! with `Q := AlgS.Hom.quotient G H f fCongr fMul` and
//! `I := AlgS.Hom.imageGroup G H f fCongr fMul`, **both of type `AlgS.Group`**.
//! That is `G/ker f ≅ Im f`: a map between two group objects that is a
//! homomorphism, injective, and onto.
//!
//! Every conjunct is nearly free once the two objects exist, and that is the
//! finding rather than a disappointment — it is what "the obstruction was the
//! carrier, not the mathematics" *means*:
//!
//! - conjunct 1 is `Iff.intro (fun h => h) (fun h => h)`: `Q.equiv a b` reduces
//!   to `H.equiv (f a) (f b)` and so does `I.equiv (induced a) (induced b)`;
//! - conjunct 2 is `fMul` verbatim, because `Q.op` reduces to `G.op` and
//!   `(I.op x y).val` to `H.op x.val y.val`;
//! - conjunct 3 is `Subtype.property`, because `y.property` IS
//!   `∃ a, H.equiv (f a) y.val`.
//!
//! Note which direction each conjunct's *first* half carries: conjunct 1's
//! `mp` is well-definedness of the induced map on the quotient and its `mpr` is
//! injectivity. Both are needed and both are the identity here, so stating only
//! one of them would look identical and mean half as much.
//!
//! # What this deliberately does NOT do
//!
//! It does not replace `AlgS.Hom.firstIso`, and it does not introduce an
//! `AlgS.Iso` record. A general isomorphism notion between two `AlgS.Group`
//! objects (bundling the map, its inverse, and the round trips) is a separate
//! decision that should be made once, for the whole `AlgS` spine, rather than
//! invented here for one theorem; the three conjuncts above are the unbundled
//! form of exactly that, stated where it can be checked today.

use super::structures::{RecordNames, app2, arrow, lam_over, mk_instance, pi_over, sel};
use super::structures_setoid::idx;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::{Kernel, KernelError, LogicPrelude};

/// The interned names this file owns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ImageGroupNames {
    /// `AlgS.Hom.imageCarrier : Π G H (f : G.carrier → H.carrier), Sort 1` —
    /// `Subtype H.carrier (AlgS.Hom.image G H f)`, the carrier ADR-1595 could
    /// not build.
    pub image_carrier: NameId,
    /// `AlgS.Hom.imageGroup : Π G H f fCongr fMul, AlgS.Group` — the image as a
    /// group object.
    pub image_group: NameId,
    /// `AlgS.Hom.induced : Π G H f fCongr fMul, G.carrier → imageCarrier G H f`
    /// — the map `G/ker f → Im f`, whose source carrier IS `G.carrier` because
    /// `AlgS.Hom.quotient` changes only the equivalence.
    pub induced: NameId,
    /// `AlgS.Hom.firstIsoClassical` — `G/ker f ≅ Im f` as three conjuncts about
    /// two `AlgS.Group` objects: well-defined-and-injective, homomorphism,
    /// surjective.
    pub first_iso_classical: NameId,
}

impl ImageGroupNames {
    /// Every name this file owns, derived from the struct's own fields.
    #[must_use]
    pub fn all(&self) -> Vec<(&'static str, NameId)> {
        vec![
            ("AlgS.Hom.imageCarrier", self.image_carrier),
            ("AlgS.Hom.imageGroup", self.image_group),
            ("AlgS.Hom.induced", self.induced),
            ("AlgS.Hom.firstIsoClassical", self.first_iso_classical),
        ]
    }
}

/// The five `AlgS.Hom` names this file consumes, all declared by
/// `structures_setoid::declare_structures_s_extra`.
#[derive(Debug, Clone, Copy)]
pub struct ImageGroupDeps {
    /// `AlgS.Hom.image : Π G H f, H.carrier → Prop`.
    pub image: NameId,
    /// `AlgS.Hom.mapOne : ∀ G H f fCongr fMul, H.equiv (f G.e) H.e`.
    pub map_one: NameId,
    /// `AlgS.Hom.mapInv : ∀ G H f fCongr fMul a,
    /// H.equiv (f (G.inv a)) (H.inv (f a))`.
    pub map_inv: NameId,
    /// `AlgS.Hom.image_mem : ∀ G H f fCongr fMul a, image G H f (f a)`.
    pub image_mem: NameId,
    /// `AlgS.Hom.quotient : Π G H f fCongr fMul, AlgS.Group`.
    pub quotient: NameId,
}

// Free-variable ids. Disjoint from `structures::CTOR_FVAR_BASE` (10_000) /
// `SELECTOR_S_FV` (10_900), `structures_setoid`'s `V_*` (9_800..) and `FI_*`
// (21_700..21_712), `subgroup_setoid` (24_000..24_043), `metric` (20_800..) and
// `intspace` (21_800..).
const IG_G: u64 = 26_500;
const IG_H: u64 = 26_501;
const IG_F: u64 = 26_502;
const IG_FC: u64 = 26_503;
const IG_FM: u64 = 26_504;
const IG_X: u64 = 26_505;
const IG_XP: u64 = 26_506;
const IG_Y: u64 = 26_507;
const IG_YP: u64 = 26_508;
const IG_Z: u64 = 26_509;
const IG_A: u64 = 26_510;
const IG_B: u64 = 26_511;
const IG_HA: u64 = 26_512;
const IG_HB: u64 = 26_513;
const IG_H1: u64 = 26_514;
const IG_H2: u64 = 26_515;
const IG_W: u64 = 26_516;

fn t_app(k: &mut Kernel, f: ExprId, xs: &[ExprId]) -> ExprId {
    let mut out = f;
    for &x in xs {
        out = k.app(out, x);
    }
    out
}

/// The homomorphism context: the five binders `G H f fCongr fMul` and the
/// selectors this file reads off `G` and `H`.
///
/// Rebuilt here rather than shared with `structures_setoid::hom_ctx`, which is
/// private to that file; the shapes are pinned against it by
/// `image_group_tests::the_hom_binder_types_match_the_existing_hom_layer`.
struct Ctx {
    group_ty: ExprId,
    g: ExprId,
    h: ExprId,
    f: ExprId,
    fc: ExprId,
    fm: ExprId,
    f_ty: ExprId,
    fc_ty: ExprId,
    fm_ty: ExprId,
    gc: ExprId,
    g_op: ExprId,
    g_e: ExprId,
    g_inv: ExprId,
    hc: ExprId,
    h_equiv: ExprId,
    h_refl: ExprId,
    h_symm: ExprId,
    h_trans: ExprId,
    h_op: ExprId,
    h_op_congr: ExprId,
    h_e: ExprId,
    h_inv: ExprId,
    h_inv_congr: ExprId,
    h_assoc: ExprId,
    h_ident_l: ExprId,
    h_ident_r: ExprId,
    h_inv_l: ExprId,
    h_inv_r: ExprId,
}

fn ctx(k: &mut Kernel, group: &RecordNames) -> Ctx {
    use idx::group::{
        ASSOC, CARRIER, E, EQUIV, EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, IDENT_L, IDENT_R, INV,
        INV_CONGR, INV_L, INV_R, OP, OP_CONGR,
    };
    let group_ty = k.const_(group.ind, vec![]);
    let g = k.fvar(IG_G);
    let h = k.fvar(IG_H);
    let f = k.fvar(IG_F);
    let fc = k.fvar(IG_FC);
    let fm = k.fvar(IG_FM);

    let gc = sel(k, group, CARRIER, g);
    let g_equiv = sel(k, group, EQUIV, g);
    let g_op = sel(k, group, OP, g);
    let g_e = sel(k, group, E, g);
    let g_inv = sel(k, group, INV, g);

    let hc = sel(k, group, CARRIER, h);
    let h_equiv = sel(k, group, EQUIV, h);
    let h_refl = sel(k, group, EQUIV_REFL, h);
    let h_symm = sel(k, group, EQUIV_SYMM, h);
    let h_trans = sel(k, group, EQUIV_TRANS, h);
    let h_op = sel(k, group, OP, h);
    let h_op_congr = sel(k, group, OP_CONGR, h);
    let h_e = sel(k, group, E, h);
    let h_inv = sel(k, group, INV, h);
    let h_inv_congr = sel(k, group, INV_CONGR, h);
    let h_assoc = sel(k, group, ASSOC, h);
    let h_ident_l = sel(k, group, IDENT_L, h);
    let h_ident_r = sel(k, group, IDENT_R, h);
    let h_inv_l = sel(k, group, INV_L, h);
    let h_inv_r = sel(k, group, INV_R, h);

    let f_ty = arrow(k, gc, hc);
    let fc_ty = {
        let a = k.fvar(IG_A);
        let b = k.fvar(IG_B);
        let hyp = app2(k, g_equiv, a, b);
        let fa = k.app(f, a);
        let fb = k.app(f, b);
        let concl = app2(k, h_equiv, fa, fb);
        let t = arrow(k, hyp, concl);
        let t = pi_over(k, IG_B, gc, t);
        pi_over(k, IG_A, gc, t)
    };
    let fm_ty = {
        let a = k.fvar(IG_A);
        let b = k.fvar(IG_B);
        let ab = app2(k, g_op, a, b);
        let f_ab = k.app(f, ab);
        let fa = k.app(f, a);
        let fb = k.app(f, b);
        let rhs = app2(k, h_op, fa, fb);
        let concl = app2(k, h_equiv, f_ab, rhs);
        let t = pi_over(k, IG_B, gc, concl);
        pi_over(k, IG_A, gc, t)
    };

    Ctx {
        group_ty,
        g,
        h,
        f,
        fc,
        fm,
        f_ty,
        fc_ty,
        fm_ty,
        gc,
        g_op,
        g_e,
        g_inv,
        hc,
        h_equiv,
        h_refl,
        h_symm,
        h_trans,
        h_op,
        h_op_congr,
        h_e,
        h_inv,
        h_inv_congr,
        h_assoc,
        h_ident_l,
        h_ident_r,
        h_inv_l,
        h_inv_r,
    }
}

/// Close over `G H f` (what a DEFINITION not mentioning the two proofs needs).
fn close_ghf(k: &mut Kernel, c: &Ctx, body: ExprId, lam: bool) -> ExprId {
    let bind = |k: &mut Kernel, fv: u64, ty: ExprId, body: ExprId| {
        if lam {
            lam_over(k, fv, ty, body)
        } else {
            pi_over(k, fv, ty, body)
        }
    };
    let t = bind(k, IG_F, c.f_ty, body);
    let t = bind(k, IG_H, c.group_ty, t);
    bind(k, IG_G, c.group_ty, t)
}

/// Close over `G H f fCongr fMul` (the five binders every `AlgS.Hom` theorem
/// and every image construction needs).
fn close_hom(k: &mut Kernel, c: &Ctx, body: ExprId, lam: bool) -> ExprId {
    let bind = |k: &mut Kernel, fv: u64, ty: ExprId, body: ExprId| {
        if lam {
            lam_over(k, fv, ty, body)
        } else {
            pi_over(k, fv, ty, body)
        }
    };
    let t = bind(k, IG_FM, c.fm_ty, body);
    let t = bind(k, IG_FC, c.fc_ty, t);
    close_ghf(k, c, t, lam)
}

/// `H.equiv x y`.
fn heq(k: &mut Kernel, c: &Ctx, x: ExprId, y: ExprId) -> ExprId {
    app2(k, c.h_equiv, x, y)
}

/// The `Subtype` vocabulary at `H.carrier` and `AlgS.Hom.image G H f`.
struct Sub {
    /// `Subtype.{1} H.carrier (image G H f)`, unfolded.
    carrier: ExprId,
    /// `Subtype.val.{1} H.carrier (image …)` — apply to one argument.
    val_head: ExprId,
    /// `Subtype.property.{1} H.carrier (image …)` — apply to one argument.
    property_head: ExprId,
    /// `Subtype.mk.{1} H.carrier (image …)` — apply to a value and a proof.
    mk_head: ExprId,
}

fn sub(k: &mut Kernel, lg: &LogicPrelude, l1: LevelId, c: &Ctx, deps: &ImageGroupDeps) -> Sub {
    let predicate = {
        let head = k.const_(deps.image, vec![]);
        t_app(k, head, &[c.g, c.h, c.f])
    };
    let carrier = {
        let head = k.const_(lg.sigma.subtype, vec![l1]);
        app2(k, head, c.hc, predicate)
    };
    let val_head = {
        let head = k.const_(lg.sigma.subtype_val, vec![l1]);
        app2(k, head, c.hc, predicate)
    };
    let property_head = {
        let head = k.const_(lg.sigma.subtype_property, vec![l1]);
        app2(k, head, c.hc, predicate)
    };
    let mk_head = {
        let head = k.const_(lg.sigma.subtype_mk, vec![l1]);
        app2(k, head, c.hc, predicate)
    };
    Sub {
        carrier,
        val_head,
        property_head,
        mk_head,
    }
}

/// `Exists.rec.{l1} α p (fun _ => goal) minor major` — a non-dependent
/// elimination of `major : Exists α p` into the `Prop` `goal`.
///
/// Legal because `goal` is always a `Prop` here; `Exists` in this kernel has no
/// large elimination, and nothing below asks for one.
fn exists_elim(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    alpha: ExprId,
    predicate: ExprId,
    goal: ExprId,
    minor: ExprId,
    major: ExprId,
) -> ExprId {
    let existential = {
        let head = k.const_(lg.exists_, vec![l1]);
        app2(k, head, alpha, predicate)
    };
    let motive = lam_over(k, IG_W, existential, goal);
    let head = k.const_(lg.exists_rec, vec![l1]);
    t_app(k, head, &[alpha, predicate, motive, minor, major])
}

/// `Exists.intro.{l1} α p w h`.
fn exists_intro(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    alpha: ExprId,
    predicate: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let head = k.const_(lg.exists_intro, vec![l1]);
    t_app(k, head, &[alpha, predicate, witness, proof])
}

/// `fun (a : G.carrier) => H.equiv (f a) target` — the predicate
/// `AlgS.Hom.image G H f target` unfolds to.
fn image_predicate(k: &mut Kernel, c: &Ctx, target: ExprId) -> ExprId {
    let a = k.fvar(IG_A);
    let fa = k.app(c.f, a);
    let body = heq(k, c, fa, target);
    lam_over(k, IG_A, c.gc, body)
}

/// `AlgS.Hom.imageCarrier : Π G H f, Sort 1`.
fn declare_image_carrier(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    group: &RecordNames,
    deps: &ImageGroupDeps,
    name: NameId,
) -> Result<(), KernelError> {
    let c = ctx(k, group);
    let s = sub(k, lg, l1, &c, deps);
    let value = close_ghf(k, &c, s.carrier, true);
    let ty = {
        let sort_one = k.sort(l1);
        close_ghf(k, &c, sort_one, false)
    };
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `AlgS.Hom.imageGroup : Π G H f fCongr fMul, AlgS.Group`.
#[allow(clippy::too_many_lines)]
fn declare_image_group(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    group: &RecordNames,
    deps: &ImageGroupDeps,
    image_carrier: NameId,
    name: NameId,
) -> Result<(), KernelError> {
    let c = ctx(k, group);
    let s = sub(k, lg, l1, &c, deps);

    // The carrier slot, by NAME: `AlgS.Hom.imageCarrier G H f`. Written by name
    // rather than unfolded so `induced`'s codomain and this field are the same
    // term, and so the rendered record says what it is.
    let carrier = {
        let head = k.const_(image_carrier, vec![]);
        t_app(k, head, &[c.g, c.h, c.f])
    };
    let val = |k: &mut Kernel, x: ExprId| {
        let head = s.val_head;
        k.app(head, x)
    };
    let property = |k: &mut Kernel, x: ExprId| {
        let head = s.property_head;
        k.app(head, x)
    };

    // equiv := fun x y => H.equiv x.val y.val.
    let equiv = {
        let x = k.fvar(IG_X);
        let y = k.fvar(IG_Y);
        let vx = val(k, x);
        let vy = val(k, y);
        let body = heq(k, &c, vx, vy);
        let t = lam_over(k, IG_Y, carrier, body);
        lam_over(k, IG_X, carrier, t)
    };
    // The three equivalence laws, each H's own at the underlying values.
    let equiv_refl = {
        let x = k.fvar(IG_X);
        let vx = val(k, x);
        let body = k.app(c.h_refl, vx);
        lam_over(k, IG_X, carrier, body)
    };
    let equiv_symm = {
        let x = k.fvar(IG_X);
        let y = k.fvar(IG_Y);
        let vx = val(k, x);
        let vy = val(k, y);
        let hyp = heq(k, &c, vx, vy);
        let h1 = k.fvar(IG_H1);
        let body = t_app(k, c.h_symm, &[vx, vy, h1]);
        let body = lam_over(k, IG_H1, hyp, body);
        let t = lam_over(k, IG_Y, carrier, body);
        lam_over(k, IG_X, carrier, t)
    };
    let equiv_trans = {
        let x = k.fvar(IG_X);
        let y = k.fvar(IG_Y);
        let z = k.fvar(IG_Z);
        let vx = val(k, x);
        let vy = val(k, y);
        let vz = val(k, z);
        let hyp1 = heq(k, &c, vx, vy);
        let hyp2 = heq(k, &c, vy, vz);
        let h1 = k.fvar(IG_H1);
        let h2 = k.fvar(IG_H2);
        let body = t_app(k, c.h_trans, &[vx, vy, vz, h1, h2]);
        let body = lam_over(k, IG_H2, hyp2, body);
        let body = lam_over(k, IG_H1, hyp1, body);
        let t = lam_over(k, IG_Z, carrier, body);
        let t = lam_over(k, IG_Y, carrier, t);
        lam_over(k, IG_X, carrier, t)
    };

    // op := fun x y => ⟨H.op x.val y.val, memOp x y⟩.
    let op = {
        let x = k.fvar(IG_X);
        let y = k.fvar(IG_Y);
        let vx = val(k, x);
        let vy = val(k, y);
        let product = app2(k, c.h_op, vx, vy);
        let membership = {
            // ∃ a, H.equiv (f a) (H.op x.val y.val).
            let goal_predicate = image_predicate(k, &c, product);
            let goal = {
                let head = k.const_(lg.exists_, vec![l1]);
                app2(k, head, c.gc, goal_predicate)
            };
            let inner_predicate_y = image_predicate(k, &c, vy);
            let inner_predicate_x = image_predicate(k, &c, vx);
            // fun (b : G.carrier) (hb : H.equiv (f b) y.val) => …
            let minor_y = {
                let a = k.fvar(IG_A);
                let b = k.fvar(IG_B);
                let ha = k.fvar(IG_HA);
                let hb = k.fvar(IG_HB);
                let fa = k.app(c.f, a);
                let fb = k.app(c.f, b);
                let ab = app2(k, c.g_op, a, b);
                let f_ab = k.app(c.f, ab);
                let middle = app2(k, c.h_op, fa, fb);
                let step_one = t_app(k, c.fm, &[a, b]);
                let step_two = t_app(k, c.h_op_congr, &[fa, vx, fb, vy, ha, hb]);
                let chained = t_app(k, c.h_trans, &[f_ab, middle, product, step_one, step_two]);
                let intro = exists_intro(k, lg, l1, c.gc, goal_predicate, ab, chained);
                let hb_ty = {
                    let fb = k.app(c.f, b);
                    heq(k, &c, fb, vy)
                };
                let t = lam_over(k, IG_HB, hb_ty, intro);
                lam_over(k, IG_B, c.gc, t)
            };
            let elim_y = {
                let major = property(k, y);
                exists_elim(k, lg, l1, c.gc, inner_predicate_y, goal, minor_y, major)
            };
            let minor_x = {
                let a = k.fvar(IG_A);
                let ha_ty = {
                    let fa = k.app(c.f, a);
                    heq(k, &c, fa, vx)
                };
                let t = lam_over(k, IG_HA, ha_ty, elim_y);
                lam_over(k, IG_A, c.gc, t)
            };
            let major = property(k, x);
            exists_elim(k, lg, l1, c.gc, inner_predicate_x, goal, minor_x, major)
        };
        let body = app2(k, s.mk_head, product, membership);
        let t = lam_over(k, IG_Y, carrier, body);
        lam_over(k, IG_X, carrier, t)
    };

    // opCongr := fun x x' y y' hx hy => H.opCongr x.val x'.val y.val y'.val hx hy.
    let op_congr = {
        let x = k.fvar(IG_X);
        let xp = k.fvar(IG_XP);
        let y = k.fvar(IG_Y);
        let yp = k.fvar(IG_YP);
        let vx = val(k, x);
        let vxp = val(k, xp);
        let vy = val(k, y);
        let vyp = val(k, yp);
        let hyp1 = heq(k, &c, vx, vxp);
        let hyp2 = heq(k, &c, vy, vyp);
        let h1 = k.fvar(IG_H1);
        let h2 = k.fvar(IG_H2);
        let body = t_app(k, c.h_op_congr, &[vx, vxp, vy, vyp, h1, h2]);
        let body = lam_over(k, IG_H2, hyp2, body);
        let body = lam_over(k, IG_H1, hyp1, body);
        let t = lam_over(k, IG_YP, carrier, body);
        let t = lam_over(k, IG_Y, carrier, t);
        let t = lam_over(k, IG_XP, carrier, t);
        lam_over(k, IG_X, carrier, t)
    };

    // e := ⟨H.e, ∃-intro at G.e by AlgS.Hom.mapOne⟩.
    let unit = {
        let goal_predicate = image_predicate(k, &c, c.h_e);
        let map_one = {
            let head = k.const_(deps.map_one, vec![]);
            t_app(k, head, &[c.g, c.h, c.f, c.fc, c.fm])
        };
        let membership = exists_intro(k, lg, l1, c.gc, goal_predicate, c.g_e, map_one);
        app2(k, s.mk_head, c.h_e, membership)
    };

    // inv := fun x => ⟨H.inv x.val, memInv x⟩.
    let inverse = {
        let x = k.fvar(IG_X);
        let vx = val(k, x);
        let inverted = k.app(c.h_inv, vx);
        let membership = {
            let goal_predicate = image_predicate(k, &c, inverted);
            let goal = {
                let head = k.const_(lg.exists_, vec![l1]);
                app2(k, head, c.gc, goal_predicate)
            };
            let inner_predicate = image_predicate(k, &c, vx);
            let minor = {
                let a = k.fvar(IG_A);
                let fa = k.app(c.f, a);
                let ha = k.fvar(IG_HA);
                let ha_ty = heq(k, &c, fa, vx);
                let inv_a = k.app(c.g_inv, a);
                let f_inv_a = k.app(c.f, inv_a);
                let middle = k.app(c.h_inv, fa);
                let step_one = {
                    let head = k.const_(deps.map_inv, vec![]);
                    t_app(k, head, &[c.g, c.h, c.f, c.fc, c.fm, a])
                };
                let step_two = t_app(k, c.h_inv_congr, &[fa, vx, ha]);
                let chained = t_app(
                    k,
                    c.h_trans,
                    &[f_inv_a, middle, inverted, step_one, step_two],
                );
                let intro = exists_intro(k, lg, l1, c.gc, goal_predicate, inv_a, chained);
                let t = lam_over(k, IG_HA, ha_ty, intro);
                lam_over(k, IG_A, c.gc, t)
            };
            let major = property(k, x);
            exists_elim(k, lg, l1, c.gc, inner_predicate, goal, minor, major)
        };
        let body = app2(k, s.mk_head, inverted, membership);
        lam_over(k, IG_X, carrier, body)
    };

    // invCongr := fun x x' h => H.invCongr x.val x'.val h.
    let inv_congr = {
        let x = k.fvar(IG_X);
        let xp = k.fvar(IG_XP);
        let vx = val(k, x);
        let vxp = val(k, xp);
        let hyp = heq(k, &c, vx, vxp);
        let h1 = k.fvar(IG_H1);
        let body = t_app(k, c.h_inv_congr, &[vx, vxp, h1]);
        let body = lam_over(k, IG_H1, hyp, body);
        let t = lam_over(k, IG_XP, carrier, body);
        lam_over(k, IG_X, carrier, t)
    };

    // The five group laws: H's own, at the underlying values.
    let one_point = |k: &mut Kernel, law: ExprId| {
        let x = k.fvar(IG_X);
        let head = s.val_head;
        let vx = k.app(head, x);
        let body = k.app(law, vx);
        lam_over(k, IG_X, carrier, body)
    };
    let assoc = {
        let x = k.fvar(IG_X);
        let y = k.fvar(IG_Y);
        let z = k.fvar(IG_Z);
        let vx = val(k, x);
        let vy = val(k, y);
        let vz = val(k, z);
        let body = t_app(k, c.h_assoc, &[vx, vy, vz]);
        let t = lam_over(k, IG_Z, carrier, body);
        let t = lam_over(k, IG_Y, carrier, t);
        lam_over(k, IG_X, carrier, t)
    };
    let ident_l = one_point(k, c.h_ident_l);
    let ident_r = one_point(k, c.h_ident_r);
    let inv_l = one_point(k, c.h_inv_l);
    let inv_r = one_point(k, c.h_inv_r);

    let fields = [
        carrier,
        equiv,
        equiv_refl,
        equiv_symm,
        equiv_trans,
        op,
        op_congr,
        unit,
        inverse,
        inv_congr,
        assoc,
        ident_l,
        ident_r,
        inv_l,
        inv_r,
    ];
    let instance = mk_instance(k, group, &fields);
    let value = close_hom(k, &c, instance, true);
    let ty = close_hom(k, &c, c.group_ty, false);
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `AlgS.Hom.induced : Π G H f fCongr fMul, G.carrier → imageCarrier G H f`.
fn declare_induced(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    group: &RecordNames,
    deps: &ImageGroupDeps,
    image_carrier: NameId,
    name: NameId,
) -> Result<(), KernelError> {
    let c = ctx(k, group);
    let s = sub(k, lg, l1, &c, deps);
    let codomain = {
        let head = k.const_(image_carrier, vec![]);
        t_app(k, head, &[c.g, c.h, c.f])
    };

    let a = k.fvar(IG_A);
    let fa = k.app(c.f, a);
    let membership = {
        let head = k.const_(deps.image_mem, vec![]);
        t_app(k, head, &[c.g, c.h, c.f, c.fc, c.fm, a])
    };
    let body = app2(k, s.mk_head, fa, membership);
    let value = {
        let t = lam_over(k, IG_A, c.gc, body);
        close_hom(k, &c, t, true)
    };
    let ty = {
        let t = arrow(k, c.gc, codomain);
        close_hom(k, &c, t, false)
    };
    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `AlgS.Hom.firstIsoClassical` — `G/ker f ≅ Im f` between two `AlgS.Group`
/// objects.
fn declare_first_iso_classical(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    group: &RecordNames,
    deps: &ImageGroupDeps,
    image_group: NameId,
    induced: NameId,
    name: NameId,
) -> Result<(), KernelError> {
    use idx::group::{CARRIER, EQUIV, OP};
    let c = ctx(k, group);
    let s = sub(k, lg, l1, &c, deps);
    let five = [c.g, c.h, c.f, c.fc, c.fm];

    let quotient = {
        let head = k.const_(deps.quotient, vec![]);
        t_app(k, head, &five)
    };
    let image = {
        let head = k.const_(image_group, vec![]);
        t_app(k, head, &five)
    };
    let q_carrier = sel(k, group, CARRIER, quotient);
    let q_equiv = sel(k, group, EQUIV, quotient);
    let q_op = sel(k, group, OP, quotient);
    let i_carrier = sel(k, group, CARRIER, image);
    let i_equiv = sel(k, group, EQUIV, image);
    let i_op = sel(k, group, OP, image);
    let induced_head = {
        let head = k.const_(induced, vec![]);
        t_app(k, head, &five)
    };

    // c1 : ∀ a b, Iff (Q.equiv a b) (I.equiv (induced a) (induced b)).
    // Both sides reduce to `H.equiv (f a) (f b)`, so both directions are the
    // identity: `mp` is well-definedness on the quotient, `mpr` is injectivity.
    let (c1_ty, c1_val) = {
        let a = k.fvar(IG_A);
        let b = k.fvar(IG_B);
        let lhs = app2(k, q_equiv, a, b);
        let ua = k.app(induced_head, a);
        let ub = k.app(induced_head, b);
        let rhs = app2(k, i_equiv, ua, ub);
        let iff_const = k.const_(lg.iff, vec![]);
        let body = app2(k, iff_const, lhs, rhs);
        let ty = {
            let t = pi_over(k, IG_B, q_carrier, body);
            pi_over(k, IG_A, q_carrier, t)
        };
        let value = {
            let h1 = k.fvar(IG_H1);
            let mp = lam_over(k, IG_H1, lhs, h1);
            let h2 = k.fvar(IG_H2);
            let mpr = lam_over(k, IG_H2, rhs, h2);
            let intro = k.const_(lg.iff_intro, vec![]);
            let applied = t_app(k, intro, &[lhs, rhs, mp, mpr]);
            let t = lam_over(k, IG_B, q_carrier, applied);
            lam_over(k, IG_A, q_carrier, t)
        };
        (ty, value)
    };

    // c2 : ∀ a b, I.equiv (induced (Q.op a b)) (I.op (induced a) (induced b)).
    // `Q.op` reduces to `G.op` and `(I.op x y).val` to `H.op x.val y.val`, so
    // this IS `fMul`.
    let (c2_ty, c2_val) = {
        let a = k.fvar(IG_A);
        let b = k.fvar(IG_B);
        let ab = app2(k, q_op, a, b);
        let u_ab = k.app(induced_head, ab);
        let ua = k.app(induced_head, a);
        let ub = k.app(induced_head, b);
        let rhs = app2(k, i_op, ua, ub);
        let body = app2(k, i_equiv, u_ab, rhs);
        let ty = {
            let t = pi_over(k, IG_B, q_carrier, body);
            pi_over(k, IG_A, q_carrier, t)
        };
        (ty, c.fm)
    };

    // c3 : ∀ (y : I.carrier), ∃ (a : Q.carrier), I.equiv (induced a) y.
    // This IS `Subtype.property`: `y.property : ∃ a, H.equiv (f a) y.val`.
    let (c3_ty, c3_val) = {
        let y = k.fvar(IG_Y);
        let predicate = {
            let a = k.fvar(IG_A);
            let ua = k.app(induced_head, a);
            let body = app2(k, i_equiv, ua, y);
            lam_over(k, IG_A, q_carrier, body)
        };
        let existential = {
            let head = k.const_(lg.exists_, vec![l1]);
            app2(k, head, q_carrier, predicate)
        };
        let ty = pi_over(k, IG_Y, i_carrier, existential);
        let value = {
            let head = s.property_head;
            let body = k.app(head, y);
            lam_over(k, IG_Y, i_carrier, body)
        };
        (ty, value)
    };

    let and_const = k.const_(lg.and, vec![]);
    let inner_ty = app2(k, and_const, c2_ty, c3_ty);
    let outer_ty = app2(k, and_const, c1_ty, inner_ty);
    let and_intro = k.const_(lg.and_intro, vec![]);
    let inner_val = t_app(k, and_intro, &[c2_ty, c3_ty, c2_val, c3_val]);
    let outer_val = t_app(k, and_intro, &[c1_ty, inner_ty, c1_val, inner_val]);

    let ty = close_hom(k, &c, outer_ty, false);
    let value = close_hom(k, &c, outer_val, true);
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// Declare the image group and the classical first-isomorphism statement.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(crate) fn declare_image_group_all(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    group: &RecordNames,
    deps: &ImageGroupDeps,
    algs: NameId,
) -> Result<ImageGroupNames, KernelError> {
    let hom_ns = k.name_str(algs, "Hom");
    let names = ImageGroupNames {
        image_carrier: k.name_str(hom_ns, "imageCarrier"),
        image_group: k.name_str(hom_ns, "imageGroup"),
        induced: k.name_str(hom_ns, "induced"),
        first_iso_classical: k.name_str(hom_ns, "firstIsoClassical"),
    };
    declare_image_carrier(k, lg, l1, group, deps, names.image_carrier)?;
    declare_image_group(
        k,
        lg,
        l1,
        group,
        deps,
        names.image_carrier,
        names.image_group,
    )?;
    declare_induced(k, lg, l1, group, deps, names.image_carrier, names.induced)?;
    declare_first_iso_classical(
        k,
        lg,
        l1,
        group,
        deps,
        names.image_group,
        names.induced,
        names.first_iso_classical,
    )?;
    Ok(names)
}

#[cfg(test)]
mod image_group_tests {
    use super::{IG_A, IG_F, IG_G, IG_H, ImageGroupNames};
    use crate::env::Declaration;
    use crate::nat_prelude::structures::{app2, sel};
    use crate::nat_prelude::structures_setoid::idx;
    use crate::{Kernel, NatPrelude, build_nat_prelude, on_a_deep_stack};

    fn built() -> (Kernel, NatPrelude, ImageGroupNames) {
        use std::sync::OnceLock;
        static TEMPLATE: OnceLock<(Kernel, NatPrelude)> = OnceLock::new();
        let (kernel, prelude) = TEMPLATE.get_or_init(|| {
            on_a_deep_stack(|| {
                let mut kernel = Kernel::new();
                let prelude = build_nat_prelude(&mut kernel).expect("Nat prelude must build");
                (kernel, prelude)
            })
        });
        let mut kernel = kernel.clone();
        // The names are deliberately not threaded into `NatPrelude` (the
        // `AlgS.Poly.*` precedent), so they are re-interned here from the same
        // root the declaration used.
        let hom_ns = kernel.name_str(prelude.structures_s_names.algs, "Hom");
        let names = ImageGroupNames {
            image_carrier: kernel.name_str(hom_ns, "imageCarrier"),
            image_group: kernel.name_str(hom_ns, "imageGroup"),
            induced: kernel.name_str(hom_ns, "induced"),
            first_iso_classical: kernel.name_str(hom_ns, "firstIsoClassical"),
        };
        (kernel, *prelude, names)
    }

    /// All four land through the trusted gate, with the kinds they claim.
    #[test]
    fn the_image_group_and_the_classical_first_isomorphism_are_admitted() {
        let (kernel, _p, names) = built();
        for (label, name) in [
            ("AlgS.Hom.imageCarrier", names.image_carrier),
            ("AlgS.Hom.imageGroup", names.image_group),
            ("AlgS.Hom.induced", names.induced),
        ] {
            assert!(
                matches!(
                    kernel.environment().get(name),
                    Some(Declaration::Definition { .. })
                ),
                "{label} must be a definition"
            );
        }
        assert!(
            matches!(
                kernel.environment().get(names.first_iso_classical),
                Some(Declaration::Theorem { .. })
            ),
            "AlgS.Hom.firstIsoClassical must be a theorem"
        );
    }

    /// No axiom is added. Paired with the control that a name which was never
    /// declared ALSO has an empty footprint, so the presence assertion is what
    /// carries the claim.
    #[test]
    fn the_image_group_layer_is_axiom_free() {
        let (mut kernel, _p, names) = built();
        for (label, name) in names.all() {
            assert!(
                kernel.environment().get(name).is_some(),
                "{label} must be declared"
            );
            let footprint = kernel.axiom_footprint(name);
            assert!(
                footprint.is_empty(),
                "{label} must be axiom-free, found {} assumption(s)",
                footprint.len()
            );
        }
        let anon = kernel.anon();
        let never = kernel.name_str(anon, "AlgS_Hom_this_name_was_never_declared");
        assert!(kernel.environment().get(never).is_none());
        assert!(
            kernel.axiom_footprint(never).is_empty(),
            "control: a missing name's footprint is empty too"
        );
    }

    /// **The deciding check for ADR-1595's blocked site.** The classical
    /// statement mentions BOTH group objects and the map between them; the
    /// pre-existing `AlgS.Hom.firstIso` mentions neither `imageGroup` nor
    /// `induced`, which is precisely the difference between "the content" and
    /// "the statement".
    #[test]
    fn the_classical_statement_is_about_two_group_objects_and_the_old_one_is_not() {
        let (kernel, p, names) = built();

        let classical = match kernel
            .environment()
            .get(names.first_iso_classical)
            .expect("declared")
        {
            Declaration::Theorem { ty, .. } => *ty,
            _ => panic!("AlgS.Hom.firstIsoClassical must be a theorem"),
        };
        let rendered = kernel.render_lean(classical);
        for needle in [
            "AlgS.Hom.quotient",
            "AlgS.Hom.imageGroup",
            "AlgS.Hom.induced",
            "Iff",
            "Exists",
        ] {
            assert!(
                rendered.contains(needle),
                "the classical statement must mention {needle}: {rendered}"
            );
        }

        let old = match kernel
            .environment()
            .get(p.structures_s_extra.hom_first_iso)
            .expect("AlgS.Hom.firstIso must still be declared")
        {
            Declaration::Theorem { ty, .. } => *ty,
            _ => panic!("AlgS.Hom.firstIso must be a theorem"),
        };
        let old_rendered = kernel.render_lean(old);
        for absent in ["AlgS.Hom.imageGroup", "AlgS.Hom.induced"] {
            assert!(
                !old_rendered.contains(absent),
                "control: the OLD firstIso does not mention {absent}, which is why it was not \
                 the classical statement: {old_rendered}"
            );
        }
        assert!(
            old_rendered.contains("AlgS.Hom.quotient"),
            "control: the old firstIso IS about the quotient, so the comparison above is \
             between two statements and not between a statement and nothing: {old_rendered}"
        );
    }

    /// The image carrier IS the subtype of `H.carrier` cut out by
    /// `AlgS.Hom.image`, and is not `H.carrier` itself.
    #[test]
    fn the_image_carrier_is_the_subtype_of_the_codomain() {
        let (mut kernel, p, names) = built();
        let logic = p.logic;
        let group = &p.structures_s.group;
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);

        let g = kernel.fvar(IG_G);
        let h = kernel.fvar(IG_H);
        let f = kernel.fvar(IG_F);
        let hc = sel(&mut kernel, group, idx::group::CARRIER, h);

        let carrier = {
            let head = kernel.const_(names.image_carrier, vec![]);
            let head = kernel.app(head, g);
            let head = kernel.app(head, h);
            kernel.app(head, f)
        };
        let predicate = {
            let head = kernel.const_(p.structures_s_extra.hom_image, vec![]);
            let head = kernel.app(head, g);
            let head = kernel.app(head, h);
            kernel.app(head, f)
        };
        let expected = {
            let head = kernel.const_(logic.sigma.subtype, vec![one]);
            app2(&mut kernel, head, hc, predicate)
        };
        assert!(
            kernel.def_eq(carrier, expected),
            "AlgS.Hom.imageCarrier must reduce to Subtype H.carrier (AlgS.Hom.image G H f)"
        );
        assert!(
            !kernel.def_eq(carrier, hc),
            "negative control: the image carrier is NOT the whole codomain"
        );
    }

    /// The induced map sends `a` to `f a`, underneath `Subtype.val` — the
    /// property that makes conjuncts 2 and 3 of the classical statement
    /// reduce to `fMul` and `Subtype.property`.
    #[test]
    fn the_induced_map_carries_a_to_f_a() {
        let (mut kernel, p, names) = built();
        let logic = p.logic;
        let group = &p.structures_s.group;
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);

        let g = kernel.fvar(IG_G);
        let h = kernel.fvar(IG_H);
        let f = kernel.fvar(IG_F);
        let fc = kernel.fvar(super::IG_FC);
        let fm = kernel.fvar(super::IG_FM);
        let a = kernel.fvar(IG_A);
        let hc = sel(&mut kernel, group, idx::group::CARRIER, h);
        let h_e = sel(&mut kernel, group, idx::group::E, h);

        let predicate = {
            let head = kernel.const_(p.structures_s_extra.hom_image, vec![]);
            let head = kernel.app(head, g);
            let head = kernel.app(head, h);
            kernel.app(head, f)
        };
        let induced_a = {
            let head = kernel.const_(names.induced, vec![]);
            let head = kernel.app(head, g);
            let head = kernel.app(head, h);
            let head = kernel.app(head, f);
            let head = kernel.app(head, fc);
            let head = kernel.app(head, fm);
            kernel.app(head, a)
        };
        let val = {
            let head = kernel.const_(logic.sigma.subtype_val, vec![one]);
            let head = app2(&mut kernel, head, hc, predicate);
            kernel.app(head, induced_a)
        };
        let fa = kernel.app(f, a);
        assert!(
            kernel.def_eq(val, fa),
            "(AlgS.Hom.induced … a).val must compute to f a"
        );
        assert!(
            !kernel.def_eq(val, h_e),
            "negative control: it does not compute to H.e"
        );
    }
}
