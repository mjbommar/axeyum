//! **Angle measure on `CPoint`, without `arccos`.**
//!
//! The seam this closes is the one the geometry review calls the most
//! conspicuous in the shelf: `CReal.sin`/`CReal.cos` exist analytically on ℝ
//! and touch no point of the plane. This module joins the two shelves — but
//! **not** by building an angle as a real number in `[0, π]`.
//!
//! ## Why cosine-first, and why `arccos` is not on the route
//!
//! An angle *as a number* needs `arccos`, i.e. an inverse for a monotone
//! function on `[-1, 1]`. Two things block that here, and only one of them is
//! the inverse:
//!
//! 1. `CReal.cos_fn` is a power series with uniform-convergence and
//!    derivative machinery, but **`CReal.sin_sq_add_cos_sq` does not exist,
//!    under any spelling** (checked 2026-09-04 against a freshly rebuilt
//!    `shape_search --include-constructed`, `declarations=3935`). Neither does
//!    an addition theorem. So even with an `arccos` in hand, `sin² + cos² = 1`
//!    — the identity every law of sines is stated against — would still have
//!    to be proved analytically first.
//! 2. The monotone inverse itself is reachable (the IVT-by-bisection layer in
//!    `creal/ivt.rs` gives a root of a continuous sign-changing function), but
//!    it delivers a root, not a *function*, and turning it into one needs a
//!    uniqueness argument plus a congruence obligation for the resulting map.
//!
//! Neither is needed. The **cosine of the angle** is an algebraic object:
//!
//! ```text
//! cosAngle u v := ⟨u,v⟩ / (‖u‖ ‖v‖)      sinAngle u v := |u × v| / (‖u‖ ‖v‖)
//! ```
//!
//! and the Pythagorean identity for *these* is
//! [`CPointPrelude::lagrange_identity`] divided by `‖u‖²‖v‖²` — pure ring
//! algebra over the existing plane, with no series, no derivative and no
//! analytic input whatsoever. [`CPointPrelude::sin_sq_add_cos_sq`] is proved
//! that way here. `arccos` would buy the *name* of the angle and nothing that
//! the laws of sines and cosines actually use.
//!
//! ## Apartness is data, so the denominator is a hypothesis
//!
//! `CReal.inv` consumes a `PosBound` witness, not an `Apart` proof (an
//! `Apart`-indexed inverse would have to eliminate a disjunction into a
//! `Type`, which `Or.rec` forbids — see [`crate::CRealPrelude::inv`]). So
//! [`CPointPrelude::cos_angle`] and [`CPointPrelude::sin_angle`] take
//! `(k : Nat)` and `PosBound (mul (norm U) (norm V)) k` as arguments, exactly
//! the idiom [`CPointPrelude::non_collinear`] already uses for a nonzero
//! determinant. "Both vectors are nonzero" is carried, never assumed.
//!
//! **What is NOT here, and what it would cost.** There is no lemma producing
//! that `PosBound` from `PosBound (dot U U) j` and `PosBound (dot V V) l`.
//! The missing step is `PosBound x k → PosBound (sqrt x) k`, which is
//! reachable from pieces already in `CRealPrelude` — writing
//! `r := ofRat (1/(k+1))`, we have `r·r ≤ r ≤ x ~ sqrt x · sqrt x`, so
//! `le_of_sq_le` closes it — but it needs `Rat.natDivSucc 1 k ≤ Rat.one` and
//! then a second lemma to fuse two moduli through `mul`
//! (`1/(j+1) · 1/(l+1) = 1/((j+1)(l+1))`, a `Nat` index computation). Sized
//! at two lemmas plus two `Rat` facts; not landed here.
//!
//! ## The one theorem that was free
//!
//! [`CPointPrelude::cross_eq_cross_v`] is `equiv_refl`. `CPoint.cross A B C`
//! is *definitionally* `crossV (sub B A) (sub C B)` — the existing triangle
//! determinant is the new vector cross product at the two edge vectors — so
//! every collinearity, area and orientation fact already proved over `cross`
//! is a fact about `sinAngle` with no transport at all.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::{CPointPrelude, KernelError};

use super::{
    DERIVED_HEIGHT, RnExpr, cadd, chain, cmul, cneg, creal_ty, czero, dotp, equiv, point_ty, psub,
    refl, rn_ring_proof, symm,
};

// --- small term builders shared by this module -------------------------------

fn cone(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    d.kernel().const_(p.creal.one, vec![])
}

fn csqrt(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    d.const_app(p.creal.sqrt, &[x])
}

fn cabs(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId) -> ExprId {
    d.const_app(p.creal.abs, &[x])
}

fn cle(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.creal.le, &[x, y])
}

fn normp(d: &mut IntDev<'_>, p: CPointPrelude, v: ExprId) -> ExprId {
    d.const_app(p.norm, &[v])
}

fn cross_vp(d: &mut IntDev<'_>, p: CPointPrelude, u: ExprId, v: ExprId) -> ExprId {
    d.const_app(p.cross_v, &[u, v])
}

fn theorem(d: &mut IntDev<'_>, name: NameId, ty: ExprId, value: ExprId) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.le CReal.zero CReal.one`, built rather than assumed: `sq_nonneg one`
/// gives `0 ≤ 1·1` and `mul_one` rewrites the right side. There is no
/// `CReal.zero_le_one` in `CRealPrelude`.
fn zero_le_one_proof(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    let c = p.creal;
    let one = cone(d, p);
    let zero = czero(d, p);
    let one_one = cmul(d, p, one, one);
    let sq = d.lemma(c.sq_nonneg, &[one]); // le zero (mul one one)
    let mo = d.lemma(c.mul_one, &[one]); // Equiv (mul one one) one
    let refl_zero = refl(d, p, zero);
    d.lemma(c.le_congr, &[zero, zero, one_one, one, refl_zero, mo, sq])
}

// --- the norm ----------------------------------------------------------------

/// `CPoint.norm V := CReal.sqrt (CPoint.dot V V)`.
pub(super) fn declare_norm(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let dvv = dotp(d, p, v, v);
    let body = csqrt(d, p, dvv);
    let value = d.lam_fv(v_fv, point, body);
    let ty = d.arrow(point, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.norm,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 30),
    })
}

/// `CPoint.norm_nonneg : ∀ V, CReal.le CReal.zero (norm V)` — `sqrt_nonneg`,
/// unconditionally (`sqrt` is total).
pub(super) fn declare_norm_nonneg(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let dvv = dotp(d, p, v, v);
    let body = d.lemma(p.creal.sqrt_nonneg, &[dvv]);
    let zero = czero(d, p);
    let nv = normp(d, p, v);
    let concl = cle(d, p, zero, nv);
    let ty = d.pi_fv(v_fv, point, concl);
    let value = d.lam_fv(v_fv, point, body);
    theorem(d, p.norm_nonneg, ty, value)
}

/// `CPoint.norm_sq : ∀ V, Equiv (mul (norm V) (norm V)) (dot V V)` —
/// `mul_self_sqrt` discharged by [`CPointPrelude::dot_self_nonneg`].
pub(super) fn declare_norm_sq(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let dvv = dotp(d, p, v, v);
    let nonneg = d.lemma(p.dot_self_nonneg, &[v]);
    let body = d.lemma(p.creal.mul_self_sqrt, &[dvv, nonneg]);
    let nv = normp(d, p, v);
    let nv_nv = cmul(d, p, nv, nv);
    let concl = equiv(d, p, nv_nv, dvv);
    let ty = d.pi_fv(v_fv, point, concl);
    let value = d.lam_fv(v_fv, point, body);
    theorem(d, p.norm_sq, ty, value)
}

/// `CPoint.norm_congr : ∀ U V, CPoint.Equiv U V → Equiv (norm U) (norm V)` —
/// the setoid obligation `norm` needs before any point-level rewriting under
/// it is legal. `dot_congr` under `sqrt_congr`.
pub(super) fn declare_norm_congr(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let hyp_ty = d.const_app(p.point_equiv, &[u, v]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let duu = dotp(d, p, u, u);
    let dvv = dotp(d, p, v, v);
    let dc = d.lemma(p.dot_congr, &[u, v, u, v, h, h]); // Equiv (dot U U) (dot V V)
    let body = d.lemma(p.creal.sqrt_congr, &[duu, dvv, dc]);

    let nu = normp(d, p, u);
    let nv = normp(d, p, v);
    let concl = equiv(d, p, nu, nv);
    let ty = {
        let w0 = d.pi_fv(h_fv, hyp_ty, concl);
        let w1 = d.pi_fv(v_fv, point, w0);
        d.pi_fv(u_fv, point, w1)
    };
    let value = {
        let w0 = d.lam_fv(h_fv, hyp_ty, body);
        let w1 = d.lam_fv(v_fv, point, w0);
        d.lam_fv(u_fv, point, w1)
    };
    theorem(d, p.norm_congr, ty, value)
}

// --- the vector cross product ------------------------------------------------

/// `CPoint.crossV U V := add (mul (x U) (y V)) (neg (mul (y U) (x V)))`.
pub(super) fn declare_cross_v(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let ux = d.const_app(p.x, &[u]);
    let uy = d.const_app(p.y, &[u]);
    let vx = d.const_app(p.x, &[v]);
    let vy = d.const_app(p.y, &[v]);
    let a = cmul(d, p, ux, vy);
    let b = cmul(d, p, uy, vx);
    let nb = cneg(d, p, b);
    let body = cadd(d, p, a, nb);

    let value = {
        let inner = d.lam_fv(v_fv, point, body);
        d.lam_fv(u_fv, point, inner)
    };
    let ty = {
        let inner = d.arrow(point, carrier);
        d.arrow(point, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cross_v,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 31),
    })
}

/// `CPoint.cross_eq_crossV : ∀ A B C,
/// Equiv (cross A B C) (crossV (sub B A) (sub C B))`.
///
/// **`equiv_refl`.** The two sides are definitionally equal: `x (sub B A)`
/// delta/iota-reduces to `add Bx (neg Ax)`, which is exactly the factor
/// `cross_raw` builds. Landed under its own name anyway, because it is the
/// bridge that makes every existing `cross` theorem — `Collinear`,
/// `NonCollinear`, Ceva, Menelaus, the medial triangle — a statement about
/// the new [`CPointPrelude::sin_angle`] with no transport.
pub(super) fn declare_cross_eq_cross_v(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let cross_abc = d.const_app(p.cross, &[a, b, c]);
    let ba = psub(d, p, b, a);
    let cb = psub(d, p, c, b);
    let cv = cross_vp(d, p, ba, cb);
    let concl = equiv(d, p, cross_abc, cv);
    let body = refl(d, p, cross_abc);

    let ty = {
        let w0 = d.pi_fv(c_fv, point, concl);
        let w1 = d.pi_fv(b_fv, point, w0);
        d.pi_fv(a_fv, point, w1)
    };
    let value = {
        let w0 = d.lam_fv(c_fv, point, body);
        let w1 = d.lam_fv(b_fv, point, w0);
        d.lam_fv(a_fv, point, w1)
    };
    theorem(d, p.cross_eq_cross_v, ty, value)
}

/// `CPoint.lagrange_vector : ∀ U V,
/// Equiv (add (mul (dot U U) (dot V V)) (neg (mul (dot U V) (dot U V))))
///       (mul (crossV U V) (crossV U V))`.
///
/// `‖u‖²‖v‖² − ⟨u,v⟩² = (u × v)²`. The proof is
/// [`CPointPrelude::lagrange_identity`] applied at the four coordinates and
/// nothing else: every one of the four compound factors in that scalar
/// statement is *definitionally* the `dot`/`crossV` term it stands for.
pub(super) fn declare_lagrange_vector(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let ux = d.const_app(p.x, &[u]);
    let uy = d.const_app(p.y, &[u]);
    let vx = d.const_app(p.x, &[v]);
    let vy = d.const_app(p.y, &[v]);
    let body = d.lemma(p.lagrange_identity, &[ux, uy, vx, vy]);

    let duu = dotp(d, p, u, u);
    let dvv = dotp(d, p, v, v);
    let duv = dotp(d, p, u, v);
    let prod = cmul(d, p, duu, dvv);
    let sq = cmul(d, p, duv, duv);
    let nsq = cneg(d, p, sq);
    let lhs = cadd(d, p, prod, nsq);
    let cv = cross_vp(d, p, u, v);
    let rhs = cmul(d, p, cv, cv);
    let concl = equiv(d, p, lhs, rhs);

    let ty = {
        let inner = d.pi_fv(v_fv, point, concl);
        d.pi_fv(u_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(v_fv, point, body);
        d.lam_fv(u_fv, point, inner)
    };
    theorem(d, p.lagrange_vector, ty, value)
}

// --- the law of cosines, in `dot` form ---------------------------------------

/// `CPoint.law_of_cosines_dot : ∀ U V,
/// Equiv (distSq U V) (add (add (dot U U) (dot V V)) (neg (add (dot U V) (dot U V))))`.
///
/// `‖u − v‖² = ‖u‖² + ‖v‖² − 2⟨u,v⟩`, with `2X` written `X + X` (this file's
/// convention). [`CPointPrelude::dot_self_sub`] regrouped: its own right side
/// interleaves the two negated cross terms, and the classical statement wants
/// them collected. `distSq U V` is definitionally its left side.
pub(super) fn declare_law_of_cosines_dot(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let duu = dotp(d, p, u, u);
    let dvv = dotp(d, p, v, v);
    let duv = dotp(d, p, u, v);
    let nduv = cneg(d, p, duv);

    let uv = psub(d, p, u, v);
    let lhs = dotp(d, p, uv, uv);
    let expand = d.lemma(p.dot_self_sub, &[u, v]);
    let inner2 = cadd(d, p, nduv, dvv);
    let inner1 = cadd(d, p, nduv, inner2);
    let mid = cadd(d, p, duu, inner1);

    let ea = RnExpr::Atom(duu);
    let eb = RnExpr::Atom(duv);
    let ec = RnExpr::Atom(dvv);
    let mid_expr = RnExpr::add(
        ea.clone(),
        RnExpr::add(
            RnExpr::neg(eb.clone()),
            RnExpr::add(RnExpr::neg(eb.clone()), ec.clone()),
        ),
    );
    let rhs_expr = RnExpr::add(
        RnExpr::add(ea, ec),
        RnExpr::neg(RnExpr::add(eb.clone(), eb)),
    );
    let regroup = rn_ring_proof(d, p.creal, &mid_expr, &rhs_expr);

    let sum = cadd(d, p, duu, dvv);
    let two_duv = cadd(d, p, duv, duv);
    let neg_two = cneg(d, p, two_duv);
    let rhs = cadd(d, p, sum, neg_two);
    let body = chain(d, p, lhs, &[(mid, expand), (rhs, regroup)]);

    let dist = d.const_app(p.dist_sq, &[u, v]);
    let concl = equiv(d, p, dist, rhs);
    let ty = {
        let inner = d.pi_fv(v_fv, point, concl);
        d.pi_fv(u_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(v_fv, point, body);
        d.lam_fv(u_fv, point, inner)
    };
    theorem(d, p.law_of_cosines_dot, ty, value)
}

// --- cosAngle / sinAngle -----------------------------------------------------

/// The four binders `cosAngle`/`sinAngle` and every theorem about them share:
/// `U V : CPoint`, `k : Nat`, `h : PosBound (mul (norm U) (norm V)) k`.
struct AngleBinders {
    u_fv: u64,
    v_fv: u64,
    k_fv: u64,
    h_fv: u64,
    u: ExprId,
    v: ExprId,
    k: ExprId,
    h: ExprId,
    hyp_ty: ExprId,
    /// `mul (norm U) (norm V)`.
    n: ExprId,
    /// `inv n k h`.
    inv: ExprId,
}

fn angle_binders(d: &mut IntDev<'_>, p: CPointPrelude) -> AngleBinders {
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let nu = normp(d, p, u);
    let nv = normp(d, p, v);
    let n = cmul(d, p, nu, nv);
    let hyp_ty = d.const_app(p.creal.pos_bound, &[n, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let inv = d.const_app(p.creal.inv, &[n, k, h]);
    AngleBinders {
        u_fv,
        v_fv,
        k_fv,
        h_fv,
        u,
        v,
        k,
        h,
        hyp_ty,
        n,
        inv,
    }
}

fn close_angle(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    b: &AngleBinders,
    concl: ExprId,
    body: ExprId,
) -> (ExprId, ExprId) {
    let point = point_ty(d, p);
    let nat = d.nat_ty();
    let ty = {
        let w0 = d.pi_fv(b.h_fv, b.hyp_ty, concl);
        let w1 = d.pi_fv(b.k_fv, nat, w0);
        let w2 = d.pi_fv(b.v_fv, point, w1);
        d.pi_fv(b.u_fv, point, w2)
    };
    let value = {
        let w0 = d.lam_fv(b.h_fv, b.hyp_ty, body);
        let w1 = d.lam_fv(b.k_fv, nat, w0);
        let w2 = d.lam_fv(b.v_fv, point, w1);
        d.lam_fv(b.u_fv, point, w2)
    };
    (ty, value)
}

/// `CPoint.cosAngle U V k h := mul (dot U V) (inv (mul (norm U) (norm V)) k h)`.
pub(super) fn declare_cos_angle(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let b = angle_binders(d, p);
    let duv = dotp(d, p, b.u, b.v);
    let body = cmul(d, p, duv, b.inv);
    let carrier = creal_ty(d, p);
    let (ty, value) = close_angle(d, p, &b, carrier, body);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cos_angle,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 32),
    })
}

/// `CPoint.sinAngle U V k h := mul (abs (crossV U V)) (inv (mul (norm U) (norm V)) k h)`.
///
/// `abs`, not a signed cross product: `sinAngle` is the *unsigned* sine of the
/// angle between two vectors, which is what the law of sines states and what
/// [`CPointPrelude::sin_sq_add_cos_sq`] needs (`|c|·|c| ~ c·c` by
/// `mul_self_abs`). A signed version would need an orientation, i.e. a
/// decision on the sign of a real, which is not available.
pub(super) fn declare_sin_angle(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let b = angle_binders(d, p);
    let cv = cross_vp(d, p, b.u, b.v);
    let acv = cabs(d, p, cv);
    let body = cmul(d, p, acv, b.inv);
    let carrier = creal_ty(d, p);
    let (ty, value) = close_angle(d, p, &b, carrier, body);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sin_angle,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 33),
    })
}

/// `CPoint.sin_sq_add_cos_sq : ∀ U V k h,
/// Equiv (add (mul (sinAngle …) (sinAngle …)) (mul (cosAngle …) (cosAngle …)))
///       CReal.one`.
///
/// **The Pythagorean identity for the angle, with no trigonometry in it.**
/// Writing `A := |u × v|`, `t := ⟨u,v⟩`, `n := ‖u‖‖v‖`, `i := n⁻¹`, the whole
/// proof is five rewrites:
///
/// ```text
/// (A i)² + (t i)²  =  (A² + t²) i²         ring
///                  =  (c² + t²) i²         mul_self_abs
///                  =  (⟨u,u⟩⟨v,v⟩) i²      lagrange_vector, then ring
///                  =  (n n) (i i)          norm_sq twice, then ring
///                  =  1                    mul_inv_cancel, mul_one
/// ```
pub(super) fn declare_sin_sq_add_cos_sq(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let b = angle_binders(d, p);
    let nu = normp(d, p, b.u);
    let nv = normp(d, p, b.v);
    let cv = cross_vp(d, p, b.u, b.v);
    let acv = cabs(d, p, cv);
    let duv = dotp(d, p, b.u, b.v);
    let duu = dotp(d, p, b.u, b.u);
    let dvv = dotp(d, p, b.v, b.v);
    let i = b.inv;

    let sin_t = cmul(d, p, acv, i);
    let cos_t = cmul(d, p, duv, i);
    let sin_sq = cmul(d, p, sin_t, sin_t);
    let cos_sq = cmul(d, p, cos_t, cos_t);
    let start = cadd(d, p, sin_sq, cos_sq);

    // step 1 (ring): (A i)² + (t i)² ~ (A² + t²) · i²
    let ea = RnExpr::Atom(acv);
    let et = RnExpr::Atom(duv);
    let ei = RnExpr::Atom(i);
    let lhs_expr = RnExpr::add(
        RnExpr::mul(
            RnExpr::mul(ea.clone(), ei.clone()),
            RnExpr::mul(ea.clone(), ei.clone()),
        ),
        RnExpr::mul(
            RnExpr::mul(et.clone(), ei.clone()),
            RnExpr::mul(et.clone(), ei.clone()),
        ),
    );
    let factored_expr = RnExpr::mul(
        RnExpr::add(
            RnExpr::mul(ea.clone(), ea.clone()),
            RnExpr::mul(et.clone(), et.clone()),
        ),
        RnExpr::mul(ei.clone(), ei.clone()),
    );
    let step1 = rn_ring_proof(d, p.creal, &lhs_expr, &factored_expr);
    let a_sq = cmul(d, p, acv, acv);
    let t_sq = cmul(d, p, duv, duv);
    let i_sq = cmul(d, p, i, i);
    let sum_a_t = cadd(d, p, a_sq, t_sq);
    let factored = cmul(d, p, sum_a_t, i_sq);

    // step 2: |c|·|c| ~ c·c
    let c_sq = cmul(d, p, cv, cv);
    let msa = d.lemma(c.mul_self_abs, &[cv]);
    let refl_tsq = refl(d, p, t_sq);
    let sum_c_t = cadd(d, p, c_sq, t_sq);
    let sum_congr = d.lemma(c.add_congr, &[a_sq, c_sq, t_sq, t_sq, msa, refl_tsq]);
    let refl_isq = refl(d, p, i_sq);
    let step2 = d.lemma(
        c.mul_congr,
        &[sum_a_t, sum_c_t, i_sq, i_sq, sum_congr, refl_isq],
    );
    let factored2 = cmul(d, p, sum_c_t, i_sq);

    // step 3: c² + t² ~ ⟨u,u⟩⟨v,v⟩, through lagrange_vector then one ring step
    let prod = cmul(d, p, duu, dvv);
    let nt_sq = cneg(d, p, t_sq);
    let lag_lhs = cadd(d, p, prod, nt_sq);
    let lag = d.lemma(p.lagrange_vector, &[b.u, b.v]); // Equiv lag_lhs c_sq
    let lag_symm = symm(d, p, lag_lhs, c_sq, lag);
    let lag_congr = d.lemma(
        c.add_congr,
        &[c_sq, lag_lhs, t_sq, t_sq, lag_symm, refl_tsq],
    );
    let expanded = cadd(d, p, lag_lhs, t_sq);
    let e_prod = RnExpr::mul(RnExpr::Atom(duu), RnExpr::Atom(dvv));
    let e_tsq = RnExpr::mul(et.clone(), et.clone());
    let cancel_lhs = RnExpr::add(
        RnExpr::add(e_prod.clone(), RnExpr::neg(e_tsq.clone())),
        e_tsq,
    );
    let cancel = rn_ring_proof(d, p.creal, &cancel_lhs, &e_prod);
    let step3 = chain(d, p, sum_c_t, &[(expanded, lag_congr), (prod, cancel)]);
    let step3_mul = d.lemma(c.mul_congr, &[sum_c_t, prod, i_sq, i_sq, step3, refl_isq]);
    let factored3 = cmul(d, p, prod, i_sq);

    // step 4: ⟨u,u⟩⟨v,v⟩ ~ (‖u‖‖u‖)(‖v‖‖v‖)
    let nu_sq = cmul(d, p, nu, nu);
    let nv_sq = cmul(d, p, nv, nv);
    let nsu = d.lemma(p.norm_sq, &[b.u]); // Equiv nu_sq duu
    let nsv = d.lemma(p.norm_sq, &[b.v]);
    let nsu_symm = symm(d, p, nu_sq, duu, nsu);
    let nsv_symm = symm(d, p, nv_sq, dvv, nsv);
    let prod_norm = cmul(d, p, nu_sq, nv_sq);
    let step4 = d.lemma(c.mul_congr, &[duu, nu_sq, dvv, nv_sq, nsu_symm, nsv_symm]);
    let step4_mul = d.lemma(c.mul_congr, &[prod, prod_norm, i_sq, i_sq, step4, refl_isq]);
    let factored4 = cmul(d, p, prod_norm, i_sq);

    // step 5 (ring): (‖u‖²‖v‖²) i² ~ (n i)(n i)
    let enu = RnExpr::Atom(nu);
    let env = RnExpr::Atom(nv);
    let lhs5 = RnExpr::mul(
        RnExpr::mul(
            RnExpr::mul(enu.clone(), enu.clone()),
            RnExpr::mul(env.clone(), env.clone()),
        ),
        RnExpr::mul(ei.clone(), ei.clone()),
    );
    let n_i = RnExpr::mul(RnExpr::mul(enu, env), ei);
    let rhs5 = RnExpr::mul(n_i.clone(), n_i);
    let step5 = rn_ring_proof(d, p.creal, &lhs5, &rhs5);
    let ni = cmul(d, p, b.n, i);
    let ni_ni = cmul(d, p, ni, ni);

    // step 6: n·n⁻¹ ~ 1, then 1·1 ~ 1
    let one = cone(d, p);
    let mic = d.lemma(c.mul_inv_cancel, &[b.n, b.k, b.h]);
    let mic2 = d.lemma(c.mul_inv_cancel, &[b.n, b.k, b.h]);
    let step6 = d.lemma(c.mul_congr, &[ni, one, ni, one, mic, mic2]);
    let one_one = cmul(d, p, one, one);
    let step7 = d.lemma(c.mul_one, &[one]);

    let body = chain(
        d,
        p,
        start,
        &[
            (factored, step1),
            (factored2, step2),
            (factored3, step3_mul),
            (factored4, step4_mul),
            (ni_ni, step5),
            (one_one, step6),
            (one, step7),
        ],
    );

    let sin_named = d.const_app(p.sin_angle, &[b.u, b.v, b.k, b.h]);
    let cos_named = d.const_app(p.cos_angle, &[b.u, b.v, b.k, b.h]);
    let sin_named_sq = cmul(d, p, sin_named, sin_named);
    let cos_named_sq = cmul(d, p, cos_named, cos_named);
    let lhs_named = cadd(d, p, sin_named_sq, cos_named_sq);
    let concl = equiv(d, p, lhs_named, one);
    let (ty, value) = close_angle(d, p, &b, concl, body);
    theorem(d, p.sin_sq_add_cos_sq, ty, value)
}

/// `CPoint.abs_cos_angle_le_one : ∀ U V k h, le (abs (cosAngle …)) CReal.one`.
///
/// **Unsquared Cauchy–Schwarz, read off the Pythagorean identity.** `sin² ≥ 0`
/// (`sq_nonneg`) makes `cos² ≤ sin² + cos² ~ 1`, and `le_of_sq_le` at
/// `t := |cos|`, `s := 1` cancels the square — `mul_self_abs` is what supplies
/// the nonnegative `t` that `le_of_sq_le` needs and the raw `cos` does not
/// have (its sign is unknown).
pub(super) fn declare_abs_cos_angle_le_one(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let b = angle_binders(d, p);
    let cv = cross_vp(d, p, b.u, b.v);
    let acv = cabs(d, p, cv);
    let duv = dotp(d, p, b.u, b.v);
    let i = b.inv;
    let sin_t = cmul(d, p, acv, i);
    let cos_t = cmul(d, p, duv, i);
    let sin_sq = cmul(d, p, sin_t, sin_t);
    let cos_sq = cmul(d, p, cos_t, cos_t);
    let total = cadd(d, p, sin_sq, cos_sq);
    let one = cone(d, p);
    let zero = czero(d, p);

    let pyth = d.lemma(p.sin_sq_add_cos_sq, &[b.u, b.v, b.k, b.h]);
    let sin_nonneg = d.lemma(c.sq_nonneg, &[sin_t]); // le zero sin_sq
    let cos_refl = d.lemma(c.le_refl, &[cos_sq]);
    let summed = d.lemma(
        c.add_le_add,
        &[zero, sin_sq, cos_sq, cos_sq, sin_nonneg, cos_refl],
    ); // le (zero + cos_sq) total
    let zero_cos = cadd(d, p, zero, cos_sq);
    let za = super::zero_add_proof(d, p, cos_sq); // Equiv (zero+cos_sq) cos_sq
    let cos_le_one = d.lemma(
        c.le_congr,
        &[zero_cos, cos_sq, total, one, za, pyth, summed],
    ); // le cos_sq one

    let abs_cos = cabs(d, p, cos_t);
    let abs_sq = cmul(d, p, abs_cos, abs_cos);
    let msa = d.lemma(c.mul_self_abs, &[cos_t]); // Equiv abs_sq cos_sq
    let msa_symm = symm(d, p, abs_sq, cos_sq, msa);
    let one_one = cmul(d, p, one, one);
    let mo = d.lemma(c.mul_one, &[one]); // Equiv (one*one) one
    let mo_symm = symm(d, p, one_one, one, mo);
    let sq_le = d.lemma(
        c.le_congr,
        &[cos_sq, abs_sq, one, one_one, msa_symm, mo_symm, cos_le_one],
    ); // le abs_sq (one*one)

    let abs_nonneg = d.lemma(c.abs_nonneg, &[cos_t]);
    let zle1 = zero_le_one_proof(d, p);
    let body = d.lemma(c.le_of_sq_le, &[abs_cos, one, abs_nonneg, zle1, sq_le]);

    let cos_named = d.const_app(p.cos_angle, &[b.u, b.v, b.k, b.h]);
    let abs_named = cabs(d, p, cos_named);
    let concl = cle(d, p, abs_named, one);
    let (ty, value) = close_angle(d, p, &b, concl, body);
    theorem(d, p.abs_cos_angle_le_one, ty, value)
}

/// `CPoint.cos_angle_le_one : ∀ U V k h, le (cosAngle …) CReal.one`.
pub(super) fn declare_cos_angle_le_one(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let b = angle_binders(d, p);
    let duv = dotp(d, p, b.u, b.v);
    let cos_t = cmul(d, p, duv, b.inv);
    let abs_cos = cabs(d, p, cos_t);
    let one = cone(d, p);
    let self_le = d.lemma(c.le_abs_self, &[cos_t]);
    let bound = d.lemma(p.abs_cos_angle_le_one, &[b.u, b.v, b.k, b.h]);
    let body = d.lemma(c.le_trans, &[cos_t, abs_cos, one, self_le, bound]);

    let cos_named = d.const_app(p.cos_angle, &[b.u, b.v, b.k, b.h]);
    let concl = cle(d, p, cos_named, one);
    let (ty, value) = close_angle(d, p, &b, concl, body);
    theorem(d, p.cos_angle_le_one, ty, value)
}

/// `CPoint.neg_one_le_cos_angle : ∀ U V k h, le (neg CReal.one) (cosAngle …)`.
///
/// The lower half of `−1 ≤ cos θ ≤ 1`, from `neg_le_abs` and `neg_le_neg`.
/// Together with [`CPointPrelude::cos_angle_le_one`] this is the range
/// condition an `arccos` would consume — landed without one.
pub(super) fn declare_neg_one_le_cos_angle(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let b = angle_binders(d, p);
    let duv = dotp(d, p, b.u, b.v);
    let cos_t = cmul(d, p, duv, b.inv);
    let abs_cos = cabs(d, p, cos_t);
    let one = cone(d, p);
    let neg_one = cneg(d, p, one);
    let neg_cos = cneg(d, p, cos_t);

    let nla = d.lemma(c.neg_le_abs, &[cos_t]); // le (neg cos) (abs cos)
    let bound = d.lemma(p.abs_cos_angle_le_one, &[b.u, b.v, b.k, b.h]);
    let neg_le_one = d.lemma(c.le_trans, &[neg_cos, abs_cos, one, nla, bound]);
    let flipped = d.lemma(c.neg_le_neg, &[neg_cos, one, neg_le_one]);
    let nn = super::neg_neg_proof(d, p, cos_t); // Equiv (neg (neg cos)) cos
    let neg_neg_cos = cneg(d, p, neg_cos);
    let refl_neg_one = refl(d, p, neg_one);
    let body = d.lemma(
        c.le_congr,
        &[
            neg_one,
            neg_one,
            neg_neg_cos,
            cos_t,
            refl_neg_one,
            nn,
            flipped,
        ],
    );

    let cos_named = d.const_app(p.cos_angle, &[b.u, b.v, b.k, b.h]);
    let concl = cle(d, p, neg_one, cos_named);
    let (ty, value) = close_angle(d, p, &b, concl, body);
    theorem(d, p.neg_one_le_cos_angle, ty, value)
}

/// `Equiv (mul n (mul w i)) w`, where `n = mul nu nv` and `i = inv n k h`:
/// the one cancellation both `norm_mul_cos_angle` and `law_of_sines` run.
fn cancel_norm_factor(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    b: &AngleBinders,
    nu: ExprId,
    nv: ExprId,
    w: ExprId,
) -> ExprId {
    let c = p.creal;
    let i = b.inv;
    let wi = cmul(d, p, w, i);
    let start = cmul(d, p, b.n, wi);
    let enu = RnExpr::Atom(nu);
    let env = RnExpr::Atom(nv);
    let ei = RnExpr::Atom(i);
    let ew = RnExpr::Atom(w);
    let lhs = RnExpr::mul(
        RnExpr::mul(enu.clone(), env.clone()),
        RnExpr::mul(ew.clone(), ei.clone()),
    );
    let rhs = RnExpr::mul(ew, RnExpr::mul(RnExpr::mul(enu, env), ei));
    let ring = rn_ring_proof(d, p.creal, &lhs, &rhs);
    let ni = cmul(d, p, b.n, i);
    let w_ni = cmul(d, p, w, ni);
    let one = cone(d, p);
    let mic = d.lemma(c.mul_inv_cancel, &[b.n, b.k, b.h]);
    let refl_w = refl(d, p, w);
    let congr = d.lemma(c.mul_congr, &[w, w, ni, one, refl_w, mic]);
    let w_one = cmul(d, p, w, one);
    let mo = d.lemma(c.mul_one, &[w]);
    chain(d, p, start, &[(w_ni, ring), (w_one, congr), (w, mo)])
}

/// `CPoint.norm_mul_cos_angle : ∀ U V k h,
/// Equiv (mul (mul (norm U) (norm V)) (cosAngle …)) (dot U V)`.
///
/// `‖u‖ ‖v‖ cos θ = ⟨u,v⟩` — the bridge that turns
/// [`CPointPrelude::law_of_cosines_dot`] into the classical statement.
pub(super) fn declare_norm_mul_cos_angle(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let b = angle_binders(d, p);
    let nu = normp(d, p, b.u);
    let nv = normp(d, p, b.v);
    let duv = dotp(d, p, b.u, b.v);
    let body = cancel_norm_factor(d, p, &b, nu, nv, duv);

    let cos_named = d.const_app(p.cos_angle, &[b.u, b.v, b.k, b.h]);
    let lhs = cmul(d, p, b.n, cos_named);
    let concl = equiv(d, p, lhs, duv);
    let (ty, value) = close_angle(d, p, &b, concl, body);
    theorem(d, p.norm_mul_cos_angle, ty, value)
}

/// `CPoint.law_of_sines : ∀ U V k h,
/// Equiv (abs (crossV U V)) (mul (mul (norm U) (norm V)) (sinAngle …))`.
///
/// **The law of sines, in the form the plane can state without an angle.**
/// `|u × v| = ‖u‖ ‖v‖ sin θ`; with [`CPointPrelude::cross_eq_cross_v`] the
/// left side is `|cross A B C|`, twice the area of the triangle, so this is
/// also the `½ab sin C` area formula.
pub(super) fn declare_law_of_sines(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let b = angle_binders(d, p);
    let nu = normp(d, p, b.u);
    let nv = normp(d, p, b.v);
    let cv = cross_vp(d, p, b.u, b.v);
    let acv = cabs(d, p, cv);
    let forward = cancel_norm_factor(d, p, &b, nu, nv, acv);
    let acv_i = cmul(d, p, acv, b.inv);
    let lhs_raw = cmul(d, p, b.n, acv_i);
    let body = symm(d, p, lhs_raw, acv, forward);

    let sin_named = d.const_app(p.sin_angle, &[b.u, b.v, b.k, b.h]);
    let rhs = cmul(d, p, b.n, sin_named);
    let concl = equiv(d, p, acv, rhs);
    let (ty, value) = close_angle(d, p, &b, concl, body);
    theorem(d, p.law_of_sines, ty, value)
}

/// `CPoint.law_of_cosines : ∀ U V k h,
/// Equiv (distSq U V)
///       (add (add (mul (norm U) (norm U)) (mul (norm V) (norm V)))
///            (neg (add (mul n (cosAngle …)) (mul n (cosAngle …)))))`
/// with `n := mul (norm U) (norm V)`.
///
/// **`c² = a² + b² − 2ab cos C`, verbatim**, with `2X` written `X + X`.
/// [`CPointPrelude::law_of_cosines_dot`] transported along
/// [`CPointPrelude::norm_sq`] (twice) and
/// [`CPointPrelude::norm_mul_cos_angle`].
pub(super) fn declare_law_of_cosines(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let b = angle_binders(d, p);
    let nu = normp(d, p, b.u);
    let nv = normp(d, p, b.v);
    let duu = dotp(d, p, b.u, b.u);
    let dvv = dotp(d, p, b.v, b.v);
    let duv = dotp(d, p, b.u, b.v);

    let dot_form = d.lemma(p.law_of_cosines_dot, &[b.u, b.v]);
    let sum_dots = cadd(d, p, duu, dvv);
    let two_duv = cadd(d, p, duv, duv);
    let neg_two = cneg(d, p, two_duv);
    let rhs_dot = cadd(d, p, sum_dots, neg_two);

    let nu_sq = cmul(d, p, nu, nu);
    let nv_sq = cmul(d, p, nv, nv);
    let nsu = d.lemma(p.norm_sq, &[b.u]);
    let nsv = d.lemma(p.norm_sq, &[b.v]);
    let nsu_symm = symm(d, p, nu_sq, duu, nsu);
    let nsv_symm = symm(d, p, nv_sq, dvv, nsv);
    let sum_norms = cadd(d, p, nu_sq, nv_sq);
    let sum_congr = d.lemma(c.add_congr, &[duu, nu_sq, dvv, nv_sq, nsu_symm, nsv_symm]);

    let cos_named = d.const_app(p.cos_angle, &[b.u, b.v, b.k, b.h]);
    let n_cos = cmul(d, p, b.n, cos_named);
    let nmc = d.lemma(p.norm_mul_cos_angle, &[b.u, b.v, b.k, b.h]); // Equiv n_cos duv
    let nmc_symm = symm(d, p, n_cos, duv, nmc);
    let nmc_symm2 = symm(d, p, n_cos, duv, nmc);
    let two_ncos = cadd(d, p, n_cos, n_cos);
    let cross_congr = d.lemma(c.add_congr, &[duv, n_cos, duv, n_cos, nmc_symm, nmc_symm2]);
    let neg_cross = d.lemma(c.neg_congr, &[two_duv, two_ncos, cross_congr]);
    let neg_two_ncos = cneg(d, p, two_ncos);
    let rhs_norm = cadd(d, p, sum_norms, neg_two_ncos);
    let outer = d.lemma(
        c.add_congr,
        &[
            sum_dots,
            sum_norms,
            neg_two,
            neg_two_ncos,
            sum_congr,
            neg_cross,
        ],
    );

    let dist = d.const_app(p.dist_sq, &[b.u, b.v]);
    let body = chain(d, p, dist, &[(rhs_dot, dot_form), (rhs_norm, outer)]);
    let concl = equiv(d, p, dist, rhs_norm);
    let (ty, value) = close_angle(d, p, &b, concl, body);
    theorem(d, p.law_of_cosines, ty, value)
}
