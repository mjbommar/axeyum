//! **Isometries of the plane: the predicate, the group operations, and three
//! families of instance.**
//!
//! `CPoint.Isometry f := ∀ P Q, Equiv (distSq (f P) (f Q)) (distSq P Q)`.
//!
//! Stated over `distSq`, not over `Metric.CPoint.dist`, for two reasons. It is
//! the same condition — `sqrt` is injective on the nonnegatives, and
//! `Metric.CPoint.dist` is literally `sqrt ∘ distSq` — but `distSq` is
//! square-root-free, so every instance below is discharged by the ring
//! normalizer alone, and `metric.rs` is a *later* prelude than this one, so a
//! `dist`-shaped definition could not live here at all.
//!
//! ## What is here
//!
//! | | |
//! |---|---|
//! | group structure | `idMap`, `comp`, `isometry_id`, `isometry_comp` |
//! | instances | `translate` (every `T`), `rotate c s` and `reflect c s` (`c² + s² = 1`) |
//! | the non-example | `scale r`, `scale_distSq`, and `not_isometry_scale_two` |
//! | toward classification | `isometry_preserves_dot` |
//!
//! **No angle appears anywhere.** A rotation is parameterised by a *pair*
//! `(c, s)` with `c² + s² ~ 1`, never by an angle, which is what makes the
//! whole family reachable without `arccos` (see `creal_point/angle.rs`) — and
//! `CPoint.sin_sq_add_cos_sq` says every `(cosAngle, sinAngle)` pair is
//! admissible input, so the two halves of this lane meet there.
//!
//! ## The negative control is a theorem, not a test
//!
//! `CPoint.not_isometry_scale_two : Isometry (scale two) → False` is proved,
//! constructively, by instantiating the hypothesis at `(1,0)` and `(0,0)`:
//! the doubling map takes `distSq = 1` to `distSq = 4`, so `4 ~ 1`, so
//! `1 + 1 ~ −1` after two `add_right_cancel` steps, so `0 ≤ −1`, which
//! `CReal.not_le_zero_neg_one` refutes by computation. A map that scales by
//! two is refused, and the refusal is checked by the kernel rather than
//! asserted in prose.
//!
//! ## The classification, sized honestly
//!
//! "Every isometry is a rotation-or-reflection after a translation" is **not**
//! here. What it needs, beyond what this file lands:
//!
//! 1. `isometry_preserves_dot` (landed here) at `R := 0`, giving that
//!    `u := f(e₁) − f(0)` and `v := f(e₂) − f(0)` are orthonormal.
//! 2. A scalar multiple of a point (`CPoint.smul`) with its `dot` bilinearity
//!    laws — six lemmas, none hard, none present.
//! 3. `f(P) − f(0) ~ Px·u + Py·v`, proved by showing the difference `W` has
//!    `⟨W,W⟩ ~ 0` and closing with the existing
//!    `CPoint.eq_zero_of_dot_self_zero`. This is the real work: expanding
//!    `⟨W,W⟩` needs step 2 throughout.
//! 4. The `±` split. `u = (c,s)` with `c² + s² ~ 1` forces `v = ±(−s,c)`, and
//!    choosing the sign is a **decision on the sign of a real**, which is not
//!    free constructively. It is decidable here — `(u × v)² ~ 1` puts `u × v`
//!    apart from `0`, and `CReal.apart_cotrans` on the threshold pair
//!    `(−1/2, 1/2)` resolves it — but it is a genuine argument, not a case
//!    split.
//!
//! Estimate: four sub-shelves, roughly 25–40 new declarations and 1200–1800
//! lines, dominated by step 2's bilinearity boilerplate and step 4's
//! cotransitivity argument. Too large to fold into this lane; nothing in it is
//! blocked.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::{CPointPrelude, KernelError};

use super::{
    DERIVED_HEIGHT, RnExpr, cadd, chain, cmul, cneg, creal_ty, czero, dotp, equiv,
    neg_add_cancel_proof, one_mul_proof, point_ty, psub, refl, rn_ring_proof, symm, zero_add_proof,
};

// --- local term builders -----------------------------------------------------

fn cone(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    d.kernel().const_(p.creal.one, vec![])
}

fn dist_sqp(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.dist_sq, &[a, b])
}

fn theorem(d: &mut IntDev<'_>, name: NameId, ty: ExprId, value: ExprId) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CPoint → CPoint`, the type every map here has.
fn map_ty(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    let point = point_ty(d, p);
    d.arrow(point, point)
}

/// The `RnExpr` mirror of `CPoint.x`/`CPoint.y` on a point-valued expression:
/// used only where the point is a bound variable, so the projection is opaque.
fn coord(d: &mut IntDev<'_>, p: CPointPrelude, pt: ExprId) -> (RnExpr, RnExpr) {
    let px = d.const_app(p.x, &[pt]);
    let py = d.const_app(p.y, &[pt]);
    (RnExpr::Atom(px), RnExpr::Atom(py))
}

/// `(a − b)` as an `RnExpr`.
fn rsub(a: RnExpr, b: RnExpr) -> RnExpr {
    RnExpr::add(a, RnExpr::neg(b))
}

/// The `RnExpr` for `distSq` given the two points' coordinate expressions.
fn rdist_sq(ax: RnExpr, ay: RnExpr, bx: RnExpr, by: RnExpr) -> RnExpr {
    let dx = rsub(ax, bx);
    let dy = rsub(ay, by);
    RnExpr::add(RnExpr::mul(dx.clone(), dx), RnExpr::mul(dy.clone(), dy))
}

// --- the predicate and the group operations ----------------------------------

/// `CPoint.Isometry f := ∀ P Q, Equiv (distSq (f P) (f Q)) (distSq P Q)`.
pub(super) fn declare_isometry(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let maps = map_ty(d, p);
    let prop = d.kernel().sort_zero();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let fp = d.kernel().app(f, pp);
    let fq = d.kernel().app(f, q);
    let lhs = dist_sqp(d, p, fp, fq);
    let rhs = dist_sqp(d, p, pp, q);
    let claim = equiv(d, p, lhs, rhs);
    let body = {
        let inner = d.pi_fv(q_fv, point, claim);
        d.pi_fv(pp_fv, point, inner)
    };
    let value = d.lam_fv(f_fv, maps, body);
    let ty = d.arrow(maps, prop);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.isometry,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 40),
    })
}

/// `CPoint.idMap := fun P => P`.
pub(super) fn declare_id_map(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let value = d.lam_fv(pp_fv, point, pp);
    let ty = map_ty(d, p);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.id_map,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 41),
    })
}

/// `CPoint.comp f g := fun P => f (g P)`.
pub(super) fn declare_comp_map(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let maps = map_ty(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);

    let gp = d.kernel().app(g, pp);
    let fgp = d.kernel().app(f, gp);
    let value = {
        let w0 = d.lam_fv(pp_fv, point, fgp);
        let w1 = d.lam_fv(g_fv, maps, w0);
        d.lam_fv(f_fv, maps, w1)
    };
    let ty = {
        let w0 = d.arrow(maps, maps);
        d.arrow(maps, w0)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.comp_map,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 42),
    })
}

/// `CPoint.isometry_id : Isometry idMap` — `equiv_refl`, after `idMap P`
/// beta-reduces to `P`.
pub(super) fn declare_isometry_id(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let dsq = dist_sqp(d, p, pp, q);
    let body = refl(d, p, dsq);
    let value = {
        let inner = d.lam_fv(q_fv, point, body);
        d.lam_fv(pp_fv, point, inner)
    };
    let id_map = d.kernel().const_(p.id_map, vec![]);
    let ty = d.const_app(p.isometry, &[id_map]);
    theorem(d, p.isometry_id, ty, value)
}

/// `CPoint.isometry_comp : ∀ f g, Isometry f → Isometry g → Isometry (comp f g)`
/// — `equiv_trans` of the two hypotheses at `(g P, g Q)` and `(P, Q)`. This
/// plus [`CPointPrelude::isometry_id`] is the monoid structure; inverses need
/// surjectivity, which is not carried by the predicate.
pub(super) fn declare_isometry_comp(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let maps = map_ty(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let hf_ty = d.const_app(p.isometry, &[f]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_ty = d.const_app(p.isometry, &[g]);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let gp = d.kernel().app(g, pp);
    let gq = d.kernel().app(g, q);
    let fgp = d.kernel().app(f, gp);
    let fgq = d.kernel().app(f, gq);

    let outer = {
        let a = d.kernel().app(hf, gp);
        d.kernel().app(a, gq)
    }; // Equiv (distSq (f (g P)) (f (g Q))) (distSq (g P) (g Q))
    let inner = {
        let a = d.kernel().app(hg, pp);
        d.kernel().app(a, q)
    }; // Equiv (distSq (g P) (g Q)) (distSq P Q)

    let lhs = dist_sqp(d, p, fgp, fgq);
    let mid = dist_sqp(d, p, gp, gq);
    let rhs = dist_sqp(d, p, pp, q);
    let body = d.lemma(p.creal.equiv_trans, &[lhs, mid, rhs, outer, inner]);

    let composed = d.const_app(p.comp_map, &[f, g]);
    let concl = d.const_app(p.isometry, &[composed]);
    let ty = {
        let w0 = d.pi_fv(hg_fv, hg_ty, concl);
        let w1 = d.pi_fv(hf_fv, hf_ty, w0);
        let w2 = d.pi_fv(g_fv, maps, w1);
        d.pi_fv(f_fv, maps, w2)
    };
    let value = {
        let w0 = d.lam_fv(q_fv, point, body);
        let w1 = d.lam_fv(pp_fv, point, w0);
        let w2 = d.lam_fv(hg_fv, hg_ty, w1);
        let w3 = d.lam_fv(hf_fv, hf_ty, w2);
        let w4 = d.lam_fv(g_fv, maps, w3);
        d.lam_fv(f_fv, maps, w4)
    };
    theorem(d, p.isometry_comp, ty, value)
}

// --- translations ------------------------------------------------------------

/// `CPoint.translate T := fun P => CPoint.add P T`.
pub(super) fn declare_translate(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let body = d.const_app(p.point_add, &[pp, t]);
    let value = {
        let inner = d.lam_fv(pp_fv, point, body);
        d.lam_fv(t_fv, point, inner)
    };
    let ty = {
        let inner = d.arrow(point, point);
        d.arrow(point, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.translate,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 43),
    })
}

/// `CPoint.isometry_translate : ∀ T, Isometry (translate T)` — the shift
/// cancels in each coordinate difference; one ring-normalizer call, no
/// hypothesis at all.
pub(super) fn declare_isometry_translate(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let (px, py) = coord(d, p, pp);
    let (qx, qy) = coord(d, p, q);
    let (tx, ty_e) = coord(d, p, t);
    let lhs_expr = rdist_sq(
        RnExpr::add(px.clone(), tx.clone()),
        RnExpr::add(py.clone(), ty_e.clone()),
        RnExpr::add(qx.clone(), tx),
        RnExpr::add(qy.clone(), ty_e),
    );
    let rhs_expr = rdist_sq(px, py, qx, qy);
    let body = rn_ring_proof(d, p.creal, &lhs_expr, &rhs_expr);

    let translate_t = d.const_app(p.translate, &[t]);
    let concl = d.const_app(p.isometry, &[translate_t]);
    let ty = d.pi_fv(t_fv, point, concl);
    let value = {
        let w0 = d.lam_fv(q_fv, point, body);
        let w1 = d.lam_fv(pp_fv, point, w0);
        d.lam_fv(t_fv, point, w1)
    };
    theorem(d, p.isometry_translate, ty, value)
}

// --- rotations and reflections ----------------------------------------------

/// `CPoint.rotate c s := fun P => mk (c·Px − s·Py) (s·Px + c·Py)`.
///
/// **Parameterised by the pair, not by an angle.** `c` and `s` are two reals
/// constrained only where a theorem needs them
/// ([`CPointPrelude::isometry_rotate`] asks for `c² + s² ~ 1`), so the family
/// is definable with no `arccos`, no `sin`, and no analytic input.
pub(super) fn declare_rotate(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);

    let px = d.const_app(p.x, &[pp]);
    let py = d.const_app(p.y, &[pp]);
    let c_px = cmul(d, p, c, px);
    let s_py = cmul(d, p, s, py);
    let neg_s_py = cneg(d, p, s_py);
    let new_x = cadd(d, p, c_px, neg_s_py);
    let s_px = cmul(d, p, s, px);
    let c_py = cmul(d, p, c, py);
    let new_y = cadd(d, p, s_px, c_py);
    let body = d.const_app(p.mk, &[new_x, new_y]);

    let value = {
        let w0 = d.lam_fv(pp_fv, point, body);
        let w1 = d.lam_fv(s_fv, carrier, w0);
        d.lam_fv(c_fv, carrier, w1)
    };
    let ty = {
        let w0 = d.arrow(point, point);
        let w1 = d.arrow(carrier, w0);
        d.arrow(carrier, w1)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.rotate,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 44),
    })
}

/// `CPoint.reflect c s := fun P => mk (c·Px + s·Py) (s·Px − c·Py)`.
///
/// Reflection in the line through the origin whose direction is the
/// half-angle of `(c, s)`. Same normalisation `c² + s² ~ 1`, opposite
/// determinant.
pub(super) fn declare_reflect(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);

    let px = d.const_app(p.x, &[pp]);
    let py = d.const_app(p.y, &[pp]);
    let c_px = cmul(d, p, c, px);
    let s_py = cmul(d, p, s, py);
    let new_x = cadd(d, p, c_px, s_py);
    let s_px = cmul(d, p, s, px);
    let c_py = cmul(d, p, c, py);
    let neg_c_py = cneg(d, p, c_py);
    let new_y = cadd(d, p, s_px, neg_c_py);
    let body = d.const_app(p.mk, &[new_x, new_y]);

    let value = {
        let w0 = d.lam_fv(pp_fv, point, body);
        let w1 = d.lam_fv(s_fv, carrier, w0);
        d.lam_fv(c_fv, carrier, w1)
    };
    let ty = {
        let w0 = d.arrow(point, point);
        let w1 = d.arrow(carrier, w0);
        d.arrow(carrier, w1)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.reflect,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 45),
    })
}

/// The shared body of [`declare_isometry_rotate`] and
/// [`declare_isometry_reflect`]: given the two images' coordinate expressions
/// as functions of `(c, s, Px, Py)` and `(c, s, Qx, Qy)`, prove
/// `distSq (map P) (map Q) ~ distSq P Q` from `hcs : c² + s² ~ 1`.
#[allow(clippy::too_many_arguments)]
fn orthogonal_map_body(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    hcs: ExprId,
    c: ExprId,
    s: ExprId,
    image_x: RnExpr,
    image_y: RnExpr,
    other_x: RnExpr,
    other_y: RnExpr,
    px: RnExpr,
    py: RnExpr,
    qx: RnExpr,
    qy: RnExpr,
    lhs_term: ExprId,
    dsq_pq: ExprId,
) -> ExprId {
    let cr = p.creal;
    let lhs_expr = rdist_sq(image_x, image_y, other_x, other_y);
    let ec = RnExpr::Atom(c);
    let es = RnExpr::Atom(s);
    let gram = RnExpr::add(RnExpr::mul(ec.clone(), ec), RnExpr::mul(es.clone(), es));
    let rhs_expr = RnExpr::mul(gram, rdist_sq(px, py, qx, qy));
    let ring = rn_ring_proof(d, p.creal, &lhs_expr, &rhs_expr);

    let cc = cmul(d, p, c, c);
    let ss = cmul(d, p, s, s);
    let gram_term = cadd(d, p, cc, ss);
    let scaled = cmul(d, p, gram_term, dsq_pq);
    let one = cone(d, p);
    let refl_dsq = refl(d, p, dsq_pq);
    let congr = d.lemma(
        cr.mul_congr,
        &[gram_term, one, dsq_pq, dsq_pq, hcs, refl_dsq],
    );
    let one_dsq = cmul(d, p, one, dsq_pq);
    let om = one_mul_proof(d, p, dsq_pq);
    chain(
        d,
        p,
        lhs_term,
        &[(scaled, ring), (one_dsq, congr), (dsq_pq, om)],
    )
}

/// `CPoint.isometry_rotate : ∀ c s, Equiv (add (mul c c) (mul s s)) CReal.one
/// → Isometry (rotate c s)`.
pub(super) fn declare_isometry_rotate(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let cc = cmul(d, p, c, c);
    let ss = cmul(d, p, s, s);
    let gram_term = cadd(d, p, cc, ss);
    let one = cone(d, p);
    let hyp_ty = equiv(d, p, gram_term, one);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let (px, py) = coord(d, p, pp);
    let (qx, qy) = coord(d, p, q);
    let ec = RnExpr::Atom(c);
    let es = RnExpr::Atom(s);
    let rot_x = |xe: &RnExpr, ye: &RnExpr| {
        RnExpr::add(
            RnExpr::mul(ec.clone(), xe.clone()),
            RnExpr::neg(RnExpr::mul(es.clone(), ye.clone())),
        )
    };
    let rot_y = |xe: &RnExpr, ye: &RnExpr| {
        RnExpr::add(
            RnExpr::mul(es.clone(), xe.clone()),
            RnExpr::mul(ec.clone(), ye.clone()),
        )
    };
    let image_x = rot_x(&px, &py);
    let image_y = rot_y(&px, &py);
    let other_x = rot_x(&qx, &qy);
    let other_y = rot_y(&qx, &qy);

    let rot = d.const_app(p.rotate, &[c, s]);
    let rp = d.kernel().app(rot, pp);
    let rq = d.kernel().app(rot, q);
    let lhs_term = dist_sqp(d, p, rp, rq);
    let dsq_pq = dist_sqp(d, p, pp, q);
    let body = orthogonal_map_body(
        d, p, h, c, s, image_x, image_y, other_x, other_y, px, py, qx, qy, lhs_term, dsq_pq,
    );

    let concl = d.const_app(p.isometry, &[rot]);
    let ty = {
        let w0 = d.pi_fv(h_fv, hyp_ty, concl);
        let w1 = d.pi_fv(s_fv, carrier, w0);
        d.pi_fv(c_fv, carrier, w1)
    };
    let value = {
        let w0 = d.lam_fv(q_fv, point, body);
        let w1 = d.lam_fv(pp_fv, point, w0);
        let w2 = d.lam_fv(h_fv, hyp_ty, w1);
        let w3 = d.lam_fv(s_fv, carrier, w2);
        d.lam_fv(c_fv, carrier, w3)
    };
    theorem(d, p.isometry_rotate, ty, value)
}

/// `CPoint.isometry_reflect : ∀ c s, Equiv (add (mul c c) (mul s s)) CReal.one
/// → Isometry (reflect c s)`.
pub(super) fn declare_isometry_reflect(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let cc = cmul(d, p, c, c);
    let ss = cmul(d, p, s, s);
    let gram_term = cadd(d, p, cc, ss);
    let one = cone(d, p);
    let hyp_ty = equiv(d, p, gram_term, one);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let (px, py) = coord(d, p, pp);
    let (qx, qy) = coord(d, p, q);
    let ec = RnExpr::Atom(c);
    let es = RnExpr::Atom(s);
    let ref_x = |xe: &RnExpr, ye: &RnExpr| {
        RnExpr::add(
            RnExpr::mul(ec.clone(), xe.clone()),
            RnExpr::mul(es.clone(), ye.clone()),
        )
    };
    let ref_y = |xe: &RnExpr, ye: &RnExpr| {
        RnExpr::add(
            RnExpr::mul(es.clone(), xe.clone()),
            RnExpr::neg(RnExpr::mul(ec.clone(), ye.clone())),
        )
    };
    let image_x = ref_x(&px, &py);
    let image_y = ref_y(&px, &py);
    let other_x = ref_x(&qx, &qy);
    let other_y = ref_y(&qx, &qy);

    let refl_map = d.const_app(p.reflect, &[c, s]);
    let rp = d.kernel().app(refl_map, pp);
    let rq = d.kernel().app(refl_map, q);
    let lhs_term = dist_sqp(d, p, rp, rq);
    let dsq_pq = dist_sqp(d, p, pp, q);
    let body = orthogonal_map_body(
        d, p, h, c, s, image_x, image_y, other_x, other_y, px, py, qx, qy, lhs_term, dsq_pq,
    );

    let concl = d.const_app(p.isometry, &[refl_map]);
    let ty = {
        let w0 = d.pi_fv(h_fv, hyp_ty, concl);
        let w1 = d.pi_fv(s_fv, carrier, w0);
        d.pi_fv(c_fv, carrier, w1)
    };
    let value = {
        let w0 = d.lam_fv(q_fv, point, body);
        let w1 = d.lam_fv(pp_fv, point, w0);
        let w2 = d.lam_fv(h_fv, hyp_ty, w1);
        let w3 = d.lam_fv(s_fv, carrier, w2);
        d.lam_fv(c_fv, carrier, w3)
    };
    theorem(d, p.isometry_reflect, ty, value)
}

// --- the non-example ---------------------------------------------------------

/// `CPoint.scale r := fun P => mk (r·Px) (r·Py)`.
pub(super) fn declare_scale(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let px = d.const_app(p.x, &[pp]);
    let py = d.const_app(p.y, &[pp]);
    let new_x = cmul(d, p, r, px);
    let new_y = cmul(d, p, r, py);
    let body = d.const_app(p.mk, &[new_x, new_y]);
    let value = {
        let inner = d.lam_fv(pp_fv, point, body);
        d.lam_fv(r_fv, carrier, inner)
    };
    let ty = {
        let inner = d.arrow(point, point);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.scale,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 46),
    })
}

/// `CPoint.scale_distSq : ∀ r P Q,
/// Equiv (distSq (scale r P) (scale r Q)) (mul (mul r r) (distSq P Q))`.
///
/// The exact scaling law, stated for every `r`: a dilation multiplies squared
/// distance by `r²`, so it is an isometry only where `r² ~ 1`. This is the
/// positive statement whose `r := two` instance
/// [`CPointPrelude::not_isometry_scale_two`] turns into a refutation.
pub(super) fn declare_scale_dist_sq(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let (px, py) = coord(d, p, pp);
    let (qx, qy) = coord(d, p, q);
    let er = RnExpr::Atom(r);
    let lhs_expr = rdist_sq(
        RnExpr::mul(er.clone(), px.clone()),
        RnExpr::mul(er.clone(), py.clone()),
        RnExpr::mul(er.clone(), qx.clone()),
        RnExpr::mul(er.clone(), qy.clone()),
    );
    let rhs_expr = RnExpr::mul(RnExpr::mul(er.clone(), er), rdist_sq(px, py, qx, qy));
    let body = rn_ring_proof(d, p.creal, &lhs_expr, &rhs_expr);

    let scale_r = d.const_app(p.scale, &[r]);
    let sp = d.kernel().app(scale_r, pp);
    let sq = d.kernel().app(scale_r, q);
    let lhs = dist_sqp(d, p, sp, sq);
    let rr = cmul(d, p, r, r);
    let dsq = dist_sqp(d, p, pp, q);
    let rhs = cmul(d, p, rr, dsq);
    let concl = equiv(d, p, lhs, rhs);
    let ty = {
        let w0 = d.pi_fv(q_fv, point, concl);
        let w1 = d.pi_fv(pp_fv, point, w0);
        d.pi_fv(r_fv, carrier, w1)
    };
    let value = {
        let w0 = d.lam_fv(q_fv, point, body);
        let w1 = d.lam_fv(pp_fv, point, w0);
        d.lam_fv(r_fv, carrier, w1)
    };
    theorem(d, p.scale_dist_sq, ty, value)
}

/// `CPoint.not_isometry_scale_two : Isometry (scale CPoint.Scalar.two) → False`.
///
/// **The negative control, as a theorem.** Instantiate the hypothesis at
/// `(1,0)` and `(0,0)`: the ring normalizer computes both `distSq` values
/// directly (`2·2` and `1`), so `2·2 ~ 1`; unfolding `two` and cancelling on
/// the right twice (`CReal.add_right_cancel`) leaves `1 + 1 ~ −1`; and
/// `0 ≤ 1` then gives `0 ≤ −1`, which `CReal.not_le_zero_neg_one` refutes by
/// computation at index 3. No `Apart`, no decidability, no case split.
pub(super) fn declare_not_isometry_scale_two(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let cr = p.creal;
    let two = d.kernel().const_(p.two, vec![]);
    let scale_two = d.const_app(p.scale, &[two]);
    let hyp_ty = d.const_app(p.isometry, &[scale_two]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let one = cone(d, p);
    let zero = czero(d, p);
    let e1 = d.const_app(p.mk, &[one, zero]);
    let e0 = d.const_app(p.mk, &[zero, zero]);

    let s1 = d.kernel().app(scale_two, e1);
    let s0 = d.kernel().app(scale_two, e0);
    let lhs = dist_sqp(d, p, s1, s0);
    let rhs = dist_sqp(d, p, e1, e0);
    let iso = {
        let a = d.kernel().app(h, e1);
        d.kernel().app(a, e0)
    }; // Equiv lhs rhs

    // distSq (2·e1) (2·e0) ~ 2·2, by the normalizer at the two literal points.
    let et = RnExpr::Atom(two);
    let scaled_lhs = rdist_sq(
        RnExpr::mul(et.clone(), RnExpr::One),
        RnExpr::mul(et.clone(), RnExpr::Zero),
        RnExpr::mul(et.clone(), RnExpr::Zero),
        RnExpr::mul(et.clone(), RnExpr::Zero),
    );
    let two_two_expr = RnExpr::mul(et.clone(), et);
    let lhs_value = rn_ring_proof(d, p.creal, &scaled_lhs, &two_two_expr);
    let two_two = cmul(d, p, two, two);
    let lhs_value_symm = symm(d, p, lhs, two_two, lhs_value);

    // distSq e1 e0 ~ 1.
    let unit_lhs = rdist_sq(RnExpr::One, RnExpr::Zero, RnExpr::Zero, RnExpr::Zero);
    let rhs_value = rn_ring_proof(d, p.creal, &unit_lhs, &RnExpr::One);

    // 2·2 ~ 1.
    let four_eq_one = chain(
        d,
        p,
        two_two,
        &[(lhs, lhs_value_symm), (rhs, iso), (one, rhs_value)],
    );

    // 2·2 ~ ((1+1)+1)+1, by the normalizer after `two` delta-unfolds.
    let one_one = RnExpr::add(RnExpr::One, RnExpr::One);
    let four_expr = RnExpr::add(RnExpr::add(one_one.clone(), RnExpr::One), RnExpr::One);
    let two_prod_expr = RnExpr::mul(one_one, RnExpr::add(RnExpr::One, RnExpr::One));
    let expand = rn_ring_proof(d, p.creal, &two_prod_expr, &four_expr);
    let one_plus_one = cadd(d, p, one, one);
    let three = cadd(d, p, one_plus_one, one);
    let four = cadd(d, p, three, one);
    let two_two_is_four = chain(d, p, two_two, &[(four, expand)]);
    let expand_symm = symm(d, p, two_two, four, two_two_is_four);
    let four_is_one = chain(d, p, four, &[(two_two, expand_symm), (one, four_eq_one)]);

    // ((1+1)+1)+1 ~ 0+1, then cancel `+1`.
    let zero_one = cadd(d, p, zero, one);
    let za = zero_add_proof(d, p, one); // Equiv (0+1) 1
    let za_symm = symm(d, p, zero_one, one, za);
    let step_a = chain(d, p, four, &[(one, four_is_one), (zero_one, za_symm)]);
    let three_is_zero = d.lemma(p.add_right_cancel, &[three, zero, one, step_a]);

    // (1+1)+1 ~ (−1)+1, then cancel `+1`.
    let neg_one = cneg(d, p, one);
    let neg_one_one = cadd(d, p, neg_one, one);
    let nac = neg_add_cancel_proof(d, p, one); // Equiv ((−1)+1) 0
    let nac_symm = symm(d, p, neg_one_one, zero, nac);
    let step_b = chain(
        d,
        p,
        three,
        &[(zero, three_is_zero), (neg_one_one, nac_symm)],
    );
    let two_is_neg_one = d.lemma(p.add_right_cancel, &[one_plus_one, neg_one, one, step_b]);

    // 0 ≤ 1 ≤ 1+1 ~ −1, contradicting `not_le_zero_neg_one`.
    let one_one_term = one_plus_one;
    let sq = d.lemma(cr.sq_nonneg, &[one]);
    let one_sq = cmul(d, p, one, one);
    let mo = d.lemma(cr.mul_one, &[one]);
    let refl_zero = refl(d, p, zero);
    let zero_le_one = d.lemma(cr.le_congr, &[zero, zero, one_sq, one, refl_zero, mo, sq]);
    let refl_le_one = d.lemma(cr.le_refl, &[one]);
    let summed = d.lemma(
        cr.add_le_add,
        &[zero, one, one, one, zero_le_one, refl_le_one],
    ); // le (0+1) (1+1)
    let one_le_neg_one = d.lemma(
        cr.le_congr,
        &[
            zero_one,
            one,
            one_one_term,
            neg_one,
            za,
            two_is_neg_one,
            summed,
        ],
    ); // le 1 (−1)
    let bad = d.lemma(
        cr.le_trans,
        &[zero, one, neg_one, zero_le_one, one_le_neg_one],
    ); // le 0 (−1)
    let body = d.lemma(cr.not_le_zero_neg_one, &[bad]);

    let false_ty = d.false_ty();
    let ty = d.pi_fv(h_fv, hyp_ty, false_ty);
    let value = d.lam_fv(h_fv, hyp_ty, body);
    theorem(d, p.not_isometry_scale_two, ty, value)
}

// --- toward the classification ----------------------------------------------

/// `Equiv (add (dot (sub X Z) (sub Y Z)) (dot (sub X Z) (sub Y Z)))
///        (add (add (distSq X Z) (distSq Y Z)) (neg (distSq X Y)))`
/// — the **polarization identity**, in the doubled form that avoids `inv2`.
/// Pure coordinate ring algebra at six atoms and degree two.
fn polarization(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    xpt: ExprId,
    ypt: ExprId,
    zpt: ExprId,
) -> ExprId {
    let (xx, xy) = coord(d, p, xpt);
    let (yx, yy) = coord(d, p, ypt);
    let (zx, zy) = coord(d, p, zpt);
    let ax = rsub(xx.clone(), zx.clone());
    let ay = rsub(xy.clone(), zy.clone());
    let bx = rsub(yx.clone(), zx.clone());
    let by = rsub(yy.clone(), zy.clone());
    let dot_ab = RnExpr::add(
        RnExpr::mul(ax.clone(), bx.clone()),
        RnExpr::mul(ay.clone(), by.clone()),
    );
    let lhs = RnExpr::add(dot_ab.clone(), dot_ab);
    let rhs = RnExpr::add(
        RnExpr::add(
            rdist_sq(xx.clone(), xy.clone(), zx.clone(), zy.clone()),
            rdist_sq(yx.clone(), yy.clone(), zx, zy),
        ),
        RnExpr::neg(rdist_sq(xx, xy, yx, yy)),
    );
    rn_ring_proof(d, p.creal, &lhs, &rhs)
}

/// From `h : Equiv (add u u) (add v v)`, produce `Equiv u v` — halving,
/// through `CPoint.Scalar.inv2`.
fn halve(d: &mut IntDev<'_>, p: CPointPrelude, u: ExprId, v: ExprId, h: ExprId) -> ExprId {
    let cr = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let uu = cadd(d, p, u, u);
    let vv = cadd(d, p, v, v);
    let half_uu = cmul(d, p, inv2, uu);
    let half_vv = cmul(d, p, inv2, vv);
    let refl_inv2 = refl(d, p, inv2);
    let scaled = d.lemma(cr.mul_congr, &[inv2, inv2, uu, vv, refl_inv2, h]);
    let left = half_cancel(d, p, u);
    let right = half_cancel(d, p, v);
    let left_symm = symm(d, p, half_uu, u, left);
    chain(
        d,
        p,
        u,
        &[(half_uu, left_symm), (half_vv, scaled), (v, right)],
    )
}

/// `Equiv (mul inv2 (add a a)) a`.
fn half_cancel(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId) -> ExprId {
    let cr = p.creal;
    let inv2 = d.kernel().const_(p.inv2, vec![]);
    let aa = cadd(d, p, a, a);
    let lhs = cmul(d, p, inv2, aa);
    let ld = d.lemma(cr.left_distrib, &[inv2, a, a]);
    let ia = cmul(d, p, inv2, a);
    let ia_ia = cadd(d, p, ia, ia);
    let hd = super::half_double_proof(d, p, a); // Equiv a (inv2·a + inv2·a)
    let hd_symm = symm(d, p, a, ia_ia, hd);
    chain(d, p, lhs, &[(ia_ia, ld), (a, hd_symm)])
}

/// `CPoint.isometry_preserves_dot : ∀ f, Isometry f → ∀ P Q R,
/// Equiv (dot (sub (f P) (f R)) (sub (f Q) (f R))) (dot (sub P R) (sub Q R))`.
///
/// **An isometry preserves the inner product of differences**, not just their
/// lengths — the polarization identity plus the hypothesis at the three pairs
/// `(P,R)`, `(Q,R)`, `(P,Q)`, then one halving through `inv2`. This is step 1
/// of the classification (see the module doc): at `R := 0` it says the images
/// of an orthonormal frame are orthonormal, which is what forces the linear
/// part into `O(2)`.
pub(super) fn declare_isometry_preserves_dot(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let cr = p.creal;
    let point = point_ty(d, p);
    let maps = map_ty(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let hyp_ty = d.const_app(p.isometry, &[f]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let fp = d.kernel().app(f, pp);
    let fq = d.kernel().app(f, q);
    let fr = d.kernel().app(f, r);

    let apply = |d: &mut IntDev<'_>, a: ExprId, b: ExprId| {
        let t = d.kernel().app(h, a);
        d.kernel().app(t, b)
    };
    let h_pr = apply(d, pp, r);
    let h_qr = apply(d, q, r);
    let h_pq = apply(d, pp, q);

    let img_pol = polarization(d, p, fp, fq, fr);
    let src_pol = polarization(d, p, pp, q, r);

    let img_dot = {
        let a = psub(d, p, fp, fr);
        let b = psub(d, p, fq, fr);
        dotp(d, p, a, b)
    };
    let src_dot = {
        let a = psub(d, p, pp, r);
        let b = psub(d, p, q, r);
        dotp(d, p, a, b)
    };
    let img_double = cadd(d, p, img_dot, img_dot);
    let src_double = cadd(d, p, src_dot, src_dot);

    let img_pr = dist_sqp(d, p, fp, fr);
    let img_qr = dist_sqp(d, p, fq, fr);
    let img_pq = dist_sqp(d, p, fp, fq);
    let src_pr = dist_sqp(d, p, pp, r);
    let src_qr = dist_sqp(d, p, q, r);
    let src_pq = dist_sqp(d, p, pp, q);

    let img_sum = cadd(d, p, img_pr, img_qr);
    let src_sum = cadd(d, p, src_pr, src_qr);
    let sum_congr = d.lemma(cr.add_congr, &[img_pr, src_pr, img_qr, src_qr, h_pr, h_qr]);
    let neg_img_pq = cneg(d, p, img_pq);
    let neg_src_pq = cneg(d, p, src_pq);
    let neg_congr = d.lemma(cr.neg_congr, &[img_pq, src_pq, h_pq]);
    let img_rhs = cadd(d, p, img_sum, neg_img_pq);
    let src_rhs = cadd(d, p, src_sum, neg_src_pq);
    let outer = d.lemma(
        cr.add_congr,
        &[
            img_sum, src_sum, neg_img_pq, neg_src_pq, sum_congr, neg_congr,
        ],
    );
    let src_pol_symm = symm(d, p, src_double, src_rhs, src_pol);
    let doubled = chain(
        d,
        p,
        img_double,
        &[
            (img_rhs, img_pol),
            (src_rhs, outer),
            (src_double, src_pol_symm),
        ],
    );
    let body = halve(d, p, img_dot, src_dot, doubled);

    let concl = equiv(d, p, img_dot, src_dot);
    let ty = {
        let w0 = d.pi_fv(r_fv, point, concl);
        let w1 = d.pi_fv(q_fv, point, w0);
        let w2 = d.pi_fv(pp_fv, point, w1);
        let w3 = d.pi_fv(h_fv, hyp_ty, w2);
        d.pi_fv(f_fv, maps, w3)
    };
    let value = {
        let w0 = d.lam_fv(r_fv, point, body);
        let w1 = d.lam_fv(q_fv, point, w0);
        let w2 = d.lam_fv(pp_fv, point, w1);
        let w3 = d.lam_fv(h_fv, hyp_ty, w2);
        d.lam_fv(f_fv, maps, w3)
    };
    theorem(d, p.isometry_preserves_dot, ty, value)
}
