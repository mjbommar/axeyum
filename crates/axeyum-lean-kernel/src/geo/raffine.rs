//! `Geo.raffine` — **the real plane satisfies Playfair's parallel axiom**,
//! and it does so with no case split and no principle `creal.rs` does not
//! already prove.
//!
//! Roadmap W3-8, third slice; ADR-1659, discharging ADR-1652 § 5. That
//! section sized this work and recorded three verified polynomial identities;
//! all three are here, and the four helpers it named — `Geo.RPlane.defectAC`,
//! `defectBC`, `defectSwap` and `onOfDefects` — are reused **unchanged**, with
//! `geo/rplane.rs` not edited at all.
//!
//! # The two witnessed predicates, and why they are witnessed
//!
//! ```text
//! Geo.RPlane.offRaw P l    := ∃ k, CReal.PosBound (e_P * e_P) k
//!                              where e_P := a l * x P + b l * y P + c l
//! Geo.RPlane.parPosRaw l m := CReal.Equiv (a l * b m − b l * a m) 0
//!                          ∧ ∃ k, CReal.PosBound (dAC*dAC + dBC*dBC) k
//!                              where dAC := a l * c m − c l * a m
//!                                    dBC := b l * c m − c l * b m
//! ```
//!
//! Read `parPosRaw` as *same direction, and not the same line*. Two coefficient
//! triples describe the same line exactly when all three defects vanish; this
//! says the first vanishes and the other two are **positively bounded away
//! from zero in the square-sum**, which is the same idiom `Geo.RLine0.Nondeg`
//! and `Geo.RPlane.Apart` already use.
//!
//! The negation `(Equiv dAB 0 → False)` would type-check and construct
//! nothing: ADR-1652 § 5's wrong first answer stated uniqueness over the
//! classical `∀ P, on P l → on P m → False` and ended at
//! `Not (Apart (a*B − b*A) 0)`, which is tightness — `creal.rs` documents that
//! as neither proved nor assumed. **The fix was to state the primitive
//! positively, not to acquire a classical principle**, and that is the whole
//! content of this file.
//!
//! # The three obligations, and where each divides
//!
//! | obligation | identity | divided by |
//! | --- | --- | --- |
//! | `parPosDisjoint` | `Geo.RPlane.defectAC`/`defectBC`, unchanged | nothing |
//! | `playfairExists` | `Geo.RPlane.parLineNorm`: `dAC² + dBC² = (a² + b²)·e_P²` | nothing — the two `PosBound`s MULTIPLY |
//! | `playfairUnique` | `Geo.RPlane.dirPivot`: `(a² + b²)(A*B' − B*A') = (a*A + b*B)(a*B' − b*A') − (a*A' + b*B')(a*B − b*A)` | `a² + b²`, once, through `cancelPosBound` |
//!
//! Two things in that table are the measurement worth keeping.
//!
//! **Existence needs no division at all.** The parallel through `P` is
//! `(a, b, −(a·x P + b·y P))` — the SAME leading coefficients, so its
//! non-degeneracy IS `l`'s with nothing to prove — and its distinctness
//! witness is the PRODUCT of `l`'s non-degeneracy modulus and `P`'s
//! off-the-line modulus, assembled by `Geo.RPlane.posBoundMul` out of
//! `CReal.pos_of_pos_bound`, `CReal.mul_pos` and `CReal.pos_bound_of_lt`.
//! Positivity is closed under multiplication constructively; that is the only
//! fact the existence half needs, and it is why the ℝ existence proof is
//! shorter than the ℚ one, which has to reach for `Rat.mul_eq_zero` twice.
//!
//! **Uniqueness divides exactly once, by the same quantity `joinUnique`
//! divides by.** `Geo.RPlane.dirPivot` is a six-variable identity over bare
//! reals with `a² + b²` as its left factor, so `Nondeg l`'s own witness cancels
//! it through `Geo.RPlane.cancelPosBound` — the lemma `rplane.rs` factored out
//! for exactly this. After that the other two defects come from `defectAC` and
//! `defectBC` at the shared point and `onOfDefects` turns the three into
//! extensional line equality in both directions, `defectSwap` supplying the
//! mirrored triple. **No new `CReal.inv` appears in this file.**

#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::GeoPrelude;
use super::RPlaneNames;
use crate::CPointPrelude;
use crate::CRealPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::creal_point::{
    RnExpr, rn_cadd, rn_cmul, rn_cneg, rn_crefl, rn_csymm, rn_ctrans, rn_czero, rn_ring_proof,
};
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;

/// The interned names `declare_all` produces.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RAffineNames {
    /// `Geo.RPlane.offRaw : CPoint → Geo.RLine0 → Prop` —
    /// `∃ k, CReal.PosBound (e_P * e_P) k`. **A witness, not a negation**: the
    /// existence half of Playfair needs the modulus, and
    /// `Geo.RPlane.onRaw P l → False` supplies none.
    pub off_raw: NameId,
    /// `Geo.RPlane.off : CPoint → Geo.RLine → Prop`.
    pub off: NameId,
    /// `Geo.RPlane.parPosRaw : Geo.RLine0 → Geo.RLine0 → Prop` — same
    /// direction, plus a `PosBound` witness that the other two defects do not
    /// both vanish. See the module docs.
    pub par_pos_raw: NameId,
    /// `Geo.RPlane.parPos : Geo.RLine → Geo.RLine → Prop`.
    pub par_pos: NameId,
    /// `Geo.RPlane.offNotOn : ∀ P l, off P l → on P l → False`.
    pub off_not_on: NameId,
    /// `Geo.RPlane.parPosDisjoint : ∀ l m P, parPos l m → on P l → on P m →
    /// False` — a common point forces the other two defects to vanish
    /// (`defectAC`/`defectBC`), contradicting the distinctness witness.
    pub par_pos_disjoint: NameId,
    /// `Geo.RPlane.posBoundMul : ∀ x y j k, PosBound x j → PosBound y k →
    /// ∃ n, PosBound (CReal.mul x y) n` — **positivity is closed under
    /// multiplication**, through `pos_of_pos_bound`, `mul_pos` and
    /// `pos_bound_of_lt`. The modulus cannot be computed from `j` and `k`
    /// without a lower bound on the factors, which is why the conclusion is an
    /// existential; that is harmless because every consumer is a `Prop`.
    pub pos_bound_mul: NameId,
    /// `Geo.RPlane.parLine : CPoint → Geo.RLine0 → Geo.RLine0` —
    /// `(a l, b l, −(a l * x P + b l * y P))`.
    pub par_line: NameId,
    /// `Geo.RPlane.parLineOn : ∀ P l, onRaw P (parLine P l)`.
    pub par_line_on: NameId,
    /// `Geo.RPlane.parLineDir : ∀ P l,
    /// Equiv (a l * b (parLine P l) − b l * a (parLine P l)) 0`.
    pub par_line_dir: NameId,
    /// `Geo.RPlane.parLineNorm : ∀ a b c x y,
    /// Equiv (dAC*dAC + dBC*dBC) ((a*a + b*b) * (e*e))` at the parallel's
    /// coefficients — the identity that turns two `PosBound` witnesses into
    /// the one `parPos` needs.
    pub par_line_norm: NameId,
    /// `Geo.RPlane.playfairExists : ∀ P l, off P l → ∃ m, on P m ∧ parPos l m`.
    pub playfair_exists: NameId,
    /// `Geo.RPlane.dirPivot : ∀ a b A B A' B' j, PosBound (a*a + b*b) j →
    /// Equiv (a*B − b*A) 0 → Equiv (a*B' − b*A') 0 →
    /// Equiv (A*B' − B*A') 0` — **the only division in this file**, and by the
    /// same quantity `Geo.RPlane.onOfDefects` divides by.
    pub dir_pivot: NameId,
    /// `Geo.RPlane.playfairUnique : ∀ P l m n, parPos l m → parPos l n →
    /// on P m → on P n → Geo.RLine.Equiv m n`.
    pub playfair_unique: NameId,
    /// `Geo.raffine : Geo.Affine` — the model itself.
    pub instance: NameId,
}

/// Pre-compute every name this module declares. `geo` is the `Geo` namespace
/// root interned by [`super::intern`].
pub(crate) fn intern(kernel: &mut Kernel, geo: NameId) -> RAffineNames {
    let plane = kernel.name_str(geo, "RPlane");
    RAffineNames {
        off_raw: kernel.name_str(plane, "offRaw"),
        off: kernel.name_str(plane, "off"),
        par_pos_raw: kernel.name_str(plane, "parPosRaw"),
        par_pos: kernel.name_str(plane, "parPos"),
        off_not_on: kernel.name_str(plane, "offNotOn"),
        par_pos_disjoint: kernel.name_str(plane, "parPosDisjoint"),
        pos_bound_mul: kernel.name_str(plane, "posBoundMul"),
        par_line: kernel.name_str(plane, "parLine"),
        par_line_on: kernel.name_str(plane, "parLineOn"),
        par_line_dir: kernel.name_str(plane, "parLineDir"),
        par_line_norm: kernel.name_str(plane, "parLineNorm"),
        playfair_exists: kernel.name_str(plane, "playfairExists"),
        dir_pivot: kernel.name_str(plane, "dirPivot"),
        playfair_unique: kernel.name_str(plane, "playfairUnique"),
        instance: kernel.name_str(geo, "raffine"),
    }
}

// ---------------------------------------------------------------------------
// Term shorthands. `rplane`'s own copies are private to that module and this
// one is its sibling, not its child, so these are re-stated rather than
// imported; ADR-1659 records the duplication and where it should go.
// ---------------------------------------------------------------------------

fn real_ty(d: &mut IntDev<'_>, cr: CRealPrelude) -> ExprId {
    d.kernel().const_(cr.creal, vec![])
}

fn point_ty(d: &mut IntDev<'_>, cp: CPointPrelude) -> ExprId {
    d.kernel().const_(cp.point, vec![])
}

fn line0_ty(d: &mut IntDev<'_>, r: RPlaneNames) -> ExprId {
    d.kernel().const_(r.rline0, vec![])
}

fn line_ty(d: &mut IntDev<'_>, r: RPlaneNames) -> ExprId {
    d.kernel().const_(r.rline, vec![])
}

fn prop_ty(d: &mut IntDev<'_>) -> ExprId {
    let l0 = d.kernel().level_zero();
    d.kernel().sort(l0)
}

fn px(d: &mut IntDev<'_>, cp: CPointPrelude, p: ExprId) -> ExprId {
    d.const_app(cp.x, &[p])
}

fn py(d: &mut IntDev<'_>, cp: CPointPrelude, p: ExprId) -> ExprId {
    d.const_app(cp.y, &[p])
}

fn la(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId) -> ExprId {
    d.const_app(r.rline0_a, &[l])
}

fn lb(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId) -> ExprId {
    d.const_app(r.rline0_b, &[l])
}

fn lc(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId) -> ExprId {
    d.const_app(r.rline0_c, &[l])
}

fn lmk(d: &mut IntDev<'_>, r: RPlaneNames, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    d.const_app(r.rline0_mk, &[a, b, c])
}

/// `CReal.Equiv a b`.
fn ceq(d: &mut IntDev<'_>, cr: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(cr.equiv, &[a, b])
}

/// `CReal.PosBound x k`.
fn pos_bound(d: &mut IntDev<'_>, cr: CRealPrelude, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(cr.pos_bound, &[x, k])
}

/// `a * s + b * t + c`, left-associated exactly as [`RnExpr`] renders it.
fn eval3(
    d: &mut IntDev<'_>,
    cr: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    s: ExprId,
    t: ExprId,
) -> ExprId {
    let m1 = rn_cmul(d, cr, a, s);
    let m2 = rn_cmul(d, cr, b, t);
    let sum = rn_cadd(d, cr, m1, m2);
    rn_cadd(d, cr, sum, c)
}

/// `u*v' − v*u'`, the defect shape every lemma here is stated over.
fn defect(
    d: &mut IntDev<'_>,
    cr: CRealPrelude,
    u: ExprId,
    v2: ExprId,
    v: ExprId,
    u2: ExprId,
) -> ExprId {
    let m1 = rn_cmul(d, cr, u, v2);
    let m2 = rn_cmul(d, cr, v, u2);
    let n2 = rn_cneg(d, cr, m2);
    rn_cadd(d, cr, m1, n2)
}

fn false_ty(d: &mut IntDev<'_>) -> ExprId {
    let name = d.int().logic.false_;
    d.kernel().const_(name, vec![])
}

fn and_ty(d: &mut IntDev<'_>, p: ExprId, q: ExprId) -> ExprId {
    let name = d.int().logic.and;
    d.const_app(name, &[p, q])
}

fn and_intro(d: &mut IntDev<'_>, p: ExprId, q: ExprId, hp: ExprId, hq: ExprId) -> ExprId {
    let name = d.int().logic.and_intro;
    d.const_app(name, &[p, q, hp, hq])
}

fn and_l(d: &mut IntDev<'_>, p: ExprId, q: ExprId, h: ExprId) -> ExprId {
    let name = d.int().logic.and_left;
    d.const_app(name, &[p, q, h])
}

fn and_r(d: &mut IntDev<'_>, p: ExprId, q: ExprId, h: ExprId) -> ExprId {
    let name = d.int().logic.and_right;
    d.const_app(name, &[p, q, h])
}

/// `Exists.{1} ty pred`.
fn exists_ty(d: &mut IntDev<'_>, ty: ExprId, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.int().logic.exists_;
    let c = d.kernel().const_(name, vec![one]);
    d.apply(c, &[ty, pred])
}

/// `Exists.intro.{1} ty pred w proof`.
fn exists_intro(d: &mut IntDev<'_>, ty: ExprId, pred: ExprId, w: ExprId, proof: ExprId) -> ExprId {
    let one = d.level_one();
    let name = d.int().logic.exists_intro;
    let c = d.kernel().const_(name, vec![one]);
    d.apply(c, &[ty, pred, w, proof])
}

/// `Subtype.val.{1} Geo.RLine0 Geo.RLine0.Nondeg l`.
fn lval(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let val = d.kernel().const_(sigma.subtype_val, vec![one]);
    let base = line0_ty(d, r);
    let nd = d.kernel().const_(r.nondeg, vec![]);
    d.apply(val, &[base, nd, l])
}

/// `Subtype.mk.{1} Geo.RLine0 Geo.RLine0.Nondeg l proof`.
fn lsub(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId, proof: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let mk = d.kernel().const_(sigma.subtype_mk, vec![one]);
    let base = line0_ty(d, r);
    let nd = d.kernel().const_(r.nondeg, vec![]);
    d.apply(mk, &[base, nd, l, proof])
}

/// `Subtype.property.{1} Geo.RLine0 Geo.RLine0.Nondeg l`.
fn lprop(d: &mut IntDev<'_>, r: RPlaneNames, l: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let prop = d.kernel().const_(sigma.subtype_property, vec![one]);
    let base = line0_ty(d, r);
    let nd = d.kernel().const_(r.nondeg, vec![]);
    d.apply(prop, &[base, nd, l])
}

/// A ring identity over ℝ, emitted by `rn_ring_proof` — never written by hand.
fn ring(d: &mut IntDev<'_>, cr: CRealPrelude, lhs: &RnExpr, rhs: &RnExpr) -> ExprId {
    rn_ring_proof(d, cr, lhs, rhs)
}

/// `RnExpr::Atom`, spelled short.
fn at(e: ExprId) -> RnExpr {
    RnExpr::Atom(e)
}

/// `a − b`, as `RnExpr`.
fn rsub(a: RnExpr, b: RnExpr) -> RnExpr {
    RnExpr::add(a, RnExpr::neg(b))
}

/// `a*s + b*t + c`, as `RnExpr` — the [`eval3`] shape.
fn rev3(a: RnExpr, b: RnExpr, c: RnExpr, s: RnExpr, t: RnExpr) -> RnExpr {
    RnExpr::add(RnExpr::add(RnExpr::mul(a, s), RnExpr::mul(b, t)), c)
}

/// Given `h : Equiv x CReal.zero`, a proof of `Equiv (mul f x) CReal.zero`.
fn mul_hyp_zero(d: &mut IntDev<'_>, cr: CRealPrelude, f: ExprId, x: ExprId, h: ExprId) -> ExprId {
    let zero = rn_czero(d, cr);
    let refl_f = rn_crefl(d, cr, f);
    let step = d.lemma(cr.mul_congr, &[f, f, x, zero, refl_f, h]);
    let f_zero = rn_cmul(d, cr, f, zero);
    let collapse = d.lemma(cr.mul_zero, &[f]);
    let start = rn_cmul(d, cr, f, x);
    rn_ctrans(d, cr, start, f_zero, zero, step, collapse)
}

/// Given `(fᵢ, xᵢ, hᵢ : Equiv xᵢ 0)`, a proof that the left-nested sum
/// `((f₁*x₁ + f₂*x₂) + …)` is `Equiv` to `CReal.zero`.
///
/// # Panics
///
/// Panics on an empty slice: every call site here has a fixed, nonempty
/// summand list, so an empty one is a coding error in this file.
fn sum_hyp_zero(
    d: &mut IntDev<'_>,
    cr: CRealPrelude,
    terms: &[(ExprId, ExprId, ExprId)],
) -> ExprId {
    assert!(!terms.is_empty(), "sum_hyp_zero needs at least one summand");
    let zero = rn_czero(d, cr);
    let (f0, x0, h0) = terms[0];
    let mut acc_term = rn_cmul(d, cr, f0, x0);
    let mut acc_proof = mul_hyp_zero(d, cr, f0, x0, h0);
    for &(f, x, h) in &terms[1..] {
        let next = rn_cmul(d, cr, f, x);
        let next_proof = mul_hyp_zero(d, cr, f, x, h);
        let summed = rn_cadd(d, cr, acc_term, next);
        let both = d.lemma(
            cr.add_congr,
            &[acc_term, zero, next, zero, acc_proof, next_proof],
        );
        let zz = rn_cadd(d, cr, zero, zero);
        let trim = d.lemma(cr.add_zero, &[zero]);
        acc_proof = rn_ctrans(d, cr, summed, zz, zero, both, trim);
        acc_term = summed;
    }
    acc_proof
}

/// The predicate `fun k => PosBound x k`, over `Nat`.
fn bound_pred(d: &mut IntDev<'_>, cr: CRealPrelude, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let pb = pos_bound(d, cr, x, k);
    d.lam_fv(k_fv, nat, pb)
}

/// `∃ k, PosBound x k`.
fn bounded(d: &mut IntDev<'_>, cr: CRealPrelude, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let pred = bound_pred(d, cr, x);
    exists_ty(d, nat, pred)
}

// ---------------------------------------------------------------------------
// The build.
// ---------------------------------------------------------------------------

/// Declare the ℝ affine layer and the `Geo.raffine` instance.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
///
/// # Panics
///
/// Panics when `rn_ring_proof` declines an identity this file claims is a ring
/// identity — see [`ring`].
pub(crate) fn declare_all(kernel: &mut Kernel, p: GeoPrelude) -> Result<(), KernelError> {
    let cp = p.cpoint;
    let cr = cp.creal;
    let r = p.rplane;
    let ra = p.raffine;
    let mut dev = IntDev::new(kernel, cr.rat.int);
    let d = &mut dev;

    declare_predicates(d, cp, cr, r, ra)?;
    declare_off_not_on(d, cp, cr, r, ra)?;
    declare_par_pos_disjoint(d, cp, cr, r, ra)?;
    declare_pos_bound_mul(d, cr, ra)?;
    declare_par_line(d, cp, cr, r, ra)?;
    declare_playfair_exists(d, cp, cr, r, ra)?;
    declare_dir_pivot(d, cr, r, ra)?;
    declare_playfair_unique(d, cp, cr, r, ra)?;
    declare_instance(d, p, r, ra)
}

/// `offRaw`, `off`, `parPosRaw`, `parPos`.
fn declare_predicates(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
    ra: RAffineNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line0 = line0_ty(d, r);
    let line = line_ty(d, r);
    let prop = prop_ty(d);

    // offRaw P l := ∃ k, PosBound (e_P * e_P) k.
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let a = la(d, r, l);
        let b = lb(d, r, l);
        let c = lc(d, r, l);
        let sx = px(d, cp, pt);
        let sy = py(d, cp, pt);
        let e = eval3(d, cr, a, b, c, sx, sy);
        let sq = rn_cmul(d, cr, e, e);
        let body = bounded(d, cr, sq);
        let value = {
            let inner = d.lam_fv(l_fv, line0, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(line0, prop);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: ra.off_raw,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // off P l := offRaw P (Subtype.val l).
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let raw = lval(d, r, l);
        let body = d.const_app(ra.off_raw, &[pt, raw]);
        let value = {
            let inner = d.lam_fv(l_fv, line, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(line, prop);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: ra.off,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // parPosRaw l m := Equiv (a l * b m − b l * a m) 0
    //                ∧ ∃ k, PosBound (dAC*dAC + dBC*dBC) k.
    {
        let l_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let m = d.kernel().fvar(m_fv);
        let a = la(d, r, l);
        let b = lb(d, r, l);
        let c = lc(d, r, l);
        let aa = la(d, r, m);
        let bb = lb(d, r, m);
        let cc = lc(d, r, m);
        let zero = rn_czero(d, cr);
        let dab = defect(d, cr, a, bb, b, aa);
        let dir = ceq(d, cr, dab, zero);
        let dac = defect(d, cr, a, cc, c, aa);
        let dbc = defect(d, cr, b, cc, c, bb);
        let s1 = rn_cmul(d, cr, dac, dac);
        let s2 = rn_cmul(d, cr, dbc, dbc);
        let sq = rn_cadd(d, cr, s1, s2);
        let distinct = bounded(d, cr, sq);
        let body = and_ty(d, dir, distinct);
        let value = {
            let inner = d.lam_fv(m_fv, line0, body);
            d.lam_fv(l_fv, line0, inner)
        };
        let ty = {
            let inner = d.arrow(line0, prop);
            d.arrow(line0, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: ra.par_pos_raw,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // parPos l m := parPosRaw (val l) (val m).
    {
        let l_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let m = d.kernel().fvar(m_fv);
        let lr = lval(d, r, l);
        let mr = lval(d, r, m);
        let body = d.const_app(ra.par_pos_raw, &[lr, mr]);
        let value = {
            let inner = d.lam_fv(m_fv, line, body);
            d.lam_fv(l_fv, line, inner)
        };
        let ty = {
            let inner = d.arrow(line, prop);
            d.arrow(line, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: ra.par_pos,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    Ok(())
}

/// `offNotOn : ∀ P l, off P l → on P l → False` — squaring the incidence
/// expression makes the `PosBound` witness contradict it.
fn declare_off_not_on(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
    ra: RAffineNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line = line_ty(d, r);
    let nat = d.nat_ty();

    let p_fv = d.fresh_fvar();
    let l_fv = d.fresh_fvar();
    let h_fv = d.fresh_fvar();
    let ho_fv = d.fresh_fvar();
    let k_fv = d.fresh_fvar();
    let hk_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(p_fv);
    let l = d.kernel().fvar(l_fv);
    let h = d.kernel().fvar(h_fv);
    let ho = d.kernel().fvar(ho_fv);
    let k = d.kernel().fvar(k_fv);
    let hk = d.kernel().fvar(hk_fv);

    let raw = lval(d, r, l);
    let a = la(d, r, raw);
    let b = lb(d, r, raw);
    let c = lc(d, r, raw);
    let sx = px(d, cp, pt);
    let sy = py(d, cp, pt);
    let e = eval3(d, cr, a, b, c, sx, sy);
    let sq = rn_cmul(d, cr, e, e);
    let f = false_ty(d);

    let sq_zero = mul_hyp_zero(d, cr, e, e, ho);
    let clash = d.lemma(r.not_zero_of_pos_bound, &[sq, k, hk, sq_zero]);
    let pred = bound_pred(d, cr, sq);
    let minor = {
        let hk_ty = pos_bound(d, cr, sq, k);
        let inner = d.lam_fv(hk_fv, hk_ty, clash);
        d.lam_fv(k_fv, nat, inner)
    };
    let proof = exists_elim(d, pred, f, h, minor);

    let h_ty = d.const_app(ra.off, &[pt, l]);
    let ho_ty = d.const_app(r.on, &[pt, l]);
    let ty = {
        let t = d.arrow(ho_ty, f);
        let t = d.arrow(h_ty, t);
        let t = d.pi_fv(l_fv, line, t);
        d.pi_fv(p_fv, point, t)
    };
    let value = {
        let t = d.lam_fv(ho_fv, ho_ty, proof);
        let t = d.lam_fv(h_fv, h_ty, t);
        let t = d.lam_fv(l_fv, line, t);
        d.lam_fv(p_fv, point, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: ra.off_not_on,
        uparams: vec![],
        ty,
        value,
    })
}

/// `parPosDisjoint : ∀ l m P, parPos l m → on P l → on P m → False`.
fn declare_par_pos_disjoint(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
    ra: RAffineNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line = line_ty(d, r);
    let nat = d.nat_ty();
    let zero = rn_czero(d, cr);

    let l_fv = d.fresh_fvar();
    let m_fv = d.fresh_fvar();
    let p_fv = d.fresh_fvar();
    let hp_fv = d.fresh_fvar();
    let h1_fv = d.fresh_fvar();
    let h2_fv = d.fresh_fvar();
    let k_fv = d.fresh_fvar();
    let hk_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let m = d.kernel().fvar(m_fv);
    let pt = d.kernel().fvar(p_fv);
    let hp = d.kernel().fvar(hp_fv);
    let h1 = d.kernel().fvar(h1_fv);
    let h2 = d.kernel().fvar(h2_fv);
    let k = d.kernel().fvar(k_fv);
    let hk = d.kernel().fvar(hk_fv);

    let lr = lval(d, r, l);
    let mr = lval(d, r, m);
    let a = la(d, r, lr);
    let b = lb(d, r, lr);
    let c = lc(d, r, lr);
    let aa = la(d, r, mr);
    let bb = lb(d, r, mr);
    let cc = lc(d, r, mr);
    let sx = px(d, cp, pt);
    let sy = py(d, cp, pt);

    let dab = defect(d, cr, a, bb, b, aa);
    let dir_ty = ceq(d, cr, dab, zero);
    let dac = defect(d, cr, a, cc, c, aa);
    let dbc = defect(d, cr, b, cc, c, bb);
    let s1 = rn_cmul(d, cr, dac, dac);
    let s2 = rn_cmul(d, cr, dbc, dbc);
    let sq = rn_cadd(d, cr, s1, s2);
    let distinct_ty = bounded(d, cr, sq);

    let hdir = and_l(d, dir_ty, distinct_ty, hp);
    let hdist = and_r(d, dir_ty, distinct_ty, hp);
    let hdac = d.lemma(r.defect_ac, &[a, b, c, aa, bb, cc, sx, sy, h1, h2, hdir]);
    let hdbc = d.lemma(r.defect_bc, &[a, b, c, aa, bb, cc, sx, sy, h1, h2, hdir]);
    let hsq = sum_hyp_zero(d, cr, &[(dac, dac, hdac), (dbc, dbc, hdbc)]);

    let f = false_ty(d);
    let clash = d.lemma(r.not_zero_of_pos_bound, &[sq, k, hk, hsq]);
    let pred = bound_pred(d, cr, sq);
    let minor = {
        let hk_ty = pos_bound(d, cr, sq, k);
        let inner = d.lam_fv(hk_fv, hk_ty, clash);
        d.lam_fv(k_fv, nat, inner)
    };
    let proof = exists_elim(d, pred, f, hdist, minor);

    let hp_ty = d.const_app(ra.par_pos, &[l, m]);
    let h1_ty = d.const_app(r.on, &[pt, l]);
    let h2_ty = d.const_app(r.on, &[pt, m]);
    let ty = {
        let t = d.arrow(h2_ty, f);
        let t = d.arrow(h1_ty, t);
        let t = d.arrow(hp_ty, t);
        let t = d.pi_fv(p_fv, point, t);
        let t = d.pi_fv(m_fv, line, t);
        d.pi_fv(l_fv, line, t)
    };
    let value = {
        let t = d.lam_fv(h2_fv, h2_ty, proof);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(hp_fv, hp_ty, t);
        let t = d.lam_fv(p_fv, point, t);
        let t = d.lam_fv(m_fv, line, t);
        d.lam_fv(l_fv, line, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: ra.par_pos_disjoint,
        uparams: vec![],
        ty,
        value,
    })
}

/// `posBoundMul : ∀ x y j k, PosBound x j → PosBound y k →
/// ∃ n, PosBound (mul x y) n`.
fn declare_pos_bound_mul(
    d: &mut IntDev<'_>,
    cr: CRealPrelude,
    ra: RAffineNames,
) -> Result<(), KernelError> {
    let carrier = real_ty(d, cr);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let y_fv = d.fresh_fvar();
    let j_fv = d.fresh_fvar();
    let k_fv = d.fresh_fvar();
    let hj_fv = d.fresh_fvar();
    let hk_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y = d.kernel().fvar(y_fv);
    let j = d.kernel().fvar(j_fv);
    let k = d.kernel().fvar(k_fv);
    let hj = d.kernel().fvar(hj_fv);
    let hk = d.kernel().fvar(hk_fv);

    let xy = rn_cmul(d, cr, x, y);
    let px_pos = d.lemma(cr.pos_of_pos_bound, &[x, j, hj]);
    let py_pos = d.lemma(cr.pos_of_pos_bound, &[y, k, hk]);
    let prod_pos = d.lemma(cr.mul_pos, &[x, y, px_pos, py_pos]);
    let proof = d.lemma(cr.pos_bound_of_lt, &[xy, prod_pos]);

    let hj_ty = pos_bound(d, cr, x, j);
    let hk_ty = pos_bound(d, cr, y, k);
    let concl = bounded(d, cr, xy);
    let ty = {
        let t = d.arrow(hk_ty, concl);
        let t = d.arrow(hj_ty, t);
        let t = d.pi_fv(k_fv, nat, t);
        let t = d.pi_fv(j_fv, nat, t);
        let t = d.pi_fv(y_fv, carrier, t);
        d.pi_fv(x_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(hk_fv, hk_ty, proof);
        let t = d.lam_fv(hj_fv, hj_ty, t);
        let t = d.lam_fv(k_fv, nat, t);
        let t = d.lam_fv(j_fv, nat, t);
        let t = d.lam_fv(y_fv, carrier, t);
        d.lam_fv(x_fv, carrier, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: ra.pos_bound_mul,
        uparams: vec![],
        ty,
        value,
    })
}

/// `parLine`, `parLineOn`, `parLineDir`, `parLineNorm`.
fn declare_par_line(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
    ra: RAffineNames,
) -> Result<(), KernelError> {
    let carrier = real_ty(d, cr);
    let point = point_ty(d, cp);
    let line0 = line0_ty(d, r);
    let zero = rn_czero(d, cr);

    // parLine P l := Geo.RLine0.mk (a l) (b l) (−(a l * x P + b l * y P)).
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let a = la(d, r, l);
        let b = lb(d, r, l);
        let sx = px(d, cp, pt);
        let sy = py(d, cp, pt);
        let m1 = rn_cmul(d, cr, a, sx);
        let m2 = rn_cmul(d, cr, b, sy);
        let sum = rn_cadd(d, cr, m1, m2);
        let cc = rn_cneg(d, cr, sum);
        let body = lmk(d, r, a, b, cc);
        let value = {
            let inner = d.lam_fv(l_fv, line0, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(line0, line0);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: ra.par_line,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // parLineOn : ∀ P l, onRaw P (parLine P l).
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let a = la(d, r, l);
        let b = lb(d, r, l);
        let sx = px(d, cp, pt);
        let sy = py(d, cp, pt);
        let lhs_rn = rev3(
            at(a),
            at(b),
            RnExpr::neg(RnExpr::add(
                RnExpr::mul(at(a), at(sx)),
                RnExpr::mul(at(b), at(sy)),
            )),
            at(sx),
            at(sy),
        );
        let proof = ring(d, cr, &lhs_rn, &RnExpr::Zero);
        let m = d.const_app(ra.par_line, &[pt, l]);
        let concl = d.const_app(r.on_raw, &[pt, m]);
        let ty = {
            let t = d.pi_fv(l_fv, line0, concl);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(l_fv, line0, proof);
            d.lam_fv(p_fv, point, t)
        };
        let _ = zero;
        d.kernel().add_declaration(Declaration::Theorem {
            name: ra.par_line_on,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // parLineDir : ∀ P l, Equiv (a l * b (parLine P l) −
    //                            b l * a (parLine P l)) 0.
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let a = la(d, r, l);
        let b = lb(d, r, l);
        let lhs_rn = rsub(RnExpr::mul(at(a), at(b)), RnExpr::mul(at(b), at(a)));
        let proof = ring(d, cr, &lhs_rn, &RnExpr::Zero);
        let m = d.const_app(ra.par_line, &[pt, l]);
        let ma = la(d, r, m);
        let mb = lb(d, r, m);
        let dab = defect(d, cr, a, mb, b, ma);
        let concl = ceq(d, cr, dab, zero);
        let ty = {
            let t = d.pi_fv(l_fv, line0, concl);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(l_fv, line0, proof);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: ra.par_line_dir,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // parLineNorm : ∀ a b c x y,
    //   Equiv (dAC*dAC + dBC*dBC) ((a*a + b*b) * (e*e)), where
    //   dAC := a*(−(a*x + b*y)) − c*a, dBC := b*(−(a*x + b*y)) − c*b.
    {
        let fvs: Vec<u64> = (0..5).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
        let (a, b, c, sx, sy) = (vars[0], vars[1], vars[2], vars[3], vars[4]);
        let m1 = rn_cmul(d, cr, a, sx);
        let m2 = rn_cmul(d, cr, b, sy);
        let sum = rn_cadd(d, cr, m1, m2);
        let cc = rn_cneg(d, cr, sum);
        let dac = defect(d, cr, a, cc, c, a);
        let dbc = defect(d, cr, b, cc, c, b);
        let s1 = rn_cmul(d, cr, dac, dac);
        let s2 = rn_cmul(d, cr, dbc, dbc);
        let lhs = rn_cadd(d, cr, s1, s2);
        let norm = {
            let p1 = rn_cmul(d, cr, a, a);
            let p2 = rn_cmul(d, cr, b, b);
            rn_cadd(d, cr, p1, p2)
        };
        let e = eval3(d, cr, a, b, c, sx, sy);
        let ee = rn_cmul(d, cr, e, e);
        let rhs = rn_cmul(d, cr, norm, ee);

        let cc_rn = RnExpr::neg(RnExpr::add(
            RnExpr::mul(at(a), at(sx)),
            RnExpr::mul(at(b), at(sy)),
        ));
        let dac_rn = rsub(RnExpr::mul(at(a), cc_rn.clone()), RnExpr::mul(at(c), at(a)));
        let dbc_rn = rsub(RnExpr::mul(at(b), cc_rn), RnExpr::mul(at(c), at(b)));
        let lhs_rn = RnExpr::add(
            RnExpr::mul(dac_rn.clone(), dac_rn),
            RnExpr::mul(dbc_rn.clone(), dbc_rn),
        );
        let e_rn = rev3(at(a), at(b), at(c), at(sx), at(sy));
        let rhs_rn = RnExpr::mul(
            RnExpr::add(RnExpr::mul(at(a), at(a)), RnExpr::mul(at(b), at(b))),
            RnExpr::mul(e_rn.clone(), e_rn),
        );
        let proof = ring(d, cr, &lhs_rn, &rhs_rn);
        let concl = ceq(d, cr, lhs, rhs);
        let ty = {
            let mut t = concl;
            for &fv in fvs.iter().rev() {
                t = d.pi_fv(fv, carrier, t);
            }
            t
        };
        let value = {
            let mut t = proof;
            for &fv in fvs.iter().rev() {
                t = d.lam_fv(fv, carrier, t);
            }
            t
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: ra.par_line_norm,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `playfairExists : ∀ P l, off P l → ∃ m, on P m ∧ parPos l m`.
fn declare_playfair_exists(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
    ra: RAffineNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line = line_ty(d, r);
    let nat = d.nat_ty();

    let p_fv = d.fresh_fvar();
    let l_fv = d.fresh_fvar();
    let h_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(p_fv);
    let l = d.kernel().fvar(l_fv);
    let h = d.kernel().fvar(h_fv);

    let lr = lval(d, r, l);
    let a = la(d, r, lr);
    let b = lb(d, r, lr);
    let c = lc(d, r, lr);
    let sx = px(d, cp, pt);
    let sy = py(d, cp, pt);

    let raw = d.const_app(ra.par_line, &[pt, lr]);
    let nd = lprop(d, r, l);
    let m = lsub(d, r, raw, nd);

    // The three quantities the witness is assembled from.
    let norm = {
        let p1 = rn_cmul(d, cr, a, a);
        let p2 = rn_cmul(d, cr, b, b);
        rn_cadd(d, cr, p1, p2)
    };
    let e = eval3(d, cr, a, b, c, sx, sy);
    let ee = rn_cmul(d, cr, e, e);
    let prod = rn_cmul(d, cr, norm, ee);
    let ma = la(d, r, raw);
    let mb = lb(d, r, raw);
    let mc = lc(d, r, raw);
    let dac = defect(d, cr, a, mc, c, ma);
    let dbc = defect(d, cr, b, mc, c, mb);
    let s1 = rn_cmul(d, cr, dac, dac);
    let s2 = rn_cmul(d, cr, dbc, dbc);
    let dsq = rn_cadd(d, cr, s1, s2);

    let target_dist = bounded(d, cr, dsq);
    let pred_dist = bound_pred(d, cr, dsq);
    let pred_norm = bound_pred(d, cr, norm);
    let pred_off = bound_pred(d, cr, ee);
    let pred_prod = bound_pred(d, cr, prod);

    // `∃ n, PosBound (dAC² + dBC²) n`, from `Nondeg l` and `off P l` through
    // `posBoundMul` and one ring identity.
    let hdist = {
        let j_fv = d.fresh_fvar();
        let hj_fv = d.fresh_fvar();
        let k_fv = d.fresh_fvar();
        let hk_fv = d.fresh_fvar();
        let n_fv = d.fresh_fvar();
        let hn_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hj = d.kernel().fvar(hj_fv);
        let k = d.kernel().fvar(k_fv);
        let hk = d.kernel().fvar(hk_fv);
        let n = d.kernel().fvar(n_fv);
        let hn = d.kernel().fvar(hn_fv);

        let norm_eq = d.lemma(ra.par_line_norm, &[a, b, c, sx, sy]);
        let back = rn_csymm(d, cr, dsq, prod, norm_eq);
        let carried = d.lemma(r.pos_bound_congr, &[prod, dsq, n, back, hn]);
        let innermost = exists_intro(d, nat, pred_dist, n, carried);
        let minor_n = {
            let hn_ty = pos_bound(d, cr, prod, n);
            let inner = d.lam_fv(hn_fv, hn_ty, innermost);
            d.lam_fv(n_fv, nat, inner)
        };
        let product = d.lemma(ra.pos_bound_mul, &[norm, ee, j, k, hj, hk]);
        let after_prod = exists_elim(d, pred_prod, target_dist, product, minor_n);
        let minor_k = {
            let hk_ty = pos_bound(d, cr, ee, k);
            let inner = d.lam_fv(hk_fv, hk_ty, after_prod);
            d.lam_fv(k_fv, nat, inner)
        };
        let off_h = h;
        let after_off = exists_elim(d, pred_off, target_dist, off_h, minor_k);
        let minor_j = {
            let hj_ty = pos_bound(d, cr, norm, j);
            let inner = d.lam_fv(hj_fv, hj_ty, after_off);
            d.lam_fv(j_fv, nat, inner)
        };
        exists_elim(d, pred_norm, target_dist, nd, minor_j)
    };

    let pred = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let on = d.const_app(r.on, &[pt, w]);
        let par = d.const_app(ra.par_pos, &[l, w]);
        let body = and_ty(d, on, par);
        d.lam_fv(w_fv, line, body)
    };

    let on_ty = d.const_app(r.on, &[pt, m]);
    let par_ty = d.const_app(ra.par_pos, &[l, m]);
    let on_proof = d.lemma(ra.par_line_on, &[pt, lr]);
    let par_proof = {
        let zero = rn_czero(d, cr);
        let dab = defect(d, cr, a, mb, b, ma);
        let dir_ty = ceq(d, cr, dab, zero);
        let dir_proof = d.lemma(ra.par_line_dir, &[pt, lr]);
        and_intro(d, dir_ty, target_dist, dir_proof, hdist)
    };
    let body = and_intro(d, on_ty, par_ty, on_proof, par_proof);
    let proof = exists_intro(d, line, pred, m, body);

    let h_ty = d.const_app(ra.off, &[pt, l]);
    let concl = exists_ty(d, line, pred);
    let ty = {
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(l_fv, line, t);
        d.pi_fv(p_fv, point, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, h_ty, proof);
        let t = d.lam_fv(l_fv, line, t);
        d.lam_fv(p_fv, point, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: ra.playfair_exists,
        uparams: vec![],
        ty,
        value,
    })
}

/// `dirPivot : ∀ a b A B A' B' j, PosBound (a*a + b*b) j →
/// Equiv (a*B − b*A) 0 → Equiv (a*B' − b*A') 0 → Equiv (A*B' − B*A') 0`.
fn declare_dir_pivot(
    d: &mut IntDev<'_>,
    cr: CRealPrelude,
    r: RPlaneNames,
    ra: RAffineNames,
) -> Result<(), KernelError> {
    let carrier = real_ty(d, cr);
    let nat = d.nat_ty();
    let zero = rn_czero(d, cr);

    let fvs: Vec<u64> = (0..6).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let (a, b, aa, bb, aa2, bb2) = (vars[0], vars[1], vars[2], vars[3], vars[4], vars[5]);
    let j_fv = d.fresh_fvar();
    let hj_fv = d.fresh_fvar();
    let h1_fv = d.fresh_fvar();
    let h2_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hj = d.kernel().fvar(hj_fv);
    let h1 = d.kernel().fvar(h1_fv);
    let h2 = d.kernel().fvar(h2_fv);

    let dlm = defect(d, cr, a, bb, b, aa);
    let dln = defect(d, cr, a, bb2, b, aa2);
    let dmn = defect(d, cr, aa, bb2, bb, aa2);
    let norm = {
        let p1 = rn_cmul(d, cr, a, a);
        let p2 = rn_cmul(d, cr, b, b);
        rn_cadd(d, cr, p1, p2)
    };
    let f1 = {
        let p1 = rn_cmul(d, cr, a, aa);
        let p2 = rn_cmul(d, cr, b, bb);
        rn_cadd(d, cr, p1, p2)
    };
    let f2 = {
        let p1 = rn_cmul(d, cr, a, aa2);
        let p2 = rn_cmul(d, cr, b, bb2);
        let s = rn_cadd(d, cr, p1, p2);
        rn_cneg(d, cr, s)
    };
    let product = rn_cmul(d, cr, norm, dmn);

    let dlm_rn = rsub(RnExpr::mul(at(a), at(bb)), RnExpr::mul(at(b), at(aa)));
    let dln_rn = rsub(RnExpr::mul(at(a), at(bb2)), RnExpr::mul(at(b), at(aa2)));
    let dmn_rn = rsub(RnExpr::mul(at(aa), at(bb2)), RnExpr::mul(at(bb), at(aa2)));
    let lhs_rn = RnExpr::mul(
        RnExpr::add(RnExpr::mul(at(a), at(a)), RnExpr::mul(at(b), at(b))),
        dmn_rn,
    );
    let rhs_rn = RnExpr::add(
        RnExpr::mul(
            RnExpr::add(RnExpr::mul(at(a), at(aa)), RnExpr::mul(at(b), at(bb))),
            dln_rn,
        ),
        RnExpr::mul(
            RnExpr::neg(RnExpr::add(
                RnExpr::mul(at(a), at(aa2)),
                RnExpr::mul(at(b), at(bb2)),
            )),
            dlm_rn,
        ),
    );
    let identity = ring(d, cr, &lhs_rn, &rhs_rn);
    let vanish = sum_hyp_zero(d, cr, &[(f1, dln, h2), (f2, dlm, h1)]);
    let rhs = {
        let t1 = rn_cmul(d, cr, f1, dln);
        let t2 = rn_cmul(d, cr, f2, dlm);
        rn_cadd(d, cr, t1, t2)
    };
    let product_zero = rn_ctrans(d, cr, product, rhs, zero, identity, vanish);
    // The one division: `Nondeg l`'s own modulus cancels `a² + b²`, through the
    // same lemma `Geo.RPlane.joinUnique` and `onOfDefects` already use.
    let proof = d.lemma(r.cancel_pos_bound, &[norm, dmn, j, hj, product_zero]);

    let hj_ty = pos_bound(d, cr, norm, j);
    let h1_ty = ceq(d, cr, dlm, zero);
    let h2_ty = ceq(d, cr, dln, zero);
    let concl = ceq(d, cr, dmn, zero);
    let ty = {
        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h1_ty, t);
        let t = d.arrow(hj_ty, t);
        let mut t = d.pi_fv(j_fv, nat, t);
        for &fv in fvs.iter().rev() {
            t = d.pi_fv(fv, carrier, t);
        }
        t
    };
    let value = {
        let t = d.lam_fv(h2_fv, h2_ty, proof);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(hj_fv, hj_ty, t);
        let mut t = d.lam_fv(j_fv, nat, t);
        for &fv in fvs.iter().rev() {
            t = d.lam_fv(fv, carrier, t);
        }
        t
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: ra.dir_pivot,
        uparams: vec![],
        ty,
        value,
    })
}

/// `playfairUnique : ∀ P l m n, parPos l m → parPos l n → on P m → on P n →
/// Geo.RLine.Equiv m n`.
fn declare_playfair_unique(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    cr: CRealPrelude,
    r: RPlaneNames,
    ra: RAffineNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, cp);
    let line = line_ty(d, r);
    let nat = d.nat_ty();
    let zero = rn_czero(d, cr);

    let p_fv = d.fresh_fvar();
    let l_fv = d.fresh_fvar();
    let m_fv = d.fresh_fvar();
    let n_fv = d.fresh_fvar();
    let h1_fv = d.fresh_fvar();
    let h2_fv = d.fresh_fvar();
    let h3_fv = d.fresh_fvar();
    let h4_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(p_fv);
    let l = d.kernel().fvar(l_fv);
    let m = d.kernel().fvar(m_fv);
    let n = d.kernel().fvar(n_fv);
    let h1 = d.kernel().fvar(h1_fv);
    let h2 = d.kernel().fvar(h2_fv);
    let h3 = d.kernel().fvar(h3_fv);
    let h4 = d.kernel().fvar(h4_fv);

    let lr = lval(d, r, l);
    let mr = lval(d, r, m);
    let nr = lval(d, r, n);
    let a = la(d, r, lr);
    let b = lb(d, r, lr);
    let c = lc(d, r, lr);
    let aa = la(d, r, mr);
    let bb = lb(d, r, mr);
    let cc = lc(d, r, mr);
    let aa2 = la(d, r, nr);
    let bb2 = lb(d, r, nr);
    let cc2 = lc(d, r, nr);
    let sx = px(d, cp, pt);
    let sy = py(d, cp, pt);
    let _ = c;

    // The left conjunct of each `parPos` hypothesis.
    let mut directions: Vec<ExprId> = Vec::with_capacity(2);
    for (u, v, w, h) in [(aa, bb, cc, h1), (aa2, bb2, cc2, h2)] {
        let dab = defect(d, cr, a, v, b, u);
        let dir_ty = ceq(d, cr, dab, zero);
        let dac = defect(d, cr, a, w, c, u);
        let dbc = defect(d, cr, b, w, c, v);
        let s1 = rn_cmul(d, cr, dac, dac);
        let s2 = rn_cmul(d, cr, dbc, dbc);
        let sq = rn_cadd(d, cr, s1, s2);
        let distinct_ty = bounded(d, cr, sq);
        directions.push(and_l(d, dir_ty, distinct_ty, h));
    }
    let hdir_m = directions[0];
    let hdir_n = directions[1];

    let norm_l = {
        let p1 = rn_cmul(d, cr, a, a);
        let p2 = rn_cmul(d, cr, b, b);
        rn_cadd(d, cr, p1, p2)
    };
    let norm_m = {
        let p1 = rn_cmul(d, cr, aa, aa);
        let p2 = rn_cmul(d, cr, bb, bb);
        rn_cadd(d, cr, p1, p2)
    };
    let norm_n = {
        let p1 = rn_cmul(d, cr, aa2, aa2);
        let p2 = rn_cmul(d, cr, bb2, bb2);
        rn_cadd(d, cr, p1, p2)
    };

    let j_fv = d.fresh_fvar();
    let hj_fv = d.fresh_fvar();
    let km_fv = d.fresh_fvar();
    let hkm_fv = d.fresh_fvar();
    let kn_fv = d.fresh_fvar();
    let hkn_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hj = d.kernel().fvar(hj_fv);
    let km = d.kernel().fvar(km_fv);
    let hkm = d.kernel().fvar(hkm_fv);
    let kn = d.kernel().fvar(kn_fv);
    let hkn = d.kernel().fvar(hkn_fv);

    let h_mn = d.lemma(
        ra.dir_pivot,
        &[a, b, aa, bb, aa2, bb2, j, hj, hdir_m, hdir_n],
    );
    let h_mac = d.lemma(
        r.defect_ac,
        &[aa, bb, cc, aa2, bb2, cc2, sx, sy, h3, h4, h_mn],
    );
    let h_mbc = d.lemma(
        r.defect_bc,
        &[aa, bb, cc, aa2, bb2, cc2, sx, sy, h3, h4, h_mn],
    );
    let h_nm = d.lemma(r.defect_swap, &[aa, bb, aa2, bb2, h_mn]);
    let h_nac = d.lemma(r.defect_swap, &[aa, cc, aa2, cc2, h_mac]);
    let h_nbc = d.lemma(r.defect_swap, &[bb, cc, bb2, cc2, h_mbc]);

    let target = d.const_app(r.line_equiv, &[m, n]);
    let body = {
        let x_fv = d.fresh_fvar();
        let xt = d.kernel().fvar(x_fv);
        let xx = px(d, cp, xt);
        let xy = py(d, cp, xt);
        let oxm = d.const_app(r.on, &[xt, m]);
        let oxn = d.const_app(r.on, &[xt, n]);
        let fwd_ty = d.arrow(oxm, oxn);
        let bwd_ty = d.arrow(oxn, oxm);
        let fwd = {
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let step = d.lemma(
                r.on_of_defects,
                &[
                    aa, bb, cc, aa2, bb2, cc2, xx, xy, km, hkm, h_mn, h_mac, h_mbc, hx,
                ],
            );
            d.lam_fv(hx_fv, oxm, step)
        };
        let bwd = {
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let step = d.lemma(
                r.on_of_defects,
                &[
                    aa2, bb2, cc2, aa, bb, cc, xx, xy, kn, hkn, h_nm, h_nac, h_nbc, hx,
                ],
            );
            d.lam_fv(hx_fv, oxn, step)
        };
        let pair = and_intro(d, fwd_ty, bwd_ty, fwd, bwd);
        d.lam_fv(x_fv, point, pair)
    };

    let pred_n = bound_pred(d, cr, norm_n);
    let pred_m = bound_pred(d, cr, norm_m);
    let pred_l = bound_pred(d, cr, norm_l);

    let minor_n = {
        let hkn_ty = pos_bound(d, cr, norm_n, kn);
        let inner = d.lam_fv(hkn_fv, hkn_ty, body);
        d.lam_fv(kn_fv, nat, inner)
    };
    let prop_n = lprop(d, r, n);
    let after_n = exists_elim(d, pred_n, target, prop_n, minor_n);

    let minor_m = {
        let hkm_ty = pos_bound(d, cr, norm_m, km);
        let inner = d.lam_fv(hkm_fv, hkm_ty, after_n);
        d.lam_fv(km_fv, nat, inner)
    };
    let prop_m = lprop(d, r, m);
    let after_m = exists_elim(d, pred_m, target, prop_m, minor_m);

    let minor_l = {
        let hj_ty = pos_bound(d, cr, norm_l, j);
        let inner = d.lam_fv(hj_fv, hj_ty, after_m);
        d.lam_fv(j_fv, nat, inner)
    };
    let prop_l = lprop(d, r, l);
    let proof = exists_elim(d, pred_l, target, prop_l, minor_l);

    let h1_ty = d.const_app(ra.par_pos, &[l, m]);
    let h2_ty = d.const_app(ra.par_pos, &[l, n]);
    let h3_ty = d.const_app(r.on, &[pt, m]);
    let h4_ty = d.const_app(r.on, &[pt, n]);
    let ty = {
        let t = d.arrow(h4_ty, target);
        let t = d.arrow(h3_ty, t);
        let t = d.arrow(h2_ty, t);
        let t = d.arrow(h1_ty, t);
        let t = d.pi_fv(n_fv, line, t);
        let t = d.pi_fv(m_fv, line, t);
        let t = d.pi_fv(l_fv, line, t);
        d.pi_fv(p_fv, point, t)
    };
    let value = {
        let t = d.lam_fv(h4_fv, h4_ty, proof);
        let t = d.lam_fv(h3_fv, h3_ty, t);
        let t = d.lam_fv(h2_fv, h2_ty, t);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(n_fv, line, t);
        let t = d.lam_fv(m_fv, line, t);
        let t = d.lam_fv(l_fv, line, t);
        d.lam_fv(p_fv, point, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: ra.playfair_unique,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Geo.raffine : Geo.Affine`.
fn declare_instance(
    d: &mut IntDev<'_>,
    p: GeoPrelude,
    r: RPlaneNames,
    ra: RAffineNames,
) -> Result<(), KernelError> {
    let inc = d.kernel().const_(r.instance, vec![]);
    let par_pos = d.kernel().const_(ra.par_pos, vec![]);
    let off = d.kernel().const_(ra.off, vec![]);
    let off_not_on = d.kernel().const_(ra.off_not_on, vec![]);
    let disjoint = d.kernel().const_(ra.par_pos_disjoint, vec![]);
    let exists = d.kernel().const_(ra.playfair_exists, vec![]);
    let unique = d.kernel().const_(ra.playfair_unique, vec![]);

    let args = [inc, par_pos, off, off_not_on, disjoint, exists, unique];
    assert_eq!(
        args.len(),
        super::affine::AFFINE_FIELD_COUNT,
        "the instance's argument list is out of step with the record"
    );
    let value = mk_instance(d.kernel(), &p.affine.record, &args);
    let ty = d.kernel().const_(p.affine.record.ind, vec![]);
    d.kernel().add_declaration(Declaration::Definition {
        name: ra.instance,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}
