//! `Geo.qaffine` — **the rational plane satisfies Playfair's parallel
//! axiom**, and therefore [`Geo.Affine`](super::affine) has a model.
//!
//! Roadmap W3-8, third slice; ADR-1659. This file adds nothing to
//! [`qplane`](super::qplane): every line, point and incidence is the one that
//! module already declared, and the four algebraic facts below are the only
//! new mathematics.
//!
//! # The two new predicates
//!
//! ```text
//! Geo.QPlane.offRaw P l    : Prop := Geo.QPlane.onRaw P l → False
//! Geo.QPlane.off    P l    : Prop := offRaw P (Subtype.val … l)
//! Geo.QPlane.parPosRaw l m : Prop :=
//!     (a l * b m = b l * a m)                                -- same direction
//!   ∧ (((a l * c m = c l * a m) ∧ (b l * c m = c l * b m)) → False)   -- distinct
//! Geo.QPlane.parPos l m    : Prop := parPosRaw (val l) (val m)
//! ```
//!
//! **Both conjuncts of `parPosRaw` are about the same three proportionalities
//! `Geo.QPlane.onOfProp` already consumes.** Two coefficient triples describe
//! the same line exactly when all three of `a*B = b*A`, `a*C = c*A` and
//! `b*C = c*B` hold; `parPos` says the first holds and the other two do not
//! both hold. So "parallel" here is *literally* "proportional in direction,
//! not proportional overall", which is why `onOfProp` — the ℚ pivot, written
//! for `joinUnique` — discharges both halves of Playfair with no new division.
//!
//! Over ℚ the distinctness half is a NEGATION and that is fine: `ℚ`'s equality
//! is decidable (`Geo.Rat.eqOrNe`) and `Rat.mul_eq_zero` turns a negated
//! product into a negated factor. The ℝ model cannot do that and states the
//! same conjunct as a `PosBound` witness; see [`raffine`](super::raffine).
//! That the two models differ here, and that ONE record serves both, is the
//! same measurement `apart` already made one layer down (ADR-1635, ADR-1652).
//!
//! # Where the work is
//!
//! | obligation | route |
//! | --- | --- |
//! | `parPosDisjoint` | `Geo.QPlane.defectAC`/`defectBC`: a common point plus `a*B = b*A` forces the other two proportionalities, so the distinctness conjunct is contradicted |
//! | `playfairExists` | the explicit parallel `(a, b, −(a·x P + b·y P))`, whose non-degeneracy IS `l`'s (same `a`, `b`) and whose two remaining defects are `−a·e_P` and `−b·e_P`; `Rat.mul_eq_zero` and `off P l` then force `a = 0` and `b = 0`, which `Nondeg l` refutes |
//! | `playfairUnique` | `Geo.QPlane.dirPivot` — `a*(A*B' − B*A') = A*(a*B' − b*A') − A'*(a*B − b*A)` and its `b` mirror, so `Geo.QLine0.nondeg_or` and `Rat.mul_eq_zero` give `A*B' = B*A'`; `defectAC`/`defectBC` at the shared point give the other two, and `onOfProp` turns the three into extensional line equality in BOTH directions (`Geo.QPlane.propSwap` supplies the mirrored triple) |
//!
//! Every polynomial identity is emitted by the `ring::rat` producer and none
//! is written by hand.

#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::GeoPrelude;
use super::QPlaneNames;
use crate::Kernel;
use crate::KernelError;
use crate::RatPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;
use crate::rat_prelude::ops::{
    radd, rat_ty, rchain, rcongr, req, rmul, rneg, rsymm, rtrans, rzero,
};

/// The interned names [`declare_all`] produces.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QAffineNames {
    /// `Geo.QPlane.offRaw : Geo.QPoint → Geo.QLine0 → Prop` — `onRaw P l →
    /// False`. The NEGATION, which over ℚ is usable because `Rat.mul_eq_zero`
    /// consumes it; the ℝ model needs a witness instead.
    pub off_raw: NameId,
    /// `Geo.QPlane.off : Geo.QPoint → Geo.QLine → Prop`.
    pub off: NameId,
    /// `Geo.QPlane.parPosRaw : Geo.QLine0 → Geo.QLine0 → Prop` — same
    /// direction, and NOT proportional overall. See the module docs.
    pub par_pos_raw: NameId,
    /// `Geo.QPlane.parPos : Geo.QLine → Geo.QLine → Prop`.
    pub par_pos: NameId,
    /// `Geo.QPlane.offNotOn : ∀ P l, off P l → on P l → False`.
    pub off_not_on: NameId,
    /// `Geo.QPlane.defectAC : ∀ a b c A B C p q, a*p + b*q + c = 0 →
    /// A*p + B*q + C = 0 → a*B = b*A → a*C = c*A` — the ℚ analogue of
    /// `Geo.RPlane.defectAC`, over eight bare rationals.
    pub defect_ac: NameId,
    /// `Geo.QPlane.defectBC : … → b*C = c*B`.
    pub defect_bc: NameId,
    /// `Geo.QPlane.parPosDisjoint : ∀ l m P, parPos l m → on P l → on P m →
    /// False`.
    pub par_pos_disjoint: NameId,
    /// `Geo.QPlane.parLine : Geo.QPoint → Geo.QLine0 → Geo.QLine0` —
    /// `(a l, b l, −(a l * x P + b l * y P))`, the parallel to `l` through
    /// `P`. Its leading coefficients are `l`'s, so its non-degeneracy IS
    /// `l`'s with nothing to prove.
    pub par_line: NameId,
    /// `Geo.QPlane.parLineOn : ∀ P l, onRaw P (parLine P l)`.
    pub par_line_on: NameId,
    /// `Geo.QPlane.parLineDir : ∀ P l,
    /// a l * b (parLine P l) = b l * a (parLine P l)`.
    pub par_line_dir: NameId,
    /// `Geo.QPlane.parNondegPair : ∀ a b c x y, ((a = 0 ∧ b = 0) → False) →
    /// ((a*x + b*y + c = 0) → False) →
    /// ((a * −(a*x + b*y) = c*a) ∧ (b * −(a*x + b*y) = c*b)) → False` — the
    /// distinctness half of `playfairExists`, over five bare rationals.
    pub par_nondeg_pair: NameId,
    /// `Geo.QPlane.playfairExists : ∀ P l, off P l → ∃ m, on P m ∧ parPos l m`.
    pub playfair_exists: NameId,
    /// `Geo.QPlane.dirPivot : ∀ a b A B A' B',
    /// ((a = 0 → False) ∨ (b = 0 → False)) → a*B = b*A → a*B' = b*A' →
    /// A*B' = B*A'` — **two lines with the same direction as a third have the
    /// same direction as each other**, and the only place Playfair's
    /// uniqueness half divides.
    pub dir_pivot: NameId,
    /// `Geo.QPlane.propSwap : ∀ α β α' β', α*β' = β*α' → α'*β = β'*α`.
    pub prop_swap: NameId,
    /// `Geo.QPlane.playfairUnique : ∀ P l m n, parPos l m → parPos l n →
    /// on P m → on P n → Geo.QLine.Equiv m n`.
    pub playfair_unique: NameId,
    /// `Geo.qaffine : Geo.Affine` — the model itself.
    pub instance: NameId,
}

/// Pre-compute every name this module declares. `geo` is the `Geo` namespace
/// root interned by [`super::intern`].
pub(crate) fn intern(kernel: &mut Kernel, geo: NameId) -> QAffineNames {
    let plane = kernel.name_str(geo, "QPlane");
    QAffineNames {
        off_raw: kernel.name_str(plane, "offRaw"),
        off: kernel.name_str(plane, "off"),
        par_pos_raw: kernel.name_str(plane, "parPosRaw"),
        par_pos: kernel.name_str(plane, "parPos"),
        off_not_on: kernel.name_str(plane, "offNotOn"),
        defect_ac: kernel.name_str(plane, "defectAC"),
        defect_bc: kernel.name_str(plane, "defectBC"),
        par_pos_disjoint: kernel.name_str(plane, "parPosDisjoint"),
        par_line: kernel.name_str(plane, "parLine"),
        par_line_on: kernel.name_str(plane, "parLineOn"),
        par_line_dir: kernel.name_str(plane, "parLineDir"),
        par_nondeg_pair: kernel.name_str(plane, "parNondegPair"),
        playfair_exists: kernel.name_str(plane, "playfairExists"),
        dir_pivot: kernel.name_str(plane, "dirPivot"),
        prop_swap: kernel.name_str(plane, "propSwap"),
        playfair_unique: kernel.name_str(plane, "playfairUnique"),
        instance: kernel.name_str(geo, "qaffine"),
    }
}

// ---------------------------------------------------------------------------
// Term shorthands. `qplane`'s own copies are private to that module and this
// one is its sibling, not its child, so these are re-stated rather than
// imported. Each is the same three lines.
// ---------------------------------------------------------------------------

fn point_ty(d: &mut IntDev<'_>, q: QPlaneNames) -> ExprId {
    d.kernel().const_(q.qpoint, vec![])
}

fn line0_ty(d: &mut IntDev<'_>, q: QPlaneNames) -> ExprId {
    d.kernel().const_(q.qline0, vec![])
}

fn line_ty(d: &mut IntDev<'_>, q: QPlaneNames) -> ExprId {
    d.kernel().const_(q.qline, vec![])
}

fn prop_ty(d: &mut IntDev<'_>) -> ExprId {
    let l0 = d.kernel().level_zero();
    d.kernel().sort(l0)
}

fn px(d: &mut IntDev<'_>, q: QPlaneNames, p: ExprId) -> ExprId {
    d.const_app(q.qpoint_x, &[p])
}

fn py(d: &mut IntDev<'_>, q: QPlaneNames, p: ExprId) -> ExprId {
    d.const_app(q.qpoint_y, &[p])
}

fn la(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId) -> ExprId {
    d.const_app(q.qline0_a, &[l])
}

fn lb(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId) -> ExprId {
    d.const_app(q.qline0_b, &[l])
}

fn lc(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId) -> ExprId {
    d.const_app(q.qline0_c, &[l])
}

fn lmk(d: &mut IntDev<'_>, q: QPlaneNames, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    d.const_app(q.qline0_mk, &[a, b, c])
}

/// `a * s + b * t + c`, the raw incidence expression.
fn eval(d: &mut IntDev<'_>, a: ExprId, b: ExprId, c: ExprId, s: ExprId, t: ExprId) -> ExprId {
    let m1 = rmul(d, a, s);
    let m2 = rmul(d, b, t);
    let sum = radd(d, m1, m2);
    radd(d, sum, c)
}

fn false_ty(d: &mut IntDev<'_>) -> ExprId {
    let name = d.int().logic.false_;
    d.kernel().const_(name, vec![])
}

fn and_ty(d: &mut IntDev<'_>, p: ExprId, r: ExprId) -> ExprId {
    let name = d.int().logic.and;
    d.const_app(name, &[p, r])
}

fn and_intro(d: &mut IntDev<'_>, p: ExprId, r: ExprId, hp: ExprId, hr: ExprId) -> ExprId {
    let name = d.int().logic.and_intro;
    d.const_app(name, &[p, r, hp, hr])
}

fn and_l(d: &mut IntDev<'_>, p: ExprId, r: ExprId, h: ExprId) -> ExprId {
    let name = d.int().logic.and_left;
    d.const_app(name, &[p, r, h])
}

fn and_r(d: &mut IntDev<'_>, p: ExprId, r: ExprId, h: ExprId) -> ExprId {
    let name = d.int().logic.and_right;
    d.const_app(name, &[p, r, h])
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

/// `Subtype.val.{1} Geo.QLine0 Geo.QLine0.Nondeg l`.
fn lval(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let val = d.kernel().const_(sigma.subtype_val, vec![one]);
    let base = line0_ty(d, q);
    let nd = d.kernel().const_(q.nondeg, vec![]);
    d.apply(val, &[base, nd, l])
}

/// `Subtype.mk.{1} Geo.QLine0 Geo.QLine0.Nondeg l proof`.
fn lsub(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId, proof: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let mk = d.kernel().const_(sigma.subtype_mk, vec![one]);
    let base = line0_ty(d, q);
    let nd = d.kernel().const_(q.nondeg, vec![]);
    d.apply(mk, &[base, nd, l, proof])
}

/// `Subtype.property.{1} Geo.QLine0 Geo.QLine0.Nondeg l`.
fn lprop(d: &mut IntDev<'_>, q: QPlaneNames, l: ExprId) -> ExprId {
    let one = d.level_one();
    let sigma = d.int().logic.sigma;
    let prop = d.kernel().const_(sigma.subtype_property, vec![one]);
    let base = line0_ty(d, q);
    let nd = d.kernel().const_(q.nondeg, vec![]);
    d.apply(prop, &[base, nd, l])
}

/// A ring identity over ℚ, searched for and emitted by `ring::rat` — never
/// written by hand.
///
/// # Panics
///
/// Panics when the producer declines: every call site here is an identity this
/// file claims is a ring identity, so a decline is an internal inconsistency
/// and the rendered goal is what a reader needs to see.
fn ring_eq(d: &mut IntDev<'_>, rat: &RatPrelude, lhs: ExprId, rhs: ExprId) -> ExprId {
    match crate::ring::rat::prove_eq(d, rat, lhs, rhs) {
        Ok(proof) => proof,
        Err(decline) => {
            let l = d.kernel().render_lean(lhs);
            let r = d.kernel().render_lean(rhs);
            panic!("ring::rat declined {decline:?} on\n  {l}\n=\n  {r}");
        }
    }
}

// ---------------------------------------------------------------------------
// Turning an equation into a vanishing difference and back, and the general
// "unconditional identity plus a list of zeros" combinator every algebraic
// lemma in this file is written against.
// ---------------------------------------------------------------------------

/// `x + (−y) = 0`, from `h : x = y`.
fn to_zero(d: &mut IntDev<'_>, rat: RatPrelude, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
    let z = rzero(d, rat);
    let ny = rneg(d, y);
    let start = radd(d, x, ny);
    let mid = radd(d, y, ny);
    let s1 = rcongr(d, x, y, h, &|d, hole| {
        let n = rneg(d, y);
        radd(d, hole, n)
    });
    let s2 = ring_eq(d, &rat, mid, z);
    rtrans(d, start, mid, z, s1, s2)
}

/// `x = y`, from `h : x + (−y) = 0`.
fn of_zero(d: &mut IntDev<'_>, rat: RatPrelude, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
    let z = rzero(d, rat);
    let ny = rneg(d, y);
    let diff = radd(d, x, ny);
    let lifted = radd(d, diff, y);
    let zeroed = radd(d, z, y);
    let s1 = ring_eq(d, &rat, x, lifted);
    let s2 = rcongr(d, diff, z, h, &|d, hole| radd(d, hole, y));
    let s3 = ring_eq(d, &rat, zeroed, y);
    let (_, proof) = rchain(d, x, &[(lifted, s1), (zeroed, s2), (y, s3)]);
    proof
}

/// The left-nested sum `k₀*x₀ + … + kₙ₋₁*xₙ₋₁`, where `xᵢ` is `Rat.zero` for
/// `i < zeroed`, `hole` when `i == zeroed` and `hole` is given, and `eᵢ`
/// otherwise.
fn nested_sum(
    d: &mut IntDev<'_>,
    terms: &[(ExprId, ExprId, ExprId)],
    zeroed: usize,
    hole: Option<ExprId>,
    z: ExprId,
) -> ExprId {
    let mut acc: Option<ExprId> = None;
    for (i, &(k, e, _)) in terms.iter().enumerate() {
        let x = match i.cmp(&zeroed) {
            std::cmp::Ordering::Less => z,
            std::cmp::Ordering::Equal => hole.unwrap_or(e),
            std::cmp::Ordering::Greater => e,
        };
        let m = rmul(d, k, x);
        acc = Some(match acc {
            None => m,
            Some(a) => radd(d, a, m),
        });
    }
    acc.expect("nested_sum needs at least one summand")
}

/// `lhs = 0`, given the unconditional ring identity
/// `lhs = k₀*e₀ + … + kₙ₋₁*eₙ₋₁` (left-nested) and each `hᵢ : eᵢ = 0`.
///
/// The ℚ counterpart of `geo/rplane.rs`'s `sum_hyp_zero`, which is private to
/// that module and works over `CReal.Equiv` rather than `Eq`.
///
/// # Panics
///
/// Panics on an empty slice: every call site has a fixed, nonempty summand
/// list, so an empty one is a coding error in this file.
fn vanish(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    lhs: ExprId,
    terms: &[(ExprId, ExprId, ExprId)],
) -> ExprId {
    assert!(!terms.is_empty(), "vanish needs at least one summand");
    let z = rzero(d, rat);
    let first = nested_sum(d, terms, 0, None, z);
    let mut steps: Vec<(ExprId, ExprId)> = Vec::with_capacity(terms.len() + 2);
    let s0 = ring_eq(d, &rat, lhs, first);
    steps.push((first, s0));
    for (i, &(_, e, h)) in terms.iter().enumerate() {
        let step = rcongr(d, e, z, h, &|d, hole| {
            nested_sum(d, terms, i, Some(hole), z)
        });
        let next = nested_sum(d, terms, i + 1, None, z);
        steps.push((next, step));
    }
    let all_zero = nested_sum(d, terms, terms.len(), None, z);
    let last = ring_eq(d, &rat, all_zero, z);
    steps.push((z, last));
    let (_, proof) = rchain(d, lhs, &steps);
    proof
}

// ---------------------------------------------------------------------------
// The build.
// ---------------------------------------------------------------------------

/// Declare the ℚ affine layer and the `Geo.qaffine` instance.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
///
/// # Panics
///
/// Panics when the `ring::rat` producer declines an identity this file claims
/// is a ring identity — see [`ring_eq`].
pub(crate) fn declare_all(kernel: &mut Kernel, p: GeoPrelude) -> Result<(), KernelError> {
    let rat = p.cpoint.creal.rat;
    let q = p.qplane;
    let qa = p.qaffine;
    let mut dev = IntDev::new(kernel, rat.int);
    let d = &mut dev;

    declare_predicates(d, rat, q, qa)?;
    declare_off_not_on(d, q, qa)?;
    declare_defects(d, rat, qa)?;
    declare_par_pos_disjoint(d, q, qa)?;
    declare_par_line(d, rat, q, qa)?;
    declare_playfair_exists(d, rat, q, qa)?;
    declare_dir_pivot(d, rat, qa)?;
    declare_playfair_unique(d, rat, q, qa)?;
    declare_instance(d, p, q, qa)
}

/// `offRaw`, `off`, `parPosRaw`, `parPos`.
fn declare_predicates(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    q: QPlaneNames,
    qa: QAffineNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line0 = line0_ty(d, q);
    let line = line_ty(d, q);
    let prop = prop_ty(d);
    let z = rzero(d, rat);

    // offRaw P l := onRaw P l → False.
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let on = d.const_app(q.on_raw, &[pt, l]);
        let f = false_ty(d);
        let body = d.arrow(on, f);
        let value = {
            let inner = d.lam_fv(l_fv, line0, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(line0, prop);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: qa.off_raw,
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
        let raw = lval(d, q, l);
        let body = d.const_app(qa.off_raw, &[pt, raw]);
        let value = {
            let inner = d.lam_fv(l_fv, line, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(line, prop);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: qa.off,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // parPosRaw l m := (a l * b m = b l * a m)
    //                ∧ (((a l * c m = c l * a m) ∧ (b l * c m = c l * b m))
    //                    → False).
    {
        let l_fv = d.fresh_fvar();
        let m_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let m = d.kernel().fvar(m_fv);
        let a = la(d, q, l);
        let b = lb(d, q, l);
        let c = lc(d, q, l);
        let aa = la(d, q, m);
        let bb = lb(d, q, m);
        let cc = lc(d, q, m);
        let dir = {
            let x = rmul(d, a, bb);
            let y = rmul(d, b, aa);
            req(d, x, y)
        };
        let p_ac = {
            let x = rmul(d, a, cc);
            let y = rmul(d, c, aa);
            req(d, x, y)
        };
        let p_bc = {
            let x = rmul(d, b, cc);
            let y = rmul(d, c, bb);
            req(d, x, y)
        };
        let both = and_ty(d, p_ac, p_bc);
        let f = false_ty(d);
        let distinct = d.arrow(both, f);
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
            name: qa.par_pos_raw,
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
        let lr = lval(d, q, l);
        let mr = lval(d, q, m);
        let body = d.const_app(qa.par_pos_raw, &[lr, mr]);
        let value = {
            let inner = d.lam_fv(m_fv, line, body);
            d.lam_fv(l_fv, line, inner)
        };
        let ty = {
            let inner = d.arrow(line, prop);
            d.arrow(line, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: qa.par_pos,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }
    let _ = z;
    Ok(())
}

/// `offNotOn : ∀ P l, off P l → on P l → False` — both sides unfold to the
/// same `onRaw`, so this is function application.
fn declare_off_not_on(
    d: &mut IntDev<'_>,
    q: QPlaneNames,
    qa: QAffineNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line = line_ty(d, q);
    let p_fv = d.fresh_fvar();
    let l_fv = d.fresh_fvar();
    let h_fv = d.fresh_fvar();
    let ho_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(p_fv);
    let l = d.kernel().fvar(l_fv);
    let h = d.kernel().fvar(h_fv);
    let ho = d.kernel().fvar(ho_fv);

    let off_ty = d.const_app(qa.off, &[pt, l]);
    let on_ty = d.const_app(q.on, &[pt, l]);
    let f = false_ty(d);
    let proof = d.apply(h, &[ho]);

    let ty = {
        let t = d.arrow(on_ty, f);
        let t = d.arrow(off_ty, t);
        let t = d.pi_fv(l_fv, line, t);
        d.pi_fv(p_fv, point, t)
    };
    let value = {
        let t = d.lam_fv(ho_fv, on_ty, proof);
        let t = d.lam_fv(h_fv, off_ty, t);
        let t = d.lam_fv(l_fv, line, t);
        d.lam_fv(p_fv, point, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: qa.off_not_on,
        uparams: vec![],
        ty,
        value,
    })
}

/// `defectAC` and `defectBC`, over eight bare rationals.
fn declare_defects(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    qa: QAffineNames,
) -> Result<(), KernelError> {
    let rt = rat_ty(d);
    let z = rzero(d, rat);

    for which_bc in [false, true] {
        let fvs: Vec<u64> = (0..8).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
        let (a, b, c, aa, bb, cc, pp, qq) = (
            vars[0], vars[1], vars[2], vars[3], vars[4], vars[5], vars[6], vars[7],
        );
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let h3_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2 = d.kernel().fvar(h2_fv);
        let h3 = d.kernel().fvar(h3_fv);

        let e_small = eval(d, a, b, c, pp, qq);
        let e_big = eval(d, aa, bb, cc, pp, qq);
        let dir_l = rmul(d, a, bb);
        let dir_r = rmul(d, b, aa);
        let dab = {
            let n = rneg(d, dir_r);
            radd(d, dir_l, n)
        };
        let hd = to_zero(d, rat, dir_l, dir_r, h3);

        // dAC = a*E − A*e − q*dAB ; dBC = b*E − B*e + p*dAB.
        let left = if which_bc { b } else { a };
        let mid = if which_bc { bb } else { aa };
        let target_l = rmul(d, left, cc);
        let target_r = rmul(d, c, mid);
        let target = {
            let n = rneg(d, target_r);
            radd(d, target_l, n)
        };
        let neg_mid = rneg(d, mid);
        let corr = if which_bc { pp } else { rneg(d, qq) };
        let terms = [(left, e_big, h2), (neg_mid, e_small, h1), (corr, dab, hd)];
        let hz = vanish(d, rat, target, &terms);
        let proof = of_zero(d, rat, target_l, target_r, hz);

        let h1_ty = req(d, e_small, z);
        let h2_ty = req(d, e_big, z);
        let h3_ty = req(d, dir_l, dir_r);
        let concl = req(d, target_l, target_r);
        let ty = {
            let t = d.arrow(h3_ty, concl);
            let t = d.arrow(h2_ty, t);
            let mut t = d.arrow(h1_ty, t);
            for &fv in fvs.iter().rev() {
                t = d.pi_fv(fv, rt, t);
            }
            t
        };
        let value = {
            let t = d.lam_fv(h3_fv, h3_ty, proof);
            let t = d.lam_fv(h2_fv, h2_ty, t);
            let mut t = d.lam_fv(h1_fv, h1_ty, t);
            for &fv in fvs.iter().rev() {
                t = d.lam_fv(fv, rt, t);
            }
            t
        };
        let name = if which_bc { qa.defect_bc } else { qa.defect_ac };
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `parPosDisjoint : ∀ l m P, parPos l m → on P l → on P m → False`.
fn declare_par_pos_disjoint(
    d: &mut IntDev<'_>,
    q: QPlaneNames,
    qa: QAffineNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line = line_ty(d, q);

    let l_fv = d.fresh_fvar();
    let m_fv = d.fresh_fvar();
    let p_fv = d.fresh_fvar();
    let hp_fv = d.fresh_fvar();
    let h1_fv = d.fresh_fvar();
    let h2_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let m = d.kernel().fvar(m_fv);
    let pt = d.kernel().fvar(p_fv);
    let hp = d.kernel().fvar(hp_fv);
    let h1 = d.kernel().fvar(h1_fv);
    let h2 = d.kernel().fvar(h2_fv);

    let lr = lval(d, q, l);
    let mr = lval(d, q, m);
    let a = la(d, q, lr);
    let b = lb(d, q, lr);
    let c = lc(d, q, lr);
    let aa = la(d, q, mr);
    let bb = lb(d, q, mr);
    let cc = lc(d, q, mr);
    let sx = px(d, q, pt);
    let sy = py(d, q, pt);

    let dir = {
        let x = rmul(d, a, bb);
        let y = rmul(d, b, aa);
        req(d, x, y)
    };
    let p_ac = {
        let x = rmul(d, a, cc);
        let y = rmul(d, c, aa);
        req(d, x, y)
    };
    let p_bc = {
        let x = rmul(d, b, cc);
        let y = rmul(d, c, bb);
        req(d, x, y)
    };
    let both = and_ty(d, p_ac, p_bc);
    let f = false_ty(d);
    let distinct = d.arrow(both, f);

    let hdir = and_l(d, dir, distinct, hp);
    let hdist = and_r(d, dir, distinct, hp);
    let hac = d.const_app(qa.defect_ac, &[a, b, c, aa, bb, cc, sx, sy, h1, h2, hdir]);
    let hbc = d.const_app(qa.defect_bc, &[a, b, c, aa, bb, cc, sx, sy, h1, h2, hdir]);
    let pair = and_intro(d, p_ac, p_bc, hac, hbc);
    let proof = d.apply(hdist, &[pair]);

    let hp_ty = d.const_app(qa.par_pos, &[l, m]);
    let h1_ty = d.const_app(q.on, &[pt, l]);
    let h2_ty = d.const_app(q.on, &[pt, m]);
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
        name: qa.par_pos_disjoint,
        uparams: vec![],
        ty,
        value,
    })
}

/// `parLine`, `parLineOn`, `parLineDir`, `parNondegPair`.
fn declare_par_line(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    q: QPlaneNames,
    qa: QAffineNames,
) -> Result<(), KernelError> {
    let rt = rat_ty(d);
    let point = point_ty(d, q);
    let line0 = line0_ty(d, q);
    let z = rzero(d, rat);

    // parLine P l := Geo.QLine0.mk (a l) (b l) (−(a l * x P + b l * y P)).
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let a = la(d, q, l);
        let b = lb(d, q, l);
        let sx = px(d, q, pt);
        let sy = py(d, q, pt);
        let m1 = rmul(d, a, sx);
        let m2 = rmul(d, b, sy);
        let sum = radd(d, m1, m2);
        let cc = rneg(d, sum);
        let body = lmk(d, q, a, b, cc);
        let value = {
            let inner = d.lam_fv(l_fv, line0, body);
            d.lam_fv(p_fv, point, inner)
        };
        let ty = {
            let inner = d.arrow(line0, line0);
            d.arrow(point, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: qa.par_line,
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
        let a = la(d, q, l);
        let b = lb(d, q, l);
        let sx = px(d, q, pt);
        let sy = py(d, q, pt);
        let m1 = rmul(d, a, sx);
        let m2 = rmul(d, b, sy);
        let sum = radd(d, m1, m2);
        let cc = rneg(d, sum);
        let lhs = eval(d, a, b, cc, sx, sy);
        let proof = ring_eq(d, &rat, lhs, z);
        let m = d.const_app(qa.par_line, &[pt, l]);
        let concl = d.const_app(q.on_raw, &[pt, m]);
        let ty = {
            let t = d.pi_fv(l_fv, line0, concl);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(l_fv, line0, proof);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: qa.par_line_on,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // parLineDir : ∀ P l, a l * b (parLine P l) = b l * a (parLine P l).
    {
        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let a = la(d, q, l);
        let b = lb(d, q, l);
        let lhs = rmul(d, a, b);
        let rhs = rmul(d, b, a);
        let proof = ring_eq(d, &rat, lhs, rhs);
        let m = d.const_app(qa.par_line, &[pt, l]);
        let ma = la(d, q, m);
        let mb = lb(d, q, m);
        let concl = {
            let x = rmul(d, a, mb);
            let y = rmul(d, b, ma);
            req(d, x, y)
        };
        let ty = {
            let t = d.pi_fv(l_fv, line0, concl);
            d.pi_fv(p_fv, point, t)
        };
        let value = {
            let t = d.lam_fv(l_fv, line0, proof);
            d.lam_fv(p_fv, point, t)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: qa.par_line_dir,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // parNondegPair : ∀ a b c x y, ((a = 0 ∧ b = 0) → False) →
    //   ((a*x + b*y + c = 0) → False) →
    //   ((a * −(a*x + b*y) = c*a) ∧ (b * −(a*x + b*y) = c*b)) → False.
    {
        let fvs: Vec<u64> = (0..5).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
        let (a, b, c, sx, sy) = (vars[0], vars[1], vars[2], vars[3], vars[4]);
        let hnd_fv = d.fresh_fvar();
        let hoff_fv = d.fresh_fvar();
        let hp_fv = d.fresh_fvar();
        let hnd = d.kernel().fvar(hnd_fv);
        let hoff = d.kernel().fvar(hoff_fv);
        let hp = d.kernel().fvar(hp_fv);

        let m1 = rmul(d, a, sx);
        let m2 = rmul(d, b, sy);
        let sum = radd(d, m1, m2);
        let cc = rneg(d, sum);
        let e = eval(d, a, b, c, sx, sy);
        let f = false_ty(d);

        let ea = req(d, a, z);
        let eb = req(d, b, z);
        let ee = req(d, e, z);
        let hnd_ty = {
            let both = and_ty(d, ea, eb);
            d.arrow(both, f)
        };
        let hoff_ty = d.arrow(ee, f);

        let p_ac_l = rmul(d, a, cc);
        let p_ac_r = rmul(d, c, a);
        let p_ac = req(d, p_ac_l, p_ac_r);
        let p_bc_l = rmul(d, b, cc);
        let p_bc_r = rmul(d, c, b);
        let p_bc = req(d, p_bc_l, p_bc_r);
        let hp_ty = and_ty(d, p_ac, p_bc);

        // From `a * (−(a*x + b*y)) = c*a`, conclude `a = 0`.
        //
        // The correction is a bare `−1`, and it is applied as `Rat.neg` of the
        // whole difference rather than as a coefficient `(−1) * …`:
        // `ring::rat`'s `scale_item` mis-derives `count == -1` against an
        // ALREADY-NEGATED monomial (it returns `item.negated()` but proves the
        // conclusion at `Rat.neg it`, so a negated `it` lands at `− − it`), and
        // `a * (−(a*x + b*y))` is exactly such a monomial. Distributing `neg`
        // goes through `Rat.neg_add`/`Rat.neg_neg` and never reaches that path.
        let mut zeros: Vec<ExprId> = Vec::with_capacity(2);
        for (coeff, comp_l, comp_r, which_left) in
            [(a, p_ac_l, p_ac_r, true), (b, p_bc_l, p_bc_r, false)]
        {
            let comp = if which_left {
                and_l(d, p_ac, p_bc, hp)
            } else {
                and_r(d, p_ac, p_bc, hp)
            };
            let dz = to_zero(d, rat, comp_l, comp_r, comp);
            let diff = {
                let n = rneg(d, comp_r);
                radd(d, comp_l, n)
            };
            let prod = rmul(d, coeff, e);
            let neg_diff = rneg(d, diff);
            let neg_zero = rneg(d, z);
            let s1 = ring_eq(d, &rat, prod, neg_diff);
            let s2 = rcongr(d, diff, z, dz, &|d, hole| rneg(d, hole));
            let s3 = ring_eq(d, &rat, neg_zero, z);
            let (_, hz) = rchain(d, prod, &[(neg_diff, s1), (neg_zero, s2), (z, s3)]);
            let split = d.const_app(rat.mul_eq_zero, &[coeff, e, hz]);
            let ecoeff = req(d, coeff, z);
            let branch = d.or_elim(
                ecoeff,
                ee,
                ecoeff,
                split,
                &|_d, hzero| hzero,
                &|d, hzero| {
                    let contra = d.apply(hoff, &[hzero]);
                    let target = req(d, coeff, z);
                    d.absurd(target, contra)
                },
            );
            zeros.push(branch);
        }
        let both = and_intro(d, ea, eb, zeros[0], zeros[1]);
        let proof = d.apply(hnd, &[both]);

        let ty = {
            let t = d.arrow(hp_ty, f);
            let t = d.arrow(hoff_ty, t);
            let mut t = d.arrow(hnd_ty, t);
            for &fv in fvs.iter().rev() {
                t = d.pi_fv(fv, rt, t);
            }
            t
        };
        let value = {
            let t = d.lam_fv(hp_fv, hp_ty, proof);
            let t = d.lam_fv(hoff_fv, hoff_ty, t);
            let mut t = d.lam_fv(hnd_fv, hnd_ty, t);
            for &fv in fvs.iter().rev() {
                t = d.lam_fv(fv, rt, t);
            }
            t
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: qa.par_nondeg_pair,
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
    rat: RatPrelude,
    q: QPlaneNames,
    qa: QAffineNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line = line_ty(d, q);
    let _ = rat;

    let p_fv = d.fresh_fvar();
    let l_fv = d.fresh_fvar();
    let h_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(p_fv);
    let l = d.kernel().fvar(l_fv);
    let h = d.kernel().fvar(h_fv);

    let lr = lval(d, q, l);
    let a = la(d, q, lr);
    let b = lb(d, q, lr);
    let c = lc(d, q, lr);
    let sx = px(d, q, pt);
    let sy = py(d, q, pt);

    let raw = d.const_app(qa.par_line, &[pt, lr]);
    let nd = lprop(d, q, l);
    let m = lsub(d, q, raw, nd);

    let pred = {
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let on = d.const_app(q.on, &[pt, w]);
        let par = d.const_app(qa.par_pos, &[l, w]);
        let body = and_ty(d, on, par);
        d.lam_fv(w_fv, line, body)
    };

    let on_ty = d.const_app(q.on, &[pt, m]);
    let par_ty = d.const_app(qa.par_pos, &[l, m]);
    let on_proof = d.const_app(qa.par_line_on, &[pt, lr]);

    // `parPos l m` unfolds to the conjunction of the direction identity and
    // the refutation of full proportionality; both components are supplied at
    // their REDUCED types and the kernel's delta/iota bridges the gap.
    let par_proof = {
        let dir_proof = d.const_app(qa.par_line_dir, &[pt, lr]);
        let ma = la(d, q, raw);
        let mb = lb(d, q, raw);
        let mc = lc(d, q, raw);
        let dir_ty = {
            let x = rmul(d, a, mb);
            let y = rmul(d, b, ma);
            req(d, x, y)
        };
        let p_ac = {
            let x = rmul(d, a, mc);
            let y = rmul(d, c, ma);
            req(d, x, y)
        };
        let p_bc = {
            let x = rmul(d, b, mc);
            let y = rmul(d, c, mb);
            req(d, x, y)
        };
        let both = and_ty(d, p_ac, p_bc);
        let f = false_ty(d);
        let distinct = d.arrow(both, f);
        let pair_proof = d.const_app(qa.par_nondeg_pair, &[a, b, c, sx, sy, nd, h]);
        and_intro(d, dir_ty, distinct, dir_proof, pair_proof)
    };

    let body = and_intro(d, on_ty, par_ty, on_proof, par_proof);
    let proof = exists_intro(d, line, pred, m, body);

    let h_ty = d.const_app(qa.off, &[pt, l]);
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
        name: qa.playfair_exists,
        uparams: vec![],
        ty,
        value,
    })
}

/// `dirPivot` and `propSwap`.
fn declare_dir_pivot(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    qa: QAffineNames,
) -> Result<(), KernelError> {
    let rt = rat_ty(d);
    let z = rzero(d, rat);

    // dirPivot : ∀ a b A B A' B', ((a = 0 → False) ∨ (b = 0 → False)) →
    //   a*B = b*A → a*B' = b*A' → A*B' = B*A'.
    {
        let fvs: Vec<u64> = (0..6).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
        let (a, b, aa, bb, aa2, bb2) = (vars[0], vars[1], vars[2], vars[3], vars[4], vars[5]);
        let hor_fv = d.fresh_fvar();
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let hor = d.kernel().fvar(hor_fv);
        let h1 = d.kernel().fvar(h1_fv);
        let h2 = d.kernel().fvar(h2_fv);

        let f = false_ty(d);
        let ea = req(d, a, z);
        let eb = req(d, b, z);
        let ne_a = d.arrow(ea, f);
        let ne_b = d.arrow(eb, f);
        let hor_ty = {
            let name = d.int().logic.or;
            d.const_app(name, &[ne_a, ne_b])
        };

        let dlm_l = rmul(d, a, bb);
        let dlm_r = rmul(d, b, aa);
        let h1_ty = req(d, dlm_l, dlm_r);
        let dln_l = rmul(d, a, bb2);
        let dln_r = rmul(d, b, aa2);
        let h2_ty = req(d, dln_l, dln_r);
        let dmn_l = rmul(d, aa, bb2);
        let dmn_r = rmul(d, bb, aa2);
        let concl = req(d, dmn_l, dmn_r);

        let hdlm = to_zero(d, rat, dlm_l, dlm_r, h1);
        let hdln = to_zero(d, rat, dln_l, dln_r, h2);
        let dlm = {
            let n = rneg(d, dlm_r);
            radd(d, dlm_l, n)
        };
        let dln = {
            let n = rneg(d, dln_r);
            radd(d, dln_l, n)
        };
        let dmn = {
            let n = rneg(d, dmn_r);
            radd(d, dmn_l, n)
        };
        let dmn_zero_ty = req(d, dmn, z);

        // a*dMN = A*dln − A'*dlm ; b*dMN = B*dln − B'*dlm.
        let mut branches: Vec<ExprId> = Vec::with_capacity(2);
        for (pivot, k_first, k_second) in [(a, aa, aa2), (b, bb, bb2)] {
            let neg_second = rneg(d, k_second);
            let prod = rmul(d, pivot, dmn);
            let hz = vanish(
                d,
                rat,
                prod,
                &[(k_first, dln, hdln), (neg_second, dlm, hdlm)],
            );
            let split = d.const_app(rat.mul_eq_zero, &[pivot, dmn, hz]);
            branches.push(split);
        }
        let split_a = branches[0];
        let split_b = branches[1];

        let hz_dmn = d.or_elim(
            ne_a,
            ne_b,
            dmn_zero_ty,
            hor,
            &|d, hna| {
                let epa = req(d, a, z);
                d.or_elim(
                    epa,
                    dmn_zero_ty,
                    dmn_zero_ty,
                    split_a,
                    &|d, hzero| {
                        let contra = d.apply(hna, &[hzero]);
                        d.absurd(dmn_zero_ty, contra)
                    },
                    &|_d, hzero| hzero,
                )
            },
            &|d, hnb| {
                let epb = req(d, b, z);
                d.or_elim(
                    epb,
                    dmn_zero_ty,
                    dmn_zero_ty,
                    split_b,
                    &|d, hzero| {
                        let contra = d.apply(hnb, &[hzero]);
                        d.absurd(dmn_zero_ty, contra)
                    },
                    &|_d, hzero| hzero,
                )
            },
        );
        let proof = of_zero(d, rat, dmn_l, dmn_r, hz_dmn);

        let ty = {
            let t = d.arrow(h2_ty, concl);
            let t = d.arrow(h1_ty, t);
            let mut t = d.arrow(hor_ty, t);
            for &fv in fvs.iter().rev() {
                t = d.pi_fv(fv, rt, t);
            }
            t
        };
        let value = {
            let t = d.lam_fv(h2_fv, h2_ty, proof);
            let t = d.lam_fv(h1_fv, h1_ty, t);
            let mut t = d.lam_fv(hor_fv, hor_ty, t);
            for &fv in fvs.iter().rev() {
                t = d.lam_fv(fv, rt, t);
            }
            t
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: qa.dir_pivot,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // propSwap : ∀ α β α' β', α*β' = β*α' → α'*β = β'*α.
    {
        let fvs: Vec<u64> = (0..4).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
        let (al, be, al2, be2) = (vars[0], vars[1], vars[2], vars[3]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let src_l = rmul(d, al, be2);
        let src_r = rmul(d, be, al2);
        let h_ty = req(d, src_l, src_r);
        let tgt_l = rmul(d, al2, be);
        let tgt_r = rmul(d, be2, al);
        let concl = req(d, tgt_l, tgt_r);

        let s1 = ring_eq(d, &rat, tgt_l, src_r);
        let s2 = rsymm(d, src_l, src_r, h);
        let s3 = ring_eq(d, &rat, src_l, tgt_r);
        let (_, proof) = rchain(d, tgt_l, &[(src_r, s1), (src_l, s2), (tgt_r, s3)]);

        let ty = {
            let mut t = d.arrow(h_ty, concl);
            for &fv in fvs.iter().rev() {
                t = d.pi_fv(fv, rt, t);
            }
            t
        };
        let value = {
            let mut t = d.lam_fv(h_fv, h_ty, proof);
            for &fv in fvs.iter().rev() {
                t = d.lam_fv(fv, rt, t);
            }
            t
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: qa.prop_swap,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `playfairUnique : ∀ P l m n, parPos l m → parPos l n → on P m → on P n →
/// Geo.QLine.Equiv m n`.
fn declare_playfair_unique(
    d: &mut IntDev<'_>,
    rat: RatPrelude,
    q: QPlaneNames,
    qa: QAffineNames,
) -> Result<(), KernelError> {
    let point = point_ty(d, q);
    let line = line_ty(d, q);
    let _ = rat;

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

    let lr = lval(d, q, l);
    let mr = lval(d, q, m);
    let nr = lval(d, q, n);
    let a = la(d, q, lr);
    let b = lb(d, q, lr);
    let c = lc(d, q, lr);
    let aa = la(d, q, mr);
    let bb = lb(d, q, mr);
    let cc = lc(d, q, mr);
    let aa2 = la(d, q, nr);
    let bb2 = lb(d, q, nr);
    let cc2 = lc(d, q, nr);
    let sx = px(d, q, pt);
    let sy = py(d, q, pt);

    // The two `parPos` hypotheses, opened at their left conjuncts.
    let direction = |d: &mut IntDev<'_>, u: ExprId, v: ExprId, w: ExprId, h: ExprId| -> ExprId {
        let dir = {
            let x = rmul(d, a, v);
            let y = rmul(d, b, u);
            req(d, x, y)
        };
        let p_ac = {
            let x = rmul(d, a, w);
            let y = rmul(d, c, u);
            req(d, x, y)
        };
        let p_bc = {
            let x = rmul(d, b, w);
            let y = rmul(d, c, v);
            req(d, x, y)
        };
        let both = and_ty(d, p_ac, p_bc);
        let f = false_ty(d);
        let distinct = d.arrow(both, f);
        and_l(d, dir, distinct, h)
    };
    let hdir_m = direction(d, aa, bb, cc, h1);
    let hdir_n = direction(d, aa2, bb2, cc2, h2);

    let nd_l = lprop(d, q, l);
    let or_l = d.const_app(q.nondeg_or, &[lr, nd_l]);
    let h_mn = d.const_app(
        qa.dir_pivot,
        &[a, b, aa, bb, aa2, bb2, or_l, hdir_m, hdir_n],
    );
    let h_mac = d.const_app(
        qa.defect_ac,
        &[aa, bb, cc, aa2, bb2, cc2, sx, sy, h3, h4, h_mn],
    );
    let h_mbc = d.const_app(
        qa.defect_bc,
        &[aa, bb, cc, aa2, bb2, cc2, sx, sy, h3, h4, h_mn],
    );
    let h_nm = d.const_app(qa.prop_swap, &[aa, bb, aa2, bb2, h_mn]);
    let h_nac = d.const_app(qa.prop_swap, &[aa, cc, aa2, cc2, h_mac]);
    let h_nbc = d.const_app(qa.prop_swap, &[bb, cc, bb2, cc2, h_mbc]);

    let nd_m = lprop(d, q, m);
    let or_m = d.const_app(q.nondeg_or, &[mr, nd_m]);
    let nd_n = lprop(d, q, n);
    let or_n = d.const_app(q.nondeg_or, &[nr, nd_n]);

    let target = d.const_app(q.line_equiv, &[m, n]);
    let body = {
        let x_fv = d.fresh_fvar();
        let xt = d.kernel().fvar(x_fv);
        let xx = px(d, q, xt);
        let xy = py(d, q, xt);
        let oxm = d.const_app(q.on, &[xt, m]);
        let oxn = d.const_app(q.on, &[xt, n]);
        let fwd_ty = d.arrow(oxm, oxn);
        let bwd_ty = d.arrow(oxn, oxm);
        let fwd = {
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let step = d.const_app(
                q.on_of_prop,
                &[
                    aa, bb, cc, aa2, bb2, cc2, xx, xy, or_m, h_mn, h_mac, h_mbc, hx,
                ],
            );
            d.lam_fv(hx_fv, oxm, step)
        };
        let bwd = {
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let step = d.const_app(
                q.on_of_prop,
                &[
                    aa2, bb2, cc2, aa, bb, cc, xx, xy, or_n, h_nm, h_nac, h_nbc, hx,
                ],
            );
            d.lam_fv(hx_fv, oxn, step)
        };
        let pair = and_intro(d, fwd_ty, bwd_ty, fwd, bwd);
        d.lam_fv(x_fv, point, pair)
    };

    let h1_ty = d.const_app(qa.par_pos, &[l, m]);
    let h2_ty = d.const_app(qa.par_pos, &[l, n]);
    let h3_ty = d.const_app(q.on, &[pt, m]);
    let h4_ty = d.const_app(q.on, &[pt, n]);
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
        let t = d.lam_fv(h4_fv, h4_ty, body);
        let t = d.lam_fv(h3_fv, h3_ty, t);
        let t = d.lam_fv(h2_fv, h2_ty, t);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(n_fv, line, t);
        let t = d.lam_fv(m_fv, line, t);
        let t = d.lam_fv(l_fv, line, t);
        d.lam_fv(p_fv, point, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: qa.playfair_unique,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Geo.qaffine : Geo.Affine`.
fn declare_instance(
    d: &mut IntDev<'_>,
    p: GeoPrelude,
    q: QPlaneNames,
    qa: QAffineNames,
) -> Result<(), KernelError> {
    let inc = d.kernel().const_(q.instance, vec![]);
    let par_pos = d.kernel().const_(qa.par_pos, vec![]);
    let off = d.kernel().const_(qa.off, vec![]);
    let off_not_on = d.kernel().const_(qa.off_not_on, vec![]);
    let disjoint = d.kernel().const_(qa.par_pos_disjoint, vec![]);
    let exists = d.kernel().const_(qa.playfair_exists, vec![]);
    let unique = d.kernel().const_(qa.playfair_unique, vec![]);

    let args = [inc, par_pos, off, off_not_on, disjoint, exists, unique];
    assert_eq!(
        args.len(),
        super::affine::AFFINE_FIELD_COUNT,
        "the instance's argument list is out of step with the record"
    );
    let value = mk_instance(d.kernel(), &p.affine.record, &args);
    let ty = d.kernel().const_(p.affine.record.ind, vec![]);
    d.kernel().add_declaration(Declaration::Definition {
        name: qa.instance,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}
