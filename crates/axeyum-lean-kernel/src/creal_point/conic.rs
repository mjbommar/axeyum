//! **Conics as a six-coefficient family on the real plane, and the
//! discriminant that classifies them.**
//!
//! A conic here is *data*, not a predicate: `CPoint.Conic` is a
//! one-constructor inductive carrying `(A, B, C, D, E, F) : CReal⁶`, and
//! `CPoint.OnConic K P` is the proposition
//! `A x² + B x y + C y² + D x + E y + F ~ 0` at `P = (x, y)`. That split is
//! what makes the rest of the file possible: an isometry acts on the
//! *coefficients* (`CPoint.Conic.rotate`, `.reflect`, `.translate` are total
//! functions `Conic → Conic`), so "the classification is isometry-invariant"
//! becomes an equation between two `CReal`s rather than a statement about
//! sets of points.
//!
//! ## What is here
//!
//! | | |
//! |---|---|
//! | the family | `Conic`, `Conic.mk`, the six projections, `Conic.eval`, `OnConic` |
//! | the classifier | `Conic.discriminant` (`B² − 4AC`), `IsEllipseType`/`IsParabolaType`/`IsHyperbolaType` |
//! | the classifier is a classifier | the three pairwise exclusion theorems |
//! | circles | `Conic.circle`, `onConic_circle_iff`, `Conic.circle_isEllipseType` |
//! | isometry action | `Conic.rotate`/`.reflect`/`.translate` with their `onConic_*_iff` and `discriminant_*` laws |
//! | invariance | `discriminant_rotate_unit`/`discriminant_reflect_unit`/`discriminant_translate`, the three `is*Type_congr` transfer lemmas, and nine `is*Type_*` corollaries |
//! | standard forms | `Conic.ellipse`, `Conic.parabola`, `Conic.hyperbola`, `Conic.parabolaFocal` with their discriminant signs |
//! | focus–directrix | `parabola_focus_directrix`, square-root-free |
//!
//! ## The three strict predicates, and why apartness is not a fourth thing
//!
//! `IsEllipseType K := lt (discriminant K) zero` and
//! `IsHyperbolaType K := lt zero (discriminant K)` are `CReal.lt`, whose
//! witness **carries a rational gap**; the middle case
//! `IsParabolaType K := Equiv (discriminant K) zero` is the setoid equality.
//! `CReal.apart x y` is `Or (lt x y) (lt y x)`, so
//! `IsEllipseType K ∨ IsHyperbolaType K` **is** `apart (discriminant K) zero`
//! definitionally — the apartness a strict classification needs is exactly
//! the disjunction of the two strict predicates, and no separate
//! `apart`-shaped declaration buys anything.
//!
//! Constructively the three do **not** cover: there is no
//! `∀ K, Or (Or …) …` trichotomy here, because deciding the sign of a general
//! real is not constructive. What *is* proved is that they are pairwise
//! exclusive (`Conic.not_ellipse_and_parabola` and its two siblings), and
//! that each is **inhabited** by a named instance (`Conic.ellipse`,
//! `Conic.parabola`, `Conic.hyperbola`). Exclusivity without inhabitation
//! would be a classification that cannot fail; inhabitation without
//! exclusivity would be three predicates that might all hold at once. Both
//! halves are here.
//!
//! ## Why the discriminant's `4` is spelled out
//!
//! `CPoint.Scalar.four` is `CPoint.Scalar.two + CPoint.Scalar.two`, i.e.
//! `(1+1)+(1+1)` after two delta steps, and every ring-normalizer mirror in
//! this file writes it as four `RnExpr::One`s. It cannot be an opaque atom
//! `t`: the invariance identity `B'² − t·A'C' = (B² − t·AC)(c²+s²)²` is
//! **false** for symbolic `t` — the `t`-free part of the left side carries
//! `A²`, `B²` and `C²` monomials the right side has only when `t` is
//! literally `4`. Checked before the proof was attempted; otherwise
//! `rn_ring_proof` would have failed with its "different normal forms"
//! assertion, which says nothing about why.
//!
//! ## What the ring producer discharges, and what it does not
//!
//! Every algebraic obligation here is a commutative-ring identity over
//! `CReal.Equiv`, and `rn_ring_proof` discharges each of them **flat** — the
//! coefficient-action laws (17 monomials a side), the invariance identity (72
//! monomials on the left, cancelling to 20), the circle correspondence, and
//! the focus–directrix characterisation. No staging was needed anywhere, and
//! **no analytic fact about `CReal` is used**: not `sqrt`, not `inv`, not
//! completeness. Order facts appear only where a sign has to become a `lt` —
//! the four sign theorems and the three exclusions.
//!
//! ## What is deliberately not here
//!
//! - **`sqrt` and the quadratic formula.** "A line meets a conic in at most
//!   two points" needs root extraction, and over a constructive real that
//!   needs a decision on the sign of the *restricted* quadratic's own
//!   discriminant, which the three predicates above cannot supply for a
//!   general conic.
//! - **The general classification `IsEllipseType K → ∃ isometry, …`**: it
//!   needs the eigenvector rotation angle (so a square root) and the
//!   `±`-choice discussed in `creal_point/isometry.rs`'s own header.

#![allow(clippy::too_many_arguments, clippy::too_many_lines)]

use crate::BinderInfo;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::{CPointPrelude, Kernel, KernelError};

use super::{
    DERIVED_HEIGHT, RnExpr, cadd, chain, cmul, cneg, creal_ty, czero, equiv, equiv_of_sub_eq_zero,
    neg_add_cancel_proof, point_ty, refl, rn_ring_proof, sub_eq_zero_of_equiv, symm,
};

/// Heights above every other `creal_point` height (`isometry.rs` tops out at
/// `DERIVED_HEIGHT + 45`), so nothing here changes another module's
/// delta-unfolding order.
const CONIC_HEIGHT: u16 = DERIVED_HEIGHT + 100;

/// The interned names this module declares, as an ADR-1512-style registry
/// rather than fifty more flat fields on [`CPointPrelude`] — the shape the
/// 2026-08-27 architecture review asks new prelude modules to use, and the
/// shape `scripts/gen-py-prelude-fields.py` flattens to `cpoint["conic.…"]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConicNames {
    /// `CPoint.Scalar.four := CReal.add CPoint.Scalar.two CPoint.Scalar.two`.
    pub four: NameId,
    /// `CPoint.Scalar.zero_lt_four : CReal.lt CReal.zero CPoint.Scalar.four`.
    pub zero_lt_four: NameId,
    /// `CPoint.Scalar.neg_lt_zero_of_pos : ∀ x, lt zero x → lt (neg x) zero`.
    pub neg_lt_zero_of_pos: NameId,
    /// `CPoint.Conic : Type` — one constructor, six `CReal` fields.
    pub conic: NameId,
    /// `CPoint.Conic.mk : CReal → CReal → CReal → CReal → CReal → CReal → Conic`.
    pub mk: NameId,
    /// `CPoint.Conic.rec` — the kernel-generated recursor.
    pub rec: NameId,
    /// `CPoint.Conic.a : Conic → CReal`, the `x²` coefficient.
    pub a: NameId,
    /// `CPoint.Conic.b : Conic → CReal`, the `x y` coefficient.
    pub b: NameId,
    /// `CPoint.Conic.c : Conic → CReal`, the `y²` coefficient.
    pub c: NameId,
    /// `CPoint.Conic.d : Conic → CReal`, the `x` coefficient.
    pub d: NameId,
    /// `CPoint.Conic.e : Conic → CReal`, the `y` coefficient.
    pub e: NameId,
    /// `CPoint.Conic.f : Conic → CReal`, the constant term.
    pub f: NameId,
    /// `CPoint.Conic.eval K P := A x² + B x y + C y² + D x + E y + F`.
    pub eval: NameId,
    /// `CPoint.OnConic K P := Equiv (Conic.eval K P) CReal.zero`.
    pub on_conic: NameId,
    /// `CPoint.Conic.discriminant K := B·B − four·(A·C)`.
    pub discriminant: NameId,
    /// `CPoint.IsEllipseType K := lt (discriminant K) zero`.
    pub is_ellipse_type: NameId,
    /// `CPoint.IsParabolaType K := Equiv (discriminant K) zero`.
    pub is_parabola_type: NameId,
    /// `CPoint.IsHyperbolaType K := lt zero (discriminant K)`.
    pub is_hyperbola_type: NameId,
    /// `CPoint.Conic.not_ellipse_and_parabola : ∀ K, IsEllipseType K →
    /// IsParabolaType K → False`.
    pub not_ellipse_and_parabola: NameId,
    /// `CPoint.Conic.not_ellipse_and_hyperbola : ∀ K, IsEllipseType K →
    /// IsHyperbolaType K → False`.
    pub not_ellipse_and_hyperbola: NameId,
    /// `CPoint.Conic.not_parabola_and_hyperbola : ∀ K, IsParabolaType K →
    /// IsHyperbolaType K → False`.
    pub not_parabola_and_hyperbola: NameId,
    /// `CPoint.Conic.isEllipseType_congr : ∀ K L,
    /// Equiv (discriminant K) (discriminant L) → IsEllipseType K →
    /// IsEllipseType L`.
    pub is_ellipse_type_congr: NameId,
    /// `CPoint.Conic.isParabolaType_congr` — the same for the middle case.
    pub is_parabola_type_congr: NameId,
    /// `CPoint.Conic.isHyperbolaType_congr` — the same for the open case.
    pub is_hyperbola_type_congr: NameId,
    /// `CPoint.Conic.circle O r2` — the conic with `A = C = 1`, `B = 0` whose
    /// zero set is `CPoint.OnCircle _ O r2`.
    pub circle: NameId,
    /// `CPoint.onConic_circle_iff : ∀ O r2 P,
    /// Iff (OnConic (Conic.circle O r2) P) (OnCircle P O r2)`.
    pub on_conic_circle_iff: NameId,
    /// `CPoint.Conic.circle_isEllipseType : ∀ O r2,
    /// IsEllipseType (Conic.circle O r2)` — every circle is of ellipse type
    /// (`discriminant ~ −4`), the degenerate `r2 ≤ 0` ones included.
    pub circle_is_ellipse_type: NameId,
    /// `CPoint.Conic.rotate c s K` — the conic whose zero set is the
    /// `CPoint.rotate c s` preimage of `K`'s.
    pub rotate: NameId,
    /// `CPoint.onConic_rotate_iff : ∀ c s K P,
    /// Iff (OnConic (Conic.rotate c s K) P) (OnConic K (CPoint.rotate c s P))`.
    pub on_conic_rotate_iff: NameId,
    /// `CPoint.Conic.discriminant_rotate : ∀ c s K,
    /// Equiv (discriminant (Conic.rotate c s K))
    ///       (mul (discriminant K) (mul (c·c + s·s) (c·c + s·s)))` — the
    /// unconditional form, with no `c² + s² ~ 1` hypothesis.
    pub discriminant_rotate: NameId,
    /// `CPoint.Conic.discriminant_rotate_unit` — the same under
    /// `Equiv (add (mul c c) (mul s s)) one`, i.e. for a genuine rotation.
    pub discriminant_rotate_unit: NameId,
    /// `CPoint.Conic.reflect c s K`.
    pub reflect: NameId,
    /// `CPoint.onConic_reflect_iff`.
    pub on_conic_reflect_iff: NameId,
    /// `CPoint.Conic.discriminant_reflect` — the same `(c²+s²)²` factor as
    /// the rotation: a reflection has determinant `−(c²+s²)`, and the
    /// discriminant sees only its square.
    pub discriminant_reflect: NameId,
    /// `CPoint.Conic.discriminant_reflect_unit`.
    pub discriminant_reflect_unit: NameId,
    /// `CPoint.Conic.translate T K`.
    pub translate: NameId,
    /// `CPoint.onConic_translate_iff`.
    pub on_conic_translate_iff: NameId,
    /// `CPoint.Conic.discriminant_translate : ∀ T K,
    /// Equiv (discriminant (Conic.translate T K)) (discriminant K)` — a
    /// translation does not touch `A`, `B` or `C` at all, so this one holds
    /// with no hypothesis and its proof is `Equiv.refl`.
    pub discriminant_translate: NameId,
    /// `CPoint.Conic.isEllipseType_rotate`.
    pub is_ellipse_type_rotate: NameId,
    /// `CPoint.Conic.isParabolaType_rotate`.
    pub is_parabola_type_rotate: NameId,
    /// `CPoint.Conic.isHyperbolaType_rotate`.
    pub is_hyperbola_type_rotate: NameId,
    /// `CPoint.Conic.isEllipseType_reflect`.
    pub is_ellipse_type_reflect: NameId,
    /// `CPoint.Conic.isParabolaType_reflect`.
    pub is_parabola_type_reflect: NameId,
    /// `CPoint.Conic.isHyperbolaType_reflect`.
    pub is_hyperbola_type_reflect: NameId,
    /// `CPoint.Conic.isEllipseType_translate`.
    pub is_ellipse_type_translate: NameId,
    /// `CPoint.Conic.isParabolaType_translate`.
    pub is_parabola_type_translate: NameId,
    /// `CPoint.Conic.isHyperbolaType_translate`.
    pub is_hyperbola_type_translate: NameId,
    /// `CPoint.Conic.ellipse a b := b²x² + a²y² − a²b²`, the standard
    /// `x²/a² + y²/b² = 1` cleared of denominators — which is what keeps
    /// `CReal.inv` (partial, `PosBound`-gated) out of the file entirely.
    pub ellipse: NameId,
    /// `CPoint.Conic.ellipse_isEllipseType : ∀ a b, lt zero a → lt zero b →
    /// IsEllipseType (Conic.ellipse a b)`.
    pub ellipse_is_ellipse_type: NameId,
    /// `CPoint.Conic.parabola a := a x² − y`, the standard `y = a x²`.
    pub parabola: NameId,
    /// `CPoint.Conic.parabola_isParabolaType : ∀ a,
    /// IsParabolaType (Conic.parabola a)` — with **no** hypothesis on `a`:
    /// `B = C = 0` makes `B² − 4AC` vanish identically, so the degenerate
    /// `a ~ 0` line is of parabola type too.
    pub parabola_is_parabola_type: NameId,
    /// `CPoint.Conic.hyperbola a b := b²x² − a²y² − a²b²`.
    pub hyperbola: NameId,
    /// `CPoint.Conic.hyperbola_isHyperbolaType : ∀ a b, lt zero a →
    /// lt zero b → IsHyperbolaType (Conic.hyperbola a b)`.
    pub hyperbola_is_hyperbola_type: NameId,
    /// `CPoint.Conic.parabolaFocal p := x² − four·(p·y)`, i.e. `x² = 4py`.
    pub parabola_focal: NameId,
    /// `CPoint.Conic.parabolaFocal_isParabolaType`.
    pub parabola_focal_is_parabola_type: NameId,
    /// **The focus–directrix property of the parabola, without a square
    /// root.** `∀ p P, Iff (OnConic (Conic.parabolaFocal p) P)
    /// (Equiv (distSq P (CPoint.mk zero p)) ((y P + p)·(y P + p)))` — the
    /// squared distance to the focus `(0, p)` equals the squared distance to
    /// the directrix `y = −p`. Comparing squares is what removes the
    /// `CReal.sqrt` the usual statement needs.
    pub parabola_focus_directrix: NameId,
}

pub(super) fn intern(kernel: &mut Kernel, point: NameId, scalar: NameId) -> ConicNames {
    let conic = kernel.name_str(point, "Conic");
    ConicNames {
        four: kernel.name_str(scalar, "four"),
        zero_lt_four: kernel.name_str(scalar, "zero_lt_four"),
        neg_lt_zero_of_pos: kernel.name_str(scalar, "neg_lt_zero_of_pos"),
        conic,
        mk: kernel.name_str(conic, "mk"),
        rec: kernel.name_str(conic, "rec"),
        a: kernel.name_str(conic, "a"),
        b: kernel.name_str(conic, "b"),
        c: kernel.name_str(conic, "c"),
        d: kernel.name_str(conic, "d"),
        e: kernel.name_str(conic, "e"),
        f: kernel.name_str(conic, "f"),
        eval: kernel.name_str(conic, "eval"),
        on_conic: kernel.name_str(point, "OnConic"),
        discriminant: kernel.name_str(conic, "discriminant"),
        is_ellipse_type: kernel.name_str(point, "IsEllipseType"),
        is_parabola_type: kernel.name_str(point, "IsParabolaType"),
        is_hyperbola_type: kernel.name_str(point, "IsHyperbolaType"),
        not_ellipse_and_parabola: kernel.name_str(conic, "not_ellipse_and_parabola"),
        not_ellipse_and_hyperbola: kernel.name_str(conic, "not_ellipse_and_hyperbola"),
        not_parabola_and_hyperbola: kernel.name_str(conic, "not_parabola_and_hyperbola"),
        is_ellipse_type_congr: kernel.name_str(conic, "isEllipseType_congr"),
        is_parabola_type_congr: kernel.name_str(conic, "isParabolaType_congr"),
        is_hyperbola_type_congr: kernel.name_str(conic, "isHyperbolaType_congr"),
        circle: kernel.name_str(conic, "circle"),
        on_conic_circle_iff: kernel.name_str(point, "onConic_circle_iff"),
        circle_is_ellipse_type: kernel.name_str(conic, "circle_isEllipseType"),
        rotate: kernel.name_str(conic, "rotate"),
        on_conic_rotate_iff: kernel.name_str(point, "onConic_rotate_iff"),
        discriminant_rotate: kernel.name_str(conic, "discriminant_rotate"),
        discriminant_rotate_unit: kernel.name_str(conic, "discriminant_rotate_unit"),
        reflect: kernel.name_str(conic, "reflect"),
        on_conic_reflect_iff: kernel.name_str(point, "onConic_reflect_iff"),
        discriminant_reflect: kernel.name_str(conic, "discriminant_reflect"),
        discriminant_reflect_unit: kernel.name_str(conic, "discriminant_reflect_unit"),
        translate: kernel.name_str(conic, "translate"),
        on_conic_translate_iff: kernel.name_str(point, "onConic_translate_iff"),
        discriminant_translate: kernel.name_str(conic, "discriminant_translate"),
        is_ellipse_type_rotate: kernel.name_str(conic, "isEllipseType_rotate"),
        is_parabola_type_rotate: kernel.name_str(conic, "isParabolaType_rotate"),
        is_hyperbola_type_rotate: kernel.name_str(conic, "isHyperbolaType_rotate"),
        is_ellipse_type_reflect: kernel.name_str(conic, "isEllipseType_reflect"),
        is_parabola_type_reflect: kernel.name_str(conic, "isParabolaType_reflect"),
        is_hyperbola_type_reflect: kernel.name_str(conic, "isHyperbolaType_reflect"),
        is_ellipse_type_translate: kernel.name_str(conic, "isEllipseType_translate"),
        is_parabola_type_translate: kernel.name_str(conic, "isParabolaType_translate"),
        is_hyperbola_type_translate: kernel.name_str(conic, "isHyperbolaType_translate"),
        ellipse: kernel.name_str(conic, "ellipse"),
        ellipse_is_ellipse_type: kernel.name_str(conic, "ellipse_isEllipseType"),
        parabola: kernel.name_str(conic, "parabola"),
        parabola_is_parabola_type: kernel.name_str(conic, "parabola_isParabolaType"),
        hyperbola: kernel.name_str(conic, "hyperbola"),
        hyperbola_is_hyperbola_type: kernel.name_str(conic, "hyperbola_isHyperbolaType"),
        parabola_focal: kernel.name_str(conic, "parabolaFocal"),
        parabola_focal_is_parabola_type: kernel.name_str(conic, "parabolaFocal_isParabolaType"),
        parabola_focus_directrix: kernel.name_str(point, "parabola_focus_directrix"),
    }
}

// --- local term builders -----------------------------------------------------

fn conic_ty(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    d.kernel().const_(p.conic.conic, vec![])
}

fn cone(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    d.kernel().const_(p.creal.one, vec![])
}

fn ctwo(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    d.kernel().const_(p.two, vec![])
}

fn cfour(d: &mut IntDev<'_>, p: CPointPrelude) -> ExprId {
    d.kernel().const_(p.conic.four, vec![])
}

fn clt(d: &mut IntDev<'_>, p: CPointPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.creal.lt, &[x, y])
}

fn theorem(d: &mut IntDev<'_>, name: NameId, ty: ExprId, value: ExprId) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

fn definition(
    d: &mut IntDev<'_>,
    name: NameId,
    ty: ExprId,
    value: ExprId,
    height: u16,
) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(height),
    })
}

/// The six coefficient projections of a conic-valued expression.
fn coeffs(d: &mut IntDev<'_>, p: CPointPrelude, k: ExprId) -> [ExprId; 6] {
    let n = p.conic;
    [
        d.const_app(n.a, &[k]),
        d.const_app(n.b, &[k]),
        d.const_app(n.c, &[k]),
        d.const_app(n.d, &[k]),
        d.const_app(n.e, &[k]),
        d.const_app(n.f, &[k]),
    ]
}

/// The two coordinate projections of a point-valued expression.
fn coord(d: &mut IntDev<'_>, p: CPointPrelude, pt: ExprId) -> (ExprId, ExprId) {
    (d.const_app(p.x, &[pt]), d.const_app(p.y, &[pt]))
}

// --- the ring-normalizer mirrors ---------------------------------------------
//
// Every `r*` function below is the `RnExpr` twin of the *term* built beside
// it. The pairing is what the whole file rests on: `rn_ring_proof` proves an
// `Equiv` between the RENDERED mirrors, and the kernel accepts it at the
// stated type because rendering, delta and iota agree. Keeping the two in one
// place is deliberate — a mirror that drifts from its term is the one defect
// class the normalizer cannot report, because it would prove a true identity
// about the wrong expression.

fn ratom(e: ExprId) -> RnExpr {
    RnExpr::Atom(e)
}

/// `1 + 1`, the mirror of `CPoint.Scalar.two`.
fn rtwo() -> RnExpr {
    RnExpr::add(RnExpr::One, RnExpr::One)
}

/// `(1 + 1) + (1 + 1)`, the mirror of `CPoint.Scalar.four`.
fn rfour() -> RnExpr {
    RnExpr::add(rtwo(), rtwo())
}

fn rsub(a: RnExpr, b: RnExpr) -> RnExpr {
    RnExpr::add(a, RnExpr::neg(b))
}

/// `A x² + B x y + C y² + D x + E y + F`, the mirror of `Conic.eval`.
fn r_eval(k: &[RnExpr; 6], x: &RnExpr, y: &RnExpr) -> RnExpr {
    RnExpr::add(
        RnExpr::mul(k[0].clone(), RnExpr::mul(x.clone(), x.clone())),
        RnExpr::add(
            RnExpr::mul(k[1].clone(), RnExpr::mul(x.clone(), y.clone())),
            RnExpr::add(
                RnExpr::mul(k[2].clone(), RnExpr::mul(y.clone(), y.clone())),
                RnExpr::add(
                    RnExpr::mul(k[3].clone(), x.clone()),
                    RnExpr::add(RnExpr::mul(k[4].clone(), y.clone()), k[5].clone()),
                ),
            ),
        ),
    )
}

/// `B·B − four·(A·C)`, the mirror of `Conic.discriminant`.
fn r_discriminant(k: &[RnExpr; 6]) -> RnExpr {
    rsub(
        RnExpr::mul(k[1].clone(), k[1].clone()),
        RnExpr::mul(rfour(), RnExpr::mul(k[0].clone(), k[2].clone())),
    )
}

/// `(ax − bx)² + (ay − by)²`, the mirror of `CPoint.distSq`.
fn r_dist_sq(ax: &RnExpr, ay: &RnExpr, bx: &RnExpr, by: &RnExpr) -> RnExpr {
    let dx = rsub(ax.clone(), bx.clone());
    let dy = rsub(ay.clone(), by.clone());
    RnExpr::add(RnExpr::mul(dx.clone(), dx), RnExpr::mul(dy.clone(), dy))
}

// --- the carrier -------------------------------------------------------------

/// `CPoint.Conic`: a one-constructor inductive in `Type 0`,
/// `mk : CReal → CReal → CReal → CReal → CReal → CReal → Conic`.
pub(super) fn declare_conic_carrier(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let conic = conic_ty(d, p);
    let one = d.level_one();
    let type0 = d.kernel().sort(one);
    let mut mk_ty = conic;
    for _ in 0..6 {
        mk_ty = d.arrow(carrier, mk_ty);
    }
    d.kernel()
        .add_inductive(p.conic.conic, &[], 0, type0, &[(p.conic.mk, mk_ty)])
}

/// The six projections, all by large elimination out of the `Type`-valued
/// inductive — the same construction `declare_projections` uses for
/// `CPoint.x`/`CPoint.y`.
pub(super) fn declare_conic_projections(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let names = [
        p.conic.a, p.conic.b, p.conic.c, p.conic.d, p.conic.e, p.conic.f,
    ];
    for (index, name) in names.into_iter().enumerate() {
        let carrier = creal_ty(d, p);
        let conic = conic_ty(d, p);
        let one = d.level_one();
        let anon = d.anon_name();
        let motive = d.kernel().lam(anon, conic, carrier, BinderInfo::Default);
        let minor = {
            let fvs: Vec<u64> = (0..6).map(|_| d.fresh_fvar()).collect();
            let mut body = d.kernel().fvar(fvs[index]);
            for &fv in fvs.iter().rev() {
                body = d.lam_fv(fv, carrier, body);
            }
            body
        };
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let rec = d.kernel().const_(p.conic.rec, vec![one]);
        let body = d.apply(rec, &[motive, minor, t]);
        let value = d.lam_fv(t_fv, conic, body);
        let ty = d.arrow(conic, carrier);
        definition(d, name, ty, value, CONIC_HEIGHT)?;
    }
    Ok(())
}

// --- the scalar `4` and two order helpers ------------------------------------

/// `CPoint.Scalar.four := CReal.add CPoint.Scalar.two CPoint.Scalar.two`.
pub(super) fn declare_four(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let two = ctwo(d, p);
    let value = cadd(d, p, two, two);
    definition(d, p.conic.four, carrier, value, CONIC_HEIGHT + 1)
}

/// `lt zero (add u u)` from `lt zero u` — the doubling step
/// [`declare_zero_lt_four`] takes twice.
fn zero_lt_double(d: &mut IntDev<'_>, p: CPointPrelude, u: ExprId, h: ExprId) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);
    let le_zero_u = d.lemma(creal.le_of_lt, &[zero, u, h]);
    let stepped = d.lemma(
        creal.add_lt_add_of_le_of_lt,
        &[zero, u, zero, u, le_zero_u, h],
    ); // lt (add zero zero) (add u u)
    let zero_zero = cadd(d, p, zero, zero);
    let uu = cadd(d, p, u, u);
    let collapse = d.lemma(creal.add_zero, &[zero]); // Equiv (add zero zero) zero
    let refl_uu = refl(d, p, uu);
    d.lemma(
        creal.lt_congr,
        &[zero_zero, zero, uu, uu, collapse, refl_uu, stepped],
    )
}

/// `CPoint.Scalar.zero_lt_four : lt CReal.zero CPoint.Scalar.four`.
pub(super) fn declare_zero_lt_four(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let zero = czero(d, p);
    let one = cone(d, p);
    let two = ctwo(d, p);
    let four = cfour(d, p);
    let zero_lt_one = d.kernel().const_(p.creal.zero_lt_one, vec![]);
    let zero_lt_two = zero_lt_double(d, p, one, zero_lt_one);
    let value = zero_lt_double(d, p, two, zero_lt_two);
    let ty = clt(d, p, zero, four);
    theorem(d, p.conic.zero_lt_four, ty, value)
}

/// `CPoint.Scalar.neg_lt_zero_of_pos : ∀ x, lt zero x → lt (neg x) zero`.
///
/// `CReal` has no `neg_lt_neg`; this goes through
/// `add_lt_add_of_le_of_lt` at `(−x ≤ −x, 0 < x)`, giving
/// `−x + 0 < −x + x`, and then rewrites both sides with `add_zero` and
/// `add_neg`.
pub(super) fn declare_neg_lt_zero_of_pos(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let carrier = creal_ty(d, p);
    let zero = czero(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let hyp_ty = clt(d, p, zero, x);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let nx = cneg(d, p, x);
    let le_nx = d.lemma(creal.le_refl, &[nx]);
    let stepped = d.lemma(creal.add_lt_add_of_le_of_lt, &[nx, nx, zero, x, le_nx, h]);
    let nx_zero = cadd(d, p, nx, zero);
    let nx_x = cadd(d, p, nx, x);
    let az = d.lemma(creal.add_zero, &[nx]);
    let cancel = neg_add_cancel_proof(d, p, x);
    let value_body = d.lemma(
        creal.lt_congr,
        &[nx_zero, nx, nx_x, zero, az, cancel, stepped],
    );

    let concl = clt(d, p, nx, zero);
    let ty = {
        let inner = d.pi_fv(h_fv, hyp_ty, concl);
        d.pi_fv(x_fv, carrier, inner)
    };
    let value = {
        let inner = d.lam_fv(h_fv, hyp_ty, value_body);
        d.lam_fv(x_fv, carrier, inner)
    };
    theorem(d, p.conic.neg_lt_zero_of_pos, ty, value)
}

// --- eval, OnConic, the discriminant and the three predicates ----------------

/// The body of [`declare_eval`], reusable wherever the unfolded form is what
/// a proof has to talk about.
fn eval_body(d: &mut IntDev<'_>, p: CPointPrelude, k: ExprId, pt: ExprId) -> ExprId {
    let [ca, cb, cc, cd, ce, cf] = coeffs(d, p, k);
    let (px, py) = coord(d, p, pt);
    let xx = cmul(d, p, px, px);
    let xy = cmul(d, p, px, py);
    let yy = cmul(d, p, py, py);
    let t0 = cmul(d, p, ca, xx);
    let t1 = cmul(d, p, cb, xy);
    let t2 = cmul(d, p, cc, yy);
    let t3 = cmul(d, p, cd, px);
    let t4 = cmul(d, p, ce, py);
    let s4 = cadd(d, p, t4, cf);
    let s3 = cadd(d, p, t3, s4);
    let s2 = cadd(d, p, t2, s3);
    let s1 = cadd(d, p, t1, s2);
    cadd(d, p, t0, s1)
}

/// `CPoint.Conic.eval K P := A x² + B x y + C y² + D x + E y + F`.
pub(super) fn declare_eval(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let conic = conic_ty(d, p);
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);

    let body = eval_body(d, p, k, pp);
    let value = {
        let inner = d.lam_fv(pp_fv, point, body);
        d.lam_fv(k_fv, conic, inner)
    };
    let ty = {
        let inner = d.arrow(point, carrier);
        d.arrow(conic, inner)
    };
    definition(d, p.conic.eval, ty, value, CONIC_HEIGHT + 2)
}

/// `CPoint.OnConic K P := Equiv (Conic.eval K P) CReal.zero`.
pub(super) fn declare_on_conic(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let conic = conic_ty(d, p);
    let point = point_ty(d, p);
    let prop = d.kernel().sort_zero();

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);

    let ev = d.const_app(p.conic.eval, &[k, pp]);
    let zero = czero(d, p);
    let claim = equiv(d, p, ev, zero);
    let value = {
        let inner = d.lam_fv(pp_fv, point, claim);
        d.lam_fv(k_fv, conic, inner)
    };
    let ty = {
        let inner = d.arrow(point, prop);
        d.arrow(conic, inner)
    };
    definition(d, p.conic.on_conic, ty, value, CONIC_HEIGHT + 3)
}

fn discriminant_body(d: &mut IntDev<'_>, p: CPointPrelude, k: ExprId) -> ExprId {
    let [ca, cb, cc, _, _, _] = coeffs(d, p, k);
    let bb = cmul(d, p, cb, cb);
    let ac = cmul(d, p, ca, cc);
    let four = cfour(d, p);
    let four_ac = cmul(d, p, four, ac);
    let neg_four_ac = cneg(d, p, four_ac);
    cadd(d, p, bb, neg_four_ac)
}

/// `CPoint.Conic.discriminant K := B·B − four·(A·C)`.
pub(super) fn declare_discriminant(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let conic = conic_ty(d, p);
    let carrier = creal_ty(d, p);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = discriminant_body(d, p, k);
    let value = d.lam_fv(k_fv, conic, body);
    let ty = d.arrow(conic, carrier);
    definition(d, p.conic.discriminant, ty, value, CONIC_HEIGHT + 4)
}

/// Which of the three classifying predicates a helper is working with.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Ellipse,
    Parabola,
    Hyperbola,
}

/// The three classifying predicates, in one pass: `IsEllipseType` (`< 0`),
/// `IsParabolaType` (`~ 0`) and `IsHyperbolaType` (`> 0`).
pub(super) fn declare_type_predicates(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let rows = [
        (p.conic.is_ellipse_type, Kind::Ellipse, CONIC_HEIGHT + 5),
        (p.conic.is_parabola_type, Kind::Parabola, CONIC_HEIGHT + 6),
        (p.conic.is_hyperbola_type, Kind::Hyperbola, CONIC_HEIGHT + 7),
    ];
    for (name, kind, height) in rows {
        let conic = conic_ty(d, p);
        let prop = d.kernel().sort_zero();
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let disc = d.const_app(p.conic.discriminant, &[k]);
        let zero = czero(d, p);
        let claim = match kind {
            Kind::Ellipse => clt(d, p, disc, zero),
            Kind::Parabola => equiv(d, p, disc, zero),
            Kind::Hyperbola => clt(d, p, zero, disc),
        };
        let value = d.lam_fv(k_fv, conic, claim);
        let ty = d.arrow(conic, prop);
        definition(d, name, ty, value, height)?;
    }
    Ok(())
}

/// The predicate applied to a conic term.
fn pred_ty(d: &mut IntDev<'_>, p: CPointPrelude, kind: Kind, k: ExprId) -> ExprId {
    let name = match kind {
        Kind::Ellipse => p.conic.is_ellipse_type,
        Kind::Parabola => p.conic.is_parabola_type,
        Kind::Hyperbola => p.conic.is_hyperbola_type,
    };
    d.const_app(name, &[k])
}

// --- the three pairwise exclusions -------------------------------------------

/// `lt zero zero → False`, the contradiction all three exclusions end in.
fn refute_zero_lt_zero(d: &mut IntDev<'_>, p: CPointPrelude, h: ExprId) -> ExprId {
    let zero = czero(d, p);
    let irrefl = d.lemma(p.creal.lt_irrefl, &[zero]);
    d.apply(irrefl, &[h])
}

/// The three `∀ K, Pred₁ K → Pred₂ K → False` theorems. Each is a genuine
/// **discrimination** witness for the classifier: without them the three
/// predicates could all be the trivially-true one.
pub(super) fn declare_type_exclusions(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let rows = [
        (
            p.conic.not_ellipse_and_parabola,
            Kind::Ellipse,
            Kind::Parabola,
        ),
        (
            p.conic.not_ellipse_and_hyperbola,
            Kind::Ellipse,
            Kind::Hyperbola,
        ),
        (
            p.conic.not_parabola_and_hyperbola,
            Kind::Parabola,
            Kind::Hyperbola,
        ),
    ];
    for (name, first, second) in rows {
        let creal = p.creal;
        let conic = conic_ty(d, p);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let disc = d.const_app(p.conic.discriminant, &[k]);
        let zero = czero(d, p);

        let ty1 = pred_ty(d, p, first, k);
        let ty2 = pred_ty(d, p, second, k);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        // In every row the two hypotheses combine to `lt zero zero`.
        let zero_lt_zero = match (first, second) {
            // `lt disc zero` and `Equiv disc zero`: rewrite the left slot.
            (Kind::Ellipse, Kind::Parabola) => {
                let refl_zero = refl(d, p, zero);
                d.lemma(creal.lt_congr, &[disc, zero, zero, zero, h2, refl_zero, h1])
            }
            // `lt disc zero` and `lt zero disc`: compose.
            (Kind::Ellipse, Kind::Hyperbola) => {
                d.lemma(creal.lt_trans, &[zero, disc, zero, h2, h1])
            }
            // `Equiv disc zero` and `lt zero disc`: rewrite the right slot.
            _ => {
                let refl_zero = refl(d, p, zero);
                d.lemma(creal.lt_congr, &[zero, zero, disc, zero, refl_zero, h1, h2])
            }
        };
        let body = refute_zero_lt_zero(d, p, zero_lt_zero);

        let false_ty = d.false_ty();
        let ty = {
            let w0 = d.pi_fv(h2_fv, ty2, false_ty);
            let w1 = d.pi_fv(h1_fv, ty1, w0);
            d.pi_fv(k_fv, conic, w1)
        };
        let value = {
            let w0 = d.lam_fv(h2_fv, ty2, body);
            let w1 = d.lam_fv(h1_fv, ty1, w0);
            d.lam_fv(k_fv, conic, w1)
        };
        theorem(d, name, ty, value)?;
    }
    Ok(())
}

// --- transferring a type along an equality of discriminants ------------------

/// From `h : Equiv (discriminant K) (discriminant L)` and `hp : Pred K`,
/// build `Pred L`. The one place the classification's isometry-invariance is
/// actually proved; every `is*Type_rotate`/`_reflect`/`_translate` corollary
/// is this applied to the matching `discriminant_*` law.
fn transfer_pred(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    kind: Kind,
    disc_k: ExprId,
    disc_l: ExprId,
    h: ExprId,
    hp: ExprId,
) -> ExprId {
    let creal = p.creal;
    let zero = czero(d, p);
    match kind {
        Kind::Ellipse => {
            let refl_zero = refl(d, p, zero);
            d.lemma(
                creal.lt_congr,
                &[disc_k, disc_l, zero, zero, h, refl_zero, hp],
            )
        }
        Kind::Parabola => {
            let back = symm(d, p, disc_k, disc_l, h);
            d.lemma(creal.equiv_trans, &[disc_l, disc_k, zero, back, hp])
        }
        Kind::Hyperbola => {
            let refl_zero = refl(d, p, zero);
            d.lemma(
                creal.lt_congr,
                &[zero, zero, disc_k, disc_l, refl_zero, h, hp],
            )
        }
    }
}

/// The three `∀ K L, Equiv (discriminant K) (discriminant L) → Pred K →
/// Pred L` transfer theorems.
pub(super) fn declare_type_congrs(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let rows = [
        (p.conic.is_ellipse_type_congr, Kind::Ellipse),
        (p.conic.is_parabola_type_congr, Kind::Parabola),
        (p.conic.is_hyperbola_type_congr, Kind::Hyperbola),
    ];
    for (name, kind) in rows {
        let conic = conic_ty(d, p);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let disc_k = d.const_app(p.conic.discriminant, &[k]);
        let disc_l = d.const_app(p.conic.discriminant, &[l]);
        let hyp_ty = equiv(d, p, disc_k, disc_l);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let pred_k = pred_ty(d, p, kind, k);
        let pred_l = pred_ty(d, p, kind, l);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let body = transfer_pred(d, p, kind, disc_k, disc_l, h, hp);
        let ty = {
            let w0 = d.pi_fv(hp_fv, pred_k, pred_l);
            let w1 = d.pi_fv(h_fv, hyp_ty, w0);
            let w2 = d.pi_fv(l_fv, conic, w1);
            d.pi_fv(k_fv, conic, w2)
        };
        let value = {
            let w0 = d.lam_fv(hp_fv, pred_k, body);
            let w1 = d.lam_fv(h_fv, hyp_ty, w0);
            let w2 = d.lam_fv(l_fv, conic, w1);
            d.lam_fv(k_fv, conic, w2)
        };
        theorem(d, name, ty, value)?;
    }
    Ok(())
}

// --- turning a ring identity into an `Iff` of two `OnConic`s -----------------

/// `Iff left_ty right_ty` where `left_ty ≡ Equiv e1 zero`,
/// `right_ty ≡ Equiv e2 zero` and `ring : Equiv e1 e2`.
///
/// The shape every `onConic_*_iff` for an isometry has: the two sides are the
/// *same* polynomial rearranged, so the correspondence is one ring identity
/// transported through `Equiv.trans` in each direction. `left_ty`/`right_ty`
/// are passed as the `OnConic` applications rather than reconstructed, so the
/// rendered statement reads as geometry and not as a bare polynomial.
fn iff_of_equiv(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    left_ty: ExprId,
    e1: ExprId,
    right_ty: ExprId,
    e2: ExprId,
    ring: ExprId,
) -> (ExprId, ExprId) {
    let logic = p.creal.rat.int.logic;
    let zero = czero(d, p);
    let mp = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let back = symm(d, p, e1, e2, ring);
        let body = chain(d, p, e2, &[(e1, back), (zero, h)]);
        d.lam_fv(h_fv, left_ty, body)
    };
    let mpr = {
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let body = chain(d, p, e1, &[(e2, ring), (zero, hc)]);
        d.lam_fv(hc_fv, right_ty, body)
    };
    let iff_stmt = d.const_app(logic.iff, &[left_ty, right_ty]);
    let iff_proof = d.const_app(logic.iff_intro, &[left_ty, right_ty, mp, mpr]);
    (iff_stmt, iff_proof)
}

// --- circles are the `A = C, B = 0` case -------------------------------------

/// `CPoint.Conic.circle O r2 := Conic.mk 1 0 1 (−2·Ox) (−2·Oy)
/// (Ox² + Oy² − r2)`.
///
/// **`CPoint.OnCircle` is not recovered definitionally** — `OnCircle P O r2`
/// is `Equiv (distSq P O) r2`, a comparison of two quantities, while
/// `OnConic K P` is `Equiv (eval K P) zero`, one quantity against `0`. The
/// two are related by moving `r2` across the `Equiv`, which is
/// `add_right_cancel`-shaped work, not `Eq.refl`-shaped.
/// [`ConicNames::on_conic_circle_iff`] is that bridge, and it is an `Iff` for
/// exactly that reason.
pub(super) fn declare_circle(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let conic = conic_ty(d, p);

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let body = circle_body(d, p, po, r);
    let value = {
        let inner = d.lam_fv(r_fv, carrier, body);
        d.lam_fv(o_fv, point, inner)
    };
    let ty = {
        let inner = d.arrow(carrier, conic);
        d.arrow(point, inner)
    };
    definition(d, p.conic.circle, ty, value, CONIC_HEIGHT + 10)
}

fn circle_body(d: &mut IntDev<'_>, p: CPointPrelude, po: ExprId, r: ExprId) -> ExprId {
    let (ox, oy) = coord(d, p, po);
    let one = cone(d, p);
    let zero = czero(d, p);
    let two = ctwo(d, p);
    let two_ox = cmul(d, p, two, ox);
    let two_oy = cmul(d, p, two, oy);
    let cd = cneg(d, p, two_ox);
    let ce = cneg(d, p, two_oy);
    let ox2 = cmul(d, p, ox, ox);
    let oy2 = cmul(d, p, oy, oy);
    let neg_r = cneg(d, p, r);
    let tail = cadd(d, p, oy2, neg_r);
    let cf = cadd(d, p, ox2, tail);
    d.const_app(p.conic.mk, &[one, zero, one, cd, ce, cf])
}

/// The `RnExpr` mirror of [`circle_body`]'s six coefficients.
fn r_circle(ox: &RnExpr, oy: &RnExpr, r: &RnExpr) -> [RnExpr; 6] {
    [
        RnExpr::One,
        RnExpr::Zero,
        RnExpr::One,
        RnExpr::neg(RnExpr::mul(rtwo(), ox.clone())),
        RnExpr::neg(RnExpr::mul(rtwo(), oy.clone())),
        RnExpr::add(
            RnExpr::mul(ox.clone(), ox.clone()),
            RnExpr::add(RnExpr::mul(oy.clone(), oy.clone()), RnExpr::neg(r.clone())),
        ),
    ]
}

/// `CPoint.onConic_circle_iff : ∀ O r2 P,
/// Iff (OnConic (Conic.circle O r2) P) (OnCircle P O r2)`.
pub(super) fn declare_on_conic_circle_iff(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);
    let logic = p.creal.rat.int.logic;

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);

    let (ox, oy) = coord(d, p, po);
    let (px, py) = coord(d, p, pp);
    let circle = d.const_app(p.conic.circle, &[po, r]);
    let ev = d.const_app(p.conic.eval, &[circle, pp]);
    let dsq = d.const_app(p.dist_sq, &[pp, po]);

    let lhs_rn = r_eval(
        &r_circle(&ratom(ox), &ratom(oy), &ratom(r)),
        &ratom(px),
        &ratom(py),
    );
    let rhs_rn = rsub(
        r_dist_sq(&ratom(px), &ratom(py), &ratom(ox), &ratom(oy)),
        ratom(r),
    );
    let raw = rn_ring_proof(d, p.creal, &lhs_rn, &rhs_rn);
    let neg_r = cneg(d, p, r);
    let sub_term = cadd(d, p, dsq, neg_r);
    let ring = chain(d, p, ev, &[(sub_term, raw)]);

    let left_ty = d.const_app(p.conic.on_conic, &[circle, pp]);
    let right_ty = d.const_app(p.on_circle, &[pp, po, r]);
    let (mp, mpr) = sub_zero_iff_parts(d, p, left_ty, right_ty, ev, sub_term, dsq, r, ring);
    let iff_stmt = d.const_app(logic.iff, &[left_ty, right_ty]);
    let iff_proof = d.const_app(logic.iff_intro, &[left_ty, right_ty, mp, mpr]);

    let ty = {
        let w0 = d.pi_fv(pp_fv, point, iff_stmt);
        let w1 = d.pi_fv(r_fv, carrier, w0);
        d.pi_fv(o_fv, point, w1)
    };
    let value = {
        let w0 = d.lam_fv(pp_fv, point, iff_proof);
        let w1 = d.lam_fv(r_fv, carrier, w0);
        d.lam_fv(o_fv, point, w1)
    };
    theorem(d, p.conic.on_conic_circle_iff, ty, value)
}

/// `CPoint.Conic.circle_isEllipseType : ∀ O r2, IsEllipseType (circle O r2)`.
///
/// `discriminant (circle O r2) ~ −4` with no hypothesis at all, so this holds
/// for `r2 ≤ 0` too: "of ellipse type" is a statement about the quadratic
/// part `A = C = 1, B = 0`, not about the zero set being a nonempty curve.
pub(super) fn declare_circle_is_ellipse_type(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let creal = p.creal;
    let point = point_ty(d, p);
    let carrier = creal_ty(d, p);

    let o_fv = d.fresh_fvar();
    let po = d.kernel().fvar(o_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let (ox, oy) = coord(d, p, po);

    let circle = d.const_app(p.conic.circle, &[po, r]);
    let disc = d.const_app(p.conic.discriminant, &[circle]);
    let four = cfour(d, p);
    let neg_four = cneg(d, p, four);

    let lhs_rn = r_discriminant(&r_circle(&ratom(ox), &ratom(oy), &ratom(r)));
    let rhs_rn = RnExpr::neg(rfour());
    let raw = rn_ring_proof(d, p.creal, &lhs_rn, &rhs_rn);
    let ring = chain(d, p, disc, &[(neg_four, raw)]);
    let back = symm(d, p, disc, neg_four, ring);

    let zero_lt_four = d.kernel().const_(p.conic.zero_lt_four, vec![]);
    let neg_four_neg = d.lemma(p.conic.neg_lt_zero_of_pos, &[four, zero_lt_four]);
    let zero = czero(d, p);
    let refl_zero = refl(d, p, zero);
    let body = d.lemma(
        creal.lt_congr,
        &[neg_four, disc, zero, zero, back, refl_zero, neg_four_neg],
    );

    let concl = d.const_app(p.conic.is_ellipse_type, &[circle]);
    let ty = {
        let inner = d.pi_fv(r_fv, carrier, concl);
        d.pi_fv(o_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(r_fv, carrier, body);
        d.lam_fv(o_fv, point, inner)
    };
    theorem(d, p.conic.circle_is_ellipse_type, ty, value)
}

// --- the isometry action on coefficients -------------------------------------

/// Which of the two linear coefficient actions a helper is building.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Action {
    Rotate,
    Reflect,
}

/// The six coefficients of `Conic.rotate c s K` / `Conic.reflect c s K`, as
/// terms. Both maps share `A'`, `C'` and `D'`; they differ in the sign
/// pattern of `B'` and `E'`, which is the whole geometric content — a
/// reflection reverses orientation, and `B'` and `E'` are the two odd slots.
fn linear_action_body(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    action: Action,
    c: ExprId,
    s: ExprId,
    k: ExprId,
) -> ExprId {
    let [ca, cb, cc, cd, ce, cf] = coeffs(d, p, k);
    let two = ctwo(d, p);
    let ccc = cmul(d, p, c, c);
    let sss = cmul(d, p, s, s);
    let cs = cmul(d, p, c, s);

    // A' = A c² + B c s + C s²
    let a1 = {
        let t0 = cmul(d, p, ca, ccc);
        let t1 = cmul(d, p, cb, cs);
        let t2 = cmul(d, p, cc, sss);
        let tail = cadd(d, p, t1, t2);
        cadd(d, p, t0, tail)
    };
    // C' = A s² − B c s + C c²
    let c1 = {
        let t0 = cmul(d, p, ca, sss);
        let t1 = cmul(d, p, cb, cs);
        let nt1 = cneg(d, p, t1);
        let t2 = cmul(d, p, cc, ccc);
        let tail = cadd(d, p, nt1, t2);
        cadd(d, p, t0, tail)
    };
    // D' = D c + E s
    let d1 = {
        let t0 = cmul(d, p, cd, c);
        let t1 = cmul(d, p, ce, s);
        cadd(d, p, t0, t1)
    };
    let (b1, e1) = match action {
        // B' = 2 (C − A) c s + B (c² − s²);  E' = −(D s) + E c
        Action::Rotate => {
            let neg_a = cneg(d, p, ca);
            let diff = cadd(d, p, cc, neg_a);
            let scaled = cmul(d, p, diff, cs);
            let doubled = cmul(d, p, two, scaled);
            let neg_ss = cneg(d, p, sss);
            let cc_ss = cadd(d, p, ccc, neg_ss);
            let bpart = cmul(d, p, cb, cc_ss);
            let b1 = cadd(d, p, doubled, bpart);
            let ds = cmul(d, p, cd, s);
            let nds = cneg(d, p, ds);
            let ec = cmul(d, p, ce, c);
            let e1 = cadd(d, p, nds, ec);
            (b1, e1)
        }
        // B' = 2 (A − C) c s + B (s² − c²);  E' = D s − E c
        Action::Reflect => {
            let neg_c = cneg(d, p, cc);
            let diff = cadd(d, p, ca, neg_c);
            let scaled = cmul(d, p, diff, cs);
            let doubled = cmul(d, p, two, scaled);
            let neg_cc = cneg(d, p, ccc);
            let ss_cc = cadd(d, p, sss, neg_cc);
            let bpart = cmul(d, p, cb, ss_cc);
            let b1 = cadd(d, p, doubled, bpart);
            let ds = cmul(d, p, cd, s);
            let ec = cmul(d, p, ce, c);
            let nec = cneg(d, p, ec);
            let e1 = cadd(d, p, ds, nec);
            (b1, e1)
        }
    };
    d.const_app(p.conic.mk, &[a1, b1, c1, d1, e1, cf])
}

/// The `RnExpr` mirror of [`linear_action_body`].
fn r_linear_action(action: Action, c: &RnExpr, s: &RnExpr, k: &[RnExpr; 6]) -> [RnExpr; 6] {
    let ccc = RnExpr::mul(c.clone(), c.clone());
    let sss = RnExpr::mul(s.clone(), s.clone());
    let cs = RnExpr::mul(c.clone(), s.clone());
    let a1 = RnExpr::add(
        RnExpr::mul(k[0].clone(), ccc.clone()),
        RnExpr::add(
            RnExpr::mul(k[1].clone(), cs.clone()),
            RnExpr::mul(k[2].clone(), sss.clone()),
        ),
    );
    let c1 = RnExpr::add(
        RnExpr::mul(k[0].clone(), sss.clone()),
        RnExpr::add(
            RnExpr::neg(RnExpr::mul(k[1].clone(), cs.clone())),
            RnExpr::mul(k[2].clone(), ccc.clone()),
        ),
    );
    let d1 = RnExpr::add(
        RnExpr::mul(k[3].clone(), c.clone()),
        RnExpr::mul(k[4].clone(), s.clone()),
    );
    let (b1, e1) = match action {
        Action::Rotate => (
            RnExpr::add(
                RnExpr::mul(
                    rtwo(),
                    RnExpr::mul(
                        RnExpr::add(k[2].clone(), RnExpr::neg(k[0].clone())),
                        cs.clone(),
                    ),
                ),
                RnExpr::mul(k[1].clone(), RnExpr::add(ccc.clone(), RnExpr::neg(sss))),
            ),
            RnExpr::add(
                RnExpr::neg(RnExpr::mul(k[3].clone(), s.clone())),
                RnExpr::mul(k[4].clone(), c.clone()),
            ),
        ),
        Action::Reflect => (
            RnExpr::add(
                RnExpr::mul(
                    rtwo(),
                    RnExpr::mul(
                        RnExpr::add(k[0].clone(), RnExpr::neg(k[2].clone())),
                        cs.clone(),
                    ),
                ),
                RnExpr::mul(k[1].clone(), RnExpr::add(sss, RnExpr::neg(ccc))),
            ),
            RnExpr::add(
                RnExpr::mul(k[3].clone(), s.clone()),
                RnExpr::neg(RnExpr::mul(k[4].clone(), c.clone())),
            ),
        ),
    };
    [a1, b1, c1, d1, e1, k[5].clone()]
}

/// The image of `(x, y)` under `CPoint.rotate c s` / `CPoint.reflect c s`, as
/// `RnExpr`s — the mirror of `isometry.rs`'s own `rotate`/`reflect` bodies.
fn r_action_image(
    action: Action,
    c: &RnExpr,
    s: &RnExpr,
    x: &RnExpr,
    y: &RnExpr,
) -> (RnExpr, RnExpr) {
    match action {
        Action::Rotate => (
            RnExpr::add(
                RnExpr::mul(c.clone(), x.clone()),
                RnExpr::neg(RnExpr::mul(s.clone(), y.clone())),
            ),
            RnExpr::add(
                RnExpr::mul(s.clone(), x.clone()),
                RnExpr::mul(c.clone(), y.clone()),
            ),
        ),
        Action::Reflect => (
            RnExpr::add(
                RnExpr::mul(c.clone(), x.clone()),
                RnExpr::mul(s.clone(), y.clone()),
            ),
            RnExpr::add(
                RnExpr::mul(s.clone(), x.clone()),
                RnExpr::neg(RnExpr::mul(c.clone(), y.clone())),
            ),
        ),
    }
}

fn action_conic_name(p: CPointPrelude, action: Action) -> NameId {
    match action {
        Action::Rotate => p.conic.rotate,
        Action::Reflect => p.conic.reflect,
    }
}

fn action_point_name(p: CPointPrelude, action: Action) -> NameId {
    match action {
        Action::Rotate => p.rotate,
        Action::Reflect => p.reflect,
    }
}

/// `CPoint.Conic.rotate` and `CPoint.Conic.reflect`, both
/// `CReal → CReal → Conic → Conic`.
pub(super) fn declare_linear_actions(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    for (action, height) in [
        (Action::Rotate, CONIC_HEIGHT + 20),
        (Action::Reflect, CONIC_HEIGHT + 21),
    ] {
        let carrier = creal_ty(d, p);
        let conic = conic_ty(d, p);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let body = linear_action_body(d, p, action, c, s, k);
        let value = {
            let w0 = d.lam_fv(k_fv, conic, body);
            let w1 = d.lam_fv(s_fv, carrier, w0);
            d.lam_fv(c_fv, carrier, w1)
        };
        let ty = {
            let w0 = d.arrow(conic, conic);
            let w1 = d.arrow(carrier, w0);
            d.arrow(carrier, w1)
        };
        definition(d, action_conic_name(p, action), ty, value, height)?;
    }
    Ok(())
}

/// `∀ c s K P, Iff (OnConic (Conic.<act> c s K) P)
///                 (OnConic K (CPoint.<act> c s P))`, for both linear actions.
pub(super) fn declare_linear_action_iffs(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    for action in [Action::Rotate, Action::Reflect] {
        let carrier = creal_ty(d, p);
        let conic = conic_ty(d, p);
        let point = point_ty(d, p);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pp_fv = d.fresh_fvar();
        let pp = d.kernel().fvar(pp_fv);

        let [ca, cb, cc, cd, ce, cf] = coeffs(d, p, k);
        let (px, py) = coord(d, p, pp);
        let k_rn = [
            ratom(ca),
            ratom(cb),
            ratom(cc),
            ratom(cd),
            ratom(ce),
            ratom(cf),
        ];
        let c_rn = ratom(c);
        let s_rn = ratom(s);
        let x_rn = ratom(px);
        let y_rn = ratom(py);

        let acted = r_linear_action(action, &c_rn, &s_rn, &k_rn);
        let lhs_rn = r_eval(&acted, &x_rn, &y_rn);
        let (ix, iy) = r_action_image(action, &c_rn, &s_rn, &x_rn, &y_rn);
        let rhs_rn = r_eval(&k_rn, &ix, &iy);
        let raw = rn_ring_proof(d, p.creal, &lhs_rn, &rhs_rn);

        let acted_conic = d.const_app(action_conic_name(p, action), &[c, s, k]);
        let e1 = d.const_app(p.conic.eval, &[acted_conic, pp]);
        let map = d.const_app(action_point_name(p, action), &[c, s]);
        let image = d.kernel().app(map, pp);
        let e2 = d.const_app(p.conic.eval, &[k, image]);
        let ring = chain(d, p, e1, &[(e2, raw)]);

        let left_ty = d.const_app(p.conic.on_conic, &[acted_conic, pp]);
        let right_ty = d.const_app(p.conic.on_conic, &[k, image]);
        let (iff_stmt, iff_proof) = iff_of_equiv(d, p, left_ty, e1, right_ty, e2, ring);

        let ty = {
            let w0 = d.pi_fv(pp_fv, point, iff_stmt);
            let w1 = d.pi_fv(k_fv, conic, w0);
            let w2 = d.pi_fv(s_fv, carrier, w1);
            d.pi_fv(c_fv, carrier, w2)
        };
        let value = {
            let w0 = d.lam_fv(pp_fv, point, iff_proof);
            let w1 = d.lam_fv(k_fv, conic, w0);
            let w2 = d.lam_fv(s_fv, carrier, w1);
            d.lam_fv(c_fv, carrier, w2)
        };
        let name = match action {
            Action::Rotate => p.conic.on_conic_rotate_iff,
            Action::Reflect => p.conic.on_conic_reflect_iff,
        };
        theorem(d, name, ty, value)?;
    }
    Ok(())
}

/// `∀ c s K, Equiv (discriminant (Conic.<act> c s K))
///                 (mul (discriminant K) (mul (c·c + s·s) (c·c + s·s)))`.
///
/// **Unconditional**: no `c² + s² ~ 1` anywhere. The linear map `M` behind
/// each action has `det M = ±(c² + s²)`, and the discriminant is `−4 det Q`
/// for the quadratic-part matrix `Q`, which transforms as `MᵀQM` — so the
/// sign of `det M` cancels and only its square survives. That is why the
/// rotation and the reflection get the *same* factor, and why the identity
/// holds for the non-isometric `c² + s² ≠ 1` members of the family too.
pub(super) fn declare_discriminant_actions(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    for action in [Action::Rotate, Action::Reflect] {
        let carrier = creal_ty(d, p);
        let conic = conic_ty(d, p);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let [ca, cb, cc, cd, ce, cf] = coeffs(d, p, k);
        let k_rn = [
            ratom(ca),
            ratom(cb),
            ratom(cc),
            ratom(cd),
            ratom(ce),
            ratom(cf),
        ];
        let c_rn = ratom(c);
        let s_rn = ratom(s);
        let acted = r_linear_action(action, &c_rn, &s_rn, &k_rn);
        let gram_rn = RnExpr::add(
            RnExpr::mul(c_rn.clone(), c_rn.clone()),
            RnExpr::mul(s_rn.clone(), s_rn),
        );
        let lhs_rn = r_discriminant(&acted);
        let rhs_rn = RnExpr::mul(r_discriminant(&k_rn), RnExpr::mul(gram_rn.clone(), gram_rn));
        let raw = rn_ring_proof(d, p.creal, &lhs_rn, &rhs_rn);

        let acted_conic = d.const_app(action_conic_name(p, action), &[c, s, k]);
        let disc_acted = d.const_app(p.conic.discriminant, &[acted_conic]);
        let disc_k = d.const_app(p.conic.discriminant, &[k]);
        let ccc = cmul(d, p, c, c);
        let sss = cmul(d, p, s, s);
        let gram = cadd(d, p, ccc, sss);
        let gram_sq = cmul(d, p, gram, gram);
        let scaled = cmul(d, p, disc_k, gram_sq);
        let body = chain(d, p, disc_acted, &[(scaled, raw)]);

        let stmt = equiv(d, p, disc_acted, scaled);
        let ty = {
            let w0 = d.pi_fv(k_fv, conic, stmt);
            let w1 = d.pi_fv(s_fv, carrier, w0);
            d.pi_fv(c_fv, carrier, w1)
        };
        let value = {
            let w0 = d.lam_fv(k_fv, conic, body);
            let w1 = d.lam_fv(s_fv, carrier, w0);
            d.lam_fv(c_fv, carrier, w1)
        };
        let name = match action {
            Action::Rotate => p.conic.discriminant_rotate,
            Action::Reflect => p.conic.discriminant_reflect,
        };
        theorem(d, name, ty, value)?;
    }
    Ok(())
}

/// `∀ c s K, Equiv (add (mul c c) (mul s s)) one →
/// Equiv (discriminant (Conic.<act> c s K)) (discriminant K)`.
pub(super) fn declare_discriminant_action_units(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    for action in [Action::Rotate, Action::Reflect] {
        let creal = p.creal;
        let carrier = creal_ty(d, p);
        let conic = conic_ty(d, p);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let ccc = cmul(d, p, c, c);
        let sss = cmul(d, p, s, s);
        let gram = cadd(d, p, ccc, sss);
        let one = cone(d, p);
        let hyp_ty = equiv(d, p, gram, one);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);

        let acted_conic = d.const_app(action_conic_name(p, action), &[c, s, k]);
        let disc_acted = d.const_app(p.conic.discriminant, &[acted_conic]);
        let disc_k = d.const_app(p.conic.discriminant, &[k]);
        let gram_sq = cmul(d, p, gram, gram);
        let one_one = cmul(d, p, one, one);
        let scaled = cmul(d, p, disc_k, gram_sq);
        let scaled_one = cmul(d, p, disc_k, one_one);

        let base_name = match action {
            Action::Rotate => p.conic.discriminant_rotate,
            Action::Reflect => p.conic.discriminant_reflect,
        };
        let base = d.lemma(base_name, &[c, s, k]);
        let gram_congr = d.lemma(creal.mul_congr, &[gram, one, gram, one, h, h]);
        let refl_disc = refl(d, p, disc_k);
        let outer = d.lemma(
            creal.mul_congr,
            &[disc_k, disc_k, gram_sq, one_one, refl_disc, gram_congr],
        );
        let collapse = rn_ring_proof(
            d,
            p.creal,
            &RnExpr::mul(ratom(disc_k), RnExpr::mul(RnExpr::One, RnExpr::One)),
            &ratom(disc_k),
        );
        let body = chain(
            d,
            p,
            disc_acted,
            &[(scaled, base), (scaled_one, outer), (disc_k, collapse)],
        );

        let stmt = equiv(d, p, disc_acted, disc_k);
        let ty = {
            let w0 = d.pi_fv(k_fv, conic, stmt);
            let w1 = d.pi_fv(h_fv, hyp_ty, w0);
            let w2 = d.pi_fv(s_fv, carrier, w1);
            d.pi_fv(c_fv, carrier, w2)
        };
        let value = {
            let w0 = d.lam_fv(k_fv, conic, body);
            let w1 = d.lam_fv(h_fv, hyp_ty, w0);
            let w2 = d.lam_fv(s_fv, carrier, w1);
            d.lam_fv(c_fv, carrier, w2)
        };
        let name = match action {
            Action::Rotate => p.conic.discriminant_rotate_unit,
            Action::Reflect => p.conic.discriminant_reflect_unit,
        };
        theorem(d, name, ty, value)?;
    }
    Ok(())
}

// --- translation -------------------------------------------------------------

fn conic_translate_body(d: &mut IntDev<'_>, p: CPointPrelude, t: ExprId, k: ExprId) -> ExprId {
    let [ca, cb, cc, cd, ce, _] = coeffs(d, p, k);
    let (tx, ty) = coord(d, p, t);
    let two = ctwo(d, p);
    // D' = 2 A tx + (B ty + D)
    let d1 = {
        let atx = cmul(d, p, ca, tx);
        let two_atx = cmul(d, p, two, atx);
        let bty = cmul(d, p, cb, ty);
        let tail = cadd(d, p, bty, cd);
        cadd(d, p, two_atx, tail)
    };
    // E' = B tx + (2 C ty + E)
    let e1 = {
        let btx = cmul(d, p, cb, tx);
        let cty = cmul(d, p, cc, ty);
        let two_cty = cmul(d, p, two, cty);
        let tail = cadd(d, p, two_cty, ce);
        cadd(d, p, btx, tail)
    };
    let f1 = d.const_app(p.conic.eval, &[k, t]);
    d.const_app(p.conic.mk, &[ca, cb, cc, d1, e1, f1])
}

/// The `RnExpr` mirror of [`conic_translate_body`].
fn r_conic_translate(k: &[RnExpr; 6], tx: &RnExpr, ty: &RnExpr) -> [RnExpr; 6] {
    [
        k[0].clone(),
        k[1].clone(),
        k[2].clone(),
        RnExpr::add(
            RnExpr::mul(rtwo(), RnExpr::mul(k[0].clone(), tx.clone())),
            RnExpr::add(RnExpr::mul(k[1].clone(), ty.clone()), k[3].clone()),
        ),
        RnExpr::add(
            RnExpr::mul(k[1].clone(), tx.clone()),
            RnExpr::add(
                RnExpr::mul(rtwo(), RnExpr::mul(k[2].clone(), ty.clone())),
                k[4].clone(),
            ),
        ),
        r_eval(k, tx, ty),
    ]
}

/// `CPoint.Conic.translate T K` — the conic whose zero set is the
/// `CPoint.translate T` preimage of `K`'s. Its constant term is literally
/// `Conic.eval K T`, which is the cleanest statement of what a translation
/// does to a conic: it evaluates the old one at the shift.
pub(super) fn declare_conic_translate(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let conic = conic_ty(d, p);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let body = conic_translate_body(d, p, t, k);
    let value = {
        let inner = d.lam_fv(k_fv, conic, body);
        d.lam_fv(t_fv, point, inner)
    };
    let ty = {
        let inner = d.arrow(conic, conic);
        d.arrow(point, inner)
    };
    definition(d, p.conic.translate, ty, value, CONIC_HEIGHT + 22)
}

/// `CPoint.onConic_translate_iff : ∀ T K P,
/// Iff (OnConic (Conic.translate T K) P) (OnConic K (CPoint.translate T P))`.
pub(super) fn declare_on_conic_translate_iff(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let conic = conic_ty(d, p);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);

    let [ca, cb, cc, cd, ce, cf] = coeffs(d, p, k);
    let (tx, ty) = coord(d, p, t);
    let (px, py) = coord(d, p, pp);
    let k_rn = [
        ratom(ca),
        ratom(cb),
        ratom(cc),
        ratom(cd),
        ratom(ce),
        ratom(cf),
    ];
    let tx_rn = ratom(tx);
    let ty_rn = ratom(ty);
    let x_rn = ratom(px);
    let y_rn = ratom(py);

    let shifted = r_conic_translate(&k_rn, &tx_rn, &ty_rn);
    let lhs_rn = r_eval(&shifted, &x_rn, &y_rn);
    let rhs_rn = r_eval(
        &k_rn,
        &RnExpr::add(x_rn.clone(), tx_rn.clone()),
        &RnExpr::add(y_rn.clone(), ty_rn.clone()),
    );
    let raw = rn_ring_proof(d, p.creal, &lhs_rn, &rhs_rn);

    let shifted_conic = d.const_app(p.conic.translate, &[t, k]);
    let e1 = d.const_app(p.conic.eval, &[shifted_conic, pp]);
    let map = d.const_app(p.translate, &[t]);
    let image = d.kernel().app(map, pp);
    let e2 = d.const_app(p.conic.eval, &[k, image]);
    let ring = chain(d, p, e1, &[(e2, raw)]);

    let left_ty = d.const_app(p.conic.on_conic, &[shifted_conic, pp]);
    let right_ty = d.const_app(p.conic.on_conic, &[k, image]);
    let (iff_stmt, iff_proof) = iff_of_equiv(d, p, left_ty, e1, right_ty, e2, ring);

    let ty_expr = {
        let w0 = d.pi_fv(pp_fv, point, iff_stmt);
        let w1 = d.pi_fv(k_fv, conic, w0);
        d.pi_fv(t_fv, point, w1)
    };
    let value = {
        let w0 = d.lam_fv(pp_fv, point, iff_proof);
        let w1 = d.lam_fv(k_fv, conic, w0);
        d.lam_fv(t_fv, point, w1)
    };
    theorem(d, p.conic.on_conic_translate_iff, ty_expr, value)
}

/// `CPoint.Conic.discriminant_translate : ∀ T K,
/// Equiv (discriminant (Conic.translate T K)) (discriminant K)`.
///
/// The proof is `Equiv.refl` — a translation copies `A`, `B` and `C`
/// unchanged into the image conic, so the two discriminants are the same term
/// after one iota step. That is not a shortcut: it is the reason a
/// translation needs no hypothesis where a rotation needs `c² + s² ~ 1`.
pub(super) fn declare_discriminant_translate(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let point = point_ty(d, p);
    let conic = conic_ty(d, p);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let shifted_conic = d.const_app(p.conic.translate, &[t, k]);
    let disc_shifted = d.const_app(p.conic.discriminant, &[shifted_conic]);
    let disc_k = d.const_app(p.conic.discriminant, &[k]);
    let body = refl(d, p, disc_k);
    let stmt = equiv(d, p, disc_shifted, disc_k);
    let ty = {
        let inner = d.pi_fv(k_fv, conic, stmt);
        d.pi_fv(t_fv, point, inner)
    };
    let value = {
        let inner = d.lam_fv(k_fv, conic, body);
        d.lam_fv(t_fv, point, inner)
    };
    theorem(d, p.conic.discriminant_translate, ty, value)
}

// --- the nine invariance corollaries -----------------------------------------

/// `∀ c s K, Equiv (c·c + s·s) one → Pred K → Pred (Conic.<act> c s K)`, and
/// the translation's hypothesis-free
/// `∀ T K, Pred K → Pred (Conic.translate T K)`.
///
/// Each is [`transfer_pred`] applied to the matching `discriminant_*` law.
/// Nine of them, because the classification's isometry-invariance is a claim
/// about **each** predicate under **each** generator of the isometry group,
/// and stating one and asserting the rest in prose is exactly the shape of
/// claim this repository does not accept.
pub(super) fn declare_invariance_corollaries(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let linear = [
        (
            Action::Rotate,
            p.conic.discriminant_rotate_unit,
            [
                p.conic.is_ellipse_type_rotate,
                p.conic.is_parabola_type_rotate,
                p.conic.is_hyperbola_type_rotate,
            ],
        ),
        (
            Action::Reflect,
            p.conic.discriminant_reflect_unit,
            [
                p.conic.is_ellipse_type_reflect,
                p.conic.is_parabola_type_reflect,
                p.conic.is_hyperbola_type_reflect,
            ],
        ),
    ];
    let kinds = [Kind::Ellipse, Kind::Parabola, Kind::Hyperbola];

    for (action, disc_name, names) in linear {
        for (slot, kind) in kinds.into_iter().enumerate() {
            let carrier = creal_ty(d, p);
            let conic = conic_ty(d, p);
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let ccc = cmul(d, p, c, c);
            let sss = cmul(d, p, s, s);
            let gram = cadd(d, p, ccc, sss);
            let one = cone(d, p);
            let hyp_ty = equiv(d, p, gram, one);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);

            let acted_conic = d.const_app(action_conic_name(p, action), &[c, s, k]);
            let disc_acted = d.const_app(p.conic.discriminant, &[acted_conic]);
            let disc_k = d.const_app(p.conic.discriminant, &[k]);
            // `discriminant_*_unit`'s telescope is `∀ c s (h : c²+s² ~ 1) K`:
            // the HYPOTHESIS binds before the conic, so the conic is the
            // fourth argument, not the third.
            let forward = d.lemma(disc_name, &[c, s, h, k]);
            let back = symm(d, p, disc_acted, disc_k, forward);
            let pred_k = pred_ty(d, p, kind, k);
            let pred_acted = pred_ty(d, p, kind, acted_conic);
            let body = transfer_pred(d, p, kind, disc_k, disc_acted, back, hp);

            let ty = {
                let w0 = d.pi_fv(hp_fv, pred_k, pred_acted);
                let w1 = d.pi_fv(k_fv, conic, w0);
                let w2 = d.pi_fv(h_fv, hyp_ty, w1);
                let w3 = d.pi_fv(s_fv, carrier, w2);
                d.pi_fv(c_fv, carrier, w3)
            };
            let value = {
                let w0 = d.lam_fv(hp_fv, pred_k, body);
                let w1 = d.lam_fv(k_fv, conic, w0);
                let w2 = d.lam_fv(h_fv, hyp_ty, w1);
                let w3 = d.lam_fv(s_fv, carrier, w2);
                d.lam_fv(c_fv, carrier, w3)
            };
            theorem(d, names[slot], ty, value)?;
        }
    }

    let translate_names = [
        p.conic.is_ellipse_type_translate,
        p.conic.is_parabola_type_translate,
        p.conic.is_hyperbola_type_translate,
    ];
    for (slot, kind) in kinds.into_iter().enumerate() {
        let point = point_ty(d, p);
        let conic = conic_ty(d, p);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let shifted = d.const_app(p.conic.translate, &[t, k]);
        let disc_shifted = d.const_app(p.conic.discriminant, &[shifted]);
        let disc_k = d.const_app(p.conic.discriminant, &[k]);
        let forward = d.lemma(p.conic.discriminant_translate, &[t, k]);
        let back = symm(d, p, disc_shifted, disc_k, forward);
        let pred_k = pred_ty(d, p, kind, k);
        let pred_shifted = pred_ty(d, p, kind, shifted);
        let body = transfer_pred(d, p, kind, disc_k, disc_shifted, back, hp);

        let ty = {
            let w0 = d.pi_fv(hp_fv, pred_k, pred_shifted);
            let w1 = d.pi_fv(k_fv, conic, w0);
            d.pi_fv(t_fv, point, w1)
        };
        let value = {
            let w0 = d.lam_fv(hp_fv, pred_k, body);
            let w1 = d.lam_fv(k_fv, conic, w0);
            d.lam_fv(t_fv, point, w1)
        };
        theorem(d, translate_names[slot], ty, value)?;
    }
    Ok(())
}

// --- the standard forms ------------------------------------------------------

/// `CPoint.Conic.ellipse a b := b²x² + a²y² − a²b²`.
///
/// The textbook form is `x²/a² + y²/b² = 1`; multiplying through by `a²b²`
/// clears both denominators and is what keeps `CReal.inv` — which is
/// **partial**, defined only on a `PosBound`-witnessed positive — out of this
/// file. The two forms have the same zero set whenever `a` and `b` are
/// nonzero, which is exactly the hypothesis
/// [`ConicNames::ellipse_is_ellipse_type`] takes anyway.
pub(super) fn declare_ellipse(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let conic = conic_ty(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let body = quadric_body(d, p, a, b, false);
    let value = {
        let inner = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, inner)
    };
    let ty = {
        let inner = d.arrow(carrier, conic);
        d.arrow(carrier, inner)
    };
    definition(d, p.conic.ellipse, ty, value, CONIC_HEIGHT + 30)
}

/// `CPoint.Conic.hyperbola a b := b²x² − a²y² − a²b²`, i.e.
/// `x²/a² − y²/b² = 1` cleared of denominators.
pub(super) fn declare_hyperbola(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let conic = conic_ty(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let body = quadric_body(d, p, a, b, true);
    let value = {
        let inner = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, inner)
    };
    let ty = {
        let inner = d.arrow(carrier, conic);
        d.arrow(carrier, inner)
    };
    definition(d, p.conic.hyperbola, ty, value, CONIC_HEIGHT + 31)
}

/// The ellipse (`flip = false`) and the hyperbola (`flip = true`) differ in
/// exactly one sign, the `y²` coefficient — which is the whole classification.
fn quadric_body(d: &mut IntDev<'_>, p: CPointPrelude, a: ExprId, b: ExprId, flip: bool) -> ExprId {
    let zero = czero(d, p);
    let aa = cmul(d, p, a, a);
    let bb = cmul(d, p, b, b);
    let cc = if flip { cneg(d, p, aa) } else { aa };
    let aabb = cmul(d, p, aa, bb);
    let cf = cneg(d, p, aabb);
    d.const_app(p.conic.mk, &[bb, zero, cc, zero, zero, cf])
}

/// The `RnExpr` mirror of [`quadric_body`].
fn r_quadric(a: &RnExpr, b: &RnExpr, flip: bool) -> [RnExpr; 6] {
    let aa = RnExpr::mul(a.clone(), a.clone());
    let bb = RnExpr::mul(b.clone(), b.clone());
    let cc = if flip {
        RnExpr::neg(aa.clone())
    } else {
        aa.clone()
    };
    [
        bb.clone(),
        RnExpr::Zero,
        cc,
        RnExpr::Zero,
        RnExpr::Zero,
        RnExpr::neg(RnExpr::mul(aa, bb)),
    ]
}

/// `CPoint.Conic.parabola a := a x² − y`, the standard `y = a x²`.
pub(super) fn declare_parabola(d: &mut IntDev<'_>, p: CPointPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let conic = conic_ty(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let zero = czero(d, p);
    let one = cone(d, p);
    let neg_one = cneg(d, p, one);
    let body = d.const_app(p.conic.mk, &[a, zero, zero, zero, neg_one, zero]);
    let value = d.lam_fv(a_fv, carrier, body);
    let ty = d.arrow(carrier, conic);
    definition(d, p.conic.parabola, ty, value, CONIC_HEIGHT + 32)
}

/// `CPoint.Conic.parabolaFocal p := x² − four·(p·y)`, i.e. `x² = 4py`.
///
/// A second parameterisation of the same curve family, and the one
/// [`ConicNames::parabola_focus_directrix`] is stated over: `4p` is the
/// *latus rectum*, so the focus is `(0, p)` and the directrix `y = −p` with
/// **no division anywhere**. Reaching the same statement from
/// [`ConicNames::parabola`]'s `y = a x²` would need the focus `(0, 1/(4a))`,
/// hence `CReal.inv` and a nonzero-`a` witness.
pub(super) fn declare_parabola_focal(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let conic = conic_ty(d, p);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);

    let body = parabola_focal_body(d, p, pf);
    let value = d.lam_fv(pf_fv, carrier, body);
    let ty = d.arrow(carrier, conic);
    definition(d, p.conic.parabola_focal, ty, value, CONIC_HEIGHT + 33)
}

fn parabola_focal_body(d: &mut IntDev<'_>, p: CPointPrelude, pf: ExprId) -> ExprId {
    let zero = czero(d, p);
    let one = cone(d, p);
    let four = cfour(d, p);
    let four_p = cmul(d, p, four, pf);
    let ce = cneg(d, p, four_p);
    d.const_app(p.conic.mk, &[one, zero, zero, zero, ce, zero])
}

/// The `RnExpr` mirror of [`parabola_focal_body`].
fn r_parabola_focal(pf: &RnExpr) -> [RnExpr; 6] {
    [
        RnExpr::One,
        RnExpr::Zero,
        RnExpr::Zero,
        RnExpr::Zero,
        RnExpr::neg(RnExpr::mul(rfour(), pf.clone())),
        RnExpr::Zero,
    ]
}

/// `∀ a b, lt zero a → lt zero b → IsEllipseType (Conic.ellipse a b)` and its
/// hyperbolic twin.
///
/// `discriminant (ellipse a b) ~ −4·b²·a²` and
/// `discriminant (hyperbola a b) ~ +4·b²·a²`; the hypotheses are needed only
/// to make that quantity STRICTLY positive, which is where `CReal.mul_pos`
/// and [`ConicNames::zero_lt_four`] come in. At `a ~ 0` the ellipse
/// degenerates to the pair of lines `y = 0` and its discriminant is `~ 0`, so
/// the hypotheses are not decoration.
pub(super) fn declare_quadric_type_theorems(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    for flip in [false, true] {
        let creal = p.creal;
        let carrier = creal_ty(d, p);
        let zero = czero(d, p);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let ha_ty = clt(d, p, zero, a);
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);
        let hb_ty = clt(d, p, zero, b);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);

        let name = if flip {
            p.conic.hyperbola
        } else {
            p.conic.ellipse
        };
        let shape = d.const_app(name, &[a, b]);
        let disc = d.const_app(p.conic.discriminant, &[shape]);

        // `magnitude := four · (b·b · (a·a))`, positive under both hypotheses.
        let aa = cmul(d, p, a, a);
        let bb = cmul(d, p, b, b);
        let bbaa = cmul(d, p, bb, aa);
        let four = cfour(d, p);
        let magnitude = cmul(d, p, four, bbaa);

        let a_rn = ratom(a);
        let b_rn = ratom(b);
        let lhs_rn = r_discriminant(&r_quadric(&a_rn, &b_rn, flip));
        let magnitude_rn = RnExpr::mul(
            rfour(),
            RnExpr::mul(
                RnExpr::mul(b_rn.clone(), b_rn),
                RnExpr::mul(a_rn.clone(), a_rn),
            ),
        );

        let pos_aa = d.lemma(creal.mul_pos, &[a, a, ha, ha]);
        let pos_bb = d.lemma(creal.mul_pos, &[b, b, hb, hb]);
        let pos_bbaa = d.lemma(creal.mul_pos, &[bb, aa, pos_bb, pos_aa]);
        let zero_lt_four = d.kernel().const_(p.conic.zero_lt_four, vec![]);
        let pos_magnitude = d.lemma(creal.mul_pos, &[four, bbaa, zero_lt_four, pos_bbaa]);
        let refl_zero = refl(d, p, zero);

        let (body, kind) = if flip {
            // `discriminant ~ magnitude`, so `0 < discriminant`.
            let raw = rn_ring_proof(d, p.creal, &lhs_rn, &magnitude_rn);
            let ring = chain(d, p, disc, &[(magnitude, raw)]);
            let back = symm(d, p, disc, magnitude, ring);
            let body = d.lemma(
                creal.lt_congr,
                &[zero, zero, magnitude, disc, refl_zero, back, pos_magnitude],
            );
            (body, Kind::Hyperbola)
        } else {
            // `discriminant ~ −magnitude`, so `discriminant < 0`.
            let neg_magnitude = cneg(d, p, magnitude);
            let raw = rn_ring_proof(d, p.creal, &lhs_rn, &RnExpr::neg(magnitude_rn));
            let ring = chain(d, p, disc, &[(neg_magnitude, raw)]);
            let back = symm(d, p, disc, neg_magnitude, ring);
            let negative = d.lemma(p.conic.neg_lt_zero_of_pos, &[magnitude, pos_magnitude]);
            let body = d.lemma(
                creal.lt_congr,
                &[neg_magnitude, disc, zero, zero, back, refl_zero, negative],
            );
            (body, Kind::Ellipse)
        };

        let concl = pred_ty(d, p, kind, shape);
        let ty = {
            let w0 = d.pi_fv(hb_fv, hb_ty, concl);
            let w1 = d.pi_fv(ha_fv, ha_ty, w0);
            let w2 = d.pi_fv(b_fv, carrier, w1);
            d.pi_fv(a_fv, carrier, w2)
        };
        let value = {
            let w0 = d.lam_fv(hb_fv, hb_ty, body);
            let w1 = d.lam_fv(ha_fv, ha_ty, w0);
            let w2 = d.lam_fv(b_fv, carrier, w1);
            d.lam_fv(a_fv, carrier, w2)
        };
        let theorem_name = if flip {
            p.conic.hyperbola_is_hyperbola_type
        } else {
            p.conic.ellipse_is_ellipse_type
        };
        theorem(d, theorem_name, ty, value)?;
    }
    Ok(())
}

/// `∀ a, IsParabolaType (Conic.parabola a)` and
/// `∀ p, IsParabolaType (Conic.parabolaFocal p)`.
///
/// Both take **no** hypothesis: `B = C = 0` in each, so `B² − 4AC` is
/// identically `0` whatever `A` is. That includes the degenerate members —
/// `Conic.parabola 0` is the line `y = 0` — which is the honest content of
/// "of parabola type": it is a statement about the quadratic part, and the
/// degenerate line really does sit in the parabolic (`discriminant ~ 0`)
/// class.
pub(super) fn declare_parabola_type_theorems(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    for focal in [false, true] {
        let carrier = creal_ty(d, p);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);

        let (shape, lhs_rn) = if focal {
            let shape = d.const_app(p.conic.parabola_focal, &[a]);
            let rn = r_discriminant(&r_parabola_focal(&ratom(a)));
            (shape, rn)
        } else {
            let shape = d.const_app(p.conic.parabola, &[a]);
            let rn = r_discriminant(&[
                ratom(a),
                RnExpr::Zero,
                RnExpr::Zero,
                RnExpr::Zero,
                RnExpr::neg(RnExpr::One),
                RnExpr::Zero,
            ]);
            (shape, rn)
        };
        let disc = d.const_app(p.conic.discriminant, &[shape]);
        let zero = czero(d, p);
        let raw = rn_ring_proof(d, p.creal, &lhs_rn, &RnExpr::Zero);
        let body = chain(d, p, disc, &[(zero, raw)]);

        let concl = pred_ty(d, p, Kind::Parabola, shape);
        let ty = d.pi_fv(a_fv, carrier, concl);
        let value = d.lam_fv(a_fv, carrier, body);
        let name = if focal {
            p.conic.parabola_focal_is_parabola_type
        } else {
            p.conic.parabola_is_parabola_type
        };
        theorem(d, name, ty, value)?;
    }
    Ok(())
}

/// **The focus–directrix property of the parabola `x² = 4py`.**
///
/// `∀ p P, Iff (OnConic (Conic.parabolaFocal p) P)
///             (Equiv (distSq P (CPoint.mk 0 p)) ((P.y + p)·(P.y + p)))`.
///
/// The usual statement is `dist P focus = dist P directrix`, and both sides
/// are square roots. Squaring both is not a weakening here: `distSq` is the
/// squared distance to the focus `(0, p)` by definition, and `(y + p)²` is
/// the squared distance from `P` to the horizontal line `y = −p` (the
/// horizontal displacement is zero, so the perpendicular distance is
/// `|y − (−p)|`, whose square is `(y + p)²` with no absolute value left to
/// interpret). So the statement is the focus–directrix property verbatim,
/// with `CReal.sqrt` never mentioned — which matters because `sqrt` on a
/// constructive real is a limit construction, not an operation the ring
/// normalizer can see through.
pub(super) fn declare_parabola_focus_directrix(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let point = point_ty(d, p);
    let logic = p.creal.rat.int.logic;

    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let pp_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let (px, py) = coord(d, p, pp);

    let shape = d.const_app(p.conic.parabola_focal, &[pf]);
    let ev = d.const_app(p.conic.eval, &[shape, pp]);
    let zero = czero(d, p);
    let focus = d.const_app(p.mk, &[zero, pf]);
    let dsq = d.const_app(p.dist_sq, &[pp, focus]);
    let y_plus_p = cadd(d, p, py, pf);
    let directrix_sq = cmul(d, p, y_plus_p, y_plus_p);

    let px_rn = ratom(px);
    let py_rn = ratom(py);
    let pf_rn = ratom(pf);
    let lhs_rn = r_eval(&r_parabola_focal(&pf_rn), &px_rn, &py_rn);
    let rhs_rn = rsub(
        r_dist_sq(&px_rn, &py_rn, &RnExpr::Zero, &pf_rn),
        RnExpr::mul(
            RnExpr::add(py_rn.clone(), pf_rn.clone()),
            RnExpr::add(py_rn, pf_rn),
        ),
    );
    let raw = rn_ring_proof(d, p.creal, &lhs_rn, &rhs_rn);
    let neg_dir = cneg(d, p, directrix_sq);
    let sub_term = cadd(d, p, dsq, neg_dir);
    let ring = chain(d, p, ev, &[(sub_term, raw)]);

    let left_ty = d.const_app(p.conic.on_conic, &[shape, pp]);
    let right_ty = equiv(d, p, dsq, directrix_sq);
    let (mp, mpr) = sub_zero_iff_parts(
        d,
        p,
        left_ty,
        right_ty,
        ev,
        sub_term,
        dsq,
        directrix_sq,
        ring,
    );
    let iff_stmt = d.const_app(logic.iff, &[left_ty, right_ty]);
    let iff_proof = d.const_app(logic.iff_intro, &[left_ty, right_ty, mp, mpr]);

    let ty = {
        let inner = d.pi_fv(pp_fv, point, iff_stmt);
        d.pi_fv(pf_fv, carrier, inner)
    };
    let value = {
        let inner = d.lam_fv(pp_fv, point, iff_proof);
        d.lam_fv(pf_fv, carrier, inner)
    };
    theorem(d, p.conic.parabola_focus_directrix, ty, value)
}

/// The two halves of an `Iff` between `Equiv e zero` (as `left_ty`) and
/// `Equiv u v` (as `right_ty`), given `ring : Equiv e (add u (neg v))`.
///
/// Shared by [`declare_on_conic_circle_iff`] and
/// [`declare_parabola_focus_directrix`], which are the same argument at
/// different polynomials: a conic's defining expression IS `u − v` for the
/// two squared quantities the geometric statement compares.
fn sub_zero_iff_parts(
    d: &mut IntDev<'_>,
    p: CPointPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    e: ExprId,
    sub_term: ExprId,
    u: ExprId,
    v: ExprId,
    ring: ExprId,
) -> (ExprId, ExprId) {
    let zero = czero(d, p);
    let mp = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let back = symm(d, p, e, sub_term, ring);
        let sub_zero = chain(d, p, sub_term, &[(e, back), (zero, h)]);
        let body = equiv_of_sub_eq_zero(d, p, u, v, sub_zero);
        d.lam_fv(h_fv, left_ty, body)
    };
    let mpr = {
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let sub_zero = sub_eq_zero_of_equiv(d, p, u, v, hc);
        let body = chain(d, p, e, &[(sub_term, ring), (zero, sub_zero)]);
        d.lam_fv(hc_fv, right_ty, body)
    };
    (mp, mpr)
}
