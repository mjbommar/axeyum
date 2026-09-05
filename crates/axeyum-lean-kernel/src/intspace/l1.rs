//! `IntSpace.l1Dist` and `IntSpace.bundledL1` — **L¹ is a metric space**
//! (roadmap W3-1 follow-on, ADR-1625).
//!
//! `intspace/bundled.rs` established that a function and its integrability
//! datum are one object (`IntSpace.Bundled S = Sigma S.carrier S.Integrable`)
//! and that `IntSpace.bundledIntegral` is therefore a **total** function on
//! that carrier — the shape `Metric.dist` demands. It then said, in its own
//! module doc, that `IntSpace.bundledDist b₁ b₂ := |∫b₁ − ∫b₂|` **is not L¹**,
//! and named what was missing: an absolute value on the carrier, and an
//! integrability witness for it.
//!
//! This file supplies both — as **hypotheses, not fields and not axioms** —
//! and builds the metric.
//!
//! ## The L¹ data, and why it is seven arguments rather than eight fields
//!
//! ADR-1612 chose not to put closure fields on the record ("a stronger axiom
//! than the existing theorems prove"). That judgement was about *closure*; the
//! measurement this file makes is narrower and sharper. What the L¹ seminorm
//! actually needs is not `|·|` and not a lattice, but **one binary operation
//! on the carrier that behaves like a pointwise distance**:
//!
//! ```text
//! fdist : S.carrier → S.carrier → S.carrier          -- "the function t ↦ |f t − g t|"
//! hI    : ∀ f g, S.Integrable f → S.Integrable g → S.Integrable (fdist f g)
//! hAdd  : ∀ f g, S.Integrable f → S.Integrable g → S.Integrable (S.fadd f g)
//! hNN   : ∀ f g, S.fle (S.fconst CReal.zero) (fdist f g)
//! hSelf : ∀ f,   S.fle (fdist f f) (S.fconst CReal.zero)
//! hComm : ∀ f g, S.fle (fdist f g) (fdist g f)
//! hTri  : ∀ f g h, S.fle (fdist f h) (S.fadd (fdist f g) (fdist g h))
//! ```
//!
//! Each of the last four is **exactly one metric law's source**, and the map is
//! one-to-one: `hNN → distNonneg`, `hSelf → distSelf`, `hComm → distComm`,
//! `hTri → distTriangle`. Nothing here asks that `fdist f g` be `|f − g|`, that
//! the carrier be closed under `|·|`, or that `fdist` relate to `fadd` and
//! `fscale` at all. Fusing `|·|` with subtraction into one operation is what
//! removes the whole lattice question from the statement: a *pointwise metric
//! on the carrier, integrated, is an L¹ metric on the bundles*.
//!
//! That is strictly weaker than the eight record fields the obvious design
//! wants, it needs no change to a sixteen-field record three instances already
//! fill, and — measured below — every instance witness is an existing lemma
//! applied verbatim.
//!
//! ## The equivalence IS the distance being zero
//!
//! `Metric` carries its own setoid (fields 1–4) and then demands
//! `distSelf : equiv a b → dist a b ~ 0` and `distEquiv : dist a b ~ 0 →
//! equiv a b`. Constructively, "equal almost everywhere" for L¹ is
//! `∫|f − g| ~ 0` and nothing else, so this file *defines*
//!
//! ```text
//! IntSpace.L1Equiv S fdist hI b₁ b₂ := CReal.Equiv (IntSpace.l1Dist S fdist hI b₁ b₂) CReal.zero
//! ```
//!
//! and both of those two fields are then the identity function `fun a b h => h`.
//! The content does not disappear — it moves into `equivRefl`, `equivSymm`,
//! `equivTrans` and `distCongr`, which are now the theorems that have to be
//! proved, and which are proved here from the triangle inequality alone.
//! `distCongr` is the only one that is not a two-line rearrangement: it is the
//! quadrilateral estimate `d(a,b) ≤ d(a,a') + d(a',b') + d(b',b)` run in both
//! directions, factored through [`declare_l1_dist_le_of_equiv`] so the second
//! direction is the first one applied to the symmetric hypotheses.
//!
//! ## What is declared
//!
//! | name | type |
//! | --- | --- |
//! | `IntSpace.l1Dist` | `Π S fdist hI, S.Bundled → S.Bundled → CReal` — **the L¹ seminorm, total** |
//! | `IntSpace.L1Equiv` | `Π S fdist hI, S.Bundled → S.Bundled → Prop` |
//! | `IntSpace.l1Dist_bundle` | `∀ S fdist hI f g hf hg, l1Dist (bundle f hf) (bundle g hg) = S.integral (fdist f g) (hI f g hf hg)` |
//! | `IntSpace.l1Dist_nonneg` | `∀ …, CReal.le CReal.zero (l1Dist a b)` |
//! | `IntSpace.l1Dist_self` | `∀ …, CReal.Equiv (l1Dist a a) CReal.zero` |
//! | `IntSpace.l1Dist_comm` | `∀ …, CReal.Equiv (l1Dist a b) (l1Dist b a)` |
//! | `IntSpace.l1Dist_triangle` | `∀ …, CReal.le (l1Dist a c) (CReal.add (l1Dist a b) (l1Dist b c))` |
//! | `IntSpace.l1Equiv_refl` | `∀ …, L1Equiv a a` |
//! | `IntSpace.l1Equiv_symm` | `∀ …, L1Equiv a b → L1Equiv b a` |
//! | `IntSpace.l1Equiv_trans` | `∀ …, L1Equiv a b → L1Equiv b c → L1Equiv a c` |
//! | `IntSpace.l1Dist_le_of_equiv` | `∀ …, L1Equiv a a' → L1Equiv b b' → CReal.le (l1Dist a b) (l1Dist a' b')` |
//! | `IntSpace.l1Dist_congr` | `∀ …, L1Equiv a a' → L1Equiv b b' → CReal.Equiv (l1Dist a b) (l1Dist a' b')` |
//! | `IntSpace.bundledL1` | `Π S fdist hI hAdd hNN hSelf hComm hTri, Metric` — **the metric space** |
//! | `IntSpace.bundledL1_carrier` | `∀ …, Metric.carrier (bundledL1 …) = IntSpace.Bundled S` |
//! | `IntSpace.bundledL1_dist` | `∀ … a b, Metric.dist (bundledL1 …) a b = l1Dist S fdist hI a b` |
//!
//! The last two are `Eq`, closed by `Eq.refl`: they are the evaluation tests
//! for the two `Definition`s, taken at **symbolic** arguments (an arbitrary
//! `S`, an arbitrary `fdist`, arbitrary bundles), which is the only place a
//! probe on this carrier can be non-vacuous — there is no concrete `CReal` to
//! compute with.
//!
//! ## Why it is called `IntSpace.bundledL1` and not `Metric.bundledL1`
//!
//! `metric/metric_tests.rs` and `intspace/intspace_tests.rs` each check that
//! every live declaration in their prelude is on a hand-maintained list, and
//! each does it with a **name-prefix filter**. A `Metric.*` name declared by
//! the `IntSpace` prelude falls between them: `metric::`'s kernel never sees
//! it, and `intspace::`'s filter (`shown.starts_with("IntSpace")`) does not
//! match it. It would be watched by nothing. Declaring it inside `IntSpace`
//! puts it back under a filter that actually runs. See ADR-1625.

// Long, straight-line term construction; same suppression and same reason as
// the rest of this module.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::{
    FADD, FCONST, FLE, INTEGRABLE, INTEGRAL, INTEGRAL_ADD, INTEGRAL_LE, IntSpacePrelude,
    definition, field, generic_space, radd, req, rle, rzero, theorem,
};
use crate::KernelError;
use crate::MetricPrelude;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;
use crate::{Kernel, LevelId};

/// The interned names this file owns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct L1Names {
    /// `IntSpace.l1Dist : Π S (fdist : S.carrier → S.carrier → S.carrier)
    /// (hI : ∀ f g, S.Integrable f → S.Integrable g → S.Integrable (fdist f g)),
    /// S.Bundled → S.Bundled → CReal` — **the L¹ seminorm**, `∫ fdist f g`,
    /// total on the bundled carrier.
    pub l1_dist: NameId,
    /// `IntSpace.L1Equiv : Π S fdist hI, S.Bundled → S.Bundled → Prop` —
    /// `CReal.Equiv (l1Dist …) CReal.zero`, constructively "equal almost
    /// everywhere".
    pub l1_equiv: NameId,
    /// `IntSpace.l1Dist_bundle : ∀ S fdist hI f g hf hg,
    /// Eq CReal (l1Dist S fdist hI (S.bundle f hf) (S.bundle g hg))
    ///          (S.integral (fdist f g) (hI f g hf hg))` — `Eq.refl`.
    pub l1_dist_bundle: NameId,
    /// `IntSpace.l1Dist_nonneg : ∀ …, CReal.le CReal.zero (l1Dist … a b)`.
    pub l1_dist_nonneg: NameId,
    /// `IntSpace.l1Dist_self : ∀ …, CReal.Equiv (l1Dist … a a) CReal.zero`.
    pub l1_dist_self: NameId,
    /// `IntSpace.l1Dist_comm : ∀ …, CReal.Equiv (l1Dist … a b) (l1Dist … b a)`.
    pub l1_dist_comm: NameId,
    /// `IntSpace.l1Dist_triangle : ∀ …, CReal.le (l1Dist … a c)
    /// (CReal.add (l1Dist … a b) (l1Dist … b c))`.
    pub l1_dist_triangle: NameId,
    /// `IntSpace.l1Equiv_refl : ∀ …, L1Equiv … a a`.
    pub l1_equiv_refl: NameId,
    /// `IntSpace.l1Equiv_symm : ∀ …, L1Equiv … a b → L1Equiv … b a`.
    pub l1_equiv_symm: NameId,
    /// `IntSpace.l1Equiv_trans : ∀ …, L1Equiv … a b → L1Equiv … b c →
    /// L1Equiv … a c`.
    pub l1_equiv_trans: NameId,
    /// `IntSpace.l1Dist_le_of_equiv : ∀ …, L1Equiv … a a' → L1Equiv … b b' →
    /// CReal.le (l1Dist … a b) (l1Dist … a' b')` — one direction of the
    /// quadrilateral estimate.
    pub l1_dist_le_of_equiv: NameId,
    /// `IntSpace.l1Dist_congr : ∀ …, L1Equiv … a a' → L1Equiv … b b' →
    /// CReal.Equiv (l1Dist … a b) (l1Dist … a' b')`.
    pub l1_dist_congr: NameId,
    /// `IntSpace.bundledL1 : Π S fdist hI hAdd hNN hSelf hComm hTri, Metric` —
    /// **the L¹ metric space**.
    pub bundled_l1: NameId,
    /// `IntSpace.bundledL1_carrier : ∀ …, Eq (Sort 1)
    /// (Metric.carrier (bundledL1 …)) (IntSpace.Bundled S)` — `Eq.refl`.
    pub bundled_l1_carrier: NameId,
    /// `IntSpace.bundledL1_dist : ∀ … a b, Eq CReal
    /// (Metric.dist (bundledL1 …) a b) (l1Dist S fdist hI a b)` — `Eq.refl`.
    pub bundled_l1_dist: NameId,
    /// `IntSpace.crealIntervalL1 : Π (a b : CReal), CReal.le a b → Metric` —
    /// **L¹[a,b]**: the Riemann-integrable functions on `[a,b]`, bundled with
    /// their moduli, under `‖F − G‖₁ = ∫ₐᵇ |F − G|`.
    pub creal_interval_l1: NameId,
    /// `IntSpace.crealIntervalL1_dist : ∀ a b hab F G hF hG, Eq CReal
    /// (Metric.dist (crealIntervalL1 a b hab) (bundle F hF) (bundle G hG))
    /// (CReal.integral (fun t => CReal.abs (CReal.add (F t) (CReal.neg (G t))))
    ///                 a b hab …)` — `Eq.refl`.
    pub creal_interval_l1_dist: NameId,
    /// `IntSpace.crealFiniteL1 : Nat → Metric` — **ℓ¹ on a finite index set**,
    /// which over `IntSpace.crealFinite` is `E|X − Y|` for counting measure.
    pub creal_finite_l1: NameId,
    /// `IntSpace.crealFiniteL1_dist : ∀ m f g, Eq CReal
    /// (Metric.dist (crealFiniteL1 m) (bundle f Triv.mk) (bundle g Triv.mk))
    /// (CReal.sumRange (fun i => CReal.abs (CReal.add (f i) (CReal.neg (g i))))
    ///                 (Nat.succ m))` — `Eq.refl`.
    pub creal_finite_l1_dist: NameId,
}

impl L1Names {
    /// Every name this file owns, for the inventory tests. Derived from the
    /// struct's own fields, never from a literal list somewhere else.
    pub fn all(&self) -> Vec<(&'static str, NameId)> {
        vec![
            ("IntSpace.l1Dist", self.l1_dist),
            ("IntSpace.L1Equiv", self.l1_equiv),
            ("IntSpace.l1Dist_bundle", self.l1_dist_bundle),
            ("IntSpace.l1Dist_nonneg", self.l1_dist_nonneg),
            ("IntSpace.l1Dist_self", self.l1_dist_self),
            ("IntSpace.l1Dist_comm", self.l1_dist_comm),
            ("IntSpace.l1Dist_triangle", self.l1_dist_triangle),
            ("IntSpace.l1Equiv_refl", self.l1_equiv_refl),
            ("IntSpace.l1Equiv_symm", self.l1_equiv_symm),
            ("IntSpace.l1Equiv_trans", self.l1_equiv_trans),
            ("IntSpace.l1Dist_le_of_equiv", self.l1_dist_le_of_equiv),
            ("IntSpace.l1Dist_congr", self.l1_dist_congr),
            ("IntSpace.bundledL1", self.bundled_l1),
            ("IntSpace.bundledL1_carrier", self.bundled_l1_carrier),
            ("IntSpace.bundledL1_dist", self.bundled_l1_dist),
            ("IntSpace.crealIntervalL1", self.creal_interval_l1),
            ("IntSpace.crealIntervalL1_dist", self.creal_interval_l1_dist),
            ("IntSpace.crealFiniteL1", self.creal_finite_l1),
            ("IntSpace.crealFiniteL1_dist", self.creal_finite_l1_dist),
        ]
    }
}

pub(super) fn intern(kernel: &mut Kernel, intspace: NameId) -> L1Names {
    L1Names {
        l1_dist: kernel.name_str(intspace, "l1Dist"),
        l1_equiv: kernel.name_str(intspace, "L1Equiv"),
        l1_dist_bundle: kernel.name_str(intspace, "l1Dist_bundle"),
        l1_dist_nonneg: kernel.name_str(intspace, "l1Dist_nonneg"),
        l1_dist_self: kernel.name_str(intspace, "l1Dist_self"),
        l1_dist_comm: kernel.name_str(intspace, "l1Dist_comm"),
        l1_dist_triangle: kernel.name_str(intspace, "l1Dist_triangle"),
        l1_equiv_refl: kernel.name_str(intspace, "l1Equiv_refl"),
        l1_equiv_symm: kernel.name_str(intspace, "l1Equiv_symm"),
        l1_equiv_trans: kernel.name_str(intspace, "l1Equiv_trans"),
        l1_dist_le_of_equiv: kernel.name_str(intspace, "l1Dist_le_of_equiv"),
        l1_dist_congr: kernel.name_str(intspace, "l1Dist_congr"),
        bundled_l1: kernel.name_str(intspace, "bundledL1"),
        bundled_l1_carrier: kernel.name_str(intspace, "bundledL1_carrier"),
        bundled_l1_dist: kernel.name_str(intspace, "bundledL1_dist"),
        creal_interval_l1: kernel.name_str(intspace, "crealIntervalL1"),
        creal_interval_l1_dist: kernel.name_str(intspace, "crealIntervalL1_dist"),
        creal_finite_l1: kernel.name_str(intspace, "crealFiniteL1"),
        creal_finite_l1_dist: kernel.name_str(intspace, "crealFiniteL1_dist"),
    }
}

// ---------------------------------------------------------------------------
// The telescope every declaration in this file opens with.
// ---------------------------------------------------------------------------

/// `S`, the seven pieces of L¹ data, and the derived shapes every proof needs.
struct L1Ctx {
    space_ty: ExprId,
    s_fv: u64,
    s: ExprId,
    carrier: ExprId,
    /// `IntSpace.Bundled S`.
    bundled: ExprId,

    fdist_ty: ExprId,
    fdist_fv: u64,
    fdist: ExprId,
    hi_ty: ExprId,
    hi_fv: u64,
    hi: ExprId,
    hadd_ty: ExprId,
    hadd_fv: u64,
    hadd: ExprId,
    hnn_ty: ExprId,
    hnn_fv: u64,
    hnn: ExprId,
    hself_ty: ExprId,
    hself_fv: u64,
    hself: ExprId,
    hcomm_ty: ExprId,
    hcomm_fv: u64,
    hcomm: ExprId,
    htri_ty: ExprId,
    htri_fv: u64,
    htri: ExprId,
}

fn ctx(d: &mut IntDev<'_>, p: IntSpacePrelude) -> L1Ctx {
    let c = p.creal;
    let g = generic_space(d, p);
    let bundled = {
        let name = p.bundled.bundled;
        d.const_app(name, &[g.s])
    };

    // `fdist : carrier → carrier → carrier`.
    let fdist_ty = {
        let inner = d.arrow(g.carrier, g.carrier);
        d.arrow(g.carrier, inner)
    };
    let fdist_fv = d.fresh_fvar();
    let fdist = d.kernel().fvar(fdist_fv);

    let integrable = field(d, p, g.s, INTEGRABLE);
    let fle = field(d, p, g.s, FLE);
    let fadd = field(d, p, g.s, FADD);
    let fconst = field(d, p, g.s, FCONST);
    let zero = rzero(d, c);
    let czero = d.apply(fconst, &[zero]);

    // `∀ f g, Integrable f → Integrable g → Integrable (<target> f g)`.
    let closure_ty = |d: &mut IntDev<'_>, target: ExprId| {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let hf_ty = d.apply(integrable, &[f]);
        let hg_ty = d.apply(integrable, &[gg]);
        let combined = d.apply(target, &[f, gg]);
        let concl = d.apply(integrable, &[combined]);
        let hg_fv = d.fresh_fvar();
        let t = d.pi_fv(hg_fv, hg_ty, concl);
        let hf_fv = d.fresh_fvar();
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(g_fv, g.carrier, t);
        d.pi_fv(f_fv, g.carrier, t)
    };
    let hi_ty = closure_ty(d, fdist);
    let hadd_ty = closure_ty(d, fadd);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let hadd_fv = d.fresh_fvar();
    let hadd = d.kernel().fvar(hadd_fv);

    // `∀ f g, fle (fconst 0) (fdist f g)`.
    let hnn_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let dfg = d.apply(fdist, &[f, gg]);
        let concl = d.apply(fle, &[czero, dfg]);
        let t = d.pi_fv(g_fv, g.carrier, concl);
        d.pi_fv(f_fv, g.carrier, t)
    };
    let hnn_fv = d.fresh_fvar();
    let hnn = d.kernel().fvar(hnn_fv);

    // `∀ f, fle (fdist f f) (fconst 0)`.
    let hself_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let dff = d.apply(fdist, &[f, f]);
        let concl = d.apply(fle, &[dff, czero]);
        d.pi_fv(f_fv, g.carrier, concl)
    };
    let hself_fv = d.fresh_fvar();
    let hself = d.kernel().fvar(hself_fv);

    // `∀ f g, fle (fdist f g) (fdist g f)`.
    let hcomm_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let dfg = d.apply(fdist, &[f, gg]);
        let dgf = d.apply(fdist, &[gg, f]);
        let concl = d.apply(fle, &[dfg, dgf]);
        let t = d.pi_fv(g_fv, g.carrier, concl);
        d.pi_fv(f_fv, g.carrier, t)
    };
    let hcomm_fv = d.fresh_fvar();
    let hcomm = d.kernel().fvar(hcomm_fv);

    // `∀ f g h, fle (fdist f h) (fadd (fdist f g) (fdist g h))`.
    let htri_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let h_fv = d.fresh_fvar();
        let hh = d.kernel().fvar(h_fv);
        let dfh = d.apply(fdist, &[f, hh]);
        let dfg = d.apply(fdist, &[f, gg]);
        let dgh = d.apply(fdist, &[gg, hh]);
        let sum = d.apply(fadd, &[dfg, dgh]);
        let concl = d.apply(fle, &[dfh, sum]);
        let t = d.pi_fv(h_fv, g.carrier, concl);
        let t = d.pi_fv(g_fv, g.carrier, t);
        d.pi_fv(f_fv, g.carrier, t)
    };
    let htri_fv = d.fresh_fvar();
    let htri = d.kernel().fvar(htri_fv);

    L1Ctx {
        space_ty: g.space_ty,
        s_fv: g.s_fv,
        s: g.s,
        carrier: g.carrier,
        bundled,
        fdist_ty,
        fdist_fv,
        fdist,
        hi_ty,
        hi_fv,
        hi,
        hadd_ty,
        hadd_fv,
        hadd,
        hnn_ty,
        hnn_fv,
        hnn,
        hself_ty,
        hself_fv,
        hself,
        hcomm_ty,
        hcomm_fv,
        hcomm,
        htri_ty,
        htri_fv,
        htri,
    }
}

/// `(S, fdist, hI)` — the prefix `l1Dist` and `L1Equiv` need.
fn dist_args(x: &L1Ctx) -> [ExprId; 3] {
    [x.s, x.fdist, x.hi]
}

/// The whole telescope, in declaration order.
fn full_args(x: &L1Ctx) -> [ExprId; 8] {
    [x.s, x.fdist, x.hi, x.hadd, x.hnn, x.hself, x.hcomm, x.htri]
}

fn close_pi_dist(d: &mut IntDev<'_>, x: &L1Ctx, body: ExprId) -> ExprId {
    let t = d.pi_fv(x.hi_fv, x.hi_ty, body);
    let t = d.pi_fv(x.fdist_fv, x.fdist_ty, t);
    d.pi_fv(x.s_fv, x.space_ty, t)
}

fn close_lam_dist(d: &mut IntDev<'_>, x: &L1Ctx, body: ExprId) -> ExprId {
    let t = d.lam_fv(x.hi_fv, x.hi_ty, body);
    let t = d.lam_fv(x.fdist_fv, x.fdist_ty, t);
    d.lam_fv(x.s_fv, x.space_ty, t)
}

fn close_pi_full(d: &mut IntDev<'_>, x: &L1Ctx, body: ExprId) -> ExprId {
    let t = d.pi_fv(x.htri_fv, x.htri_ty, body);
    let t = d.pi_fv(x.hcomm_fv, x.hcomm_ty, t);
    let t = d.pi_fv(x.hself_fv, x.hself_ty, t);
    let t = d.pi_fv(x.hnn_fv, x.hnn_ty, t);
    let t = d.pi_fv(x.hadd_fv, x.hadd_ty, t);
    let t = d.pi_fv(x.hi_fv, x.hi_ty, t);
    let t = d.pi_fv(x.fdist_fv, x.fdist_ty, t);
    d.pi_fv(x.s_fv, x.space_ty, t)
}

fn close_lam_full(d: &mut IntDev<'_>, x: &L1Ctx, body: ExprId) -> ExprId {
    let t = d.lam_fv(x.htri_fv, x.htri_ty, body);
    let t = d.lam_fv(x.hcomm_fv, x.hcomm_ty, t);
    let t = d.lam_fv(x.hself_fv, x.hself_ty, t);
    let t = d.lam_fv(x.hnn_fv, x.hnn_ty, t);
    let t = d.lam_fv(x.hadd_fv, x.hadd_ty, t);
    let t = d.lam_fv(x.hi_fv, x.hi_ty, t);
    let t = d.lam_fv(x.fdist_fv, x.fdist_ty, t);
    d.lam_fv(x.s_fv, x.space_ty, t)
}

/// `IntSpace.l1Dist S fdist hI b₁ b₂`.
fn l1dist(d: &mut IntDev<'_>, p: IntSpacePrelude, x: &L1Ctx, b1: ExprId, b2: ExprId) -> ExprId {
    let name = p.l1.l1_dist;
    let [s, fdist, hi] = dist_args(x);
    d.const_app(name, &[s, fdist, hi, b1, b2])
}

/// `IntSpace.L1Equiv S fdist hI b₁ b₂`.
fn l1equiv(d: &mut IntDev<'_>, p: IntSpacePrelude, x: &L1Ctx, b1: ExprId, b2: ExprId) -> ExprId {
    let name = p.l1.l1_equiv;
    let [s, fdist, hi] = dist_args(x);
    d.const_app(name, &[s, fdist, hi, b1, b2])
}

/// `IntSpace.bundledFun S b` and `IntSpace.bundledWitness S b`.
fn unbundle(d: &mut IntDev<'_>, p: IntSpacePrelude, x: &L1Ctx, b: ExprId) -> (ExprId, ExprId) {
    let fun_name = p.bundled.bundled_fun;
    let wit_name = p.bundled.bundled_witness;
    let f = d.const_app(fun_name, &[x.s, b]);
    let w = d.const_app(wit_name, &[x.s, b]);
    (f, w)
}

/// The integrability witness `hI f g hf hg` for `fdist f g`.
fn dist_witness(
    d: &mut IntDev<'_>,
    x: &L1Ctx,
    f: ExprId,
    g: ExprId,
    hf: ExprId,
    hg: ExprId,
) -> ExprId {
    d.apply(x.hi, &[f, g, hf, hg])
}

// ---------------------------------------------------------------------------
// The two definitions.
// ---------------------------------------------------------------------------

/// `IntSpace.l1Dist : Π S fdist hI, S.Bundled → S.Bundled → CReal
///   := fun S fdist hI b₁ b₂ =>
///        S.integral (fdist (S.bundledFun b₁) (S.bundledFun b₂))
///                   (hI _ _ (S.bundledWitness b₁) (S.bundledWitness b₂))`.
///
/// **The L¹ seminorm.** It is total on `S.Bundled` for exactly the reason
/// `IntSpace.bundledIntegral` is: the bundle carries the integrability datum,
/// and `hI` turns two of them into the one this integrand needs.
fn declare_l1_dist(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let x = ctx(d, p);
    let real = super::rty(d, c);

    let b1_fv = d.fresh_fvar();
    let b1 = d.kernel().fvar(b1_fv);
    let b2_fv = d.fresh_fvar();
    let b2 = d.kernel().fvar(b2_fv);

    let body = {
        let (f1, w1) = unbundle(d, p, &x, b1);
        let (f2, w2) = unbundle(d, p, &x, b2);
        let integrand = d.apply(x.fdist, &[f1, f2]);
        let witness = dist_witness(d, &x, f1, f2, w1, w2);
        let integral = field(d, p, x.s, INTEGRAL);
        d.apply(integral, &[integrand, witness])
    };
    let value = {
        let t = d.lam_fv(b2_fv, x.bundled, body);
        let t = d.lam_fv(b1_fv, x.bundled, t);
        close_lam_dist(d, &x, t)
    };
    let ty = {
        let inner = d.arrow(x.bundled, real);
        let outer = d.arrow(x.bundled, inner);
        close_pi_dist(d, &x, outer)
    };
    definition(d, p.l1.l1_dist, ty, value)
}

/// `IntSpace.L1Equiv : Π S fdist hI, S.Bundled → S.Bundled → Prop
///   := fun S fdist hI b₁ b₂ => CReal.Equiv (l1Dist S fdist hI b₁ b₂) CReal.zero`.
///
/// "Equal almost everywhere", constructively. Making this a *definition* rather
/// than a field of the metric is what makes `Metric.distSelf` and
/// `Metric.distEquiv` the identity.
fn declare_l1_equiv(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let x = ctx(d, p);
    let prop = d.kernel().sort_zero();

    let b1_fv = d.fresh_fvar();
    let b1 = d.kernel().fvar(b1_fv);
    let b2_fv = d.fresh_fvar();
    let b2 = d.kernel().fvar(b2_fv);

    let body = {
        let dist = l1dist(d, p, &x, b1, b2);
        let zero = rzero(d, c);
        req(d, c, dist, zero)
    };
    let value = {
        let t = d.lam_fv(b2_fv, x.bundled, body);
        let t = d.lam_fv(b1_fv, x.bundled, t);
        close_lam_dist(d, &x, t)
    };
    let ty = {
        let inner = d.arrow(x.bundled, prop);
        let outer = d.arrow(x.bundled, inner);
        close_pi_dist(d, &x, outer)
    };
    definition(d, p.l1.l1_equiv, ty, value)
}

/// `IntSpace.l1Dist_bundle : ∀ S fdist hI f g hf hg,
/// Eq CReal (l1Dist S fdist hI (S.bundle f hf) (S.bundle g hg))
///          (S.integral (fdist f g) (hI f g hf hg))`.
///
/// **The evaluation test for `l1Dist`, at symbolic arguments.** `Eq.refl`:
/// `Sigma.fst`/`snd` ι-reduce on the literal constructor, so bundling two
/// functions and taking their L¹ distance IS integrating `fdist f g`. Nothing
/// concrete can be substituted here — a `CReal` numeral probe would be vacuous
/// — so an arbitrary `S`, an arbitrary `fdist` and two arbitrary integrands is
/// the strongest form this check has.
fn declare_l1_dist_bundle(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let logic = c.rat.int.logic;
    let x = ctx(d, p);
    let real = super::rty(d, c);
    let zero = d.kernel().level_zero();
    let one = d.kernel().level_succ(zero);

    let integrable = field(d, p, x.s, INTEGRABLE);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(g_fv);
    let hf_ty = d.apply(integrable, &[f]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_ty = d.apply(integrable, &[gg]);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let rhs = {
        let integrand = d.apply(x.fdist, &[f, gg]);
        let witness = dist_witness(d, &x, f, gg, hf, hg);
        let integral = field(d, p, x.s, INTEGRAL);
        d.apply(integral, &[integrand, witness])
    };
    let lhs = {
        let bundle = p.bundled.bundle;
        let b1 = d.const_app(bundle, &[x.s, f, hf]);
        let b2 = d.const_app(bundle, &[x.s, gg, hg]);
        l1dist(d, p, &x, b1, b2)
    };
    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![one]);
        d.apply(head, &[real, lhs, rhs])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![one]);
        d.apply(head, &[real, rhs])
    };

    let ty = {
        let t = d.pi_fv(hg_fv, hg_ty, stmt);
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(g_fv, x.carrier, t);
        let t = d.pi_fv(f_fv, x.carrier, t);
        close_pi_dist(d, &x, t)
    };
    let value = {
        let t = d.lam_fv(hg_fv, hg_ty, proof);
        let t = d.lam_fv(hf_fv, hf_ty, t);
        let t = d.lam_fv(g_fv, x.carrier, t);
        let t = d.lam_fv(f_fv, x.carrier, t);
        close_lam_dist(d, &x, t)
    };
    theorem(d, p.l1.l1_dist_bundle, ty, value)
}

// ---------------------------------------------------------------------------
// The four metric estimates.
// ---------------------------------------------------------------------------

/// `IntSpace.l1Dist_nonneg : ∀ S fdist hI hAdd hNN hSelf hComm hTri a b,
/// CReal.le CReal.zero (l1Dist S fdist hI a b)`.
///
/// `IntSpace.integral_nonneg` at the integrand `fdist f g`, with `hNN` as its
/// pointwise hypothesis. The whole `0 · total ~ 0` step is inside
/// `integral_nonneg` already; this file does not repeat it.
fn declare_l1_dist_nonneg(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let x = ctx(d, p);

    let b1_fv = d.fresh_fvar();
    let b1 = d.kernel().fvar(b1_fv);
    let b2_fv = d.fresh_fvar();
    let b2 = d.kernel().fvar(b2_fv);

    let concl = {
        let zero = rzero(d, c);
        let dist = l1dist(d, p, &x, b1, b2);
        rle(d, c, zero, dist)
    };
    let proof = {
        let (f1, w1) = unbundle(d, p, &x, b1);
        let (f2, w2) = unbundle(d, p, &x, b2);
        let integrand = d.apply(x.fdist, &[f1, f2]);
        let witness = dist_witness(d, &x, f1, f2, w1, w2);
        let pointwise = d.apply(x.hnn, &[f1, f2]);
        d.lemma(p.integral_nonneg, &[x.s, integrand, witness, pointwise])
    };

    let ty = {
        let t = d.pi_fv(b2_fv, x.bundled, concl);
        let t = d.pi_fv(b1_fv, x.bundled, t);
        close_pi_full(d, &x, t)
    };
    let value = {
        let t = d.lam_fv(b2_fv, x.bundled, proof);
        let t = d.lam_fv(b1_fv, x.bundled, t);
        close_lam_full(d, &x, t)
    };
    theorem(d, p.l1.l1_dist_nonneg, ty, value)
}

/// `IntSpace.l1Dist_self : ∀ …, CReal.Equiv (l1Dist … a a) CReal.zero`.
///
/// `≤ 0` from `hSelf` through `IntSpace.integral_le_const` at `M := 0` (whose
/// conclusion is `≤ 0 · total`, closed by `mul_comm`/`mul_zero` — the ℝ
/// prelude has `mul_zero` and no `zero_mul`), and `0 ≤` from
/// [`declare_l1_dist_nonneg`]. `equiv_of_le_le` closes it.
fn declare_l1_dist_self(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let x = ctx(d, p);

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let dist = l1dist(d, p, &x, b, b);
    let zero = rzero(d, c);
    let concl = req(d, c, dist, zero);

    let proof = {
        let (f, w) = unbundle(d, p, &x, b);
        let integrand = d.apply(x.fdist, &[f, f]);
        let witness = dist_witness(d, &x, f, f, w, w);
        let pointwise = d.apply(x.hself, &[f]);

        // `∫ ≤ 0 · total`.
        let upper = d.lemma(
            p.integral_le_const,
            &[x.s, zero, integrand, witness, pointwise],
        );
        // `0 · total ~ total · 0 ~ 0`.
        let total = field(d, p, x.s, super::TOTAL);
        let zt = super::rmul(d, c, zero, total);
        let tz = super::rmul(d, c, total, zero);
        let comm = d.lemma(c.mul_comm, &[zero, total]);
        let mz = d.lemma(c.mul_zero, &[total]);
        let zt_zero = super::rtrans(d, c, zt, tz, zero, comm, mz);
        let zt_le_zero = d.lemma(c.le_of_equiv, &[zt, zero, zt_zero]);
        let le_up = d.lemma(c.le_trans, &[dist, zt, zero, upper, zt_le_zero]);

        let args = full_args(&x);
        let le_down = {
            let name = p.l1.l1_dist_nonneg;
            d.lemma(
                name,
                &[
                    args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7], b, b,
                ],
            )
        };
        d.lemma(c.equiv_of_le_le, &[dist, zero, le_up, le_down])
    };

    let ty = {
        let t = d.pi_fv(b_fv, x.bundled, concl);
        close_pi_full(d, &x, t)
    };
    let value = {
        let t = d.lam_fv(b_fv, x.bundled, proof);
        close_lam_full(d, &x, t)
    };
    theorem(d, p.l1.l1_dist_self, ty, value)
}

/// `IntSpace.l1Dist_comm : ∀ …, CReal.Equiv (l1Dist … a b) (l1Dist … b a)`.
///
/// `IntSpace.integral_congr` — the integrand congruence `CReal.integral` never
/// had — applied to `hComm` in both argument orders. No estimate.
fn declare_l1_dist_comm(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let x = ctx(d, p);

    let b1_fv = d.fresh_fvar();
    let b1 = d.kernel().fvar(b1_fv);
    let b2_fv = d.fresh_fvar();
    let b2 = d.kernel().fvar(b2_fv);

    let concl = {
        let lhs = l1dist(d, p, &x, b1, b2);
        let rhs = l1dist(d, p, &x, b2, b1);
        req(d, c, lhs, rhs)
    };
    let proof = {
        let (f1, w1) = unbundle(d, p, &x, b1);
        let (f2, w2) = unbundle(d, p, &x, b2);
        let d12 = d.apply(x.fdist, &[f1, f2]);
        let d21 = d.apply(x.fdist, &[f2, f1]);
        let w12 = dist_witness(d, &x, f1, f2, w1, w2);
        let w21 = dist_witness(d, &x, f2, f1, w2, w1);
        let fwd = d.apply(x.hcomm, &[f1, f2]);
        let bwd = d.apply(x.hcomm, &[f2, f1]);
        d.lemma(p.integral_congr, &[x.s, d12, d21, w12, w21, fwd, bwd])
    };

    let ty = {
        let t = d.pi_fv(b2_fv, x.bundled, concl);
        let t = d.pi_fv(b1_fv, x.bundled, t);
        close_pi_full(d, &x, t)
    };
    let value = {
        let t = d.lam_fv(b2_fv, x.bundled, proof);
        let t = d.lam_fv(b1_fv, x.bundled, t);
        close_lam_full(d, &x, t)
    };
    theorem(d, p.l1.l1_dist_comm, ty, value)
}

/// `IntSpace.l1Dist_triangle : ∀ …, CReal.le (l1Dist … a c)
/// (CReal.add (l1Dist … a b) (l1Dist … b c))`.
///
/// `hTri` under `S.integralLe`, then `S.integralAdd` splits the right-hand
/// integral. `hAdd` exists for exactly one reason: `integralAdd` takes the
/// integrability witness of the SUM as an explicit argument (ADR-1612's
/// deliberate shape), and nothing else in the record produces one.
fn declare_l1_dist_triangle(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let x = ctx(d, p);

    let b1_fv = d.fresh_fvar();
    let b1 = d.kernel().fvar(b1_fv);
    let b2_fv = d.fresh_fvar();
    let b2 = d.kernel().fvar(b2_fv);
    let b3_fv = d.fresh_fvar();
    let b3 = d.kernel().fvar(b3_fv);

    let d13 = l1dist(d, p, &x, b1, b3);
    let d12 = l1dist(d, p, &x, b1, b2);
    let d23 = l1dist(d, p, &x, b2, b3);
    let sum = radd(d, c, d12, d23);
    let concl = rle(d, c, d13, sum);

    let proof = {
        let (f1, w1) = unbundle(d, p, &x, b1);
        let (f2, w2) = unbundle(d, p, &x, b2);
        let (f3, w3) = unbundle(d, p, &x, b3);

        let g13 = d.apply(x.fdist, &[f1, f3]);
        let g12 = d.apply(x.fdist, &[f1, f2]);
        let g23 = d.apply(x.fdist, &[f2, f3]);
        let fadd = field(d, p, x.s, FADD);
        let gsum = d.apply(fadd, &[g12, g23]);

        let i13 = dist_witness(d, &x, f1, f3, w1, w3);
        let i12 = dist_witness(d, &x, f1, f2, w1, w2);
        let i23 = dist_witness(d, &x, f2, f3, w2, w3);
        let isum = d.apply(x.hadd, &[g12, g23, i12, i23]);

        // `∫ fdist f₁ f₃ ≤ ∫ (fdist f₁ f₂ + fdist f₂ f₃)`.
        let pointwise = d.apply(x.htri, &[f1, f2, f3]);
        let integral_le = field(d, p, x.s, INTEGRAL_LE);
        let step = d.apply(integral_le, &[g13, gsum, i13, isum, pointwise]);

        // `∫ (g₁₂ + g₂₃) ~ ∫g₁₂ + ∫g₂₃`.
        let integral_add = field(d, p, x.s, INTEGRAL_ADD);
        let split = d.apply(integral_add, &[g12, g23, i12, i23, isum]);

        let integral = field(d, p, x.s, INTEGRAL);
        let isum_val = d.apply(integral, &[gsum, isum]);
        let refl13 = super::rrefl(d, c, d13);
        d.lemma(c.le_congr, &[d13, d13, isum_val, sum, refl13, split, step])
    };

    let ty = {
        let t = d.pi_fv(b3_fv, x.bundled, concl);
        let t = d.pi_fv(b2_fv, x.bundled, t);
        let t = d.pi_fv(b1_fv, x.bundled, t);
        close_pi_full(d, &x, t)
    };
    let value = {
        let t = d.lam_fv(b3_fv, x.bundled, proof);
        let t = d.lam_fv(b2_fv, x.bundled, t);
        let t = d.lam_fv(b1_fv, x.bundled, t);
        close_lam_full(d, &x, t)
    };
    theorem(d, p.l1.l1_dist_triangle, ty, value)
}

// ---------------------------------------------------------------------------
// The setoid laws.
// ---------------------------------------------------------------------------

/// Apply a theorem of this file that takes the full telescope, then `extra`.
fn full_lemma(d: &mut IntDev<'_>, x: &L1Ctx, name: NameId, extra: &[ExprId]) -> ExprId {
    let mut args = full_args(x).to_vec();
    args.extend_from_slice(extra);
    d.lemma(name, &args)
}

/// `IntSpace.l1Equiv_refl : ∀ …, L1Equiv … a a`.
///
/// [`declare_l1_dist_self`] verbatim: `L1Equiv a a` δ-unfolds to
/// `CReal.Equiv (l1Dist a a) CReal.zero`, which is that theorem's statement.
fn declare_l1_equiv_refl(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let x = ctx(d, p);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let concl = l1equiv(d, p, &x, b, b);
    let proof = full_lemma(d, &x, p.l1.l1_dist_self, &[b]);

    let ty = {
        let t = d.pi_fv(b_fv, x.bundled, concl);
        close_pi_full(d, &x, t)
    };
    let value = {
        let t = d.lam_fv(b_fv, x.bundled, proof);
        close_lam_full(d, &x, t)
    };
    theorem(d, p.l1.l1_equiv_refl, ty, value)
}

/// `IntSpace.l1Equiv_symm : ∀ …, L1Equiv … a b → L1Equiv … b a`.
fn declare_l1_equiv_symm(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let x = ctx(d, p);

    let b1_fv = d.fresh_fvar();
    let b1 = d.kernel().fvar(b1_fv);
    let b2_fv = d.fresh_fvar();
    let b2 = d.kernel().fvar(b2_fv);

    let hyp_ty = l1equiv(d, p, &x, b1, b2);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let concl = l1equiv(d, p, &x, b2, b1);

    let proof = {
        let d12 = l1dist(d, p, &x, b1, b2);
        let d21 = l1dist(d, p, &x, b2, b1);
        let zero = rzero(d, c);
        let comm = full_lemma(d, &x, p.l1.l1_dist_comm, &[b1, b2]);
        let flipped = super::rsymm(d, c, d12, d21, comm);
        super::rtrans(d, c, d21, d12, zero, flipped, h)
    };

    let ty = {
        let t = d.pi_fv(h_fv, hyp_ty, concl);
        let t = d.pi_fv(b2_fv, x.bundled, t);
        let t = d.pi_fv(b1_fv, x.bundled, t);
        close_pi_full(d, &x, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, hyp_ty, proof);
        let t = d.lam_fv(b2_fv, x.bundled, t);
        let t = d.lam_fv(b1_fv, x.bundled, t);
        close_lam_full(d, &x, t)
    };
    theorem(d, p.l1.l1_equiv_symm, ty, value)
}

/// `IntSpace.l1Equiv_trans : ∀ …, L1Equiv … a b → L1Equiv … b c →
/// L1Equiv … a c`.
///
/// The triangle inequality bounds `d(a,c)` by `d(a,b) + d(b,c) ~ 0 + 0 ~ 0`,
/// and `l1Dist_nonneg` bounds it below; `equiv_of_le_le` closes it. The
/// `0 + 0 ~ 0` step is `add_congr` followed by `add_zero`.
fn declare_l1_equiv_trans(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let x = ctx(d, p);

    let b1_fv = d.fresh_fvar();
    let b1 = d.kernel().fvar(b1_fv);
    let b2_fv = d.fresh_fvar();
    let b2 = d.kernel().fvar(b2_fv);
    let b3_fv = d.fresh_fvar();
    let b3 = d.kernel().fvar(b3_fv);

    let h12_ty = l1equiv(d, p, &x, b1, b2);
    let h12_fv = d.fresh_fvar();
    let h12 = d.kernel().fvar(h12_fv);
    let h23_ty = l1equiv(d, p, &x, b2, b3);
    let h23_fv = d.fresh_fvar();
    let h23 = d.kernel().fvar(h23_fv);
    let concl = l1equiv(d, p, &x, b1, b3);

    let proof = {
        let zero = rzero(d, c);
        let d13 = l1dist(d, p, &x, b1, b3);
        let d12 = l1dist(d, p, &x, b1, b2);
        let d23 = l1dist(d, p, &x, b2, b3);
        let sum = radd(d, c, d12, d23);
        let zz = radd(d, c, zero, zero);

        let tri = full_lemma(d, &x, p.l1.l1_dist_triangle, &[b1, b2, b3]);
        let sum_zz = d.lemma(c.add_congr, &[d12, zero, d23, zero, h12, h23]);
        let zz_zero = d.lemma(c.add_zero, &[zero]);
        let sum_zero = super::rtrans(d, c, sum, zz, zero, sum_zz, zz_zero);
        let refl13 = super::rrefl(d, c, d13);
        let le_up = d.lemma(c.le_congr, &[d13, d13, sum, zero, refl13, sum_zero, tri]);
        let le_down = full_lemma(d, &x, p.l1.l1_dist_nonneg, &[b1, b3]);
        d.lemma(c.equiv_of_le_le, &[d13, zero, le_up, le_down])
    };

    let ty = {
        let t = d.pi_fv(h23_fv, h23_ty, concl);
        let t = d.pi_fv(h12_fv, h12_ty, t);
        let t = d.pi_fv(b3_fv, x.bundled, t);
        let t = d.pi_fv(b2_fv, x.bundled, t);
        let t = d.pi_fv(b1_fv, x.bundled, t);
        close_pi_full(d, &x, t)
    };
    let value = {
        let t = d.lam_fv(h23_fv, h23_ty, proof);
        let t = d.lam_fv(h12_fv, h12_ty, t);
        let t = d.lam_fv(b3_fv, x.bundled, t);
        let t = d.lam_fv(b2_fv, x.bundled, t);
        let t = d.lam_fv(b1_fv, x.bundled, t);
        close_lam_full(d, &x, t)
    };
    theorem(d, p.l1.l1_equiv_trans, ty, value)
}

/// `IntSpace.l1Dist_le_of_equiv : ∀ …, L1Equiv … a a' → L1Equiv … b b' →
/// CReal.le (l1Dist … a b) (l1Dist … a' b')`.
///
/// The quadrilateral estimate, one direction:
///
/// ```text
/// d(a,b) ≤ d(a,a') + d(a',b)                        [triangle]
///        ≤ d(a,a') + (d(a',b') + d(b',b))           [triangle, inside]
///        ~ 0 + (d(a',b') + 0) ~ d(a',b')
/// ```
///
/// `d(b',b) ~ 0` comes from the second hypothesis through `l1Equiv_symm`.
/// [`declare_l1_dist_congr`] is this theorem run twice.
fn declare_l1_dist_le_of_equiv(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let x = ctx(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let ap_fv = d.fresh_fvar();
    let ap = d.kernel().fvar(ap_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let bp_fv = d.fresh_fvar();
    let bp = d.kernel().fvar(bp_fv);

    let ha_ty = l1equiv(d, p, &x, a, ap);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);
    let hb_ty = l1equiv(d, p, &x, b, bp);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let d_ab = l1dist(d, p, &x, a, b);
    let d_apbp = l1dist(d, p, &x, ap, bp);
    let concl = rle(d, c, d_ab, d_apbp);

    let proof = {
        let zero = rzero(d, c);
        let d_aap = l1dist(d, p, &x, a, ap);
        let d_apb = l1dist(d, p, &x, ap, b);
        let d_bpb = l1dist(d, p, &x, bp, b);

        // `d(b',b) ~ 0`.
        let hbp = full_lemma(d, &x, p.l1.l1_equiv_symm, &[b, bp, hb]);

        // `d(a',b) ≤ d(a',b') + d(b',b) ~ d(a',b') + 0 ~ d(a',b')`.
        let inner_sum = radd(d, c, d_apbp, d_bpb);
        let inner_tri = full_lemma(d, &x, p.l1.l1_dist_triangle, &[ap, bp, b]);
        let apbp_zero = radd(d, c, d_apbp, zero);
        let refl_apbp = super::rrefl(d, c, d_apbp);
        let sum_congr = d.lemma(c.add_congr, &[d_apbp, d_apbp, d_bpb, zero, refl_apbp, hbp]);
        let drop_zero = d.lemma(c.add_zero, &[d_apbp]);
        let inner_eq = super::rtrans(d, c, inner_sum, apbp_zero, d_apbp, sum_congr, drop_zero);
        let refl_apb = super::rrefl(d, c, d_apb);
        let u2 = d.lemma(
            c.le_congr,
            &[
                d_apb, d_apb, inner_sum, d_apbp, refl_apb, inner_eq, inner_tri,
            ],
        );

        // `d(a,a') + d(a',b) ≤ 0 + d(a',b')`.
        let ha_le = d.lemma(c.le_of_equiv, &[d_aap, zero, ha]);
        let outer_lhs = radd(d, c, d_aap, d_apb);
        let outer_rhs = radd(d, c, zero, d_apbp);
        let combined = d.lemma(c.add_le_add, &[d_aap, zero, d_apb, d_apbp, ha_le, u2]);

        // `d(a,b) ≤ d(a,a') + d(a',b)`.
        let outer_tri = full_lemma(d, &x, p.l1.l1_dist_triangle, &[a, ap, b]);
        let chained = d.lemma(
            c.le_trans,
            &[d_ab, outer_lhs, outer_rhs, outer_tri, combined],
        );

        // `0 + d(a',b') ~ d(a',b') + 0 ~ d(a',b')`.
        let flipped = radd(d, c, d_apbp, zero);
        let comm = d.lemma(c.add_comm, &[zero, d_apbp]);
        let az = d.lemma(c.add_zero, &[d_apbp]);
        let outer_eq = super::rtrans(d, c, outer_rhs, flipped, d_apbp, comm, az);
        let refl_ab = super::rrefl(d, c, d_ab);
        d.lemma(
            c.le_congr,
            &[d_ab, d_ab, outer_rhs, d_apbp, refl_ab, outer_eq, chained],
        )
    };

    let ty = {
        let t = d.pi_fv(hb_fv, hb_ty, concl);
        let t = d.pi_fv(ha_fv, ha_ty, t);
        let t = d.pi_fv(bp_fv, x.bundled, t);
        let t = d.pi_fv(b_fv, x.bundled, t);
        let t = d.pi_fv(ap_fv, x.bundled, t);
        let t = d.pi_fv(a_fv, x.bundled, t);
        close_pi_full(d, &x, t)
    };
    let value = {
        let t = d.lam_fv(hb_fv, hb_ty, proof);
        let t = d.lam_fv(ha_fv, ha_ty, t);
        let t = d.lam_fv(bp_fv, x.bundled, t);
        let t = d.lam_fv(b_fv, x.bundled, t);
        let t = d.lam_fv(ap_fv, x.bundled, t);
        let t = d.lam_fv(a_fv, x.bundled, t);
        close_lam_full(d, &x, t)
    };
    theorem(d, p.l1.l1_dist_le_of_equiv, ty, value)
}

/// `IntSpace.l1Dist_congr : ∀ …, L1Equiv … a a' → L1Equiv … b b' →
/// CReal.Equiv (l1Dist … a b) (l1Dist … a' b')`.
///
/// [`declare_l1_dist_le_of_equiv`] in both directions — the second with the two
/// hypotheses run through `l1Equiv_symm` — and `equiv_of_le_le`. The binder
/// order `a a' b b'` is `Metric.distCongr`'s own, so this theorem partially
/// applied IS that field.
fn declare_l1_dist_congr(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Result<(), KernelError> {
    let c = p.creal;
    let x = ctx(d, p);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let ap_fv = d.fresh_fvar();
    let ap = d.kernel().fvar(ap_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let bp_fv = d.fresh_fvar();
    let bp = d.kernel().fvar(bp_fv);

    let ha_ty = l1equiv(d, p, &x, a, ap);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);
    let hb_ty = l1equiv(d, p, &x, b, bp);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let d_ab = l1dist(d, p, &x, a, b);
    let d_apbp = l1dist(d, p, &x, ap, bp);
    let concl = req(d, c, d_ab, d_apbp);

    let proof = {
        let fwd = full_lemma(d, &x, p.l1.l1_dist_le_of_equiv, &[a, ap, b, bp, ha, hb]);
        let ha_sym = full_lemma(d, &x, p.l1.l1_equiv_symm, &[a, ap, ha]);
        let hb_sym = full_lemma(d, &x, p.l1.l1_equiv_symm, &[b, bp, hb]);
        let bwd = full_lemma(
            d,
            &x,
            p.l1.l1_dist_le_of_equiv,
            &[ap, a, bp, b, ha_sym, hb_sym],
        );
        d.lemma(c.equiv_of_le_le, &[d_ab, d_apbp, fwd, bwd])
    };

    let ty = {
        let t = d.pi_fv(hb_fv, hb_ty, concl);
        let t = d.pi_fv(ha_fv, ha_ty, t);
        let t = d.pi_fv(bp_fv, x.bundled, t);
        let t = d.pi_fv(b_fv, x.bundled, t);
        let t = d.pi_fv(ap_fv, x.bundled, t);
        let t = d.pi_fv(a_fv, x.bundled, t);
        close_pi_full(d, &x, t)
    };
    let value = {
        let t = d.lam_fv(hb_fv, hb_ty, proof);
        let t = d.lam_fv(ha_fv, ha_ty, t);
        let t = d.lam_fv(bp_fv, x.bundled, t);
        let t = d.lam_fv(b_fv, x.bundled, t);
        let t = d.lam_fv(ap_fv, x.bundled, t);
        let t = d.lam_fv(a_fv, x.bundled, t);
        close_lam_full(d, &x, t)
    };
    theorem(d, p.l1.l1_dist_congr, ty, value)
}

// ---------------------------------------------------------------------------
// The metric space itself.
// ---------------------------------------------------------------------------

/// `IntSpace.bundledL1 : Π S fdist hI hAdd hNN hSelf hComm hTri, Metric`.
///
/// **The first metric space in this library that is not a subspace of one that
/// already existed.** Ten of the twelve fields are a theorem of this file
/// partially applied — the binder orders were chosen to make that true — and
/// the remaining two, `distSelf` and `distEquiv`, are `fun a b h => h`, because
/// `L1Equiv` δ-unfolds to exactly `CReal.Equiv (dist a b) CReal.zero`.
fn declare_bundled_l1(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    m: MetricPrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let x = ctx(d, p);
    let args = full_args(&x);
    let [s, fdist, hi] = dist_args(&x);

    let carrier = x.bundled;
    let equiv = {
        let name = p.l1.l1_equiv;
        d.const_app(name, &[s, fdist, hi])
    };
    let dist = {
        let name = p.l1.l1_dist;
        d.const_app(name, &[s, fdist, hi])
    };
    let partial = |d: &mut IntDev<'_>, name: NameId| d.lemma(name, &args);

    let equiv_refl = partial(d, p.l1.l1_equiv_refl);
    let equiv_symm = partial(d, p.l1.l1_equiv_symm);
    let equiv_trans = partial(d, p.l1.l1_equiv_trans);
    let dist_congr = partial(d, p.l1.l1_dist_congr);
    let dist_nonneg = partial(d, p.l1.l1_dist_nonneg);
    let dist_comm = partial(d, p.l1.l1_dist_comm);
    let dist_triangle = partial(d, p.l1.l1_dist_triangle);

    // `fun a b (h : L1Equiv a b) => h`, used for BOTH `distSelf` and
    // `distEquiv`: the two directions are the same term because the two
    // propositions are δ-equal.
    let identity_law = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let hyp = l1equiv(d, p, &x, a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let t = d.lam_fv(h_fv, hyp, h);
        let t = d.lam_fv(b_fv, x.bundled, t);
        d.lam_fv(a_fv, x.bundled, t)
    };
    let dist_self = identity_law;
    let dist_equiv = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let dab = l1dist(d, p, &x, a, b);
        let zero = rzero(d, c);
        let hyp = req(d, c, dab, zero);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let t = d.lam_fv(h_fv, hyp, h);
        let t = d.lam_fv(b_fv, x.bundled, t);
        d.lam_fv(a_fv, x.bundled, t)
    };

    let fields = vec![
        carrier,
        equiv,
        equiv_refl,
        equiv_symm,
        equiv_trans,
        dist,
        dist_congr,
        dist_nonneg,
        dist_self,
        dist_equiv,
        dist_comm,
        dist_triangle,
    ];
    let inst = mk_instance(d.kernel(), &m.record, &fields);

    let metric_ty = d.kernel().const_(m.record.ind, vec![]);
    let ty = close_pi_full(d, &x, metric_ty);
    let value = close_lam_full(d, &x, inst);
    definition(d, p.l1.bundled_l1, ty, value)
}

/// The universe level `1`, at which `Eq` over `Sort 1` is stated.
fn level_one(d: &mut IntDev<'_>) -> LevelId {
    let zero = d.kernel().level_zero();
    d.kernel().level_succ(zero)
}

/// `IntSpace.bundledL1_carrier : ∀ …,
/// Eq (Sort 1) (Metric.carrier (bundledL1 …)) (IntSpace.Bundled S)`.
///
/// The evaluation test for `bundledL1`, at symbolic arguments: `Eq.refl`. The
/// carrier of the L¹ metric IS the bundled carrier, definitionally.
fn declare_bundled_l1_carrier(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    m: MetricPrelude,
) -> Result<(), KernelError> {
    let logic = p.creal.rat.int.logic;
    let x = ctx(d, p);
    let one = level_one(d);
    let two = d.kernel().level_succ(one);

    let inst = {
        let name = p.l1.bundled_l1;
        let args = full_args(&x);
        d.const_app(name, &args)
    };
    let lhs = {
        let sel = d
            .kernel()
            .const_(m.record.sel(crate::METRIC_CARRIER), vec![]);
        d.apply(sel, &[inst])
    };
    let sort_one = d.kernel().sort(one);
    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![two]);
        d.apply(head, &[sort_one, lhs, x.bundled])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![two]);
        d.apply(head, &[sort_one, x.bundled])
    };
    let ty = close_pi_full(d, &x, stmt);
    let value = close_lam_full(d, &x, proof);
    theorem(d, p.l1.bundled_l1_carrier, ty, value)
}

/// `IntSpace.bundledL1_dist : ∀ … a b,
/// Eq CReal (Metric.dist (bundledL1 …) a b) (l1Dist S fdist hI a b)`.
///
/// The evaluation test that matters: the metric's distance IS the L¹ seminorm,
/// by `Eq.refl`. Without it, "we built a `Metric`" would be a claim about a
/// record and not about L¹.
fn declare_bundled_l1_dist(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    m: MetricPrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let logic = c.rat.int.logic;
    let x = ctx(d, p);
    let real = super::rty(d, c);
    let one = level_one(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let inst = {
        let name = p.l1.bundled_l1;
        let args = full_args(&x);
        d.const_app(name, &args)
    };
    let lhs = {
        let sel = d.kernel().const_(m.record.sel(crate::METRIC_DIST), vec![]);
        let applied = d.apply(sel, &[inst]);
        d.apply(applied, &[a, b])
    };
    let rhs = l1dist(d, p, &x, a, b);
    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![one]);
        d.apply(head, &[real, lhs, rhs])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![one]);
        d.apply(head, &[real, rhs])
    };
    let ty = {
        let t = d.pi_fv(b_fv, x.bundled, stmt);
        let t = d.pi_fv(a_fv, x.bundled, t);
        close_pi_full(d, &x, t)
    };
    let value = {
        let t = d.lam_fv(b_fv, x.bundled, proof);
        let t = d.lam_fv(a_fv, x.bundled, t);
        close_lam_full(d, &x, t)
    };
    theorem(d, p.l1.bundled_l1_dist, ty, value)
}

// ---------------------------------------------------------------------------
// The two instances. NOTHING here is a new estimate: every one of the seven
// L1 arguments is an EXISTING lemma applied verbatim, which is the reuse
// measurement ADR-1625 records.
// ---------------------------------------------------------------------------

/// A carrier of the shape `X -> CReal`, which is what both instances have.
struct Pointwise {
    /// The instance's carrier `X -> CReal`.
    carrier: ExprId,
    /// The point type `X`.
    point: ExprId,
}

/// `fun f g => fun t => CReal.abs (CReal.add (f t) (CReal.neg (g t)))` — the
/// pointwise distance.
///
/// Note it is `CReal.neg`, not `CReal.mul (CReal.neg CReal.one)`. Taking
/// `fdist` as the datum rather than deriving it from the record's `fscale` is
/// what makes every `Metric.CReal.*` lemma below apply with **no bridging step
/// at all**: those lemmas are stated about `abs (a + -b)`, and `fscale` would
/// have forced a `mul (neg one) x ~ neg x` lemma the ℝ prelude does not have.
fn pointwise_fdist(d: &mut IntDev<'_>, p: IntSpacePrelude, w: &Pointwise) -> ExprId {
    let c = p.creal;
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(g_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let ft = d.apply(f, &[t]);
    let gt = d.apply(gg, &[t]);
    let ngt = super::rneg(d, c, gt);
    let diff = radd(d, c, ft, ngt);
    let body = d.const_app(c.abs, &[diff]);
    let body = d.lam_fv(t_fv, w.point, body);
    let inner = d.lam_fv(g_fv, w.carrier, body);
    d.lam_fv(f_fv, w.carrier, inner)
}

/// `IntSpace.crealIntervalL1 : Pi (a b : CReal), CReal.le a b -> Metric`.
///
/// **L1[a, b].** The seven arguments, and what each one is:
///
/// | argument | witness | new estimate? |
/// | --- | --- | --- |
/// | `hI` | `IntSpace.CReal.uniformly_continuous_abs` after `CReal.uniformly_continuous_sub` | no |
/// | `hAdd` | `CReal.uniformly_continuous_add` | no |
/// | `hNN` | `CReal.abs_nonneg` | no |
/// | `hSelf` | `Metric.CReal.distSelf` | no |
/// | `hComm` | `Metric.CReal.absSubLe` | no |
/// | `hTri` | `Metric.CReal.distTriangle` | no |
///
/// The last three are `Metric.creal`'s own metric laws — the ℝ metric's
/// `distSelf`, `distComm` and `distTriangle` — applied at the point `t`. That
/// is the sense in which W2-1's `Metric` layer pays for itself twice: the
/// theorems that made ℝ a metric space are exactly the theorems that make L1
/// one.
fn declare_creal_interval_l1(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    m: MetricPrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let real = super::rty(d, c);
    let w = Pointwise {
        carrier: d.arrow(real, real),
        point: real,
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let space = d.const_app(p.creal_interval, &[a, b, hab]);
    let fdist = pointwise_fdist(d, p, &w);

    // Re-wrap a proof stated at one point into `fun t (_ : a <= t) (_ : t <= b) => …`.
    let wrap = |d: &mut IntDev<'_>, t_fv: u64, t: ExprId, body: ExprId| {
        let lo = rle(d, c, a, t);
        let hi = rle(d, c, t, b);
        let h2_fv = d.fresh_fvar();
        let body = d.lam_fv(h2_fv, hi, body);
        let h1_fv = d.fresh_fvar();
        let body = d.lam_fv(h1_fv, lo, body);
        d.lam_fv(t_fv, real, body)
    };

    // `fun F G hF hG => IntSpace.CReal.uniformly_continuous_abs (F - G) a b
    //                     (CReal.uniformly_continuous_sub F G a b hF hG)`,
    // and the same binders around `CReal.uniformly_continuous_add`.
    let (hi_arg, hadd_arg) = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let hf_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);
        let hg_ty = d.const_app(c.uniformly_continuous_on, &[gg, a, b]);
        let hg_fv = d.fresh_fvar();
        let hg = d.kernel().fvar(hg_fv);

        let difference = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let ft = d.apply(f, &[t]);
            let gt = d.apply(gg, &[t]);
            let ngt = super::rneg(d, c, gt);
            let body = radd(d, c, ft, ngt);
            d.lam_fv(t_fv, real, body)
        };
        let sub = d.lemma(c.uniformly_continuous_sub, &[f, gg, a, b, hf, hg]);
        let abs_uc = d.lemma(p.creal_uniformly_continuous_abs, &[difference, a, b, sub]);
        let add_uc = d.lemma(c.uniformly_continuous_add, &[f, gg, a, b, hf, hg]);

        let hi_arg = {
            let t = d.lam_fv(hg_fv, hg_ty, abs_uc);
            let t = d.lam_fv(hf_fv, hf_ty, t);
            let t = d.lam_fv(g_fv, w.carrier, t);
            d.lam_fv(f_fv, w.carrier, t)
        };
        let hadd_arg = {
            let t = d.lam_fv(hg_fv, hg_ty, add_uc);
            let t = d.lam_fv(hf_fv, hf_ty, t);
            let t = d.lam_fv(g_fv, w.carrier, t);
            d.lam_fv(f_fv, w.carrier, t)
        };
        (hi_arg, hadd_arg)
    };

    // `fun F G t _ _ => CReal.abs_nonneg (F t + -G t)`.
    let hnn_arg = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let gt = d.apply(gg, &[t]);
        let ngt = super::rneg(d, c, gt);
        let diff = radd(d, c, ft, ngt);
        let body = d.lemma(c.abs_nonneg, &[diff]);
        let body = wrap(d, t_fv, t, body);
        let inner = d.lam_fv(g_fv, w.carrier, body);
        d.lam_fv(f_fv, w.carrier, inner)
    };

    // `fun F t _ _ => CReal.le_of_equiv _ 0 (Metric.CReal.distSelf (F t) (F t) refl)`.
    let hself_arg = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let nft = super::rneg(d, c, ft);
        let diff = radd(d, c, ft, nft);
        let absdiff = d.const_app(c.abs, &[diff]);
        let zero = rzero(d, c);
        let refl = super::rrefl(d, c, ft);
        let eq = d.lemma(m.creal_dist_self, &[ft, ft, refl]);
        let body = d.lemma(c.le_of_equiv, &[absdiff, zero, eq]);
        let body = wrap(d, t_fv, t, body);
        d.lam_fv(f_fv, w.carrier, body)
    };

    // `fun F G t _ _ => Metric.CReal.absSubLe (F t) (G t)`.
    let hcomm_arg = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let gt = d.apply(gg, &[t]);
        let body = d.lemma(m.creal_abs_sub_le, &[ft, gt]);
        let body = wrap(d, t_fv, t, body);
        let inner = d.lam_fv(g_fv, w.carrier, body);
        d.lam_fv(f_fv, w.carrier, inner)
    };

    // `fun F G H t _ _ => Metric.CReal.distTriangle (F t) (G t) (H t)`.
    let htri_arg = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let h_fv = d.fresh_fvar();
        let hh = d.kernel().fvar(h_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let gt = d.apply(gg, &[t]);
        let ht = d.apply(hh, &[t]);
        let body = d.lemma(m.creal_dist_triangle, &[ft, gt, ht]);
        let body = wrap(d, t_fv, t, body);
        let body = d.lam_fv(h_fv, w.carrier, body);
        let body = d.lam_fv(g_fv, w.carrier, body);
        d.lam_fv(f_fv, w.carrier, body)
    };

    let value = {
        let name = p.l1.bundled_l1;
        let inst = d.const_app(
            name,
            &[
                space, fdist, hi_arg, hadd_arg, hnn_arg, hself_arg, hcomm_arg, htri_arg,
            ],
        );
        let t = d.lam_fv(hab_fv, hab_ty, inst);
        let t = d.lam_fv(b_fv, real, t);
        d.lam_fv(a_fv, real, t)
    };
    let ty = {
        let metric_ty = d.kernel().const_(m.record.ind, vec![]);
        let t = d.pi_fv(hab_fv, hab_ty, metric_ty);
        let t = d.pi_fv(b_fv, real, t);
        d.pi_fv(a_fv, real, t)
    };
    definition(d, p.l1.creal_interval_l1, ty, value)
}

/// `IntSpace.crealFiniteL1 : Nat -> Metric`.
///
/// The same four lattice witnesses as the interval instance — the wrapper is
/// `forall i, i < n -> …` instead of `forall t, a <= t -> t <= b -> …` and
/// nothing else changes — with `hI` and `hAdd` both
/// `fun _ _ _ _ => IntSpace.Triv.mk`, because on a finite index set every
/// function is integrable. Over `IntSpace.crealFinite` the derived measure is
/// COUNTING measure, so this is the L1 distance `E|X - Y|` of the finite
/// probability layer (ADR-1616).
fn declare_creal_finite_l1(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    m: MetricPrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let natp = d.prelude();
    let real = super::rty(d, c);
    let nat = d.nat_ty();
    let w = Pointwise {
        carrier: d.arrow(nat, real),
        point: nat,
    };

    let m_fv = d.fresh_fvar();
    let mm = d.kernel().fvar(m_fv);
    let n = d.succ(mm);
    let space = d.const_app(p.creal_finite, &[mm]);
    let fdist = pointwise_fdist(d, p, &w);

    let triv_ty = d.kernel().const_(p.triv, vec![]);
    let triv_mk = d.kernel().const_(p.triv_mk, vec![]);

    let wrap = |d: &mut IntDev<'_>, i_fv: u64, i: ExprId, body: ExprId| {
        let lt = d.const_app(natp.lt, &[i, n]);
        let h_fv = d.fresh_fvar();
        let body = d.lam_fv(h_fv, lt, body);
        d.lam_fv(i_fv, nat, body)
    };

    // `fun _ _ _ _ => IntSpace.Triv.mk`, for both closure arguments.
    let triv_closure = {
        let f_fv = d.fresh_fvar();
        let g_fv = d.fresh_fvar();
        let h1_fv = d.fresh_fvar();
        let h2_fv = d.fresh_fvar();
        let t = d.lam_fv(h2_fv, triv_ty, triv_mk);
        let t = d.lam_fv(h1_fv, triv_ty, t);
        let t = d.lam_fv(g_fv, w.carrier, t);
        d.lam_fv(f_fv, w.carrier, t)
    };

    let hnn_arg = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(gg, &[i]);
        let ngi = super::rneg(d, c, gi);
        let diff = radd(d, c, fi, ngi);
        let body = d.lemma(c.abs_nonneg, &[diff]);
        let body = wrap(d, i_fv, i, body);
        let inner = d.lam_fv(g_fv, w.carrier, body);
        d.lam_fv(f_fv, w.carrier, inner)
    };

    let hself_arg = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let nfi = super::rneg(d, c, fi);
        let diff = radd(d, c, fi, nfi);
        let absdiff = d.const_app(c.abs, &[diff]);
        let zero = rzero(d, c);
        let refl = super::rrefl(d, c, fi);
        let eq = d.lemma(m.creal_dist_self, &[fi, fi, refl]);
        let body = d.lemma(c.le_of_equiv, &[absdiff, zero, eq]);
        let body = wrap(d, i_fv, i, body);
        d.lam_fv(f_fv, w.carrier, body)
    };

    let hcomm_arg = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(gg, &[i]);
        let body = d.lemma(m.creal_abs_sub_le, &[fi, gi]);
        let body = wrap(d, i_fv, i, body);
        let inner = d.lam_fv(g_fv, w.carrier, body);
        d.lam_fv(f_fv, w.carrier, inner)
    };

    let htri_arg = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let gg = d.kernel().fvar(g_fv);
        let h_fv = d.fresh_fvar();
        let hh = d.kernel().fvar(h_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(gg, &[i]);
        let hi2 = d.apply(hh, &[i]);
        let body = d.lemma(m.creal_dist_triangle, &[fi, gi, hi2]);
        let body = wrap(d, i_fv, i, body);
        let body = d.lam_fv(h_fv, w.carrier, body);
        let body = d.lam_fv(g_fv, w.carrier, body);
        d.lam_fv(f_fv, w.carrier, body)
    };

    let value = {
        let name = p.l1.bundled_l1;
        let inst = d.const_app(
            name,
            &[
                space,
                fdist,
                triv_closure,
                triv_closure,
                hnn_arg,
                hself_arg,
                hcomm_arg,
                htri_arg,
            ],
        );
        d.lam_fv(m_fv, nat, inst)
    };
    let ty = {
        let metric_ty = d.kernel().const_(m.record.ind, vec![]);
        d.pi_fv(m_fv, nat, metric_ty)
    };
    definition(d, p.l1.creal_finite_l1, ty, value)
}

/// `IntSpace.crealIntervalL1_dist : forall a b hab F G hF hG, Eq CReal
/// (Metric.dist (crealIntervalL1 a b hab) (bundle F hF) (bundle G hG))
/// (CReal.integral (fun t => CReal.abs (CReal.add (F t) (CReal.neg (G t))))
///                 a b hab …)`.
///
/// **The claim, made checkable**, by `Eq.refl`: the L1 distance between two
/// bundled functions on `[a,b]` IS the Riemann integral of `|F - G|`. Without
/// this equation the file would only have established that some `Metric` record
/// exists.
fn declare_creal_interval_l1_dist(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    m: MetricPrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let logic = c.rat.int.logic;
    let real = super::rty(d, c);
    let carrier = d.arrow(real, real);
    let one = level_one(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(g_fv);
    let hf_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);
    let hg_ty = d.const_app(c.uniformly_continuous_on, &[gg, a, b]);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let difference = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let gt = d.apply(gg, &[t]);
        let ngt = super::rneg(d, c, gt);
        let body = radd(d, c, ft, ngt);
        d.lam_fv(t_fv, real, body)
    };
    let absdiff = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ft = d.apply(f, &[t]);
        let gt = d.apply(gg, &[t]);
        let ngt = super::rneg(d, c, gt);
        let diff = radd(d, c, ft, ngt);
        let body = d.const_app(c.abs, &[diff]);
        d.lam_fv(t_fv, real, body)
    };
    let witness = {
        let sub = d.lemma(c.uniformly_continuous_sub, &[f, gg, a, b, hf, hg]);
        d.lemma(p.creal_uniformly_continuous_abs, &[difference, a, b, sub])
    };
    let rhs = d.const_app(c.integral, &[absdiff, a, b, hab, witness]);

    let space = d.const_app(p.creal_interval, &[a, b, hab]);
    let lhs = {
        let bundle = p.bundled.bundle;
        let b1 = d.const_app(bundle, &[space, f, hf]);
        let b2 = d.const_app(bundle, &[space, gg, hg]);
        let inst = d.const_app(p.l1.creal_interval_l1, &[a, b, hab]);
        let sel = d.kernel().const_(m.record.sel(crate::METRIC_DIST), vec![]);
        let head = d.apply(sel, &[inst]);
        d.apply(head, &[b1, b2])
    };

    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![one]);
        d.apply(head, &[real, lhs, rhs])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![one]);
        d.apply(head, &[real, rhs])
    };
    let ty = {
        let t = d.pi_fv(hg_fv, hg_ty, stmt);
        let t = d.pi_fv(hf_fv, hf_ty, t);
        let t = d.pi_fv(g_fv, carrier, t);
        let t = d.pi_fv(f_fv, carrier, t);
        let t = d.pi_fv(hab_fv, hab_ty, t);
        let t = d.pi_fv(b_fv, real, t);
        d.pi_fv(a_fv, real, t)
    };
    let value = {
        let t = d.lam_fv(hg_fv, hg_ty, proof);
        let t = d.lam_fv(hf_fv, hf_ty, t);
        let t = d.lam_fv(g_fv, carrier, t);
        let t = d.lam_fv(f_fv, carrier, t);
        let t = d.lam_fv(hab_fv, hab_ty, t);
        let t = d.lam_fv(b_fv, real, t);
        d.lam_fv(a_fv, real, t)
    };
    theorem(d, p.l1.creal_interval_l1_dist, ty, value)
}

/// `IntSpace.crealFiniteL1_dist : forall m f g, Eq CReal
/// (Metric.dist (crealFiniteL1 m) (bundle f Triv.mk) (bundle g Triv.mk))
/// (CReal.sumRange (fun i => CReal.abs (CReal.add (f i) (CReal.neg (g i))))
///                 (Nat.succ m))` — `Eq.refl`.
///
/// The finite counterpart: the L1 distance is `Sigma|f - g|`, which over
/// counting measure is `E|X - Y|`.
fn declare_creal_finite_l1_dist(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    mp: MetricPrelude,
) -> Result<(), KernelError> {
    let c = p.creal;
    let logic = c.rat.int.logic;
    let real = super::rty(d, c);
    let nat = d.nat_ty();
    let carrier = d.arrow(nat, real);
    let one = level_one(d);

    let m_fv = d.fresh_fvar();
    let mm = d.kernel().fvar(m_fv);
    let n = d.succ(mm);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let gg = d.kernel().fvar(g_fv);

    let absdiff = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let gi = d.apply(gg, &[i]);
        let ngi = super::rneg(d, c, gi);
        let diff = radd(d, c, fi, ngi);
        let body = d.const_app(c.abs, &[diff]);
        d.lam_fv(i_fv, nat, body)
    };
    let rhs = d.const_app(c.sum_range, &[absdiff, n]);

    let space = d.const_app(p.creal_finite, &[mm]);
    let triv_mk = d.kernel().const_(p.triv_mk, vec![]);
    let lhs = {
        let bundle = p.bundled.bundle;
        let b1 = d.const_app(bundle, &[space, f, triv_mk]);
        let b2 = d.const_app(bundle, &[space, gg, triv_mk]);
        let inst = d.const_app(p.l1.creal_finite_l1, &[mm]);
        let sel = d.kernel().const_(mp.record.sel(crate::METRIC_DIST), vec![]);
        let head = d.apply(sel, &[inst]);
        d.apply(head, &[b1, b2])
    };

    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![one]);
        d.apply(head, &[real, lhs, rhs])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![one]);
        d.apply(head, &[real, rhs])
    };
    let ty = {
        let t = d.pi_fv(g_fv, carrier, stmt);
        let t = d.pi_fv(f_fv, carrier, t);
        d.pi_fv(m_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(g_fv, carrier, proof);
        let t = d.lam_fv(f_fv, carrier, t);
        d.lam_fv(m_fv, nat, t)
    };
    theorem(d, p.l1.creal_finite_l1_dist, ty, value)
}

/// Land every declaration this file owns, in dependency order.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection. An `Err` from a
/// `Theorem` here means the kernel **refused** a proof.
pub(super) fn declare_all(
    d: &mut IntDev<'_>,
    p: IntSpacePrelude,
    m: MetricPrelude,
) -> Result<(), KernelError> {
    declare_l1_dist(d, p)?;
    declare_l1_equiv(d, p)?;
    declare_l1_dist_bundle(d, p)?;
    declare_l1_dist_nonneg(d, p)?;
    declare_l1_dist_self(d, p)?;
    declare_l1_dist_comm(d, p)?;
    declare_l1_dist_triangle(d, p)?;
    declare_l1_equiv_refl(d, p)?;
    declare_l1_equiv_symm(d, p)?;
    declare_l1_equiv_trans(d, p)?;
    declare_l1_dist_le_of_equiv(d, p)?;
    declare_l1_dist_congr(d, p)?;
    declare_bundled_l1(d, p, m)?;
    declare_bundled_l1_carrier(d, p, m)?;
    declare_bundled_l1_dist(d, p, m)?;
    declare_creal_interval_l1(d, p, m)?;
    declare_creal_interval_l1_dist(d, p, m)?;
    declare_creal_finite_l1(d, p, m)?;
    declare_creal_finite_l1_dist(d, p, m)
}
