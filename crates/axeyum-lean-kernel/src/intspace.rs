//! `IntSpace.*` — a constructive **integration space**, and measure derived
//! from the integral rather than the other way round.
//!
//! Roadmap W3-1 (reviewers 03.4 and 08.5), decided in ADR-1612.
//!
//! ## The inversion this module tests
//!
//! Classically, measure comes first and the integral second. Bishop inverts
//! it (*Constructive Analysis*, ch. 6): the **integral is primitive**, and the
//! measure of a set is the integral of its indicator *when that indicator is
//! integrable*. Not every set has one, and that is the constructive content —
//! so "integrable set" has to be a **positive** notion, never the absence of
//! an obstruction.
//!
//! The reason to try it here rather than argue about it: the library already
//! had most of an integration space and called it Riemann integration.
//! `CReal.integral` carries linearity (`integral_add`, `integral_scale`,
//! `integral_const`), monotonicity (`integral_le`) and witness independence
//! (`integral_witness_independent`), and every one of those is a statement
//! about a linear functional on a partially ordered set of functions, with no
//! Riemann sum in it.
//!
//! ## Field layout
//!
//! | # | field | type |
//! |---|---|---|
//! | 0 | `carrier` | `Sort 1` — the functions being integrated |
//! | 1 | `fle` | `carrier → carrier → Prop` |
//! | 2 | `fleRefl` | `∀ f, fle f f` |
//! | 3 | `fleTrans` | `∀ f g h, fle f g → fle g h → fle f h` |
//! | 4 | `fadd` | `carrier → carrier → carrier` |
//! | 5 | `fscale` | `CReal → carrier → carrier` |
//! | 6 | `fconst` | `CReal → carrier` |
//! | 7 | `constMono` | `∀ x y, CReal.le x y → fle (fconst x) (fconst y)` |
//! | 8 | `Integrable` | `carrier → Sort 1` |
//! | 9 | `constIntegrable` | `∀ c, Integrable (fconst c)` |
//! | 10 | `integral` | `∀ f, Integrable f → CReal` |
//! | 11 | `total` | `CReal` |
//! | 12 | `integralConst` | `∀ c h, Equiv (integral (fconst c) h) (mul c total)` |
//! | 13 | `integralLe` | `∀ f g hf hg, fle f g → le (integral f hf) (integral g hg)` |
//! | 14 | `integralAdd` | `∀ f g hf hg hfg, Equiv (integral (fadd f g) hfg) (add (integral f hf) (integral g hg))` |
//! | 15 | `integralScale` | `∀ c f hf hcf, Equiv (integral (fscale c f) hcf) (mul c (integral f hf))` |
//!
//! Three things about that table are decisions, not transcription:
//!
//! **`Integrable` is `Sort 1`, not `Prop`.** `CReal.UniformlyContinuousOn` is
//! a `Type` — a modulus paired with its spec — because `CReal.integral`
//! *consumes* the modulus to build the value. An integration space over this
//! kernel therefore cannot make integrability a proposition without losing
//! the integral, and the consequences run through the whole module: an
//! "integrable set" cannot be bundled into one object (`Sigma` and `Subtype`
//! are absent from this kernel, ADR-1595, and `declare_record` is fixed at
//! `Sort 2`), so it is carried as a `Sort 1` integrability datum plus a
//! `Prop`-valued `IntSpace.Indicator` side condition.
//!
//! **Every integral law takes its own integrability witnesses as explicit
//! arguments**, exactly the shape `CReal.integral_add` and
//! `CReal.integral_scale` already have. The alternative — closure fields
//! (`Integrable f → Integrable g → Integrable (fadd f g)`) — is a stronger
//! axiom than the existing theorems prove, and it is not needed: witness
//! independence makes the choice of witness immaterial, and it is
//! *derived* here rather than assumed.
//!
//! **`fconst` and `total`, not `fone`.** The library's evaluation law is
//! `CReal.integral_const`, whose statement is `∫c = c·(b−a)`. Making the
//! constant embedding and the measure of the whole space fields turns that
//! single existing theorem into field 12 verbatim, and it is what the
//! `integral_le_const` family and the measure bounds are built from.
//!
//! ## What is NOT a field, and why
//!
//! Domain additivity (`CReal.integral_split`, `integralSplitAnywhere`,
//! `integralSplitArbitrary`) relates **three different integration spaces**
//! — over `[a,b]`, `[a,c]` and `[c,b]` — and no statement about one space can
//! express it. The Riemann-sum machinery (`riemannSum_*`, some thirty-five
//! lemmas) and the fundamental theorem of calculus (which varies the
//! endpoint) are outside for the same reason. ADR-1612 counts them.

// `IntSpacePrelude` is a `Copy` handle carrying the whole `CRealPrelude` plus
// the record's fixed-size selector array, so it is large and every `declare_*`
// below trips `large_types_passed_by_value`. Same shape, same suppression and
// the same reason as `metric.rs`, `creal.rs` and `complex.rs`: these are long,
// straight-line term constructions and the handle is a `Copy` snapshot by
// design.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use crate::CRealPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::{
    FieldKind, FieldSpec, RecordNames, arrow, declare_record, pi_over,
};

// ---------------------------------------------------------------------------
// Field indices. Fixed across the record; index a field through these, never
// with a bare integer.
// ---------------------------------------------------------------------------

/// `IntSpace.carrier`.
pub const CARRIER: usize = 0;
/// `IntSpace.fle`.
pub const FLE: usize = 1;
/// `IntSpace.fleRefl`.
pub const FLE_REFL: usize = 2;
/// `IntSpace.fleTrans`.
pub const FLE_TRANS: usize = 3;
/// `IntSpace.fadd`.
pub const FADD: usize = 4;
/// `IntSpace.fscale`.
pub const FSCALE: usize = 5;
/// `IntSpace.fconst`.
pub const FCONST: usize = 6;
/// `IntSpace.constMono`.
pub const CONST_MONO: usize = 7;
/// `IntSpace.Integrable`.
pub const INTEGRABLE: usize = 8;
/// `IntSpace.constIntegrable`.
pub const CONST_INTEGRABLE: usize = 9;
/// `IntSpace.integral`.
pub const INTEGRAL: usize = 10;
/// `IntSpace.total`.
pub const TOTAL: usize = 11;
/// `IntSpace.integralConst`.
pub const INTEGRAL_CONST: usize = 12;
/// `IntSpace.integralLe`.
pub const INTEGRAL_LE: usize = 13;
/// `IntSpace.integralAdd`.
pub const INTEGRAL_ADD: usize = 14;
/// `IntSpace.integralScale`.
pub const INTEGRAL_SCALE: usize = 15;

/// The number of fields the record carries.
pub const FIELD_COUNT: usize = 16;

// Free-variable ids used inside the field-shape closures. Disjoint from
// `structures::CTOR_FVAR_BASE` (10_000), `SELECTOR_S_FV` (10_900) and
// `metric.rs`'s own block (20_800..20_805).
const F_F: u64 = 21_800;
const F_G: u64 = 21_801;
const F_H: u64 = 21_802;
const F_C: u64 = 21_803;
const F_X: u64 = 21_804;
const F_Y: u64 = 21_805;
const F_HF: u64 = 21_806;
const F_HG: u64 = 21_807;
const F_HFG: u64 = 21_808;

// ---------------------------------------------------------------------------
// Small term builders.
// ---------------------------------------------------------------------------

fn capp(k: &mut Kernel, name: NameId, args: &[ExprId]) -> ExprId {
    let mut e = k.const_(name, vec![]);
    for &a in args {
        e = k.app(e, a);
    }
    e
}

fn app_all(k: &mut Kernel, head: ExprId, args: &[ExprId]) -> ExprId {
    let mut e = head;
    for &a in args {
        e = k.app(e, a);
    }
    e
}

// ---------------------------------------------------------------------------
// Field shapes.
// ---------------------------------------------------------------------------

fn carrier_field() -> FieldSpec {
    FieldSpec {
        suffix: "carrier",
        kind: FieldKind::CarrierSort,
        build: Box::new(|k, _lg, l1, _vals| k.sort(l1)),
    }
}

/// `carrier -> carrier -> Prop`.
fn fle_field() -> FieldSpec {
    FieldSpec {
        suffix: "fle",
        kind: FieldKind::Data,
        build: Box::new(|k, _lg, _l1, vals| {
            let a = vals[CARRIER];
            let l0 = k.level_zero();
            let prop = k.sort(l0);
            let inner = arrow(k, a, prop);
            arrow(k, a, inner)
        }),
    }
}

/// `forall f, fle f f`.
fn fle_refl_field() -> FieldSpec {
    FieldSpec {
        suffix: "fleRefl",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[FLE];
            let f = k.fvar(F_F);
            let body = app_all(k, le, &[f, f]);
            pi_over(k, F_F, ty, body)
        }),
    }
}

/// `forall f g h, fle f g -> fle g h -> fle f h`.
fn fle_trans_field() -> FieldSpec {
    FieldSpec {
        suffix: "fleTrans",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[FLE];
            let f = k.fvar(F_F);
            let g = k.fvar(F_G);
            let h = k.fvar(F_H);
            let fg = app_all(k, le, &[f, g]);
            let gh = app_all(k, le, &[g, h]);
            let fh = app_all(k, le, &[f, h]);
            let inner = arrow(k, gh, fh);
            let imp = arrow(k, fg, inner);
            let t = pi_over(k, F_H, ty, imp);
            let t = pi_over(k, F_G, ty, t);
            pi_over(k, F_F, ty, t)
        }),
    }
}

/// `carrier -> carrier -> carrier`.
fn fadd_field() -> FieldSpec {
    FieldSpec {
        suffix: "fadd",
        kind: FieldKind::Data,
        build: Box::new(|k, _lg, _l1, vals| {
            let a = vals[CARRIER];
            let inner = arrow(k, a, a);
            arrow(k, a, inner)
        }),
    }
}

/// `CReal -> carrier -> carrier`.
fn fscale_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "fscale",
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a = vals[CARRIER];
            let r = k.const_(creal.creal, vec![]);
            let inner = arrow(k, a, a);
            arrow(k, r, inner)
        }),
    }
}

/// `CReal -> carrier`.
fn fconst_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "fconst",
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a = vals[CARRIER];
            let r = k.const_(creal.creal, vec![]);
            arrow(k, r, a)
        }),
    }
}

/// `forall x y, CReal.le x y -> fle (fconst x) (fconst y)`.
fn const_mono_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "constMono",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let le = vals[FLE];
            let fconst = vals[FCONST];
            let r = k.const_(creal.creal, vec![]);
            let x = k.fvar(F_X);
            let y = k.fvar(F_Y);
            let hyp = capp(k, creal.le, &[x, y]);
            let cx = app_all(k, fconst, &[x]);
            let cy = app_all(k, fconst, &[y]);
            let concl = app_all(k, le, &[cx, cy]);
            let imp = arrow(k, hyp, concl);
            let t = pi_over(k, F_Y, r, imp);
            pi_over(k, F_X, r, t)
        }),
    }
}

/// `carrier -> Sort 1` — integrability is DATA, not a proposition. See the
/// module docs.
fn integrable_field() -> FieldSpec {
    FieldSpec {
        suffix: "Integrable",
        // The type `carrier -> Sort 1` lives at `Sort 2`, so its selector's
        // motive has to be eliminated at `l2` — the same level the carrier
        // field itself needs.
        kind: FieldKind::CarrierSort,
        build: Box::new(|k, _lg, l1, vals| {
            let a = vals[CARRIER];
            let s1 = k.sort(l1);
            arrow(k, a, s1)
        }),
    }
}

/// `forall (c : CReal), Integrable (fconst c)`.
fn const_integrable_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "constIntegrable",
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let fconst = vals[FCONST];
            let integrable = vals[INTEGRABLE];
            let r = k.const_(creal.creal, vec![]);
            let c = k.fvar(F_C);
            let cc = app_all(k, fconst, &[c]);
            let body = app_all(k, integrable, &[cc]);
            pi_over(k, F_C, r, body)
        }),
    }
}

/// `forall (f : carrier), Integrable f -> CReal`.
fn integral_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "integral",
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let integrable = vals[INTEGRABLE];
            let r = k.const_(creal.creal, vec![]);
            let f = k.fvar(F_F);
            let hyp = app_all(k, integrable, &[f]);
            let inner = arrow(k, hyp, r);
            pi_over(k, F_F, ty, inner)
        }),
    }
}

/// `CReal` — the measure of the whole space.
fn total_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "total",
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, _vals| k.const_(creal.creal, vec![])),
    }
}

/// `forall c h, CReal.Equiv (integral (fconst c) h) (CReal.mul c total)`.
fn integral_const_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "integralConst",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let fconst = vals[FCONST];
            let integrable = vals[INTEGRABLE];
            let integral = vals[INTEGRAL];
            let total = vals[TOTAL];
            let r = k.const_(creal.creal, vec![]);
            let c = k.fvar(F_C);
            let cc = app_all(k, fconst, &[c]);
            let hty = app_all(k, integrable, &[cc]);
            let h = k.fvar(F_HF);
            let lhs = app_all(k, integral, &[cc, h]);
            let rhs = capp(k, creal.mul, &[c, total]);
            let concl = capp(k, creal.equiv, &[lhs, rhs]);
            let t = pi_over(k, F_HF, hty, concl);
            pi_over(k, F_C, r, t)
        }),
    }
}

/// `forall f g hf hg, fle f g -> CReal.le (integral f hf) (integral g hg)`.
fn integral_le_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "integralLe",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let le = vals[FLE];
            let integrable = vals[INTEGRABLE];
            let integral = vals[INTEGRAL];
            let f = k.fvar(F_F);
            let g = k.fvar(F_G);
            let hf_ty = app_all(k, integrable, &[f]);
            let hg_ty = app_all(k, integrable, &[g]);
            let hf = k.fvar(F_HF);
            let hg = k.fvar(F_HG);
            let hyp = app_all(k, le, &[f, g]);
            let lhs = app_all(k, integral, &[f, hf]);
            let rhs = app_all(k, integral, &[g, hg]);
            let concl = capp(k, creal.le, &[lhs, rhs]);
            let imp = arrow(k, hyp, concl);
            let t = pi_over(k, F_HG, hg_ty, imp);
            let t = pi_over(k, F_HF, hf_ty, t);
            let t = pi_over(k, F_G, ty, t);
            pi_over(k, F_F, ty, t)
        }),
    }
}

/// `forall f g hf hg hfg,
/// CReal.Equiv (integral (fadd f g) hfg)
///   (CReal.add (integral f hf) (integral g hg))`.
fn integral_add_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "integralAdd",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let fadd = vals[FADD];
            let integrable = vals[INTEGRABLE];
            let integral = vals[INTEGRAL];
            let f = k.fvar(F_F);
            let g = k.fvar(F_G);
            let sum = app_all(k, fadd, &[f, g]);
            let hf_ty = app_all(k, integrable, &[f]);
            let hg_ty = app_all(k, integrable, &[g]);
            let hfg_ty = app_all(k, integrable, &[sum]);
            let hf = k.fvar(F_HF);
            let hg = k.fvar(F_HG);
            let hfg = k.fvar(F_HFG);
            let lhs = app_all(k, integral, &[sum, hfg]);
            let if_ = app_all(k, integral, &[f, hf]);
            let ig = app_all(k, integral, &[g, hg]);
            let rhs = capp(k, creal.add, &[if_, ig]);
            let concl = capp(k, creal.equiv, &[lhs, rhs]);
            let t = pi_over(k, F_HFG, hfg_ty, concl);
            let t = pi_over(k, F_HG, hg_ty, t);
            let t = pi_over(k, F_HF, hf_ty, t);
            let t = pi_over(k, F_G, ty, t);
            pi_over(k, F_F, ty, t)
        }),
    }
}

/// `forall c f hf hcf,
/// CReal.Equiv (integral (fscale c f) hcf) (CReal.mul c (integral f hf))`.
fn integral_scale_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "integralScale",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let fscale = vals[FSCALE];
            let integrable = vals[INTEGRABLE];
            let integral = vals[INTEGRAL];
            let r = k.const_(creal.creal, vec![]);
            let c = k.fvar(F_C);
            let f = k.fvar(F_F);
            let scaled = app_all(k, fscale, &[c, f]);
            let hf_ty = app_all(k, integrable, &[f]);
            let hcf_ty = app_all(k, integrable, &[scaled]);
            let hf = k.fvar(F_HF);
            let hcf = k.fvar(F_HFG);
            let lhs = app_all(k, integral, &[scaled, hcf]);
            let if_ = app_all(k, integral, &[f, hf]);
            let rhs = capp(k, creal.mul, &[c, if_]);
            let concl = capp(k, creal.equiv, &[lhs, rhs]);
            let t = pi_over(k, F_HFG, hcf_ty, concl);
            let t = pi_over(k, F_HF, hf_ty, t);
            let t = pi_over(k, F_F, ty, t);
            pi_over(k, F_C, r, t)
        }),
    }
}

fn intspace_fields(creal: CRealPrelude) -> Vec<FieldSpec> {
    vec![
        carrier_field(),
        fle_field(),
        fle_refl_field(),
        fle_trans_field(),
        fadd_field(),
        fscale_field(creal),
        fconst_field(creal),
        const_mono_field(creal),
        integrable_field(),
        const_integrable_field(creal),
        integral_field(creal),
        total_field(creal),
        integral_const_field(creal),
        integral_le_field(creal),
        integral_add_field(creal),
        integral_scale_field(creal),
    ]
}

// ---------------------------------------------------------------------------
// The prelude handle.
// ---------------------------------------------------------------------------

/// The interned names produced by [`build_intspace_prelude`].
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntSpacePrelude {
    /// The reals this development's integrals are valued in.
    pub creal: CRealPrelude,
    /// The `IntSpace` record: its inductive, `mk`, `rec` and sixteen
    /// selectors.
    pub record: RecordNames,

    /// The bundled-carrier layer (`intspace/bundled.rs`, ADR-1613): a function
    /// packaged with its integrability datum through `Sigma`, so the integral
    /// becomes a total function of one argument.
    pub bundled: bundled::BundledNames,

    /// The L¹ layer (`intspace/l1.rs`, ADR-1625): the L¹ seminorm on the
    /// bundled carrier, its setoid, and the `Metric` instance built from them.
    pub l1: l1::L1Names,

    /// `IntSpace.Triv : Sort 1` — a one-constructor `Type`, the integrability
    /// datum of a space where **every** function is integrable. `True` will
    /// not do: `Integrable` is `Sort 1`-valued and `True : Prop`.
    pub triv: NameId,
    /// `IntSpace.Triv.mk : IntSpace.Triv`.
    pub triv_mk: NameId,
    /// `IntSpace.Triv.rec` — the kernel-generated recursor. Named here only
    /// so `every_live_intspace_declaration_is_listed` can see it: the
    /// environment check found it live and unlisted, which is what an
    /// auto-generated declaration does to a handle-derived list.
    pub triv_rec: NameId,

    /// `IntSpace.integral_congr : ∀ S f g hf hg, S.fle f g → S.fle g f →
    /// CReal.Equiv (S.integral f hf) (S.integral g hg)` — the integrand
    /// congruence `CReal.integral` never had, derived from monotonicity alone
    /// by antisymmetry.
    pub integral_congr: NameId,
    /// `IntSpace.integral_witness_independent : ∀ S f h1 h2,
    /// CReal.Equiv (S.integral f h1) (S.integral f h2)` — derived, not
    /// assumed.
    pub integral_witness_independent: NameId,
    /// `IntSpace.integral_le_const : ∀ S M f hf, S.fle f (S.fconst M) →
    /// CReal.le (S.integral f hf) (CReal.mul M S.total)`.
    pub integral_le_const: NameId,
    /// `IntSpace.const_le_integral : ∀ S M f hf, S.fle (S.fconst M) f →
    /// CReal.le (CReal.mul M S.total) (S.integral f hf)`.
    pub const_le_integral: NameId,
    /// `IntSpace.integral_nonneg : ∀ S f hf,
    /// S.fle (S.fconst CReal.zero) f → CReal.le CReal.zero (S.integral f hf)`.
    pub integral_nonneg: NameId,
    /// `IntSpace.integral_le_total : ∀ S f hf,
    /// S.fle f (S.fconst CReal.one) → CReal.le (S.integral f hf) S.total`.
    pub integral_le_total: NameId,

    /// `IntSpace.FEquiv S f g := And (S.fle f g) (S.fle g f)`.
    pub fequiv: NameId,
    /// `IntSpace.fequiv_refl : ∀ S f, FEquiv S f f`.
    pub fequiv_refl: NameId,
    /// `IntSpace.fequiv_symm : ∀ S f g, FEquiv S f g → FEquiv S g f`.
    pub fequiv_symm: NameId,
    /// `IntSpace.fequiv_trans : ∀ S f g h,
    /// FEquiv S f g → FEquiv S g h → FEquiv S f h`.
    pub fequiv_trans: NameId,
    /// `IntSpace.integral_fequiv_congr : ∀ S f g hf hg, FEquiv S f g →
    /// CReal.Equiv (S.integral f hf) (S.integral g hg)`.
    pub integral_fequiv_congr: NameId,

    /// `IntSpace.Indicator S chi := And (S.fle (S.fconst CReal.zero) chi)
    /// (S.fle chi (S.fconst CReal.one))` — the positive side condition that
    /// makes an integrable function the indicator of an integrable set.
    pub indicator: NameId,
    /// `IntSpace.measure S chi h := S.integral chi h` — the measure of the
    /// set whose indicator is `chi`, defined only where the integrability
    /// datum `h` exists.
    pub measure: NameId,
    /// `IntSpace.measure_nonneg : ∀ S chi h, Indicator S chi →
    /// CReal.le CReal.zero (measure S chi h)`.
    pub measure_nonneg: NameId,
    /// `IntSpace.measure_le_total : ∀ S chi h, Indicator S chi →
    /// CReal.le (measure S chi h) S.total`.
    pub measure_le_total: NameId,
    /// `IntSpace.measure_witness_independent : ∀ S chi h1 h2,
    /// CReal.Equiv (measure S chi h1) (measure S chi h2)`.
    pub measure_witness_independent: NameId,
    /// `IntSpace.measure_const : ∀ S c h,
    /// CReal.Equiv (measure S (S.fconst c) h) (CReal.mul c S.total)`.
    pub measure_const: NameId,
    /// `IntSpace.indicator_univ : ∀ S, Indicator S (S.fconst CReal.one)`.
    pub indicator_univ: NameId,
    /// `IntSpace.measure_univ : ∀ S h,
    /// CReal.Equiv (measure S (S.fconst CReal.one) h) S.total`.
    pub measure_univ: NameId,

    /// `IntSpace.MonotoneSeq S u := ∀ n, S.fle (u n) (u (Nat.succ n))`.
    pub monotone_seq: NameId,
    /// `IntSpace.integral_mono_step` — the constructive half of monotone
    /// convergence: the integrals increase.
    pub integral_mono_step: NameId,
    /// `IntSpace.integral_seq_le` — the constructive bound.
    pub integral_seq_le: NameId,
    /// `IntSpace.RealMonotoneConvergence : Prop` — every bounded monotone
    /// sequence of reals converges. **Not** provable here; the classical
    /// principle, carried as a hypothesis per ADR-1601.
    pub real_monotone_convergence: NameId,
    /// `IntSpace.MonotoneConvergence S : Prop`.
    pub monotone_convergence: NameId,
    /// `IntSpace.monotone_convergence_of_real : ∀ S,
    /// RealMonotoneConvergence → MonotoneConvergence S` — the graded family's
    /// classical member, at a cost of one binder.
    pub monotone_convergence_of_real: NameId,

    /// `IntSpace.crealInterval : ∀ (a b : CReal), CReal.le a b → IntSpace`.
    pub creal_interval: NameId,
    /// `IntSpace.crealInterval_integral` — the reduction probe: proved by
    /// `CReal.equiv_refl`, so its admission IS the statement that the
    /// `integral` selector reduces definitionally on the instance.
    pub creal_interval_integral: NameId,
    /// `IntSpace.crealInterval_total` — the second reduction probe.
    pub creal_interval_total: NameId,

    /// `IntSpace.crealFinite : Nat → IntSpace` — `CReal.sumRange` over
    /// `Nat.succ m` indices.
    pub creal_finite: NameId,
    /// `IntSpace.crealFinite_integral` — the finite instance's reduction
    /// probe.
    pub creal_finite_integral: NameId,

    /// ADR-1616: `IntSpace.crealFinite_expectation` — the ℝ-valued finite
    /// expectation IS the `crealFinite` integral.
    pub creal_finite_expectation: NameId,
    /// ADR-1616: `IntSpace.ratExpectation_integral` — the RATIONAL
    /// expectation is that integral, carried across `CReal.ofRat`. The join
    /// ADR-1612 named as its next step; see
    /// [`probability_bridge`](self::probability_bridge) for why the
    /// `ℚ`-valued form cannot be stated at all.
    pub rat_expectation_integral: NameId,

    /// `IntSpace.CReal.integral_witness_independent` — `CReal`'s own theorem,
    /// re-derived as the generic one at `crealInterval`.
    pub creal_witness_independent: NameId,
    /// `IntSpace.CReal.integral_congr` — new content on ℝ.
    pub creal_integral_congr: NameId,
    /// `IntSpace.CReal.integral_nonneg` — new content on ℝ.
    pub creal_integral_nonneg: NameId,
    /// `IntSpace.CReal.sumRange_congr` — the same generic congruence on the
    /// FINITE instance, where it is about `CReal.sumRange`.
    pub creal_sum_range_congr: NameId,
    /// `IntSpace.CReal.sumRange_nonneg` — likewise.
    pub creal_sum_range_nonneg: NameId,

    // --- detachable subsets, counting measure, and the Dirac space ---------
    /// `IntSpace.boolIndicator : Bool → CReal` — `1` at `true`, `0` at
    /// `false`. The indicator of a DETACHABLE subset is genuinely
    /// `Bool`-valued and computes.
    pub bool_indicator: NameId,
    /// `IntSpace.boolIndicator_nonneg : ∀ b, CReal.le CReal.zero
    /// (boolIndicator b)`.
    pub bool_indicator_nonneg: NameId,
    /// `IntSpace.boolIndicator_le_one : ∀ b,
    /// CReal.le (boolIndicator b) CReal.one`.
    pub bool_indicator_le_one: NameId,
    /// `IntSpace.detachableIndicator : (Nat → Bool) → Nat → CReal`.
    pub detachable_indicator: NameId,
    /// `IntSpace.detachable_is_indicator : ∀ A m,
    /// Indicator (crealFinite m) (detachableIndicator A)` — every detachable
    /// subset of a finite index set is an integrable set.
    pub detachable_is_indicator: NameId,
    /// `IntSpace.countingMeasure : (Nat → Bool) → Nat → CReal`.
    pub counting_measure: NameId,
    /// `IntSpace.countingMeasure_nonneg`.
    pub counting_measure_nonneg: NameId,
    /// `IntSpace.countingMeasure_le_total`.
    pub counting_measure_le_total: NameId,
    /// `IntSpace.crealDirac : Nat → IntSpace` — evaluation at `k`, with
    /// `total = 1`: a probability integration space.
    pub creal_dirac: NameId,
    /// `IntSpace.crealDirac_integral` — the Dirac reduction probe.
    pub creal_dirac_integral: NameId,
    /// `IntSpace.crealDirac_total : ∀ k,
    /// CReal.Equiv (crealDirac k).total CReal.one`.
    pub creal_dirac_total: NameId,
    /// `IntSpace.dirac_measure_detachable` — the Dirac measure of a
    /// detachable set, by `CReal.Equiv.refl`.
    pub dirac_measure_detachable: NameId,

    /// `IntSpace.CReal.uniformly_continuous_abs : ∀ F a b,
    /// CReal.UniformlyContinuousOn F a b →
    /// CReal.UniformlyContinuousOn (fun t => CReal.abs (F t)) a b`.
    ///
    /// **A blocker this lane claimed and then refuted.** `\|·\|` closure was
    /// recorded as the missing lemma standing between `IntSpace` and a
    /// Petrakis–Zeuner pre-integration space (whose `L` is closed under the
    /// lattice operations) and between the interval space and the L¹
    /// seminorm. A name search says it is absent. `shape_search
    /// --concl CReal.UniformlyContinuousOn` says the STEP is present:
    /// `CReal.abs` is `max x (neg x)` by definition and
    /// `CReal.uniformly_continuous_max` and `_neg` both exist, so this is
    /// their composition and no new estimate. Searching for the step, not the
    /// name — the rule, applied to a blocker this lane wrote down itself.
    pub creal_uniformly_continuous_abs: NameId,
}

// ---------------------------------------------------------------------------
// Name interning.
// ---------------------------------------------------------------------------

/// The record's field suffixes, in declaration order. Used both to build the
/// record and to re-intern its selectors on the already-declared path.
const FIELD_SUFFIXES: [&str; FIELD_COUNT] = [
    "carrier",
    "fle",
    "fleRefl",
    "fleTrans",
    "fadd",
    "fscale",
    "fconst",
    "constMono",
    "Integrable",
    "constIntegrable",
    "integral",
    "total",
    "integralConst",
    "integralLe",
    "integralAdd",
    "integralScale",
];

fn intern(kernel: &mut Kernel, creal: CRealPrelude) -> IntSpacePrelude {
    let root = kernel.anon();
    let ns = kernel.name_str(root, "IntSpace");
    let creal_ns = kernel.name_str(ns, "CReal");
    let triv = kernel.name_str(ns, "Triv");

    let mk = kernel.name_str(ns, "mk");
    let rec = kernel.name_str(ns, "rec");
    let mut selectors = [mk; crate::nat_prelude::structures::MAX_FIELDS];
    for (i, suffix) in FIELD_SUFFIXES.iter().enumerate() {
        selectors[i] = kernel.name_str(ns, *suffix);
    }
    let record = RecordNames {
        ind: ns,
        mk,
        rec,
        selectors,
        len: FIELD_COUNT,
    };

    IntSpacePrelude {
        creal,
        record,
        bundled: bundled::intern(kernel, ns),
        l1: l1::intern(kernel, ns),
        triv,
        triv_mk: kernel.name_str(triv, "mk"),
        triv_rec: kernel.name_str(triv, "rec"),
        integral_congr: kernel.name_str(ns, "integral_congr"),
        integral_witness_independent: kernel.name_str(ns, "integral_witness_independent"),
        integral_le_const: kernel.name_str(ns, "integral_le_const"),
        const_le_integral: kernel.name_str(ns, "const_le_integral"),
        integral_nonneg: kernel.name_str(ns, "integral_nonneg"),
        integral_le_total: kernel.name_str(ns, "integral_le_total"),
        fequiv: kernel.name_str(ns, "FEquiv"),
        fequiv_refl: kernel.name_str(ns, "fequiv_refl"),
        fequiv_symm: kernel.name_str(ns, "fequiv_symm"),
        fequiv_trans: kernel.name_str(ns, "fequiv_trans"),
        integral_fequiv_congr: kernel.name_str(ns, "integral_fequiv_congr"),
        indicator: kernel.name_str(ns, "Indicator"),
        measure: kernel.name_str(ns, "measure"),
        measure_nonneg: kernel.name_str(ns, "measure_nonneg"),
        measure_le_total: kernel.name_str(ns, "measure_le_total"),
        measure_witness_independent: kernel.name_str(ns, "measure_witness_independent"),
        measure_const: kernel.name_str(ns, "measure_const"),
        indicator_univ: kernel.name_str(ns, "indicator_univ"),
        measure_univ: kernel.name_str(ns, "measure_univ"),
        monotone_seq: kernel.name_str(ns, "MonotoneSeq"),
        integral_mono_step: kernel.name_str(ns, "integral_mono_step"),
        integral_seq_le: kernel.name_str(ns, "integral_seq_le"),
        real_monotone_convergence: kernel.name_str(ns, "RealMonotoneConvergence"),
        monotone_convergence: kernel.name_str(ns, "MonotoneConvergence"),
        monotone_convergence_of_real: kernel.name_str(ns, "monotone_convergence_of_real"),
        creal_interval: kernel.name_str(ns, "crealInterval"),
        creal_interval_integral: kernel.name_str(ns, "crealInterval_integral"),
        creal_interval_total: kernel.name_str(ns, "crealInterval_total"),
        creal_finite: kernel.name_str(ns, "crealFinite"),
        creal_finite_integral: kernel.name_str(ns, "crealFinite_integral"),
        creal_finite_expectation: kernel.name_str(ns, "crealFinite_expectation"),
        rat_expectation_integral: kernel.name_str(ns, "ratExpectation_integral"),
        creal_witness_independent: kernel.name_str(creal_ns, "integral_witness_independent"),
        creal_integral_congr: kernel.name_str(creal_ns, "integral_congr"),
        creal_integral_nonneg: kernel.name_str(creal_ns, "integral_nonneg"),
        creal_sum_range_congr: kernel.name_str(creal_ns, "sumRange_congr"),
        creal_sum_range_nonneg: kernel.name_str(creal_ns, "sumRange_nonneg"),
        bool_indicator: kernel.name_str(ns, "boolIndicator"),
        bool_indicator_nonneg: kernel.name_str(ns, "boolIndicator_nonneg"),
        bool_indicator_le_one: kernel.name_str(ns, "boolIndicator_le_one"),
        detachable_indicator: kernel.name_str(ns, "detachableIndicator"),
        detachable_is_indicator: kernel.name_str(ns, "detachable_is_indicator"),
        counting_measure: kernel.name_str(ns, "countingMeasure"),
        counting_measure_nonneg: kernel.name_str(ns, "countingMeasure_nonneg"),
        counting_measure_le_total: kernel.name_str(ns, "countingMeasure_le_total"),
        creal_dirac: kernel.name_str(ns, "crealDirac"),
        creal_dirac_integral: kernel.name_str(ns, "crealDirac_integral"),
        creal_dirac_total: kernel.name_str(ns, "crealDirac_total"),
        dirac_measure_detachable: kernel.name_str(ns, "dirac_measure_detachable"),
        creal_uniformly_continuous_abs: kernel.name_str(creal_ns, "uniformly_continuous_abs"),
    }
}

/// Build (or return, if already built) the `IntSpace.*` declarations.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
///
/// # Panics
///
/// Panics if the field-shape list has drifted from [`FIELD_COUNT`], or if
/// [`declare_record`] returns selectors under names other than the ones
/// `intern` pre-computed. Both are internal-consistency assertions between
/// this file's two descriptions of the same record.
pub fn build_intspace_prelude(kernel: &mut Kernel) -> Result<IntSpacePrelude, KernelError> {
    let creal = crate::build_creal_prelude(kernel)?;
    // ADR-1625: the L¹ layer builds a `Metric`, so the metric prelude is now a
    // dependency of this one. `Metric` does not depend on `IntSpace`, so there
    // is no cycle; both builders are idempotent.
    let metric = crate::build_metric_prelude(kernel)?;
    let p = intern(kernel, creal);
    if kernel.environment().get(p.record.ind).is_some() {
        return Ok(p);
    }

    let l0 = kernel.level_zero();
    let l1 = kernel.level_succ(l0);
    let l2 = kernel.level_succ(l1);
    let logic = creal.rat.int.logic;

    // The trivial integrability datum, declared BEFORE the record so the
    // finite instance can name it.
    {
        let sort1 = kernel.sort(l1);
        let triv_const = kernel.const_(p.triv, vec![]);
        kernel.add_inductive(p.triv, &[], 0, sort1, &[(p.triv_mk, triv_const)])?;
    }

    let specs = intspace_fields(creal);
    assert_eq!(
        specs.len(),
        FIELD_COUNT,
        "field list out of step with FIELD_COUNT"
    );
    let record = declare_record(kernel, &logic, l0, l1, l2, p.record.ind, &specs)?;
    assert_eq!(
        record.field_count(),
        FIELD_COUNT,
        "declare_record produced the wrong field count"
    );
    for (i, suffix) in FIELD_SUFFIXES.iter().enumerate() {
        assert_eq!(
            record.sel(i),
            p.record.sel(i),
            "selector {i} ({suffix}) was interned under a different name"
        );
    }

    let mut d = IntDev::new(kernel, creal.rat.int);
    generic::declare_all(&mut d, p)?;
    measure::declare_all(&mut d, p)?;
    convergence::declare_all(&mut d, p)?;
    instances::declare_all(&mut d, p)?;
    detachable::declare_all(&mut d, p)?;
    probability_bridge::declare_all(&mut d, p)?;
    bundled::declare_all(&mut d, p)?;
    l1::declare_all(&mut d, p, metric)?;

    Ok(p)
}

// ---------------------------------------------------------------------------
// Shared helpers for the submodules.
// ---------------------------------------------------------------------------

pub mod bundled;
mod convergence;
mod detachable;
mod generic;
mod instances;
pub mod l1;
mod measure;
mod probability_bridge;

#[cfg(test)]
mod intspace_tests;

/// A bound `S : IntSpace` plus its carrier, the shape every generic theorem
/// opens with.
pub(crate) struct Generic {
    pub(crate) space_ty: ExprId,
    pub(crate) s_fv: u64,
    pub(crate) s: ExprId,
    pub(crate) carrier: ExprId,
}

pub(crate) fn generic_space(d: &mut IntDev<'_>, p: IntSpacePrelude) -> Generic {
    let space_ty = d.kernel().const_(p.record.ind, vec![]);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let sel = d.kernel().const_(p.record.sel(CARRIER), vec![]);
    let carrier = d.apply(sel, &[s]);
    Generic {
        space_ty,
        s_fv,
        s,
        carrier,
    }
}

/// `IntSpace.<field i> s`.
pub(crate) fn field(d: &mut IntDev<'_>, p: IntSpacePrelude, s: ExprId, i: usize) -> ExprId {
    let sel = d.kernel().const_(p.record.sel(i), vec![]);
    d.apply(sel, &[s])
}

// --- `CReal` shorthands ----------------------------------------------------

pub(crate) fn rty(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    d.kernel().const_(c.creal, vec![])
}
pub(crate) fn rzero(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    d.kernel().const_(c.zero, vec![])
}
pub(crate) fn rone(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    d.kernel().const_(c.one, vec![])
}
pub(crate) fn radd(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.add, &[a, b])
}
pub(crate) fn rneg(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.const_app(c.neg, &[a])
}
pub(crate) fn rmul(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.mul, &[a, b])
}
pub(crate) fn rle(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.le, &[a, b])
}
pub(crate) fn req(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.equiv, &[a, b])
}
pub(crate) fn rrefl(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(c.equiv_refl, &[a])
}
pub(crate) fn rsymm(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    d.lemma(c.equiv_symm, &[a, b, h])
}
pub(crate) fn rtrans(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    a: ExprId,
    b: ExprId,
    z: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    d.lemma(c.equiv_trans, &[a, b, z, h1, h2])
}

pub(crate) fn theorem(
    d: &mut IntDev<'_>,
    name: NameId,
    ty: ExprId,
    value: ExprId,
) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

pub(crate) fn definition(
    d: &mut IntDev<'_>,
    name: NameId,
    ty: ExprId,
    value: ExprId,
) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })
}
