//! `Metric.*` — a **constructive metric-space carrier**, and the first
//! topology declarations in this kernel.
//!
//! Roadmap W2-1 (reviewer 06.2). Before this module the library had *zero*
//! topology declarations: `topology`, `open_set`, `compact_space`,
//! `metric_space`, `connected`, `homotopy`, `homology` and
//! `fundamental_group` each returned zero files, against a positive control
//! (`riemann`) of 16. Every classically-topological theorem in the library —
//! `CReal.UniformlyContinuousOn`, `CReal.converges_of_cauchy`, the IVT, the
//! EVT — was proved by hand on one specific carrier and generalized to
//! nothing.
//!
//! ## The design, in one paragraph
//!
//! A metric space is a **record over a carrier with an explicit equivalence**
//! — the [`AlgS`](crate::nat_prelude::structures_setoid) spine's shape
//! (ADR-1588), not the `Alg` spine's, because `CReal`'s equality is the
//! defined relation `CReal.Equiv` and not the kernel's primitive `Eq`
//! (ADR-0512). Distance is valued in `CReal`. The axioms are stated in
//! Bishop's constructive form (*Constructive Analysis*, §4.1): the identity
//! of indiscernibles is **two separate one-directional fields**
//! (`distSelf`, `distEquiv`) rather than one `Iff`, because the two
//! directions have genuinely different proofs on every instance built here,
//! and nonnegativity is a field rather than a derived theorem for the same
//! reason Bishop lists it as an axiom.
//!
//! ## Field layout
//!
//! | # | field | type |
//! |---|---|---|
//! | 0 | `carrier` | `Sort 1` |
//! | 1 | `equiv` | `carrier → carrier → Prop` |
//! | 2 | `equivRefl` | `∀ a, equiv a a` |
//! | 3 | `equivSymm` | `∀ a b, equiv a b → equiv b a` |
//! | 4 | `equivTrans` | `∀ a b c, equiv a b → equiv b c → equiv a c` |
//! | 5 | `dist` | `carrier → carrier → CReal` |
//! | 6 | `distCongr` | `∀ a a' b b', equiv a a' → equiv b b' → CReal.Equiv (dist a b) (dist a' b')` |
//! | 7 | `distNonneg` | `∀ a b, CReal.le CReal.zero (dist a b)` |
//! | 8 | `distSelf` | `∀ a b, equiv a b → CReal.Equiv (dist a b) CReal.zero` |
//! | 9 | `distEquiv` | `∀ a b, CReal.Equiv (dist a b) CReal.zero → equiv a b` |
//! | 10 | `distComm` | `∀ a b, CReal.Equiv (dist a b) (dist b a)` |
//! | 11 | `distTriangle` | `∀ a b c, CReal.le (dist a c) (CReal.add (dist a b) (dist b c))` |
//!
//! `distCongr` is the field the `AlgS` spine taught us to expect and that a
//! bare `Eq`-flavored record would not need: without it, `dist` is a function
//! on representatives rather than on the setoid, and nothing downstream can
//! rewrite under it.
//!
//! ## What generalizes
//!
//! [`MetricPrelude::complete`] states completeness for an **arbitrary**
//! metric space and [`MetricPrelude::creal_complete`] proves ℝ satisfies it,
//! by routing `CReal.converges_of_cauchy` through the two `abs`-to-samples
//! bridges (`CReal.cauchy_of_abs_diff_le`, `CReal.close_within_of_within`).
//! See ADR-1602 for the measurement and for why those two bridges are the
//! whole cost.

// `MetricPrelude` is a `Copy` handle carrying `CPointPrelude` (itself the
// whole `CRealPrelude`) plus the record's fixed-size selector array, so it is
// 15 kB and every `declare_*` below trips `large_types_passed_by_value`. Same
// shape, same suppression, and the same reason as `creal.rs`, `complex.rs`,
// `int_prelude.rs` and `characterization/ops.rs`: these are long, straight-line
// term constructions and the handle is a `Copy` snapshot by design.
#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use crate::CPointPrelude;
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
    FieldKind, FieldSpec, RecordNames, arrow, declare_record, mk_instance, pi_over,
};

pub mod compactness;
pub mod continuity;

pub use compactness::CompactnessNames;
pub use continuity::ContinuityNames;

// ---------------------------------------------------------------------------
// Field indices. Fixed across the record; index a field through these, never
// with a bare integer.
// ---------------------------------------------------------------------------

/// `Metric.carrier`.
pub const CARRIER: usize = 0;
/// `Metric.equiv`.
pub const EQUIV: usize = 1;
/// `Metric.equivRefl`.
pub const EQUIV_REFL: usize = 2;
/// `Metric.equivSymm`.
pub const EQUIV_SYMM: usize = 3;
/// `Metric.equivTrans`.
pub const EQUIV_TRANS: usize = 4;
/// `Metric.dist`.
pub const DIST: usize = 5;
/// `Metric.distCongr`.
pub const DIST_CONGR: usize = 6;
/// `Metric.distNonneg`.
pub const DIST_NONNEG: usize = 7;
/// `Metric.distSelf`.
pub const DIST_SELF: usize = 8;
/// `Metric.distEquiv`.
pub const DIST_EQUIV: usize = 9;
/// `Metric.distComm`.
pub const DIST_COMM: usize = 10;
/// `Metric.distTriangle`.
pub const DIST_TRIANGLE: usize = 11;

/// The number of fields the record carries.
pub const FIELD_COUNT: usize = 12;

// Free-variable ids used inside the field-shape closures. Disjoint from
// `structures::CTOR_FVAR_BASE` (10_000) and `SELECTOR_S_FV` (10_900).
const F_A: u64 = 20_800;
const F_AP: u64 = 20_801;
const F_B: u64 = 20_802;
const F_BP: u64 = 20_803;
const F_C: u64 = 20_804;

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
fn equiv_field() -> FieldSpec {
    FieldSpec {
        suffix: "equiv",
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

/// `forall a, equiv a a`.
fn equiv_refl_field() -> FieldSpec {
    FieldSpec {
        suffix: "equivRefl",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let eq = vals[EQUIV];
            let a = k.fvar(F_A);
            let body = app_all(k, eq, &[a, a]);
            pi_over(k, F_A, ty, body)
        }),
    }
}

/// `forall a b, equiv a b -> equiv b a`.
fn equiv_symm_field() -> FieldSpec {
    FieldSpec {
        suffix: "equivSymm",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let eq = vals[EQUIV];
            let a = k.fvar(F_A);
            let b = k.fvar(F_B);
            let ab = app_all(k, eq, &[a, b]);
            let ba = app_all(k, eq, &[b, a]);
            let imp = arrow(k, ab, ba);
            let t = pi_over(k, F_B, ty, imp);
            pi_over(k, F_A, ty, t)
        }),
    }
}

/// `forall a b c, equiv a b -> equiv b c -> equiv a c`.
fn equiv_trans_field() -> FieldSpec {
    FieldSpec {
        suffix: "equivTrans",
        kind: FieldKind::Law,
        build: Box::new(|k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let eq = vals[EQUIV];
            let a = k.fvar(F_A);
            let b = k.fvar(F_B);
            let c = k.fvar(F_C);
            let ab = app_all(k, eq, &[a, b]);
            let bc = app_all(k, eq, &[b, c]);
            let ac = app_all(k, eq, &[a, c]);
            let inner = arrow(k, bc, ac);
            let imp = arrow(k, ab, inner);
            let t = pi_over(k, F_C, ty, imp);
            let t = pi_over(k, F_B, ty, t);
            pi_over(k, F_A, ty, t)
        }),
    }
}

/// `carrier -> carrier -> CReal`.
fn dist_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "dist",
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a = vals[CARRIER];
            let r = k.const_(creal.creal, vec![]);
            let inner = arrow(k, a, r);
            arrow(k, a, inner)
        }),
    }
}

/// `forall a a' b b', equiv a a' -> equiv b b' ->
/// CReal.Equiv (dist a b) (dist a' b')`.
fn dist_congr_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "distCongr",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let eq = vals[EQUIV];
            let dist = vals[DIST];
            let a = k.fvar(F_A);
            let ap = k.fvar(F_AP);
            let b = k.fvar(F_B);
            let bp = k.fvar(F_BP);
            let h1 = app_all(k, eq, &[a, ap]);
            let h2 = app_all(k, eq, &[b, bp]);
            let d1 = app_all(k, dist, &[a, b]);
            let d2 = app_all(k, dist, &[ap, bp]);
            let concl = capp(k, creal.equiv, &[d1, d2]);
            let imp = arrow(k, h2, concl);
            let imp = arrow(k, h1, imp);
            let t = pi_over(k, F_BP, ty, imp);
            let t = pi_over(k, F_B, ty, t);
            let t = pi_over(k, F_AP, ty, t);
            pi_over(k, F_A, ty, t)
        }),
    }
}

/// `forall a b, CReal.le CReal.zero (dist a b)`.
fn dist_nonneg_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "distNonneg",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let dist = vals[DIST];
            let a = k.fvar(F_A);
            let b = k.fvar(F_B);
            let d = app_all(k, dist, &[a, b]);
            let zero = k.const_(creal.zero, vec![]);
            let concl = capp(k, creal.le, &[zero, d]);
            let t = pi_over(k, F_B, ty, concl);
            pi_over(k, F_A, ty, t)
        }),
    }
}

/// `forall a b, equiv a b -> CReal.Equiv (dist a b) CReal.zero`.
fn dist_self_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "distSelf",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let eq = vals[EQUIV];
            let dist = vals[DIST];
            let a = k.fvar(F_A);
            let b = k.fvar(F_B);
            let h = app_all(k, eq, &[a, b]);
            let d = app_all(k, dist, &[a, b]);
            let zero = k.const_(creal.zero, vec![]);
            let concl = capp(k, creal.equiv, &[d, zero]);
            let imp = arrow(k, h, concl);
            let t = pi_over(k, F_B, ty, imp);
            pi_over(k, F_A, ty, t)
        }),
    }
}

/// `forall a b, CReal.Equiv (dist a b) CReal.zero -> equiv a b`.
fn dist_equiv_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "distEquiv",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let eq = vals[EQUIV];
            let dist = vals[DIST];
            let a = k.fvar(F_A);
            let b = k.fvar(F_B);
            let d = app_all(k, dist, &[a, b]);
            let zero = k.const_(creal.zero, vec![]);
            let h = capp(k, creal.equiv, &[d, zero]);
            let concl = app_all(k, eq, &[a, b]);
            let imp = arrow(k, h, concl);
            let t = pi_over(k, F_B, ty, imp);
            pi_over(k, F_A, ty, t)
        }),
    }
}

/// `forall a b, CReal.Equiv (dist a b) (dist b a)`.
fn dist_comm_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "distComm",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let dist = vals[DIST];
            let a = k.fvar(F_A);
            let b = k.fvar(F_B);
            let ab = app_all(k, dist, &[a, b]);
            let ba = app_all(k, dist, &[b, a]);
            let concl = capp(k, creal.equiv, &[ab, ba]);
            let t = pi_over(k, F_B, ty, concl);
            pi_over(k, F_A, ty, t)
        }),
    }
}

/// `forall a b c, CReal.le (dist a c) (CReal.add (dist a b) (dist b c))`.
fn dist_triangle_field(creal: CRealPrelude) -> FieldSpec {
    FieldSpec {
        suffix: "distTriangle",
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let ty = vals[CARRIER];
            let dist = vals[DIST];
            let a = k.fvar(F_A);
            let b = k.fvar(F_B);
            let c = k.fvar(F_C);
            let ac = app_all(k, dist, &[a, c]);
            let ab = app_all(k, dist, &[a, b]);
            let bc = app_all(k, dist, &[b, c]);
            let sum = capp(k, creal.add, &[ab, bc]);
            let concl = capp(k, creal.le, &[ac, sum]);
            let t = pi_over(k, F_C, ty, concl);
            let t = pi_over(k, F_B, ty, t);
            pi_over(k, F_A, ty, t)
        }),
    }
}

fn metric_fields(creal: CRealPrelude) -> Vec<FieldSpec> {
    vec![
        carrier_field(),
        equiv_field(),
        equiv_refl_field(),
        equiv_symm_field(),
        equiv_trans_field(),
        dist_field(creal),
        dist_congr_field(creal),
        dist_nonneg_field(creal),
        dist_self_field(creal),
        dist_equiv_field(creal),
        dist_comm_field(creal),
        dist_triangle_field(creal),
    ]
}

// ---------------------------------------------------------------------------
// The prelude handle.
// ---------------------------------------------------------------------------

/// The interned names produced by [`build_metric_prelude`].
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MetricPrelude {
    /// The plane this development's second instance lives on (and, through
    /// it, the reals the first one does).
    pub cpoint: CPointPrelude,
    /// The `Metric` record: its inductive, `mk`, `rec` and twelve selectors.
    pub record: RecordNames,

    // --- the ℝ instance ----------------------------------------------------
    /// `Metric.CReal.negZero : CReal.Equiv (CReal.neg CReal.zero) CReal.zero`.
    pub creal_neg_zero: NameId,
    /// `Metric.CReal.absZero : CReal.Equiv (CReal.abs CReal.zero) CReal.zero`.
    pub creal_abs_zero: NameId,
    /// `Metric.CReal.leOfSubNonpos : ∀ x y,
    /// CReal.le (CReal.add x (CReal.neg y)) CReal.zero → CReal.le x y`.
    pub creal_le_of_sub_nonpos: NameId,
    /// `Metric.CReal.distCongr : ∀ a a' b b', Equiv a a' → Equiv b b' →
    /// Equiv (abs (a + -b)) (abs (a' + -b'))`.
    pub creal_dist_congr: NameId,
    /// `Metric.CReal.distSelf : ∀ a b, Equiv a b → Equiv (abs (a + -b)) zero`.
    pub creal_dist_self: NameId,
    /// `Metric.CReal.distEquiv : ∀ a b, Equiv (abs (a + -b)) zero → Equiv a b`.
    pub creal_dist_equiv: NameId,
    /// `Metric.CReal.absSubLe : ∀ a b, le (abs (a + -b)) (abs (b + -a))` —
    /// one direction of `distComm`, applied twice.
    pub creal_abs_sub_le: NameId,
    /// `Metric.CReal.distComm : ∀ a b, Equiv (abs (a + -b)) (abs (b + -a))`.
    pub creal_dist_comm: NameId,
    /// `Metric.CReal.subTelescope : ∀ a b c,
    /// Equiv (add (add a (neg b)) (add b (neg c))) (add a (neg c))`.
    pub creal_sub_telescope: NameId,
    /// `Metric.CReal.distTriangle : ∀ a b c,
    /// le (abs (a + -c)) (add (abs (a + -b)) (abs (b + -c)))`.
    pub creal_dist_triangle: NameId,
    /// `Metric.creal : Metric` — the real line with `d(x,y) = |x − y|`.
    pub creal_metric: NameId,
    /// `Metric.creal_dist : ∀ x y,
    /// CReal.Equiv (Metric.dist Metric.creal x y) (CReal.abs (add x (neg y)))`
    /// — proved by `CReal.equiv_refl`, so its admission IS the statement that
    /// the selector reduces definitionally on the instance. The `AlgS`
    /// spine's `quotient_equiv` probe, transplanted.
    pub creal_dist: NameId,

    // --- theorems generalized off the carrier ------------------------------
    /// `Metric.dist_self : ∀ (M : Metric) (a : M.carrier),
    /// CReal.Equiv (M.dist a a) CReal.zero`.
    pub dist_self: NameId,
    /// `Metric.dist_quadrilateral : ∀ M a b c e,
    /// CReal.le (M.dist a e)
    ///   (CReal.add (M.dist a b) (CReal.add (M.dist b c) (M.dist c e)))` —
    /// the four-point inequality, two `distTriangle`s.
    pub dist_quadrilateral: NameId,

    // --- completeness, stated for an arbitrary metric space ----------------
    /// `Metric.CauchyAt : ∀ (M : Metric) (f : Nat → M.carrier) (K : Nat), Prop
    /// := ∀ m n, CReal.le (M.dist (f m) (f n))
    ///      (CReal.ofRat (Rat.add (Rat.natDivSucc K m) (Rat.natDivSucc K n)))`.
    pub cauchy_at: NameId,
    /// `Metric.Cauchy M f := ∃ K, Metric.CauchyAt M f K`.
    pub cauchy: NameId,
    /// `Metric.TendsToAt M f L K := ∀ n,
    /// CReal.le (M.dist (f n) L) (CReal.ofRat (Rat.natDivSucc K n))`.
    pub tends_to_at: NameId,
    /// `Metric.TendsTo M f L := ∃ K, Metric.TendsToAt M f L K`.
    pub tends_to: NameId,
    /// `Metric.Complete M := ∀ f, Metric.Cauchy M f →
    /// ∃ L, Metric.TendsTo M f L`.
    pub complete: NameId,
    /// `Metric.CPoint.equivRefl : ∀ P, CPoint.Equiv P P` — the plane prelude
    /// builds this inline and never names it.
    pub cpoint_equiv_refl: NameId,
    /// `Metric.CPoint.equivSymm`.
    pub cpoint_equiv_symm: NameId,
    /// `Metric.CPoint.equivTrans`.
    pub cpoint_equiv_trans: NameId,
    /// `Metric.CPoint.subTelescope : ∀ A B C,
    /// CPoint.Equiv (sub A C) (add (sub A B) (sub B C))`.
    pub cpoint_sub_telescope: NameId,
    /// `Metric.CPoint.dotLeSqrtMul : ∀ U V,
    /// CReal.le (dot U V) (CReal.sqrt (mul (dot U U) (dot V V)))` —
    /// **unsquared Cauchy–Schwarz**, the step `CPoint.cauchy_schwarz` (which
    /// is squared) does not give.
    pub cpoint_dot_le_sqrt_mul: NameId,
    /// `Metric.CPoint.dist := fun P Q => CReal.sqrt (CPoint.distSq P Q)`.
    pub cpoint_dist: NameId,
    /// `Metric.CPoint.distCongr`.
    pub cpoint_dist_congr: NameId,
    /// `Metric.CPoint.distSelf`.
    pub cpoint_dist_self: NameId,
    /// `Metric.CPoint.distEquiv`.
    pub cpoint_dist_equiv: NameId,
    /// `Metric.CPoint.distComm`.
    pub cpoint_dist_comm: NameId,
    /// `Metric.CPoint.distSqExpand : ∀ A B C, Equiv (distSq A C)
    /// (add (dot U U) (add (dot U V) (add (dot U V) (dot V V))))`.
    pub cpoint_dist_sq_expand: NameId,
    /// `Metric.CPoint.distTriangle` — **Euclid I.20 on the UNSQUARED
    /// distance**, which the plane prelude's own squared bounds stop short of.
    pub cpoint_dist_triangle: NameId,
    /// `Metric.cpoint : Metric` — the Euclidean plane.
    pub cpoint_metric: NameId,
    /// `Metric.cpoint_dist` — the reduction probe for the plane instance.
    pub cpoint_dist_reduces: NameId,
    /// `Metric.creal_complete : Metric.Complete Metric.creal` — **the
    /// generalization**: `CReal.converges_of_cauchy` becomes an instance of a
    /// statement about metric spaces.
    pub creal_complete: NameId,
    /// The W2-2 continuity layer (`metric/continuity.rs`).
    pub continuity: ContinuityNames,
    /// The W2-3 compactness layer (`metric/compactness.rs`).
    pub compactness: CompactnessNames,
}

// ---------------------------------------------------------------------------
// Name interning.
// ---------------------------------------------------------------------------

/// The record's field suffixes, in declaration order. Used both to build the
/// record and to re-intern its selectors on the already-declared path.
const FIELD_SUFFIXES: [&str; FIELD_COUNT] = [
    "carrier",
    "equiv",
    "equivRefl",
    "equivSymm",
    "equivTrans",
    "dist",
    "distCongr",
    "distNonneg",
    "distSelf",
    "distEquiv",
    "distComm",
    "distTriangle",
];

fn intern(kernel: &mut Kernel, cpoint: CPointPrelude) -> MetricPrelude {
    let root = kernel.anon();
    let metric = kernel.name_str(root, "Metric");
    let creal_ns = kernel.name_str(metric, "CReal");
    let cpoint_ns = kernel.name_str(metric, "CPoint");

    let mk = kernel.name_str(metric, "mk");
    let rec = kernel.name_str(metric, "rec");
    let mut selectors = [mk; crate::nat_prelude::structures::MAX_FIELDS];
    for (i, suffix) in FIELD_SUFFIXES.iter().enumerate() {
        selectors[i] = kernel.name_str(metric, *suffix);
    }
    let record = RecordNames {
        ind: metric,
        mk,
        rec,
        selectors,
        len: FIELD_COUNT,
    };

    MetricPrelude {
        cpoint,
        record,
        creal_neg_zero: kernel.name_str(creal_ns, "negZero"),
        creal_abs_zero: kernel.name_str(creal_ns, "absZero"),
        creal_le_of_sub_nonpos: kernel.name_str(creal_ns, "leOfSubNonpos"),
        creal_dist_congr: kernel.name_str(creal_ns, "distCongr"),
        creal_dist_self: kernel.name_str(creal_ns, "distSelf"),
        creal_dist_equiv: kernel.name_str(creal_ns, "distEquiv"),
        creal_abs_sub_le: kernel.name_str(creal_ns, "absSubLe"),
        creal_dist_comm: kernel.name_str(creal_ns, "distComm"),
        creal_sub_telescope: kernel.name_str(creal_ns, "subTelescope"),
        creal_dist_triangle: kernel.name_str(creal_ns, "distTriangle"),
        creal_metric: kernel.name_str(metric, "creal"),
        creal_dist: kernel.name_str(metric, "creal_dist"),
        dist_self: kernel.name_str(metric, "dist_self"),
        dist_quadrilateral: kernel.name_str(metric, "dist_quadrilateral"),
        cauchy_at: kernel.name_str(metric, "CauchyAt"),
        cauchy: kernel.name_str(metric, "Cauchy"),
        tends_to_at: kernel.name_str(metric, "TendsToAt"),
        tends_to: kernel.name_str(metric, "TendsTo"),
        complete: kernel.name_str(metric, "Complete"),
        creal_complete: kernel.name_str(metric, "creal_complete"),
        cpoint_equiv_refl: kernel.name_str(cpoint_ns, "equivRefl"),
        cpoint_equiv_symm: kernel.name_str(cpoint_ns, "equivSymm"),
        cpoint_equiv_trans: kernel.name_str(cpoint_ns, "equivTrans"),
        cpoint_sub_telescope: kernel.name_str(cpoint_ns, "subTelescope"),
        cpoint_dot_le_sqrt_mul: kernel.name_str(cpoint_ns, "dotLeSqrtMul"),
        cpoint_dist: kernel.name_str(cpoint_ns, "dist"),
        cpoint_dist_congr: kernel.name_str(cpoint_ns, "distCongr"),
        cpoint_dist_self: kernel.name_str(cpoint_ns, "distSelf"),
        cpoint_dist_equiv: kernel.name_str(cpoint_ns, "distEquiv"),
        cpoint_dist_comm: kernel.name_str(cpoint_ns, "distComm"),
        cpoint_dist_sq_expand: kernel.name_str(cpoint_ns, "distSqExpand"),
        cpoint_dist_triangle: kernel.name_str(cpoint_ns, "distTriangle"),
        cpoint_metric: kernel.name_str(metric, "cpoint"),
        cpoint_dist_reduces: kernel.name_str(metric, "cpoint_dist"),
        continuity: continuity::intern(kernel, metric),
        compactness: compactness::intern(kernel, metric),
    }
}

/// Build (or return, if already built) the `Metric.*` declarations.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
///
/// # Panics
///
/// Panics if the field-shape list has drifted from [`FIELD_COUNT`], or if
/// [`declare_record`] returns selectors under names other than the ones
/// [`intern`] pre-computed. Both are internal-consistency assertions between
/// this file's two descriptions of the same record -- the `FIELD_SUFFIXES`
/// array that names the selectors and the `metric_fields` list that types
/// them -- and a drift between them would otherwise surface as a `Metric.*`
/// handle silently pointing at a declaration that does not exist.
pub fn build_metric_prelude(kernel: &mut Kernel) -> Result<MetricPrelude, KernelError> {
    let cpoint = crate::build_cpoint_prelude(kernel)?;
    let creal = cpoint.creal;
    let p = intern(kernel, cpoint);
    if kernel.environment().get(p.record.ind).is_some() {
        return Ok(p);
    }

    let l0 = kernel.level_zero();
    let l1 = kernel.level_succ(l0);
    let l2 = kernel.level_succ(l1);
    let logic = creal.rat.int.logic;
    let specs = metric_fields(creal);
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
    declare_creal_neg_zero(&mut d, creal, p)?;
    declare_creal_abs_zero(&mut d, creal, p)?;
    declare_creal_le_of_sub_nonpos(&mut d, creal, p)?;
    declare_creal_dist_congr(&mut d, creal, p)?;
    declare_creal_dist_self(&mut d, creal, p)?;
    declare_creal_dist_equiv(&mut d, creal, p)?;
    declare_creal_abs_sub_le(&mut d, creal, p)?;
    declare_creal_dist_comm(&mut d, creal, p)?;
    declare_creal_sub_telescope(&mut d, creal, p)?;
    declare_creal_dist_triangle(&mut d, creal, p)?;
    declare_creal_metric(&mut d, creal, p)?;
    declare_creal_dist_reduces(&mut d, creal, p)?;
    declare_dist_self(&mut d, creal, p)?;
    declare_dist_quadrilateral(&mut d, creal, p)?;
    declare_cauchy_at(&mut d, creal, p)?;
    declare_cauchy(&mut d, creal, p)?;
    declare_tends_to_at(&mut d, creal, p)?;
    declare_tends_to(&mut d, creal, p)?;
    declare_complete(&mut d, creal, p)?;
    declare_creal_complete(&mut d, creal, p)?;

    declare_cpoint_equiv_refl(&mut d, cpoint, p)?;
    declare_cpoint_equiv_symm(&mut d, cpoint, p)?;
    declare_cpoint_equiv_trans(&mut d, cpoint, p)?;
    declare_cpoint_sub_telescope(&mut d, cpoint, p)?;
    declare_cpoint_dot_le_sqrt_mul(&mut d, cpoint, p)?;
    declare_cpoint_dist(&mut d, cpoint, p)?;
    declare_cpoint_dist_congr(&mut d, cpoint, p)?;
    declare_cpoint_dist_self(&mut d, cpoint, p)?;
    declare_cpoint_dist_equiv(&mut d, cpoint, p)?;
    declare_cpoint_dist_comm(&mut d, cpoint, p)?;
    declare_cpoint_dist_sq_expand(&mut d, cpoint, p)?;
    declare_cpoint_dist_triangle(&mut d, cpoint, p)?;
    declare_cpoint_metric(&mut d, cpoint, p)?;
    declare_cpoint_dist_reduces(&mut d, cpoint, p)?;

    continuity::declare_all(&mut d, creal, p)?;
    compactness::declare_all(&mut d, creal, p)?;

    Ok(p)
}

// ---------------------------------------------------------------------------
// `CReal` term/proof shorthands. Every one is a constant applied to
// arguments; none introduces a new estimate.
// ---------------------------------------------------------------------------

fn rty(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    d.kernel().const_(c.creal, vec![])
}
fn rzero(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    d.kernel().const_(c.zero, vec![])
}
fn radd(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.add, &[a, b])
}
fn rneg(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.const_app(c.neg, &[a])
}
fn rabs(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.const_app(c.abs, &[a])
}
fn rsub_term(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let nb = rneg(d, c, b);
    radd(d, c, a, nb)
}
fn rle(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.le, &[a, b])
}
fn req(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.equiv, &[a, b])
}
fn rrefl(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(c.equiv_refl, &[a])
}
fn rsymm(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(c.equiv_symm, &[a, b, h])
}
fn rtrans(
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

/// Fold a chain of `Equiv` steps `start ~ t1 ~ t2 ~ …`, each given as
/// `(next_term, proof_that_current_equiv_next)`. Returns the endpoint and
/// the composite proof.
fn rchain(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> (ExprId, ExprId) {
    let mut cur = start;
    let mut acc: Option<ExprId> = None;
    for &(next, step) in steps {
        acc = Some(match acc {
            None => step,
            Some(prev) => rtrans(d, c, start, cur, next, prev, step),
        });
        cur = next;
    }
    let proof = match acc {
        Some(pr) => pr,
        None => rrefl(d, c, start),
    };
    (cur, proof)
}

fn theorem(d: &mut IntDev<'_>, name: NameId, ty: ExprId, value: ExprId) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// The ℝ instance's obligations.
// ---------------------------------------------------------------------------

/// `Metric.CReal.negZero : Equiv (neg zero) zero`.
///
/// `neg 0 ~ (neg 0) + 0 ~ 0 + (neg 0) ~ 0` — `add_zero`, `add_comm`,
/// `add_neg`. There is no `CReal.neg_zero` in the reals prelude; this is the
/// one-line stand-in `absZero` needs.
fn declare_creal_neg_zero(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let z = rzero(d, c);
    let nz = rneg(d, c, z);
    let nz_z = radd(d, c, nz, z);
    let z_nz = radd(d, c, z, nz);

    let az = d.lemma(c.add_zero, &[nz]); // Equiv (nz + 0) nz
    let h1 = rsymm(d, c, nz_z, nz, az);
    let ac = d.lemma(c.add_comm, &[z, nz]); // Equiv (0 + nz) (nz + 0)
    let h2 = rsymm(d, c, z_nz, nz_z, ac);
    let h3 = d.lemma(c.add_neg, &[z]); // Equiv (0 + neg 0) 0

    let (_, value) = rchain(d, c, nz, &[(nz_z, h1), (z_nz, h2), (z, h3)]);
    let ty = req(d, c, nz, z);
    theorem(d, p.creal_neg_zero, ty, value)
}

/// `Metric.CReal.absZero : Equiv (abs zero) zero`.
fn declare_creal_abs_zero(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let z = rzero(d, c);
    let nz = rneg(d, c, z);
    let az = rabs(d, c, z);

    let neg_zero = d.lemma(p.creal_neg_zero, &[]);
    let neg_le = d.lemma(c.le_of_equiv, &[nz, z, neg_zero]); // le (neg 0) 0
    let refl = d.lemma(c.le_refl, &[z]);
    let upper = d.lemma(c.abs_le, &[z, z, refl, neg_le]); // le (abs 0) 0
    let lower = d.lemma(c.abs_nonneg, &[z]); // le 0 (abs 0)
    let value = d.lemma(c.equiv_of_le_le, &[az, z, upper, lower]);
    let ty = req(d, c, az, z);
    theorem(d, p.creal_abs_zero, ty, value)
}

/// `Metric.CReal.leOfSubNonpos : ∀ x y, le (add x (neg y)) zero → le x y`.
///
/// Add `y` to both sides of the hypothesis and simplify each side — the
/// reals prelude has no "move a term across `le`" lemma, and both halves of
/// the `distEquiv` obligation need one.
fn declare_creal_le_of_sub_nonpos(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let z = rzero(d, c);
    let ny = rneg(d, c, y);
    let diff = radd(d, c, x, ny);
    let hyp_ty = rle(d, c, diff, z);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // s1 : le (diff + y) (0 + y)
    let refl_y = d.lemma(c.le_refl, &[y]);
    let s1 = d.lemma(c.add_le_add, &[diff, z, y, y, h, refl_y]);
    let diff_y = radd(d, c, diff, y);
    let z_y = radd(d, c, z, y);

    // e1 : Equiv (diff + y) x
    let ny_y = radd(d, c, ny, y);
    let x_ny_y = radd(d, c, x, ny_y);
    let a1 = d.lemma(c.add_assoc, &[x, ny, y]); // Equiv (diff + y) (x + (ny + y))
    let y_ny = radd(d, c, y, ny);
    let c1 = d.lemma(c.add_comm, &[ny, y]); // Equiv (ny + y) (y + ny)
    let c2 = d.lemma(c.add_neg, &[y]); // Equiv (y + ny) 0
    let c3 = rtrans(d, c, ny_y, y_ny, z, c1, c2); // Equiv (ny + y) 0
    let refl_x = rrefl(d, c, x);
    let a2 = d.lemma(c.add_congr, &[x, x, ny_y, z, refl_x, c3]); // Equiv (x+(ny+y)) (x+0)
    let x_z = radd(d, c, x, z);
    let a3 = d.lemma(c.add_zero, &[x]); // Equiv (x + 0) x
    let (_, e1) = rchain(d, c, diff_y, &[(x_ny_y, a1), (x_z, a2), (x, a3)]);

    // e2 : Equiv (0 + y) y
    let y_z = radd(d, c, y, z);
    let b1 = d.lemma(c.add_comm, &[z, y]); // Equiv (0 + y) (y + 0)
    let b2 = d.lemma(c.add_zero, &[y]); // Equiv (y + 0) y
    let (_, e2) = rchain(d, c, z_y, &[(y_z, b1), (y, b2)]);

    let body = d.lemma(c.le_congr, &[diff_y, x, z_y, y, e1, e2, s1]);

    let value = {
        let t = d.lam_fv(h_fv, hyp_ty, body);
        let t = d.lam_fv(y_fv, carrier, t);
        d.lam_fv(x_fv, carrier, t)
    };
    let ty = {
        let concl = rle(d, c, x, y);
        let inner = d.arrow(hyp_ty, concl);
        let t = d.pi_fv(y_fv, carrier, inner);
        d.pi_fv(x_fv, carrier, t)
    };
    theorem(d, p.creal_le_of_sub_nonpos, ty, value)
}

/// `Metric.CReal.distCongr : ∀ a a' b b', Equiv a a' → Equiv b b' →
/// Equiv (abs (a + -b)) (abs (a' + -b'))`.
fn declare_creal_dist_congr(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let ap_fv = d.fresh_fvar();
    let ap = d.kernel().fvar(ap_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let bp_fv = d.fresh_fvar();
    let bp = d.kernel().fvar(bp_fv);

    let ha_ty = req(d, c, a, ap);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);
    let hb_ty = req(d, c, b, bp);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let nb = rneg(d, c, b);
    let nbp = rneg(d, c, bp);
    let d1 = radd(d, c, a, nb);
    let d2 = radd(d, c, ap, nbp);

    let hn = d.lemma(c.neg_congr, &[b, bp, hb]);
    let hs = d.lemma(c.add_congr, &[a, ap, nb, nbp, ha, hn]);
    let body = d.lemma(c.abs_congr, &[d1, d2, hs]);

    let value = {
        let t = d.lam_fv(hb_fv, hb_ty, body);
        let t = d.lam_fv(ha_fv, ha_ty, t);
        let t = d.lam_fv(bp_fv, carrier, t);
        let t = d.lam_fv(b_fv, carrier, t);
        let t = d.lam_fv(ap_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    let ty = {
        let l = rabs(d, c, d1);
        let r = rabs(d, c, d2);
        let concl = req(d, c, l, r);
        let t = d.arrow(hb_ty, concl);
        let t = d.arrow(ha_ty, t);
        let t = d.pi_fv(bp_fv, carrier, t);
        let t = d.pi_fv(b_fv, carrier, t);
        let t = d.pi_fv(ap_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    theorem(d, p.creal_dist_congr, ty, value)
}

/// `Metric.CReal.distSelf : ∀ a b, Equiv a b → Equiv (abs (a + -b)) zero`.
fn declare_creal_dist_self(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let h_ty = req(d, c, a, b);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let z = rzero(d, c);
    let nb = rneg(d, c, b);
    let d1 = radd(d, c, a, nb);
    let bb = radd(d, c, b, nb);
    let refl_nb = rrefl(d, c, nb);
    let s1 = d.lemma(c.add_congr, &[a, b, nb, nb, h, refl_nb]); // Equiv d1 (b + -b)
    let s2 = d.lemma(c.add_neg, &[b]); // Equiv (b + -b) 0
    let (_, s3) = rchain(d, c, d1, &[(bb, s1), (z, s2)]);
    let ad1 = rabs(d, c, d1);
    let az = rabs(d, c, z);
    let s4 = d.lemma(c.abs_congr, &[d1, z, s3]); // Equiv (abs d1) (abs 0)
    let s5 = d.lemma(p.creal_abs_zero, &[]);
    let (_, body) = rchain(d, c, ad1, &[(az, s4), (z, s5)]);

    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    let ty = {
        let concl = req(d, c, ad1, z);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    theorem(d, p.creal_dist_self, ty, value)
}

/// `Metric.CReal.distEquiv : ∀ a b, Equiv (abs (a + -b)) zero → Equiv a b`.
///
/// **The identity of indiscernibles, in the direction that needs the order.**
/// `|a−b| ~ 0` bounds both `a−b` and `−(a−b)` above by `0`
/// (`le_abs_self`/`neg_le_abs`), and [`declare_creal_le_of_sub_nonpos`] turns
/// each into a one-sided `le`; `equiv_of_le_le` closes it. `neg_sub_swap` is
/// what makes the second half the *same* lemma at swapped arguments.
fn declare_creal_dist_equiv(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let z = rzero(d, c);
    let d1 = rsub_term(d, c, a, b);
    let ad1 = rabs(d, c, d1);
    let h_ty = req(d, c, ad1, z);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let h0 = d.lemma(c.le_of_equiv, &[ad1, z, h]); // le (abs d1) 0
    let up = d.lemma(c.le_abs_self, &[d1]); // le d1 (abs d1)
    let u1 = d.lemma(c.le_trans, &[d1, ad1, z, up, h0]); // le d1 0
    let hab = d.lemma(p.creal_le_of_sub_nonpos, &[a, b, u1]); // le a b

    let nd1 = rneg(d, c, d1);
    let lo = d.lemma(c.neg_le_abs, &[d1]); // le (neg d1) (abs d1)
    let u2 = d.lemma(c.le_trans, &[nd1, ad1, z, lo, h0]); // le (neg d1) 0
    let d2 = rsub_term(d, c, b, a);
    let ns = d.lemma(c.neg_sub_swap, &[a, b]); // Equiv (neg (a + -b)) (b + -a)
    let refl_z = rrefl(d, c, z);
    let u3 = d.lemma(c.le_congr, &[nd1, d2, z, z, ns, refl_z, u2]); // le (b + -a) 0
    let hba = d.lemma(p.creal_le_of_sub_nonpos, &[b, a, u3]); // le b a

    let body = d.lemma(c.equiv_of_le_le, &[a, b, hab, hba]);

    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    let ty = {
        let concl = req(d, c, a, b);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    theorem(d, p.creal_dist_equiv, ty, value)
}

/// `Metric.CReal.absSubLe : ∀ a b, le (abs (a + -b)) (abs (b + -a))`.
///
/// One direction of symmetry. The reals prelude has no `abs_neg`, so this is
/// built straight from the lattice universal property `abs_le`, with
/// `neg_sub_swap` supplying both branches.
fn declare_creal_abs_sub_le(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let d1 = rsub_term(d, c, a, b);
    let d2 = rsub_term(d, c, b, a);
    let a2 = rabs(d, c, d2);
    let refl_a2 = rrefl(d, c, a2);

    // q1 : le d1 (abs d2), from `neg d2 ~ d1` and `neg d2 ≤ abs d2`.
    let nd2 = rneg(d, c, d2);
    let p1 = d.lemma(c.neg_le_abs, &[d2]);
    let ns_ba = d.lemma(c.neg_sub_swap, &[b, a]); // Equiv (neg (b + -a)) (a + -b)
    let q1 = d.lemma(c.le_congr, &[nd2, d1, a2, a2, ns_ba, refl_a2, p1]);

    // q2 : le (neg d1) (abs d2), from `d2 ~ neg d1` and `d2 ≤ abs d2`.
    let nd1 = rneg(d, c, d1);
    let p2 = d.lemma(c.le_abs_self, &[d2]);
    let ns_ab = d.lemma(c.neg_sub_swap, &[a, b]); // Equiv (neg (a + -b)) (b + -a)
    let ns_ab_symm = rsymm(d, c, nd1, d2, ns_ab); // Equiv (b + -a) (neg (a + -b))
    let q2 = d.lemma(c.le_congr, &[d2, nd1, a2, a2, ns_ab_symm, refl_a2, p2]);

    let body = d.lemma(c.abs_le, &[d1, a2, q1, q2]);

    let value = {
        let t = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, t)
    };
    let ty = {
        let a1 = rabs(d, c, d1);
        let concl = rle(d, c, a1, a2);
        let t = d.pi_fv(b_fv, carrier, concl);
        d.pi_fv(a_fv, carrier, t)
    };
    theorem(d, p.creal_abs_sub_le, ty, value)
}

/// `Metric.CReal.distComm : ∀ a b, Equiv (abs (a + -b)) (abs (b + -a))`.
fn declare_creal_dist_comm(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let d1 = rsub_term(d, c, a, b);
    let d2 = rsub_term(d, c, b, a);
    let a1 = rabs(d, c, d1);
    let a2 = rabs(d, c, d2);
    let fwd = d.lemma(p.creal_abs_sub_le, &[a, b]);
    let bwd = d.lemma(p.creal_abs_sub_le, &[b, a]);
    let body = d.lemma(c.equiv_of_le_le, &[a1, a2, fwd, bwd]);

    let value = {
        let t = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, t)
    };
    let ty = {
        let concl = req(d, c, a1, a2);
        let t = d.pi_fv(b_fv, carrier, concl);
        d.pi_fv(a_fv, carrier, t)
    };
    theorem(d, p.creal_dist_comm, ty, value)
}

/// `Metric.CReal.subTelescope : ∀ a b c,
/// Equiv (add (add a (neg b)) (add b (neg c))) (add a (neg c))`.
fn declare_creal_sub_telescope(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let cc = d.kernel().fvar(c_fv);

    let z = rzero(d, c);
    let nb = rneg(d, c, b);
    let nc = rneg(d, c, cc);
    let u = radd(d, c, a, nb);
    let v = radd(d, c, b, nc);
    let uv = radd(d, c, u, v);
    let target = radd(d, c, a, nc);

    let nb_v = radd(d, c, nb, v);
    let a_nb_v = radd(d, c, a, nb_v);
    let t1 = d.lemma(c.add_assoc, &[a, nb, v]); // Equiv uv (a + (nb + v))

    // inner : Equiv (nb + v) (neg c)
    let nb_b = radd(d, c, nb, b);
    let nb_b_nc = radd(d, c, nb_b, nc);
    let assoc = d.lemma(c.add_assoc, &[nb, b, nc]); // Equiv ((nb+b)+nc) (nb+(b+nc))
    let t2 = rsymm(d, c, nb_b_nc, nb_v, assoc);
    let b_nb = radd(d, c, b, nb);
    let cm = d.lemma(c.add_comm, &[nb, b]); // Equiv (nb+b) (b+nb)
    let an = d.lemma(c.add_neg, &[b]); // Equiv (b+nb) 0
    let (_, nb_b_zero) = rchain(d, c, nb_b, &[(b_nb, cm), (z, an)]);
    let refl_nc = rrefl(d, c, nc);
    let z_nc = radd(d, c, z, nc);
    let t3 = d.lemma(c.add_congr, &[nb_b, z, nc, nc, nb_b_zero, refl_nc]);
    let nc_z = radd(d, c, nc, z);
    let t4 = d.lemma(c.add_comm, &[z, nc]); // Equiv (0+nc) (nc+0)
    let t5 = d.lemma(c.add_zero, &[nc]); // Equiv (nc+0) nc
    let (_, inner) = rchain(
        d,
        c,
        nb_v,
        &[(nb_b_nc, t2), (z_nc, t3), (nc_z, t4), (nc, t5)],
    );

    let refl_a = rrefl(d, c, a);
    let t6 = d.lemma(c.add_congr, &[a, a, nb_v, nc, refl_a, inner]);
    let (_, body) = rchain(d, c, uv, &[(a_nb_v, t1), (target, t6)]);

    let value = {
        let t = d.lam_fv(c_fv, carrier, body);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    let ty = {
        let concl = req(d, c, uv, target);
        let t = d.pi_fv(c_fv, carrier, concl);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    theorem(d, p.creal_sub_telescope, ty, value)
}

/// `Metric.CReal.distTriangle : ∀ a b c,
/// le (abs (a + -c)) (add (abs (a + -b)) (abs (b + -c)))`.
fn declare_creal_dist_triangle(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let cc = d.kernel().fvar(c_fv);

    let u = rsub_term(d, c, a, b);
    let v = rsub_term(d, c, b, cc);
    let w = rsub_term(d, c, a, cc);
    let uv = radd(d, c, u, v);
    let au = rabs(d, c, u);
    let av = rabs(d, c, v);
    let sum = radd(d, c, au, av);
    let auv = rabs(d, c, uv);
    let aw = rabs(d, c, w);

    let tri = d.lemma(c.abs_add_le, &[u, v]); // le (abs (u+v)) (abs u + abs v)
    let tel = d.lemma(p.creal_sub_telescope, &[a, b, cc]); // Equiv (u+v) w
    let ac = d.lemma(c.abs_congr, &[uv, w, tel]); // Equiv (abs (u+v)) (abs w)
    let refl_sum = rrefl(d, c, sum);
    let body = d.lemma(c.le_congr, &[auv, aw, sum, sum, ac, refl_sum, tri]);

    let value = {
        let t = d.lam_fv(c_fv, carrier, body);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    let ty = {
        let concl = rle(d, c, aw, sum);
        let t = d.pi_fv(c_fv, carrier, concl);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    theorem(d, p.creal_dist_triangle, ty, value)
}

/// `Metric.creal : Metric` — the real line under `d(x,y) = |x − y|`.
fn declare_creal_metric(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);

    let equiv = d.kernel().const_(c.equiv, vec![]);
    let equiv_refl = d.kernel().const_(c.equiv_refl, vec![]);
    let equiv_symm = d.kernel().const_(c.equiv_symm, vec![]);
    let equiv_trans = d.kernel().const_(c.equiv_trans, vec![]);

    // `fun x y => abs (x + -y)`.
    let dist = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let diff = rsub_term(d, c, x, y);
        let body = rabs(d, c, diff);
        let inner = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, inner)
    };
    // `fun a b => CReal.abs_nonneg (a + -b)`.
    let nonneg = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let diff = rsub_term(d, c, a, b);
        let body = d.lemma(c.abs_nonneg, &[diff]);
        let inner = d.lam_fv(b_fv, carrier, body);
        d.lam_fv(a_fv, carrier, inner)
    };

    let dist_congr = d.kernel().const_(p.creal_dist_congr, vec![]);
    let dist_self = d.kernel().const_(p.creal_dist_self, vec![]);
    let dist_equiv = d.kernel().const_(p.creal_dist_equiv, vec![]);
    let dist_comm = d.kernel().const_(p.creal_dist_comm, vec![]);
    let dist_triangle = d.kernel().const_(p.creal_dist_triangle, vec![]);

    let args = [
        carrier,
        equiv,
        equiv_refl,
        equiv_symm,
        equiv_trans,
        dist,
        dist_congr,
        nonneg,
        dist_self,
        dist_equiv,
        dist_comm,
        dist_triangle,
    ];
    let value = mk_instance(d.kernel(), &p.record, &args);
    let ty = d.kernel().const_(p.record.ind, vec![]);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.creal_metric,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.creal_dist : ∀ x y,
/// Equiv (Metric.dist Metric.creal x y) (abs (x + -y))`, proved by
/// `CReal.Equiv.refl`.
///
/// **A probe, not a convenience lemma.** Its admission IS the statement that
/// the `dist` selector reduces definitionally on this instance — the same
/// role `AlgS.Hom.quotient_equiv` plays for the setoid quotient (ADR-1595).
/// Everything downstream that feeds a `Metric.dist Metric.creal …` term to a
/// `CReal.abs`-shaped lemma depends on it.
fn declare_creal_dist_reduces(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let inst = d.kernel().const_(p.creal_metric, vec![]);
    let selector = d.kernel().const_(p.record.sel(DIST), vec![]);
    let lhs = d.apply(selector, &[inst, x, y]);
    let diff = rsub_term(d, c, x, y);
    let rhs = rabs(d, c, diff);
    let body = rrefl(d, c, rhs);

    let value = {
        let t = d.lam_fv(y_fv, carrier, body);
        d.lam_fv(x_fv, carrier, t)
    };
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(y_fv, carrier, concl);
        d.pi_fv(x_fv, carrier, t)
    };
    theorem(d, p.creal_dist, ty, value)
}

// ---------------------------------------------------------------------------
// Theorems about an ARBITRARY metric space. These are the point of having a
// carrier at all: each is proved once and holds on every instance.
// ---------------------------------------------------------------------------

/// The `Metric` binder and its carrier, shared by every generic theorem.
struct Generic {
    metric_ty: ExprId,
    m_fv: u64,
    m: ExprId,
    carrier: ExprId,
}

fn generic(d: &mut IntDev<'_>, p: MetricPrelude) -> Generic {
    let metric_ty = d.kernel().const_(p.record.ind, vec![]);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let s = d.kernel().const_(p.record.sel(CARRIER), vec![]);
    let carrier = d.apply(s, &[m]);
    Generic {
        metric_ty,
        m_fv,
        m,
        carrier,
    }
}

fn field(d: &mut IntDev<'_>, p: MetricPrelude, m: ExprId, i: usize) -> ExprId {
    let s = d.kernel().const_(p.record.sel(i), vec![]);
    d.apply(s, &[m])
}

/// `Metric.dist_self : ∀ (M : Metric) (a : M.carrier),
/// CReal.Equiv (M.dist a a) CReal.zero`.
///
/// One line — `M.distSelf a a (M.equivRefl a)` — and the first statement in
/// this kernel that is true of every metric space rather than of one carrier.
fn declare_dist_self(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = generic(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let refl = field(d, p, g.m, EQUIV_REFL);
    let ha = d.apply(refl, &[a]);
    let ds = field(d, p, g.m, DIST_SELF);
    let body = d.apply(ds, &[a, a, ha]);

    let value = {
        let t = d.lam_fv(a_fv, g.carrier, body);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let dist = field(d, p, g.m, DIST);
        let daa = d.apply(dist, &[a, a]);
        let z = rzero(d, c);
        let concl = req(d, c, daa, z);
        let t = d.pi_fv(a_fv, g.carrier, concl);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    theorem(d, p.dist_self, ty, value)
}

/// `Metric.dist_quadrilateral : ∀ M a b c e,
/// le (M.dist a e) (add (M.dist a b) (add (M.dist b c) (M.dist c e)))`.
///
/// Two `distTriangle`s and one `add_le_add`, generic in `M`.
fn declare_dist_quadrilateral(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = generic(d, p);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let cc = d.kernel().fvar(c_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let dist = field(d, p, g.m, DIST);
    let d_ae = d.apply(dist, &[a, e]);
    let d_ab = d.apply(dist, &[a, b]);
    let d_be = d.apply(dist, &[b, e]);
    let d_bc = d.apply(dist, &[b, cc]);
    let d_ce = d.apply(dist, &[cc, e]);

    let tri = field(d, p, g.m, DIST_TRIANGLE);
    let t1 = d.apply(tri, &[a, b, e]); // le d_ae (d_ab + d_be)
    let t2 = d.apply(tri, &[b, cc, e]); // le d_be (d_bc + d_ce)

    let bc_ce = radd(d, c, d_bc, d_ce);
    let refl_ab = d.lemma(c.le_refl, &[d_ab]);
    let s1 = d.lemma(c.add_le_add, &[d_ab, d_ab, d_be, bc_ce, refl_ab, t2]);
    let ab_be = radd(d, c, d_ab, d_be);
    let rhs = radd(d, c, d_ab, bc_ce);
    let body = d.lemma(c.le_trans, &[d_ae, ab_be, rhs, t1, s1]);

    let value = {
        let t = d.lam_fv(e_fv, g.carrier, body);
        let t = d.lam_fv(c_fv, g.carrier, t);
        let t = d.lam_fv(b_fv, g.carrier, t);
        let t = d.lam_fv(a_fv, g.carrier, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let concl = rle(d, c, d_ae, rhs);
        let t = d.pi_fv(e_fv, g.carrier, concl);
        let t = d.pi_fv(c_fv, g.carrier, t);
        let t = d.pi_fv(b_fv, g.carrier, t);
        let t = d.pi_fv(a_fv, g.carrier, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    theorem(d, p.dist_quadrilateral, ty, value)
}

// ---------------------------------------------------------------------------
// Completeness, stated for an ARBITRARY metric space.
//
// The shape follows `CReal.Converges`/`CReal.Cauchy` (ADR-0512 phase R9)
// deliberately: a **free constant** `K` and a canonical `1/(n+1)`-family rate,
// not the textbook `∀ ε ∃ N ∀ n ≥ N`. That form needs an antitonicity lemma
// for `Rat.natDivSucc` the reals development never proves, and the ℝ instance
// below would then not be an instance of anything already built.
// ---------------------------------------------------------------------------

fn nat_ty_of(d: &mut IntDev<'_>) -> ExprId {
    d.nat_ty()
}

/// `CReal.ofRat (Rat.natDivSucc k n)`.
fn rate_at(d: &mut IntDev<'_>, c: CRealPrelude, k: ExprId, n: ExprId) -> ExprId {
    let q = d.const_app(c.rat.nat_div_succ, &[k, n]);
    d.const_app(c.of_rat, &[q])
}

/// `CReal.ofRat (Rat.add (Rat.natDivSucc k m) (Rat.natDivSucc k n))`.
fn pair_rate_at(d: &mut IntDev<'_>, c: CRealPrelude, k: ExprId, m: ExprId, n: ExprId) -> ExprId {
    let qm = d.const_app(c.rat.nat_div_succ, &[k, m]);
    let qn = d.const_app(c.rat.nat_div_succ, &[k, n]);
    let rat_add = d.int().rat_add;
    let q = d.const_app(rat_add, &[qm, qn]);
    d.const_app(c.of_rat, &[q])
}

/// `Exists elem_ty predicate`, at universe level 1.
fn exists_ty(d: &mut IntDev<'_>, c: CRealPrelude, elem_ty: ExprId, predicate: ExprId) -> ExprId {
    let one = d.level_one();
    let name = c.rat.int.logic.exists_;
    let head = d.kernel().const_(name, vec![one]);
    d.apply(head, &[elem_ty, predicate])
}

/// `Exists.intro elem_ty predicate witness proof`.
fn exists_intro(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    elem_ty: ExprId,
    predicate: ExprId,
    witness: ExprId,
    proof: ExprId,
) -> ExprId {
    let one = d.level_one();
    let name = c.rat.int.logic.exists_intro;
    let head = d.kernel().const_(name, vec![one]);
    d.apply(head, &[elem_ty, predicate, witness, proof])
}

/// `Exists.rec elem_ty predicate (fun _ => target) minor witness`.
fn exists_elim(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    elem_ty: ExprId,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let ex_ty = exists_ty(d, c, elem_ty, predicate);
    let motive = {
        let fv = d.fresh_fvar();
        d.lam_fv(fv, ex_ty, target)
    };
    let one = d.level_one();
    let name = c.rat.int.logic.exists_rec;
    let head = d.kernel().const_(name, vec![one]);
    d.apply(head, &[elem_ty, predicate, motive, minor, witness])
}

/// `Metric.CauchyAt (M : Metric) (f : Nat → M.carrier) (K : Nat) : Prop :=
/// ∀ m n, CReal.le (M.dist (f m) (f n))
///   (CReal.ofRat (Rat.natDivSucc K m + Rat.natDivSucc K n))`.
fn declare_cauchy_at(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = generic(d, p);
    let nat = nat_ty_of(d);
    let seq_ty = d.arrow(nat, g.carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let dist = field(d, p, g.m, DIST);
    let fm = d.apply(f, &[m]);
    let fn_ = d.apply(f, &[n]);
    let dmn = d.apply(dist, &[fm, fn_]);
    let bound = pair_rate_at(d, c, k, m, n);
    let claim = rle(d, c, dmn, bound);
    let body = {
        let over_n = d.pi_fv(n_fv, nat, claim);
        d.pi_fv(m_fv, nat, over_n)
    };

    let value = {
        let t = d.lam_fv(k_fv, nat, body);
        let t = d.lam_fv(f_fv, seq_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(nat, prop);
        let t = d.pi_fv(f_fv, seq_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cauchy_at,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.Cauchy M f := ∃ K, Metric.CauchyAt M f K`.
fn declare_cauchy(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = generic(d, p);
    let nat = nat_ty_of(d);
    let seq_ty = d.arrow(nat, g.carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let predicate = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.cauchy_at, &[g.m, f, k]);
        d.lam_fv(k_fv, nat, body)
    };
    let body = exists_ty(d, c, nat, predicate);

    let value = {
        let t = d.lam_fv(f_fv, seq_ty, body);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(seq_ty, prop);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cauchy,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.TendsToAt M f L K := ∀ n,
/// CReal.le (M.dist (f n) L) (CReal.ofRat (Rat.natDivSucc K n))`.
fn declare_tends_to_at(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = generic(d, p);
    let nat = nat_ty_of(d);
    let seq_ty = d.arrow(nat, g.carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let dist = field(d, p, g.m, DIST);
    let fn_ = d.apply(f, &[n]);
    let dn = d.apply(dist, &[fn_, l]);
    let bound = rate_at(d, c, k, n);
    let claim = rle(d, c, dn, bound);
    let body = d.pi_fv(n_fv, nat, claim);

    let value = {
        let t = d.lam_fv(k_fv, nat, body);
        let t = d.lam_fv(l_fv, g.carrier, t);
        let t = d.lam_fv(f_fv, seq_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(nat, prop);
        let t = d.pi_fv(l_fv, g.carrier, t);
        let t = d.pi_fv(f_fv, seq_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.tends_to_at,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.TendsTo M f L := ∃ K, Metric.TendsToAt M f L K`.
fn declare_tends_to(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = generic(d, p);
    let nat = nat_ty_of(d);
    let seq_ty = d.arrow(nat, g.carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);

    let predicate = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.tends_to_at, &[g.m, f, l, k]);
        d.lam_fv(k_fv, nat, body)
    };
    let body = exists_ty(d, c, nat, predicate);

    let value = {
        let t = d.lam_fv(l_fv, g.carrier, body);
        let t = d.lam_fv(f_fv, seq_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.pi_fv(l_fv, g.carrier, prop);
        let t = d.pi_fv(f_fv, seq_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.tends_to,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.Complete M := ∀ f, Metric.Cauchy M f → ∃ L, Metric.TendsTo M f L`.
///
/// **The statement W2-1 exists to make.** Nothing in it mentions `CReal`
/// except through `M.dist`'s codomain.
fn declare_complete(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = generic(d, p);
    let nat = nat_ty_of(d);
    let seq_ty = d.arrow(nat, g.carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let hyp = d.const_app(p.cauchy, &[g.m, f]);
    let target = {
        let predicate = {
            let l_fv = d.fresh_fvar();
            let l = d.kernel().fvar(l_fv);
            let inner = d.const_app(p.tends_to, &[g.m, f, l]);
            d.lam_fv(l_fv, g.carrier, inner)
        };
        exists_ty(d, c, g.carrier, predicate)
    };
    let claim = d.arrow(hyp, target);
    let body = d.pi_fv(f_fv, seq_ty, claim);

    let value = d.lam_fv(g.m_fv, g.metric_ty, body);
    let ty = {
        let prop = d.kernel().sort_zero();
        d.pi_fv(g.m_fv, g.metric_ty, prop)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.complete,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.creal_complete : Metric.Complete Metric.creal`.
///
/// **The generalization.** `CReal.converges_of_cauchy` is a statement about
/// `CReal` alone, phrased on the rational SAMPLES of the Cauchy
/// representation (`Within (seq (f m) m − seq (f n) n) …`). The metric
/// statement is phrased on `CReal.abs`. Two already-landed bridges cross that
/// gap, one in each direction, and **they are the entire cost of the
/// generalization**:
///
/// - `CReal.cauchy_of_abs_diff_le` turns the metric hypothesis
///   (`|f m − f n| ≤ 1/(K+m+1) + 1/(K+n+1)`) into `CReal.Cauchy f`;
/// - `CReal.close_within_of_within` turns `CReal.Converges`'s sample-level
///   conclusion back into `|f n − L| ≤ 1/(rate+n+1)` with `rate = 1 + (K'+1)`.
///
/// Between them sits `converges_of_cauchy` itself, used as a black box. Three
/// `Exists.rec` eliminations thread the witnesses; all three targets are
/// `Prop`, so `Exists`'s `Prop`-only elimination is never an obstruction —
/// unlike the `Type`-valued constructions ADR-1595 measured, where it is.
fn declare_creal_complete(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = rty(d, c);
    let nat = nat_ty_of(d);
    let seq_ty = d.arrow(nat, carrier);
    let inst = d.kernel().const_(p.creal_metric, vec![]);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    // The goal, shared by all three eliminations.
    let target = {
        let predicate = {
            let l_fv = d.fresh_fvar();
            let l = d.kernel().fvar(l_fv);
            let inner = d.const_app(p.tends_to, &[inst, f, l]);
            d.lam_fv(l_fv, carrier, inner)
        };
        exists_ty(d, c, carrier, predicate)
    };
    let target_pred = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let inner = d.const_app(p.tends_to, &[inst, f, l]);
        d.lam_fv(l_fv, carrier, inner)
    };

    // --- innermost: from `Converges f L`'s witness to `TendsTo`. -----------
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);

    // `fun K' => ∀ n, Within (seq (f n) n − seq L n) (natDivSucc K' n)` —
    // `CReal.Converges f L` delta-reduces to `Exists Nat` of exactly this.
    let converges_pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_ = d.apply(f, &[n]);
        let left = d.const_app(c.seq, &[fn_, n]);
        let right = d.const_app(c.seq, &[l, n]);
        let difference = d.const_app(c.rat.sub, &[left, right]);
        let bound = d.const_app(c.rat.nat_div_succ, &[k, n]);
        let claim = d.const_app(c.within, &[difference, bound]);
        let over_n = d.pi_fv(n_fv, nat, claim);
        d.lam_fv(k_fv, nat, over_n)
    };

    let minor3 = {
        let kp_fv = d.fresh_fvar();
        let kp = d.kernel().fvar(kp_fv);
        let hyp_ty = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let fn_ = d.apply(f, &[n]);
            let left = d.const_app(c.seq, &[fn_, n]);
            let right = d.const_app(c.seq, &[l, n]);
            let difference = d.const_app(c.rat.sub, &[left, right]);
            let bound = d.const_app(c.rat.nat_div_succ, &[kp, n]);
            let claim = d.const_app(c.within, &[difference, bound]);
            d.pi_fv(n_fv, nat, claim)
        };
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // `rate := Nat.add 1 (Nat.add K' 1)`, exactly the numerator
        // `close_within_of_within`'s conclusion carries.
        let one = d.num(1);
        let k1 = NatOps::add(d, kp, one);
        let rate = NatOps::add(d, one, k1);

        let inner_pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = d.const_app(p.tends_to_at, &[inst, f, l, k]);
            d.lam_fv(k_fv, nat, body)
        };
        let inner_proof = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let fn_ = d.apply(f, &[n]);
            let hn = d.apply(h, &[n]);
            let step = d.lemma(c.close_within_of_within, &[fn_, l, n, kp, hn]);
            d.lam_fv(n_fv, nat, step)
        };
        let tends = exists_intro(d, c, nat, inner_pred, rate, inner_proof);
        let body = exists_intro(d, c, carrier, target_pred, l, tends);

        let t = d.lam_fv(h_fv, hyp_ty, body);
        d.lam_fv(kp_fv, nat, t)
    };

    let minor2 = {
        let converges_ty = d.const_app(c.converges, &[f, l]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = exists_elim(d, c, nat, converges_pred, target, h, minor3);
        let t = d.lam_fv(h_fv, converges_ty, body);
        d.lam_fv(l_fv, carrier, t)
    };

    let converges_pred_over_l = {
        let lv_fv = d.fresh_fvar();
        let lv = d.kernel().fvar(lv_fv);
        let body = d.const_app(c.converges, &[f, lv]);
        d.lam_fv(lv_fv, carrier, body)
    };

    let minor1 = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hyp_ty = d.const_app(p.cauchy_at, &[inst, f, k]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let hcauchy = d.lemma(c.cauchy_of_abs_diff_le, &[f, k, h]);
        let hex = d.lemma(c.converges_of_cauchy, &[f, hcauchy]);
        let body = exists_elim(d, c, carrier, converges_pred_over_l, target, hex, minor2);

        let t = d.lam_fv(h_fv, hyp_ty, body);
        d.lam_fv(k_fv, nat, t)
    };

    let cauchy_pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.cauchy_at, &[inst, f, k]);
        d.lam_fv(k_fv, nat, body)
    };
    let hc_ty = d.const_app(p.cauchy, &[inst, f]);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let outer = exists_elim(d, c, nat, cauchy_pred, target, hc, minor1);

    let value = {
        let t = d.lam_fv(hc_fv, hc_ty, outer);
        d.lam_fv(f_fv, seq_ty, t)
    };
    let ty = d.const_app(p.complete, &[inst]);
    theorem(d, p.creal_complete, ty, value)
}

// ---------------------------------------------------------------------------
// The Euclidean plane instance.
//
// `CPoint.distSq` is the SQUARED distance and is not a metric: `d(0,2)² = 4 >
// 1 + 1 = d(0,1)² + d(1,2)²`. `metric_tests::a_squared_distance_is_refused_as_
// a_metric` makes that concrete against this very record. So the instance has
// to take a square root, and the triangle inequality has to be proved in its
// UNSQUARED form — which `CPoint.dist_sq_triangle_sq_bound` (the squared,
// Lagrange-derived bound) and `CPoint.cauchy_schwarz` (squared) do not give.
//
// The gap is exactly one lemma, `Metric.CPoint.dotLeSqrtMul` — unsquared
// Cauchy-Schwarz, `⟨U,V⟩ ≤ sqrt(⟨U,U⟩·⟨V,V⟩)`. It needs `CReal.mul_self_abs`
// to recover `t` from `t²` with NO sign hypothesis (the cross term `⟨U,V⟩`
// has no known sign, and `CReal` has no `le_or_lt`); that is the same fact
// `Complex.abs_add_le` needed, and the reason both were out of reach before
// `mul_self_abs` landed. See `ComplexPrelude::norm_sq_add_le`'s doc for the
// refuted attempts.
// ---------------------------------------------------------------------------

fn pty(d: &mut IntDev<'_>, cp: CPointPrelude) -> ExprId {
    d.kernel().const_(cp.point, vec![])
}
fn psub(d: &mut IntDev<'_>, cp: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(cp.point_sub, &[a, b])
}
fn padd(d: &mut IntDev<'_>, cp: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(cp.point_add, &[a, b])
}
fn pdot(d: &mut IntDev<'_>, cp: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(cp.dot, &[a, b])
}
fn pdist_sq(d: &mut IntDev<'_>, cp: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(cp.dist_sq, &[a, b])
}
fn peq(d: &mut IntDev<'_>, cp: CPointPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(cp.point_equiv, &[a, b])
}
fn rmul(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.mul, &[a, b])
}
fn rsqrt(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.const_app(c.sqrt, &[a])
}

/// `Metric.CPoint.subTelescope : ∀ A B C,
/// CPoint.Equiv (sub A C) (add (sub A B) (sub B C))`.
///
/// Coordinatewise [`declare_creal_sub_telescope`], run backwards. The plane
/// prelude builds this same fact inline (`point_sub_telescope_fact`) but
/// never gives it a name, so there is nothing to apply.
fn declare_cpoint_sub_telescope(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let cc = d.kernel().fvar(c_fv);

    let ac = psub(d, cp, a, cc);
    let ab = psub(d, cp, a, b);
    let bc = psub(d, cp, b, cc);
    let sum = padd(d, cp, ab, bc);

    let mut halves: Vec<ExprId> = Vec::with_capacity(2);
    let mut claims: Vec<ExprId> = Vec::with_capacity(2);
    for projection in [cp.x, cp.y] {
        let lhs = d.const_app(projection, &[ac]);
        let rhs = d.const_app(projection, &[sum]);
        claims.push(req(d, c, lhs, rhs));
        let pa = d.const_app(projection, &[a]);
        let pb = d.const_app(projection, &[b]);
        let pc = d.const_app(projection, &[cc]);
        let forward = d.lemma(p.creal_sub_telescope, &[pa, pb, pc]);
        let npb = rneg(d, c, pb);
        let npc = rneg(d, c, pc);
        let u = radd(d, c, pa, npb);
        let v = radd(d, c, pb, npc);
        let uv = radd(d, c, u, v);
        let target = radd(d, c, pa, npc);
        halves.push(rsymm(d, c, uv, target, forward));
    }

    let intro = c.rat.int.logic.and_intro;
    let body = d.const_app(intro, &[claims[0], claims[1], halves[0], halves[1]]);

    let value = {
        let t = d.lam_fv(c_fv, point, body);
        let t = d.lam_fv(b_fv, point, t);
        d.lam_fv(a_fv, point, t)
    };
    let ty = {
        let concl = peq(d, cp, ac, sum);
        let t = d.pi_fv(c_fv, point, concl);
        let t = d.pi_fv(b_fv, point, t);
        d.pi_fv(a_fv, point, t)
    };
    theorem(d, p.cpoint_sub_telescope, ty, value)
}

/// `Metric.CPoint.dotLeSqrtMul : ∀ U V,
/// CReal.le (dot U V) (CReal.sqrt (mul (dot U U) (dot V V)))`.
///
/// **Unsquared Cauchy–Schwarz.** `CPoint.cauchy_schwarz` gives
/// `⟨U,V⟩² ≤ ⟨U,U⟩⟨V,V⟩`; `sqrt_le_sqrt` carries that under the root, and the
/// only real step is `sqrt(t·t) ~ |t|`, which is `sqrt_sq` at `|t|` composed
/// with `mul_self_abs`. `sqrt_sq` alone will not do it: it needs `0 ≤ t`, and
/// the cross term `⟨U,V⟩` has no known sign.
fn declare_cpoint_dot_le_sqrt_mul(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let uu = pdot(d, cp, u, u);
    let uv = pdot(d, cp, u, v);
    let vv = pdot(d, cp, v, v);
    let uv_sq = rmul(d, c, uv, uv);
    let uu_vv = rmul(d, c, uu, vv);
    let target = rsqrt(d, c, uu_vv);

    let cs = d.lemma(cp.cauchy_schwarz, &[u, v]); // le (uv·uv) (uu·vv)
    let s1 = d.lemma(c.sqrt_le_sqrt, &[uv_sq, uu_vv, cs]); // le (sqrt (uv·uv)) target

    let abs_uv = rabs(d, c, uv);
    let abs_sq = rmul(d, c, abs_uv, abs_uv);
    let msa = d.lemma(c.mul_self_abs, &[uv]); // Equiv (|uv|·|uv|) (uv·uv)
    let msa_symm = rsymm(d, c, abs_sq, uv_sq, msa);
    let sqrt_uv_sq = rsqrt(d, c, uv_sq);
    let sqrt_abs_sq = rsqrt(d, c, abs_sq);
    let sc = d.lemma(c.sqrt_congr, &[uv_sq, abs_sq, msa_symm]);
    let nonneg_abs = d.lemma(c.abs_nonneg, &[uv]);
    let ss = d.lemma(c.sqrt_sq, &[abs_uv, nonneg_abs]); // Equiv (sqrt (|uv|·|uv|)) |uv|
    let (_, e) = rchain(d, c, sqrt_uv_sq, &[(sqrt_abs_sq, sc), (abs_uv, ss)]);

    let refl_t = rrefl(d, c, target);
    let s2 = d.lemma(
        c.le_congr,
        &[sqrt_uv_sq, abs_uv, target, target, e, refl_t, s1],
    );
    let self_le = d.lemma(c.le_abs_self, &[uv]);
    let body = d.lemma(c.le_trans, &[uv, abs_uv, target, self_le, s2]);

    let value = {
        let t = d.lam_fv(v_fv, point, body);
        d.lam_fv(u_fv, point, t)
    };
    let ty = {
        let concl = rle(d, c, uv, target);
        let t = d.pi_fv(v_fv, point, concl);
        d.pi_fv(u_fv, point, t)
    };
    theorem(d, p.cpoint_dot_le_sqrt_mul, ty, value)
}

/// `Metric.CPoint.dist : CPoint → CPoint → CReal
/// := fun P Q => CReal.sqrt (CPoint.distSq P Q)`.
fn declare_cpoint_dist(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let carrier = rty(d, c);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let dsq = pdist_sq(d, cp, a, b);
    let body = rsqrt(d, c, dsq);
    let value = {
        let t = d.lam_fv(b_fv, point, body);
        d.lam_fv(a_fv, point, t)
    };
    let ty = {
        let inner = d.arrow(point, carrier);
        d.arrow(point, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cpoint_dist,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.CPoint.distCongr` — `distSq_congr` under `sqrt_congr`.
fn declare_cpoint_dist_congr(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let ap_fv = d.fresh_fvar();
    let ap = d.kernel().fvar(ap_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let bp_fv = d.fresh_fvar();
    let bp = d.kernel().fvar(bp_fv);

    let ha_ty = peq(d, cp, a, ap);
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);
    let hb_ty = peq(d, cp, b, bp);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let d1 = pdist_sq(d, cp, a, b);
    let d2 = pdist_sq(d, cp, ap, bp);
    let hs = d.lemma(cp.dist_sq_congr, &[a, ap, b, bp, ha, hb]);
    let body = d.lemma(c.sqrt_congr, &[d1, d2, hs]);

    let value = {
        let t = d.lam_fv(hb_fv, hb_ty, body);
        let t = d.lam_fv(ha_fv, ha_ty, t);
        let t = d.lam_fv(bp_fv, point, t);
        let t = d.lam_fv(b_fv, point, t);
        let t = d.lam_fv(ap_fv, point, t);
        d.lam_fv(a_fv, point, t)
    };
    let ty = {
        let l = rsqrt(d, c, d1);
        let r = rsqrt(d, c, d2);
        let concl = req(d, c, l, r);
        let t = d.arrow(hb_ty, concl);
        let t = d.arrow(ha_ty, t);
        let t = d.pi_fv(bp_fv, point, t);
        let t = d.pi_fv(b_fv, point, t);
        let t = d.pi_fv(ap_fv, point, t);
        d.pi_fv(a_fv, point, t)
    };
    theorem(d, p.cpoint_dist_congr, ty, value)
}

/// `Metric.CPoint.distSelf : ∀ A B, CPoint.Equiv A B →
/// Equiv (sqrt (distSq A B)) zero`.
fn declare_cpoint_dist_self(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let h_ty = peq(d, cp, a, b);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let z = rzero(d, c);
    let dsq = pdist_sq(d, cp, a, b);
    let sq = rsqrt(d, c, dsq);
    let sqrt_z = rsqrt(d, c, z);

    let hz = d.lemma(cp.dist_sq_eq_zero_of_equiv, &[a, b, h]); // Equiv (distSq A B) 0
    let s1 = d.lemma(c.sqrt_congr, &[dsq, z, hz]);
    let s2 = d.lemma(c.sqrt_zero, &[]);
    let (_, body) = rchain(d, c, sq, &[(sqrt_z, s1), (z, s2)]);

    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(b_fv, point, t);
        d.lam_fv(a_fv, point, t)
    };
    let ty = {
        let concl = req(d, c, sq, z);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(b_fv, point, t);
        d.pi_fv(a_fv, point, t)
    };
    theorem(d, p.cpoint_dist_self, ty, value)
}

/// `Metric.CPoint.distEquiv : ∀ A B, Equiv (sqrt (distSq A B)) zero →
/// CPoint.Equiv A B`.
///
/// `sqrt D ~ 0` gives `D ~ sqrt D · sqrt D ~ 0 · 0 ~ 0` (`mul_self_sqrt`
/// backwards, then `mul_congr`, then `mul_zero`), and
/// `CPoint.eq_zero_of_distSq_eq_zero` closes it. `mul_self_sqrt` needs
/// `0 ≤ D`, which is `dot_self_nonneg` at `sub A B`.
fn declare_cpoint_dist_equiv(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let z = rzero(d, c);
    let dsq = pdist_sq(d, cp, a, b);
    let sq = rsqrt(d, c, dsq);
    let h_ty = req(d, c, sq, z);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let ab = psub(d, cp, a, b);
    let nonneg = d.lemma(cp.dot_self_nonneg, &[ab]); // le zero (dot (sub A B) (sub A B))
    let sq_sq = rmul(d, c, sq, sq);
    let ms = d.lemma(c.mul_self_sqrt, &[dsq, nonneg]); // Equiv (sqrt D · sqrt D) D
    let ms_symm = rsymm(d, c, sq_sq, dsq, ms); // Equiv D (sqrt D · sqrt D)
    let zz = rmul(d, c, z, z);
    let mc = d.lemma(c.mul_congr, &[sq, z, sq, z, h, h]); // Equiv (sqrt D · sqrt D) (0·0)
    let mz = d.lemma(c.mul_zero, &[z]); // Equiv (0·0) 0
    let (_, dz) = rchain(d, c, dsq, &[(sq_sq, ms_symm), (zz, mc), (z, mz)]);
    let body = d.lemma(cp.eq_zero_of_dist_sq_eq_zero, &[a, b, dz]);

    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(b_fv, point, t);
        d.lam_fv(a_fv, point, t)
    };
    let ty = {
        let concl = peq(d, cp, a, b);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(b_fv, point, t);
        d.pi_fv(a_fv, point, t)
    };
    theorem(d, p.cpoint_dist_equiv, ty, value)
}

/// `Metric.CPoint.distComm` — `distSq_comm` under `sqrt_congr`.
fn declare_cpoint_dist_comm(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let d1 = pdist_sq(d, cp, a, b);
    let d2 = pdist_sq(d, cp, b, a);
    let hc = d.lemma(cp.dist_sq_comm, &[a, b]);
    let body = d.lemma(c.sqrt_congr, &[d1, d2, hc]);

    let value = {
        let t = d.lam_fv(b_fv, point, body);
        d.lam_fv(a_fv, point, t)
    };
    let ty = {
        let l = rsqrt(d, c, d1);
        let r = rsqrt(d, c, d2);
        let concl = req(d, c, l, r);
        let t = d.pi_fv(b_fv, point, concl);
        d.pi_fv(a_fv, point, t)
    };
    theorem(d, p.cpoint_dist_comm, ty, value)
}

/// `Metric.CPoint.distSqExpand : ∀ A B C,
/// Equiv (distSq A C) (add uu (add uv (add uv vv)))`, with `U := sub A B`,
/// `V := sub B C`. The bilinear expansion, via
/// [`declare_cpoint_sub_telescope`] and `CPoint.dot_self_add`.
fn declare_cpoint_dist_sq_expand(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let cc = d.kernel().fvar(c_fv);

    let u = psub(d, cp, a, b);
    let v = psub(d, cp, b, cc);
    let ac = psub(d, cp, a, cc);
    let uv_pt = padd(d, cp, u, v);
    let uu = pdot(d, cp, u, u);
    let uv = pdot(d, cp, u, v);
    let vv = pdot(d, cp, v, v);
    let dsq = pdist_sq(d, cp, a, cc);
    let dot_uvuv = pdot(d, cp, uv_pt, uv_pt);
    let inner = radd(d, c, uv, vv);
    let mid = radd(d, c, uv, inner);
    let expanded = radd(d, c, uu, mid);

    let tel = d.lemma(p.cpoint_sub_telescope, &[a, b, cc]);
    let s1 = d.lemma(cp.dot_congr, &[ac, uv_pt, ac, uv_pt, tel, tel]);
    let s2 = d.lemma(cp.dot_self_add, &[u, v]);
    let (_, body) = rchain(d, c, dsq, &[(dot_uvuv, s1), (expanded, s2)]);

    let value = {
        let t = d.lam_fv(c_fv, point, body);
        let t = d.lam_fv(b_fv, point, t);
        d.lam_fv(a_fv, point, t)
    };
    let ty = {
        let concl = req(d, c, dsq, expanded);
        let t = d.pi_fv(c_fv, point, concl);
        let t = d.pi_fv(b_fv, point, t);
        d.pi_fv(a_fv, point, t)
    };
    theorem(d, p.cpoint_dist_sq_expand, ty, value)
}

/// `Metric.CPoint.distTriangle : ∀ A B C,
/// le (sqrt (distSq A C)) (add (sqrt (distSq A B)) (sqrt (distSq B C)))`.
///
/// **Euclid I.20 on the unsquared distance** — the statement the plane
/// prelude's own `dist_sq_triangle_sq_bound` and `dist_sq_double_sum_bound`
/// deliberately stop short of, because neither is expressible without a
/// square root.
///
/// The route, all of it composition:
///
/// 1. `distSq A C ~ ⟨U,U⟩ + (⟨U,V⟩ + (⟨U,V⟩ + ⟨V,V⟩))`
///    ([`declare_cpoint_dist_sq_expand`]);
/// 2. `⟨U,V⟩ ≤ sqrt(⟨U,U⟩⟨V,V⟩) ~ a·c` where `a = sqrt⟨U,U⟩`, `c = sqrt⟨V,V⟩`
///    ([`declare_cpoint_dot_le_sqrt_mul`] then `CReal.sqrt_mul`);
/// 3. `⟨U,U⟩ ~ a·a` and `⟨V,V⟩ ~ c·c` (`mul_self_sqrt`), so the whole
///    expansion is `≤ a·a + (a·c + (a·c + c·c))`;
/// 4. that right-hand side `~ (a+c)·(a+c)` (two `left_distrib`s, three
///    `mul_comm`s and one `add_assoc` — the ring step, spelled out because
///    the reals prelude has no `sq_add`);
/// 5. `CReal.le_of_sq_le` cancels the square, with `0 ≤ sqrt(distSq A C)` and
///    `0 ≤ a + c` from `sqrt_nonneg`.
fn declare_cpoint_dist_triangle(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let a_fv = d.fresh_fvar();
    let pa = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let pb = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(c_fv);

    let z = rzero(d, c);
    let u = psub(d, cp, pa, pb);
    let v = psub(d, cp, pb, pc);
    let ac = psub(d, cp, pa, pc);
    let uu = pdot(d, cp, u, u);
    let uv = pdot(d, cp, u, v);
    let vv = pdot(d, cp, v, v);

    let d_ab = pdist_sq(d, cp, pa, pb);
    let d_bc = pdist_sq(d, cp, pb, pc);
    let d_ac = pdist_sq(d, cp, pa, pc);

    // `a`, `cq` and `x` are the three unsquared distances. Note `distSq A B`
    // and `dot U U` are the SAME term up to delta; the statement uses the
    // `distSq` spelling and the proof the `dot` one.
    let a = rsqrt(d, c, d_ab);
    let cq = rsqrt(d, c, d_bc);
    let x = rsqrt(d, c, d_ac);
    let s = radd(d, c, a, cq);

    let hu = d.lemma(cp.dot_self_nonneg, &[u]); // le zero uu
    let hv = d.lemma(cp.dot_self_nonneg, &[v]); // le zero vv
    let hw = d.lemma(cp.dot_self_nonneg, &[ac]); // le zero (distSq A C)
    let hx = d.lemma(c.sqrt_nonneg, &[d_ac]);
    let ha = d.lemma(c.sqrt_nonneg, &[d_ab]);
    let hc = d.lemma(c.sqrt_nonneg, &[d_bc]);

    // hs : le zero (a + cq)
    let hs = {
        let zz = radd(d, c, z, z);
        let step = d.lemma(c.add_le_add, &[z, a, z, cq, ha, hc]); // le (0+0) (a+cq)
        let az = d.lemma(c.add_zero, &[z]); // Equiv (0+0) 0
        let refl_s = rrefl(d, c, s);
        d.lemma(c.le_congr, &[zz, z, s, s, az, refl_s, step])
    };

    // e_expand : Equiv (distSq A C) E, E := uu + (uv + (uv + vv))
    let e_expand = d.lemma(p.cpoint_dist_sq_expand, &[pa, pb, pc]);
    let inner = radd(d, c, uv, vv);
    let mid = radd(d, c, uv, inner);
    let big_e = radd(d, c, uu, mid);

    // cross : le uv (a·cq)
    let uu_vv = rmul(d, c, uu, vv);
    let sqrt_uuvv = rsqrt(d, c, uu_vv);
    let a_cq = rmul(d, c, a, cq);
    let cross = {
        let raw = d.lemma(p.cpoint_dot_le_sqrt_mul, &[u, v]); // le uv (sqrt (uu·vv))
        let split = d.lemma(c.sqrt_mul, &[uu, vv, hu, hv]); // Equiv (sqrt (uu·vv)) (a·cq)
        let refl_uv = rrefl(d, c, uv);
        d.lemma(c.le_congr, &[uv, uv, sqrt_uuvv, a_cq, refl_uv, split, raw])
    };

    // huu : le uu (a·a), hvv : le vv (cq·cq)
    let a_a = rmul(d, c, a, a);
    let cq_cq = rmul(d, c, cq, cq);
    let huu = {
        let ms = d.lemma(c.mul_self_sqrt, &[d_ab, hu]); // Equiv (a·a) uu
        let sym = rsymm(d, c, a_a, uu, ms);
        d.lemma(c.le_of_equiv, &[uu, a_a, sym])
    };
    let hvv = {
        let ms = d.lemma(c.mul_self_sqrt, &[d_bc, hv]); // Equiv (cq·cq) vv
        let sym = rsymm(d, c, cq_cq, vv, ms);
        d.lemma(c.le_of_equiv, &[vv, cq_cq, sym])
    };

    // le E E', E' := a·a + (a·cq + (a·cq + cq·cq))
    let inner_p = radd(d, c, a_cq, cq_cq);
    let mid_p = radd(d, c, a_cq, inner_p);
    let big_ep = radd(d, c, a_a, mid_p);
    let l1 = d.lemma(c.add_le_add, &[uv, a_cq, vv, cq_cq, cross, hvv]);
    let l2 = d.lemma(c.add_le_add, &[uv, a_cq, inner, inner_p, cross, l1]);
    let l3 = d.lemma(c.add_le_add, &[uu, a_a, mid, mid_p, huu, l2]);

    // ring : Equiv (s·s) E'
    let s_s = rmul(d, c, s, s);
    let s_a = rmul(d, c, s, a);
    let s_cq = rmul(d, c, s, cq);
    let ring = {
        // (a+cq)·(a+cq) ~ (a+cq)·a + (a+cq)·cq
        let d1 = d.lemma(c.left_distrib, &[s, a, cq]);
        let split = radd(d, c, s_a, s_cq);

        // (a+cq)·a ~ a·a + a·cq
        let left = {
            let comm = d.lemma(c.mul_comm, &[s, a]); // Equiv (s·a) (a·s)
            let a_s = rmul(d, c, a, s);
            let dist = d.lemma(c.left_distrib, &[a, a, cq]); // Equiv (a·s) (a·a + a·cq)
            let sum = radd(d, c, a_a, a_cq);
            let (_, pr) = rchain(d, c, s_a, &[(a_s, comm), (sum, dist)]);
            (sum, pr)
        };
        // (a+cq)·cq ~ a·cq + cq·cq
        let right = {
            let comm = d.lemma(c.mul_comm, &[s, cq]); // Equiv (s·cq) (cq·s)
            let cq_s = rmul(d, c, cq, s);
            let dist = d.lemma(c.left_distrib, &[cq, a, cq]); // Equiv (cq·s) (cq·a + cq·cq)
            let cq_a = rmul(d, c, cq, a);
            let raw = radd(d, c, cq_a, cq_cq);
            let swap = d.lemma(c.mul_comm, &[cq, a]); // Equiv (cq·a) (a·cq)
            let refl_cc = rrefl(d, c, cq_cq);
            let fix = d.lemma(c.add_congr, &[cq_a, a_cq, cq_cq, cq_cq, swap, refl_cc]);
            let (_, pr) = rchain(d, c, s_cq, &[(cq_s, comm), (raw, dist), (inner_p, fix)]);
            (inner_p, pr)
        };

        let (left_t, left_p) = left;
        let (right_t, right_p) = right;
        let combined = radd(d, c, left_t, right_t);
        let cg = d.lemma(c.add_congr, &[s_a, left_t, s_cq, right_t, left_p, right_p]);
        // (a·a + a·cq) + (a·cq + cq·cq) ~ a·a + (a·cq + (a·cq + cq·cq))
        let assoc = d.lemma(c.add_assoc, &[a_a, a_cq, inner_p]);
        let (_, pr) = rchain(d, c, s_s, &[(split, d1), (combined, cg), (big_ep, assoc)]);
        pr
    };

    // le (x·x) (s·s)
    let x_x = rmul(d, c, x, x);
    let sq_bound = {
        let ms = d.lemma(c.mul_self_sqrt, &[d_ac, hw]); // Equiv (x·x) (distSq A C)
        let (_, to_e) = rchain(d, c, x_x, &[(d_ac, ms), (big_e, e_expand)]);
        let e_to_xx = rsymm(d, c, x_x, big_e, to_e);
        let ep_to_ss = rsymm(d, c, s_s, big_ep, ring);
        d.lemma(
            c.le_congr,
            &[big_e, x_x, big_ep, s_s, e_to_xx, ep_to_ss, l3],
        )
    };

    let body = d.lemma(c.le_of_sq_le, &[x, s, hx, hs, sq_bound]);

    let value = {
        let t = d.lam_fv(c_fv, point, body);
        let t = d.lam_fv(b_fv, point, t);
        d.lam_fv(a_fv, point, t)
    };
    let ty = {
        let concl = rle(d, c, x, s);
        let t = d.pi_fv(c_fv, point, concl);
        let t = d.pi_fv(b_fv, point, t);
        d.pi_fv(a_fv, point, t)
    };
    theorem(d, p.cpoint_dist_triangle, ty, value)
}

/// `Metric.cpoint : Metric` — the Euclidean plane.
fn declare_cpoint_metric(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);

    let equiv = d.kernel().const_(cp.point_equiv, vec![]);
    let equiv_refl = d.kernel().const_(p.cpoint_equiv_refl, vec![]);
    let equiv_symm = d.kernel().const_(p.cpoint_equiv_symm, vec![]);
    let equiv_trans = d.kernel().const_(p.cpoint_equiv_trans, vec![]);
    let dist = d.kernel().const_(p.cpoint_dist, vec![]);

    let nonneg = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let dsq = pdist_sq(d, cp, a, b);
        let body = d.lemma(c.sqrt_nonneg, &[dsq]);
        let inner = d.lam_fv(b_fv, point, body);
        d.lam_fv(a_fv, point, inner)
    };

    let dist_congr = d.kernel().const_(p.cpoint_dist_congr, vec![]);
    let dist_self = d.kernel().const_(p.cpoint_dist_self, vec![]);
    let dist_equiv = d.kernel().const_(p.cpoint_dist_equiv, vec![]);
    let dist_comm = d.kernel().const_(p.cpoint_dist_comm, vec![]);
    let dist_triangle = d.kernel().const_(p.cpoint_dist_triangle, vec![]);

    let args = [
        point,
        equiv,
        equiv_refl,
        equiv_symm,
        equiv_trans,
        dist,
        dist_congr,
        nonneg,
        dist_self,
        dist_equiv,
        dist_comm,
        dist_triangle,
    ];
    let value = mk_instance(d.kernel(), &p.record, &args);
    let ty = d.kernel().const_(p.record.ind, vec![]);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.cpoint_metric,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.cpoint_dist : ∀ P Q,
/// Equiv (Metric.dist Metric.cpoint P Q) (CReal.sqrt (CPoint.distSq P Q))`,
/// by `CReal.Equiv.refl` — the same reduction probe the ℝ instance carries.
fn declare_cpoint_dist_reduces(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let inst = d.kernel().const_(p.cpoint_metric, vec![]);
    let selector = d.kernel().const_(p.record.sel(DIST), vec![]);
    let lhs = d.apply(selector, &[inst, a, b]);
    let dsq = pdist_sq(d, cp, a, b);
    let rhs = rsqrt(d, c, dsq);
    let body = rrefl(d, c, rhs);

    let value = {
        let t = d.lam_fv(b_fv, point, body);
        d.lam_fv(a_fv, point, t)
    };
    let ty = {
        let concl = req(d, c, lhs, rhs);
        let t = d.pi_fv(b_fv, point, concl);
        d.pi_fv(a_fv, point, t)
    };
    theorem(d, p.cpoint_dist_reduces, ty, value)
}

// ---------------------------------------------------------------------------
// `CPoint.Equiv`'s setoid infrastructure. The plane prelude builds
// reflexivity inline (`point_equiv_refl`) and never names symmetry or
// transitivity at all -- there was nothing that needed them until a record
// asked for the three as FIELDS. Each is `And.intro` over the two
// coordinates.
// ---------------------------------------------------------------------------

/// `Metric.CPoint.equivRefl : ∀ P, CPoint.Equiv P P`.
fn declare_cpoint_equiv_refl(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let mut claims: Vec<ExprId> = Vec::with_capacity(2);
    let mut proofs: Vec<ExprId> = Vec::with_capacity(2);
    for projection in [cp.x, cp.y] {
        let pa = d.const_app(projection, &[a]);
        claims.push(req(d, c, pa, pa));
        proofs.push(rrefl(d, c, pa));
    }
    let intro = c.rat.int.logic.and_intro;
    let body = d.const_app(intro, &[claims[0], claims[1], proofs[0], proofs[1]]);

    let value = d.lam_fv(a_fv, point, body);
    let ty = {
        let concl = peq(d, cp, a, a);
        d.pi_fv(a_fv, point, concl)
    };
    theorem(d, p.cpoint_equiv_refl, ty, value)
}

/// `Metric.CPoint.equivSymm : ∀ P Q, CPoint.Equiv P Q → CPoint.Equiv Q P`.
fn declare_cpoint_equiv_symm(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let h_ty = peq(d, cp, a, b);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let ax = d.const_app(cp.x, &[a]);
    let bx = d.const_app(cp.x, &[b]);
    let ay = d.const_app(cp.y, &[a]);
    let by = d.const_app(cp.y, &[b]);
    let claim_x = req(d, c, ax, bx);
    let claim_y = req(d, c, ay, by);
    let hx = d.and_left(claim_x, claim_y, h);
    let hy = d.and_right(claim_x, claim_y, h);
    let px = rsymm(d, c, ax, bx, hx);
    let py = rsymm(d, c, ay, by, hy);
    let goal_x = req(d, c, bx, ax);
    let goal_y = req(d, c, by, ay);
    let intro = c.rat.int.logic.and_intro;
    let body = d.const_app(intro, &[goal_x, goal_y, px, py]);

    let value = {
        let t = d.lam_fv(h_fv, h_ty, body);
        let t = d.lam_fv(b_fv, point, t);
        d.lam_fv(a_fv, point, t)
    };
    let ty = {
        let concl = peq(d, cp, b, a);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(b_fv, point, t);
        d.pi_fv(a_fv, point, t)
    };
    theorem(d, p.cpoint_equiv_symm, ty, value)
}

/// `Metric.CPoint.equivTrans : ∀ P Q R,
/// CPoint.Equiv P Q → CPoint.Equiv Q R → CPoint.Equiv P R`.
fn declare_cpoint_equiv_trans(
    d: &mut IntDev<'_>,
    cp: CPointPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let c = cp.creal;
    let point = pty(d, cp);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let cc = d.kernel().fvar(c_fv);

    let h1_ty = peq(d, cp, a, b);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_ty = peq(d, cp, b, cc);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let ax = d.const_app(cp.x, &[a]);
    let bx = d.const_app(cp.x, &[b]);
    let cx = d.const_app(cp.x, &[cc]);
    let ay = d.const_app(cp.y, &[a]);
    let by = d.const_app(cp.y, &[b]);
    let cy = d.const_app(cp.y, &[cc]);

    let ab_x = req(d, c, ax, bx);
    let ab_y = req(d, c, ay, by);
    let bc_x = req(d, c, bx, cx);
    let bc_y = req(d, c, by, cy);

    let h1x = d.and_left(ab_x, ab_y, h1);
    let h1y = d.and_right(ab_x, ab_y, h1);
    let h2x = d.and_left(bc_x, bc_y, h2);
    let h2y = d.and_right(bc_x, bc_y, h2);

    let px = rtrans(d, c, ax, bx, cx, h1x, h2x);
    let py = rtrans(d, c, ay, by, cy, h1y, h2y);
    let goal_x = req(d, c, ax, cx);
    let goal_y = req(d, c, ay, cy);
    let intro = c.rat.int.logic.and_intro;
    let body = d.const_app(intro, &[goal_x, goal_y, px, py]);

    let value = {
        let t = d.lam_fv(h2_fv, h2_ty, body);
        let t = d.lam_fv(h1_fv, h1_ty, t);
        let t = d.lam_fv(c_fv, point, t);
        let t = d.lam_fv(b_fv, point, t);
        d.lam_fv(a_fv, point, t)
    };
    let ty = {
        let concl = peq(d, cp, a, cc);
        let t = d.arrow(h2_ty, concl);
        let t = d.arrow(h1_ty, t);
        let t = d.pi_fv(c_fv, point, t);
        let t = d.pi_fv(b_fv, point, t);
        d.pi_fv(a_fv, point, t)
    };
    theorem(d, p.cpoint_equiv_trans, ty, value)
}

#[cfg(test)]
mod metric_tests;
