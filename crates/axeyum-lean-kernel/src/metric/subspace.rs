//! `Metric.subspace` — **a predicate on a metric space is now a metric space**
//! (ADR-1613, closing the half of W2-10 that ADR-1602 split off).
//!
//! ADR-1602 recorded the obstruction precisely: `Metric.dist` is *total* on its
//! carrier, so a subspace's distance is the ambient one **restricted**, and a
//! restriction needs a carrier built from a predicate. This kernel had no way
//! to build one, so every notion in `metric/continuity.rs` and
//! `metric/compactness.rs` comes in a relativized `*On P` form instead, with
//! `P : M.carrier → Prop` threaded through by hand.
//!
//! `Subtype` (ADR-1613, `sigma_prelude.rs`) removes the obstruction, and the
//! construction is the shortest one in this layer:
//!
//! ```text
//! Metric.subspace (M : Metric) (P : M.carrier → Prop) : Metric
//!   carrier := Subtype.{1} M.carrier P
//!   equiv   := fun x y => M.equiv (Subtype.val x) (Subtype.val y)
//!   dist    := fun x y => M.dist  (Subtype.val x) (Subtype.val y)
//!   …and every one of the other nine fields is M's own field applied to
//!      `Subtype.val`, verbatim.
//! ```
//!
//! **Why all nine laws are free.** `Subtype.val` ι-reduces on the literal
//! constructor, so the subspace's `equiv` and `dist` are *definitionally* the
//! ambient ones on the underlying values. Every law the record demands —
//! `distTriangle`, `distComm`, `distEquiv`, … — therefore has, after
//! β-reduction, exactly the statement `M`'s own field already proves, at the
//! three points `Subtype.val x`, `Subtype.val y`, `Subtype.val z`. No
//! congruence obligation, no side condition, and **no hypothesis on `P`**: a
//! subspace of a metric space is a metric space for *any* predicate, including
//! the empty one, because none of the twelve fields asserts the carrier is
//! inhabited.
//!
//! Universe check: `M.carrier : Sort 1`, so this is `Subtype.{1}`, whose result
//! universe is `Sort (max 1 1)` — definitionally `Sort 1`, exactly the carrier
//! universe `declare_record` fixes. The subspace is a first-class `Metric`, not
//! a weaker relativized shadow.
//!
//! # What is declared
//!
//! | name | type |
//! | --- | --- |
//! | `Metric.subspace` | `Metric → (M.carrier → Prop) → Metric` |
//! | `Metric.subspace_carrier` | `∀ M P, (Metric.subspace M P).carrier = Subtype M.carrier P` |
//! | `Metric.subspace_dist` | `∀ M P x y, (Metric.subspace M P).dist x y = M.dist x.val y.val` |
//! | `Metric.crealIntervalSpace` | `CReal → CReal → Metric` — `[a,b] ⊂ ℝ` as a metric space in its own right |
//!
//! Both equations are `Eq`, not `CReal.Equiv`, and both close by `Eq.refl`:
//! they are *definitional* facts made checkable, which is the whole content of
//! "the distance is the ambient one restricted".
//!
//! `Metric.crealIntervalSpace a b := Metric.subspace Metric.creal
//! (Metric.Interval a b)` is the first instance and the reason this is not an
//! empty generality: `Metric.Interval` was previously usable only as the `P` of
//! a `*On` form, and is now a metric space that `Metric.Complete`,
//! `Metric.Cauchy` and everything else in the layer applies to directly.
//!
//! # What this deliberately does NOT do
//!
//! It does not migrate the existing `*On` forms. `Metric.CompactOn`,
//! `Metric.TotallyBoundedOn`, `Metric.CompleteOn` and the continuity family
//! keep their relativized statements and their proofs; whether they should be
//! restated as facts about `Metric.subspace` is a separate decision with real
//! proof cost, and this file only establishes that the restatement is now
//! *expressible*.

use super::{
    CARRIER, DIST, DIST_COMM, DIST_CONGR, DIST_EQUIV, DIST_NONNEG, DIST_SELF, DIST_TRIANGLE, EQUIV,
    EQUIV_REFL, EQUIV_SYMM, EQUIV_TRANS, MetricPrelude,
};
use crate::CRealPrelude;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;
use crate::{Kernel, LevelId};

/// The interned names this file owns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SubspaceNames {
    /// `Metric.subspace : Π (M : Metric), (M.carrier → Prop) → Metric` — the
    /// ambient space restricted to a predicate, carried by `Subtype`.
    pub subspace: NameId,
    /// `Metric.subspace_carrier : ∀ M P,
    /// Eq (Sort 1) (Metric.carrier (Metric.subspace M P))
    ///    (Subtype M.carrier P)` — the carrier IS the subtype, by `Eq.refl`.
    pub subspace_carrier: NameId,
    /// `Metric.subspace_dist : ∀ M P (x y : Subtype M.carrier P),
    /// Eq CReal (Metric.dist (Metric.subspace M P) x y)
    ///          (Metric.dist M (Subtype.val x) (Subtype.val y))` — the
    /// distance is the ambient one restricted, by `Eq.refl`.
    pub subspace_dist: NameId,
    /// `Metric.crealIntervalSpace : CReal → CReal → Metric` — `[a,b] ⊂ ℝ` as a
    /// metric space, the first instance of `Metric.subspace`.
    pub creal_interval_space: NameId,
}

impl SubspaceNames {
    /// Every name this file owns, for the inventory tests. Derived from the
    /// struct's own fields, never from a literal list somewhere else.
    pub fn all(&self) -> Vec<(&'static str, NameId)> {
        vec![
            ("Metric.subspace", self.subspace),
            ("Metric.subspace_carrier", self.subspace_carrier),
            ("Metric.subspace_dist", self.subspace_dist),
            ("Metric.crealIntervalSpace", self.creal_interval_space),
        ]
    }
}

pub(super) fn intern(kernel: &mut Kernel, metric: NameId) -> SubspaceNames {
    SubspaceNames {
        subspace: kernel.name_str(metric, "subspace"),
        subspace_carrier: kernel.name_str(metric, "subspace_carrier"),
        subspace_dist: kernel.name_str(metric, "subspace_dist"),
        creal_interval_space: kernel.name_str(metric, "crealIntervalSpace"),
    }
}

/// The pieces every declaration in this file opens: the ambient `M`, its
/// carrier, the predicate `P`, the subtype carrier, and `Subtype.val`.
struct Ambient {
    metric_ty: ExprId,
    m_fv: u64,
    m: ExprId,
    predicate_ty: ExprId,
    p_fv: u64,
    predicate: ExprId,
    /// `Subtype.{1} M.carrier P`.
    sub_carrier: ExprId,
    /// `Subtype.val.{1} M.carrier P` — apply to one argument.
    val_head: ExprId,
    /// The universe level `1`.
    one: LevelId,
}

fn ambient(d: &mut IntDev<'_>, c: CRealPrelude, p: MetricPrelude) -> Ambient {
    let logic = c.rat.int.logic;
    let zero = d.kernel().level_zero();
    let one = d.kernel().level_succ(zero);

    let metric_ty = d.kernel().const_(p.record.ind, vec![]);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let carrier = {
        let s = d.kernel().const_(p.record.sel(CARRIER), vec![]);
        d.apply(s, &[m])
    };
    let prop = d.kernel().sort_zero();
    let predicate_ty = d.arrow(carrier, prop);
    let p_fv = d.fresh_fvar();
    let predicate = d.kernel().fvar(p_fv);

    let sub_carrier = {
        let head = d.kernel().const_(logic.sigma.subtype, vec![one]);
        d.apply(head, &[carrier, predicate])
    };
    let val_head = {
        let head = d.kernel().const_(logic.sigma.subtype_val, vec![one]);
        d.apply(head, &[carrier, predicate])
    };
    Ambient {
        metric_ty,
        m_fv,
        m,
        predicate_ty,
        p_fv,
        predicate,
        sub_carrier,
        val_head,
        one,
    }
}

/// `M`'s field `i`, already applied to `M`.
fn field(d: &mut IntDev<'_>, p: MetricPrelude, m: ExprId, i: usize) -> ExprId {
    let s = d.kernel().const_(p.record.sel(i), vec![]);
    d.apply(s, &[m])
}

/// `Metric.subspace M P`.
fn subspace_app(d: &mut IntDev<'_>, p: MetricPrelude, m: ExprId, predicate: ExprId) -> ExprId {
    let name = p.subspace.subspace;
    d.const_app(name, &[m, predicate])
}

/// Build one field of the subspace: `fun (x₁ … xₙ : sub_carrier) (h₁ … : …) =>
/// M.<field> (val x₁) … h₁ …`.
///
/// `points` is the number of carrier-sorted binders (all of which are passed
/// through `Subtype.val`), and `hyps` the proof binders that follow, each given
/// as the type it must have *at the underlying values*. Every hypothesis type
/// the record demands is β-equal to the one built here, because the subspace's
/// `equiv`/`dist` are literally the ambient ones composed with `Subtype.val`.
fn lift_field(
    d: &mut IntDev<'_>,
    a: &Ambient,
    head: ExprId,
    points: usize,
    hyps: &[(usize, usize, HypKind)],
    c: CRealPrelude,
    p: MetricPrelude,
) -> ExprId {
    let point_fvs: Vec<u64> = (0..points).map(|_| d.fresh_fvar()).collect();
    let point_vars: Vec<ExprId> = point_fvs.iter().map(|&fv| d.kernel().fvar(fv)).collect();
    let vals: Vec<ExprId> = point_vars
        .iter()
        .map(|&x| {
            let head = a.val_head;
            d.apply(head, &[x])
        })
        .collect();

    let hyp_fvs: Vec<u64> = hyps.iter().map(|_| d.fresh_fvar()).collect();
    let hyp_tys: Vec<ExprId> = hyps
        .iter()
        .map(|&(left, right, kind)| hyp_type(d, a, c, p, vals[left], vals[right], kind))
        .collect();
    let hyp_vars: Vec<ExprId> = hyp_fvs.iter().map(|&fv| d.kernel().fvar(fv)).collect();

    let mut args = vals.clone();
    args.extend(hyp_vars);
    let mut body = d.apply(head, &args);
    for (&fv, &ty) in hyp_fvs.iter().zip(hyp_tys.iter()).rev() {
        body = d.lam_fv(fv, ty, body);
    }
    for &fv in point_fvs.iter().rev() {
        body = d.lam_fv(fv, a.sub_carrier, body);
    }
    body
}

/// Which of the two hypothesis shapes a lifted field's proof binder has.
#[derive(Clone, Copy)]
enum HypKind {
    /// `M.equiv u v`.
    Equiv,
    /// `CReal.Equiv (M.dist u v) CReal.zero`.
    DistZero,
}

fn hyp_type(
    d: &mut IntDev<'_>,
    a: &Ambient,
    c: CRealPrelude,
    p: MetricPrelude,
    left: ExprId,
    right: ExprId,
    kind: HypKind,
) -> ExprId {
    match kind {
        HypKind::Equiv => {
            let equiv = field(d, p, a.m, EQUIV);
            d.apply(equiv, &[left, right])
        }
        HypKind::DistZero => {
            let dist = field(d, p, a.m, DIST);
            let distance = d.apply(dist, &[left, right]);
            let zero = d.kernel().const_(c.zero, vec![]);
            let name = c.equiv;
            d.const_app(name, &[distance, zero])
        }
    }
}

/// `Metric.subspace : Π (M : Metric) (P : M.carrier → Prop), Metric`.
///
/// Twelve field values: the carrier is the subtype, and the other eleven are
/// `M`'s own fields with every carrier-sorted argument routed through
/// `Subtype.val`. The proof binders need no adjustment at all — the subspace's
/// `equiv` and `dist` β-reduce to the ambient ones at the underlying values, so
/// a hypothesis of the shape the record demands IS a hypothesis of the shape
/// `M`'s field consumes.
fn declare_subspace(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let a = ambient(d, c, p);

    let mut fields = Vec::with_capacity(12);
    fields.push(a.sub_carrier);
    for (index, points, hyps) in [
        (EQUIV, 2, &[][..]),
        (EQUIV_REFL, 1, &[]),
        (EQUIV_SYMM, 2, &[(0, 1, HypKind::Equiv)][..]),
        (
            EQUIV_TRANS,
            3,
            &[(0, 1, HypKind::Equiv), (1, 2, HypKind::Equiv)][..],
        ),
        (DIST, 2, &[]),
        (
            DIST_CONGR,
            4,
            &[(0, 1, HypKind::Equiv), (2, 3, HypKind::Equiv)][..],
        ),
        (DIST_NONNEG, 2, &[]),
        (DIST_SELF, 2, &[(0, 1, HypKind::Equiv)][..]),
        (DIST_EQUIV, 2, &[(0, 1, HypKind::DistZero)][..]),
        (DIST_COMM, 2, &[]),
        (DIST_TRIANGLE, 3, &[]),
    ] {
        let head = field(d, p, a.m, index);
        let value = lift_field(d, &a, head, points, hyps, c, p);
        fields.push(value);
    }

    let instance = mk_instance(d.kernel(), &p.record, &fields);
    let value = {
        let with_predicate = d.lam_fv(a.p_fv, a.predicate_ty, instance);
        d.lam_fv(a.m_fv, a.metric_ty, with_predicate)
    };
    let ty = {
        let inner = d.pi_fv(a.p_fv, a.predicate_ty, a.metric_ty);
        d.pi_fv(a.m_fv, a.metric_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.subspace.subspace,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.subspace_carrier : ∀ M P,
/// Eq (Sort 1) (Metric.carrier (Metric.subspace M P)) (Subtype M.carrier P)`.
///
/// `Eq.refl`. The point is not that it is hard but that it is *checkable*: the
/// subspace's carrier is the subtype on the nose, not up to an isomorphism
/// someone would then have to transport along.
fn declare_subspace_carrier(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let a = ambient(d, c, p);
    let logic = c.rat.int.logic;
    let two = d.kernel().level_succ(a.one);
    let sort_one = d.kernel().sort(a.one);

    let lhs = {
        let space = subspace_app(d, p, a.m, a.predicate);
        let s = d.kernel().const_(p.record.sel(CARRIER), vec![]);
        d.apply(s, &[space])
    };
    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![two]);
        d.apply(head, &[sort_one, lhs, a.sub_carrier])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![two]);
        d.apply(head, &[sort_one, a.sub_carrier])
    };
    let ty = {
        let inner = d.pi_fv(a.p_fv, a.predicate_ty, stmt);
        d.pi_fv(a.m_fv, a.metric_ty, inner)
    };
    let value = {
        let inner = d.lam_fv(a.p_fv, a.predicate_ty, proof);
        d.lam_fv(a.m_fv, a.metric_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.subspace.subspace_carrier,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Metric.subspace_dist : ∀ M P x y,
/// Eq CReal ((Metric.subspace M P).dist x y) (M.dist x.val y.val)`.
///
/// This is ADR-1602's obstruction, discharged: "the distance is the ambient one
/// restricted" is now a theorem of this kernel rather than a sentence in a
/// design note. `Eq.refl` again — restriction is definitional here.
fn declare_subspace_dist(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let a = ambient(d, c, p);
    let logic = c.rat.int.logic;
    let creal_ty = d.kernel().const_(c.creal, vec![]);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let val_x = {
        let head = a.val_head;
        d.apply(head, &[x])
    };
    let val_y = {
        let head = a.val_head;
        d.apply(head, &[y])
    };

    let lhs = {
        let space = subspace_app(d, p, a.m, a.predicate);
        let dist = field(d, p, space, DIST);
        d.apply(dist, &[x, y])
    };
    let rhs = {
        let dist = field(d, p, a.m, DIST);
        d.apply(dist, &[val_x, val_y])
    };
    let stmt = {
        let head = d.kernel().const_(logic.eq, vec![a.one]);
        d.apply(head, &[creal_ty, lhs, rhs])
    };
    let proof = {
        let head = d.kernel().const_(logic.eq_refl, vec![a.one]);
        d.apply(head, &[creal_ty, rhs])
    };
    let ty = {
        let with_y = d.pi_fv(y_fv, a.sub_carrier, stmt);
        let with_x = d.pi_fv(x_fv, a.sub_carrier, with_y);
        let inner = d.pi_fv(a.p_fv, a.predicate_ty, with_x);
        d.pi_fv(a.m_fv, a.metric_ty, inner)
    };
    let value = {
        let with_y = d.lam_fv(y_fv, a.sub_carrier, proof);
        let with_x = d.lam_fv(x_fv, a.sub_carrier, with_y);
        let inner = d.lam_fv(a.p_fv, a.predicate_ty, with_x);
        d.lam_fv(a.m_fv, a.metric_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.subspace.subspace_dist,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Metric.crealIntervalSpace (a b : CReal) : Metric
///   := Metric.subspace Metric.creal (Metric.Interval a b)`.
///
/// The first instance, and the reason `Metric.subspace` is not an empty
/// generality: `Metric.Interval` existed only as the `P` of a relativized `*On`
/// form, and is now a metric space in its own right.
fn declare_creal_interval_space(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let creal_ty = d.kernel().const_(c.creal, vec![]);
    let metric_ty = d.kernel().const_(p.record.ind, vec![]);
    let creal_metric = d.kernel().const_(p.creal_metric, vec![]);

    let a_fv = d.fresh_fvar();
    let left = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let right = d.kernel().fvar(b_fv);

    let predicate = {
        let name = p.continuity.interval;
        d.const_app(name, &[left, right])
    };
    let body = subspace_app(d, p, creal_metric, predicate);

    let value = {
        let with_b = d.lam_fv(b_fv, creal_ty, body);
        d.lam_fv(a_fv, creal_ty, with_b)
    };
    let ty = {
        let with_b = d.arrow(creal_ty, metric_ty);
        d.arrow(creal_ty, with_b)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.subspace.creal_interval_space,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// Land every declaration this file owns, in dependency order.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_all(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    declare_subspace(d, c, p)?;
    declare_subspace_carrier(d, c, p)?;
    declare_subspace_dist(d, c, p)?;
    declare_creal_interval_space(d, c, p)
}
