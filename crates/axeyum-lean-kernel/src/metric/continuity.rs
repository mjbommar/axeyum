//! `Metric.UniformlyContinuous*` / `Metric.Continuous*` — **W2-2, continuity
//! as a notion of the metric layer rather than of one carrier.**
//!
//! Before this file the library had exactly two continuity vocabularies and
//! they were parallel rather than connected:
//!
//! - `CReal.UniformlyContinuousOn F a b : Type` — a one-constructor inductive
//!   carrying `modulus : Nat → Nat` as **data** plus a `Prop`-valued `spec`,
//!   stated only for `F : CReal → CReal` on a real interval;
//! - `CReal.ContinuousAt F x : Prop` — *sequential* continuity, phrased
//!   through `CReal.Converges`, again only on ℝ.
//!
//! Neither mentions a metric space, and nothing related them. This file
//! states both notions over an **arbitrary pair of metric spaces** and then
//! proves the two bridges that make the vocabularies one vocabulary:
//! `Metric.continuous_of_uniformly_continuous` (uniform ⇒ pointwise, and
//! **only** that direction — see below) and
//! `Metric.creal_uniformly_continuous_on` (`CReal.UniformlyContinuousOn` ⇒
//! the metric notion, relativized to the interval predicate).
//!
//! ## The shape, and why it is not `∀ ε ∃ δ`
//!
//! Every rate here is one `Rat.natDivSucc 1 k`, i.e. `1/(k+1)`, and the
//! modulus is a **free `Nat → Nat` argument** with an `∃` wrapped around it
//! exactly one level up. That is `Metric.CauchyAt`/`Metric.Cauchy`'s own
//! shape (ADR-1602 §"Completeness, stated for an ARBITRARY metric space"),
//! and it is deliberate: the textbook `∀ ε > 0, ∃ δ > 0` form needs an
//! antitonicity lemma for `Rat.natDivSucc` that the reals development never
//! proves, and — decisively — `CReal.UniformlyContinuousOn`'s own `spec` is
//! already in the `1/(modulus n + 1) → 1/(n+1)` form, so the `With` predicate
//! below is *definitionally* that spec once `M = N = Metric.creal`. The
//! bridge is therefore four `And` projections and one application, with no
//! estimate at all. Had either side been phrased differently the bridge would
//! have needed a genuine proof; that it does not is the measurement.
//!
//! ## The constructive subtlety: the implication runs one way
//!
//! `Metric.continuous_of_uniformly_continuous` is proved here. **Its converse
//! is not, and must not be**, even on a compact space, and the reason is not
//! that the proof is hard: pointwise continuity supplies, for each point `x`,
//! *some* modulus `k`, with no claim that a single `k` works for all `x`, and
//! extracting one is a choice principle over the carrier — classically the
//! Heine–Cantor theorem, whose usual proof is a finite subcover argument that
//! this library deliberately does not have (ADR-1602 declines open covers).
//! Bishop's own development takes the opposite route and makes *uniform*
//! continuity on a compact set the primitive notion, precisely because the
//! pointwise one does not recover it. So the arrow here is one-directional on
//! purpose, and `metric_tests` pins that: nothing in this file claims the
//! converse, and the module documentation is the record of why.
//!
//! ## What is relativized, and why there is no subspace
//!
//! ADR-1602's §"The one thing that is genuinely blocked" records that this
//! kernel has no `Subtype`, so a subspace of a metric space is a **predicate
//! on the ambient carrier**, not a new carrier. Every `*On` variant below
//! takes `P : M.carrier → Prop` and quantifies `P x → P y → …`. That is the
//! established idiom (`CReal.UniformlyContinuousOn`, `CReal.supOn`,
//! `CReal.HasDerivativeOn` are all interval-relativized), not a new one.
//! [`ContinuityNames::interval`] is the predicate that makes ℝ's closed
//! interval one of these.

#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::DIST;
use super::MetricPrelude;
use crate::CRealPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// The kernel names `metric/continuity.rs` declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ContinuityNames {
    /// `Metric.UniformlyContinuousWith (M N : Metric)
    /// (F : M.carrier → N.carrier) (mu : Nat → Nat) : Prop := ∀ n x y,
    /// CReal.le (M.dist x y) (CReal.ofRat (Rat.natDivSucc 1 (mu n))) →
    /// CReal.le (N.dist (F x) (F y)) (CReal.ofRat (Rat.natDivSucc 1 n))`.
    pub uniformly_continuous_with: NameId,
    /// `Metric.UniformlyContinuous M N F := ∃ mu,
    /// Metric.UniformlyContinuousWith M N F mu`.
    pub uniformly_continuous: NameId,
    /// `Metric.UniformlyContinuousOnWith M N (P : M.carrier → Prop) F mu :
    /// Prop` — [`Self::uniformly_continuous_with`] with `P x → P y →` in
    /// front. The subspace is a predicate, not a carrier (ADR-1602).
    pub uniformly_continuous_on_with: NameId,
    /// `Metric.UniformlyContinuousOn M N P F := ∃ mu,
    /// Metric.UniformlyContinuousOnWith M N P F mu`.
    pub uniformly_continuous_on: NameId,
    /// `Metric.ContinuousAtWith M N F x (k : Nat → Nat) : Prop := ∀ n y,
    /// CReal.le (M.dist x y) (ofRat (natDivSucc 1 (k n))) →
    /// CReal.le (N.dist (F x) (F y)) (ofRat (natDivSucc 1 n))`.
    pub continuous_at_with: NameId,
    /// `Metric.ContinuousAt M N F x := ∃ k, Metric.ContinuousAtWith M N F x k`
    /// — **pointwise**: the modulus may depend on `x`.
    pub continuous_at: NameId,
    /// `Metric.Continuous M N F := ∀ x, Metric.ContinuousAt M N F x`.
    pub continuous: NameId,
    /// `Metric.ContinuousOnAtWith M N P F x k : Prop` —
    /// [`Self::continuous_at_with`] with `P y →` in front.
    pub continuous_on_at_with: NameId,
    /// `Metric.ContinuousOnAt M N P F x := ∃ k,
    /// Metric.ContinuousOnAtWith M N P F x k`.
    pub continuous_on_at: NameId,
    /// `Metric.ContinuousOn M N P F := ∀ x, P x →
    /// Metric.ContinuousOnAt M N P F x`.
    pub continuous_on: NameId,
    /// `Metric.continuous_of_uniformly_continuous : ∀ M N F,
    /// Metric.UniformlyContinuous M N F → Metric.Continuous M N F` — **the
    /// one-directional implication**. See the module documentation for why
    /// the converse is absent rather than unproved.
    pub continuous_of_uniformly_continuous: NameId,
    /// `Metric.continuousOn_of_uniformlyContinuousOn : ∀ M N P F,
    /// Metric.UniformlyContinuousOn M N P F → Metric.ContinuousOn M N P F`.
    pub continuous_on_of_uniformly_continuous_on: NameId,
    /// `Metric.Interval (a b : CReal) : CReal → Prop :=
    /// fun x => And (CReal.le a x) (CReal.le x b)` — the closed interval as a
    /// **predicate on ℝ**, which is what a subspace is in this kernel.
    pub interval: NameId,
    /// `Metric.creal_uniformly_continuous_on : ∀ F a b,
    /// CReal.UniformlyContinuousOn F a b →
    /// Metric.UniformlyContinuousOn Metric.creal Metric.creal
    ///   (Metric.Interval a b) F` — **the W2-2 bridge**: ℝ's own uniform
    /// continuity is an instance of the metric notion. The witness is the
    /// `UniformlyContinuousOn.modulus` field verbatim and the proof is the
    /// `spec` field applied to four `And` projections; the two rate shapes
    /// coincide definitionally, which is the whole finding.
    pub creal_uniformly_continuous_on: NameId,
    /// `Metric.creal_continuous_on : ∀ F a b,
    /// CReal.UniformlyContinuousOn F a b →
    /// Metric.ContinuousOn Metric.creal Metric.creal (Metric.Interval a b) F`
    /// — the two bridges composed, i.e. the sentence W2-2 asks for:
    /// *`CReal.UniformlyContinuousOn` implies continuity as a metric notion*.
    pub creal_continuous_on: NameId,
}

impl ContinuityNames {
    /// Every name this module declares, paired with its rendered label.
    ///
    /// The list is what `metric_tests` iterates for presence and for
    /// axiom-freedom, and — because
    /// `metric_tests::every_metric_namespace_declaration_is_accounted_for`
    /// derives its subject from `Kernel::environment` rather than from a
    /// literal — a name added to the module and forgotten here fails a test
    /// rather than escaping one.
    #[must_use]
    pub fn all(&self) -> Vec<(&'static str, NameId)> {
        vec![
            (
                "Metric.UniformlyContinuousWith",
                self.uniformly_continuous_with,
            ),
            ("Metric.UniformlyContinuous", self.uniformly_continuous),
            (
                "Metric.UniformlyContinuousOnWith",
                self.uniformly_continuous_on_with,
            ),
            ("Metric.UniformlyContinuousOn", self.uniformly_continuous_on),
            ("Metric.ContinuousAtWith", self.continuous_at_with),
            ("Metric.ContinuousAt", self.continuous_at),
            ("Metric.Continuous", self.continuous),
            ("Metric.ContinuousOnAtWith", self.continuous_on_at_with),
            ("Metric.ContinuousOnAt", self.continuous_on_at),
            ("Metric.ContinuousOn", self.continuous_on),
            (
                "Metric.continuous_of_uniformly_continuous",
                self.continuous_of_uniformly_continuous,
            ),
            (
                "Metric.continuousOn_of_uniformlyContinuousOn",
                self.continuous_on_of_uniformly_continuous_on,
            ),
            ("Metric.Interval", self.interval),
            (
                "Metric.creal_uniformly_continuous_on",
                self.creal_uniformly_continuous_on,
            ),
            ("Metric.creal_continuous_on", self.creal_continuous_on),
        ]
    }
}

pub(super) fn intern(kernel: &mut Kernel, metric: NameId) -> ContinuityNames {
    ContinuityNames {
        uniformly_continuous_with: kernel.name_str(metric, "UniformlyContinuousWith"),
        uniformly_continuous: kernel.name_str(metric, "UniformlyContinuous"),
        uniformly_continuous_on_with: kernel.name_str(metric, "UniformlyContinuousOnWith"),
        uniformly_continuous_on: kernel.name_str(metric, "UniformlyContinuousOn"),
        continuous_at_with: kernel.name_str(metric, "ContinuousAtWith"),
        continuous_at: kernel.name_str(metric, "ContinuousAt"),
        continuous: kernel.name_str(metric, "Continuous"),
        continuous_on_at_with: kernel.name_str(metric, "ContinuousOnAtWith"),
        continuous_on_at: kernel.name_str(metric, "ContinuousOnAt"),
        continuous_on: kernel.name_str(metric, "ContinuousOn"),
        continuous_of_uniformly_continuous: kernel
            .name_str(metric, "continuous_of_uniformly_continuous"),
        continuous_on_of_uniformly_continuous_on: kernel
            .name_str(metric, "continuousOn_of_uniformlyContinuousOn"),
        interval: kernel.name_str(metric, "Interval"),
        creal_uniformly_continuous_on: kernel.name_str(metric, "creal_uniformly_continuous_on"),
        creal_continuous_on: kernel.name_str(metric, "creal_continuous_on"),
    }
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
    declare_uniformly_continuous_with(d, c, p)?;
    declare_uniformly_continuous(d, c, p)?;
    declare_uniformly_continuous_on_with(d, c, p)?;
    declare_uniformly_continuous_on(d, c, p)?;
    declare_continuous_at_with(d, c, p)?;
    declare_continuous_at(d, c, p)?;
    declare_continuous(d, c, p)?;
    declare_continuous_on_at_with(d, c, p)?;
    declare_continuous_on_at(d, c, p)?;
    declare_continuous_on(d, c, p)?;
    declare_continuous_of_uniformly_continuous(d, c, p)?;
    declare_continuous_on_of_uniformly_continuous_on(d, c, p)?;
    declare_interval(d, c, p)?;
    declare_creal_uniformly_continuous_on(d, c, p)?;
    declare_creal_continuous_on(d, c, p)
}

// ---------------------------------------------------------------------------
// Shared shorthands. Each is a constant applied to arguments; none introduces
// an estimate.
// ---------------------------------------------------------------------------

/// `CReal.ofRat (Rat.natDivSucc 1 k)`, i.e. `1/(k+1)` — the one rate shape
/// this whole layer uses.
pub(super) fn unit_rate(d: &mut IntDev<'_>, c: CRealPrelude, k: ExprId) -> ExprId {
    let one = d.num(1);
    let q = d.const_app(c.rat.nat_div_succ, &[one, k]);
    d.const_app(c.of_rat, &[q])
}

/// `CReal.le a b`.
pub(super) fn rle(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.le, &[a, b])
}

/// `Exists elem_ty predicate`, at universe level 1.
pub(super) fn exists_ty(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    elem_ty: ExprId,
    predicate: ExprId,
) -> ExprId {
    let one = d.level_one();
    let name = c.rat.int.logic.exists_;
    let head = d.kernel().const_(name, vec![one]);
    d.apply(head, &[elem_ty, predicate])
}

/// `Exists.intro elem_ty predicate witness proof`.
pub(super) fn exists_intro(
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
pub(super) fn exists_elim(
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

/// `And.intro left right hl hr`.
pub(super) fn and_intro(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    left: ExprId,
    right: ExprId,
    hl: ExprId,
    hr: ExprId,
) -> ExprId {
    let name = c.rat.int.logic.and_intro;
    d.const_app(name, &[left, right, hl, hr])
}

/// The two `Metric` binders every declaration in this file opens, plus their
/// carriers. `M` is the source space and `N` the target.
pub(super) struct Pair {
    pub metric_ty: ExprId,
    pub m_fv: u64,
    pub m: ExprId,
    pub m_carrier: ExprId,
    pub n_fv: u64,
    pub n: ExprId,
    /// `M.carrier → N.carrier`.
    pub fn_ty: ExprId,
    /// `Nat → Nat`.
    pub mod_ty: ExprId,
}

pub(super) fn pair(d: &mut IntDev<'_>, p: MetricPrelude) -> Pair {
    let metric_ty = d.kernel().const_(p.record.ind, vec![]);
    let sel = d.kernel().const_(p.record.sel(super::CARRIER), vec![]);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let m_carrier = d.apply(sel, &[m]);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let n_carrier = d.apply(sel, &[n]);
    let fn_ty = d.arrow(m_carrier, n_carrier);
    let nat = d.nat_ty();
    let mod_ty = d.arrow(nat, nat);
    Pair {
        metric_ty,
        m_fv,
        m,
        m_carrier,
        n_fv,
        n,
        fn_ty,
        mod_ty,
    }
}

/// `M.dist a b` — the record's `dist` selector applied to a space and two
/// points.
pub(super) fn dist(
    d: &mut IntDev<'_>,
    p: MetricPrelude,
    m: ExprId,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    let sel = d.kernel().const_(p.record.sel(DIST), vec![]);
    d.apply(sel, &[m, a, b])
}

/// `P x`, the relativizing predicate applied to a point.
fn holds(d: &mut IntDev<'_>, pred: ExprId, x: ExprId) -> ExprId {
    d.apply(pred, &[x])
}

// ---------------------------------------------------------------------------
// Uniform continuity.
// ---------------------------------------------------------------------------

/// The body shared by [`declare_uniformly_continuous_with`] and its
/// relativized twin: `∀ n x y, [P x → P y →] d(x,y) ≤ 1/(mu n + 1) →
/// d(F x, F y) ≤ 1/(n+1)`.
fn uc_body(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    g: &Pair,
    f: ExprId,
    mu: ExprId,
    restrict: Option<ExprId>,
) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let dxy = dist(d, p, g.m, x, y);
    let mu_n = d.apply(mu, &[n]);
    let inner_rate = unit_rate(d, c, mu_n);
    let hyp = rle(d, c, dxy, inner_rate);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);
    let dfxy = dist(d, p, g.n, fx, fy);
    let outer_rate = unit_rate(d, c, n);
    let concl = rle(d, c, dfxy, outer_rate);

    let mut body = d.arrow(hyp, concl);
    if let Some(pred) = restrict {
        let py = holds(d, pred, y);
        body = d.arrow(py, body);
        let px = holds(d, pred, x);
        body = d.arrow(px, body);
    }
    let body = d.pi_fv(y_fv, g.m_carrier, body);
    let body = d.pi_fv(x_fv, g.m_carrier, body);
    d.pi_fv(n_fv, nat, body)
}

/// `Metric.UniformlyContinuousWith M N F mu : Prop`.
fn declare_uniformly_continuous_with(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let mu_fv = d.fresh_fvar();
    let mu = d.kernel().fvar(mu_fv);

    let body = uc_body(d, c, p, &g, f, mu, None);
    let value = {
        let t = d.lam_fv(mu_fv, g.mod_ty, body);
        let t = d.lam_fv(f_fv, g.fn_ty, t);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(g.mod_ty, prop);
        let t = d.pi_fv(f_fv, g.fn_ty, t);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuity.uniformly_continuous_with,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.UniformlyContinuous M N F := ∃ mu, UniformlyContinuousWith M N F mu`.
fn declare_uniformly_continuous(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let predicate = {
        let mu_fv = d.fresh_fvar();
        let mu = d.kernel().fvar(mu_fv);
        let body = d.const_app(p.continuity.uniformly_continuous_with, &[g.m, g.n, f, mu]);
        d.lam_fv(mu_fv, g.mod_ty, body)
    };
    let body = exists_ty(d, c, g.mod_ty, predicate);

    let value = {
        let t = d.lam_fv(f_fv, g.fn_ty, body);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(g.fn_ty, prop);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuity.uniformly_continuous,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.UniformlyContinuousOnWith M N P F mu : Prop`.
fn declare_uniformly_continuous_on_with(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let prop = d.kernel().sort_zero();
    let pred_ty = d.arrow(g.m_carrier, prop);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let mu_fv = d.fresh_fvar();
    let mu = d.kernel().fvar(mu_fv);

    let body = uc_body(d, c, p, &g, f, mu, Some(pred));
    let value = {
        let t = d.lam_fv(mu_fv, g.mod_ty, body);
        let t = d.lam_fv(f_fv, g.fn_ty, t);
        let t = d.lam_fv(pred_fv, pred_ty, t);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let t = d.arrow(g.mod_ty, prop);
        let t = d.pi_fv(f_fv, g.fn_ty, t);
        let t = d.pi_fv(pred_fv, pred_ty, t);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuity.uniformly_continuous_on_with,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.UniformlyContinuousOn M N P F := ∃ mu, …OnWith M N P F mu`.
fn declare_uniformly_continuous_on(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let prop = d.kernel().sort_zero();
    let pred_ty = d.arrow(g.m_carrier, prop);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let predicate = {
        let mu_fv = d.fresh_fvar();
        let mu = d.kernel().fvar(mu_fv);
        let body = d.const_app(
            p.continuity.uniformly_continuous_on_with,
            &[g.m, g.n, pred, f, mu],
        );
        d.lam_fv(mu_fv, g.mod_ty, body)
    };
    let body = exists_ty(d, c, g.mod_ty, predicate);

    let value = {
        let t = d.lam_fv(f_fv, g.fn_ty, body);
        let t = d.lam_fv(pred_fv, pred_ty, t);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let t = d.arrow(g.fn_ty, prop);
        let t = d.pi_fv(pred_fv, pred_ty, t);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuity.uniformly_continuous_on,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

// ---------------------------------------------------------------------------
// Pointwise continuity.
// ---------------------------------------------------------------------------

/// `∀ n y, [P y →] d(x,y) ≤ 1/(k n + 1) → d(F x, F y) ≤ 1/(n+1)`.
fn cont_body(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
    g: &Pair,
    f: ExprId,
    x: ExprId,
    k: ExprId,
    restrict: Option<ExprId>,
) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let dxy = dist(d, p, g.m, x, y);
    let k_n = d.apply(k, &[n]);
    let inner_rate = unit_rate(d, c, k_n);
    let hyp = rle(d, c, dxy, inner_rate);

    let fx = d.apply(f, &[x]);
    let fy = d.apply(f, &[y]);
    let dfxy = dist(d, p, g.n, fx, fy);
    let outer_rate = unit_rate(d, c, n);
    let concl = rle(d, c, dfxy, outer_rate);

    let mut body = d.arrow(hyp, concl);
    if let Some(pred) = restrict {
        let py = holds(d, pred, y);
        body = d.arrow(py, body);
    }
    let body = d.pi_fv(y_fv, g.m_carrier, body);
    d.pi_fv(n_fv, nat, body)
}

/// `Metric.ContinuousAtWith M N F x k : Prop`.
fn declare_continuous_at_with(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let body = cont_body(d, c, p, &g, f, x, k, None);
    let value = {
        let t = d.lam_fv(k_fv, g.mod_ty, body);
        let t = d.lam_fv(x_fv, g.m_carrier, t);
        let t = d.lam_fv(f_fv, g.fn_ty, t);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(g.mod_ty, prop);
        let t = d.pi_fv(x_fv, g.m_carrier, t);
        let t = d.pi_fv(f_fv, g.fn_ty, t);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuity.continuous_at_with,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.ContinuousAt M N F x := ∃ k, ContinuousAtWith M N F x k`.
fn declare_continuous_at(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let predicate = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.continuity.continuous_at_with, &[g.m, g.n, f, x, k]);
        d.lam_fv(k_fv, g.mod_ty, body)
    };
    let body = exists_ty(d, c, g.mod_ty, predicate);

    let value = {
        let t = d.lam_fv(x_fv, g.m_carrier, body);
        let t = d.lam_fv(f_fv, g.fn_ty, t);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.pi_fv(x_fv, g.m_carrier, prop);
        let t = d.pi_fv(f_fv, g.fn_ty, t);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuity.continuous_at,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.Continuous M N F := ∀ x, Metric.ContinuousAt M N F x`.
fn declare_continuous(
    d: &mut IntDev<'_>,
    _c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let body = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let inner = d.const_app(p.continuity.continuous_at, &[g.m, g.n, f, x]);
        d.pi_fv(x_fv, g.m_carrier, inner)
    };
    let value = {
        let t = d.lam_fv(f_fv, g.fn_ty, body);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(g.fn_ty, prop);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuity.continuous,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.ContinuousOnAtWith M N P F x k : Prop`.
fn declare_continuous_on_at_with(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let prop = d.kernel().sort_zero();
    let pred_ty = d.arrow(g.m_carrier, prop);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let body = cont_body(d, c, p, &g, f, x, k, Some(pred));
    let value = {
        let t = d.lam_fv(k_fv, g.mod_ty, body);
        let t = d.lam_fv(x_fv, g.m_carrier, t);
        let t = d.lam_fv(f_fv, g.fn_ty, t);
        let t = d.lam_fv(pred_fv, pred_ty, t);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let t = d.arrow(g.mod_ty, prop);
        let t = d.pi_fv(x_fv, g.m_carrier, t);
        let t = d.pi_fv(f_fv, g.fn_ty, t);
        let t = d.pi_fv(pred_fv, pred_ty, t);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuity.continuous_on_at_with,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.ContinuousOnAt M N P F x := ∃ k, ContinuousOnAtWith M N P F x k`.
fn declare_continuous_on_at(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let prop = d.kernel().sort_zero();
    let pred_ty = d.arrow(g.m_carrier, prop);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let predicate = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(
            p.continuity.continuous_on_at_with,
            &[g.m, g.n, pred, f, x, k],
        );
        d.lam_fv(k_fv, g.mod_ty, body)
    };
    let body = exists_ty(d, c, g.mod_ty, predicate);

    let value = {
        let t = d.lam_fv(x_fv, g.m_carrier, body);
        let t = d.lam_fv(f_fv, g.fn_ty, t);
        let t = d.lam_fv(pred_fv, pred_ty, t);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let t = d.pi_fv(x_fv, g.m_carrier, prop);
        let t = d.pi_fv(f_fv, g.fn_ty, t);
        let t = d.pi_fv(pred_fv, pred_ty, t);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuity.continuous_on_at,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.ContinuousOn M N P F := ∀ x, P x → ContinuousOnAt M N P F x`.
fn declare_continuous_on(
    d: &mut IntDev<'_>,
    _c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let prop = d.kernel().sort_zero();
    let pred_ty = d.arrow(g.m_carrier, prop);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let body = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let inner = d.const_app(p.continuity.continuous_on_at, &[g.m, g.n, pred, f, x]);
        let px = holds(d, pred, x);
        let out = d.arrow(px, inner);
        d.pi_fv(x_fv, g.m_carrier, out)
    };
    let value = {
        let t = d.lam_fv(f_fv, g.fn_ty, body);
        let t = d.lam_fv(pred_fv, pred_ty, t);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let t = d.arrow(g.fn_ty, prop);
        let t = d.pi_fv(pred_fv, pred_ty, t);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuity.continuous_on,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

// ---------------------------------------------------------------------------
// Uniform ⇒ pointwise. ONE direction; see the module documentation.
// ---------------------------------------------------------------------------

/// `Metric.continuous_of_uniformly_continuous : ∀ M N F,
/// UniformlyContinuous M N F → Continuous M N F`.
///
/// The proof is the definition of "uniform": the single modulus the `∃`
/// carries is handed back **unchanged** at every point `x`, which is exactly
/// what pointwise continuity asks for and exactly what its converse cannot
/// undo.
fn declare_continuous_of_uniformly_continuous(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.const_app(p.continuity.uniformly_continuous, &[g.m, g.n, f]);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let uc_pred = {
        let mu_fv = d.fresh_fvar();
        let mu = d.kernel().fvar(mu_fv);
        let body = d.const_app(p.continuity.uniformly_continuous_with, &[g.m, g.n, f, mu]);
        d.lam_fv(mu_fv, g.mod_ty, body)
    };
    let target = d.const_app(p.continuity.continuous_at, &[g.m, g.n, f, x]);

    let minor = {
        let mu_fv = d.fresh_fvar();
        let mu = d.kernel().fvar(mu_fv);
        let hyp_ty = d.const_app(p.continuity.uniformly_continuous_with, &[g.m, g.n, f, mu]);
        let hmu_fv = d.fresh_fvar();
        let hmu = d.kernel().fvar(hmu_fv);

        let at_pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = d.const_app(p.continuity.continuous_at_with, &[g.m, g.n, f, x, k]);
            d.lam_fv(k_fv, g.mod_ty, body)
        };
        // `fun n y hd => hmu n x y hd` — the uniform witness read at the
        // fixed first point.
        let proof = {
            let nat = d.nat_ty();
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let dxy = dist(d, p, g.m, x, y);
            let mu_n = d.apply(mu, &[n]);
            let inner_rate = unit_rate(d, c, mu_n);
            let hd_ty = rle(d, c, dxy, inner_rate);
            let hd_fv = d.fresh_fvar();
            let hd = d.kernel().fvar(hd_fv);
            let body = d.apply(hmu, &[n, x, y, hd]);
            let t = d.lam_fv(hd_fv, hd_ty, body);
            let t = d.lam_fv(y_fv, g.m_carrier, t);
            d.lam_fv(n_fv, nat, t)
        };
        let intro = exists_intro(d, c, g.mod_ty, at_pred, mu, proof);
        let t = d.lam_fv(hmu_fv, hyp_ty, intro);
        d.lam_fv(mu_fv, g.mod_ty, t)
    };

    let elim = exists_elim(d, c, g.mod_ty, uc_pred, target, h, minor);

    let value = {
        let t = d.lam_fv(x_fv, g.m_carrier, elim);
        let t = d.lam_fv(h_fv, h_ty, t);
        let t = d.lam_fv(f_fv, g.fn_ty, t);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let concl = d.const_app(p.continuity.continuous, &[g.m, g.n, f]);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(f_fv, g.fn_ty, t);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.continuity.continuous_of_uniformly_continuous,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Metric.continuousOn_of_uniformlyContinuousOn : ∀ M N P F,
/// UniformlyContinuousOn M N P F → ContinuousOn M N P F` — the relativized
/// twin, with `P x` carried through as an extra hypothesis on the point.
fn declare_continuous_on_of_uniformly_continuous_on(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let g = pair(d, p);
    let prop = d.kernel().sort_zero();
    let pred_ty = d.arrow(g.m_carrier, prop);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.const_app(p.continuity.uniformly_continuous_on, &[g.m, g.n, pred, f]);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let px_ty = holds(d, pred, x);
    let hpx_fv = d.fresh_fvar();
    let hpx = d.kernel().fvar(hpx_fv);

    let uc_pred = {
        let mu_fv = d.fresh_fvar();
        let mu = d.kernel().fvar(mu_fv);
        let body = d.const_app(
            p.continuity.uniformly_continuous_on_with,
            &[g.m, g.n, pred, f, mu],
        );
        d.lam_fv(mu_fv, g.mod_ty, body)
    };
    let target = d.const_app(p.continuity.continuous_on_at, &[g.m, g.n, pred, f, x]);

    let minor = {
        let mu_fv = d.fresh_fvar();
        let mu = d.kernel().fvar(mu_fv);
        let hyp_ty = d.const_app(
            p.continuity.uniformly_continuous_on_with,
            &[g.m, g.n, pred, f, mu],
        );
        let hmu_fv = d.fresh_fvar();
        let hmu = d.kernel().fvar(hmu_fv);

        let at_pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = d.const_app(
                p.continuity.continuous_on_at_with,
                &[g.m, g.n, pred, f, x, k],
            );
            d.lam_fv(k_fv, g.mod_ty, body)
        };
        let proof = {
            let nat = d.nat_ty();
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let py_ty = holds(d, pred, y);
            let hpy_fv = d.fresh_fvar();
            let hpy = d.kernel().fvar(hpy_fv);
            let dxy = dist(d, p, g.m, x, y);
            let mu_n = d.apply(mu, &[n]);
            let inner_rate = unit_rate(d, c, mu_n);
            let hd_ty = rle(d, c, dxy, inner_rate);
            let hd_fv = d.fresh_fvar();
            let hd = d.kernel().fvar(hd_fv);
            let body = d.apply(hmu, &[n, x, y, hpx, hpy, hd]);
            let t = d.lam_fv(hd_fv, hd_ty, body);
            let t = d.lam_fv(hpy_fv, py_ty, t);
            let t = d.lam_fv(y_fv, g.m_carrier, t);
            d.lam_fv(n_fv, nat, t)
        };
        let intro = exists_intro(d, c, g.mod_ty, at_pred, mu, proof);
        let t = d.lam_fv(hmu_fv, hyp_ty, intro);
        d.lam_fv(mu_fv, g.mod_ty, t)
    };

    let elim = exists_elim(d, c, g.mod_ty, uc_pred, target, h, minor);

    let value = {
        let t = d.lam_fv(hpx_fv, px_ty, elim);
        let t = d.lam_fv(x_fv, g.m_carrier, t);
        let t = d.lam_fv(h_fv, h_ty, t);
        let t = d.lam_fv(f_fv, g.fn_ty, t);
        let t = d.lam_fv(pred_fv, pred_ty, t);
        let t = d.lam_fv(g.n_fv, g.metric_ty, t);
        d.lam_fv(g.m_fv, g.metric_ty, t)
    };
    let ty = {
        let concl = d.const_app(p.continuity.continuous_on, &[g.m, g.n, pred, f]);
        let t = d.arrow(h_ty, concl);
        let t = d.pi_fv(f_fv, g.fn_ty, t);
        let t = d.pi_fv(pred_fv, pred_ty, t);
        let t = d.pi_fv(g.n_fv, g.metric_ty, t);
        d.pi_fv(g.m_fv, g.metric_ty, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.continuity.continuous_on_of_uniformly_continuous_on,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// The bridge from ℝ's own vocabulary.
// ---------------------------------------------------------------------------

/// `Metric.Interval (a b : CReal) : CReal → Prop :=
/// fun x => And (CReal.le a x) (CReal.le x b)`.
fn declare_interval(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = d.kernel().const_(c.creal, vec![]);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let lo = rle(d, c, a, x);
    let hi = rle(d, c, x, b);
    let body = d.and(lo, hi);

    let value = {
        let t = d.lam_fv(x_fv, carrier, body);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(carrier, prop);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.continuity.interval,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// `Metric.creal_uniformly_continuous_on : ∀ F a b,
/// CReal.UniformlyContinuousOn F a b →
/// Metric.UniformlyContinuousOn Metric.creal Metric.creal (Interval a b) F`.
///
/// **The W2-2 measurement.** The witness is
/// `CReal.UniformlyContinuousOn.modulus F a b u` verbatim — no reindexing,
/// no rate arithmetic — and the proof is `CReal.UniformlyContinuousOn.spec`
/// applied to the four `And` projections of the two interval hypotheses. The
/// hypothesis and conclusion of the metric predicate are *definitionally*
/// `spec`'s own, because `Metric.dist Metric.creal x y` δι-reduces to
/// `CReal.abs (x + -y)` (that is what `Metric.creal_dist` pins) and because
/// both sides already spell every rate as `1/(k+1)`.
fn declare_creal_uniformly_continuous_on(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = d.kernel().const_(c.creal, vec![]);
    let nat = d.nat_ty();
    let mod_ty = d.arrow(nat, nat);
    let func_ty = d.arrow(carrier, carrier);
    let inst = d.kernel().const_(p.creal_metric, vec![]);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);

    let pred = d.const_app(p.continuity.interval, &[a, b]);
    let modulus = d.const_app(c.uc_modulus, &[f, a, b, u]);
    let spec = d.const_app(c.uc_spec, &[f, a, b, u]);

    let target_pred = {
        let mu_fv = d.fresh_fvar();
        let mu = d.kernel().fvar(mu_fv);
        let body = d.const_app(
            p.continuity.uniformly_continuous_on_with,
            &[inst, inst, pred, f, mu],
        );
        d.lam_fv(mu_fv, mod_ty, body)
    };

    let proof = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);

        let lo_x = rle(d, c, a, x);
        let hi_x = rle(d, c, x, b);
        let lo_y = rle(d, c, a, y);
        let hi_y = rle(d, c, y, b);
        let px_ty = d.and(lo_x, hi_x);
        let py_ty = d.and(lo_y, hi_y);
        let hpx_fv = d.fresh_fvar();
        let hpx = d.kernel().fvar(hpx_fv);
        let hpy_fv = d.fresh_fvar();
        let hpy = d.kernel().fvar(hpy_fv);

        let hax = d.and_left(lo_x, hi_x, hpx);
        let hxb = d.and_right(lo_x, hi_x, hpx);
        let hay = d.and_left(lo_y, hi_y, hpy);
        let hyb = d.and_right(lo_y, hi_y, hpy);

        let dxy = dist(d, p, inst, x, y);
        let mu_n = d.apply(modulus, &[n]);
        let inner_rate = unit_rate(d, c, mu_n);
        let hd_ty = rle(d, c, dxy, inner_rate);
        let hd_fv = d.fresh_fvar();
        let hd = d.kernel().fvar(hd_fv);

        let body = d.apply(spec, &[n, x, y, hax, hxb, hay, hyb, hd]);
        let t = d.lam_fv(hd_fv, hd_ty, body);
        let t = d.lam_fv(hpy_fv, py_ty, t);
        let t = d.lam_fv(hpx_fv, px_ty, t);
        let t = d.lam_fv(y_fv, carrier, t);
        let t = d.lam_fv(x_fv, carrier, t);
        d.lam_fv(n_fv, nat, t)
    };

    let intro = exists_intro(d, c, mod_ty, target_pred, modulus, proof);

    let value = {
        let t = d.lam_fv(u_fv, u_ty, intro);
        let t = d.lam_fv(b_fv, carrier, t);
        let t = d.lam_fv(a_fv, carrier, t);
        d.lam_fv(f_fv, func_ty, t)
    };
    let ty = {
        let concl = d.const_app(p.continuity.uniformly_continuous_on, &[inst, inst, pred, f]);
        let t = d.arrow(u_ty, concl);
        let t = d.pi_fv(b_fv, carrier, t);
        let t = d.pi_fv(a_fv, carrier, t);
        d.pi_fv(f_fv, func_ty, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.continuity.creal_uniformly_continuous_on,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Metric.creal_continuous_on : ∀ F a b,
/// CReal.UniformlyContinuousOn F a b →
/// Metric.ContinuousOn Metric.creal Metric.creal (Interval a b) F`.
///
/// The sentence W2-2 asks for, as one composition of the two theorems above.
fn declare_creal_continuous_on(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = d.kernel().const_(c.creal, vec![]);
    let func_ty = d.arrow(carrier, carrier);
    let inst = d.kernel().const_(p.creal_metric, vec![]);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);

    let pred = d.const_app(p.continuity.interval, &[a, b]);
    let bridged = d.lemma(p.continuity.creal_uniformly_continuous_on, &[f, a, b, u]);
    let body = d.lemma(
        p.continuity.continuous_on_of_uniformly_continuous_on,
        &[inst, inst, pred, f, bridged],
    );

    let value = {
        let t = d.lam_fv(u_fv, u_ty, body);
        let t = d.lam_fv(b_fv, carrier, t);
        let t = d.lam_fv(a_fv, carrier, t);
        d.lam_fv(f_fv, func_ty, t)
    };
    let ty = {
        let concl = d.const_app(p.continuity.continuous_on, &[inst, inst, pred, f]);
        let t = d.arrow(u_ty, concl);
        let t = d.pi_fv(b_fv, carrier, t);
        let t = d.pi_fv(a_fv, carrier, t);
        d.pi_fv(f_fv, func_ty, t)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.continuity.creal_continuous_on,
        uparams: vec![],
        ty,
        value,
    })
}
