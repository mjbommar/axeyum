//! `Metric.creal_totallyBoundedOn_interval` and what it unlocks — **the
//! closed interval of ℝ is Bishop-compact, and `CReal.evt_approx_max` is an
//! instance of `Metric.evt_approx_max`.**
//!
//! `metric/compactness.rs` states Bishop compactness and proves the Extreme
//! Value Theorem over any totally bounded subset of any metric space, and
//! `Metric.creal_completeOn_interval` supplies one of the two halves for
//! `[a,b] ⊂ ℝ`. This file supplies the other half — total boundedness — and
//! then spends it twice: once to conclude `Metric.CompactOn Metric.creal
//! (Metric.Interval a b)`, and once to re-derive `CReal.evt_approx_max`'s
//! exact statement through the general theorem.
//!
//! ## The net, and the two lemmas it costs
//!
//! At accuracy `n` the net is
//!
//! ```text
//! g n i := CReal.min b (a + (i / (n+1)))      for i ≤ B·(n+1)
//! ```
//!
//! where `B` is any natural with `b − a ≤ B` (`CReal.archimedean`, whose
//! `Exists` is eliminable here because the whole conclusion is a `Prop`).
//!
//! **The `min` is not decoration.** `Metric.NetIn` requires every net point to
//! satisfy the predicate, and `a + i/(n+1)` runs past `b` for large `i`; the
//! clamp is what puts it back. Only a *lower* clamp would be redundant —
//! `a + i/(n+1) ≥ a` already — so one `min` and no `max` is exactly the
//! obligation, and [`IntervalNames::creal_abs_sub_min_le`] is the price:
//! clamping a point of `[a,b]`'s neighbour does not move it further away.
//!
//! The covering itself, [`IntervalNames::creal_grid_cover`], is an induction
//! on the index bound with **one `CReal.lt_cotrans` split per step**, at the
//! pair `x < x + 1/(n+1)` against the grid point `a + K/(n+1)`:
//!
//! - if `x < a + K/(n+1)`, the induction hypothesis applies unchanged and its
//!   index is widened by `Nat.le_succ_of_le`;
//! - if `a + K/(n+1) < x + 1/(n+1)`, then `x` is within `1/(n+1)` of
//!   `a + K/(n+1)` **on both sides** — above because the step hypothesis is
//!   `x ≤ a + (K+1)/(n+1)`, below because that is what the branch says — so
//!   index `K` itself is the witness.
//!
//! Note which branch takes which index: the *second* one takes `K`, not
//! `K+1`. A split whose second branch only reproduced the step hypothesis
//! would make no progress, and cotransitivity's two alternatives overlap, so
//! the useful reading is the one where the overlap is exactly the radius.
//!
//! `CReal.abs_le_of_two_sided` does all the `abs` work: every bound below is
//! produced as the pair `x ≤ c + q` and `c ≤ x + q`, never by taking a
//! magnitude apart. That is why this file needs no `neg_add` law, which this
//! kernel does not have.
//!
//! ## The one arithmetic identity
//!
//! `Rat.natDivSucc` is deliberately **not** antitone in its index here
//! (ADR-0512), so `B ≤ B·(n+1)/(n+1)` is not a rearrangement — it is
//! [`IntervalNames::creal_nat_rate_scale`], proved as an `Eq Rat` by the
//! three-step route `rat_prelude/field.rs` already uses for the reciprocal:
//! `Rat.natDivSucc_mul` factors, `Rat.natDivSucc_scale` at `m = 0` reads
//! `(n+1)/(n+1)` as `1/1` (its index `(n+1)·0 + n` needing one `Nat.zero_add`
//! to flatten), and `Rat.natDivSucc_mul` again with `Nat.mul_one` closes it.
//!
//! ## What this makes an instance
//!
//! [`IntervalNames::creal_evt_approx_max_via_metric`] carries **the same
//! type** as `Metric.creal_evt_approx_max` — a test asserts the two `ty`
//! fields are the identical `ExprId` — and its proof is one application of
//! `Metric.evt_approx_max` to this file's total-boundedness theorem and
//! `metric/continuity.rs`'s uniform-continuity bridge. Two proofs of one
//! statement, one going through `CReal.supOn` and one through a net in an
//! arbitrary metric space, is the strongest form the claim "the interval EVT
//! is an instance of the general EVT" can take in this kernel.

#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::MetricPrelude;
use super::continuity::{and_intro, exists_elim, exists_intro, exists_ty, rle, unit_rate};
use crate::CRealPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{nat_eq_to_rat, nat_rewrite_prop, rat_eq_rewrite};

/// The kernel names `metric/interval.rs` declares.
///
/// Every field is prefixed `creal_` because every declaration here is about
/// the ONE carrier this file instantiates. That is the point of the module —
/// `metric/compactness.rs` holds the statements true of every metric space,
/// and this file holds the ℝ instance — so the shared prefix is the intended
/// reading, not an accident of naming.
#[allow(clippy::struct_field_names)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntervalNames {
    /// `Metric.CReal.addSubCancel : ∀ v e,
    /// CReal.Equiv (CReal.add (CReal.add v e) (CReal.neg e)) v`.
    pub creal_add_sub_cancel: NameId,
    /// `Metric.CReal.subLeOfLeAdd : ∀ u v e,
    /// CReal.le u (CReal.add v e) → CReal.le (CReal.add u (CReal.neg v)) e` —
    /// the converse of `Metric.CReal.leAddOfSubLe`.
    pub creal_sub_le_of_le_add: NameId,
    /// `Metric.CReal.negNonpos : ∀ t,
    /// CReal.le CReal.zero t → CReal.le (CReal.neg t) CReal.zero`.
    pub creal_neg_nonpos: NameId,
    /// `Metric.CReal.zeroLeOfRat : ∀ q, Rat.le Rat.zero q →
    /// CReal.le CReal.zero (CReal.ofRat q)`.
    pub creal_zero_le_of_rat: NameId,
    /// `Metric.CReal.absSubMinLe : ∀ b x s q, CReal.le x b →
    /// CReal.le (CReal.abs (x − s)) (CReal.ofRat q) →
    /// CReal.le (CReal.abs (x − CReal.min b s)) (CReal.ofRat q)` — **clamping
    /// a neighbour of a point below `b` does not move it away.** This is what
    /// makes `Metric.NetIn` satisfiable without giving up the covering.
    pub creal_abs_sub_min_le: NameId,
    /// `Metric.CReal.gridCover : ∀ a n K x, CReal.le a x →
    /// CReal.le x (a + (K/(n+1))) →
    /// ∃ i, Nat.le i K ∧ CReal.le (CReal.abs (x − (a + (i/(n+1)))))
    ///        (CReal.ofRat (Rat.natDivSucc 1 n))` — the rational grid covers
    /// the interval it spans, by induction on `K` with one cotransitivity
    /// split per step.
    pub creal_grid_cover: NameId,
    /// `Metric.CReal.natRateScale : ∀ B n,
    /// Eq Rat (Rat.natDivSucc (Nat.mul B (Nat.succ n)) n)
    ///        (Rat.natDivSucc B 0)` — `B·(n+1)/(n+1) = B/1`, which
    /// `Rat.natDivSucc`'s deliberate non-antitonicity makes a theorem rather
    /// than a rearrangement.
    pub creal_nat_rate_scale: NameId,
    /// `Metric.creal_totallyBoundedOn_interval : ∀ a b, CReal.le a b →
    /// Metric.TotallyBoundedOn Metric.creal (Metric.Interval a b)`.
    pub creal_totally_bounded_on_interval: NameId,
    /// `Metric.creal_compactOn_interval : ∀ a b, CReal.le a b →
    /// Metric.CompactOn Metric.creal (Metric.Interval a b)` — **a closed
    /// interval of ℝ is Bishop-compact**, the two halves being this file's
    /// total boundedness and `Metric.creal_completeOn_interval`.
    pub creal_compact_on_interval: NameId,
    /// `Metric.creal_evt_approx_max_via_metric` — **the same statement as
    /// `Metric.creal_evt_approx_max`, proved through the general metric
    /// EVT.** One application of `Metric.evt_approx_max` to
    /// [`Self::creal_totally_bounded_on_interval`] and
    /// `Metric.creal_uniformly_continuous_on`.
    pub creal_evt_approx_max_via_metric: NameId,
}

impl IntervalNames {
    /// Every name this module declares, paired with its rendered label.
    #[must_use]
    pub fn all(&self) -> Vec<(&'static str, NameId)> {
        vec![
            ("Metric.CReal.addSubCancel", self.creal_add_sub_cancel),
            ("Metric.CReal.subLeOfLeAdd", self.creal_sub_le_of_le_add),
            ("Metric.CReal.negNonpos", self.creal_neg_nonpos),
            ("Metric.CReal.zeroLeOfRat", self.creal_zero_le_of_rat),
            ("Metric.CReal.absSubMinLe", self.creal_abs_sub_min_le),
            ("Metric.CReal.gridCover", self.creal_grid_cover),
            ("Metric.CReal.natRateScale", self.creal_nat_rate_scale),
            (
                "Metric.creal_totallyBoundedOn_interval",
                self.creal_totally_bounded_on_interval,
            ),
            (
                "Metric.creal_compactOn_interval",
                self.creal_compact_on_interval,
            ),
            (
                "Metric.creal_evt_approx_max_via_metric",
                self.creal_evt_approx_max_via_metric,
            ),
        ]
    }
}

pub(super) fn intern(kernel: &mut Kernel, metric: NameId) -> IntervalNames {
    let creal_ns = kernel.name_str(metric, "CReal");
    IntervalNames {
        creal_add_sub_cancel: kernel.name_str(creal_ns, "addSubCancel"),
        creal_sub_le_of_le_add: kernel.name_str(creal_ns, "subLeOfLeAdd"),
        creal_neg_nonpos: kernel.name_str(creal_ns, "negNonpos"),
        creal_zero_le_of_rat: kernel.name_str(creal_ns, "zeroLeOfRat"),
        creal_abs_sub_min_le: kernel.name_str(creal_ns, "absSubMinLe"),
        creal_grid_cover: kernel.name_str(creal_ns, "gridCover"),
        creal_nat_rate_scale: kernel.name_str(creal_ns, "natRateScale"),
        creal_totally_bounded_on_interval: kernel
            .name_str(metric, "creal_totallyBoundedOn_interval"),
        creal_compact_on_interval: kernel.name_str(metric, "creal_compactOn_interval"),
        creal_evt_approx_max_via_metric: kernel.name_str(metric, "creal_evt_approx_max_via_metric"),
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
    type Step = (
        &'static str,
        fn(&mut IntDev<'_>, CRealPrelude, MetricPrelude) -> Result<(), KernelError>,
    );
    const STEPS: [Step; 10] = [
        ("CReal.addSubCancel", declare_add_sub_cancel),
        ("CReal.subLeOfLeAdd", declare_sub_le_of_le_add),
        ("CReal.negNonpos", declare_neg_nonpos),
        ("CReal.zeroLeOfRat", declare_zero_le_of_rat),
        ("CReal.absSubMinLe", declare_abs_sub_min_le),
        ("CReal.gridCover", declare_grid_cover),
        ("CReal.natRateScale", declare_nat_rate_scale),
        (
            "creal_totallyBoundedOn_interval",
            declare_totally_bounded_on_interval,
        ),
        ("creal_compactOn_interval", declare_compact_on_interval),
        (
            "creal_evt_approx_max_via_metric",
            declare_evt_approx_max_via_metric,
        ),
    ];

    let timing = std::env::var_os("AXEYUM_METRIC_TIMING").is_some();
    for (label, step) in STEPS {
        let started = std::time::Instant::now();
        let outcome = step(d, c, p);
        if timing {
            eprintln!(
                "metric/interval {label}: {:?} {}",
                started.elapsed(),
                if outcome.is_ok() { "ok" } else { "REFUSED" }
            );
        }
        outcome?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Shorthands.
// ---------------------------------------------------------------------------

fn cty(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    d.kernel().const_(c.creal, vec![])
}
fn radd(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.add, &[a, b])
}
fn rneg(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.const_app(c.neg, &[a])
}
fn rsub(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let nb = rneg(d, c, b);
    radd(d, c, a, nb)
}
fn rabs(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.const_app(c.abs, &[a])
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
fn rzero(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    d.kernel().const_(c.zero, vec![])
}
/// `CReal.ofRat (Rat.natDivSucc k j)`.
fn rate(d: &mut IntDev<'_>, c: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    let q = d.const_app(c.rat.nat_div_succ, &[k, j]);
    d.const_app(c.of_rat, &[q])
}
/// `Nat.le a b`.
fn nle(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let name = d.prelude().le;
    d.const_app(name, &[a, b])
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
// Four small rearrangements the reals prelude does not name.
// ---------------------------------------------------------------------------

/// `Metric.CReal.addSubCancel : ∀ v e, Equiv ((v + e) + -e) v`.
fn declare_add_sub_cancel(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = cty(d, c);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let ne = rneg(d, c, e);
    let ve = radd(d, c, v, e);
    let lhs = radd(d, c, ve, ne);
    let inner = radd(d, c, e, ne);
    let mid = radd(d, c, v, inner);
    let assoc = d.lemma(c.add_assoc, &[v, e, ne]);

    let zero = rzero(d, c);
    let cancel = d.lemma(c.add_neg, &[e]);
    let v_zero = radd(d, c, v, zero);
    let refl_v = rrefl(d, c, v);
    let congr = d.lemma(c.add_congr, &[v, v, inner, zero, refl_v, cancel]);
    let add_zero = d.lemma(c.add_zero, &[v]);
    let tail = rtrans(d, c, mid, v_zero, v, congr, add_zero);
    let proof = rtrans(d, c, lhs, mid, v, assoc, tail);

    let ty = {
        let stmt = req(d, c, lhs, v);
        let t = d.pi_fv(e_fv, carrier, stmt);
        d.pi_fv(v_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(e_fv, carrier, proof);
        d.lam_fv(v_fv, carrier, t)
    };
    theorem(d, p.interval.creal_add_sub_cancel, ty, value)
}

/// `Metric.CReal.subLeOfLeAdd : ∀ u v e, le u (v + e) → le (u + -v) e`.
fn declare_sub_le_of_le_add(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = cty(d, c);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let ve = radd(d, c, v, e);
    let hyp_ty = rle(d, c, u, ve);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let nv = rneg(d, c, v);
    let refl_nv = d.lemma(c.le_refl, &[nv]);
    let shifted = d.lemma(c.add_le_add, &[u, ve, nv, nv, h, refl_nv]);
    // `(v + e) + -v ~ (e + v) + -v ~ e`.
    let ve_nv = radd(d, c, ve, nv);
    let ev = radd(d, c, e, v);
    let ev_nv = radd(d, c, ev, nv);
    let comm = d.lemma(c.add_comm, &[v, e]);
    let refl_nv_eq = rrefl(d, c, nv);
    let step1 = d.lemma(c.add_congr, &[ve, ev, nv, nv, comm, refl_nv_eq]);
    let step2 = d.lemma(p.interval.creal_add_sub_cancel, &[e, v]);
    let collapse = rtrans(d, c, ve_nv, ev_nv, e, step1, step2);

    let u_nv = radd(d, c, u, nv);
    let refl_u_nv = rrefl(d, c, u_nv);
    let proof = d.lemma(
        c.le_congr,
        &[u_nv, u_nv, ve_nv, e, refl_u_nv, collapse, shifted],
    );

    let ty = {
        let concl = rle(d, c, u_nv, e);
        let t = d.arrow(hyp_ty, concl);
        let t = d.pi_fv(e_fv, carrier, t);
        let t = d.pi_fv(v_fv, carrier, t);
        d.pi_fv(u_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, hyp_ty, proof);
        let t = d.lam_fv(e_fv, carrier, t);
        let t = d.lam_fv(v_fv, carrier, t);
        d.lam_fv(u_fv, carrier, t)
    };
    theorem(d, p.interval.creal_sub_le_of_le_add, ty, value)
}

/// `Metric.CReal.negNonpos : ∀ t, le zero t → le (neg t) zero`.
fn declare_neg_nonpos(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = cty(d, c);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let zero = rzero(d, c);
    let hyp_ty = rle(d, c, zero, t);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let nt = rneg(d, c, t);
    let nzero = rneg(d, c, zero);
    let flipped = d.lemma(c.neg_le_neg, &[zero, t, h]);
    let neg_zero = d.lemma(p.creal_neg_zero, &[]);
    let refl_nt = rrefl(d, c, nt);
    let proof = d.lemma(
        c.le_congr,
        &[nt, nt, nzero, zero, refl_nt, neg_zero, flipped],
    );

    let ty = {
        let concl = rle(d, c, nt, zero);
        let t2 = d.arrow(hyp_ty, concl);
        d.pi_fv(t_fv, carrier, t2)
    };
    let value = {
        let t2 = d.lam_fv(h_fv, hyp_ty, proof);
        d.lam_fv(t_fv, carrier, t2)
    };
    theorem(d, p.interval.creal_neg_nonpos, ty, value)
}

/// `Metric.CReal.zeroLeOfRat : ∀ q, Rat.le Rat.zero q → le zero (ofRat q)`.
fn declare_zero_le_of_rat(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let rat = crate::rat_prelude::ops::rat_ty(d);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let rzero_q = d.kernel().const_(c.rat.zero, vec![]);
    let hyp_ty = d.const_app(c.rat.le, &[rzero_q, q]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = rzero(d, c);
    let embedded = d.const_app(c.of_rat, &[q]);
    let stepped = d.lemma(c.le_add_of_nonneg, &[zero, q, h]);
    let zero_e = radd(d, c, zero, embedded);
    let e_zero = radd(d, c, embedded, zero);
    let comm = d.lemma(c.add_comm, &[zero, embedded]);
    let az = d.lemma(c.add_zero, &[embedded]);
    let collapse = rtrans(d, c, zero_e, e_zero, embedded, comm, az);
    let refl_zero = rrefl(d, c, zero);
    let proof = d.lemma(
        c.le_congr,
        &[zero, zero, zero_e, embedded, refl_zero, collapse, stepped],
    );

    let ty = {
        let concl = rle(d, c, zero, embedded);
        let t = d.arrow(hyp_ty, concl);
        d.pi_fv(q_fv, rat, t)
    };
    let value = {
        let t = d.lam_fv(h_fv, hyp_ty, proof);
        d.lam_fv(q_fv, rat, t)
    };
    theorem(d, p.interval.creal_zero_le_of_rat, ty, value)
}

// ---------------------------------------------------------------------------
// The clamp.
// ---------------------------------------------------------------------------

/// `Metric.CReal.absSubMinLe : ∀ b x s q, le x b →
/// le (abs (x − s)) (ofRat q) → le (abs (x − min b s)) (ofRat q)`.
///
/// Both directions go through `CReal.abs_le_of_two_sided`, so no `abs` is ever
/// taken apart and this file needs no `neg_add` law. Upward:
/// `min b s ≤ s ≤ x + q`. Downward: `x − q ≤ b` (because `x ≤ b` and `−q ≤ 0`)
/// and `x − q ≤ s` (the hypothesis, moved across), so `x − q ≤ min b s` by
/// `CReal.le_min` — the one direction a meet does not hand you.
fn declare_abs_sub_min_le(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = cty(d, c);
    let rat = crate::rat_prelude::ops::rat_ty(d);

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let hxb_ty = rle(d, c, x, b);
    let hxb_fv = d.fresh_fvar();
    let hxb = d.kernel().fvar(hxb_fv);
    let diff = rsub(d, c, x, s);
    let mag = rabs(d, c, diff);
    let bound = d.const_app(c.of_rat, &[q]);
    let hmag_ty = rle(d, c, mag, bound);
    let hmag_fv = d.fresh_fvar();
    let hmag = d.kernel().fvar(hmag_fv);

    // `x − s ≤ |x − s| ≤ q`, hence `x ≤ s + q`.
    let self_le = d.lemma(c.le_abs_self, &[diff]);
    let hxs = d.lemma(c.le_trans, &[diff, mag, bound, self_le, hmag]);
    let hx_s_q = d.lemma(p.compactness.creal_le_add_of_sub_le, &[x, s, bound, hxs]);

    // `s − x ≤ |x − s| ≤ q`, hence `s ≤ x + q`.
    let ndiff = rneg(d, c, diff);
    let sx = rsub(d, c, s, x);
    let neg_le = d.lemma(c.neg_le_abs, &[diff]);
    let swap = d.lemma(c.neg_sub_swap, &[x, s]);
    let refl_mag = rrefl(d, c, mag);
    let hsx_mag = d.lemma(c.le_congr, &[ndiff, sx, mag, mag, swap, refl_mag, neg_le]);
    let hsx = d.lemma(c.le_trans, &[sx, mag, bound, hsx_mag, hmag]);
    let hs_x_q = d.lemma(p.compactness.creal_le_add_of_sub_le, &[s, x, bound, hsx]);

    let m = d.const_app(c.min, &[b, s]);

    // Upward: `min b s ≤ s ≤ x + q`.
    let min_s = d.lemma(c.min_le_right, &[b, s]);
    let x_q = radd(d, c, x, bound);
    let up = d.lemma(c.le_trans, &[m, s, x_q, min_s, hs_x_q]);

    // Downward: `x − q ≤ min b s`, then across to `x ≤ min b s + q`.
    let nbound = rneg(d, c, bound);
    let x_minus_q = radd(d, c, x, nbound);
    let zero = rzero(d, c);
    let rat_zero = d.kernel().const_(c.rat.zero, vec![]);
    let hq_nonneg_ty = d.const_app(c.rat.le, &[rat_zero, q]);
    let _ = hq_nonneg_ty;
    // `−q ≤ 0` needs `0 ≤ q`, which follows from `0 ≤ |x−s| ≤ q` — no extra
    // hypothesis is required.
    let abs_nonneg = d.lemma(c.abs_nonneg, &[diff]);
    let zero_le_bound = d.lemma(c.le_trans, &[zero, mag, bound, abs_nonneg, hmag]);
    let nbound_nonpos = d.lemma(p.interval.creal_neg_nonpos, &[bound, zero_le_bound]);
    let refl_x = d.lemma(c.le_refl, &[x]);
    let x_zero = radd(d, c, x, zero);
    let shifted = d.lemma(c.add_le_add, &[x, x, nbound, zero, refl_x, nbound_nonpos]);
    let az = d.lemma(c.add_zero, &[x]);
    let refl_xmq = rrefl(d, c, x_minus_q);
    let hxq_x = d.lemma(
        c.le_congr,
        &[x_minus_q, x_minus_q, x_zero, x, refl_xmq, az, shifted],
    );
    let hxq_b = d.lemma(c.le_trans, &[x_minus_q, x, b, hxq_x, hxb]);
    // `x ≤ s + q ~ q + s`, so `x − q ≤ s`.
    let q_s = radd(d, c, bound, s);
    let s_q = radd(d, c, s, bound);
    let comm_sq = d.lemma(c.add_comm, &[s, bound]);
    let refl_x_eq = rrefl(d, c, x);
    let hx_q_s = d.lemma(c.le_congr, &[x, x, s_q, q_s, refl_x_eq, comm_sq, hx_s_q]);
    let hxq_s = d.lemma(p.interval.creal_sub_le_of_le_add, &[x, bound, s, hx_q_s]);
    let hxq_m = d.lemma(c.le_min, &[b, s, x_minus_q, hxq_b, hxq_s]);
    let down_raw = d.lemma(p.compactness.creal_le_add_of_sub_le, &[x, bound, m, hxq_m]);
    // `x ≤ q + min b s ~ min b s + q`.
    let q_m = radd(d, c, bound, m);
    let m_q = radd(d, c, m, bound);
    let comm_qm = d.lemma(c.add_comm, &[bound, m]);
    let down = d.lemma(c.le_congr, &[x, x, q_m, m_q, refl_x_eq, comm_qm, down_raw]);

    let proof = d.lemma(c.abs_le_of_two_sided, &[x, m, q, down, up]);

    let ty = {
        let clamped = rsub(d, c, x, m);
        let clamped_mag = rabs(d, c, clamped);
        let concl = rle(d, c, clamped_mag, bound);
        let t = d.arrow(hmag_ty, concl);
        let t = d.arrow(hxb_ty, t);
        let t = d.pi_fv(q_fv, rat, t);
        let t = d.pi_fv(s_fv, carrier, t);
        let t = d.pi_fv(x_fv, carrier, t);
        d.pi_fv(b_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(hmag_fv, hmag_ty, proof);
        let t = d.lam_fv(hxb_fv, hxb_ty, t);
        let t = d.lam_fv(q_fv, rat, t);
        let t = d.lam_fv(s_fv, carrier, t);
        let t = d.lam_fv(x_fv, carrier, t);
        d.lam_fv(b_fv, carrier, t)
    };
    theorem(d, p.interval.creal_abs_sub_min_le, ty, value)
}

// ---------------------------------------------------------------------------
// The grid.
// ---------------------------------------------------------------------------

/// `Metric.CReal.gridCover`. See the module documentation for the split.
fn declare_grid_cover(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = cty(d, c);
    let nat = d.nat_ty();
    let natp = d.prelude();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one = d.num(1);
    let unit_q = d.const_app(c.rat.nat_div_succ, &[one, n]);
    let urate = d.const_app(c.of_rat, &[unit_q]);

    // `fun i => Nat.le i bound ∧ |x − (a + i/(n+1))| ≤ 1/(n+1)`.
    let claim_pred = |d: &mut IntDev<'_>, bound: ExprId, x: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let small = nle(d, i, bound);
        let point = {
            let r = rate(d, c, i, n);
            radd(d, c, a, r)
        };
        let diff = rsub(d, c, x, point);
        let mag = rabs(d, c, diff);
        let close = rle(d, c, mag, urate);
        let body = d.and(small, close);
        d.lam_fv(i_fv, nat, body)
    };
    let motive = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hax_ty = rle(d, c, a, x);
        let span = {
            let r = rate(d, c, bound, n);
            radd(d, c, a, r)
        };
        let hxb_ty = rle(d, c, x, span);
        let pred = claim_pred(d, bound, x);
        let concl = exists_ty(d, c, nat, pred);
        let out = d.arrow(hxb_ty, concl);
        let out = d.arrow(hax_ty, out);
        d.pi_fv(x_fv, carrier, out)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero = d.zero();
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hax_ty = rle(d, c, a, x);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let r0 = rate(d, c, zero, n);
        let span = radd(d, c, a, r0);
        let hxb_ty = rle(d, c, x, span);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);

        // side 1: `x ≤ span ≤ span + 1/(n+1)`.
        let padded = radd(d, c, span, urate);
        let widen = d.lemma(p.compactness.creal_le_add_rate, &[span, n]);
        let side1 = d.lemma(c.le_trans, &[x, span, padded, hxb, widen]);
        // side 2: `a + 0/(n+1) ≤ x + 1/(n+1)`.
        let zero_q = d.const_app(c.rat.nat_div_succ, &[zero, n]);
        let widen_num = d.lemma(c.rat.nat_div_succ_le_add_left, &[zero, one, n]);
        let rate_le = d.lemma(c.of_rat_le, &[zero_q, unit_q, widen_num]);
        let side2 = d.lemma(c.add_le_add, &[a, x, r0, urate, hax, rate_le]);

        let body = d.lemma(c.abs_le_of_two_sided, &[x, span, unit_q, side1, side2]);
        let pred = claim_pred(d, zero, x);
        let small = nle(d, zero, zero);
        let refl = d.lemma(natp.le_refl_thm, &[zero]);
        let diff = rsub(d, c, x, span);
        let mag = rabs(d, c, diff);
        let close_ty = rle(d, c, mag, urate);
        let pair = and_intro(d, c, small, close_ty, refl, body);
        let intro = exists_intro(d, c, nat, pred, zero, pair);
        let t = d.lam_fv(hxb_fv, hxb_ty, intro);
        let t = d.lam_fv(hax_fv, hax_ty, t);
        d.lam_fv(x_fv, carrier, t)
    };

    let step = |d: &mut IntDev<'_>, j0: ExprId, ih: ExprId| -> ExprId {
        let next = d.succ(j0);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let hax_ty = rle(d, c, a, x);
        let hax_fv = d.fresh_fvar();
        let hax = d.kernel().fvar(hax_fv);
        let r_next = rate(d, c, next, n);
        let span_next = radd(d, c, a, r_next);
        let hxb_ty = rle(d, c, x, span_next);
        let hxb_fv = d.fresh_fvar();
        let hxb = d.kernel().fvar(hxb_fv);

        let r_j0 = rate(d, c, j0, n);
        let span_j0 = radd(d, c, a, r_j0);
        let goal = {
            let pred = claim_pred(d, next, x);
            exists_ty(d, c, nat, pred)
        };

        let padded_x = radd(d, c, x, urate);
        let hlt = d.lemma(p.compactness.creal_lt_add_rate, &[x, n]);
        let cot = d.lemma(c.lt_cotrans, &[x, padded_x, hlt, span_j0]);
        let left_ty = d.const_app(c.lt, &[x, span_j0]);
        let right_ty = d.const_app(c.lt, &[span_j0, padded_x]);

        let on_left = |d: &mut IntDev<'_>, hl: ExprId| -> ExprId {
            let hxk = d.lemma(c.le_of_lt, &[x, span_j0, hl]);
            let ih_at = d.apply(ih, &[x, hax, hxk]);
            let ih_pred = claim_pred(d, j0, x);
            let minor = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let small_i = nle(d, i, j0);
                let point = {
                    let r = rate(d, c, i, n);
                    radd(d, c, a, r)
                };
                let diff = rsub(d, c, x, point);
                let mag = rabs(d, c, diff);
                let close_ty = rle(d, c, mag, urate);
                let hyp_ty = d.and(small_i, close_ty);
                let hyp_fv = d.fresh_fvar();
                let hyp = d.kernel().fvar(hyp_fv);
                let hile = d.and_left(small_i, close_ty, hyp);
                let hclose = d.and_right(small_i, close_ty, hyp);
                let widened = d.lemma(natp.le_succ_of_le, &[i, j0, hile]);
                let small_next = nle(d, i, next);
                let pair = and_intro(d, c, small_next, close_ty, widened, hclose);
                let pred = claim_pred(d, next, x);
                let intro = exists_intro(d, c, nat, pred, i, pair);
                let t = d.lam_fv(hyp_fv, hyp_ty, intro);
                d.lam_fv(i_fv, nat, t)
            };
            exists_elim(d, c, nat, ih_pred, goal, ih_at, minor)
        };

        let on_right = |d: &mut IntDev<'_>, hr: ExprId| -> ExprId {
            // `a + (K+1)/(n+1) ~ (a + K/(n+1)) + 1/(n+1)`.
            let j0_q = d.const_app(c.rat.nat_div_succ, &[j0, n]);
            let sum_q = {
                let rat_add = d.int().rat_add;
                d.const_app(rat_add, &[j0_q, unit_q])
            };
            let fused_index = NatOps::add(d, j0, one);
            let fused_q = d.const_app(c.rat.nat_div_succ, &[fused_index, n]);
            let fuse = d.lemma(c.rat.nat_div_succ_add, &[j0, one, n]);
            let base_eq = d.lemma(c.of_rat_add, &[j0_q, unit_q]);
            let rate_sum = radd(d, c, r_j0, urate);
            let hsplit = rat_eq_rewrite(d, sum_q, fused_q, fuse, base_eq, &|d, z| {
                let rhs = d.const_app(c.of_rat, &[z]);
                req(d, c, rate_sum, rhs)
            });
            // `hsplit : Equiv (r_j0 + urate) (a's rate at succ j0)`.
            let hsplit_back = rsymm(d, c, rate_sum, r_next, hsplit);
            let refl_a = rrefl(d, c, a);
            let inner = radd(d, c, a, rate_sum);
            let e1 = d.lemma(c.add_congr, &[a, a, r_next, rate_sum, refl_a, hsplit_back]);
            let stacked = radd(d, c, span_j0, urate);
            let assoc = d.lemma(c.add_assoc, &[a, r_j0, urate]);
            let assoc_back = rsymm(d, c, stacked, inner, assoc);
            let e3 = rtrans(d, c, span_next, inner, stacked, e1, assoc_back);
            let refl_x = rrefl(d, c, x);
            let side1 = d.lemma(c.le_congr, &[x, x, span_next, stacked, refl_x, e3, hxb]);
            let side2 = d.lemma(c.le_of_lt, &[span_j0, padded_x, hr]);

            let body = d.lemma(c.abs_le_of_two_sided, &[x, span_j0, unit_q, side1, side2]);
            let small = nle(d, j0, next);
            let widened = d.lemma(natp.le_succ, &[j0]);
            let diff = rsub(d, c, x, span_j0);
            let mag = rabs(d, c, diff);
            let close_ty = rle(d, c, mag, urate);
            let pair = and_intro(d, c, small, close_ty, widened, body);
            let pred = claim_pred(d, next, x);
            exists_intro(d, c, nat, pred, j0, pair)
        };

        let body = d.or_elim(left_ty, right_ty, goal, cot, &on_left, &on_right);
        let t = d.lam_fv(hxb_fv, hxb_ty, body);
        let t = d.lam_fv(hax_fv, hax_ty, t);
        d.lam_fv(x_fv, carrier, t)
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let proof = d.induct(&motive, &base, &step, k);

    let ty = {
        let stmt = motive(d, k);
        let t = d.pi_fv(k_fv, nat, stmt);
        let t = d.pi_fv(n_fv, nat, t);
        d.pi_fv(a_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(k_fv, nat, proof);
        let t = d.lam_fv(n_fv, nat, t);
        d.lam_fv(a_fv, carrier, t)
    };
    theorem(d, p.interval.creal_grid_cover, ty, value)
}

// ---------------------------------------------------------------------------
// `B·(n+1)/(n+1) = B/1`.
// ---------------------------------------------------------------------------

/// `Metric.CReal.natRateScale : ∀ B n,
/// Eq Rat (natDivSucc (Nat.mul B (Nat.succ n)) n) (natDivSucc B 0)`.
///
/// The three-step route `rat_prelude/field.rs` uses for the reciprocal, run
/// once forwards: `natDivSucc_mul` factors `B·(n+1)/(n+1)` into
/// `(B/1)·((n+1)/(n+1))`, `natDivSucc_scale` at `m = 0` reads the second
/// factor as `1/1` (its index `(n+1)·0 + n` flattening by `Nat.zero_add`),
/// and `natDivSucc_mul` again with `Nat.mul_one` collapses `(B/1)·(1/1)` back
/// to `B/1`.
fn declare_nat_rate_scale(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let natp = d.prelude();
    let rp = c.rat;

    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let zero_nat = d.zero();
    let one_nat = d.num(1);
    let successor = d.succ(n);
    let whole = d.const_app(rp.nat_div_succ, &[b, zero_nat]);
    let unit = d.const_app(rp.nat_div_succ, &[one_nat, zero_nat]);
    let deep = d.const_app(rp.nat_div_succ, &[successor, n]);

    // `(n+1)/(n+1) = 1/1`.
    let scale = {
        let inner = NatOps::mul(d, successor, zero_nat);
        let index = NatOps::add(d, inner, n);
        let law = d.lemma(rp.nat_div_succ_scale, &[n, zero_nat]);
        let flatten = d.lemma(natp.zero_add, &[n]);
        nat_rewrite_prop(d, index, n, flatten, law, &|d, t| {
            let left = d.const_app(rp.nat_div_succ, &[successor, t]);
            crate::rat_prelude::ops::req(d, left, unit)
        })
    };

    // `(B/1)·((n+1)/(n+1)) = B·(n+1)/(n+1)`; read right to left.
    let product_deep = crate::rat_prelude::ops::rmul(d, whole, deep);
    let scaled_index = NatOps::mul(d, b, successor);
    let target = d.const_app(rp.nat_div_succ, &[scaled_index, n]);
    let fuse_deep = d.lemma(rp.nat_div_succ_mul, &[b, successor, n]);

    // `(B/1)·(1/1) = (B·1)/1 = B/1`.
    let product_unit = crate::rat_prelude::ops::rmul(d, whole, unit);
    let b_one = NatOps::mul(d, b, one_nat);
    let fused_unit = d.const_app(rp.nat_div_succ, &[b_one, zero_nat]);
    let fuse_unit = d.lemma(rp.nat_div_succ_mul, &[b, one_nat, zero_nat]);
    let collapse_unit = {
        let identity = d.lemma(natp.mul_one, &[b]);
        nat_eq_to_rat(d, b_one, b, identity, &|d, t| {
            d.const_app(rp.nat_div_succ, &[t, zero_nat])
        })
    };

    // `target = (B/1)·((n+1)/(n+1))` — `fuse_deep` reversed.
    let back = crate::rat_prelude::ops::rsymm(d, product_deep, target, fuse_deep);
    // Rewrite the second factor from `(n+1)/(n+1)` to `1/1`.
    let to_unit = rat_eq_rewrite(d, deep, unit, scale, back, &|d, z| {
        let prod = crate::rat_prelude::ops::rmul(d, whole, z);
        crate::rat_prelude::ops::req(d, target, prod)
    });
    let (_, proof) = crate::rat_prelude::ops::rchain(
        d,
        target,
        &[
            (product_unit, to_unit),
            (fused_unit, fuse_unit),
            (whole, collapse_unit),
        ],
    );

    let ty = {
        let stmt = crate::rat_prelude::ops::req(d, target, whole);
        let t = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(b_fv, nat, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(b_fv, nat, t)
    };
    theorem(d, p.interval.creal_nat_rate_scale, ty, value)
}

// ---------------------------------------------------------------------------
// The interval is totally bounded, hence Bishop-compact.
// ---------------------------------------------------------------------------

/// `Metric.creal_totallyBoundedOn_interval`.
fn declare_totally_bounded_on_interval(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = cty(d, c);
    let nat = d.nat_ty();
    let natp = d.prelude();
    let count_ty = d.arrow(nat, nat);
    let seq_ty = d.arrow(nat, carrier);
    let net_ty = d.arrow(nat, seq_ty);
    let inst = d.kernel().const_(p.creal_metric, vec![]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let pred = d.const_app(p.continuity.interval, &[a, b]);

    let goal = d.const_app(p.compactness.totally_bounded_on, &[inst, pred]);

    // `archimedean (b − a) : ∃ B, le (b − a) (ofNat B)`.
    let span = rsub(d, c, b, a);
    let arch = d.lemma(c.archimedean, &[span]);
    let arch_pred = {
        let bb_fv = d.fresh_fvar();
        let bb = d.kernel().fvar(bb_fv);
        let embedded = d.const_app(c.of_nat, &[bb]);
        let body = rle(d, c, span, embedded);
        d.lam_fv(bb_fv, nat, body)
    };

    let minor = {
        let bb_fv = d.fresh_fvar();
        let bb = d.kernel().fvar(bb_fv);
        let embedded = d.const_app(c.of_nat, &[bb]);
        let hyp_ty = rle(d, c, span, embedded);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);

        // `cnt n := B * (n + 1)` and `g n i := min b (a + i/(n+1))`.
        let cnt = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let succ_n = d.succ(n);
            let body = NatOps::mul(d, bb, succ_n);
            d.lam_fv(n_fv, nat, body)
        };
        let g = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let r = rate(d, c, i, n);
            let point = radd(d, c, a, r);
            let body = d.const_app(c.min, &[b, point]);
            let inner = d.lam_fv(i_fv, nat, body);
            d.lam_fv(n_fv, nat, inner)
        };

        // NetIn: `a ≤ min b (a + i/(n+1)) ≤ b`.
        let net_in = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.apply(cnt, &[n]);
            let small_ty = nle(d, i, bound);
            let hsmall_fv = d.fresh_fvar();
            let r = rate(d, c, i, n);
            let point = radd(d, c, a, r);
            let m = d.const_app(c.min, &[b, point]);
            let q = d.const_app(c.rat.nat_div_succ, &[i, n]);
            let nonneg = d.lemma(c.rat.zero_le_nat_div_succ, &[i, n]);
            let a_le_point = d.lemma(c.le_add_of_nonneg, &[a, q, nonneg]);
            let lo = d.lemma(c.le_min, &[b, point, a, hab, a_le_point]);
            let hi = d.lemma(c.min_le_left, &[b, point]);
            let lo_ty = rle(d, c, a, m);
            let hi_ty = rle(d, c, m, b);
            let body = and_intro(d, c, lo_ty, hi_ty, lo, hi);
            let t = d.lam_fv(hsmall_fv, small_ty, body);
            let t = d.lam_fv(i_fv, nat, t);
            d.lam_fv(n_fv, nat, t)
        };
        let net_in_ty = d.const_app(p.compactness.net_in, &[inst, pred, g, cnt]);

        // NetCovers.
        let net_covers = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let lo_ty = rle(d, c, a, x);
            let hi_ty = rle(d, c, x, b);
            let hx_ty = d.and(lo_ty, hi_ty);
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let hax = d.and_left(lo_ty, hi_ty, hx);
            let hxb = d.and_right(lo_ty, hi_ty, hx);

            let one = d.num(1);
            let unit_q = d.const_app(c.rat.nat_div_succ, &[one, n]);
            let urate = d.const_app(c.of_rat, &[unit_q]);
            let succ_n = d.succ(n);
            let bound = NatOps::mul(d, bb, succ_n);

            // `b ≤ a + B` and `B/1 = bound/(n+1)`, so `x ≤ a + bound/(n+1)`.
            let b_le = d.lemma(p.compactness.creal_le_add_of_sub_le, &[b, a, embedded, hb]);
            let scale = d.lemma(p.interval.creal_nat_rate_scale, &[bb, n]);
            let zero_nat = d.zero();
            let whole_q = d.const_app(c.rat.nat_div_succ, &[bb, zero_nat]);
            let bound_q = d.const_app(c.rat.nat_div_succ, &[bound, n]);
            let scale_back = crate::rat_prelude::ops::rsymm(d, bound_q, whole_q, scale);
            let b_le_span = rat_eq_rewrite(d, whole_q, bound_q, scale_back, b_le, &|d, z| {
                let embedded_z = d.const_app(c.of_rat, &[z]);
                let span_z = radd(d, c, a, embedded_z);
                rle(d, c, b, span_z)
            });
            let bound_rate = d.const_app(c.of_rat, &[bound_q]);
            let span_bound = radd(d, c, a, bound_rate);
            let hx_span = d.lemma(c.le_trans, &[x, b, span_bound, hxb, b_le_span]);

            let cover = d.lemma(p.interval.creal_grid_cover, &[a, n, bound, x, hax, hx_span]);
            let cover_pred = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let small = nle(d, i, bound);
                let r = rate(d, c, i, n);
                let point = radd(d, c, a, r);
                let diff = rsub(d, c, x, point);
                let mag = rabs(d, c, diff);
                let close = rle(d, c, mag, urate);
                let body = d.and(small, close);
                d.lam_fv(i_fv, nat, body)
            };

            let target_pred = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let small = nle(d, i, bound);
                let point = d.apply(g, &[n, i]);
                let diff = rsub(d, c, x, point);
                let mag = rabs(d, c, diff);
                let close = rle(d, c, mag, urate);
                let body = d.and(small, close);
                d.lam_fv(i_fv, nat, body)
            };
            let target = exists_ty(d, c, nat, target_pred);

            let cover_minor = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let small = nle(d, i, bound);
                let r = rate(d, c, i, n);
                let point = radd(d, c, a, r);
                let diff = rsub(d, c, x, point);
                let mag = rabs(d, c, diff);
                let close_ty = rle(d, c, mag, urate);
                let hyp_ty = d.and(small, close_ty);
                let hyp_fv = d.fresh_fvar();
                let hyp = d.kernel().fvar(hyp_fv);
                let hile = d.and_left(small, close_ty, hyp);
                let hclose = d.and_right(small, close_ty, hyp);

                let clamped = d.lemma(
                    p.interval.creal_abs_sub_min_le,
                    &[b, x, point, unit_q, hxb, hclose],
                );
                let m = d.const_app(c.min, &[b, point]);
                let cdiff = rsub(d, c, x, m);
                let cmag = rabs(d, c, cdiff);
                let cclose_ty = rle(d, c, cmag, urate);
                let pair = and_intro(d, c, small, cclose_ty, hile, clamped);
                let intro = exists_intro(d, c, nat, target_pred, i, pair);
                let t = d.lam_fv(hyp_fv, hyp_ty, intro);
                d.lam_fv(i_fv, nat, t)
            };
            let body = exists_elim(d, c, nat, cover_pred, target, cover, cover_minor);
            let t = d.lam_fv(hx_fv, hx_ty, body);
            let t = d.lam_fv(x_fv, carrier, t);
            d.lam_fv(n_fv, nat, t)
        };
        let net_covers_ty = d.const_app(p.compactness.net_covers, &[inst, pred, g, cnt]);

        let tbw = and_intro(d, c, net_in_ty, net_covers_ty, net_in, net_covers);
        let inner_pred = {
            let gg_fv = d.fresh_fvar();
            let gg = d.kernel().fvar(gg_fv);
            let body = d.const_app(
                p.compactness.totally_bounded_on_with,
                &[inst, pred, gg, cnt],
            );
            d.lam_fv(gg_fv, net_ty, body)
        };
        let inner = exists_intro(d, c, net_ty, inner_pred, g, tbw);
        let outer_pred = {
            let cc_fv = d.fresh_fvar();
            let cc = d.kernel().fvar(cc_fv);
            let ip = {
                let gg_fv = d.fresh_fvar();
                let gg = d.kernel().fvar(gg_fv);
                let body =
                    d.const_app(p.compactness.totally_bounded_on_with, &[inst, pred, gg, cc]);
                d.lam_fv(gg_fv, net_ty, body)
            };
            let body = exists_ty(d, c, net_ty, ip);
            d.lam_fv(cc_fv, count_ty, body)
        };
        let out = exists_intro(d, c, count_ty, outer_pred, cnt, inner);
        let t = d.lam_fv(hb_fv, hyp_ty, out);
        d.lam_fv(bb_fv, nat, t)
    };

    let proof = exists_elim(d, c, nat, arch_pred, goal, arch, minor);
    let _ = natp;

    let ty = {
        let t = d.arrow(hab_ty, goal);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(hab_fv, hab_ty, proof);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    theorem(d, p.interval.creal_totally_bounded_on_interval, ty, value)
}

/// `Metric.creal_compactOn_interval : ∀ a b, le a b →
/// Metric.CompactOn Metric.creal (Metric.Interval a b)`.
fn declare_compact_on_interval(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = cty(d, c);
    let inst = d.kernel().const_(p.creal_metric, vec![]);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let pred = d.const_app(p.continuity.interval, &[a, b]);

    let tb_ty = d.const_app(p.compactness.totally_bounded_on, &[inst, pred]);
    let cp_ty = d.const_app(p.compactness.complete_on, &[inst, pred]);
    let tb = d.lemma(p.interval.creal_totally_bounded_on_interval, &[a, b, hab]);
    let cp = d.lemma(p.compactness.creal_complete_on_interval, &[a, b]);
    let proof = and_intro(d, c, tb_ty, cp_ty, tb, cp);

    let ty = {
        let concl = d.const_app(p.compactness.compact_on, &[inst, pred]);
        let t = d.arrow(hab_ty, concl);
        let t = d.pi_fv(b_fv, carrier, t);
        d.pi_fv(a_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(hab_fv, hab_ty, proof);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    theorem(d, p.interval.creal_compact_on_interval, ty, value)
}

/// `Metric.creal_evt_approx_max_via_metric` — **the same type as
/// `Metric.creal_evt_approx_max`, proved through `Metric.evt_approx_max`.**
///
/// The `ty` is rebuilt here rather than read back so the two declarations are
/// independently constructed; `metric_tests` then asserts the kernel holds
/// the same `ExprId` for both, which is what makes "it is an instance" a
/// measurement rather than a reading of two similar-looking statements.
fn declare_evt_approx_max_via_metric(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = cty(d, c);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let inst = d.kernel().const_(p.creal_metric, vec![]);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_ty = rle(d, c, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pred = d.const_app(p.continuity.interval, &[a, b]);
    let htb = d.lemma(p.interval.creal_totally_bounded_on_interval, &[a, b, hab]);
    let huc = d.lemma(p.continuity.creal_uniformly_continuous_on, &[f, a, b, u]);
    let proof = d.lemma(p.compactness.evt_approx_max, &[inst, pred, f, htb, huc, n]);

    let goal = {
        let rate_n = unit_rate(d, c, n);
        let gp = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let px = d.apply(pred, &[x]);
            let fx = d.apply(f, &[x]);
            let padded = radd(d, c, fx, rate_n);
            let all = {
                let y_fv = d.fresh_fvar();
                let y = d.kernel().fvar(y_fv);
                let py = d.apply(pred, &[y]);
                let fy = d.apply(f, &[y]);
                let concl = rle(d, c, fy, padded);
                let out = d.arrow(py, concl);
                d.pi_fv(y_fv, carrier, out)
            };
            let body = d.and(px, all);
            d.lam_fv(x_fv, carrier, body)
        };
        exists_ty(d, c, carrier, gp)
    };

    let ty = {
        let t = d.pi_fv(n_fv, nat, goal);
        let t = d.arrow(u_ty, t);
        let t = d.arrow(hab_ty, t);
        let t = d.pi_fv(b_fv, carrier, t);
        let t = d.pi_fv(a_fv, carrier, t);
        d.pi_fv(f_fv, func_ty, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, proof);
        let t = d.lam_fv(u_fv, u_ty, t);
        let t = d.lam_fv(hab_fv, hab_ty, t);
        let t = d.lam_fv(b_fv, carrier, t);
        let t = d.lam_fv(a_fv, carrier, t);
        d.lam_fv(f_fv, func_ty, t)
    };
    theorem(d, p.interval.creal_evt_approx_max_via_metric, ty, value)
}
