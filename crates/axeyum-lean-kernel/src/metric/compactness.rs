//! `Metric.TotallyBounded*` / `Metric.Compact*` / `Metric.evt_approx_max` —
//! **W2-3, Bishop compactness and the Extreme Value Theorem stated once and
//! proved once, over an arbitrary metric space.**
//!
//! ## Bishop compactness is not a cover condition
//!
//! ADR-1602 chose the metric layer over open sets precisely so that the
//! compactness this library needs is expressible without a topology. Bishop's
//! definition (*Constructive Analysis*, §4.2) is
//!
//! > a metric space is **compact** iff it is **complete** and **totally
//! > bounded**,
//!
//! and both halves are metric conditions. `Metric.Complete` landed with the
//! carrier; [`CompactnessNames::totally_bounded`] is the other half, and
//! [`CompactnessNames::compact`] is their conjunction. No open set, no
//! index type ranging over a family of subsets, no finite subcover.
//!
//! ## The net is data, and it is indexed by ℕ, not by a `List`
//!
//! Total boundedness says: for every accuracy `n` there is a **finite
//! ε-net** — finitely many points such that every point of the space is
//! within `1/(n+1)` of one of them. "Finitely many points" is written here as
//! a pair
//!
//! ```text
//! g : Nat → Nat → carrier      -- g n i is the i-th point of the n-th net
//! N : Nat → Nat                -- the n-th net is g n 0 … g n (N n)
//! ```
//!
//! rather than as a `List carrier`, for two reasons that are measurements and
//! not preferences. First, the covering clause has to *produce* an index, and
//! `∃ i, Nat.le i (N n) ∧ …` is one `Exists` over `Nat` — a shape this kernel
//! eliminates freely into `Prop` — whereas membership in a list is an
//! inductive predicate whose elimination brings its own recursor. Second,
//! [`CompactnessNames::approx_max_up_to`], the finite-maximum lemma the EVT
//! runs on, is an induction on that very bound `N`; over a list it would be
//! an induction on the list and every `Nat.le` step would become a `List`
//! step for no gain.
//!
//! `NetIn` — every net point satisfies the relativizing predicate — is a
//! **separate field** of total boundedness rather than a convention, and it
//! is load-bearing twice: the EVT's witness is one of the net points, so the
//! conclusion `P x` comes from `NetIn` directly, and uniform continuity is
//! only assumed *on* `P`, so applying it to a net point needs `NetIn` again.
//! It also makes the net automatically **inhabited** (index `0` is always
//! `≤ N n`), which is why the EVT below needs no separate non-emptiness
//! hypothesis — a hypothesis Bishop's own statement carries.
//!
//! ## Subspaces are predicates (ADR-1602)
//!
//! This kernel has no `Subtype`, so a closed interval of ℝ is not a metric
//! space of its own; it is `Metric.Interval a b`, a predicate on `CReal`, and
//! every definition here comes in a relativized `*On` form taking
//! `P : M.carrier → Prop`. The un-relativized `TotallyBounded` / `Compact`
//! are stated too, for the whole-space case, and are *not* derived from the
//! relativized ones — that derivation needs a `P` that holds everywhere and
//! this logic prelude's `True` would put a spurious `And` in every consumer.
//!
//! ## What the EVT needs, and what it does not
//!
//! [`CompactnessNames::evt_approx_max`] takes **total boundedness alone**,
//! not compactness. Completeness is not used anywhere in its proof, and
//! saying so is worth more than hiding it behind the stronger hypothesis:
//! the approximate maximum is a statement about a finite net and a uniformly
//! continuous function, and the limit of a Cauchy sequence never appears.
//! [`CompactnessNames::evt_approx_max_of_compact`] states the Bishop-shaped
//! corollary on top, by projecting the conjunction.
//!
//! The conclusion is the **approximate** maximum
//!
//! ```text
//! ∀ n, ∃ x, P x ∧ ∀ y, P y → F y ≤ F x + 1/(n+1)
//! ```
//!
//! and not an attained one, for the reason `CReal.evt_approx_max`'s own
//! module documents at length and
//! `CReal.evt_attained_max_decides_sign` proves: an exact maximiser would
//! decide the sign of an arbitrary real. Landing the general theorem does not
//! move that boundary; it moves the *general* statement to where the specific
//! one already was.
//!
//! ## The estimate, in one line
//!
//! Fix `n` and write `m := 2n+1`, so `1/(m+1) + 1/(m+1) = 1/(n+1)`
//! (`Rat.natDivSucc_add` then `Rat.natDivSucc_halve`, and that identity is
//! [`CompactnessNames::creal_rate_split`]). Take the net at accuracy
//! `mu m`, where `mu` is uniform continuity's modulus. For any `y ∈ P` the
//! net supplies `i` with `d(y, g i) ≤ 1/(mu m + 1)`, so `F y ≤ F (g i) +
//! 1/(m+1)`; the finite approximate maximum supplies `j` with
//! `F (g i) ≤ F (g j) + 1/(m+1)`; the two halves add to `1/(n+1)`.

#![allow(
    clippy::doc_markdown,
    clippy::large_types_passed_by_value,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::CARRIER;
use super::MetricPrelude;
use super::continuity::{and_intro, dist, exists_elim, exists_intro, exists_ty, rle, unit_rate};
use crate::CRealPrelude;
use crate::Kernel;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::rat_eq_rewrite;

/// The kernel names `metric/compactness.rs` declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CompactnessNames {
    /// `Metric.NetIn M (P : M.carrier → Prop) (g : Nat → Nat → M.carrier)
    /// (N : Nat → Nat) : Prop := ∀ n i, Nat.le i (N n) → P (g n i)`.
    pub net_in: NameId,
    /// `Metric.NetCovers M P g N : Prop := ∀ n x, P x →
    /// ∃ i, Nat.le i (N n) ∧ CReal.le (M.dist x (g n i))
    ///        (CReal.ofRat (Rat.natDivSucc 1 n))`.
    pub net_covers: NameId,
    /// `Metric.TotallyBoundedOnWith M P g N :=
    /// And (Metric.NetIn M P g N) (Metric.NetCovers M P g N)`.
    pub totally_bounded_on_with: NameId,
    /// `Metric.TotallyBoundedOn M P := ∃ N g,
    /// Metric.TotallyBoundedOnWith M P g N`.
    pub totally_bounded_on: NameId,
    /// `Metric.CompleteOn M P := ∀ f, (∀ n, P (f n)) → Metric.Cauchy M f →
    /// ∃ L, P L ∧ Metric.TendsTo M f L` — completeness **relativized**: the
    /// limit is required to land back in `P`, which is what makes a closed
    /// interval complete and an open one not.
    pub complete_on: NameId,
    /// `Metric.CompactOn M P :=
    /// And (Metric.TotallyBoundedOn M P) (Metric.CompleteOn M P)` —
    /// **Bishop compactness**, relativized to a predicate.
    pub compact_on: NameId,
    /// `Metric.TotallyBoundedWith M g N : Prop` — the whole-space form.
    pub totally_bounded_with: NameId,
    /// `Metric.TotallyBounded M := ∃ N g, Metric.TotallyBoundedWith M g N`.
    pub totally_bounded: NameId,
    /// `Metric.Compact M :=
    /// And (Metric.TotallyBounded M) (Metric.Complete M)` — **Bishop
    /// compactness** of a whole metric space.
    pub compact: NameId,

    // --- the `CReal` rearrangements this file needed ------------------------
    /// `Metric.CReal.subAddCancel : ∀ u v,
    /// CReal.Equiv (CReal.add (CReal.add u (CReal.neg v)) v) u`.
    pub creal_sub_add_cancel: NameId,
    /// `Metric.CReal.leAddOfSubLe : ∀ u v e,
    /// CReal.le (CReal.add u (CReal.neg v)) e → CReal.le u (CReal.add v e)` —
    /// "move a term across `≤`". The reals prelude has no such lemma; the
    /// closest, `Metric.CReal.leOfSubNonpos`, is its `e = 0` instance.
    pub creal_le_add_of_sub_le: NameId,
    /// `Metric.CReal.leAddRate : ∀ t k,
    /// CReal.le t (CReal.add t (CReal.ofRat (Rat.natDivSucc 1 k)))`.
    pub creal_le_add_rate: NameId,
    /// `Metric.CReal.ltAddRate : ∀ t k,
    /// CReal.lt t (CReal.add t (CReal.ofRat (Rat.natDivSucc 1 k)))` — the
    /// **strict** version, and the only thing in this file that consumes the
    /// strict order. It is what
    /// [`CompactnessNames::approx_max_up_to`] cotransits on.
    pub creal_lt_add_rate: NameId,
    /// `Metric.CReal.rateSplit : ∀ n, CReal.Equiv
    /// (add (ofRat (natDivSucc 1 (Nat.succ (Nat.mul 2 n))))
    ///      (ofRat (natDivSucc 1 (Nat.succ (Nat.mul 2 n)))))
    /// (ofRat (natDivSucc 1 n))` — `1/(2n+2) + 1/(2n+2) = 1/(n+1)`, lifted
    /// from `Rat.natDivSucc_add` + `Rat.natDivSucc_halve` through
    /// `CReal.ofRat_add`. The index is spelled `Nat.succ (Nat.mul 2 n)`
    /// because that is `Rat.natDivSucc_halve`'s own spelling and the two must
    /// match syntactically for the rewrite to fire.
    pub creal_rate_split: NameId,

    /// `Metric.approxMaxUpTo : ∀ (h : Nat → CReal) (k N : Nat),
    /// ∃ j, Nat.le j N ∧ ∀ i, Nat.le i N →
    ///   CReal.le (h i) (CReal.add (h j) (CReal.ofRat (Rat.natDivSucc 1 k)))`
    /// — **the finite approximate maximum**, and the one genuinely
    /// constructive step in this file.
    ///
    /// An *exact* maximum of `N+1` reals is not available: choosing which
    /// index attains it decides comparisons between reals. An approximate one
    /// is, by induction on `N` and one cotransitivity split
    /// (`CReal.lt_cotrans`) per step at the pair `h j < h j + 1/(k+1)`. The
    /// slack does **not** accumulate: in the branch where the new element
    /// wins, the previous witness is discarded rather than chained through,
    /// and in the branch where it loses, the old witness's bound is reused
    /// verbatim.
    pub approx_max_up_to: NameId,
    /// `Metric.evt_approx_max : ∀ M P F,
    /// Metric.TotallyBoundedOn M P →
    /// Metric.UniformlyContinuousOn M Metric.creal P F →
    /// ∀ n, ∃ x, P x ∧ ∀ y, P y → CReal.le (F y)
    ///   (CReal.add (F x) (CReal.ofRat (Rat.natDivSucc 1 n)))`
    /// — **the Extreme Value Theorem over an arbitrary metric space.**
    ///
    /// Note the hypothesis: total boundedness, **not** compactness.
    /// Completeness is not used. See the module documentation.
    pub evt_approx_max: NameId,
    /// `Metric.evt_approx_max_of_compact : ∀ M P F, Metric.CompactOn M P → …`
    /// — the Bishop-shaped corollary, one `And.left` on top of
    /// [`Self::evt_approx_max`].
    pub evt_approx_max_of_compact: NameId,
    /// `Metric.creal_completeOn_interval : ∀ a b,
    /// Metric.CompleteOn Metric.creal (Metric.Interval a b)` — **half of
    /// "a closed interval of ℝ is Bishop-compact"**: a Cauchy sequence inside
    /// `[a,b]` converges, and its limit is still inside `[a,b]`.
    ///
    /// The route is `Metric.creal_complete`'s own, with two extra facts
    /// threaded through the same `Exists.rec`s:
    /// `CReal.converges_lower_bound` and `CReal.converges_upper_bound` read
    /// the two interval bounds off the `CReal.Converges` witness that
    /// `converges_of_cauchy` already produced. Neither is a new estimate.
    pub creal_complete_on_interval: NameId,
    /// `Metric.creal_evt_approx_max : ∀ F a b, CReal.le a b →
    /// CReal.UniformlyContinuousOn F a b → ∀ n,
    /// ∃ x, Metric.Interval a b x ∧ ∀ y, Metric.Interval a b y →
    ///   CReal.le (F y) (CReal.add (F x) (CReal.ofRat (Rat.natDivSucc 1 n)))`
    /// — **`CReal.evt_approx_max`'s conclusion, re-expressed in the general
    /// EVT's exact shape**, and proved from the existing interval theorem.
    ///
    /// This is the measurement the "is the interval EVT an instance of the
    /// general one?" question actually turns on, and it isolates the answer:
    /// the two **conclusions** are the same statement, differing only by
    /// `And`-currying (`P x ∧ Q` against `a ≤ x ∧ (x ≤ b ∧ Q)`, and
    /// `∀ y, P y → …` against `∀ y, a ≤ y → y ≤ b → …`), which four
    /// projections and two `And.intro`s reconcile with no estimate at all.
    /// What the two theorems do **not** share is the hypothesis: this one
    /// assumes `CReal.le a b` and its proof runs through `CReal.supOn`, while
    /// [`Self::evt_approx_max`] assumes [`Self::totally_bounded_on`]. So the
    /// derivation reduces entirely to proving the closed interval totally
    /// bounded; nothing else stands between the two theorems.
    pub creal_evt_approx_max: NameId,
}

impl CompactnessNames {
    /// Every name this module declares, paired with its rendered label.
    #[must_use]
    pub fn all(&self) -> Vec<(&'static str, NameId)> {
        vec![
            ("Metric.NetIn", self.net_in),
            ("Metric.NetCovers", self.net_covers),
            ("Metric.TotallyBoundedOnWith", self.totally_bounded_on_with),
            ("Metric.TotallyBoundedOn", self.totally_bounded_on),
            ("Metric.CompleteOn", self.complete_on),
            ("Metric.CompactOn", self.compact_on),
            ("Metric.TotallyBoundedWith", self.totally_bounded_with),
            ("Metric.TotallyBounded", self.totally_bounded),
            ("Metric.Compact", self.compact),
            ("Metric.CReal.subAddCancel", self.creal_sub_add_cancel),
            ("Metric.CReal.leAddOfSubLe", self.creal_le_add_of_sub_le),
            ("Metric.CReal.leAddRate", self.creal_le_add_rate),
            ("Metric.CReal.ltAddRate", self.creal_lt_add_rate),
            ("Metric.CReal.rateSplit", self.creal_rate_split),
            ("Metric.approxMaxUpTo", self.approx_max_up_to),
            ("Metric.evt_approx_max", self.evt_approx_max),
            (
                "Metric.evt_approx_max_of_compact",
                self.evt_approx_max_of_compact,
            ),
            (
                "Metric.creal_completeOn_interval",
                self.creal_complete_on_interval,
            ),
            ("Metric.creal_evt_approx_max", self.creal_evt_approx_max),
        ]
    }
}

pub(super) fn intern(kernel: &mut Kernel, metric: NameId) -> CompactnessNames {
    let creal_ns = kernel.name_str(metric, "CReal");
    CompactnessNames {
        net_in: kernel.name_str(metric, "NetIn"),
        net_covers: kernel.name_str(metric, "NetCovers"),
        totally_bounded_on_with: kernel.name_str(metric, "TotallyBoundedOnWith"),
        totally_bounded_on: kernel.name_str(metric, "TotallyBoundedOn"),
        complete_on: kernel.name_str(metric, "CompleteOn"),
        compact_on: kernel.name_str(metric, "CompactOn"),
        totally_bounded_with: kernel.name_str(metric, "TotallyBoundedWith"),
        totally_bounded: kernel.name_str(metric, "TotallyBounded"),
        compact: kernel.name_str(metric, "Compact"),
        creal_sub_add_cancel: kernel.name_str(creal_ns, "subAddCancel"),
        creal_le_add_of_sub_le: kernel.name_str(creal_ns, "leAddOfSubLe"),
        creal_le_add_rate: kernel.name_str(creal_ns, "leAddRate"),
        creal_lt_add_rate: kernel.name_str(creal_ns, "ltAddRate"),
        creal_rate_split: kernel.name_str(creal_ns, "rateSplit"),
        approx_max_up_to: kernel.name_str(metric, "approxMaxUpTo"),
        evt_approx_max: kernel.name_str(metric, "evt_approx_max"),
        evt_approx_max_of_compact: kernel.name_str(metric, "evt_approx_max_of_compact"),
        creal_complete_on_interval: kernel.name_str(metric, "creal_completeOn_interval"),
        creal_evt_approx_max: kernel.name_str(metric, "creal_evt_approx_max"),
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
    const STEPS: [Step; 19] = [
        ("NetIn", declare_net_in),
        ("NetCovers", declare_net_covers),
        ("TotallyBoundedOnWith", declare_totally_bounded_on_with),
        ("TotallyBoundedOn", declare_totally_bounded_on),
        ("CompleteOn", declare_complete_on),
        ("CompactOn", declare_compact_on),
        ("TotallyBoundedWith", declare_totally_bounded_with),
        ("TotallyBounded", declare_totally_bounded),
        ("Compact", declare_compact),
        ("CReal.subAddCancel", declare_sub_add_cancel),
        ("CReal.leAddOfSubLe", declare_le_add_of_sub_le),
        ("CReal.leAddRate", declare_le_add_rate),
        ("CReal.ltAddRate", declare_lt_add_rate),
        ("CReal.rateSplit", declare_rate_split),
        ("approxMaxUpTo", declare_approx_max_up_to),
        ("evt_approx_max", declare_evt_approx_max),
        (
            "evt_approx_max_of_compact",
            declare_evt_approx_max_of_compact,
        ),
        (
            "creal_completeOn_interval",
            declare_creal_complete_on_interval,
        ),
        ("creal_evt_approx_max", declare_creal_evt_approx_max),
    ];

    // `AXEYUM_METRIC_TIMING=1` prints one line per declaration. A slow or
    // rejected declaration in a straight-line build is otherwise attributed by
    // guesswork, and this repository has three recorded instances of a wrong
    // attribution being propagated in a brief before anyone measured.
    let timing = std::env::var_os("AXEYUM_METRIC_TIMING").is_some();
    for (label, step) in STEPS {
        let started = std::time::Instant::now();
        let outcome = step(d, c, p);
        if timing {
            eprintln!(
                "metric/compactness {label}: {:?} {}",
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

/// The single `Metric` binder the relativized definitions open, its carrier,
/// and the two function types the net is built from.
struct Space {
    metric_ty: ExprId,
    m_fv: u64,
    m: ExprId,
    carrier: ExprId,
    /// `M.carrier → Prop`.
    pred_ty: ExprId,
    /// `Nat → Nat → M.carrier`.
    net_ty: ExprId,
    /// `Nat → Nat`.
    count_ty: ExprId,
    /// `Nat → M.carrier`.
    seq_ty: ExprId,
}

fn space(d: &mut IntDev<'_>, p: MetricPrelude) -> Space {
    let metric_ty = d.kernel().const_(p.record.ind, vec![]);
    let sel = d.kernel().const_(p.record.sel(CARRIER), vec![]);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let carrier = d.apply(sel, &[m]);
    let prop = d.kernel().sort_zero();
    let pred_ty = d.arrow(carrier, prop);
    let nat = d.nat_ty();
    let count_ty = d.arrow(nat, nat);
    let seq_ty = d.arrow(nat, carrier);
    let net_ty = d.arrow(nat, seq_ty);
    Space {
        metric_ty,
        m_fv,
        m,
        carrier,
        pred_ty,
        net_ty,
        count_ty,
        seq_ty,
    }
}

/// `Nat.le a b`.
fn nle(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let name = d.prelude().le;
    d.const_app(name, &[a, b])
}

/// `Nat.succ (Nat.mul 2 n)` — the doubled index, spelled exactly as
/// `Rat.natDivSucc_halve` spells it.
fn dbl(d: &mut IntDev<'_>, n: ExprId) -> ExprId {
    let two = d.num(2);
    let doubled = NatOps::mul(d, two, n);
    d.succ(doubled)
}

fn radd(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.add, &[a, b])
}
fn rneg(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.const_app(c.neg, &[a])
}
fn req(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.equiv, &[a, b])
}
fn rrefl(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(c.equiv_refl, &[a])
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
) -> Result<(), KernelError> {
    d.kernel().add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

// ---------------------------------------------------------------------------
// Total boundedness and compactness, relativized.
// ---------------------------------------------------------------------------

/// `Metric.NetIn M P g N := ∀ n i, Nat.le i (N n) → P (g n i)`.
fn declare_net_in(
    d: &mut IntDev<'_>,
    _c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let s = space(d, p);
    let nat = d.nat_ty();
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let cnt_fv = d.fresh_fvar();
    let cnt = d.kernel().fvar(cnt_fv);

    let body = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let bound = d.apply(cnt, &[n]);
        let hyp = nle(d, i, bound);
        let point = d.apply(g, &[n, i]);
        let concl = d.apply(pred, &[point]);
        let out = d.arrow(hyp, concl);
        let out = d.pi_fv(i_fv, nat, out);
        d.pi_fv(n_fv, nat, out)
    };

    let value = {
        let t = d.lam_fv(cnt_fv, s.count_ty, body);
        let t = d.lam_fv(g_fv, s.net_ty, t);
        let t = d.lam_fv(pred_fv, s.pred_ty, t);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(s.count_ty, prop);
        let t = d.arrow(s.net_ty, t);
        let t = d.pi_fv(pred_fv, s.pred_ty, t);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    definition(d, p.compactness.net_in, ty, value)
}

/// `Metric.NetCovers M P g N := ∀ n x, P x →
/// ∃ i, Nat.le i (N n) ∧ CReal.le (M.dist x (g n i)) (1/(n+1))`.
fn declare_net_covers(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let s = space(d, p);
    let nat = d.nat_ty();
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let cnt_fv = d.fresh_fvar();
    let cnt = d.kernel().fvar(cnt_fv);

    let body = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let px = d.apply(pred, &[x]);

        let predicate = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.apply(cnt, &[n]);
            let small = nle(d, i, bound);
            let point = d.apply(g, &[n, i]);
            let dxg = dist(d, p, s.m, x, point);
            let rate = unit_rate(d, c, n);
            let close = rle(d, c, dxg, rate);
            let inner = d.and(small, close);
            d.lam_fv(i_fv, nat, inner)
        };
        let concl = exists_ty(d, c, nat, predicate);
        let out = d.arrow(px, concl);
        let out = d.pi_fv(x_fv, s.carrier, out);
        d.pi_fv(n_fv, nat, out)
    };

    let value = {
        let t = d.lam_fv(cnt_fv, s.count_ty, body);
        let t = d.lam_fv(g_fv, s.net_ty, t);
        let t = d.lam_fv(pred_fv, s.pred_ty, t);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(s.count_ty, prop);
        let t = d.arrow(s.net_ty, t);
        let t = d.pi_fv(pred_fv, s.pred_ty, t);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    definition(d, p.compactness.net_covers, ty, value)
}

/// `Metric.TotallyBoundedOnWith M P g N := And (NetIn …) (NetCovers …)`.
fn declare_totally_bounded_on_with(
    d: &mut IntDev<'_>,
    _c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let s = space(d, p);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let cnt_fv = d.fresh_fvar();
    let cnt = d.kernel().fvar(cnt_fv);

    let inside = d.const_app(p.compactness.net_in, &[s.m, pred, g, cnt]);
    let covers = d.const_app(p.compactness.net_covers, &[s.m, pred, g, cnt]);
    let body = d.and(inside, covers);

    let value = {
        let t = d.lam_fv(cnt_fv, s.count_ty, body);
        let t = d.lam_fv(g_fv, s.net_ty, t);
        let t = d.lam_fv(pred_fv, s.pred_ty, t);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(s.count_ty, prop);
        let t = d.arrow(s.net_ty, t);
        let t = d.pi_fv(pred_fv, s.pred_ty, t);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    definition(d, p.compactness.totally_bounded_on_with, ty, value)
}

/// `Metric.TotallyBoundedOn M P := ∃ N g, TotallyBoundedOnWith M P g N`.
fn declare_totally_bounded_on(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let s = space(d, p);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);

    let outer_pred = {
        let cnt_fv = d.fresh_fvar();
        let cnt = d.kernel().fvar(cnt_fv);
        let inner_pred = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let body = d.const_app(p.compactness.totally_bounded_on_with, &[s.m, pred, g, cnt]);
            d.lam_fv(g_fv, s.net_ty, body)
        };
        let inner = exists_ty(d, c, s.net_ty, inner_pred);
        d.lam_fv(cnt_fv, s.count_ty, inner)
    };
    let body = exists_ty(d, c, s.count_ty, outer_pred);

    let value = {
        let t = d.lam_fv(pred_fv, s.pred_ty, body);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(s.pred_ty, prop);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    definition(d, p.compactness.totally_bounded_on, ty, value)
}

/// `Metric.CompleteOn M P := ∀ f, (∀ n, P (f n)) → Metric.Cauchy M f →
/// ∃ L, P L ∧ Metric.TendsTo M f L`.
fn declare_complete_on(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let s = space(d, p);
    let nat = d.nat_ty();
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let stays = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_ = d.apply(f, &[n]);
        let body = d.apply(pred, &[fn_]);
        d.pi_fv(n_fv, nat, body)
    };
    let cauchy = d.const_app(p.cauchy, &[s.m, f]);
    let target = {
        let predicate = {
            let l_fv = d.fresh_fvar();
            let l = d.kernel().fvar(l_fv);
            let pl = d.apply(pred, &[l]);
            let tends = d.const_app(p.tends_to, &[s.m, f, l]);
            let inner = d.and(pl, tends);
            d.lam_fv(l_fv, s.carrier, inner)
        };
        exists_ty(d, c, s.carrier, predicate)
    };
    let body = {
        let out = d.arrow(cauchy, target);
        let out = d.arrow(stays, out);
        d.pi_fv(f_fv, s.seq_ty, out)
    };

    let value = {
        let t = d.lam_fv(pred_fv, s.pred_ty, body);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(s.pred_ty, prop);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    definition(d, p.compactness.complete_on, ty, value)
}

/// `Metric.CompactOn M P := And (TotallyBoundedOn M P) (CompleteOn M P)`.
fn declare_compact_on(
    d: &mut IntDev<'_>,
    _c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let s = space(d, p);
    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);

    let tb = d.const_app(p.compactness.totally_bounded_on, &[s.m, pred]);
    let cp = d.const_app(p.compactness.complete_on, &[s.m, pred]);
    let body = d.and(tb, cp);

    let value = {
        let t = d.lam_fv(pred_fv, s.pred_ty, body);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(s.pred_ty, prop);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    definition(d, p.compactness.compact_on, ty, value)
}

/// `Metric.TotallyBoundedWith M g N := ∀ n x,
/// ∃ i, Nat.le i (N n) ∧ CReal.le (M.dist x (g n i)) (1/(n+1))`.
fn declare_totally_bounded_with(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let s = space(d, p);
    let nat = d.nat_ty();
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let cnt_fv = d.fresh_fvar();
    let cnt = d.kernel().fvar(cnt_fv);

    let body = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let predicate = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let bound = d.apply(cnt, &[n]);
            let small = nle(d, i, bound);
            let point = d.apply(g, &[n, i]);
            let dxg = dist(d, p, s.m, x, point);
            let rate = unit_rate(d, c, n);
            let close = rle(d, c, dxg, rate);
            let inner = d.and(small, close);
            d.lam_fv(i_fv, nat, inner)
        };
        let concl = exists_ty(d, c, nat, predicate);
        let out = d.pi_fv(x_fv, s.carrier, concl);
        d.pi_fv(n_fv, nat, out)
    };

    let value = {
        let t = d.lam_fv(cnt_fv, s.count_ty, body);
        let t = d.lam_fv(g_fv, s.net_ty, t);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    let ty = {
        let prop = d.kernel().sort_zero();
        let t = d.arrow(s.count_ty, prop);
        let t = d.arrow(s.net_ty, t);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    definition(d, p.compactness.totally_bounded_with, ty, value)
}

/// `Metric.TotallyBounded M := ∃ N g, TotallyBoundedWith M g N`.
fn declare_totally_bounded(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let s = space(d, p);

    let outer_pred = {
        let cnt_fv = d.fresh_fvar();
        let cnt = d.kernel().fvar(cnt_fv);
        let inner_pred = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let body = d.const_app(p.compactness.totally_bounded_with, &[s.m, g, cnt]);
            d.lam_fv(g_fv, s.net_ty, body)
        };
        let inner = exists_ty(d, c, s.net_ty, inner_pred);
        d.lam_fv(cnt_fv, s.count_ty, inner)
    };
    let body = exists_ty(d, c, s.count_ty, outer_pred);

    let value = d.lam_fv(s.m_fv, s.metric_ty, body);
    let ty = {
        let prop = d.kernel().sort_zero();
        d.pi_fv(s.m_fv, s.metric_ty, prop)
    };
    definition(d, p.compactness.totally_bounded, ty, value)
}

/// `Metric.Compact M := And (TotallyBounded M) (Complete M)` — Bishop.
fn declare_compact(
    d: &mut IntDev<'_>,
    _c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let s = space(d, p);
    let tb = d.const_app(p.compactness.totally_bounded, &[s.m]);
    let cp = d.const_app(p.complete, &[s.m]);
    let body = d.and(tb, cp);
    let value = d.lam_fv(s.m_fv, s.metric_ty, body);
    let ty = {
        let prop = d.kernel().sort_zero();
        d.pi_fv(s.m_fv, s.metric_ty, prop)
    };
    definition(d, p.compactness.compact, ty, value)
}

// ---------------------------------------------------------------------------
// The `CReal` rearrangements. None of these is new mathematics; all four are
// steps the reals prelude never named.
// ---------------------------------------------------------------------------

/// `Metric.CReal.subAddCancel : ∀ u v, Equiv ((u + -v) + v) u`.
///
/// `add_assoc`, then `add_comm`+`add_neg` on the inner pair, then `add_zero`.
fn declare_sub_add_cancel(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = d.kernel().const_(c.creal, vec![]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let nv = rneg(d, c, v);
    let sub = radd(d, c, u, nv);
    let lhs = radd(d, c, sub, v);
    let inner = radd(d, c, nv, v);
    let mid = radd(d, c, u, inner);
    let assoc = d.lemma(c.add_assoc, &[u, nv, v]);

    // `-v + v ~ 0`, via `add_comm` then `add_neg`.
    let flipped = radd(d, c, v, nv);
    let comm = d.lemma(c.add_comm, &[nv, v]);
    let cancel = d.lemma(c.add_neg, &[v]);
    let zero = d.kernel().const_(c.zero, vec![]);
    let inner_zero = rtrans(d, c, inner, flipped, zero, comm, cancel);

    let u_zero = radd(d, c, u, zero);
    let refl_u = rrefl(d, c, u);
    let congr = d.lemma(c.add_congr, &[u, u, inner, zero, refl_u, inner_zero]);
    let add_zero = d.lemma(c.add_zero, &[u]);
    let tail = rtrans(d, c, mid, u_zero, u, congr, add_zero);
    let proof = rtrans(d, c, lhs, mid, u, assoc, tail);

    let ty = {
        let stmt = req(d, c, lhs, u);
        let t = d.pi_fv(v_fv, carrier, stmt);
        d.pi_fv(u_fv, carrier, t)
    };
    let value = {
        let t = d.lam_fv(v_fv, carrier, proof);
        d.lam_fv(u_fv, carrier, t)
    };
    theorem(d, p.compactness.creal_sub_add_cancel, ty, value)
}

/// `Metric.CReal.leAddOfSubLe : ∀ u v e, le (u + -v) e → le u (v + e)`.
fn declare_le_add_of_sub_le(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = d.kernel().const_(c.creal, vec![]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let nv = rneg(d, c, v);
    let sub = radd(d, c, u, nv);
    let hyp_ty = rle(d, c, sub, e);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let sub_v = radd(d, c, sub, v);
    let e_v = radd(d, c, e, v);
    let v_e = radd(d, c, v, e);
    let refl_v = d.lemma(c.le_refl, &[v]);
    let shifted = d.lemma(c.add_le_add, &[sub, e, v, v, h, refl_v]);
    let cancel = d.lemma(p.compactness.creal_sub_add_cancel, &[u, v]);
    let comm = d.lemma(c.add_comm, &[e, v]);
    let proof = d.lemma(c.le_congr, &[sub_v, u, e_v, v_e, cancel, comm, shifted]);

    let ty = {
        let concl = rle(d, c, u, v_e);
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
    theorem(d, p.compactness.creal_le_add_of_sub_le, ty, value)
}

/// `Metric.CReal.leAddRate : ∀ t k, le t (t + 1/(k+1))`.
fn declare_le_add_rate(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = d.kernel().const_(c.creal, vec![]);
    let nat = d.nat_ty();
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let one = d.num(1);
    let q = d.const_app(c.rat.nat_div_succ, &[one, k]);
    let nonneg = d.lemma(c.rat.zero_le_nat_div_succ, &[one, k]);
    let proof = d.lemma(c.le_add_of_nonneg, &[t, q, nonneg]);

    let ty = {
        let rate = unit_rate(d, c, k);
        let padded = radd(d, c, t, rate);
        let stmt = rle(d, c, t, padded);
        let out = d.pi_fv(k_fv, nat, stmt);
        d.pi_fv(t_fv, carrier, out)
    };
    let value = {
        let out = d.lam_fv(k_fv, nat, proof);
        d.lam_fv(t_fv, carrier, out)
    };
    theorem(d, p.compactness.creal_le_add_rate, ty, value)
}

/// `Metric.CReal.ltAddRate : ∀ t k, lt t (t + 1/(k+1))`.
///
/// `CReal.PosBound (ofRat (1/(k+1))) k` is `le (ofRat (1/(k+1)))
/// (ofRat (1/(k+1)))` — `le_refl`, with nothing to prove — so
/// `pos_of_pos_bound` gives `0 < 1/(k+1)` outright. Then
/// `add_lt_add_of_le_of_lt` at `t ≤ t` and `0 < 1/(k+1)` gives
/// `t + 0 < t + 1/(k+1)`, and `lt_congr` moves the left side across
/// `add_zero`.
fn declare_lt_add_rate(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = d.kernel().const_(c.creal, vec![]);
    let nat = d.nat_ty();
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let rate = unit_rate(d, c, k);
    let self_le = d.lemma(c.le_refl, &[rate]);
    let hpos = d.lemma(c.pos_of_pos_bound, &[rate, k, self_le]);

    let zero = d.kernel().const_(c.zero, vec![]);
    let t_le = d.lemma(c.le_refl, &[t]);
    let stepped = d.lemma(c.add_lt_add_of_le_of_lt, &[t, t, zero, rate, t_le, hpos]);

    let t_zero = radd(d, c, t, zero);
    let padded = radd(d, c, t, rate);
    let az = d.lemma(c.add_zero, &[t]);
    let refl_padded = rrefl(d, c, padded);
    let proof = d.lemma(
        c.lt_congr,
        &[t_zero, t, padded, padded, az, refl_padded, stepped],
    );

    let ty = {
        let stmt = d.const_app(c.lt, &[t, padded]);
        let out = d.pi_fv(k_fv, nat, stmt);
        d.pi_fv(t_fv, carrier, out)
    };
    let value = {
        let out = d.lam_fv(k_fv, nat, proof);
        d.lam_fv(t_fv, carrier, out)
    };
    theorem(d, p.compactness.creal_lt_add_rate, ty, value)
}

/// `Metric.CReal.rateSplit : ∀ n, Equiv (r + r) (1/(n+1))` for
/// `r := 1/(2n+2)`.
fn declare_rate_split(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let one = d.num(1);
    let two = d.num(2);
    let shifted = dbl(d, n);
    let q = d.const_app(c.rat.nat_div_succ, &[one, shifted]);
    let rate = d.const_app(c.of_rat, &[q]);
    let doubled_rate = radd(d, c, rate, rate);

    // `Equiv (ofRat q + ofRat q) (ofRat (q + q))`.
    let base = d.lemma(c.of_rat_add, &[q, q]);

    // `Rat.add q q = natDivSucc (1+1) (2n+1)`; `1+1` is `2` definitionally.
    let rat_add = d.int().rat_add;
    let sum_q = d.const_app(rat_add, &[q, q]);
    let fused_num = NatOps::add(d, one, one);
    let fused = d.const_app(c.rat.nat_div_succ, &[fused_num, shifted]);
    let fuse = d.lemma(c.rat.nat_div_succ_add, &[one, one, shifted]);
    let step1 = rat_eq_rewrite(d, sum_q, fused, fuse, base, &|d, z| {
        let rhs = d.const_app(c.of_rat, &[z]);
        req(d, c, doubled_rate, rhs)
    });

    // `natDivSucc 2 (2n+1) = natDivSucc 1 n`.
    let two_form = d.const_app(c.rat.nat_div_succ, &[two, shifted]);
    let target_q = d.const_app(c.rat.nat_div_succ, &[one, n]);
    let halve = d.lemma(c.rat.nat_div_succ_halve, &[n]);
    let proof = rat_eq_rewrite(d, two_form, target_q, halve, step1, &|d, z| {
        let rhs = d.const_app(c.of_rat, &[z]);
        req(d, c, doubled_rate, rhs)
    });

    let ty = {
        let target = unit_rate(d, c, n);
        let stmt = req(d, c, doubled_rate, target);
        d.pi_fv(n_fv, nat, stmt)
    };
    let value = d.lam_fv(n_fv, nat, proof);
    theorem(d, p.compactness.creal_rate_split, ty, value)
}

// ---------------------------------------------------------------------------
// The finite approximate maximum.
// ---------------------------------------------------------------------------

/// `Metric.approxMaxUpTo : ∀ h k N,
/// ∃ j, Nat.le j N ∧ ∀ i, Nat.le i N → le (h i) (h j + 1/(k+1))`.
fn declare_approx_max_up_to(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = d.kernel().const_(c.creal, vec![]);
    let seq_ty = d.arrow(nat, carrier);
    let natp = d.prelude();

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    // `fun j => Nat.le j bound ∧ ∀ i, Nat.le i bound → h i ≤ h j + 1/(k+1)`.
    let claim_pred = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let small = nle(d, j, bound);
        let hj = d.apply(h, &[j]);
        let rate = unit_rate(d, c, k);
        let padded = radd(d, c, hj, rate);
        let all = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hi_small = nle(d, i, bound);
            let hi = d.apply(h, &[i]);
            let concl = rle(d, c, hi, padded);
            let out = d.arrow(hi_small, concl);
            d.pi_fv(i_fv, nat, out)
        };
        let body = d.and(small, all);
        d.lam_fv(j_fv, nat, body)
    };
    let motive = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let pred = claim_pred(d, bound);
        exists_ty(d, c, nat, pred)
    };

    // --- base: `N = 0`, witness `0`. --------------------------------------
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero = d.zero();
        let pred = claim_pred(d, zero);
        let small = nle(d, zero, zero);
        let refl = d.lemma(natp.le_refl_thm, &[zero]);
        let h0 = d.apply(h, &[zero]);
        let rate = unit_rate(d, c, k);
        let padded = radd(d, c, h0, rate);

        let all = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hyp_ty = nle(d, i, zero);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);
            // `i = 0` from `i ≤ 0` and `0 ≤ i`.
            let zero_le_i = d.lemma(natp.zero_le, &[i]);
            let i_eq_zero = d.lemma(natp.le_antisymm, &[i, zero, hyp, zero_le_i]);
            let zero_eq_i = NatOps::symm(d, i, zero, i_eq_zero);
            let at_zero = d.lemma(p.compactness.creal_le_add_rate, &[h0, k]);
            let body = d.nat_rewrite(zero, i, zero_eq_i, at_zero, &|d, z| {
                let hz = d.apply(h, &[z]);
                rle(d, c, hz, padded)
            });
            let t = d.lam_fv(hyp_fv, hyp_ty, body);
            d.lam_fv(i_fv, nat, t)
        };
        let all_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let hyp_ty = nle(d, i, zero);
            let hi = d.apply(h, &[i]);
            let concl = rle(d, c, hi, padded);
            let out = d.arrow(hyp_ty, concl);
            d.pi_fv(i_fv, nat, out)
        };
        let pair_proof = and_intro(d, c, small, all_ty, refl, all);
        exists_intro(d, c, nat, pred, zero, pair_proof)
    };

    // --- step: `N = succ j0`, one cotransitivity split. --------------------
    let step = |d: &mut IntDev<'_>, j0: ExprId, ih: ExprId| -> ExprId {
        let next = d.succ(j0);
        let goal = motive(d, next);
        let ih_pred = claim_pred(d, j0);

        let minor = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let small_j = nle(d, j, j0);
            let hj = d.apply(h, &[j]);
            let rate = unit_rate(d, c, k);
            let padded_j = radd(d, c, hj, rate);
            let all_j_ty = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hyp_ty = nle(d, i, j0);
                let hi = d.apply(h, &[i]);
                let concl = rle(d, c, hi, padded_j);
                let out = d.arrow(hyp_ty, concl);
                d.pi_fv(i_fv, nat, out)
            };
            let hyp_ty = d.and(small_j, all_j_ty);
            let hj_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hj_fv);
            let hjle = d.and_left(small_j, all_j_ty, hyp);
            let hjall = d.and_right(small_j, all_j_ty, hyp);

            let hnew = d.apply(h, &[next]);
            let hlt = d.lemma(p.compactness.creal_lt_add_rate, &[hj, k]);
            let cot = d.lemma(c.lt_cotrans, &[hj, padded_j, hlt, hnew]);
            let left_ty = d.const_app(c.lt, &[hj, hnew]);
            let right_ty = d.const_app(c.lt, &[hnew, padded_j]);

            let on_left = |d: &mut IntDev<'_>, hl: ExprId| -> ExprId {
                // The new element wins: the witness is `succ j0`.
                let pred = claim_pred(d, next);
                let small = nle(d, next, next);
                let refl = d.lemma(natp.le_refl_thm, &[next]);
                let padded_new = radd(d, c, hnew, rate);
                let hjle_new = d.lemma(c.le_of_lt, &[hj, hnew, hl]);

                let all_ty = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hyp_ty = nle(d, i, next);
                    let hi = d.apply(h, &[i]);
                    let concl = rle(d, c, hi, padded_new);
                    let out = d.arrow(hyp_ty, concl);
                    d.pi_fv(i_fv, nat, out)
                };
                let all = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hyp_ty = nle(d, i, next);
                    let hyp_fv = d.fresh_fvar();
                    let hi_le = d.kernel().fvar(hyp_fv);
                    let hi = d.apply(h, &[i]);
                    let target = rle(d, c, hi, padded_new);
                    let split = d.lemma(natp.lt_or_eq_of_le, &[i, next, hi_le]);
                    let lt_ty = d.const_app(natp.lt, &[i, next]);
                    let eq_ty = NatOps::eq(d, i, next);
                    let body = d.or_elim(
                        lt_ty,
                        eq_ty,
                        target,
                        split,
                        &|d, hlt_i| {
                            let small_i = d.lemma(natp.le_of_lt_succ, &[i, j0, hlt_i]);
                            let from_ih = d.apply(hjall, &[i, small_i]);
                            let refl_rate = d.lemma(c.le_refl, &[rate]);
                            let widened =
                                d.lemma(c.add_le_add, &[hj, hnew, rate, rate, hjle_new, refl_rate]);
                            d.lemma(c.le_trans, &[hi, padded_j, padded_new, from_ih, widened])
                        },
                        &|d, heq| {
                            let back = NatOps::symm(d, i, next, heq);
                            let at_new = d.lemma(p.compactness.creal_le_add_rate, &[hnew, k]);
                            d.nat_rewrite(next, i, back, at_new, &|d, z| {
                                let hz = d.apply(h, &[z]);
                                rle(d, c, hz, padded_new)
                            })
                        },
                    );
                    let t = d.lam_fv(hyp_fv, hyp_ty, body);
                    d.lam_fv(i_fv, nat, t)
                };
                let pair_proof = and_intro(d, c, small, all_ty, refl, all);
                exists_intro(d, c, nat, pred, next, pair_proof)
            };

            let on_right = |d: &mut IntDev<'_>, hr: ExprId| -> ExprId {
                // The old witness still dominates, with the SAME slack.
                let pred = claim_pred(d, next);
                let small = nle(d, j, next);
                let widened = d.lemma(natp.le_succ_of_le, &[j, j0, hjle]);
                let hnew_le = d.lemma(c.le_of_lt, &[hnew, padded_j, hr]);

                let all_ty = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hyp_ty = nle(d, i, next);
                    let hi = d.apply(h, &[i]);
                    let concl = rle(d, c, hi, padded_j);
                    let out = d.arrow(hyp_ty, concl);
                    d.pi_fv(i_fv, nat, out)
                };
                let all = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let hyp_ty = nle(d, i, next);
                    let hyp_fv = d.fresh_fvar();
                    let hi_le = d.kernel().fvar(hyp_fv);
                    let hi = d.apply(h, &[i]);
                    let target = rle(d, c, hi, padded_j);
                    let split = d.lemma(natp.lt_or_eq_of_le, &[i, next, hi_le]);
                    let lt_ty = d.const_app(natp.lt, &[i, next]);
                    let eq_ty = NatOps::eq(d, i, next);
                    let body = d.or_elim(
                        lt_ty,
                        eq_ty,
                        target,
                        split,
                        &|d, hlt_i| {
                            let small_i = d.lemma(natp.le_of_lt_succ, &[i, j0, hlt_i]);
                            d.apply(hjall, &[i, small_i])
                        },
                        &|d, heq| {
                            let back = NatOps::symm(d, i, next, heq);
                            d.nat_rewrite(next, i, back, hnew_le, &|d, z| {
                                let hz = d.apply(h, &[z]);
                                rle(d, c, hz, padded_j)
                            })
                        },
                    );
                    let t = d.lam_fv(hyp_fv, hyp_ty, body);
                    d.lam_fv(i_fv, nat, t)
                };
                let pair_proof = and_intro(d, c, small, all_ty, widened, all);
                exists_intro(d, c, nat, pred, j, pair_proof)
            };

            let body = d.or_elim(left_ty, right_ty, goal, cot, &on_left, &on_right);
            let t = d.lam_fv(hj_fv, hyp_ty, body);
            d.lam_fv(j_fv, nat, t)
        };

        exists_elim(d, c, nat, ih_pred, goal, ih, minor)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof = d.induct(&motive, &base, &step, n);

    let ty = {
        let stmt = motive(d, n);
        let t = d.pi_fv(n_fv, nat, stmt);
        let t = d.pi_fv(k_fv, nat, t);
        d.pi_fv(h_fv, seq_ty, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, proof);
        let t = d.lam_fv(k_fv, nat, t);
        d.lam_fv(h_fv, seq_ty, t)
    };
    theorem(d, p.compactness.approx_max_up_to, ty, value)
}

// ---------------------------------------------------------------------------
// The Extreme Value Theorem, over an arbitrary metric space.
// ---------------------------------------------------------------------------

/// `Metric.evt_approx_max`. See the module documentation for the estimate.
fn declare_evt_approx_max(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let s = space(d, p);
    let nat = d.nat_ty();
    let creal_ty = d.kernel().const_(c.creal, vec![]);
    let f_ty = d.arrow(s.carrier, creal_ty);
    let creal_inst = d.kernel().const_(p.creal_metric, vec![]);

    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let htb_fv = d.fresh_fvar();
    let htb = d.kernel().fvar(htb_fv);
    let htb_ty = d.const_app(p.compactness.totally_bounded_on, &[s.m, pred]);
    let huc_fv = d.fresh_fvar();
    let huc = d.kernel().fvar(huc_fv);
    let huc_ty = d.const_app(
        p.continuity.uniformly_continuous_on,
        &[s.m, creal_inst, pred, f],
    );
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // The goal: `∃ x, P x ∧ ∀ y, P y → F y ≤ F x + 1/(n+1)`.
    let goal_pred = |d: &mut IntDev<'_>| -> ExprId {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let px = d.apply(pred, &[x]);
        let fx = d.apply(f, &[x]);
        let rate_n = unit_rate(d, c, n);
        let padded = radd(d, c, fx, rate_n);
        let all = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let py = d.apply(pred, &[y]);
            let fy = d.apply(f, &[y]);
            let concl = rle(d, c, fy, padded);
            let out = d.arrow(py, concl);
            d.pi_fv(y_fv, s.carrier, out)
        };
        let body = d.and(px, all);
        d.lam_fv(x_fv, s.carrier, body)
    };
    let goal = {
        let gp = goal_pred(d);
        exists_ty(d, c, s.carrier, gp)
    };

    // --- innermost: the modulus is known, the net is known, the ------------
    //     approximate maximiser is known.
    let minor_over_count = {
        let cnt_fv = d.fresh_fvar();
        let cnt = d.kernel().fvar(cnt_fv);
        let inner_pred = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let body = d.const_app(p.compactness.totally_bounded_on_with, &[s.m, pred, g, cnt]);
            d.lam_fv(g_fv, s.net_ty, body)
        };
        let hyp_ty = exists_ty(d, c, s.net_ty, inner_pred);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let minor_over_net = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let inside = d.const_app(p.compactness.net_in, &[s.m, pred, g, cnt]);
            let covers = d.const_app(p.compactness.net_covers, &[s.m, pred, g, cnt]);
            let tbw_ty = d.and(inside, covers);
            let tbw_fv = d.fresh_fvar();
            let tbw = d.kernel().fvar(tbw_fv);
            let h_inside = d.and_left(inside, covers, tbw);
            let h_covers = d.and_right(inside, covers, tbw);

            let uc_pred = {
                let mu_fv = d.fresh_fvar();
                let mu = d.kernel().fvar(mu_fv);
                let body = d.const_app(
                    p.continuity.uniformly_continuous_on_with,
                    &[s.m, creal_inst, pred, f, mu],
                );
                d.lam_fv(mu_fv, s.count_ty, body)
            };

            let minor_over_mu = {
                let mu_fv = d.fresh_fvar();
                let mu = d.kernel().fvar(mu_fv);
                let hmu_ty = d.const_app(
                    p.continuity.uniformly_continuous_on_with,
                    &[s.m, creal_inst, pred, f, mu],
                );
                let hmu_fv = d.fresh_fvar();
                let hmu = d.kernel().fvar(hmu_fv);

                // `m := 2n+1`, `acc := mu m`, `K := N acc`.
                let m_index = dbl(d, n);
                let acc = d.apply(mu, &[m_index]);
                let bound = d.apply(cnt, &[acc]);
                let rate_m = unit_rate(d, c, m_index);

                // `hfun i := F (g acc i)`.
                let hfun = {
                    let i_fv = d.fresh_fvar();
                    let i = d.kernel().fvar(i_fv);
                    let point = d.apply(g, &[acc, i]);
                    let body = d.apply(f, &[point]);
                    d.lam_fv(i_fv, nat, body)
                };

                let max_pred = {
                    let j_fv = d.fresh_fvar();
                    let j = d.kernel().fvar(j_fv);
                    let small = nle(d, j, bound);
                    let hj = d.apply(hfun, &[j]);
                    let padded = radd(d, c, hj, rate_m);
                    let all = {
                        let i_fv = d.fresh_fvar();
                        let i = d.kernel().fvar(i_fv);
                        let hyp = nle(d, i, bound);
                        let hi = d.apply(hfun, &[i]);
                        let concl = rle(d, c, hi, padded);
                        let out = d.arrow(hyp, concl);
                        d.pi_fv(i_fv, nat, out)
                    };
                    let body = d.and(small, all);
                    d.lam_fv(j_fv, nat, body)
                };
                let hmax = d.lemma(p.compactness.approx_max_up_to, &[hfun, m_index, bound]);

                let minor_over_j = {
                    let j_fv = d.fresh_fvar();
                    let j = d.kernel().fvar(j_fv);
                    let small_j = nle(d, j, bound);
                    let hj = d.apply(hfun, &[j]);
                    let padded_j = radd(d, c, hj, rate_m);
                    let all_j_ty = {
                        let i_fv = d.fresh_fvar();
                        let i = d.kernel().fvar(i_fv);
                        let hyp = nle(d, i, bound);
                        let hi = d.apply(hfun, &[i]);
                        let concl = rle(d, c, hi, padded_j);
                        let out = d.arrow(hyp, concl);
                        d.pi_fv(i_fv, nat, out)
                    };
                    let hj_ty = d.and(small_j, all_j_ty);
                    let hjp_fv = d.fresh_fvar();
                    let hjp = d.kernel().fvar(hjp_fv);
                    let hjle = d.and_left(small_j, all_j_ty, hjp);
                    let hjall = d.and_right(small_j, all_j_ty, hjp);

                    let witness = d.apply(g, &[acc, j]);
                    let hpw = d.apply(h_inside, &[acc, j, hjle]);
                    let fw = d.apply(f, &[witness]);
                    let rate_n = unit_rate(d, c, n);
                    let padded_w = radd(d, c, fw, rate_n);

                    let all_ty = {
                        let y_fv = d.fresh_fvar();
                        let y = d.kernel().fvar(y_fv);
                        let py = d.apply(pred, &[y]);
                        let fy = d.apply(f, &[y]);
                        let concl = rle(d, c, fy, padded_w);
                        let out = d.arrow(py, concl);
                        d.pi_fv(y_fv, s.carrier, out)
                    };
                    let all = {
                        let y_fv = d.fresh_fvar();
                        let y = d.kernel().fvar(y_fv);
                        let py_ty = d.apply(pred, &[y]);
                        let hpy_fv = d.fresh_fvar();
                        let hpy = d.kernel().fvar(hpy_fv);
                        let fy = d.apply(f, &[y]);
                        let target = rle(d, c, fy, padded_w);

                        let cover_pred = {
                            let i_fv = d.fresh_fvar();
                            let i = d.kernel().fvar(i_fv);
                            let small = nle(d, i, bound);
                            let point = d.apply(g, &[acc, i]);
                            let dyg = dist(d, p, s.m, y, point);
                            let rate_acc = unit_rate(d, c, acc);
                            let close = rle(d, c, dyg, rate_acc);
                            let body = d.and(small, close);
                            d.lam_fv(i_fv, nat, body)
                        };
                        let hcov = d.apply(h_covers, &[acc, y, hpy]);

                        let minor_over_i = {
                            let i_fv = d.fresh_fvar();
                            let i = d.kernel().fvar(i_fv);
                            let small_i = nle(d, i, bound);
                            let point = d.apply(g, &[acc, i]);
                            let dyg = dist(d, p, s.m, y, point);
                            let rate_acc = unit_rate(d, c, acc);
                            let close_ty = rle(d, c, dyg, rate_acc);
                            let hi_ty = d.and(small_i, close_ty);
                            let hip_fv = d.fresh_fvar();
                            let hip = d.kernel().fvar(hip_fv);
                            let hile = d.and_left(small_i, close_ty, hip);
                            let hclose = d.and_right(small_i, close_ty, hip);

                            let hpi = d.apply(h_inside, &[acc, i, hile]);
                            let fi = d.apply(f, &[point]);

                            // `|F y − F (g acc i)| ≤ 1/(m+1)`.
                            let habs = d.apply(hmu, &[m_index, y, point, hpy, hpi, hclose]);
                            let nfi = rneg(d, c, fi);
                            let diff = radd(d, c, fy, nfi);
                            let mag = d.const_app(c.abs, &[diff]);
                            let self_le = d.lemma(c.le_abs_self, &[diff]);
                            let hsub = d.lemma(c.le_trans, &[diff, mag, rate_m, self_le, habs]);
                            let step_a = d.lemma(
                                p.compactness.creal_le_add_of_sub_le,
                                &[fy, fi, rate_m, hsub],
                            );
                            let padded_i = radd(d, c, fi, rate_m);

                            // `F (g acc i) ≤ F (g acc j) + 1/(m+1)`.
                            let step_b = d.apply(hjall, &[i, hile]);
                            let refl_rate = d.lemma(c.le_refl, &[rate_m]);
                            let widened = d.lemma(
                                c.add_le_add,
                                &[fi, padded_j, rate_m, rate_m, step_b, refl_rate],
                            );
                            let stacked = radd(d, c, padded_j, rate_m);
                            let chained =
                                d.lemma(c.le_trans, &[fy, padded_i, stacked, step_a, widened]);

                            // `(F w + r) + r ~ F w + (r + r) ~ F w + 1/(n+1)`.
                            let doubled = radd(d, c, rate_m, rate_m);
                            let assoc = d.lemma(c.add_assoc, &[hj, rate_m, rate_m]);
                            let split = d.lemma(p.compactness.creal_rate_split, &[n]);
                            let refl_hj = rrefl(d, c, hj);
                            let congr =
                                d.lemma(c.add_congr, &[hj, hj, doubled, rate_n, refl_hj, split]);
                            let mid = radd(d, c, hj, doubled);
                            let collapse = rtrans(d, c, stacked, mid, padded_w, assoc, congr);
                            let refl_fy = rrefl(d, c, fy);
                            let body = d.lemma(
                                c.le_congr,
                                &[fy, fy, stacked, padded_w, refl_fy, collapse, chained],
                            );
                            let t = d.lam_fv(hip_fv, hi_ty, body);
                            d.lam_fv(i_fv, nat, t)
                        };
                        let elim = exists_elim(d, c, nat, cover_pred, target, hcov, minor_over_i);
                        let t = d.lam_fv(hpy_fv, py_ty, elim);
                        d.lam_fv(y_fv, s.carrier, t)
                    };
                    let px_ty = d.apply(pred, &[witness]);
                    let pair_proof = and_intro(d, c, px_ty, all_ty, hpw, all);
                    let gp = goal_pred(d);
                    let intro = exists_intro(d, c, s.carrier, gp, witness, pair_proof);
                    let t = d.lam_fv(hjp_fv, hj_ty, intro);
                    d.lam_fv(j_fv, nat, t)
                };

                let body = exists_elim(d, c, nat, max_pred, goal, hmax, minor_over_j);
                let t = d.lam_fv(hmu_fv, hmu_ty, body);
                d.lam_fv(mu_fv, s.count_ty, t)
            };

            let body = exists_elim(d, c, s.count_ty, uc_pred, goal, huc, minor_over_mu);
            let t = d.lam_fv(tbw_fv, tbw_ty, body);
            d.lam_fv(g_fv, s.net_ty, t)
        };

        let body = exists_elim(d, c, s.net_ty, inner_pred, goal, hyp, minor_over_net);
        let t = d.lam_fv(hyp_fv, hyp_ty, body);
        d.lam_fv(cnt_fv, s.count_ty, t)
    };

    let outer_pred = {
        let cnt_fv = d.fresh_fvar();
        let cnt = d.kernel().fvar(cnt_fv);
        let inner_pred = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let body = d.const_app(p.compactness.totally_bounded_on_with, &[s.m, pred, g, cnt]);
            d.lam_fv(g_fv, s.net_ty, body)
        };
        let inner = exists_ty(d, c, s.net_ty, inner_pred);
        d.lam_fv(cnt_fv, s.count_ty, inner)
    };
    let proof = exists_elim(d, c, s.count_ty, outer_pred, goal, htb, minor_over_count);

    let ty = {
        let t = d.pi_fv(n_fv, nat, goal);
        let t = d.arrow(huc_ty, t);
        let t = d.arrow(htb_ty, t);
        let t = d.pi_fv(f_fv, f_ty, t);
        let t = d.pi_fv(pred_fv, s.pred_ty, t);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, proof);
        let t = d.lam_fv(huc_fv, huc_ty, t);
        let t = d.lam_fv(htb_fv, htb_ty, t);
        let t = d.lam_fv(f_fv, f_ty, t);
        let t = d.lam_fv(pred_fv, s.pred_ty, t);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    theorem(d, p.compactness.evt_approx_max, ty, value)
}

/// `Metric.evt_approx_max_of_compact` — the Bishop-shaped corollary.
fn declare_evt_approx_max_of_compact(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let s = space(d, p);
    let nat = d.nat_ty();
    let creal_ty = d.kernel().const_(c.creal, vec![]);
    let f_ty = d.arrow(s.carrier, creal_ty);
    let creal_inst = d.kernel().const_(p.creal_metric, vec![]);

    let pred_fv = d.fresh_fvar();
    let pred = d.kernel().fvar(pred_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let hc_ty = d.const_app(p.compactness.compact_on, &[s.m, pred]);
    let huc_fv = d.fresh_fvar();
    let huc = d.kernel().fvar(huc_fv);
    let huc_ty = d.const_app(
        p.continuity.uniformly_continuous_on,
        &[s.m, creal_inst, pred, f],
    );
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let tb_ty = d.const_app(p.compactness.totally_bounded_on, &[s.m, pred]);
    let cp_ty = d.const_app(p.compactness.complete_on, &[s.m, pred]);
    let htb = d.and_left(tb_ty, cp_ty, hc);
    let proof = d.lemma(p.compactness.evt_approx_max, &[s.m, pred, f, htb, huc, n]);

    let goal = {
        let gp = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let px = d.apply(pred, &[x]);
            let fx = d.apply(f, &[x]);
            let rate_n = unit_rate(d, c, n);
            let padded = radd(d, c, fx, rate_n);
            let all = {
                let y_fv = d.fresh_fvar();
                let y = d.kernel().fvar(y_fv);
                let py = d.apply(pred, &[y]);
                let fy = d.apply(f, &[y]);
                let concl = rle(d, c, fy, padded);
                let out = d.arrow(py, concl);
                d.pi_fv(y_fv, s.carrier, out)
            };
            let body = d.and(px, all);
            d.lam_fv(x_fv, s.carrier, body)
        };
        exists_ty(d, c, s.carrier, gp)
    };

    let ty = {
        let t = d.pi_fv(n_fv, nat, goal);
        let t = d.arrow(huc_ty, t);
        let t = d.arrow(hc_ty, t);
        let t = d.pi_fv(f_fv, f_ty, t);
        let t = d.pi_fv(pred_fv, s.pred_ty, t);
        d.pi_fv(s.m_fv, s.metric_ty, t)
    };
    let value = {
        let t = d.lam_fv(n_fv, nat, proof);
        let t = d.lam_fv(huc_fv, huc_ty, t);
        let t = d.lam_fv(hc_fv, hc_ty, t);
        let t = d.lam_fv(f_fv, f_ty, t);
        let t = d.lam_fv(pred_fv, s.pred_ty, t);
        d.lam_fv(s.m_fv, s.metric_ty, t)
    };
    theorem(d, p.compactness.evt_approx_max_of_compact, ty, value)
}

// ---------------------------------------------------------------------------
// The interval is complete.
// ---------------------------------------------------------------------------

/// `Metric.creal_completeOn_interval : ∀ a b,
/// Metric.CompleteOn Metric.creal (Metric.Interval a b)`.
fn declare_creal_complete_on_interval(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = d.kernel().const_(c.creal, vec![]);
    let nat = d.nat_ty();
    let seq_ty = d.arrow(nat, carrier);
    let inst = d.kernel().const_(p.creal_metric, vec![]);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let pred = d.const_app(p.continuity.interval, &[a, b]);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let stays_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_ = d.apply(f, &[n]);
        let body = d.apply(pred, &[fn_]);
        d.pi_fv(n_fv, nat, body)
    };
    let stays_fv = d.fresh_fvar();
    let stays = d.kernel().fvar(stays_fv);

    // The two one-sided families, read off `stays` with `And` projections.
    let lower_family = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_ = d.apply(f, &[n]);
        let lo = rle(d, c, a, fn_);
        let hi = rle(d, c, fn_, b);
        let hn = d.apply(stays, &[n]);
        let body = d.and_left(lo, hi, hn);
        d.lam_fv(n_fv, nat, body)
    };
    let upper_family = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let fn_ = d.apply(f, &[n]);
        let lo = rle(d, c, a, fn_);
        let hi = rle(d, c, fn_, b);
        let hn = d.apply(stays, &[n]);
        let body = d.and_right(lo, hi, hn);
        d.lam_fv(n_fv, nat, body)
    };

    let goal = {
        let predicate = {
            let l_fv = d.fresh_fvar();
            let l = d.kernel().fvar(l_fv);
            let pl = d.apply(pred, &[l]);
            let tends = d.const_app(p.tends_to, &[inst, f, l]);
            let inner = d.and(pl, tends);
            d.lam_fv(l_fv, carrier, inner)
        };
        exists_ty(d, c, carrier, predicate)
    };
    let goal_pred = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let pl = d.apply(pred, &[l]);
        let tends = d.const_app(p.tends_to, &[inst, f, l]);
        let inner = d.and(pl, tends);
        d.lam_fv(l_fv, carrier, inner)
    };

    // `fun K' => ∀ n, Within (seq (f n) n − seq L n) (natDivSucc K' n)`, at a
    // bound limit `l`.
    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
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

        // `Converges f l` is the very hypothesis we are eliminating, rebuilt
        // here so the two bound lemmas can consume it.
        let hconv = exists_intro(d, c, nat, converges_pred, kp, h);
        let hlow = d.lemma(c.converges_lower_bound, &[a, f, l, lower_family, hconv]);
        let hhigh = d.lemma(c.converges_upper_bound, &[f, l, b, upper_family, hconv]);
        let lo = rle(d, c, a, l);
        let hi = rle(d, c, l, b);
        let in_interval = and_intro(d, c, lo, hi, hlow, hhigh);

        let pl_ty = d.apply(pred, &[l]);
        let tends_ty = d.const_app(p.tends_to, &[inst, f, l]);
        let pair_proof = and_intro(d, c, pl_ty, tends_ty, in_interval, tends);
        let body = exists_intro(d, c, carrier, goal_pred, l, pair_proof);

        let t = d.lam_fv(h_fv, hyp_ty, body);
        d.lam_fv(kp_fv, nat, t)
    };

    let minor2 = {
        let converges_ty = d.const_app(c.converges, &[f, l]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = exists_elim(d, c, nat, converges_pred, goal, h, minor3);
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
        let body = exists_elim(d, c, carrier, converges_pred_over_l, goal, hex, minor2);
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
    let outer = exists_elim(d, c, nat, cauchy_pred, goal, hc, minor1);

    let value = {
        let t = d.lam_fv(hc_fv, hc_ty, outer);
        let t = d.lam_fv(stays_fv, stays_ty, t);
        let t = d.lam_fv(f_fv, seq_ty, t);
        let t = d.lam_fv(b_fv, carrier, t);
        d.lam_fv(a_fv, carrier, t)
    };
    let ty = {
        let concl = d.const_app(p.compactness.complete_on, &[inst, pred]);
        let t = d.pi_fv(b_fv, carrier, concl);
        d.pi_fv(a_fv, carrier, t)
    };
    theorem(d, p.compactness.creal_complete_on_interval, ty, value)
}

// ---------------------------------------------------------------------------
// The interval EVT, restated in the general EVT's shape.
// ---------------------------------------------------------------------------

/// `Metric.creal_evt_approx_max` — see [`CompactnessNames::creal_evt_approx_max`].
///
/// Everything here is `And` bookkeeping. `CReal.evt_approx_max` concludes
/// `∃ x, a ≤ x ∧ (x ≤ b ∧ ∀ y, a ≤ y → y ≤ b → F y ≤ F x + 1/(n+1))`;
/// `Metric.evt_approx_max` concludes
/// `∃ x, P x ∧ (∀ y, P y → F y ≤ F x + 1/(n+1))` at `P := Metric.Interval a b`.
/// With `Interval a b x` δβ-reducing to `a ≤ x ∧ x ≤ b`, the two differ by
/// exactly the association of the conjunctions and the currying of the two
/// range hypotheses on `y`. No estimate, no rate arithmetic, no new lemma.
fn declare_creal_evt_approx_max(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    p: MetricPrelude,
) -> Result<(), KernelError> {
    let carrier = d.kernel().const_(c.creal, vec![]);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);
    let hab_ty = rle(d, c, a, b);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let u_ty = d.const_app(c.uniformly_continuous_on, &[f, a, b]);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pred = d.const_app(p.continuity.interval, &[a, b]);
    let rate = unit_rate(d, c, n);

    // The metric-shaped goal.
    let goal_pred = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let px = d.apply(pred, &[x]);
        let fx = d.apply(f, &[x]);
        let padded = radd(d, c, fx, rate);
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
    let goal = exists_ty(d, c, carrier, goal_pred);

    // `CReal.evt_approx_max`'s own conclusion predicate, verbatim.
    let source_pred = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let lo = rle(d, c, a, x);
        let hi = rle(d, c, x, b);
        let fx = d.apply(f, &[x]);
        let padded = radd(d, c, fx, rate);
        let all = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let hay = rle(d, c, a, y);
            let hyb = rle(d, c, y, b);
            let fy = d.apply(f, &[y]);
            let concl = rle(d, c, fy, padded);
            let out = d.arrow(hyb, concl);
            let out = d.arrow(hay, out);
            d.pi_fv(y_fv, carrier, out)
        };
        let tail = d.and(hi, all);
        let body = d.and(lo, tail);
        d.lam_fv(x_fv, carrier, body)
    };
    let source = d.lemma(c.evt_row1.evt_approx_max, &[f, a, b, hab, u, n]);

    let minor = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let lo = rle(d, c, a, x);
        let hi = rle(d, c, x, b);
        let fx = d.apply(f, &[x]);
        let padded = radd(d, c, fx, rate);
        let all_src_ty = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let hay = rle(d, c, a, y);
            let hyb = rle(d, c, y, b);
            let fy = d.apply(f, &[y]);
            let concl = rle(d, c, fy, padded);
            let out = d.arrow(hyb, concl);
            let out = d.arrow(hay, out);
            d.pi_fv(y_fv, carrier, out)
        };
        let tail_ty = d.and(hi, all_src_ty);
        let hyp_ty = d.and(lo, tail_ty);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let hax = d.and_left(lo, tail_ty, hp);
        let rest = d.and_right(lo, tail_ty, hp);
        let hxb = d.and_left(hi, all_src_ty, rest);
        let hall = d.and_right(hi, all_src_ty, rest);

        let px_ty = d.apply(pred, &[x]);
        let px = and_intro(d, c, lo, hi, hax, hxb);

        let all_ty = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let py = d.apply(pred, &[y]);
            let fy = d.apply(f, &[y]);
            let concl = rle(d, c, fy, padded);
            let out = d.arrow(py, concl);
            d.pi_fv(y_fv, carrier, out)
        };
        let all = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let hay = rle(d, c, a, y);
            let hyb = rle(d, c, y, b);
            let py_ty = d.and(hay, hyb);
            let hpy_fv = d.fresh_fvar();
            let hpy = d.kernel().fvar(hpy_fv);
            let left = d.and_left(hay, hyb, hpy);
            let right = d.and_right(hay, hyb, hpy);
            let body = d.apply(hall, &[y, left, right]);
            let t = d.lam_fv(hpy_fv, py_ty, body);
            d.lam_fv(y_fv, carrier, t)
        };

        let pair_proof = and_intro(d, c, px_ty, all_ty, px, all);
        let intro = exists_intro(d, c, carrier, goal_pred, x, pair_proof);
        let t = d.lam_fv(hp_fv, hyp_ty, intro);
        d.lam_fv(x_fv, carrier, t)
    };

    let proof = exists_elim(d, c, carrier, source_pred, goal, source, minor);

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
    theorem(d, p.compactness.creal_evt_approx_max, ty, value)
}
