//! `Metric.prod` — **the product of two metric spaces**, with the max
//! metric, projections uniformly continuous, completeness transfer, and the
//! Euclidean plane related to `Metric.prod Metric.creal Metric.creal`
//! (roadmap W2-10, the half left open by `metric/subspace.rs`).
//!
//! Lane `metric-products`. A NEW top-level module, not a submodule of
//! `metric.rs` — everything here is built from `MetricPrelude`'s and
//! `CPointPrelude`'s **public** surface (`NameId`/field access), the same
//! boundary `creal_point.rs` and `metric/subspace.rs` each already keep, so
//! this file does not touch `metric.rs`'s own build pipeline, its private
//! helpers, or anything another lane owns this round.
//!
//! ## The carrier and the metric
//!
//! The carrier is the non-dependent `Sigma`: `Sigma.{0,0} M.carrier
//! (fun _ => N.carrier)` — the SAME dependent-pair inductive
//! `metric/subspace.rs` uses for `Subtype` (ADR-1613), specialized to a
//! constant family. `M.carrier : Sort 1`, i.e. `Type 0`, so the level
//! arguments are `[0, 0]` and the result sort is `Type (max 0 0) = Type 0 =
//! Sort 1` — exactly the sort `Metric`'s own `carrier` field demands.
//!
//! The distance is the **max metric**, `dist (x, y) := CReal.max (M.dist
//! (fst x) (fst y)) (N.dist (snd x) (snd y))`, not the sum metric. The
//! triangle inequality for the sum metric needs `add_le_add` twice and one
//! more `le_trans`-through-`add_assoc`-shaped rearrangement; the max metric
//! needs `max_le` once against a target that is *already* the max-metric
//! triangle inequality's own right-hand side, because `CReal.max_le`'s
//! premises are exactly "each component's bound is itself bounded by the
//! sum of the two per-component distances" — `le_max_left`/`le_max_right`
//! plus `add_le_add` plus `le_trans`, no case split, no extra lemma about
//! `max` distributing over `add`. That is cheaper on `CReal`, which is why
//! it is the one built here (the brief's call to make and record).
//!
//! ## What is proved
//!
//! - [`build_metric_prod_prelude`] declares `Metric.prod : Metric → Metric →
//!   Metric` (the full 12-field record) plus `Metric.prod_fst`/
//!   `Metric.prod_snd`, both proved uniformly continuous with the identity
//!   modulus (`le_max_left`/`le_max_right` plus one `le_trans`, no rate
//!   change at all — the projections are literally 1-Lipschitz).
//! - `Metric.prod_fst_continuous_of_continuous` /
//!   `Metric.prod_snd_continuous_of_continuous`: a map `G` into the product
//!   that is `Metric.Continuous` stays continuous after composing with
//!   either projection, at the SAME modulus. This is the `→` direction of
//!   "continuous into the product iff continuous in both components"; the
//!   `←` direction (both components continuous implies the pair map is)
//!   needs `CReal.max_le`-shaped combination of the two moduli and is not
//!   attempted this round (see the module's closing note).
//! - `Metric.prod_complete`: `Complete M → Complete N → Complete (Metric.prod
//!   M N)`. The Cauchy-ness of each PROJECTED sequence needs no combination
//!   of moduli (`le_max_left`/`le_max_right` bound each component by the
//!   SAME witness the product's own Cauchy proof already supplies), but
//!   recombining the two LIMITS' `TendsToAt` moduli into one witness for the
//!   pair does: `Rat.natDivSucc` is monotone increasing in its numerator
//!   (`Rat.natDivSucc_le_add_left`), so the combined modulus `K₁ + K₂`
//!   dominates both `K₁` and `K₂`'s own rate — the additive stand-in for
//!   "take the max of the two moduli". Forgetting to combine them (reusing
//!   `K₁` alone) is exactly the adversarial mutant `metric_prod_tests`
//!   pins.
//! - `Metric.cpoint_of_prod` / `Metric.prod_of_cpoint`: the two carrier maps
//!   between `CPoint` and `(Metric.prod Metric.creal Metric.creal).carrier`,
//!   and BOTH round trips, up to each side's own equivalence:
//!   `Metric.prod_of_cpoint_of_prod` (cheap: two `Sigma`/`CPoint` ι-reductions
//!   land on literally the same point) and `Metric.cpoint_of_prod_of_cpoint`
//!   (needs `CPoint.rec`, since `CPoint.mk (CPoint.x P) (CPoint.y P) ~ P` is
//!   not definitional for an arbitrary bound `P` — no `Subtype`-style
//!   ι-reduction is available on a *variable*).
//!
//!   **This is a carrier-level (setoid) equivalence, not an isometry.**
//!   `Metric.cpoint`'s distance is the Euclidean `sqrt (distSq P Q)`
//!   (`Metric.CPoint.dist`, `metric.rs`); `Metric.prod`'s is the max metric.
//!   The two are bi-Lipschitz equivalent (`max(|dx|,|dy|) ≤ sqrt(dx²+dy²) ≤
//!   max(|dx|,|dy|)·sqrt 2`) but not equal, so no isometry statement is
//!   attempted here — see the module's closing note for the precise
//!   obstruction and what proving it would need.
//!
//! ## What is deliberately NOT attempted this round
//!
//! - **Compactness transfer** (`CompactOn` for the product via the net-cover
//!   machinery in `metric/compactness.rs`). The brief marks this
//!   conditional on 1–3 landing; those three are substantial on their own
//!   (12-field record, two continuity theorems, a four-fold nested
//!   `Exists.rec` completeness proof), and the net-cover route needs its own
//!   careful reading of `compactness.rs`'s ~2000 lines this lane did not
//!   have room for.
//! - **The `←` direction of "continuous into the product iff continuous in
//!   both components"** (given `ContinuousAt P M (fst∘G) x` and `ContinuousAt
//!   P N (snd∘G) x`, produce `ContinuousAt P (Metric.prod M N) G x`). This
//!   needs `CReal.max_le` to combine the two component moduli into one, the
//!   same "combine, don't drop" shape as the completeness proof, but nested
//!   one level deeper (inside a modulus-producing existential rather than at
//!   the top of a theorem) — tractable, but out of this round's budget.
//! - **The isometry (or bi-Lipschitz) statement relating `Metric.cpoint` and
//!   `Metric.prod Metric.creal Metric.creal`'s DISTANCES** (as opposed to
//!   their carriers). It needs `CReal.sqrt` monotonicity against both
//!   `max(|dx|,|dy|)` and `|dx|+|dy|`, which is available in principle
//!   (`Metric.CPoint.dotLeSqrtMul`, `CReal.sqrt`'s own monotonicity lemmas)
//!   but was not derived this round.

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
use crate::MetricPrelude;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::nat_prelude::structures::mk_instance;
use crate::{
    METRIC_CARRIER as CARRIER, METRIC_DIST as DIST, METRIC_DIST_COMM as DIST_COMM,
    METRIC_DIST_CONGR as DIST_CONGR, METRIC_DIST_EQUIV as DIST_EQUIV,
    METRIC_DIST_NONNEG as DIST_NONNEG, METRIC_DIST_SELF as DIST_SELF,
    METRIC_DIST_TRIANGLE as DIST_TRIANGLE, METRIC_EQUIV as EQUIV, METRIC_EQUIV_REFL as EQUIV_REFL,
    METRIC_EQUIV_SYMM as EQUIV_SYMM, METRIC_EQUIV_TRANS as EQUIV_TRANS,
};

#[cfg(test)]
mod metric_prod_tests;

// ---------------------------------------------------------------------------
// The prelude handle.
// ---------------------------------------------------------------------------

/// The interned names this file owns.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MetricProdNames {
    /// `Metric.prod : Metric → Metric → Metric` — the max-metric product,
    /// carried by `Sigma.{0,0} M.carrier (fun _ => N.carrier)`.
    pub prod: NameId,
    /// `Metric.prod_fst : Π M N, (Metric.prod M N).carrier → M.carrier`.
    pub prod_fst: NameId,
    /// `Metric.prod_snd : Π M N, (Metric.prod M N).carrier → N.carrier`.
    pub prod_snd: NameId,
    /// `Metric.prod_fst_uniformly_continuous : ∀ M N,
    /// Metric.UniformlyContinuous (Metric.prod M N) M (Metric.prod_fst M N)`
    /// — 1-Lipschitz, with modulus `fun n => n`.
    pub prod_fst_uniformly_continuous: NameId,
    /// `Metric.prod_snd_uniformly_continuous` — the same for `prod_snd`.
    pub prod_snd_uniformly_continuous: NameId,
    /// `Metric.prod_fst_continuous_of_continuous : ∀ P M N G,
    /// Metric.Continuous P (Metric.prod M N) G →
    /// Metric.Continuous P M (fun p => Metric.prod_fst M N (G p))`.
    pub prod_fst_continuous_of_continuous: NameId,
    /// `Metric.prod_snd_continuous_of_continuous` — the same for `prod_snd`.
    pub prod_snd_continuous_of_continuous: NameId,
    /// `Metric.prod_complete : ∀ M N, Metric.Complete M → Metric.Complete N →
    /// Metric.Complete (Metric.prod M N)`.
    pub prod_complete: NameId,
    /// `Metric.cpoint_of_prod : (Metric.prod Metric.creal
    /// Metric.creal).carrier → CPoint`.
    pub cpoint_of_prod: NameId,
    /// `Metric.prod_of_cpoint : CPoint → (Metric.prod Metric.creal
    /// Metric.creal).carrier`.
    pub prod_of_cpoint: NameId,
    /// `Metric.prod_of_cpoint_of_prod : ∀ p,
    /// (Metric.prod Metric.creal Metric.creal).equiv
    ///   (Metric.prod_of_cpoint (Metric.cpoint_of_prod p)) p` — round trip
    /// one, cheap (both maps ι-reduce on the other's literal constructor).
    pub prod_of_cpoint_of_prod: NameId,
    /// `Metric.cpoint_of_prod_of_cpoint : ∀ P,
    /// CPoint.Equiv (Metric.cpoint_of_prod (Metric.prod_of_cpoint P)) P` —
    /// round trip two, via `CPoint.rec` (see the module doc).
    pub cpoint_of_prod_of_cpoint: NameId,
}

impl MetricProdNames {
    /// Every name this file owns, for the inventory tests. Derived from the
    /// struct's own fields, never a literal list somewhere else.
    /// Named `owned_names`, not `all`: `check-kernel-trusted-core.py` resolves
    /// method calls loosely by name and the trusted core calls `.all(..)` on other
    /// receivers, so `all` here put 31 lines of this content file into the
    /// trusted closure (guard D, 2026-09-05; same as `ImageGroupNames`).
    pub fn owned_names(&self) -> Vec<(&'static str, NameId)> {
        vec![
            ("Metric.prod", self.prod),
            ("Metric.prod_fst", self.prod_fst),
            ("Metric.prod_snd", self.prod_snd),
            (
                "Metric.prod_fst_uniformly_continuous",
                self.prod_fst_uniformly_continuous,
            ),
            (
                "Metric.prod_snd_uniformly_continuous",
                self.prod_snd_uniformly_continuous,
            ),
            (
                "Metric.prod_fst_continuous_of_continuous",
                self.prod_fst_continuous_of_continuous,
            ),
            (
                "Metric.prod_snd_continuous_of_continuous",
                self.prod_snd_continuous_of_continuous,
            ),
            ("Metric.prod_complete", self.prod_complete),
            ("Metric.cpoint_of_prod", self.cpoint_of_prod),
            ("Metric.prod_of_cpoint", self.prod_of_cpoint),
            ("Metric.prod_of_cpoint_of_prod", self.prod_of_cpoint_of_prod),
            (
                "Metric.cpoint_of_prod_of_cpoint",
                self.cpoint_of_prod_of_cpoint,
            ),
        ]
    }
}

fn intern(kernel: &mut Kernel, metric: NameId) -> MetricProdNames {
    MetricProdNames {
        prod: kernel.name_str(metric, "prod"),
        prod_fst: kernel.name_str(metric, "prod_fst"),
        prod_snd: kernel.name_str(metric, "prod_snd"),
        prod_fst_uniformly_continuous: kernel.name_str(metric, "prod_fst_uniformly_continuous"),
        prod_snd_uniformly_continuous: kernel.name_str(metric, "prod_snd_uniformly_continuous"),
        prod_fst_continuous_of_continuous: kernel
            .name_str(metric, "prod_fst_continuous_of_continuous"),
        prod_snd_continuous_of_continuous: kernel
            .name_str(metric, "prod_snd_continuous_of_continuous"),
        prod_complete: kernel.name_str(metric, "prod_complete"),
        cpoint_of_prod: kernel.name_str(metric, "cpoint_of_prod"),
        prod_of_cpoint: kernel.name_str(metric, "prod_of_cpoint"),
        prod_of_cpoint_of_prod: kernel.name_str(metric, "prod_of_cpoint_of_prod"),
        cpoint_of_prod_of_cpoint: kernel.name_str(metric, "cpoint_of_prod_of_cpoint"),
    }
}

/// Build (or return, if already built) the `Metric.prod` declarations.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub fn build_metric_prod_prelude(kernel: &mut Kernel) -> Result<MetricProdNames, KernelError> {
    let mp = crate::build_metric_prelude(kernel)?;
    let cp = mp.cpoint;
    let creal = cp.creal;
    let metric_ns = {
        // `Metric.<x>` — the SAME interned namespace `metric.rs`'s own
        // `intern` produces (name interning is content-addressed, so this is
        // not a second, colliding `Metric` root).
        let root = kernel.anon();
        kernel.name_str(root, "Metric")
    };
    let names = intern(kernel, metric_ns);
    if kernel.environment().get(names.prod).is_some() {
        return Ok(names);
    }

    let mut d = IntDev::new(kernel, creal.rat.int);
    declare_prod(&mut d, creal, mp, names)?;
    declare_prod_fst(&mut d, creal, mp, names)?;
    declare_prod_snd(&mut d, creal, mp, names)?;
    declare_prod_fst_uniformly_continuous(&mut d, creal, mp, names)?;
    declare_prod_snd_uniformly_continuous(&mut d, creal, mp, names)?;
    declare_prod_fst_continuous_of_continuous(&mut d, creal, mp, names)?;
    declare_prod_snd_continuous_of_continuous(&mut d, creal, mp, names)?;
    declare_prod_complete(&mut d, creal, mp, names)?;
    declare_cpoint_of_prod(&mut d, creal, cp, mp, names)?;
    declare_prod_of_cpoint(&mut d, creal, cp, mp, names)?;
    declare_prod_of_cpoint_of_prod(&mut d, creal, cp, mp, names)?;
    declare_cpoint_of_prod_of_cpoint(&mut d, creal, cp, mp, names)?;

    Ok(names)
}

// ---------------------------------------------------------------------------
// Small term builders (local to this file; `metric.rs`'s own are private).
// ---------------------------------------------------------------------------

fn field(d: &mut IntDev<'_>, mp: MetricPrelude, m: ExprId, i: usize) -> ExprId {
    let s = d.kernel().const_(mp.record.sel(i), vec![]);
    d.apply(s, &[m])
}
fn metric_ty(d: &mut IntDev<'_>, mp: MetricPrelude) -> ExprId {
    d.kernel().const_(mp.record.ind, vec![])
}
fn rty(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    d.kernel().const_(c.creal, vec![])
}
fn rzero(d: &mut IntDev<'_>, c: CRealPrelude) -> ExprId {
    d.kernel().const_(c.zero, vec![])
}
fn rmax(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.max, &[a, b])
}
fn radd(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.add, &[a, b])
}
fn rle(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.le, &[a, b])
}
fn req(d: &mut IntDev<'_>, c: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(c.equiv, &[a, b])
}
fn nat_ty(d: &mut IntDev<'_>) -> ExprId {
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
/// `Exists elem_ty predicate`, at universe level 1 (every `elem_ty` used in
/// this file — `Nat`, a metric's `carrier`, `CReal` — is `Sort 1`).
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
/// Build `Exists.rec` from a witness/proof-name pair and a Rust closure for
/// the minor premise's body: `fun w hw => build(d, w, hw)`.
fn exists_elim_build(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    elem_ty: ExprId,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    build: impl FnOnce(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let w_fv = d.fresh_fvar();
    let w = d.kernel().fvar(w_fv);
    let pred_w = d.apply(predicate, &[w]);
    let hw_fv = d.fresh_fvar();
    let hw = d.kernel().fvar(hw_fv);
    let body = build(d, w, hw);
    let minor = {
        let inner = d.lam_fv(hw_fv, pred_w, body);
        d.lam_fv(w_fv, elem_ty, inner)
    };
    exists_elim(d, c, elem_ty, predicate, target, witness, minor)
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
// The `Sigma.{0,0}` pair carrier, for two ALREADY-BUILT metric-space terms
// `m`, `n` (either free variables or literal constants).
// ---------------------------------------------------------------------------

struct ProdPieces {
    m_carrier: ExprId,
    n_carrier: ExprId,
    /// `Sigma.{0,0} m_carrier (fun _ => n_carrier)`.
    prod_carrier: ExprId,
    /// `Sigma.fst.{0,0} m_carrier beta` — apply to one more argument.
    fst_head: ExprId,
    /// `Sigma.snd.{0,0} m_carrier beta` — apply to one more argument.
    snd_head: ExprId,
    /// `Sigma.mk.{0,0} m_carrier beta` — apply to two more arguments.
    mk_head: ExprId,
}

fn prod_pieces(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    m: ExprId,
    n: ExprId,
) -> ProdPieces {
    let zero = d.kernel().level_zero();
    let sigma = c.rat.int.logic.sigma;
    let m_carrier = field(d, mp, m, CARRIER);
    let n_carrier = field(d, mp, n, CARRIER);
    let beta = {
        let dummy = d.fresh_fvar();
        d.lam_fv(dummy, m_carrier, n_carrier)
    };
    let prod_carrier = {
        let head = d.kernel().const_(sigma.sigma, vec![zero, zero]);
        d.apply(head, &[m_carrier, beta])
    };
    let fst_head = {
        let head = d.kernel().const_(sigma.sigma_fst, vec![zero, zero]);
        d.apply(head, &[m_carrier, beta])
    };
    let snd_head = {
        let head = d.kernel().const_(sigma.sigma_snd, vec![zero, zero]);
        d.apply(head, &[m_carrier, beta])
    };
    let mk_head = {
        let head = d.kernel().const_(sigma.sigma_mk, vec![zero, zero]);
        d.apply(head, &[m_carrier, beta])
    };
    ProdPieces {
        m_carrier,
        n_carrier,
        prod_carrier,
        fst_head,
        snd_head,
        mk_head,
    }
}
fn fst_of(d: &mut IntDev<'_>, pieces: &ProdPieces, x: ExprId) -> ExprId {
    d.apply(pieces.fst_head, &[x])
}
fn snd_of(d: &mut IntDev<'_>, pieces: &ProdPieces, x: ExprId) -> ExprId {
    d.apply(pieces.snd_head, &[x])
}
fn mk_of(d: &mut IntDev<'_>, pieces: &ProdPieces, a: ExprId, b: ExprId) -> ExprId {
    d.apply(pieces.mk_head, &[a, b])
}

/// The ambient `M`, `N` (free variables) plus the pair pieces built from
/// them. Fresh every call, matching `metric/subspace.rs`'s own `ambient()`.
struct MN {
    m_fv: u64,
    m: ExprId,
    n_fv: u64,
    n: ExprId,
    pieces: ProdPieces,
}
fn mn_ambient(d: &mut IntDev<'_>, c: CRealPrelude, mp: MetricPrelude) -> MN {
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pieces = prod_pieces(d, c, mp, m, n);
    MN {
        m_fv,
        m,
        n_fv,
        n,
        pieces,
    }
}

// ---------------------------------------------------------------------------
// `Metric.prod` — the twelve fields.
// ---------------------------------------------------------------------------

/// `fun x y => And (M.equiv (fst x) (fst y)) (N.equiv (snd x) (snd y))`.
fn build_equiv(d: &mut IntDev<'_>, mp: MetricPrelude, mn: &MN) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let fx = fst_of(d, &mn.pieces, x);
    let fy = fst_of(d, &mn.pieces, y);
    let sx = snd_of(d, &mn.pieces, x);
    let sy = snd_of(d, &mn.pieces, y);
    let m_equiv = field(d, mp, mn.m, EQUIV);
    let n_equiv = field(d, mp, mn.n, EQUIV);
    let left = d.apply(m_equiv, &[fx, fy]);
    let right = d.apply(n_equiv, &[sx, sy]);
    let body = d.and(left, right);
    let with_y = d.lam_fv(y_fv, mn.pieces.prod_carrier, body);
    d.lam_fv(x_fv, mn.pieces.prod_carrier, with_y)
}

/// `fun x => And.intro _ _ (M.equivRefl (fst x)) (N.equivRefl (snd x))`.
fn build_equiv_refl(d: &mut IntDev<'_>, mp: MetricPrelude, mn: &MN) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let fx = fst_of(d, &mn.pieces, x);
    let sx = snd_of(d, &mn.pieces, x);
    let m_equiv = field(d, mp, mn.m, EQUIV);
    let n_equiv = field(d, mp, mn.n, EQUIV);
    let left_ty = d.apply(m_equiv, &[fx, fx]);
    let right_ty = d.apply(n_equiv, &[sx, sx]);
    let m_er = field(d, mp, mn.m, EQUIV_REFL);
    let n_er = field(d, mp, mn.n, EQUIV_REFL);
    let proof_l = d.apply(m_er, &[fx]);
    let proof_r = d.apply(n_er, &[sx]);
    let intro = d.int().logic.and_intro;
    let body = d.const_app(intro, &[left_ty, right_ty, proof_l, proof_r]);
    d.lam_fv(x_fv, mn.pieces.prod_carrier, body)
}

/// `fun x y h => And.intro _ _ (M.equivSymm (fst x) (fst y) h.left)
///                            (N.equivSymm (snd x) (snd y) h.right)`.
fn build_equiv_symm(d: &mut IntDev<'_>, mp: MetricPrelude, mn: &MN) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let fx = fst_of(d, &mn.pieces, x);
    let fy = fst_of(d, &mn.pieces, y);
    let sx = snd_of(d, &mn.pieces, x);
    let sy = snd_of(d, &mn.pieces, y);
    let m_equiv = field(d, mp, mn.m, EQUIV);
    let n_equiv = field(d, mp, mn.n, EQUIV);
    let h_left_ty = d.apply(m_equiv, &[fx, fy]);
    let h_right_ty = d.apply(n_equiv, &[sx, sy]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.and(h_left_ty, h_right_ty);
    let h_l = d.and_left(h_left_ty, h_right_ty, h);
    let h_r = d.and_right(h_left_ty, h_right_ty, h);
    let m_es = field(d, mp, mn.m, EQUIV_SYMM);
    let n_es = field(d, mp, mn.n, EQUIV_SYMM);
    let proof_l = d.apply(m_es, &[fx, fy, h_l]);
    let proof_r = d.apply(n_es, &[sx, sy, h_r]);
    let concl_l = d.apply(m_equiv, &[fy, fx]);
    let concl_r = d.apply(n_equiv, &[sy, sx]);
    let intro = d.int().logic.and_intro;
    let body = d.const_app(intro, &[concl_l, concl_r, proof_l, proof_r]);
    let with_h = d.lam_fv(h_fv, h_ty, body);
    let with_y = d.lam_fv(y_fv, mn.pieces.prod_carrier, with_h);
    d.lam_fv(x_fv, mn.pieces.prod_carrier, with_y)
}

/// `fun x y z h1 h2 => And.intro _ _
///    (M.equivTrans (fst x)(fst y)(fst z) h1.left h2.left)
///    (N.equivTrans (snd x)(snd y)(snd z) h1.right h2.right)`.
fn build_equiv_trans(d: &mut IntDev<'_>, mp: MetricPrelude, mn: &MN) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let fx = fst_of(d, &mn.pieces, x);
    let fy = fst_of(d, &mn.pieces, y);
    let fz = fst_of(d, &mn.pieces, z);
    let sx = snd_of(d, &mn.pieces, x);
    let sy = snd_of(d, &mn.pieces, y);
    let sz = snd_of(d, &mn.pieces, z);
    let m_equiv = field(d, mp, mn.m, EQUIV);
    let n_equiv = field(d, mp, mn.n, EQUIV);

    let h1_left_ty = d.apply(m_equiv, &[fx, fy]);
    let h1_right_ty = d.apply(n_equiv, &[sx, sy]);
    let h1_ty = d.and(h1_left_ty, h1_right_ty);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);

    let h2_left_ty = d.apply(m_equiv, &[fy, fz]);
    let h2_right_ty = d.apply(n_equiv, &[sy, sz]);
    let h2_ty = d.and(h2_left_ty, h2_right_ty);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let h1_l = d.and_left(h1_left_ty, h1_right_ty, h1);
    let h1_r = d.and_right(h1_left_ty, h1_right_ty, h1);
    let h2_l = d.and_left(h2_left_ty, h2_right_ty, h2);
    let h2_r = d.and_right(h2_left_ty, h2_right_ty, h2);

    let m_et = field(d, mp, mn.m, EQUIV_TRANS);
    let n_et = field(d, mp, mn.n, EQUIV_TRANS);
    let proof_l = d.apply(m_et, &[fx, fy, fz, h1_l, h2_l]);
    let proof_r = d.apply(n_et, &[sx, sy, sz, h1_r, h2_r]);
    let concl_l = d.apply(m_equiv, &[fx, fz]);
    let concl_r = d.apply(n_equiv, &[sx, sz]);
    let intro = d.int().logic.and_intro;
    let body = d.const_app(intro, &[concl_l, concl_r, proof_l, proof_r]);

    let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
    let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);
    let with_z = d.lam_fv(z_fv, mn.pieces.prod_carrier, with_h1);
    let with_y = d.lam_fv(y_fv, mn.pieces.prod_carrier, with_z);
    d.lam_fv(x_fv, mn.pieces.prod_carrier, with_y)
}

/// `fun x y => CReal.max (M.dist (fst x)(fst y)) (N.dist (snd x)(snd y))` —
/// **the max metric.**
fn build_dist(d: &mut IntDev<'_>, c: CRealPrelude, mp: MetricPrelude, mn: &MN) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let fx = fst_of(d, &mn.pieces, x);
    let fy = fst_of(d, &mn.pieces, y);
    let sx = snd_of(d, &mn.pieces, x);
    let sy = snd_of(d, &mn.pieces, y);
    let m_dist = field(d, mp, mn.m, DIST);
    let n_dist = field(d, mp, mn.n, DIST);
    let dm = d.apply(m_dist, &[fx, fy]);
    let dn = d.apply(n_dist, &[sx, sy]);
    let body = rmax(d, c, dm, dn);
    let with_y = d.lam_fv(y_fv, mn.pieces.prod_carrier, body);
    d.lam_fv(x_fv, mn.pieces.prod_carrier, with_y)
}

/// `fun x x' y y' h1 h2 => CReal.max_congr _ _ _ _
///    (M.distCongr (fst x)(fst x')(fst y)(fst y') h1.left h2.left)
///    (N.distCongr (snd x)(snd x')(snd y)(snd y') h1.right h2.right)`.
fn build_dist_congr(d: &mut IntDev<'_>, c: CRealPrelude, mp: MetricPrelude, mn: &MN) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let xp_fv = d.fresh_fvar();
    let xp = d.kernel().fvar(xp_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let yp_fv = d.fresh_fvar();
    let yp = d.kernel().fvar(yp_fv);

    let fx = fst_of(d, &mn.pieces, x);
    let fxp = fst_of(d, &mn.pieces, xp);
    let fy = fst_of(d, &mn.pieces, y);
    let fyp = fst_of(d, &mn.pieces, yp);
    let sx = snd_of(d, &mn.pieces, x);
    let sxp = snd_of(d, &mn.pieces, xp);
    let sy = snd_of(d, &mn.pieces, y);
    let syp = snd_of(d, &mn.pieces, yp);

    let m_equiv = field(d, mp, mn.m, EQUIV);
    let n_equiv = field(d, mp, mn.n, EQUIV);
    let h1_left_ty = d.apply(m_equiv, &[fx, fxp]);
    let h1_right_ty = d.apply(n_equiv, &[sx, sxp]);
    let h1_ty = d.and(h1_left_ty, h1_right_ty);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_left_ty = d.apply(m_equiv, &[fy, fyp]);
    let h2_right_ty = d.apply(n_equiv, &[sy, syp]);
    let h2_ty = d.and(h2_left_ty, h2_right_ty);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let h1_l = d.and_left(h1_left_ty, h1_right_ty, h1);
    let h1_r = d.and_right(h1_left_ty, h1_right_ty, h1);
    let h2_l = d.and_left(h2_left_ty, h2_right_ty, h2);
    let h2_r = d.and_right(h2_left_ty, h2_right_ty, h2);

    let m_dc = field(d, mp, mn.m, DIST_CONGR);
    let n_dc = field(d, mp, mn.n, DIST_CONGR);
    let ha = d.apply(m_dc, &[fx, fxp, fy, fyp, h1_l, h2_l]);
    let hb = d.apply(n_dc, &[sx, sxp, sy, syp, h1_r, h2_r]);

    let m_dist = field(d, mp, mn.m, DIST);
    let n_dist = field(d, mp, mn.n, DIST);
    let a = d.apply(m_dist, &[fx, fy]);
    let ap = d.apply(m_dist, &[fxp, fyp]);
    let b = d.apply(n_dist, &[sx, sy]);
    let bp = d.apply(n_dist, &[sxp, syp]);
    let body = d.lemma(c.max_congr, &[a, ap, b, bp, ha, hb]);

    let with_h2 = d.lam_fv(h2_fv, h2_ty, body);
    let with_h1 = d.lam_fv(h1_fv, h1_ty, with_h2);
    let with_yp = d.lam_fv(yp_fv, mn.pieces.prod_carrier, with_h1);
    let with_y = d.lam_fv(y_fv, mn.pieces.prod_carrier, with_yp);
    let with_xp = d.lam_fv(xp_fv, mn.pieces.prod_carrier, with_y);
    d.lam_fv(x_fv, mn.pieces.prod_carrier, with_xp)
}

/// `0 ≤ max dM dN`, shared by `distNonneg` and half of `distSelf`.
fn zero_le_max(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    mn: &MN,
    fx: ExprId,
    fy: ExprId,
    sx: ExprId,
    sy: ExprId,
) -> ExprId {
    let m_dist = field(d, mp, mn.m, DIST);
    let n_dist = field(d, mp, mn.n, DIST);
    let dm = d.apply(m_dist, &[fx, fy]);
    let dn = d.apply(n_dist, &[sx, sy]);
    let m_dn = field(d, mp, mn.m, DIST_NONNEG);
    let zero_le_dm = d.apply(m_dn, &[fx, fy]);
    let dm_le_max = d.lemma(c.le_max_left, &[dm, dn]);
    let zero_c = rzero(d, c);
    let max_dm_dn = rmax(d, c, dm, dn);
    d.lemma(c.le_trans, &[zero_c, dm, max_dm_dn, zero_le_dm, dm_le_max])
}

/// `fun x y => le_trans 0 (M.dist ..) (max ..) M.distNonneg le_max_left`.
fn build_dist_nonneg(d: &mut IntDev<'_>, c: CRealPrelude, mp: MetricPrelude, mn: &MN) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let fx = fst_of(d, &mn.pieces, x);
    let fy = fst_of(d, &mn.pieces, y);
    let sx = snd_of(d, &mn.pieces, x);
    let sy = snd_of(d, &mn.pieces, y);
    let body = zero_le_max(d, c, mp, mn, fx, fy, sx, sy);
    let with_y = d.lam_fv(y_fv, mn.pieces.prod_carrier, body);
    d.lam_fv(x_fv, mn.pieces.prod_carrier, with_y)
}

/// `fun x y h => equiv_of_le_le (max dM dN) 0 (max_le dM dN 0 leM leN) (0 ≤ max)`.
fn build_dist_self(d: &mut IntDev<'_>, c: CRealPrelude, mp: MetricPrelude, mn: &MN) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let fx = fst_of(d, &mn.pieces, x);
    let fy = fst_of(d, &mn.pieces, y);
    let sx = snd_of(d, &mn.pieces, x);
    let sy = snd_of(d, &mn.pieces, y);

    let m_equiv = field(d, mp, mn.m, EQUIV);
    let n_equiv = field(d, mp, mn.n, EQUIV);
    let h_left_ty = d.apply(m_equiv, &[fx, fy]);
    let h_right_ty = d.apply(n_equiv, &[sx, sy]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_ty = d.and(h_left_ty, h_right_ty);
    let h_l = d.and_left(h_left_ty, h_right_ty, h);
    let h_r = d.and_right(h_left_ty, h_right_ty, h);

    let m_dist = field(d, mp, mn.m, DIST);
    let n_dist = field(d, mp, mn.n, DIST);
    let dm = d.apply(m_dist, &[fx, fy]);
    let dn = d.apply(n_dist, &[sx, sy]);
    let zero_c = rzero(d, c);

    let m_ds = field(d, mp, mn.m, DIST_SELF);
    let n_ds = field(d, mp, mn.n, DIST_SELF);
    let dm_equiv_zero = d.apply(m_ds, &[fx, fy, h_l]);
    let dn_equiv_zero = d.apply(n_ds, &[sx, sy, h_r]);
    let dm_le_zero = d.lemma(c.le_of_equiv, &[dm, zero_c, dm_equiv_zero]);
    let dn_le_zero = d.lemma(c.le_of_equiv, &[dn, zero_c, dn_equiv_zero]);
    let max_le_zero = d.lemma(c.max_le, &[dm, dn, zero_c, dm_le_zero, dn_le_zero]);
    let zero_le_max_proof = zero_le_max(d, c, mp, mn, fx, fy, sx, sy);

    let max_dm_dn = rmax(d, c, dm, dn);
    let body = d.lemma(
        c.equiv_of_le_le,
        &[max_dm_dn, zero_c, max_le_zero, zero_le_max_proof],
    );
    let with_h = d.lam_fv(h_fv, h_ty, body);
    let with_y = d.lam_fv(y_fv, mn.pieces.prod_carrier, with_h);
    d.lam_fv(x_fv, mn.pieces.prod_carrier, with_y)
}

/// `fun x y h => And.intro _ _ (M.distEquiv .. ) (N.distEquiv ..)`.
fn build_dist_equiv(d: &mut IntDev<'_>, c: CRealPrelude, mp: MetricPrelude, mn: &MN) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let fx = fst_of(d, &mn.pieces, x);
    let fy = fst_of(d, &mn.pieces, y);
    let sx = snd_of(d, &mn.pieces, x);
    let sy = snd_of(d, &mn.pieces, y);

    let m_dist = field(d, mp, mn.m, DIST);
    let n_dist = field(d, mp, mn.n, DIST);
    let dm = d.apply(m_dist, &[fx, fy]);
    let dn = d.apply(n_dist, &[sx, sy]);
    let zero_c = rzero(d, c);
    let max_dm_dn = rmax(d, c, dm, dn);

    let h_ty = req(d, c, max_dm_dn, zero_c);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let max_le_zero = d.lemma(c.le_of_equiv, &[max_dm_dn, zero_c, h]);

    let dm_le_max = d.lemma(c.le_max_left, &[dm, dn]);
    let dn_le_max = d.lemma(c.le_max_right, &[dm, dn]);
    let dm_le_zero = d.lemma(c.le_trans, &[dm, max_dm_dn, zero_c, dm_le_max, max_le_zero]);
    let dn_le_zero = d.lemma(c.le_trans, &[dn, max_dm_dn, zero_c, dn_le_max, max_le_zero]);

    let m_dn = field(d, mp, mn.m, DIST_NONNEG);
    let n_dn = field(d, mp, mn.n, DIST_NONNEG);
    let zero_le_dm = d.apply(m_dn, &[fx, fy]);
    let zero_le_dn = d.apply(n_dn, &[sx, sy]);

    let dm_equiv_zero = d.lemma(c.equiv_of_le_le, &[dm, zero_c, dm_le_zero, zero_le_dm]);
    let dn_equiv_zero = d.lemma(c.equiv_of_le_le, &[dn, zero_c, dn_le_zero, zero_le_dn]);

    let m_de = field(d, mp, mn.m, DIST_EQUIV);
    let n_de = field(d, mp, mn.n, DIST_EQUIV);
    let proof_l = d.apply(m_de, &[fx, fy, dm_equiv_zero]);
    let proof_r = d.apply(n_de, &[sx, sy, dn_equiv_zero]);

    let m_equiv = field(d, mp, mn.m, EQUIV);
    let n_equiv = field(d, mp, mn.n, EQUIV);
    let concl_l = d.apply(m_equiv, &[fx, fy]);
    let concl_r = d.apply(n_equiv, &[sx, sy]);
    let intro = d.int().logic.and_intro;
    let body = d.const_app(intro, &[concl_l, concl_r, proof_l, proof_r]);

    let with_h = d.lam_fv(h_fv, h_ty, body);
    let with_y = d.lam_fv(y_fv, mn.pieces.prod_carrier, with_h);
    d.lam_fv(x_fv, mn.pieces.prod_carrier, with_y)
}

/// `fun x y => CReal.max_congr _ _ _ _ (M.distComm (fst x)(fst y))
///                                    (N.distComm (snd x)(snd y))`.
fn build_dist_comm(d: &mut IntDev<'_>, c: CRealPrelude, mp: MetricPrelude, mn: &MN) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let fx = fst_of(d, &mn.pieces, x);
    let fy = fst_of(d, &mn.pieces, y);
    let sx = snd_of(d, &mn.pieces, x);
    let sy = snd_of(d, &mn.pieces, y);

    let m_dist = field(d, mp, mn.m, DIST);
    let n_dist = field(d, mp, mn.n, DIST);
    let dm_xy = d.apply(m_dist, &[fx, fy]);
    let dm_yx = d.apply(m_dist, &[fy, fx]);
    let dn_xy = d.apply(n_dist, &[sx, sy]);
    let dn_yx = d.apply(n_dist, &[sy, sx]);

    let m_dcm = field(d, mp, mn.m, DIST_COMM);
    let n_dcm = field(d, mp, mn.n, DIST_COMM);
    let hm = d.apply(m_dcm, &[fx, fy]);
    let hn = d.apply(n_dcm, &[sx, sy]);
    let body = d.lemma(c.max_congr, &[dm_xy, dm_yx, dn_xy, dn_yx, hm, hn]);

    let with_y = d.lam_fv(y_fv, mn.pieces.prod_carrier, body);
    d.lam_fv(x_fv, mn.pieces.prod_carrier, with_y)
}

/// `fun x y z => max_le dM(x,z) dN(x,z) (add (dist x y)(dist y z)) boundM boundN`.
fn build_dist_triangle(d: &mut IntDev<'_>, c: CRealPrelude, mp: MetricPrelude, mn: &MN) -> ExprId {
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let fx = fst_of(d, &mn.pieces, x);
    let fy = fst_of(d, &mn.pieces, y);
    let fz = fst_of(d, &mn.pieces, z);
    let sx = snd_of(d, &mn.pieces, x);
    let sy = snd_of(d, &mn.pieces, y);
    let sz = snd_of(d, &mn.pieces, z);

    let m_dist = field(d, mp, mn.m, DIST);
    let n_dist = field(d, mp, mn.n, DIST);
    let dm_xy = d.apply(m_dist, &[fx, fy]);
    let dm_yz = d.apply(m_dist, &[fy, fz]);
    let dm_xz = d.apply(m_dist, &[fx, fz]);
    let dn_xy = d.apply(n_dist, &[sx, sy]);
    let dn_yz = d.apply(n_dist, &[sy, sz]);
    let dn_xz = d.apply(n_dist, &[sx, sz]);

    let dist_xy = rmax(d, c, dm_xy, dn_xy);
    let dist_yz = rmax(d, c, dm_yz, dn_yz);
    let target = radd(d, c, dist_xy, dist_yz);

    // -- bound on the M component --
    let m_dt = field(d, mp, mn.m, DIST_TRIANGLE);
    let t1 = d.apply(m_dt, &[fx, fy, fz]); // le dm_xz (add dm_xy dm_yz)
    let t2a = d.lemma(c.le_max_left, &[dm_xy, dn_xy]); // le dm_xy dist_xy
    let t2b = d.lemma(c.le_max_left, &[dm_yz, dn_yz]); // le dm_yz dist_yz
    let sum_m = radd(d, c, dm_xy, dm_yz);
    let t2 = d.lemma(c.add_le_add, &[dm_xy, dist_xy, dm_yz, dist_yz, t2a, t2b]);
    let bound_m = d.lemma(c.le_trans, &[dm_xz, sum_m, target, t1, t2]);

    // -- bound on the N component --
    let n_dt = field(d, mp, mn.n, DIST_TRIANGLE);
    let u1 = d.apply(n_dt, &[sx, sy, sz]);
    let u2a = d.lemma(c.le_max_right, &[dm_xy, dn_xy]);
    let u2b = d.lemma(c.le_max_right, &[dm_yz, dn_yz]);
    let sum_n = radd(d, c, dn_xy, dn_yz);
    let u2 = d.lemma(c.add_le_add, &[dn_xy, dist_xy, dn_yz, dist_yz, u2a, u2b]);
    let bound_n = d.lemma(c.le_trans, &[dn_xz, sum_n, target, u1, u2]);

    let body = d.lemma(c.max_le, &[dm_xz, dn_xz, target, bound_m, bound_n]);

    let with_z = d.lam_fv(z_fv, mn.pieces.prod_carrier, body);
    let with_y = d.lam_fv(y_fv, mn.pieces.prod_carrier, with_z);
    d.lam_fv(x_fv, mn.pieces.prod_carrier, with_y)
}

/// `Metric.prod : Metric → Metric → Metric`.
fn declare_prod(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    let mn = mn_ambient(d, c, mp);

    // Order matters: this must match `FIELD_SUFFIXES` in `metric.rs` exactly
    // (carrier, equiv, equivRefl, equivSymm, equivTrans, dist, distCongr,
    // distNonneg, distSelf, distEquiv, distComm, distTriangle). `vec![...]`
    // evaluates its elements left-to-right, same as the sequential pushes
    // this replaced, which matters here: each builder also mints fresh
    // fvars from `d` in sequence.
    let fields = vec![
        mn.pieces.prod_carrier,
        build_equiv(d, mp, &mn),
        build_equiv_refl(d, mp, &mn),
        build_equiv_symm(d, mp, &mn),
        build_equiv_trans(d, mp, &mn),
        build_dist(d, c, mp, &mn),
        build_dist_congr(d, c, mp, &mn),
        build_dist_nonneg(d, c, mp, &mn),
        build_dist_self(d, c, mp, &mn),
        build_dist_equiv(d, c, mp, &mn),
        build_dist_comm(d, c, mp, &mn),
        build_dist_triangle(d, c, mp, &mn),
    ];

    let instance = mk_instance(d.kernel(), &mp.record, &fields);
    let mty = metric_ty(d, mp);
    let value = {
        let with_n = d.lam_fv(mn.n_fv, mty, instance);
        d.lam_fv(mn.m_fv, mty, with_n)
    };
    let ty = {
        let inner = d.pi_fv(mn.n_fv, mty, mty);
        d.pi_fv(mn.m_fv, mty, inner)
    };
    definition(d, names.prod, ty, value)
}

/// `(Metric.prod M N).carrier`, for `M`, `N` already-built terms.
fn prod_carrier_of(
    d: &mut IntDev<'_>,
    mp: MetricPrelude,
    names: MetricProdNames,
    m: ExprId,
    n: ExprId,
) -> ExprId {
    let app = d.const_app(names.prod, &[m, n]);
    field(d, mp, app, CARRIER)
}

/// `Metric.prod_fst : Π M N, (Metric.prod M N).carrier → M.carrier
///   := fun M N x => Sigma.fst M.carrier (fun _ => N.carrier) x`.
fn declare_prod_fst(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    let mn = mn_ambient(d, c, mp);
    let mty = metric_ty(d, mp);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let body = fst_of(d, &mn.pieces, x);

    let value = {
        let with_x = d.lam_fv(x_fv, mn.pieces.prod_carrier, body);
        let with_n = d.lam_fv(mn.n_fv, mty, with_x);
        d.lam_fv(mn.m_fv, mty, with_n)
    };
    let ty = {
        let prod_carrier = prod_carrier_of(d, mp, names, mn.m, mn.n);
        let inner = d.arrow(prod_carrier, mn.pieces.m_carrier);
        let with_n = d.pi_fv(mn.n_fv, mty, inner);
        d.pi_fv(mn.m_fv, mty, with_n)
    };
    definition(d, names.prod_fst, ty, value)
}

/// `Metric.prod_snd : Π M N, (Metric.prod M N).carrier → N.carrier
///   := fun M N x => Sigma.snd M.carrier (fun _ => N.carrier) x`.
fn declare_prod_snd(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    let mn = mn_ambient(d, c, mp);
    let mty = metric_ty(d, mp);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let body = snd_of(d, &mn.pieces, x);

    let value = {
        let with_x = d.lam_fv(x_fv, mn.pieces.prod_carrier, body);
        let with_n = d.lam_fv(mn.n_fv, mty, with_x);
        d.lam_fv(mn.m_fv, mty, with_n)
    };
    let ty = {
        let prod_carrier = prod_carrier_of(d, mp, names, mn.m, mn.n);
        let inner = d.arrow(prod_carrier, mn.pieces.n_carrier);
        let with_n = d.pi_fv(mn.n_fv, mty, inner);
        d.pi_fv(mn.m_fv, mty, with_n)
    };
    definition(d, names.prod_snd, ty, value)
}

// ---------------------------------------------------------------------------
// Continuity: the projections are 1-Lipschitz, and continuity into the
// product implies continuity of each projected component (the `→`
// direction).
// ---------------------------------------------------------------------------

/// `Metric.prod_fst_uniformly_continuous : ∀ M N,
/// Metric.UniformlyContinuous (Metric.prod M N) M (Metric.prod_fst M N)`.
///
/// Witness modulus `fun n => n` (the identity): `dist_prod x y ≤
/// rate(1,n)` already gives `M.dist (fst x)(fst y) ≤ rate(1,n)` via
/// `le_max_left` + `le_trans`, no rate change at all.
#[allow(clippy::too_many_lines)]
fn declare_projection_uniformly_continuous(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
    result_name: NameId,
    // `true` for `fst` (codomain `M`, `le_max_left`), `false` for `snd`
    // (codomain `N`, `le_max_right`).
    is_fst: bool,
) -> Result<(), KernelError> {
    let mn = mn_ambient(d, c, mp);
    let mty = metric_ty(d, mp);
    let nat = nat_ty(d);
    let prod_inst = d.const_app(names.prod, &[mn.m, mn.n]);
    let proj_inst = if is_fst {
        d.const_app(names.prod_fst, &[mn.m, mn.n])
    } else {
        d.const_app(names.prod_snd, &[mn.m, mn.n])
    };
    let codomain = if is_fst { mn.m } else { mn.n };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let fx = fst_of(d, &mn.pieces, x);
    let fy = fst_of(d, &mn.pieces, y);
    let sx = snd_of(d, &mn.pieces, x);
    let sy = snd_of(d, &mn.pieces, y);

    let m_dist = field(d, mp, mn.m, DIST);
    let n_dist = field(d, mp, mn.n, DIST);
    let dm = d.apply(m_dist, &[fx, fy]);
    let dn = d.apply(n_dist, &[sx, sy]);
    let d_proj = if is_fst { dm } else { dn };
    let dprod = rmax(d, c, dm, dn);

    let one_num = d.num(1);
    let rate_n = rate_at(d, c, one_num, n);
    let hyp_ty = rle(d, c, dprod, rate_n);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let d_proj_le_dprod = if is_fst {
        d.lemma(c.le_max_left, &[dm, dn])
    } else {
        d.lemma(c.le_max_right, &[dm, dn])
    };
    let concl = d.lemma(c.le_trans, &[d_proj, dprod, rate_n, d_proj_le_dprod, h]);

    let with_h = d.lam_fv(h_fv, hyp_ty, concl);
    let with_y = d.lam_fv(y_fv, mn.pieces.prod_carrier, with_h);
    let with_x = d.lam_fv(x_fv, mn.pieces.prod_carrier, with_y);
    let with_n = d.lam_fv(n_fv, nat, with_x);

    // `mu := fun n => n` — the identity modulus.
    let mu = {
        let n2_fv = d.fresh_fvar();
        let n2 = d.kernel().fvar(n2_fv);
        d.lam_fv(n2_fv, nat, n2)
    };
    let nat_to_nat = d.arrow(nat, nat);
    let uc_with_pred = {
        let mu_fv = d.fresh_fvar();
        let mu_var = d.kernel().fvar(mu_fv);
        let body = d.const_app(
            mp.continuity.uniformly_continuous_with,
            &[prod_inst, codomain, proj_inst, mu_var],
        );
        d.lam_fv(mu_fv, nat_to_nat, body)
    };
    let ex_proof = exists_intro(d, c, nat_to_nat, uc_with_pred, mu, with_n);

    let value = {
        let with_n2 = d.lam_fv(mn.n_fv, mty, ex_proof);
        d.lam_fv(mn.m_fv, mty, with_n2)
    };
    let ty = {
        let uc_ty = d.const_app(
            mp.continuity.uniformly_continuous,
            &[prod_inst, codomain, proj_inst],
        );
        let with_n2 = d.pi_fv(mn.n_fv, mty, uc_ty);
        d.pi_fv(mn.m_fv, mty, with_n2)
    };
    theorem(d, result_name, ty, value)
}

fn declare_prod_fst_uniformly_continuous(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    declare_projection_uniformly_continuous(
        d,
        c,
        mp,
        names,
        names.prod_fst_uniformly_continuous,
        true,
    )
}

fn declare_prod_snd_uniformly_continuous(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    declare_projection_uniformly_continuous(
        d,
        c,
        mp,
        names,
        names.prod_snd_uniformly_continuous,
        false,
    )
}

/// The `→` direction of "a map into the product is continuous iff both
/// components are": `Metric.prod_fst_continuous_of_continuous` /
/// `Metric.prod_snd_continuous_of_continuous`.
///
/// `∀ P M N G, Metric.Continuous P (Metric.prod M N) G →
///   Metric.Continuous P M (fun p => Metric.prod_fst M N (G p))`
/// (or `prod_snd`/`N`). Proved at the SAME modulus the hypothesis supplies —
/// composing with a projection is nonexpansive, so no rate change is needed,
/// exactly like [`declare_projection_uniformly_continuous`].
#[allow(clippy::too_many_lines)]
fn declare_continuous_comp(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
    result_name: NameId,
    is_fst: bool,
) -> Result<(), KernelError> {
    let mn = mn_ambient(d, c, mp);
    let mty = metric_ty(d, mp);
    let nat = nat_ty(d);
    // `ContinuousAtWith`'s modulus `k` is `Nat -> Nat` (it supplies the
    // DENOMINATOR argument `k n`), unlike `CauchyAt`/`TendsToAt`'s plain
    // `Nat` numerator -- the existential over it must range over
    // `Nat -> Nat`, not `Nat`.
    let nat_to_nat = d.arrow(nat, nat);
    let prod_inst = d.const_app(names.prod, &[mn.m, mn.n]);
    let proj_inst = if is_fst {
        d.const_app(names.prod_fst, &[mn.m, mn.n])
    } else {
        d.const_app(names.prod_snd, &[mn.m, mn.n])
    };
    let codomain = if is_fst { mn.m } else { mn.n };

    // `P`, the domain of `G`.
    let p_fv = d.fresh_fvar();
    let p_inst = d.kernel().fvar(p_fv);
    let p_carrier = field(d, mp, p_inst, CARRIER);

    // `G : P.carrier → (Metric.prod M N).carrier`.
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let g_ty = d.arrow(p_carrier, mn.pieces.prod_carrier);

    // `F := fun q => proj (G q)`, the projected map.
    let f_map = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let gq = d.apply(g, &[q]);
        let body = d.apply(proj_inst, &[gq]);
        d.lam_fv(q_fv, p_carrier, body)
    };

    // `hG : Metric.Continuous P (Metric.prod M N) G`.
    let hg_ty = d.const_app(mp.continuity.continuous, &[p_inst, prod_inst, g]);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    // The per-point body: `fun pt => <ContinuousAt P M F pt>`.
    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let hg_at_pt = d.apply(hg, &[pt]); // : ContinuousAt P (prod M N) G pt = ∃ k, ContinuousAtWith .. pt k

    let target_at_pt = {
        // `ContinuousAt P M F pt`.
        d.const_app(mp.continuity.continuous_at, &[p_inst, codomain, f_map, pt])
    };
    let at_with_pred_prod = {
        let k_fv = d.fresh_fvar();
        let k_var = d.kernel().fvar(k_fv);
        let body = d.const_app(
            mp.continuity.continuous_at_with,
            &[p_inst, prod_inst, g, pt, k_var],
        );
        d.lam_fv(k_fv, nat_to_nat, body)
    };

    let body_at_pt = exists_elim_build(
        d,
        c,
        nat_to_nat,
        at_with_pred_prod,
        target_at_pt,
        hg_at_pt,
        |d, k, hk| {
            // `hk : ContinuousAtWith P (prod M N) G pt k`; reuse `k` unchanged.
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);

            // `ContinuousAtWith`'s numerator is FIXED at 1; the modulus `k`
            // supplies the DENOMINATOR argument `k n`, not a numerator (unlike
            // `TendsToAt`/`CauchyAt`'s `K`). So the hypothesis bound is
            // `ofRat (natDivSucc 1 (k n))`, not `ofRat (natDivSucc k n)`.
            let p_dist = field(d, mp, p_inst, DIST);
            let d_py = d.apply(p_dist, &[pt, y]);
            let one_num_hyp = d.num(1);
            let k_n = d.apply(k, &[n]);
            let rate_kn = rate_at(d, c, one_num_hyp, k_n);
            let hyp_ty = rle(d, c, d_py, rate_kn);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let step1 = d.apply(hk, &[n, y, h]); // le (dist_prod (G pt) (G y)) (rate n)

            let gp = d.apply(g, &[pt]);
            let gy = d.apply(g, &[y]);
            let fpt = fst_of(d, &mn.pieces, gp);
            let fpy = fst_of(d, &mn.pieces, gy);
            let spt = snd_of(d, &mn.pieces, gp);
            let spy = snd_of(d, &mn.pieces, gy);
            let m_dist = field(d, mp, mn.m, DIST);
            let n_dist = field(d, mp, mn.n, DIST);
            let dm = d.apply(m_dist, &[fpt, fpy]);
            let dn = d.apply(n_dist, &[spt, spy]);
            let d_proj = if is_fst { dm } else { dn };
            let one_num = d.num(1);
            let rate_n = rate_at(d, c, one_num, n);
            let proj_le_prod = if is_fst {
                d.lemma(c.le_max_left, &[dm, dn])
            } else {
                d.lemma(c.le_max_right, &[dm, dn])
            };
            let dprod_gp_gy = rmax(d, c, dm, dn);
            let concl = d.lemma(
                c.le_trans,
                &[d_proj, dprod_gp_gy, rate_n, proj_le_prod, step1],
            );

            let with_h = d.lam_fv(h_fv, hyp_ty, concl);
            let with_y = d.lam_fv(y_fv, p_carrier, with_h);
            let with_n = d.lam_fv(n_fv, nat, with_y);

            let at_with_pred_target = {
                let k2_fv = d.fresh_fvar();
                let k2_var = d.kernel().fvar(k2_fv);
                let body = d.const_app(
                    mp.continuity.continuous_at_with,
                    &[p_inst, codomain, f_map, pt, k2_var],
                );
                d.lam_fv(k2_fv, nat_to_nat, body)
            };
            exists_intro(d, c, nat_to_nat, at_with_pred_target, k, with_n)
        },
    );

    let value = {
        let with_pt = d.lam_fv(pt_fv, p_carrier, body_at_pt);
        let with_hg = d.lam_fv(hg_fv, hg_ty, with_pt);
        let with_g = d.lam_fv(g_fv, g_ty, with_hg);
        let with_n2 = d.lam_fv(mn.n_fv, mty, with_g);
        let with_m2 = d.lam_fv(mn.m_fv, mty, with_n2);
        d.lam_fv(p_fv, mty, with_m2)
    };
    let ty = {
        let continuous_ty = d.const_app(mp.continuity.continuous, &[p_inst, codomain, f_map]);
        let claim = d.arrow(hg_ty, continuous_ty);
        let with_g = d.pi_fv(g_fv, g_ty, claim);
        let with_n2 = d.pi_fv(mn.n_fv, mty, with_g);
        let with_m2 = d.pi_fv(mn.m_fv, mty, with_n2);
        d.pi_fv(p_fv, mty, with_m2)
    };
    theorem(d, result_name, ty, value)
}

fn declare_prod_fst_continuous_of_continuous(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    declare_continuous_comp(
        d,
        c,
        mp,
        names,
        names.prod_fst_continuous_of_continuous,
        true,
    )
}

fn declare_prod_snd_continuous_of_continuous(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    declare_continuous_comp(
        d,
        c,
        mp,
        names,
        names.prod_snd_continuous_of_continuous,
        false,
    )
}

// ---------------------------------------------------------------------------
// Completeness transfer.
// ---------------------------------------------------------------------------

/// `Metric.prod_complete : ∀ M N, Metric.Complete M → Metric.Complete N →
/// Metric.Complete (Metric.prod M N)`.
///
/// The combined modulus `K1 + K2` (via `Rat.natDivSucc_le_add_left`, which
/// is monotone INCREASING in the numerator) stands in for "the max of the
/// two moduli" — see the module doc. The `N`-side bound needs one
/// `Nat.add_comm` rewrite (`K2 + K1 = K1 + K2`) to line up with the SAME
/// combined modulus the `M`-side bound already used.
#[allow(clippy::too_many_lines)]
fn declare_prod_complete(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    let mn = mn_ambient(d, c, mp);
    let mty = metric_ty(d, mp);
    let nat = nat_ty(d);
    let prod_inst = d.const_app(names.prod, &[mn.m, mn.n]);

    let hm_ty = d.const_app(mp.complete, &[mn.m]);
    let hm_fv = d.fresh_fvar();
    let hm = d.kernel().fvar(hm_fv);
    let hn_ty = d.const_app(mp.complete, &[mn.n]);
    let hn_fv = d.fresh_fvar();
    let hn = d.kernel().fvar(hn_fv);

    let seq_ty = d.arrow(nat, mn.pieces.prod_carrier);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let f1 = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = fst_of(d, &mn.pieces, fi);
        d.lam_fv(i_fv, nat, body)
    };
    let f2 = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = snd_of(d, &mn.pieces, fi);
        d.lam_fv(i_fv, nat, body)
    };

    let hf_ty = d.const_app(mp.cauchy, &[prod_inst, f]);
    let hf_fv = d.fresh_fvar();
    let hf = d.kernel().fvar(hf_fv);

    // The goal shared by every nested elimination.
    let target = {
        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let pred = {
            let inner = d.const_app(mp.tends_to, &[prod_inst, f, l]);
            d.lam_fv(l_fv, mn.pieces.prod_carrier, inner)
        };
        exists_ty(d, c, mn.pieces.prod_carrier, pred)
    };

    let cauchy_pred_prod = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(mp.cauchy_at, &[prod_inst, f, k]);
        d.lam_fv(k_fv, nat, body)
    };

    let body = exists_elim_build(d, c, nat, cauchy_pred_prod, target, hf, |d, k, hk| {
        // `hk : CauchyAt (prod M N) f K = ∀ m n, le (dist_prod (f m) (f n))
        //   (pair_rate K m n)`.
        let hk1 = {
            let m_fv = d.fresh_fvar();
            let mv = d.kernel().fvar(m_fv);
            let n_fv = d.fresh_fvar();
            let nv = d.kernel().fvar(n_fv);
            let fm = d.apply(f, &[mv]);
            let fn_ = d.apply(f, &[nv]);
            let dprod = {
                let m_dist = field(d, mp, mn.m, DIST);
                let n_dist = field(d, mp, mn.n, DIST);
                let fmv = fst_of(d, &mn.pieces, fm);
                let fnv = fst_of(d, &mn.pieces, fn_);
                let smv = snd_of(d, &mn.pieces, fm);
                let snv = snd_of(d, &mn.pieces, fn_);
                let dm = d.apply(m_dist, &[fmv, fnv]);
                let dn = d.apply(n_dist, &[smv, snv]);
                rmax(d, c, dm, dn)
            };
            let f1m = d.apply(f1, &[mv]);
            let f1n = d.apply(f1, &[nv]);
            let m_dist = field(d, mp, mn.m, DIST);
            let dm1 = d.apply(m_dist, &[f1m, f1n]);
            let n_dist_ = field(d, mp, mn.n, DIST);
            let dn1 = {
                let smv = snd_of(d, &mn.pieces, fm);
                let snv = snd_of(d, &mn.pieces, fn_);
                d.apply(n_dist_, &[smv, snv])
            };
            let le_m = d.lemma(c.le_max_left, &[dm1, dn1]);
            let bound = pair_rate_at(d, c, k, mv, nv);
            let hkmn = d.apply(hk, &[mv, nv]);
            let step = d.lemma(c.le_trans, &[dm1, dprod, bound, le_m, hkmn]);
            let with_n = d.lam_fv(n_fv, nat, step);
            d.lam_fv(m_fv, nat, with_n)
        };
        let hk2 = {
            let m_fv = d.fresh_fvar();
            let mv = d.kernel().fvar(m_fv);
            let n_fv = d.fresh_fvar();
            let nv = d.kernel().fvar(n_fv);
            let fm = d.apply(f, &[mv]);
            let fn_ = d.apply(f, &[nv]);
            let dprod = {
                let m_dist = field(d, mp, mn.m, DIST);
                let n_dist = field(d, mp, mn.n, DIST);
                let fmv = fst_of(d, &mn.pieces, fm);
                let fnv = fst_of(d, &mn.pieces, fn_);
                let smv = snd_of(d, &mn.pieces, fm);
                let snv = snd_of(d, &mn.pieces, fn_);
                let dm = d.apply(m_dist, &[fmv, fnv]);
                let dn = d.apply(n_dist, &[smv, snv]);
                rmax(d, c, dm, dn)
            };
            let f2m = d.apply(f2, &[mv]);
            let f2n = d.apply(f2, &[nv]);
            let n_dist = field(d, mp, mn.n, DIST);
            let dn2 = d.apply(n_dist, &[f2m, f2n]);
            let m_dist_ = field(d, mp, mn.m, DIST);
            let dm2 = {
                let fmv = fst_of(d, &mn.pieces, fm);
                let fnv = fst_of(d, &mn.pieces, fn_);
                d.apply(m_dist_, &[fmv, fnv])
            };
            let le_n = d.lemma(c.le_max_right, &[dm2, dn2]);
            let bound = pair_rate_at(d, c, k, mv, nv);
            let hkmn = d.apply(hk, &[mv, nv]);
            let step = d.lemma(c.le_trans, &[dn2, dprod, bound, le_n, hkmn]);
            let with_n = d.lam_fv(n_fv, nat, step);
            d.lam_fv(m_fv, nat, with_n)
        };

        let cauchy_pred_m = {
            let k2_fv = d.fresh_fvar();
            let k2 = d.kernel().fvar(k2_fv);
            let body = d.const_app(mp.cauchy_at, &[mn.m, f1, k2]);
            d.lam_fv(k2_fv, nat, body)
        };
        let cauchy_pred_n = {
            let k2_fv = d.fresh_fvar();
            let k2 = d.kernel().fvar(k2_fv);
            let body = d.const_app(mp.cauchy_at, &[mn.n, f2, k2]);
            d.lam_fv(k2_fv, nat, body)
        };
        let h_cauchy1 = exists_intro(d, c, nat, cauchy_pred_m, k, hk1);
        let h_cauchy2 = exists_intro(d, c, nat, cauchy_pred_n, k, hk2);

        let res1 = d.apply(hm, &[f1, h_cauchy1]); // : Exists M.carrier (TendsTo M f1)
        let tends_to_pred_m = {
            let l_fv = d.fresh_fvar();
            let l = d.kernel().fvar(l_fv);
            let body = d.const_app(mp.tends_to, &[mn.m, f1, l]);
            d.lam_fv(l_fv, mn.pieces.m_carrier, body)
        };

        exists_elim_build(
            d,
            c,
            mn.pieces.m_carrier,
            tends_to_pred_m,
            target,
            res1,
            |d, l1, hl1| {
                let tends_to_at_pred_m = {
                    let k2_fv = d.fresh_fvar();
                    let k2 = d.kernel().fvar(k2_fv);
                    let body = d.const_app(mp.tends_to_at, &[mn.m, f1, l1, k2]);
                    d.lam_fv(k2_fv, nat, body)
                };
                exists_elim_build(d, c, nat, tends_to_at_pred_m, target, hl1, |d, k1, hk1t| {
                    let res2 = d.apply(hn, &[f2, h_cauchy2]);
                    let tends_to_pred_n = {
                        let l_fv = d.fresh_fvar();
                        let l = d.kernel().fvar(l_fv);
                        let body = d.const_app(mp.tends_to, &[mn.n, f2, l]);
                        d.lam_fv(l_fv, mn.pieces.n_carrier, body)
                    };
                    exists_elim_build(
                        d,
                        c,
                        mn.pieces.n_carrier,
                        tends_to_pred_n,
                        target,
                        res2,
                        |d, l2, hl2| {
                            let tends_to_at_pred_n = {
                                let k2_fv = d.fresh_fvar();
                                let k2 = d.kernel().fvar(k2_fv);
                                let body = d.const_app(mp.tends_to_at, &[mn.n, f2, l2, k2]);
                                d.lam_fv(k2_fv, nat, body)
                            };
                            exists_elim_build(
                                d,
                                c,
                                nat,
                                tends_to_at_pred_n,
                                target,
                                hl2,
                                |d, k2, hk2t| {
                                    let l = mk_of(d, &mn.pieces, l1, l2);
                                    let kc = d.add(k1, k2);

                                    let n_fv = d.fresh_fvar();
                                    let nv = d.kernel().fvar(n_fv);

                                    // -- M-side bound at the combined modulus --
                                    let step_m = d.apply(hk1t, &[nv]);
                                    let f1n = d.apply(f1, &[nv]);
                                    let m_dist = field(d, mp, mn.m, DIST);
                                    let dm_bound = d.apply(m_dist, &[f1n, l1]);
                                    let rate_k1 = rate_at(d, c, k1, nv);
                                    let rate_kc = rate_at(d, c, kc, nv);
                                    let mono_m =
                                        d.lemma(c.rat.nat_div_succ_le_add_left, &[k1, k2, nv]);
                                    let nk1 = d.const_app(c.rat.nat_div_succ, &[k1, nv]);
                                    let nkc = d.const_app(c.rat.nat_div_succ, &[kc, nv]);
                                    let lift_m = d.lemma(c.of_rat_le, &[nk1, nkc, mono_m]);
                                    let bound_m = d.lemma(
                                        c.le_trans,
                                        &[dm_bound, rate_k1, rate_kc, step_m, lift_m],
                                    );

                                    // -- N-side bound: rewrite K2+K1 to K1+K2 first --
                                    let step_n = d.apply(hk2t, &[nv]);
                                    let f2n = d.apply(f2, &[nv]);
                                    let n_dist = field(d, mp, mn.n, DIST);
                                    let dn_bound = d.apply(n_dist, &[f2n, l2]);
                                    let rate_k2 = rate_at(d, c, k2, nv);
                                    let mono_n_raw =
                                        d.lemma(c.rat.nat_div_succ_le_add_left, &[k2, k1, nv]);
                                    let k21 = d.add(k2, k1);
                                    let nk2 = d.const_app(c.rat.nat_div_succ, &[k2, nv]);
                                    let add_comm_name = d.prelude().add_comm;
                                    let comm = d.lemma(add_comm_name, &[k2, k1]); // Eq Nat (k2+k1) (k1+k2)
                                    let motive = {
                                        // NOTE: this is a `Rat.le` motive (both
                                        // sides are `Rat.natDivSucc` values, not
                                        // yet lifted through `CReal.ofRat`) --
                                        // `c.rat.le`, not `c.le` (`CReal.le`).
                                        let motive_body = |dd: &mut IntDev<'_>, zz: ExprId| {
                                            let nkz = dd.const_app(c.rat.nat_div_succ, &[zz, nv]);
                                            dd.const_app(c.rat.le, &[nk2, nkz])
                                        };
                                        d.eq_motive(k21, &motive_body)
                                    };
                                    let mono_n = d.transport(k21, motive, mono_n_raw, kc, comm);
                                    let lift_n = d.lemma(c.of_rat_le, &[nk2, nkc, mono_n]);
                                    let bound_n = d.lemma(
                                        c.le_trans,
                                        &[dn_bound, rate_k2, rate_kc, step_n, lift_n],
                                    );

                                    let dist_prod_body = d.lemma(
                                        c.max_le,
                                        &[dm_bound, dn_bound, rate_kc, bound_m, bound_n],
                                    );

                                    let tends_to_at_body = d.lam_fv(n_fv, nat, dist_prod_body);
                                    let tends_to_at_pred_prod = {
                                        let k3_fv = d.fresh_fvar();
                                        let k3 = d.kernel().fvar(k3_fv);
                                        let body =
                                            d.const_app(mp.tends_to_at, &[prod_inst, f, l, k3]);
                                        d.lam_fv(k3_fv, nat, body)
                                    };
                                    let tends_to_proof = exists_intro(
                                        d,
                                        c,
                                        nat,
                                        tends_to_at_pred_prod,
                                        kc,
                                        tends_to_at_body,
                                    );
                                    let tends_to_pred_prod = {
                                        let l3_fv = d.fresh_fvar();
                                        let l3 = d.kernel().fvar(l3_fv);
                                        let body = d.const_app(mp.tends_to, &[prod_inst, f, l3]);
                                        d.lam_fv(l3_fv, mn.pieces.prod_carrier, body)
                                    };
                                    exists_intro(
                                        d,
                                        c,
                                        mn.pieces.prod_carrier,
                                        tends_to_pred_prod,
                                        l,
                                        tends_to_proof,
                                    )
                                },
                            )
                        },
                    )
                })
            },
        )
    });

    let value = {
        let with_hf = d.lam_fv(hf_fv, hf_ty, body);
        let with_f = d.lam_fv(f_fv, seq_ty, with_hf);
        let with_hn = d.lam_fv(hn_fv, hn_ty, with_f);
        let with_hm = d.lam_fv(hm_fv, hm_ty, with_hn);
        let with_n2 = d.lam_fv(mn.n_fv, mty, with_hm);
        d.lam_fv(mn.m_fv, mty, with_n2)
    };
    let ty = {
        let complete_prod = d.const_app(mp.complete, &[prod_inst]);
        let claim = d.arrow(hn_ty, complete_prod);
        let claim = d.arrow(hm_ty, claim);
        let with_n2 = d.pi_fv(mn.n_fv, mty, claim);
        d.pi_fv(mn.m_fv, mty, with_n2)
    };
    theorem(d, names.prod_complete, ty, value)
}

// ---------------------------------------------------------------------------
// `Metric.cpoint` related to `Metric.prod Metric.creal Metric.creal`.
//
// A CARRIER-level (setoid) equivalence, not an isometry — see the module
// doc for why: `Metric.cpoint`'s distance is Euclidean (`sqrt (distSq ..)`),
// `Metric.prod`'s is the max metric, and the two coincide only up to a
// bi-Lipschitz bound this round does not derive.
// ---------------------------------------------------------------------------

/// The `Sigma.{0,0}` pieces for `Metric.prod Metric.creal Metric.creal`
/// specifically (both factors the SAME concrete `Metric.creal` instance).
fn creal_creal_pieces(d: &mut IntDev<'_>, c: CRealPrelude, mp: MetricPrelude) -> ProdPieces {
    let creal_inst = d.kernel().const_(mp.creal_metric, vec![]);
    prod_pieces(d, c, mp, creal_inst, creal_inst)
}

/// `Metric.cpoint_of_prod : (Metric.prod Metric.creal Metric.creal).carrier
/// → CPoint := fun p => CPoint.mk (Sigma.fst .. p) (Sigma.snd .. p)`.
fn declare_cpoint_of_prod(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    cp: CPointPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    let pieces = creal_creal_pieces(d, c, mp);
    let point_ty = d.kernel().const_(cp.point, vec![]);

    let p_fv = d.fresh_fvar();
    let p = d.kernel().fvar(p_fv);
    let fp = fst_of(d, &pieces, p);
    let sp = snd_of(d, &pieces, p);
    let body = d.const_app(cp.mk, &[fp, sp]);

    let value = d.lam_fv(p_fv, pieces.prod_carrier, body);
    let ty = d.arrow(pieces.prod_carrier, point_ty);
    definition(d, names.cpoint_of_prod, ty, value)
}

/// `Metric.prod_of_cpoint : CPoint → (Metric.prod Metric.creal
/// Metric.creal).carrier := fun P => Sigma.mk .. (CPoint.x P) (CPoint.y P)`.
fn declare_prod_of_cpoint(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    cp: CPointPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    let pieces = creal_creal_pieces(d, c, mp);
    let point_ty = d.kernel().const_(cp.point, vec![]);

    let pt_fv = d.fresh_fvar();
    let pt = d.kernel().fvar(pt_fv);
    let px = d.const_app(cp.x, &[pt]);
    let py = d.const_app(cp.y, &[pt]);
    let body = mk_of(d, &pieces, px, py);

    let value = d.lam_fv(pt_fv, point_ty, body);
    let ty = d.arrow(point_ty, pieces.prod_carrier);
    definition(d, names.prod_of_cpoint, ty, value)
}

/// `Metric.prod_of_cpoint_of_prod : ∀ p,
/// (Metric.prod Metric.creal Metric.creal).equiv
///   (Metric.prod_of_cpoint (Metric.cpoint_of_prod p)) p`.
///
/// Cheap: `cpoint_of_prod p` is a literal `CPoint.mk`, so `CPoint.x`/`.y`
/// ι-reduce on it; `prod_of_cpoint` of THAT is a literal `Sigma.mk`, so
/// `Sigma.fst`/`.snd` ι-reduce again, landing exactly on `fst p`/`snd p` —
/// two reflexivity proofs, `And.intro`d.
fn declare_prod_of_cpoint_of_prod(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    _cp: CPointPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    let pieces = creal_creal_pieces(d, c, mp);
    let creal_inst = d.kernel().const_(mp.creal_metric, vec![]);
    let prod_inst = d.const_app(names.prod, &[creal_inst, creal_inst]);

    let p_fv = d.fresh_fvar();
    let p = d.kernel().fvar(p_fv);
    let fp = fst_of(d, &pieces, p);
    let sp = snd_of(d, &pieces, p);

    let cpoint_of_prod_p = d.const_app(names.cpoint_of_prod, &[p]);
    let lhs_pt = d.const_app(names.prod_of_cpoint, &[cpoint_of_prod_p]);

    let refl_fst = d.lemma(c.equiv_refl, &[fp]);
    let refl_snd = d.lemma(c.equiv_refl, &[sp]);
    let concl_l = req(d, c, fp, fp);
    let concl_r = req(d, c, sp, sp);
    let intro = d.int().logic.and_intro;
    let body = d.const_app(intro, &[concl_l, concl_r, refl_fst, refl_snd]);

    let value = d.lam_fv(p_fv, pieces.prod_carrier, body);
    let ty = {
        let equiv_applied = field(d, mp, prod_inst, EQUIV);
        let stmt = d.apply(equiv_applied, &[lhs_pt, p]);
        d.pi_fv(p_fv, pieces.prod_carrier, stmt)
    };
    theorem(d, names.prod_of_cpoint_of_prod, ty, value)
}

/// `Metric.cpoint_of_prod_of_cpoint : ∀ P,
/// CPoint.Equiv (Metric.cpoint_of_prod (Metric.prod_of_cpoint P)) P`.
///
/// Needs `CPoint.rec`: for an ARBITRARY (bound-variable) `P`, `CPoint.x P`/
/// `.y P` are stuck (no ι-reduction on a variable), so the round trip is not
/// definitional the way [`declare_prod_of_cpoint_of_prod`]'s is. Case
/// analysis on `P` via `CPoint.rec` reduces it to the literal-constructor
/// case, where both selector chains DO ι-reduce, landing on `CPoint.mk a b ~
/// CPoint.mk a b` — `Metric.cpoint_equiv_refl`.
fn declare_cpoint_of_prod_of_cpoint(
    d: &mut IntDev<'_>,
    c: CRealPrelude,
    cp: CPointPrelude,
    mp: MetricPrelude,
    names: MetricProdNames,
) -> Result<(), KernelError> {
    let point_ty = d.kernel().const_(cp.point, vec![]);
    let creal_ty = rty(d, c);
    let zero = d.kernel().level_zero();

    // `motive := fun t => CPoint.Equiv (cpoint_of_prod (prod_of_cpoint t)) t`.
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let prod_of_cpoint_t = d.const_app(names.prod_of_cpoint, &[t]);
    let cpoint_of_prod_of_t = d.const_app(names.cpoint_of_prod, &[prod_of_cpoint_t]);
    let equiv_stmt = d.const_app(cp.point_equiv, &[cpoint_of_prod_of_t, t]);
    let motive = d.lam_fv(t_fv, point_ty, equiv_stmt);

    // `minor := fun (a b : CReal) =>
    //   Metric.cpoint_equiv_refl (CPoint.mk a b)`.
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let mk_ab = d.const_app(cp.mk, &[a, b]);
    let proof_body = d.lemma(mp.cpoint_equiv_refl, &[mk_ab]);
    let minor = {
        let with_b = d.lam_fv(b_fv, creal_ty, proof_body);
        d.lam_fv(a_fv, creal_ty, with_b)
    };

    let p2_fv = d.fresh_fvar();
    let p2 = d.kernel().fvar(p2_fv);
    let rec = d.kernel().const_(cp.rec, vec![zero]);
    let body = d.apply(rec, &[motive, minor, p2]);
    let value = d.lam_fv(p2_fv, point_ty, body);

    let ty = {
        let prod_of_cpoint_p2 = d.const_app(names.prod_of_cpoint, &[p2]);
        let cpoint_of_prod_of_p2 = d.const_app(names.cpoint_of_prod, &[prod_of_cpoint_p2]);
        let stmt = d.const_app(cp.point_equiv, &[cpoint_of_prod_of_p2, p2]);
        d.pi_fv(p2_fv, point_ty, stmt)
    };
    theorem(d, names.cpoint_of_prod_of_cpoint, ty, value)
}
