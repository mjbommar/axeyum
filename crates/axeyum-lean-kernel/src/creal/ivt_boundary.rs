//! **The Intermediate Value Theorem's boundary certificate** (ADR-0603 row 2,
//! Spivak *Calculus* ch. 7 "Three Hard Theorems") — a machine-checked
//! reduction showing that an *exact* root, for a uniformly continuous family
//! on `[0, 1]` whose endpoint signs are proved rather than assumed, decides an
//! order question this development states outright that it cannot decide.
//!
//! ## What this file replaces
//!
//! `creal/ivt.rs`'s module documentation carried IVT's row-2 claim as prose:
//!
//! > Classical IVT (`f` continuous on `[a,b]`, `f a ≤ 0 ≤ f b` ⟹ `∃ x, f x =
//! > 0`) asserts a *computable* root, and no algorithm produces one in
//! > general: deciding which side of the root a candidate point falls on is
//! > exactly as hard as deciding the sign of an arbitrary real.
//!
//! That sentence is right, and until this file it was the whole of IVT's row
//! 2 at the *statement* level. What `ivt.rs` additionally carries — two
//! kernel-verified counterexamples on `F := id` over `[-1, 2]` — is **not a
//! weaker version of this**; it is a different and complementary claim, about
//! two specific bisection *construction routes* rather than about the
//! classical conclusion. Nothing there is changed, weakened or relabelled by
//! this file: `ivt.rs` answers "do these algorithms converge to the root?"
//! (no), and this file answers "what does the classical conclusion cost?".
//!
//! [`CReal.evt_attained_max_decides_sign`](super::ExtremeValueNames::evt_attained_max_decides_sign)
//! is the structural model — `creal/extreme_value.rs`, ADR-0603 row 2 for the
//! Extreme Value Theorem — and this file follows it deliberately, down to the
//! shape of the proof (one [`CReal.lt_cotrans`](super::CRealPrelude::lt_cotrans)
//! call on the fixed, always-strict pair
//! [`CReal.zero_lt_one`](super::CRealPrelude::zero_lt_one), then one more
//! inside each branch).
//!
//! ## The family, and why this one
//!
//! ```text
//! CReal.ivtPlateau v := fun x => CReal.min x (CReal.max (x + (−1)) v)
//! ```
//!
//! on `[0, 1]`. Read it as the **clamp of `v` into the unit-width window
//! `[x − 1, x]`**: `max (x − 1) v` lifts `v` to the window's floor, `min x`
//! caps it at the window's ceiling. Classically, then, the graph is the ramp
//! `x ↦ x` while the window sits below `v`, the horizontal **plateau**
//! `x ↦ v` while the window straddles `v`, and the ramp `x ↦ x − 1` once
//! the window has passed above it:
//!
//! | `v` | value on `[0, 1]` | root |
//! | --- | --- | --- |
//! | `0 < v` | `x` on `[0, v]`, then the plateau `v > 0` | unique, at `x = 0` |
//! | `v < 0` | the plateau `v < 0`, then `x − 1` on `[v + 1, 1]` | unique, at `x = 1` |
//! | `v = 0` | identically `0` | every `x ∈ [0, 1]` |
//!
//! So the root sits at the LEFT endpoint exactly when `v ≥ 0` and at the
//! RIGHT endpoint exactly when `v ≤ 0`.
//!
//! **Which end of the interval the root sits at is precisely the sign of
//! `v`**, and that is the whole content of the counterexample: a root is not
//! merely a real number, it is a real number whose *position* answers a
//! question about `v`. A plateau is what forces this, and it is why no
//! polynomial family could serve — constructive IVT *is* available for
//! polynomials, and the two lattice operations are exactly what takes this
//! family outside that fragment.
//!
//! ## Both IVT hypotheses are PROVED here, not assumed
//!
//! Classical IVT applies to `f` continuous on `[a, b]` with `f a ≤ 0 ≤ f b`.
//! All three obligations are kernel declarations in this file, so the family
//! is machine-checked to lie inside classical IVT's hypothesis class rather
//! than asserted to:
//!
//! - [`CReal.ivtPlateau_nonpos_at_zero`](IvtBoundaryNames::ivt_plateau_nonpos_at_zero)
//!   `: ∀ v, le (ivtPlateau v zero) zero`. One
//!   [`CReal.min_le_left`](super::CRealPrelude::min_le_left) — the whole point
//!   of putting the window's ceiling at `x` is that the left endpoint's value
//!   is `min zero _`, nonpositive by the meet's own universal property, with
//!   **no case split and no condition on `v`**.
//! - [`CReal.ivtPlateau_nonneg_at_one`](IvtBoundaryNames::ivt_plateau_nonneg_at_one)
//!   `: ∀ v, le zero (ivtPlateau v one)`. One
//!   [`CReal.le_min`](super::CRealPrelude::le_min) against `0 ≤ 1` and
//!   `0 ≤ max (1 + (−1)) v`, the latter being
//!   [`CReal.le_max_left`](super::CRealPrelude::le_max_left) transported
//!   across `add_neg`. Again unconditional in `v`.
//! - [`CReal.ivtPlateau_uniformly_continuous`](IvtBoundaryNames::ivt_plateau_uniformly_continuous)
//!   `: ∀ v, UniformlyContinuousOn (ivtPlateau v) zero one`. Pure assembly,
//!   once the lattice closure lemmas below exist.
//!
//! ## The lattice is uniformly-continuity-closed, and that is new
//!
//! [`CReal.uniformly_continuous_max`](IvtBoundaryNames::uniformly_continuous_max)
//! and [`CReal.uniformly_continuous_min`](IvtBoundaryNames::uniformly_continuous_min)
//! are declared here because this file is their first consumer, and they are
//! general: `∀ F G a b, UC F a b → UC G a b → UC (fun r => max (F r) (G r)) a
//! b`, and the same for `min`. They are the lattice's entries in the same
//! closure table `uniformly_continuous_add`/`_neg`/`_sub`/`_mul` already fill
//! for the ring operations.
//!
//! The combined modulus is `mF n + mG n` — `Nat.add` rather than a `Nat.max`
//! this development does not have, unblocked by
//! [`Rat.natDivSucc_antitone`](crate::RatPrelude::nat_div_succ_antitone),
//! exactly as `uniformly_continuous_add` does it. Unlike `add`, there is **no
//! index shift**: `max`/`min` are one-Lipschitz *jointly* (see
//! `creal/lattice.rs`, `Rat.sub_max_le`), so both specs are consulted at the
//! caller's own accuracy `n` and no `1/(2n+2)` halving argument is needed.
//!
//! The estimate itself, for `max`: split each hypothesis with
//! [`CReal.two_sided_of_abs_sub_le`](super::CRealPrelude::two_sided_of_abs_sub_le)
//! into `F x ≤ F y + q` and `F y ≤ F x + q`, then
//! [`CReal.max_le`](super::CRealPrelude::max_le) reduces
//! `max (F x) (G x) ≤ max (F y) (G y) + q` to the two one-sided bounds via
//! [`CReal.le_max_left`](super::CRealPrelude::le_max_left)/`_right`, and
//! [`CReal.abs_le_of_two_sided`](super::CRealPrelude::abs_le_of_two_sided)
//! rebuilds the `close_within` shape. For `min` the same route does **not**
//! transcribe: `min` is on the LEFT of the goal, so `le_min` would need the
//! RIGHT to be a meet, and `min (F y) (G y) + q` is not one. The fix is to
//! move `q` across first — prove `min (F x) (G x) + (−q) ≤ min (F y) (G y)`
//! by `le_min`, then shift back — which is why this file carries the two
//! small `((x + a) + b) ≈ x` cancellation helpers and the `max` half does
//! not.
//!
//! ## The statement
//!
//! ```text
//! CReal.ivt_exact_root_decides_sign : ∀ v c,
//!   le zero c → le c one →
//!   Equiv (min c (max (add c (neg one)) v)) zero →
//!   Or (le v zero) (le zero v)
//! ```
//!
//! The root hypothesis is written out rather than folded through
//! `ivtPlateau`, so the theorem is legible without unfolding a definition —
//! the same choice `evt_attained_max_decides_sign` makes in writing `mul t v`
//! rather than `evtLinear v t`. The two are definitionally equal; that is
//! pinned by `creal_tests::ivt_plateau_is_the_clamp_the_row_two_theorem_uses`.
//!
//! The conclusion `∀ v, v ≤ 0 ∨ 0 ≤ v` is *analytic LLPO* — equivalently the
//! total order `le_total` on `CReal`, which
//! [`creal/cotransitivity.rs`](super::cotransitivity)'s own module
//! documentation states verbatim is "not decidable and **no `lt_total` is
//! assumed or provable over `CReal`**". So an *operator* `root : CReal →
//! CReal` returning an exact root of `ivtPlateau v` for every `v` — which is
//! what the classical conclusion, read constructively, asserts — would
//! discharge the hypothesis at every `v` at once and hand back the comparison
//! the order deliberately lacks. That is the boundary, proved rather than
//! asserted, and it is what makes
//! [`CReal.ivt_approx`](super::CRealPrelude::ivt_approx) — an *approximate*
//! root, `|F x| ≤ ε` per accuracy — optimal rather than merely unimproved.
//!
//! ## The proof, on paper
//!
//! Write `a := c + (−1)` (the window's floor at `c`), `w := max a v`, so the
//! root hypothesis is `min c w ≈ 0`. Two consequences are free and
//! unconditional, straight off the meet's projections:
//!
//! - `min c w ≤ c`, hence **`0 ≤ c`** — the root is at or right of the
//!   window's own zero.
//! - `min c w ≤ w`, hence **`0 ≤ w`**.
//!
//! One [`CReal.lt_cotrans`](super::CRealPrelude::lt_cotrans) call on the
//! fixed, always-strict pair `zero < one`
//! ([`CReal.zero_lt_one`](super::CRealPrelude::zero_lt_one)) at `z := c`
//! gives `Or (lt zero c) (lt c one)`, unconditionally. Each branch then makes
//! ONE more cotransitivity call, and both of its cases land a disjunct:
//!
//! - **`0 < c`.** Cotransitivity of `0 < c` at `z := v` gives
//!   `Or (lt zero v) (lt v c)`.
//!   - `0 < v` is the right disjunct outright.
//!   - `v < c`: with `a ≤ c` (that is `c + (−1) ≤ c + 0 ≈ c`),
//!     [`CReal.max_le`](super::CRealPrelude::max_le) gives `w ≤ c`, so
//!     [`CReal.le_min`](super::CRealPrelude::le_min) gives `w ≤ min c w` and
//!     antisymmetry gives `w ≈ min c w ≈ 0`. Then `v ≤ w ≈ 0` by
//!     [`CReal.le_max_right`](super::CRealPrelude::le_max_right) — the left
//!     disjunct.
//! - **`c < 1`.** Then `a = c + (−1) < 0` (add `−1` to both sides and
//!   transport `(−1) + 1 ≈ 0`, the same manoeuvre
//!   `evt_attained_max_decides_sign`'s own second branch makes).
//!   Cotransitivity of `a < 0` at `z := v` gives `Or (lt a v) (lt v zero)`.
//!   - `v < 0` is the left disjunct outright.
//!   - `a < v`: `max_le` gives `w ≤ v` and `le_max_right` gives `v ≤ w`, so
//!     `w ≈ v`; with `0 ≤ w` from above, `0 ≤ v` — the right disjunct.
//!
//! Note what the proof does **not** use: neither `le zero c` nor `le c one`
//! is consumed anywhere. They are kept in the statement because IVT's own
//! conclusion supplies them — a faithful hypothesis, not a needed one — and
//! their being unnecessary strengthens the reduction: the root need not even
//! be known to lie in the interval for the decision to fall out. The same is
//! true of `evt_attained_max_decides_sign`'s two interval hypotheses, and for
//! the same reason.
//!
//! ## Honest scope — what this is NOT
//!
//! This is **not** a proof that `∀ v, Or (le v zero) (le zero v)` is FALSE,
//! and no such proof is available: analytic LLPO is consistent with Bishop's
//! constructive mathematics, so it is *unprovable here*, not refutable.
//! ADR-0603 calls this row "boundary refutation"; that name is looser than
//! what is proved. What "refuted" means, precisely: **the classical
//! conclusion is proved at least as strong as a decision principle this
//! kernel demonstrably does not have.** That is a machine-checked statement
//! about the boundary, and it is falsifiable — if someone lands `lt_total`
//! over `CReal`, this theorem stops being a refutation and becomes a route to
//! IVT.
//!
//! Nor does it say anything against
//! [`CReal.ivt_exact_root`](super::CRealPrelude::ivt_exact_root), which
//! *does* produce an exact root. That theorem carries a uniformly positive
//! derivative hypothesis, and `ivtPlateau v` has a plateau — derivative `0`
//! on an interval of positive length whenever the plateau is inside `[0, 1]`
//! — so it is exactly the shape that hypothesis excludes. The two results
//! bound the constructive fragment from opposite sides.

#![allow(clippy::too_many_lines, clippy::many_single_char_names)]

use super::{CRealPrelude, cadd, cle, clt, creal_ty};
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::nat_rewrite_prop;

/// This module's own name registry — ADR-1512's first migration out of the
/// `CRealPrelude` god-struct.
///
/// Reached as `p.ivt_boundary.<name>`. It lives here rather than in
/// `creal.rs` so that adding a declaration to this file touches **this file
/// only**: the field, its documentation, and its interning are all beside the
/// `declare_*` that uses them.
///
/// The measurement behind the split
/// (`docs/research/11-design-review/2026-09-01-creal-declare-deps-measured.md`):
/// `CRealPrelude` had grown from 441 fields to 606 in five days, and nothing
/// in this module's seven names is read by any other module — which is what
/// makes the move local rather than a cross-module rename.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IvtBoundaryNames {
    /// `CReal.uniformly_continuous_max : forall F G a b,
    /// UniformlyContinuousOn F a b -> UniformlyContinuousOn G a b ->
    /// UniformlyContinuousOn (fun r => max (F r) (G r)) a b` -- the lattice's
    /// entry in the same closure table
    /// [`uniformly_continuous_add`](super::CRealPrelude::uniformly_continuous_add)/`_neg`/`_sub`/`_mul`
    /// fill for the ring operations. Combined modulus `mF n + mG n`, and
    /// unlike `add` there is **no index shift**: `max` is one-Lipschitz
    /// JOINTLY in both arguments (`creal/lattice.rs`, `Rat.sub_max_le`), so
    /// both specs are consulted at the caller's own accuracy `n`. Declared
    /// here because this file is its first consumer.
    pub uniformly_continuous_max: NameId,
    /// `CReal.uniformly_continuous_min` -- the same for the meet, and NOT a
    /// transcription of [`Self::uniformly_continuous_max`]'s proof: `min`
    /// sits on the LEFT of the goal, so
    /// [`le_min`](super::CRealPrelude::le_min) would need the RIGHT to be a
    /// meet and `min (G x) (G y) + q` is not one. It moves `q` across first.
    pub uniformly_continuous_min: NameId,
    /// `CReal.ivtPlateau : CReal -> CReal -> CReal :=
    /// fun v x => min x (max (add x (neg one)) v)` -- the IVT counterexample
    /// family, the **clamp of `v` into the unit-width window `[x-1, x]`**.
    /// Classically a ramp, then a horizontal PLATEAU at height `v`, then a
    /// ramp: the root sits at the left endpoint exactly when `v >= 0` and at
    /// the right endpoint exactly when `v <= 0`, so *which end attains it* IS
    /// the sign of `v`.
    ///
    /// A plateau is what forces this, which is why no polynomial family could
    /// serve -- constructive IVT IS available for polynomials, and the two
    /// lattice operations are exactly what takes this family outside that
    /// fragment.
    pub ivt_plateau: NameId,
    /// `CReal.ivtPlateau_nonpos_at_zero : forall v,
    /// le (ivtPlateau v zero) zero` -- IVT's left-endpoint sign condition,
    /// proved and unconditional in `v`: one
    /// [`min_le_left`](super::CRealPrelude::min_le_left), since the window's
    /// ceiling at `x` makes the left endpoint's value `min zero _`.
    pub ivt_plateau_nonpos_at_zero: NameId,
    /// `CReal.ivtPlateau_nonneg_at_one : forall v,
    /// le zero (ivtPlateau v one)` -- IVT's right-endpoint sign condition,
    /// also unconditional in `v`: one
    /// [`le_min`](super::CRealPrelude::le_min) against `0 <= 1` and
    /// [`le_max_left`](super::CRealPrelude::le_max_left) transported across
    /// `add_neg`.
    pub ivt_plateau_nonneg_at_one: NameId,
    /// `CReal.ivtPlateau_uniformly_continuous : forall v,
    /// UniformlyContinuousOn (ivtPlateau v) zero one` -- the third and last
    /// of classical IVT's hypotheses, **proved rather than asserted**, so the
    /// counterexample family is machine-checked to lie inside IVT's
    /// hypothesis class. Pure assembly over
    /// [`Self::uniformly_continuous_min`], [`Self::uniformly_continuous_max`],
    /// [`uniformly_continuous_add`](super::CRealPrelude::uniformly_continuous_add),
    /// [`uniformly_continuous_id`](super::CRealPrelude::uniformly_continuous_id)
    /// and
    /// [`uniformly_continuous_const`](super::CRealPrelude::uniformly_continuous_const).
    pub ivt_plateau_uniformly_continuous: NameId,
    /// `CReal.ivt_exact_root_decides_sign : forall v c, le zero c ->
    /// le c one -> Equiv (min c (max (add c (neg one)) v)) zero ->
    /// Or (le v zero) (le zero v)` --
    /// **ADR-0603 row 2 for the Intermediate Value Theorem**, machine-checked
    /// rather than asserted.
    ///
    /// An *exact* root of [`Self::ivt_plateau`] on `[0, 1]` yields
    /// `v <= 0` or `0 <= v` for an ARBITRARY real -- analytic LLPO,
    /// equivalently the total order `le_total` that
    /// `creal/cotransitivity.rs`'s module documentation states is neither
    /// assumed nor provable here. So an operator handing back a root for
    /// every `v` would hand back the comparison the order deliberately lacks,
    /// which is what makes [`ivt_approx`](super::CRealPrelude::ivt_approx) --
    /// an APPROXIMATE root, `|F x| <= e` per accuracy -- optimal rather than
    /// merely unimproved.
    ///
    /// One [`lt_cotrans`](super::CRealPrelude::lt_cotrans) call on the fixed
    /// strict pair [`zero_lt_one`](super::CRealPrelude::zero_lt_one) at
    /// `z := c`, then one more inside each branch (at `z := v`), with the
    /// meet's own projections supplying `0 <= c` and `0 <= max (c + (-1)) v`
    /// for free. Both interval hypotheses are faithful but UNUSED, exactly as
    /// in
    /// [`evt_attained_max_decides_sign`](super::ExtremeValueNames::evt_attained_max_decides_sign).
    ///
    /// This does NOT contradict
    /// [`ivt_exact_root`](super::CRealPrelude::ivt_exact_root), which does
    /// produce an exact root: that theorem carries a uniformly positive
    /// derivative hypothesis, and a plateau is precisely the shape it
    /// excludes. See this module's "Honest scope" section: this proves the
    /// classical conclusion at least as strong as a decision principle this
    /// kernel does not have, NOT that the principle is false (it is
    /// consistent, hence unprovable here rather than refutable).
    pub ivt_exact_root_decides_sign: NameId,
}

impl IvtBoundaryNames {
    /// Interns this module's names under the `CReal` root.
    ///
    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel
    /// spelling of each name now sits in the file that declares it, so a
    /// rename is one edit rather than two files apart.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            uniformly_continuous_max: kernel.name_str(creal, "uniformly_continuous_max"),
            uniformly_continuous_min: kernel.name_str(creal, "uniformly_continuous_min"),
            ivt_plateau: kernel.name_str(creal, "ivtPlateau"),
            ivt_plateau_nonpos_at_zero: kernel.name_str(creal, "ivtPlateau_nonpos_at_zero"),
            ivt_plateau_nonneg_at_one: kernel.name_str(creal, "ivtPlateau_nonneg_at_one"),
            ivt_plateau_uniformly_continuous: kernel
                .name_str(creal, "ivtPlateau_uniformly_continuous"),
            ivt_exact_root_decides_sign: kernel.name_str(creal, "ivt_exact_root_decides_sign"),
        }
    }
}

/// Admit this file's seven declarations, in dependency order.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_ivt_boundary(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_uniformly_continuous_lattice(d, p, true)?;
    declare_uniformly_continuous_lattice(d, p, false)?;
    declare_ivt_plateau(d, p)?;
    declare_ivt_plateau_nonpos_at_zero(d, p)?;
    declare_ivt_plateau_nonneg_at_one(d, p)?;
    declare_ivt_plateau_uniformly_continuous(d, p)?;
    declare_ivt_exact_root_decides_sign(d, p)
}

// --- shared term builders ----------------------------------------------------

/// `CReal.neg x`.
fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

/// `CReal → CReal`.
fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

/// `Rat.natDivSucc k j`, with a literal numerator `k`.
fn div_succ(d: &mut IntDev<'_>, p: CRealPrelude, k: u32, j: ExprId) -> ExprId {
    let numerator = d.num(k);
    d.const_app(p.rat.nat_div_succ, &[numerator, j])
}

/// `CReal.UniformlyContinuousOn F a b`.
fn uc_ty(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.uniformly_continuous_on, &[f, a, b])
}

/// `CReal.le (CReal.abs (CReal.add x (CReal.neg y))) (CReal.ofRat q)` —
/// `|x − y| ≤ q`. A local copy of `uniform_continuity.rs`'s private
/// `close_within` (private there; this crate duplicates small term builders
/// rather than widening a helper's visibility for one caller).
fn close_within(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, q: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny);
    let magnitude = d.const_app(p.abs, &[diff]);
    let target = d.const_app(p.of_rat, &[q]);
    d.const_app(p.le, &[magnitude, target])
}

/// Chain `Equiv start …` through `(next, step)` pairs. Local restatement of
/// the identical helper private to `extreme_value.rs`/`series.rs`/
/// `uniform_continuity.rs`.
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

/// `Equiv (add (add x a) b) x`, given `inner : Equiv (add a b) zero`.
///
/// `add_assoc` to `x + (a + b)`, `add_congr` with `inner` to `x + 0`, then
/// `add_zero`. Both cancellation helpers below are this one instantiated.
fn add_shift_cancel(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    a: ExprId,
    b: ExprId,
    inner: ExprId,
) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let xa = cadd(d, p, x, a);
    let lhs = cadd(d, p, xa, b);
    let ab = cadd(d, p, a, b);
    let x_ab = cadd(d, p, x, ab);
    let assoc = d.lemma(p.add_assoc, &[x, a, b]);
    let refl_x = d.lemma(p.equiv_refl, &[x]);
    let step = d.lemma(p.add_congr, &[x, x, ab, zero, refl_x, inner]);
    let x_zero = cadd(d, p, x, zero);
    let collapse = d.lemma(p.add_zero, &[x]);
    echain(d, p, lhs, &[(x_ab, assoc), (x_zero, step), (x, collapse)])
}

/// `Equiv (add (add x q) (neg q)) x` — add then subtract.
fn add_then_sub_cancel(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, q: ExprId) -> ExprId {
    let inner = d.lemma(p.add_neg, &[q]);
    let nq = cneg(d, p, q);
    add_shift_cancel(d, p, x, q, nq, inner)
}

/// `Equiv (add (add x (neg q)) q) x` — subtract then add.
fn sub_then_add_cancel(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, q: ExprId) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let nq = cneg(d, p, q);
    let nq_q = cadd(d, p, nq, q);
    let q_nq = cadd(d, p, q, nq);
    let comm = d.lemma(p.add_comm, &[nq, q]);
    let cancel = d.lemma(p.add_neg, &[q]);
    let inner = d.lemma(p.equiv_trans, &[nq_q, q_nq, zero, comm, cancel]);
    add_shift_cancel(d, p, x, nq, q, inner)
}

// --- the lattice closure lemmas ---------------------------------------------

/// `CReal.uniformly_continuous_max : ∀ F G a b, UniformlyContinuousOn F a b →
/// UniformlyContinuousOn G a b → UniformlyContinuousOn (fun r => max (F r)
/// (G r)) a b`, and (`join = false`) the same for `min` — this file's module
/// documentation has the modulus and the estimate.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_uniformly_continuous_lattice(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    join: bool,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let func_ty = fn_ty(d, p);
    let nat = d.nat_ty();
    let op = if join { p.max } else { p.min };
    let name = if join {
        p.ivt_boundary.uniformly_continuous_max
    } else {
        p.ivt_boundary.uniformly_continuous_min
    };

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let huc_f_ty = uc_ty(d, p, f, a, b);
    let huc_f_fv = d.fresh_fvar();
    let huc_f = d.kernel().fvar(huc_f_fv);
    let huc_g_ty = uc_ty(d, p, g, a, b);
    let huc_g_fv = d.fresh_fvar();
    let huc_g = d.kernel().fvar(huc_g_fv);

    let combined_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let fr = d.apply(f, &[r]);
        let gr = d.apply(g, &[r]);
        let joined = d.const_app(op, &[fr, gr]);
        d.lam_fv(r_fv, carrier, joined)
    };

    let mf = d.const_app(p.uc_modulus, &[f, a, b, huc_f]);
    let mg = d.const_app(p.uc_modulus, &[g, a, b, huc_g]);

    // `modulus n := mF n + mG n` — no index shift: `max`/`min` are jointly
    // one-Lipschitz, so neither spec is consulted at a finer accuracy.
    let modulus = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let mf_n = d.apply(mf, &[n]);
        let mg_n = d.apply(mg, &[n]);
        let sum = d.add(mf_n, mg_n);
        d.lam_fv(n_fv, nat, sum)
    };

    let spec = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let hax_fv = d.fresh_fvar();
        let hxb_fv = d.fresh_fvar();
        let hay_fv = d.fresh_fvar();
        let hyb_fv = d.fresh_fvar();
        let h_fv = d.fresh_fvar();

        let range_ax = d.const_app(p.le, &[a, x]);
        let range_xb = d.const_app(p.le, &[x, b]);
        let range_ay = d.const_app(p.le, &[a, y]);
        let range_yb = d.const_app(p.le, &[y, b]);
        let hax = d.kernel().fvar(hax_fv);
        let hxb = d.kernel().fvar(hxb_fv);
        let hay = d.kernel().fvar(hay_fv);
        let hyb = d.kernel().fvar(hyb_fv);

        let mf_n = d.apply(mf, &[n]);
        let mg_n = d.apply(mg, &[n]);
        let combined = d.add(mf_n, mg_n);

        let mod_n = d.apply(modulus, &[n]);
        let in_bound = div_succ(d, p, 1, mod_n);
        let hyp = close_within(d, p, x, y, in_bound);
        let h = d.kernel().fvar(h_fv);

        // Read the combined-modulus hypothesis back down to F's and G's own.
        let mg_plus_mf = d.add(mg_n, mf_n);
        let nat_p = p.rat.int.nat;
        let h_le_f = d.lemma(nat_p.le_add_right, &[mf_n, mg_n]);
        let raw_g = d.lemma(nat_p.le_add_right, &[mg_n, mf_n]);
        let comm_eq = d.lemma(nat_p.add_comm, &[mg_n, mf_n]);
        let h_le_g = nat_rewrite_prop(d, mg_plus_mf, combined, comm_eq, raw_g, &|d, t| {
            NatOps::le(d, mg_n, t)
        });

        let r_f = div_succ(d, p, 1, mf_n);
        let r_g = div_succ(d, p, 1, mg_n);
        let r_combined = div_succ(d, p, 1, combined);
        let rat_f = d.lemma(p.rat.nat_div_succ_antitone, &[mf_n, combined, h_le_f]);
        let rat_g = d.lemma(p.rat.nat_div_succ_antitone, &[mg_n, combined, h_le_g]);

        let ofr_combined = d.const_app(p.of_rat, &[r_combined]);
        let ofr_f = d.const_app(p.of_rat, &[r_f]);
        let ofr_g = d.const_app(p.of_rat, &[r_g]);
        let creal_f = d.lemma(p.of_rat_le, &[r_combined, r_f, rat_f]);
        let creal_g = d.lemma(p.of_rat_le, &[r_combined, r_g, rat_g]);

        let ny = cneg(d, p, y);
        let diff_xy = cadd(d, p, x, ny);
        let abs_diff = d.const_app(p.abs, &[diff_xy]);
        let hyp_f = d.lemma(p.le_trans, &[abs_diff, ofr_combined, ofr_f, h, creal_f]);
        let hyp_g = d.lemma(p.le_trans, &[abs_diff, ofr_combined, ofr_g, h, creal_g]);

        let spec_f = d.const_app(p.uc_spec, &[f, a, b, huc_f]);
        let spec_g = d.const_app(p.uc_spec, &[g, a, b, huc_g]);
        let close_f = d.apply(spec_f, &[n, x, y, hax, hxb, hay, hyb, hyp_f]);
        let close_g = d.apply(spec_g, &[n, x, y, hax, hxb, hay, hyb, hyp_g]);

        let q = div_succ(d, p, 1, n);
        let oq = d.const_app(p.of_rat, &[q]);

        let fx = d.apply(f, &[x]);
        let fy = d.apply(f, &[y]);
        let gx = d.apply(g, &[x]);
        let gy = d.apply(g, &[y]);

        // Split both `close_within`s into their two shifted one-sided halves.
        let (hf_xy, hf_yx) = two_sided(d, p, fx, fy, q, close_f);
        let (hg_xy, hg_yx) = two_sided(d, p, gx, gy, q, close_g);

        let jx = d.const_app(op, &[fx, gx]);
        let jy = d.const_app(op, &[fy, gy]);

        let forward = lattice_shift(d, p, join, op, fx, gx, fy, gy, oq, hf_xy, hg_xy);
        let backward = lattice_shift(d, p, join, op, fy, gy, fx, gx, oq, hf_yx, hg_yx);

        let result = d.lemma(p.abs_le_of_two_sided, &[jx, jy, q, forward, backward]);

        let with_h = d.lam_fv(h_fv, hyp, result);
        let with_hyb = d.lam_fv(hyb_fv, range_yb, with_h);
        let with_hay = d.lam_fv(hay_fv, range_ay, with_hyb);
        let with_hxb = d.lam_fv(hxb_fv, range_xb, with_hay);
        let with_hax = d.lam_fv(hax_fv, range_ax, with_hxb);
        let with_y = d.lam_fv(y_fv, carrier, with_hax);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(n_fv, nat, with_x)
    };

    let mk_applied = d.const_app(p.uc_mk, &[combined_fn, a, b, modulus, spec]);
    let value = {
        let with_huc_g = d.lam_fv(huc_g_fv, huc_g_ty, mk_applied);
        let with_huc_f = d.lam_fv(huc_f_fv, huc_f_ty, with_huc_g);
        let with_b = d.lam_fv(b_fv, carrier, with_huc_f);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        let with_g = d.lam_fv(g_fv, func_ty, with_a);
        d.lam_fv(f_fv, func_ty, with_g)
    };
    let ty = {
        let applied = uc_ty(d, p, combined_fn, a, b);
        let with_huc_g = d.arrow(huc_g_ty, applied);
        let with_huc_f = d.arrow(huc_f_ty, with_huc_g);
        let with_b = d.pi_fv(b_fv, carrier, with_huc_f);
        let with_a = d.pi_fv(a_fv, carrier, with_b);
        let with_g = d.pi_fv(g_fv, func_ty, with_a);
        d.pi_fv(f_fv, func_ty, with_g)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// `(le u (add v (ofRat q)), le v (add u (ofRat q)))` from
/// `h : close_within u v q`, via [`CRealPrelude::two_sided_of_abs_sub_le`].
fn two_sided(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    q: ExprId,
    h: ExprId,
) -> (ExprId, ExprId) {
    let oq = d.const_app(p.of_rat, &[q]);
    let v_q = cadd(d, p, v, oq);
    let u_q = cadd(d, p, u, oq);
    let l_ty = cle(d, p, u, v_q);
    let r_ty = cle(d, p, v, u_q);
    let both = d.lemma(p.two_sided_of_abs_sub_le, &[u, v, q, h]);
    let left = d.and_left(l_ty, r_ty, both);
    let right = d.and_right(l_ty, r_ty, both);
    (left, right)
}

/// `le (OP u1 u2) (add (OP w1 w2) oq)` from `h1 : le u1 (add w1 oq)` and
/// `h2 : le u2 (add w2 oq)`, where `OP` is `max` (`join`) or `min`.
///
/// The two halves are genuinely different arguments, not duals of one
/// builder: see this file's module documentation.
#[allow(clippy::too_many_arguments)]
fn lattice_shift(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    join: bool,
    op: crate::NameId,
    u1: ExprId,
    u2: ExprId,
    w1: ExprId,
    w2: ExprId,
    oq: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let ju = d.const_app(op, &[u1, u2]);
    let jw = d.const_app(op, &[w1, w2]);
    let jw_q = cadd(d, p, jw, oq);
    let w1_q = cadd(d, p, w1, oq);
    let w2_q = cadd(d, p, w2, oq);
    let refl_oq = d.lemma(p.le_refl, &[oq]);

    if join {
        // `u1 ≤ w1 + q ≤ max w1 w2 + q`, likewise `u2`, then `max_le`.
        let w1_le = d.lemma(p.le_max_left, &[w1, w2]);
        let s1 = d.lemma(p.add_le_add, &[w1, jw, oq, oq, w1_le, refl_oq]);
        let a1 = d.lemma(p.le_trans, &[u1, w1_q, jw_q, h1, s1]);
        let w2_le = d.lemma(p.le_max_right, &[w1, w2]);
        let s2 = d.lemma(p.add_le_add, &[w2, jw, oq, oq, w2_le, refl_oq]);
        let a2 = d.lemma(p.le_trans, &[u2, w2_q, jw_q, h2, s2]);
        d.lemma(p.max_le, &[u1, u2, jw_q, a1, a2])
    } else {
        // `min u1 u2 + (−q) ≤ w1` and `≤ w2`, then `le_min`, then shift back.
        let noq = cneg(d, p, oq);
        let ju_noq = cadd(d, p, ju, noq);
        let refl_noq = d.lemma(p.le_refl, &[noq]);
        let refl_ju_noq = d.lemma(p.equiv_refl, &[ju_noq]);

        // `min u1 u2 ≤ u1 ≤ w1 + q`
        let proj1 = d.lemma(p.min_le_left, &[u1, u2]);
        let step1 = d.lemma(p.le_trans, &[ju, u1, w1_q, proj1, h1]);
        let sh1 = d.lemma(p.add_le_add, &[ju, w1_q, noq, noq, step1, refl_noq]);
        let w1_q_noq = cadd(d, p, w1_q, noq);
        let can1 = add_then_sub_cancel(d, p, w1, oq);
        let l1 = d.lemma(
            p.le_congr,
            &[ju_noq, ju_noq, w1_q_noq, w1, refl_ju_noq, can1, sh1],
        );

        // `min u1 u2 ≤ u2 ≤ w2 + q`
        let proj2 = d.lemma(p.min_le_right, &[u1, u2]);
        let step2 = d.lemma(p.le_trans, &[ju, u2, w2_q, proj2, h2]);
        let sh2 = d.lemma(p.add_le_add, &[ju, w2_q, noq, noq, step2, refl_noq]);
        let w2_q_noq = cadd(d, p, w2_q, noq);
        let can2 = add_then_sub_cancel(d, p, w2, oq);
        let l2 = d.lemma(
            p.le_congr,
            &[ju_noq, ju_noq, w2_q_noq, w2, refl_ju_noq, can2, sh2],
        );

        let meet = d.lemma(p.le_min, &[w1, w2, ju_noq, l1, l2]);
        // meet : le (add ju (neg oq)) (min w1 w2)
        let back = d.lemma(p.add_le_add, &[ju_noq, jw, oq, oq, meet, refl_oq]);
        let ju_noq_q = cadd(d, p, ju_noq, oq);
        let restore = sub_then_add_cancel(d, p, ju, oq);
        let refl_jw_q = d.lemma(p.equiv_refl, &[jw_q]);
        d.lemma(
            p.le_congr,
            &[ju_noq_q, ju, jw_q, jw_q, restore, refl_jw_q, back],
        )
    }
}

// --- the family --------------------------------------------------------------

/// `CReal.ivtPlateau : CReal → CReal → CReal :=
/// fun v x => min x (max (add x (neg one)) v)`.
fn declare_ivt_plateau(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let one = d.kernel().const_(p.one, vec![]);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let neg_one = cneg(d, p, one);
    let floor = cadd(d, p, x, neg_one);
    let lifted = d.const_app(p.max, &[floor, v]);
    let body = d.const_app(p.min, &[x, lifted]);

    let value = {
        let inner = d.lam_fv(x_fv, carrier, body);
        d.lam_fv(v_fv, carrier, inner)
    };
    let ty = {
        let inner = d.arrow(carrier, carrier);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.ivt_boundary.ivt_plateau,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 1),
    })
}

/// `CReal.ivtPlateau_nonpos_at_zero : ∀ v, le (ivtPlateau v zero) zero`.
fn declare_ivt_plateau_nonpos_at_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let neg_one = cneg(d, p, one);
    let floor = cadd(d, p, zero, neg_one);
    let lifted = d.const_app(p.max, &[floor, v]);
    let body = d.lemma(p.min_le_left, &[zero, lifted]);

    let value = d.lam_fv(v_fv, carrier, body);
    let ty = {
        let applied = d.const_app(p.ivt_boundary.ivt_plateau, &[v, zero]);
        let conclusion = cle(d, p, applied, zero);
        d.pi_fv(v_fv, carrier, conclusion)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_boundary.ivt_plateau_nonpos_at_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.ivtPlateau_nonneg_at_one : ∀ v, le zero (ivtPlateau v one)`.
fn declare_ivt_plateau_nonneg_at_one(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);

    let neg_one = cneg(d, p, one);
    let floor = cadd(d, p, one, neg_one);
    let lifted = d.const_app(p.max, &[floor, v]);

    let zero_lt_one = d.kernel().const_(p.zero_lt_one, vec![]);
    let zero_le_one = d.lemma(p.le_of_lt, &[zero, one, zero_lt_one]);

    // 0 ≈ 1 + (−1) ≤ max (1 + (−1)) v
    let floor_le = d.lemma(p.le_max_left, &[floor, v]);
    let floor_zero = d.lemma(p.add_neg, &[one]);
    let refl_lifted = d.lemma(p.equiv_refl, &[lifted]);
    let zero_le_lifted = d.lemma(
        p.le_congr,
        &[
            floor,
            zero,
            lifted,
            lifted,
            floor_zero,
            refl_lifted,
            floor_le,
        ],
    );

    let body = d.lemma(p.le_min, &[one, lifted, zero, zero_le_one, zero_le_lifted]);
    let value = d.lam_fv(v_fv, carrier, body);
    let ty = {
        let applied = d.const_app(p.ivt_boundary.ivt_plateau, &[v, one]);
        let conclusion = cle(d, p, zero, applied);
        d.pi_fv(v_fv, carrier, conclusion)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_boundary.ivt_plateau_nonneg_at_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.ivtPlateau_uniformly_continuous : ∀ v,
/// UniformlyContinuousOn (ivtPlateau v) zero one` — pure assembly over the
/// lattice closure lemmas declared above and the existing
/// `uniformly_continuous_id`/`_const`/`_add`.
fn declare_ivt_plateau_uniformly_continuous(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let neg_one = cneg(d, p, one);

    let id_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        d.lam_fv(r_fv, carrier, r)
    };
    let const_neg_one_fn = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, neg_one)
    };
    let const_v_fn = {
        let r_fv = d.fresh_fvar();
        d.lam_fv(r_fv, carrier, v)
    };
    let shift_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let body = cadd(d, p, r, neg_one);
        d.lam_fv(r_fv, carrier, body)
    };
    let lifted_fn = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let floor = cadd(d, p, r, neg_one);
        let body = d.const_app(p.max, &[floor, v]);
        d.lam_fv(r_fv, carrier, body)
    };

    let uc_id = d.lemma(p.uniformly_continuous_id, &[zero, one]);
    let uc_cn = d.lemma(p.uniformly_continuous_const, &[neg_one, zero, one]);
    let uc_cv = d.lemma(p.uniformly_continuous_const, &[v, zero, one]);
    let uc_shift = d.lemma(
        p.uniformly_continuous_add,
        &[id_fn, const_neg_one_fn, zero, one, uc_id, uc_cn],
    );
    let uc_lifted = d.lemma(
        p.ivt_boundary.uniformly_continuous_max,
        &[shift_fn, const_v_fn, zero, one, uc_shift, uc_cv],
    );
    let body = d.lemma(
        p.ivt_boundary.uniformly_continuous_min,
        &[id_fn, lifted_fn, zero, one, uc_id, uc_lifted],
    );

    let value = d.lam_fv(v_fv, carrier, body);
    let ty = {
        let family = d.const_app(p.ivt_boundary.ivt_plateau, &[v]);
        let conclusion = uc_ty(d, p, family, zero, one);
        d.pi_fv(v_fv, carrier, conclusion)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_boundary.ivt_plateau_uniformly_continuous,
        uparams: vec![],
        ty,
        value,
    })
}

// --- ADR-0603 row 2 -----------------------------------------------------------

/// `CReal.ivt_exact_root_decides_sign : ∀ v c, le zero c → le c one →
/// Equiv (min c (max (add c (neg one)) v)) zero → Or (le v zero) (le zero v)`
/// — this file's module documentation has the statement, the reason for this
/// particular family, and the two-branch paper proof.
fn declare_ivt_exact_root_decides_sign(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    // The two faithful-but-unused interval hypotheses.
    let hc0_ty = cle(d, p, zero, c);
    let hc1_ty = cle(d, p, c, one);

    let neg_one = cneg(d, p, one);
    let floor = cadd(d, p, c, neg_one); // a := c + (−1)
    let lifted = d.const_app(p.max, &[floor, v]); // w := max a v
    let plateau = d.const_app(p.min, &[c, lifted]); // min c w

    let hroot_ty = d.const_app(p.equiv, &[plateau, zero]);
    let hroot_fv = d.fresh_fvar();
    let hroot = d.kernel().fvar(hroot_fv);

    let left_disj = cle(d, p, v, zero);
    let right_disj = cle(d, p, zero, v);
    let target = d.or(left_disj, right_disj);

    // `0 ≤ w`, free from the meet's right projection plus the root.
    let min_le_w = d.lemma(p.min_le_right, &[c, lifted]);
    let refl_lifted = d.lemma(p.equiv_refl, &[lifted]);
    let zero_le_w = d.lemma(
        p.le_congr,
        &[plateau, zero, lifted, lifted, hroot, refl_lifted, min_le_w],
    );

    let zero_lt_one = d.kernel().const_(p.zero_lt_one, vec![]);
    let lt_zero_c = clt(d, p, zero, c);
    let lt_c_one = clt(d, p, c, one);
    let cotrans = d.lemma(p.lt_cotrans, &[zero, one, zero_lt_one, c]);

    let body = d.or_elim(
        lt_zero_c,
        lt_c_one,
        target,
        cotrans,
        // --- branch A: 0 < c ------------------------------------------------
        &|d, hpos| {
            let lt_zero_v = clt(d, p, zero, v);
            let lt_v_c = clt(d, p, v, c);
            let inner = d.lemma(p.lt_cotrans, &[zero, c, hpos, v]);
            d.or_elim(
                lt_zero_v,
                lt_v_c,
                target,
                inner,
                // 0 < v  =>  0 ≤ v
                &|d, hv| {
                    let le_zero_v = d.lemma(p.le_of_lt, &[zero, v, hv]);
                    d.or_inr(left_disj, right_disj, le_zero_v)
                },
                // v < c  =>  w ≈ 0  =>  v ≤ 0
                &|d, hvc| {
                    let le_v_c = d.lemma(p.le_of_lt, &[v, c, hvc]);
                    // a = c + (−1) ≤ c + 0 ≈ c
                    let le_floor_c = {
                        let refl_c = d.lemma(p.le_refl, &[c]);
                        let neg_one_le_zero = neg_one_nonpos(d, p);
                        let widened = d.lemma(
                            p.add_le_add,
                            &[c, c, neg_one, zero, refl_c, neg_one_le_zero],
                        );
                        // widened : le (add c (neg one)) (add c zero)
                        let c_zero = cadd(d, p, c, zero);
                        let collapse = d.lemma(p.add_zero, &[c]);
                        let refl_floor = d.lemma(p.equiv_refl, &[floor]);
                        d.lemma(
                            p.le_congr,
                            &[floor, floor, c_zero, c, refl_floor, collapse, widened],
                        )
                    };
                    let w_le_c = d.lemma(p.max_le, &[floor, v, c, le_floor_c, le_v_c]);
                    let refl_w = d.lemma(p.le_refl, &[lifted]);
                    let w_le_min = d.lemma(p.le_min, &[c, lifted, lifted, w_le_c, refl_w]);
                    let w_eq_min =
                        d.lemma(p.equiv_of_le_le, &[lifted, plateau, w_le_min, min_le_w]);
                    let w_eq_zero =
                        d.lemma(p.equiv_trans, &[lifted, plateau, zero, w_eq_min, hroot]);
                    let v_le_w = d.lemma(p.le_max_right, &[floor, v]);
                    let refl_v = d.lemma(p.equiv_refl, &[v]);
                    let le_v_zero =
                        d.lemma(p.le_congr, &[v, v, lifted, zero, refl_v, w_eq_zero, v_le_w]);
                    d.or_inl(left_disj, right_disj, le_v_zero)
                },
            )
        },
        // --- branch B: c < 1 ------------------------------------------------
        &|d, hlt1| {
            // a := c + (−1) < 0, from `c < 1` plus `(−1) + 1 ≈ 0`.
            let floor_neg = {
                let refl_neg_one = d.lemma(p.le_refl, &[neg_one]);
                let raw = d.lemma(
                    p.add_lt_add_of_le_of_lt,
                    &[neg_one, neg_one, c, one, refl_neg_one, hlt1],
                );
                // raw : lt (add (neg one) c) (add (neg one) one)
                let no_c = cadd(d, p, neg_one, c);
                let lhs_eq = d.lemma(p.add_comm, &[neg_one, c]);
                let no_one = cadd(d, p, neg_one, one);
                let one_no = cadd(d, p, one, neg_one);
                let rhs_comm = d.lemma(p.add_comm, &[neg_one, one]);
                let rhs_cancel = d.lemma(p.add_neg, &[one]);
                let rhs_eq = d.lemma(p.equiv_trans, &[no_one, one_no, zero, rhs_comm, rhs_cancel]);
                d.lemma(
                    p.lt_congr,
                    &[no_c, floor, no_one, zero, lhs_eq, rhs_eq, raw],
                )
            };
            let lt_floor_v = clt(d, p, floor, v);
            let lt_v_zero = clt(d, p, v, zero);
            let inner = d.lemma(p.lt_cotrans, &[floor, zero, floor_neg, v]);
            d.or_elim(
                lt_floor_v,
                lt_v_zero,
                target,
                inner,
                // a < v  =>  w ≈ v  =>  0 ≤ v
                &|d, hav| {
                    let le_floor_v = d.lemma(p.le_of_lt, &[floor, v, hav]);
                    let refl_v = d.lemma(p.le_refl, &[v]);
                    let w_le_v = d.lemma(p.max_le, &[floor, v, v, le_floor_v, refl_v]);
                    let v_le_w = d.lemma(p.le_max_right, &[floor, v]);
                    let w_eq_v = d.lemma(p.equiv_of_le_le, &[lifted, v, w_le_v, v_le_w]);
                    let refl_zero = d.lemma(p.equiv_refl, &[zero]);
                    let le_zero_v = d.lemma(
                        p.le_congr,
                        &[zero, zero, lifted, v, refl_zero, w_eq_v, zero_le_w],
                    );
                    d.or_inr(left_disj, right_disj, le_zero_v)
                },
                // v < 0  =>  v ≤ 0
                &|d, hv| {
                    let le_v_zero = d.lemma(p.le_of_lt, &[v, zero, hv]);
                    d.or_inl(left_disj, right_disj, le_v_zero)
                },
            )
        },
    );

    let value = {
        let with_hroot = d.lam_fv(hroot_fv, hroot_ty, body);
        let hc1_fv = d.fresh_fvar();
        let with_hc1 = d.lam_fv(hc1_fv, hc1_ty, with_hroot);
        let hc0_fv = d.fresh_fvar();
        let with_hc0 = d.lam_fv(hc0_fv, hc0_ty, with_hc1);
        let with_c = d.lam_fv(c_fv, carrier, with_hc0);
        d.lam_fv(v_fv, carrier, with_c)
    };
    let ty = {
        let with_hroot = d.arrow(hroot_ty, target);
        let with_hc1 = d.arrow(hc1_ty, with_hroot);
        let with_hc0 = d.arrow(hc0_ty, with_hc1);
        let with_c = d.pi_fv(c_fv, carrier, with_hc0);
        d.pi_fv(v_fv, carrier, with_c)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.ivt_boundary.ivt_exact_root_decides_sign,
        uparams: vec![],
        ty,
        value,
    })
}

/// `le (neg one) zero` — `0 ≤ 1` with `(−1)` added to both sides, then
/// `add zero (neg one) ≈ neg one` and `add one (neg one) ≈ zero`.
fn neg_one_nonpos(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let neg_one = cneg(d, p, one);
    let zero_lt_one = d.kernel().const_(p.zero_lt_one, vec![]);
    let zero_le_one = d.lemma(p.le_of_lt, &[zero, one, zero_lt_one]);
    let refl_neg_one = d.lemma(p.le_refl, &[neg_one]);
    let widened = d.lemma(
        p.add_le_add,
        &[zero, one, neg_one, neg_one, zero_le_one, refl_neg_one],
    );
    // widened : le (add zero (neg one)) (add one (neg one))
    let zero_no = cadd(d, p, zero, neg_one);
    let no_zero = cadd(d, p, neg_one, zero);
    let lhs_comm = d.lemma(p.add_comm, &[zero, neg_one]);
    let lhs_collapse = d.lemma(p.add_zero, &[neg_one]);
    let lhs_eq = d.lemma(
        p.equiv_trans,
        &[zero_no, no_zero, neg_one, lhs_comm, lhs_collapse],
    );
    let one_no = cadd(d, p, one, neg_one);
    let rhs_eq = d.lemma(p.add_neg, &[one]);
    d.lemma(
        p.le_congr,
        &[zero_no, neg_one, one_no, zero, lhs_eq, rhs_eq, widened],
    )
}
