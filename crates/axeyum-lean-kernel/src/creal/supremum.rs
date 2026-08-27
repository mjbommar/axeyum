//! `CReal.maxRange`, the finite-mesh-maximum primitive for the LUB family's
//! honest row 1 (Spivak ch. 8): the supremum of a uniformly continuous
//! function on a compact interval.
//!
//! See
//! [`docs/research/11-design-review/2026-08-27-locatedness-and-the-measure-theoretic-lesson.md`](../../../../../docs/research/11-design-review/2026-08-27-locatedness-and-the-measure-theoretic-lesson.md)
//! §4 for the assignment this file answers, and its own §2 for **why this is
//! constructive at all**: `sup` for a general bounded set needs
//! **locatedness** (a computable distance function) and is NOT available
//! here — that is why Bishop completeness, not a general LUB, is what this
//! kernel ships. A uniformly continuous function on `[a, b]` is different:
//! its mesh maxima converge (this file), because the modulus itself supplies
//! the missing locatedness.
//!
//! ## The value/argmax distinction — read this before using anything here
//!
//! **The supremum VALUE of a uniformly continuous `F` on `[a, b]` is
//! constructive. The ARGMAX is not, and never will be with the tools this
//! kernel has.**
//! [`CReal.evt_attained_max_decides_sign`](super::CRealPrelude::evt_attained_max_decides_sign)
//! (`creal/extreme_value.rs`) proves that an *attaining* maximiser for a
//! specific uniformly continuous family would decide the sign of an
//! arbitrary real — i.e. attainment is EVT's row 2, and it is a genuine
//! impossibility result, not an unfinished proof. `CReal.maxRange` and
//! everything built on it here only ever produce a *value*: the height of
//! the graph, never a point that reaches it. Anyone tempted to add an
//! `argmax`-shaped declaration to this file should read that theorem's own
//! module documentation first (`creal/extreme_value.rs`).
//!
//! ## What this file lands, and what it does not
//!
//! **Landed**: `CReal.maxRange`, a `Nat.rec`-structured finite-mesh-maximum
//! fold over an arbitrary `Nat → CReal` sequence — the `max`-lattice analogue
//! of [`CReal.sumRange`](super::CRealPrelude::sum_range) — plus its defining
//! equations and the two order facts every consumer of a finite maximum
//! needs: every sampled value is `≤` the fold (`maxRange_self_le`, hence
//! `maxRange_ub` at any earlier index via `maxRange_mono`), and the fold is
//! monotone in its own bound (`maxRange_mono`, built from
//! [`CReal.mono_of_le_succ`](super::CRealPrelude::mono_of_le_succ) exactly
//! the way [`CReal.sumRange_mono_outer`](super::CRealPrelude::sum_range_mono_outer)
//! is, but with no nonnegativity hypothesis — `max`'s own step law
//! (`le_max_left`) needs none).
//!
//! **Also landed this session (route 2's first two rungs — see below):**
//! `CReal.meshLevelCount` (`Nat → Nat`, the geometric doubling schedule
//! `meshLevelCount j = 2^j − 1`, built additively so it needs no `Nat.mul`)
//! and `CReal.meshMax` (`(CReal → CReal) → CReal → CReal → Nat → CReal`, the
//! level-`j` mesh maximum `meshMax F a b j := maxRange (fun i => F(a +
//! i·Δⱼ)) (meshLevelCount j)`, `Δⱼ := (b−a)/(meshLevelCount j + 1)`). Both
//! are pure `Definition`s needing no hypothesis on `F`/`a`/`b` and no
//! continuity witness — the continuity only enters at the NEXT rung.
//!
//! **Still not landed: `CReal.supOn` itself**, and therefore none of
//! deliverables (a)/(b)/(c) the assignment names in fully assembled form.
//! This is not a hedge — it is the honest outcome of a real attempt at the
//! full route, and the remaining obstruction is now characterized much more
//! precisely than at the start of this session (below), which is the point
//! of recording it here rather than leaving a silent gap.
//!
//! ### Why `supOn` did not land, precisely — and the now-concrete plan for it
//!
//! `supOn` needs `CReal.mk (speedup f_lambda K) (regularity proof)`, built
//! **without** `Exists.rec` (kernel fact 1 — `K` and `f_lambda` must be
//! *concrete* data, never extracted from an existential, since they feed
//! `speedup`, a `Type`-level construction). Landing that regularity proof —
//! `∀ p q, Within (seq (f_lambda p) p − seq (f_lambda q) q) (natDivSucc K p +
//! natDivSucc K q)` — needs, for two *independent* accuracies `p`/`q`, a
//! bound relating a mesh maximum at one accuracy to one at another. That
//! bound needs, for an arbitrary point of one mesh, the *nearest point of the
//! other mesh* — a genuine "which cell" lookup, UNLESS the two meshes are
//! chosen to nest exactly, which is exactly what `meshLevelCount`'s doubling
//! schedule buys (below).
//!
//! Two routes were investigated and both are real, existing machinery — this
//! is not a case of the tool being missing, only of correctly assembling it
//! not fitting this session:
//!
//! 1. **Reuse `CReal.bucketIndex`/`bucketIndexFloorLower`/`bucketIndexFloorUpper`**
//!    (`creal/uniform_continuity.rs`, built for
//!    [`CReal.bounded_of_uniformly_continuous`](super::CRealPrelude::bounded_of_uniformly_continuous)'s
//!    own covering argument). These are public, already proved, and directly
//!    applicable in principle — but that covering argument is ~700 lines with
//!    real, documented subtleties (a `+2`/`+3` floor slack, a sign hypothesis
//!    on the lower clamp, a still-open gap the same file's `crossingClose`
//!    entry names explicitly). Reusing it correctly for a *different*
//!    quantity (a running maximum, not a single boundedness witness) is a
//!    genuine new proof, not a two-line application. **Rejected**, unchanged
//!    from the prior assessment.
//! 2. **A NESTED-REFINEMENT construction avoiding bucket-index entirely**
//!    (this file, in progress). `meshLevelCount`'s doubling means level `j`'s
//!    mesh points are EXACTLY a subset of level `j'`'s (`j' ≥ j`): a coarse
//!    sample `a + i·Δⱼ` equals the fine sample `a + (i·2^(j'−j))·Δⱼ'`, a pure
//!    index-scaling identity via
//!    [`Rat.natDivSucc_scale`](crate::RatPrelude::nat_div_succ_scale) /
//!    [`Rat.natDivSucc_mul`](crate::RatPrelude::nat_div_succ_mul) — no
//!    `Nat.div`, no search. That is the property route 1 does not have.
//!
//! **The remaining assembly, characterized precisely (verified against this
//! kernel's actual API this session, not just worked out on paper):**
//!
//! - **Rung 3, the order half (no continuity needed):**
//!   `meshMax_step_le : ∀ F a b j, le (meshMax F a b j) (meshMax F a b
//!   (Nat.succ j))`. This is NOT an instance of
//!   [`CReal.mono_of_le_succ`](super::CRealPrelude::mono_of_le_succ) the way
//!   `maxRange_mono` is (`mono_of_le_succ` holds the SAMPLING FUNCTION fixed
//!   and varies only `maxRange`'s own bound; here both the sampling function
//!   AND the bound change together as `j` grows). It needs a genuinely new
//!   combinator, proved once and reusable well beyond this file:
//!   `maxRange_transport : ∀ f g n n' (e : Nat → Nat), (∀ i, Nat.le i n →
//!   Nat.le (e i) n') → (∀ i, Nat.le i n → Equiv (f i) (g (e i))) → le
//!   (maxRange f n) (maxRange g n')` — by induction on an AUXILIARY index `k`
//!   (motive `fun k => Nat.le k n → le (maxRange f k) (maxRange g n')`, the
//!   side condition threaded through the motive exactly the way
//!   [`NatOps::induct`](crate::nat_prelude::NatOps::induct)'s generic `p`
//!   closure supports — confirmed against its actual signature this session),
//!   base case via [`CRealPrelude::maxRange_ub`] plus
//!   [`CRealPrelude::le_congr`], step case via
//!   [`CRealPrelude::max_le`](super::CRealPrelude::max_le) (confirmed to
//!   exist: `∀ x y z, le x z → le y z → le (max x y) z`) combining the IH
//!   with a fresh `maxRange_ub` instance. Instantiated at `e(i) := 2·i`,
//!   `n := meshLevelCount j`, `n' := meshLevelCount (succ j)` (so `e(i) ≤ n'`
//!   is `2i ≤ 2·meshLevelCount j + 1`, immediate from `i ≤ meshLevelCount j`),
//!   the `Equiv` hypothesis is exactly the sample-point identity above,
//!   closed via [`CRealPrelude::of_nat_mul`] (`ofNat (2i) ~ mul (ofNat 2)
//!   (ofNat i)`, confirmed to exist) plus the `natDivSucc_scale`/`_mul`
//!   algebra giving `mul (ofNat 2) Δⱼ' ~ Δⱼ`.
//! - **Rung 4, general monotonicity, for free once rung 3 lands:**
//!   `meshMax_mono : ∀ F a b j j', Nat.le j j' → le (meshMax F a b j)
//!   (meshMax F a b j')`, by [`CRealPrelude::mono_of_le_succ`] applied to
//!   `fun j => meshMax F a b j` with rung 3 as the adjacent step — EXACTLY
//!   [`declare_max_range_mono`]'s own construction, one level up.
//! - **Rung 5, the accuracy-selection scheme (where continuity enters).**
//!   The naive choice — request the SAME accuracy `k` as the outer `CReal`
//!   index — fails: uniform continuity at request `k` only bounds the
//!   one-step gap by `1/(k+1)` (the HARMONIC series, not summable), so the
//!   telescoped tail never converges. The level-`k` mesh must instead be fine
//!   enough for accuracy request `2^k − 1` (i.e. `meshLevelCount k` itself,
//!   reusing that same function as the REQUESTED accuracy index), giving a
//!   one-step gap `≤ 1/2^k` — summable — via
//!   `Nat.lt_pow_size : ∀ n, Lt n (pow 2 (size n))` (confirmed to exist,
//!   `nat_prelude.rs`) to turn `u.modulus(meshLevelCount k)`, an ARBITRARY
//!   `Nat`, into a POWER-OF-TWO exponent comfortably above it, with NO
//!   `Nat.div`/search: `exponent(k) := Nat.size (u.modulus (meshLevelCount
//!   k))`. `exponent` need not be monotone (an arbitrary modulus need not
//!   be), so nesting needs a running accumulator forcing monotonicity —
//!   **use `Nat.add`, not `Nat.max`: this kernel's `Nat` prelude has no
//!   `Nat.max`,** and addition suffices (`trueExponent 0 := exponent 0`,
//!   `trueExponent (succ k) := add (trueExponent k) (exponent (succ k))`,
//!   monotone via [`Nat.le_add_right`](crate::NatPrelude::le_add_right) and
//!   `≥ exponent(k)` via the same lemma read through `Nat.add_comm`). The
//!   final `f_lambda(k) := meshMax F a b (trueExponent k)` is then genuinely
//!   nested (rung 3/4 apply, `j := trueExponent k`), and the per-level
//!   gap is bounded by `1/2^k` via the modulus applied at accuracy request
//!   `meshLevelCount k` on the KNOWN, closed-form displacement between a
//!   fine point and its immediate coarse neighbour (no bucket search — the
//!   doubling nesting makes that displacement exact, not merely bounded).
//! - **Rung 6, the telescope.** Sum the per-level gaps via
//!   [`CReal.sumRange_cauchy_of_dominated`](super::CRealPrelude::sum_range_cauchy_of_dominated)
//!   (`creal/series.rs`) against a CONCRETE ratio-`1/2` geometric dominator —
//!   **`creal/geometric.rs` already proves `Cauchy (sumRange (fun n => pow x
//!   n))` for `x` bounded away from `1` by a witnessed `PosBound`**
//!   (`geom_tail_bounded_div`/`geom_tail_within`, that file's own module
//!   documentation), and at the CONCRETE `x := natDivSucc 1 1` (`= 1/2`) the
//!   needed `PosBound (add one (neg x)) k` witness is immediate (no
//!   apartness search — `1 − 1/2 = 1/2` is a fixed rational, not an arbitrary
//!   hypothesis). A constant-multiple corollary (scaling a Cauchy bound by a
//!   fixed positive `CReal` constant) is the one piece here NOT already
//!   confirmed to exist by name and may need a short derivation.
//! - **Rung 7.** Feed the resulting `K`-scaled Cauchy witness to
//!   [`CReal.regular_of_scaled_cauchy`](super::CRealPrelude::regular_of_scaled_cauchy),
//!   exactly [`declare_creal_integral`](super::integral::declare_creal_integral)'s
//!   own `CReal.mk (speedup f_lambda K) (regular_of_scaled_cauchy f_lambda K
//!   h)` shape (kernel fact 1 respected: `f_lambda`/`K` stay concrete data
//!   throughout, never pulled from an `Exists`).
//!
//! This plan is now grounded against the kernel's actual API (every named
//! lemma above was confirmed present this session, not merely recalled) —
//! the remaining work is assembling rungs 3–7 as kernel terms, each with its
//! own real risk of `TypeMismatch` cycles (see this file's own experience
//! with rungs 1–2, which built cleanly on the first attempt each time by
//! mirroring `declare_max_range`'s and `integral.rs`'s existing shapes
//! exactly rather than composing primitives from scratch). Rung 3 is the
//! next concrete task; do NOT skip to rung 5 without it, since rung 4's
//! `mono_of_le_succ` application needs rung 3 as its adjacent-step
//! hypothesis verbatim.

#![allow(clippy::doc_markdown, clippy::too_many_arguments)]

use super::{CRealPrelude, cadd, cle, creal_ty, embed};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Reducibility height for [`declare_max_range`]'s `Definition`. Deliberately
/// far above [`super::DERIVED_HEIGHT`] plus every other derived-operation
/// offset in this file's build neighbourhood — `maxRange` depends only on
/// `CReal.max` (declared in `creal/lattice.rs`, itself near the bottom of the
/// height order), so any height comfortably above the existing offsets used
/// elsewhere in `creal.rs` is safe; the exact number carries no meaning
/// beyond "unfolds no more eagerly than it has to".
const MAX_RANGE_HEIGHT: u16 = super::DERIVED_HEIGHT + 500;

/// `Eq.{1} CReal a b` — mirrors `series.rs`'s private `creal_eq` (not
/// `pub(super)`, so re-derived here from the same public primitives rather
/// than imported).
fn creal_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let eq = d.kernel().const_(logic.eq, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(eq, &[carrier, a, b])
}

/// `Eq.refl.{1} CReal a` — mirrors `series.rs`'s private `creal_eq_refl`.
fn creal_eq_refl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let one = d.level_one();
    let logic = p.rat.int.logic;
    let refl = d.kernel().const_(logic.eq_refl, vec![one]);
    let carrier = creal_ty(d, p);
    d.apply(refl, &[carrier, a])
}

/// `CReal.maxRange : (Nat → CReal) → Nat → CReal`, structural `Nat.rec` on
/// the bound: `maxRange f 0 := f 0`, `maxRange f (succ n) := max (maxRange f
/// n) (f (succ n))` — so `maxRange f n` is `max_{k≤n} f k` (`n+1` sampled
/// points, unlike `CReal.sumRange`'s `k<n`/`n` points convention: a maximum
/// needs a real starting VALUE, not an identity element, so it anchors at
/// `f 0` rather than at a `zero` the way `sumRange` does).
fn declare_max_range_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d
        .kernel()
        .lam(anon, nat, carrier, crate::BinderInfo::Default);
    let zero_n = d.zero();
    let minor_zero = d.apply(f, &[zero_n]);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let sj = d.succ(j);
        let fsj = d.apply(f, &[sj]);
        let body = d.const_app(p.max, &[ih, fsj]);
        let inner = d.lam_fv(ih_fv, carrier, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, carrier);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.max_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// `CReal.maxRange_zero`/`CReal.maxRange_succ`: the defining equations of
/// [`declare_max_range`], each closed by `Eq.refl` alone since `maxRange`'s
/// `Nat.rec` application ι-reduces on both minor premises (mirrors
/// `series.rs`'s `declare_sum_range_equations`).
fn declare_max_range_equations(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let _ = carrier;

    // maxRange_zero : ∀ f, Eq CReal (maxRange f Nat.zero) (f Nat.zero).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero_n = d.zero();
        let lhs = d.const_app(p.max_range, &[f, zero_n]);
        let f0 = d.apply(f, &[zero_n]);
        let stmt = creal_eq(d, p, lhs, f0);
        let proof = creal_eq_refl(d, p, f0);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.max_range_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // maxRange_succ : ∀ f (n : Nat),
    //   Eq CReal (maxRange f (succ n)) (max (maxRange f n) (f n... succ n)).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let lhs = d.const_app(p.max_range, &[f, sn]);
        let prior = d.const_app(p.max_range, &[f, n]);
        let fsn = d.apply(f, &[sn]);
        let rhs = d.const_app(p.max, &[prior, fsn]);
        let stmt_inner = creal_eq(d, p, lhs, rhs);
        let proof_inner = creal_eq_refl(d, p, rhs);
        let ty = {
            let inner = d.pi_fv(n_fv, nat, stmt_inner);
            d.pi_fv(f_fv, fn_ty, inner)
        };
        let value = {
            let inner = d.lam_fv(n_fv, nat, proof_inner);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.max_range_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `CReal.maxRange_self_le : ∀ f n, le (f n) (maxRange f n)` — every sampled
/// value is at most the running maximum through its own index. `Nat.rec`
/// case analysis (no inductive hypothesis is used): the base case is
/// `le_refl` against `maxRange f 0`'s ι-reduction to `f 0`, the successor
/// case is `le_max_right` against `maxRange f (succ j)`'s ι-reduction to
/// `max (maxRange f j) (f (succ j))` — both close by defeq alone, the same
/// way `maxRange_zero`/`maxRange_succ` do.
fn declare_max_range_self_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let _ = carrier;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let fx = d.apply(f, &[x]);
        let mr = d.const_app(p.max_range, &[f, x]);
        cle(d, p, fx, mr)
    };

    let proof = d.induct(
        &motive,
        &|d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            let f0 = d.apply(f, &[zero_n]);
            d.lemma(p.le_refl, &[f0])
        },
        &|d: &mut IntDev<'_>, j: ExprId, _ih: ExprId| -> ExprId {
            let sj = d.succ(j);
            let mr_j = d.const_app(p.max_range, &[f, j]);
            let fsj = d.apply(f, &[sj]);
            d.lemma(p.le_max_right, &[mr_j, fsj])
        },
        n,
    );

    let stmt = motive(d, n);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_range_self_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.maxRange_mono : ∀ f m n, Nat.le m n → le (maxRange f m) (maxRange f
/// n)` — monotonicity of the running maximum in its own bound. Built from
/// [`CRealPrelude::mono_of_le_succ`] applied to `fun k => maxRange f k`,
/// exactly the way
/// [`declare_sum_range_mono_outer`](super::series) builds
/// [`CRealPrelude::sum_range_mono_outer`] — but with **no** nonnegativity
/// hypothesis: the adjacent step `le (maxRange f n) (maxRange f (succ n))`
/// is `le_max_left` applied at `(maxRange f n, f (succ n))` directly (defeq
/// to `maxRange f (succ n)`'s own ι-reduction), unlike `sumRange`'s adjacent
/// step, which genuinely needs `f n ≥ 0` to shift by a nonnegative summand.
fn declare_max_range_mono(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let _ = carrier;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);

    let max_f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.max_range, &[f, k]);
        d.lam_fv(k_fv, nat, body)
    };

    let adjacent = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let mr_n = d.const_app(p.max_range, &[f, n]);
        let sn = d.succ(n);
        let fsn = d.apply(f, &[sn]);
        let body = d.lemma(p.le_max_left, &[mr_n, fsn]);
        d.lam_fv(n_fv, nat, body)
    };

    let mono = d.const_app(p.mono_of_le_succ, &[max_f, adjacent]);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hmn_fv = d.fresh_fvar();
    let hmn = d.kernel().fvar(hmn_fv);
    let hmn_ty = d.le(m, n);
    let applied = d.apply(mono, &[m, n, hmn]);

    let mr_m = d.const_app(p.max_range, &[f, m]);
    let mr_n = d.const_app(p.max_range, &[f, n]);
    let conclusion = cle(d, p, mr_m, mr_n);

    let ty = {
        let anon = d.anon_name();
        let out = d
            .kernel()
            .pi(anon, hmn_ty, conclusion, crate::BinderInfo::Default);
        let out = d.pi_fv(n_fv, nat, out);
        let out = d.pi_fv(m_fv, nat, out);
        d.pi_fv(f_fv, fn_ty, out)
    };
    let value = {
        let out = d.lam_fv(hmn_fv, hmn_ty, applied);
        let out = d.lam_fv(n_fv, nat, out);
        let out = d.lam_fv(m_fv, nat, out);
        d.lam_fv(f_fv, fn_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_range_mono,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.maxRange_ub : ∀ f n i, Nat.le i n → le (f i) (maxRange f n)` — the
/// upper-bound property every consumer of a finite maximum actually wants:
/// **any** sampled value up to and including the bound, not only the last
/// one. [`CRealPrelude::max_range_self_le`] at `i` (`le (f i) (maxRange f
/// i)`) composed with [`CRealPrelude::max_range_mono`] at `(i, n, hin)` (`le
/// (maxRange f i) (maxRange f n)`) via [`CRealPrelude::le_trans`] — no new
/// induction needed, since both ingredients already are one.
fn declare_max_range_ub(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let _ = carrier;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hin_fv = d.fresh_fvar();
    let hin = d.kernel().fvar(hin_fv);
    let hin_ty = d.le(i, n);

    let self_le = d.lemma(p.max_range_self_le, &[f, i]);
    let mono = d.lemma(p.max_range_mono, &[f, i, n, hin]);
    let fi = d.apply(f, &[i]);
    let mr_i = d.const_app(p.max_range, &[f, i]);
    let mr_n = d.const_app(p.max_range, &[f, n]);
    let proof = d.lemma(p.le_trans, &[fi, mr_i, mr_n, self_le, mono]);

    let conclusion = cle(d, p, fi, mr_n);
    let ty = {
        let anon = d.anon_name();
        let out = d
            .kernel()
            .pi(anon, hin_ty, conclusion, crate::BinderInfo::Default);
        let out = d.pi_fv(i_fv, nat, out);
        let out = d.pi_fv(n_fv, nat, out);
        d.pi_fv(f_fv, fn_ty, out)
    };
    let value = {
        let out = d.lam_fv(hin_fv, hin_ty, proof);
        let out = d.lam_fv(i_fv, nat, out);
        let out = d.lam_fv(n_fv, nat, out);
        d.lam_fv(f_fv, fn_ty, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_range_ub,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.maxRange` and its order theory: the `Definition`, its two
/// defining equations, and the two order facts (`maxRange_self_le`,
/// `maxRange_mono`, composed into `maxRange_ub`) documented above.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_max_range(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_max_range_def(d, p)?;
    declare_max_range_equations(d, p)?;
    declare_max_range_self_le(d, p)?;
    declare_max_range_mono(d, p)?;
    declare_max_range_ub(d, p)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `CReal.maxRange_transport` -- rung 3's general combinator: comparing two
// DIFFERENT `maxRange` folds (different sampling function, different bound)
// related by an index embedding. See this module's own documentation,
// "Rung 3, the order half", for why this is NOT an instance of
// `mono_of_le_succ` and for the induction this builds.
// ---------------------------------------------------------------------------

/// `CReal.equiv x y` — mirrors the file's own `cle`/`cadd`/`embed` helpers
/// (imported from `super`), re-derived here since none of the sibling files
/// exports an `Equiv`-application helper under a name this file can import.
fn cequiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.equiv, &[x, y])
}

/// `CReal.maxRange_transport : ∀ f g n n' e, (∀ i, Nat.le i n → Nat.le (e i)
/// n') → (∀ i, Nat.le i n → Equiv (f i) (g (e i))) → le (maxRange f n)
/// (maxRange g n')`.
///
/// Proved by induction on an AUXILIARY index `k`, motive `fun k => Nat.le k
/// n → le (maxRange f k) (maxRange g n')`, instantiated at `k := n` (target
/// of the [`NatOps::induct`] call) and discharged with `Nat.le_refl n` —
/// **not** induction on `n` itself, since `n` is a parameter shared by every
/// case, not the thing being inducted on.
///
/// - **Base** (`k = 0`, hypothesis `h0 : Nat.le 0 n`): `maxRange_ub g n' (e
///   0) (hbound 0 h0)` gives `le (g (e 0)) (maxRange g n')`; `le_congr`
///   transports it across `equiv_symm (heq 0 h0) : Equiv (g (e 0)) (f 0)`
///   (the pre-substitution type is `le (g (e 0)) (maxRange g n')`, matching
///   `le_congr`'s own convention) to `le (f 0) (maxRange g n')` — defeq to
///   the goal since `maxRange f 0 ≡ f 0` by ι-reduction, exactly the defeq
///   [`declare_max_range_self_le`]'s own base case leans on.
/// - **Step** (`k = succ j`, hypothesis `hsj : Nat.le (succ j) n`, `ih : Nat.le
///   j n → le (maxRange f j) (maxRange g n')`): `hj := le_trans (le_succ j)
///   hsj : Nat.le j n` feeds `ih hj`; a second `maxRange_ub`/`le_congr`
///   instance at `succ j` (identical shape to the base case) gives `le (f
///   (succ j)) (maxRange g n')`; [`CRealPrelude::max_le`] combines the two
///   into `le (max (maxRange f j) (f (succ j))) (maxRange g n')`, defeq to
///   the goal since `maxRange f (succ j) ≡ max (maxRange f j) (f (succ
///   j))`, exactly the defeq [`declare_max_range_mono`]'s own step leans on.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_max_range_transport_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = creal_ty(d, p);
    let fn_ty = d.arrow(nat, carrier);
    let nat_fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let np_fv = d.fresh_fvar();
    let np = d.kernel().fvar(np_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let hbound_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.le(i, n);
        let ei = d.apply(e, &[i]);
        let concl = d.le(ei, np);
        let inner = d.arrow(hi_ty, concl);
        d.pi_fv(i_fv, nat, inner)
    };
    let hbound_fv = d.fresh_fvar();
    let hbound = d.kernel().fvar(hbound_fv);

    let heq_ty = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.le(i, n);
        let fi = d.apply(f, &[i]);
        let ei = d.apply(e, &[i]);
        let gei = d.apply(g, &[ei]);
        let equiv_i = cequiv(d, p, fi, gei);
        let inner = d.arrow(hi_ty, equiv_i);
        d.pi_fv(i_fv, nat, inner)
    };
    let heq_fv = d.fresh_fvar();
    let heq = d.kernel().fvar(heq_fv);

    // Auxiliary induction motive: `fun k => Nat.le k n -> le (maxRange f k)
    // (maxRange g n')`. `h` (the `Nat.le k n` witness) is never used inside
    // the conclusion, so this is a plain (non-dependent) arrow.
    let motive = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        let h_ty = d.le(k, n);
        let mrk = d.const_app(p.max_range, &[f, k]);
        let mrnp = d.const_app(p.max_range, &[g, np]);
        let concl = cle(d, p, mrk, mrnp);
        d.arrow(h_ty, concl)
    };

    let proof = d.induct(
        &motive,
        &|d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            let h0_fv = d.fresh_fvar();
            let h0 = d.kernel().fvar(h0_fv);
            let h0_ty = d.le(zero_n, n);

            let f0 = d.apply(f, &[zero_n]);
            let e0 = d.apply(e, &[zero_n]);
            let g_e0 = d.apply(g, &[e0]);
            let mrnp = d.const_app(p.max_range, &[g, np]);

            let heq0 = d.apply(heq, &[zero_n, h0]);
            let he0 = d.apply(hbound, &[zero_n, h0]);
            let ub0 = d.lemma(p.max_range_ub, &[g, np, e0, he0]);
            let symm0 = d.lemma(p.equiv_symm, &[f0, g_e0, heq0]);
            let refl_mrnp = d.lemma(p.equiv_refl, &[mrnp]);
            let result0 = d.lemma(p.le_congr, &[g_e0, f0, mrnp, mrnp, symm0, refl_mrnp, ub0]);

            d.lam_fv(h0_fv, h0_ty, result0)
        },
        &|d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let sj = d.succ(j);
            let hsj_fv = d.fresh_fvar();
            let hsj = d.kernel().fvar(hsj_fv);
            let hsj_ty = d.le(sj, n);

            let le_succ_j = d.lemma(p.rat.int.nat.le_succ, &[j]);
            let hj = d.lemma(p.rat.int.nat.le_trans, &[j, sj, n, le_succ_j, hsj]);
            let ih_hj = d.apply(ih, &[hj]);

            let fsj = d.apply(f, &[sj]);
            let esj = d.apply(e, &[sj]);
            let g_esj = d.apply(g, &[esj]);
            let mrj = d.const_app(p.max_range, &[f, j]);
            let mrnp = d.const_app(p.max_range, &[g, np]);

            let heq_sj = d.apply(heq, &[sj, hsj]);
            let he_sj = d.apply(hbound, &[sj, hsj]);
            let ub_sj = d.lemma(p.max_range_ub, &[g, np, esj, he_sj]);
            let symm_sj = d.lemma(p.equiv_symm, &[fsj, g_esj, heq_sj]);
            let refl_mrnp = d.lemma(p.equiv_refl, &[mrnp]);
            let fsj_le = d.lemma(
                p.le_congr,
                &[g_esj, fsj, mrnp, mrnp, symm_sj, refl_mrnp, ub_sj],
            );

            let combine = d.lemma(p.max_le, &[mrj, fsj, mrnp, ih_hj, fsj_le]);
            d.lam_fv(hsj_fv, hsj_ty, combine)
        },
        n,
    );

    let le_refl_n = d.lemma(p.rat.int.nat.le_refl, &[n]);
    let value_body = d.apply(proof, &[le_refl_n]);

    let mrn = d.const_app(p.max_range, &[f, n]);
    let mrnp_final = d.const_app(p.max_range, &[g, np]);
    let conclusion = cle(d, p, mrn, mrnp_final);

    let ty = {
        let out = d.pi_fv(heq_fv, heq_ty, conclusion);
        let out = d.pi_fv(hbound_fv, hbound_ty, out);
        let out = d.pi_fv(e_fv, nat_fn_ty, out);
        let out = d.pi_fv(np_fv, nat, out);
        let out = d.pi_fv(n_fv, nat, out);
        let out = d.pi_fv(g_fv, fn_ty, out);
        d.pi_fv(f_fv, fn_ty, out)
    };
    let value = {
        let out = d.lam_fv(heq_fv, heq_ty, value_body);
        let out = d.lam_fv(hbound_fv, hbound_ty, out);
        let out = d.lam_fv(e_fv, nat_fn_ty, out);
        let out = d.lam_fv(np_fv, nat, out);
        let out = d.lam_fv(n_fv, nat, out);
        let out = d.lam_fv(g_fv, fn_ty, out);
        d.lam_fv(f_fv, fn_ty, out)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.max_range_transport,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.maxRange_transport` alone (a one-declaration `BuildStep`,
/// mirroring the shape of every other single-theorem step in this file's
/// `STEPS` table entries).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_max_range_transport(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_max_range_transport_thm(d, p)
}

// ---------------------------------------------------------------------------
// `CReal.meshLevelCount` -- the geometric (doubling) mesh-count schedule
// route 2's nested refinement runs on. See this module's own documentation,
// "Route 2 is the one to pick up", for why doubling (rather than an
// arbitrary refinement factor) is what makes the coarse-in-fine embedding
// need only closed-form index SCALING (`Rat.natDivSucc_scale`/
// `nat_div_succ_mul`) and no `Nat.div`/bucket-index search.
// ---------------------------------------------------------------------------

/// `CReal.meshLevelCount : Nat → Nat`, `meshLevelCount 0 := 0`, `meshLevelCount
/// (succ j) := succ (add (meshLevelCount j) (meshLevelCount j))` — i.e.
/// `meshLevelCount j = 2^j − 1` (a `mesh_level_count(j)+1`-point mesh has
/// `2^j` points), built additively (`add x x` rather than `mul 2 x`) so no
/// `Nat.mul` dependency is needed for this one recursion. Declared under the
/// `creal` namespace (a [`CRealPrelude`] field) even though its VALUE is pure
/// `Nat → Nat`, because every consumer of it lives in this file's later
/// `CReal`-level construction — mirrors [`declare_max_range_def`]'s own
/// `Nat.rec` shape, minus the `f` parameter (this recursion carries no
/// external function, only the level index itself).
fn declare_mesh_level_count_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let nat_add = d.prelude().add;

    let motive = d.kernel().lam(anon, nat, nat, crate::BinderInfo::Default);
    let minor_zero = d.zero();
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let doubled = d.const_app(nat_add, &[ih, ih]);
        let body = d.succ(doubled);
        let inner = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let value_body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = d.lam_fv(n_fv, nat, value_body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mesh_level_count,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// `CReal.meshLevelCount_zero : Eq Nat (meshLevelCount Nat.zero) Nat.zero` and
/// `CReal.meshLevelCount_succ : ∀ j, Eq Nat (meshLevelCount (succ j)) (add
/// (meshLevelCount j) (meshLevelCount j)).succ` — both close by `Eq.refl`
/// alone, the same reason [`declare_max_range_equations`]'s two equations do
/// (`meshLevelCount`'s `Nat.rec` application ι-reduces on both minor
/// premises).
fn declare_mesh_level_count_equations(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_add = d.prelude().add;
    let one = d.level_one();
    let logic = p.rat.int.logic;

    // meshLevelCount_zero : Eq Nat (meshLevelCount zero) zero.
    {
        let zero_n = d.zero();
        let lhs = d.const_app(p.mesh_level_count, &[zero_n]);
        let eq = d.kernel().const_(logic.eq, vec![one]);
        let stmt = d.apply(eq, &[nat, lhs, zero_n]);
        let refl = d.kernel().const_(logic.eq_refl, vec![one]);
        let value = d.apply(refl, &[nat, zero_n]);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.mesh_level_count_zero,
            uparams: vec![],
            ty: stmt,
            value,
        })?;
    }

    // meshLevelCount_succ : ∀ j,
    //   Eq Nat (meshLevelCount (succ j)) (succ (add (meshLevelCount j)
    //     (meshLevelCount j))).
    {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sj = d.succ(j);
        let lhs = d.const_app(p.mesh_level_count, &[sj]);
        let mlc_j = d.const_app(p.mesh_level_count, &[j]);
        let doubled = d.const_app(nat_add, &[mlc_j, mlc_j]);
        let rhs = d.succ(doubled);
        let eq = d.kernel().const_(logic.eq, vec![one]);
        let stmt_inner = d.apply(eq, &[nat, lhs, rhs]);
        let refl = d.kernel().const_(logic.eq_refl, vec![one]);
        let proof_inner = d.apply(refl, &[nat, rhs]);
        let ty = d.pi_fv(j_fv, nat, stmt_inner);
        let value = d.lam_fv(j_fv, nat, proof_inner);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.mesh_level_count_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// Land `CReal.meshLevelCount` and its two defining equations.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_level_count(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_level_count_def(d, p)?;
    declare_mesh_level_count_equations(d, p)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `CReal.meshMax` -- the level-`j` mesh maximum: `maxRange` sampled over the
// `meshLevelCount j`-point mesh of `[a, b]`.
// ---------------------------------------------------------------------------

/// `CReal.mul x y` -- mirrors the `cmul` private to several sibling files
/// (`trig.rs`, `integral.rs`, …), re-derived here rather than imported per
/// this development's own convention (see [`creal_eq`]'s doc comment).
fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

/// `CReal.neg x` -- mirrors sibling files' private `cneg`.
fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

/// `add (mul (b + (neg a)) (embed (Rat.natDivSucc 1 m)))` — the mesh width
/// `Δ = (b − a)/(m + 1)`, the SAME formula and SAME total-in-`m` design
/// `integral.rs`'s own private `delta_of` uses (see that file's own doc
/// comment for why no `CReal.inv`/`PosBound` is needed); re-derived here
/// rather than imported, per this development's convention.
fn mesh_delta(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, m: ExprId) -> ExprId {
    let na = cneg(d, p, a);
    let width = cadd(d, p, b, na);
    let one_nat = d.num(1);
    let frac = d.const_app(p.rat.nat_div_succ, &[one_nat, m]);
    let frac_real = embed(d, p, frac);
    cmul(d, p, width, frac_real)
}

/// `add a (mul (ofNat i) delta)` — the `i`-th LEFT sample point `a + i·Δ`.
/// Mirrors `integral.rs`'s own private `sample_point`, re-derived here per
/// this development's convention.
fn mesh_sample_point(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    delta: ExprId,
    i: ExprId,
) -> ExprId {
    let oi = d.const_app(p.of_nat, &[i]);
    let shift = cmul(d, p, oi, delta);
    cadd(d, p, a, shift)
}

/// `(CReal → CReal) → CReal → CReal → Nat → CReal`.
fn mesh_max_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let over_j = d.arrow(nat, carrier);
    let over_b = d.arrow(carrier, over_j);
    let over_a = d.arrow(carrier, over_b);
    d.arrow(func_ty, over_a)
}

/// `CReal.meshMax : (CReal → CReal) → CReal → CReal → Nat → CReal :=
/// fun F a b j => maxRange (fun i => F (meshSamplePoint a (meshDelta a b
/// (meshLevelCount j)) i)) (meshLevelCount j)` — the level-`j` mesh maximum:
/// `max_{i ≤ meshLevelCount j} F(a + i·Δⱼ)`, `Δⱼ := (b−a)/(meshLevelCount j +
/// 1)`. Building block for `CReal.supOn` (this module's own documentation):
/// route 2's telescoping construction produces `supOn` as `CReal.mk` on the
/// sequence `fun j => meshMax F a b j` (or a `speedup` of it), once the
/// regularity estimate lands.
fn declare_mesh_max_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let m = d.const_app(p.mesh_level_count, &[j]);
    let delta = mesh_delta(d, p, a, b, m);

    // The maxRange sampling function: fun i => F (meshSamplePoint a delta i).
    let sampler = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = mesh_sample_point(d, p, a, delta, i);
        let fx = d.apply(f, &[sp]);
        d.lam_fv(i_fv, nat, fx)
    };
    let body = d.const_app(p.max_range, &[sampler, m]);

    let value = {
        let with_j = d.lam_fv(j_fv, nat, body);
        let with_b = d.lam_fv(b_fv, carrier, with_j);
        let with_a = d.lam_fv(a_fv, carrier, with_b);
        d.lam_fv(f_fv, func_ty, with_a)
    };
    let ty = mesh_max_ty(d, p);
    let _ = anon;
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mesh_max,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// Land `CReal.meshMax`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_max(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_mesh_max_def(d, p)
}
