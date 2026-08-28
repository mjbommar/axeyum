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
//! **Also landed this session: `CReal.meshMax_step_le` and
//! `CReal.meshMax_mono`** (rungs 3 and 4 below), both first-attempt kernel
//! accepts. **Still not landed: `CReal.supOn` itself**, and therefore none of
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
//! - **Rung 3, the order half — LANDED, and the plan below was subtly
//!   WRONG about its statement.** The actual, kernel-accepted signature is
//!   `meshMax_step_le : ∀ F a b j, UniformlyContinuousOn F a b → le a b → le
//!   (meshMax F a b j) (meshMax F a b (Nat.succ j))` — **not** hypothesis-free
//!   as first planned. `F` applied to the two `Equiv`-but-not-equal mesh
//!   points needs `F` to respect `Equiv`, which is exactly
//!   [`CRealPrelude::congr_of_uniformly_continuous`] and is FALSE for an
//!   arbitrary `F` with no continuity witness. This is NOT an instance of
//!   [`CReal.mono_of_le_succ`](super::CRealPrelude::mono_of_le_succ) the way
//!   `maxRange_mono` is (`mono_of_le_succ` holds the SAMPLING FUNCTION fixed
//!   and varies only `maxRange`'s own bound; here both the sampling function
//!   AND the bound change together as `j` grows). Built from
//!   [`CRealPrelude::max_range_transport`], induction on an AUXILIARY index
//!   `k` (motive `fun k => Nat.le k n → le (maxRange f k) (maxRange g n')`),
//!   base case via [`CRealPrelude::maxRange_ub`] plus
//!   [`CRealPrelude::le_congr`], step case via
//!   [`CRealPrelude::max_le`](super::CRealPrelude::max_le) combining the IH
//!   with a fresh `maxRange_ub` instance — see [`declare_max_range_transport_thm`]
//!   for that combinator's own construction. Instantiated at `e(i) := add i
//!   i` (built ADDITIVELY, matching `meshLevelCount`'s own convention — not
//!   `mul 2 i` as first planned, which would have needed a `Nat.mul`
//!   dependency this file otherwise avoids entirely), `n := meshLevelCount
//!   j`, `n' := meshLevelCount (succ j)` (`hbound` is pure `Nat` order
//!   algebra: `add_le_add_left`/`_right` plus `le_succ`, `le_trans`). The
//!   `Equiv` hypothesis places both sample points in `[a, b]` via
//!   [`CRealPrelude::riemann_sample_in_bounds`] (the same mesh-point shape
//!   `riemannSum` uses) and closes with
//!   [`CRealPrelude::congr_of_uniformly_continuous`] against
//!   [`mesh_sample_transport`]'s point-level `Equiv (meshSamplePoint a Δⱼ i)
//!   (meshSamplePoint a Δⱼ' (add i i))` — built from `ofNat (add i i) ~ add
//!   (ofNat i) (ofNat i)` ([`CRealPrelude::of_nat_add`], not `of_nat_mul` as
//!   first planned), [`right_distrib`]/[`CRealPrelude::left_distrib`], and
//!   [`mesh_delta_halve`]'s `Δⱼ' + Δⱼ' ~ Δⱼ` (via `Rat.natDivSucc_add` fusing
//!   the sum, then `Rat.natDivSucc_halve` rewritten along a small
//!   `mul 2 m = add m m` bridge lemma — not `natDivSucc_scale`/`_mul` as
//!   first planned, which multiply rather than add and so do not match
//!   `meshLevelCount`'s additive doubling directly).
//! - **Rung 4, general monotonicity — LANDED**, for free once rung 3 lands:
//!   `meshMax_mono : ∀ F a b, UniformlyContinuousOn F a b → le a b → ∀ j j',
//!   Nat.le j j' → le (meshMax F a b j) (meshMax F a b j')` (`F`/`a`/`b`/the
//!   continuity witness/`le a b` closed over rather than varying, since
//!   rung 3's hypotheses are needed at every adjacent step), by
//!   [`CRealPrelude::mono_of_le_succ`] applied to `fun j => meshMax F a b j`
//!   with rung 3 as the adjacent step — EXACTLY
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
//! This plan was grounded against the kernel's actual API, and rungs 1–4 have
//! now all built cleanly on the first attempt by mirroring
//! `declare_max_range`'s and `integral.rs`'s existing shapes exactly rather
//! than composing primitives from scratch — the same held for rung 3's own
//! sub-lemmas ([`mesh_delta_halve`], [`mesh_sample_transport`]), each of
//! which needed one correction against the ORIGINAL plan above (documented
//! inline at rung 3: additive doubling and `natDivSucc_add`/`_halve` in
//! place of the originally planned multiplicative route, and an added
//! `UniformlyContinuousOn`/`le a b` hypothesis the original statement
//! omitted). **Rung 5, the accuracy-selection scheme, is the next concrete
//! task** — the first rung where continuity's actual QUANTITATIVE content
//! (the modulus, not just `Equiv`-respecting) is used, and the harmonic-vs.
//! summable trap it documents above is real and unverified against the
//! kernel until that rung is built.

#![allow(clippy::doc_markdown, clippy::too_many_arguments)]

use super::ring_helpers::right_distrib;
use super::{CRealPrelude, cadd, cle, creal_ty, embed};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{nat_rewrite_prop, radd, rat_eq_rewrite, req, rtrans};

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

// ---------------------------------------------------------------------------
// `CReal.meshMax_step_le` -- rung 3, the order half: adjacent mesh levels are
// ordered, for a function uniformly continuous on `[a, b]`. See this
// module's own documentation, "Rung 3, the order half", and the correction
// to it recorded there: this needs `UniformlyContinuousOn F a b` and `le a
// b` after all (`F` applied to two `Equiv`-but-not-equal mesh points needs
// `F` to respect `Equiv`, which is exactly
// [`CRealPrelude::congr_of_uniformly_continuous`] and is FALSE for an
// arbitrary `F` with no continuity hypothesis).
// ---------------------------------------------------------------------------

/// `Eq Nat (mul (Nat.succ (Nat.succ Nat.zero)) m) (add m m)` -- `2·m = m + m`,
/// built from `Nat.succ_mul` (`mul (succ n) m = add (mul n m) m`, at `n :=
/// 1`) and `Nat.one_mul`, exactly the pattern `nat_prelude/factorization.rs`
/// uses for the same identity (re-derived here per this development's
/// convention of not importing another file's private helper).
fn nat_two_mul_eq_add(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let nat_p = p.rat.int.nat;
    let one_v = d.num(1);
    let sm = d.lemma(nat_p.succ_mul, &[one_v, m]);
    // sm : Eq (mul (succ one_v) m) (add (mul one_v m) m) -- LHS is `mul (num
    // 2) m` since `succ one_v` and `num 2` are the same interned term.
    let one_mul_m = d.lemma(nat_p.one_mul, &[m]); // Eq (mul one_v m) m
    let one_m = NatOps::mul(d, one_v, m);
    let cong_add = NatOps::congr(d, one_m, m, one_mul_m, &|d, t| NatOps::add(d, t, m));
    // cong_add : Eq (add one_m m) (add m m)
    let add_one_m_m = NatOps::add(d, one_m, m);
    let m_m = NatOps::add(d, m, m);
    let two_v = d.num(2);
    let two_m = NatOps::mul(d, two_v, m);
    NatOps::trans(d, two_m, add_one_m_m, m_m, sm, cong_add)
}

/// `Equiv (add Δⱼ' Δⱼ') Δⱼ`, where `Δⱼ := meshDelta a b (meshLevelCount j)`
/// and `Δⱼ' := meshDelta a b (meshLevelCount (Nat.succ j))` -- the mesh width
/// exactly halves from level `j` to level `j+1`.
///
/// Rat-level core: `natDivSucc 1 (meshLevelCount (succ j)) + natDivSucc 1
/// (meshLevelCount (succ j)) = natDivSucc 1 (meshLevelCount j)`, via
/// `Rat.natDivSucc_add` (fusing the sum into `natDivSucc 2 …`) then
/// `Rat.natDivSucc_halve` (`natDivSucc 2 (succ (mul 2 m)) = natDivSucc 1 m`)
/// rewritten along [`nat_two_mul_eq_add`] to replace the multiplicative
/// index `succ (mul 2 m)` with the additive one `succ (add m m)` --
/// `meshLevelCount (succ j)`'s own ι-reduction, since `meshLevelCount` is
/// built additively (`add x x`, not `mul 2 x`, per this file's own
/// `meshLevelCount` documentation). Lifted to `CReal` via `CReal.ofRat_add`
/// and `CReal.left_distrib`.
fn mesh_delta_halve(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    j: ExprId,
) -> ExprId {
    let rat = p.rat;
    let mlc_j = d.const_app(p.mesh_level_count, &[j]);
    let sj = d.succ(j);
    let mlc_sj = d.const_app(p.mesh_level_count, &[sj]);

    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let q = d.const_app(rat.nat_div_succ, &[one_nat, mlc_sj]);
    let target_rat = d.const_app(rat.nat_div_succ, &[one_nat, mlc_j]);

    // Rat level: Eq Rat (radd q q) target_rat.
    let add_fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, mlc_sj]);
    // add_fuse : Eq Rat (radd q q) (natDivSucc (add 1 1) mlc_sj)
    let radd_qq = radd(d, q, q);
    let one_plus_one = NatOps::add(d, one_nat, one_nat);
    let fused_idx = d.const_app(rat.nat_div_succ, &[one_plus_one, mlc_sj]);

    let two_mul_eq = nat_two_mul_eq_add(d, p, mlc_j); // Eq Nat (mul 2 mlc_j) (add mlc_j mlc_j)
    let mul2mlcj = NatOps::mul(d, two_nat, mlc_j);
    let addmlcjmlcj = NatOps::add(d, mlc_j, mlc_j);
    let midx = d.succ(mul2mlcj);
    let ridx = d.succ(addmlcjmlcj);
    let bridge_nat = NatOps::congr(d, mul2mlcj, addmlcjmlcj, two_mul_eq, &|d, t| d.succ(t));
    // bridge_nat : Eq Nat midx ridx

    let halve = d.lemma(rat.nat_div_succ_halve, &[mlc_j]); // Eq Rat (natDivSucc 2 midx) target_rat
    let halve_at_ridx = nat_rewrite_prop(d, midx, ridx, bridge_nat, halve, &|d, t| {
        let lhs = d.const_app(rat.nat_div_succ, &[two_nat, t]);
        req(d, lhs, target_rat)
    });
    // halve_at_ridx : Eq Rat (natDivSucc 2 ridx) target_rat -- ridx is defeq
    // mlc_sj (meshLevelCount's own ι-reduction), so this and `add_fuse`
    // chain at the shared middle term up to defeq.
    let rat_eq = rtrans(d, radd_qq, fused_idx, target_rat, add_fuse, halve_at_ridx);
    // rat_eq : Eq Rat (radd q q) target_rat

    // Lift to CReal: Equiv (add (embed q) (embed q)) (embed target_rat).
    let of_rat_add_step = d.lemma(p.of_rat_add, &[q, q]);
    // of_rat_add_step : Equiv (add (embed q) (embed q)) (embed (radd q q))
    let embed_level = rat_eq_rewrite(d, radd_qq, target_rat, rat_eq, of_rat_add_step, &|d, t| {
        let embed_q = embed(d, p, q);
        let sum_real = cadd(d, p, embed_q, embed_q);
        let embedded = embed(d, p, t);
        cequiv(d, p, sum_real, embedded)
    });
    // embed_level : Equiv (add (embed q) (embed q)) (embed target_rat)

    // Multiply through by the shared width factor.
    let delta_j = mesh_delta(d, p, a, b, mlc_j);
    let delta_sj = mesh_delta(d, p, a, b, mlc_sj);
    let width = {
        let na = cneg(d, p, a);
        cadd(d, p, b, na)
    };
    let embed_q = embed(d, p, q);
    let embed_target = embed(d, p, target_rat);
    let sum_embed = cadd(d, p, embed_q, embed_q);

    let refl_width = d.lemma(p.equiv_refl, &[width]);
    let mul_congr_step = d.lemma(
        p.mul_congr,
        &[
            width,
            width,
            sum_embed,
            embed_target,
            refl_width,
            embed_level,
        ],
    );
    // mul_congr_step : Equiv (mul width sum_embed) (mul width embed_target)
    //                = Equiv (mul width sum_embed) delta_j

    let dist_left = d.lemma(p.left_distrib, &[width, embed_q, embed_q]);
    // dist_left : Equiv (mul width sum_embed) (add (mul width embed_q) (mul width embed_q))
    //           = Equiv (mul width sum_embed) (add delta_sj delta_sj)
    let mul_width_sum = cmul(d, p, width, sum_embed);
    let add_delta_sj_delta_sj = cadd(d, p, delta_sj, delta_sj);
    let dist_left_symm = d.lemma(
        p.equiv_symm,
        &[mul_width_sum, add_delta_sj_delta_sj, dist_left],
    );
    // dist_left_symm : Equiv (add delta_sj delta_sj) (mul width sum_embed)

    d.lemma(
        p.equiv_trans,
        &[
            add_delta_sj_delta_sj,
            mul_width_sum,
            delta_j,
            dist_left_symm,
            mul_congr_step,
        ],
    )
    // : Equiv (add delta_sj delta_sj) delta_j
}

/// `Equiv (meshSamplePoint a Δⱼ i) (meshSamplePoint a Δⱼ' (add i i))` -- the
/// level-`j` coarse sample point at index `i` is `CReal.Equiv` to the
/// level-`(j+1)` fine sample point at index `2i` (built additively as `add i
/// i`). Route: `ofNat (add i i) ~ add (ofNat i) (ofNat i)`
/// ([`CRealPrelude::of_nat_add`]), distribute across `Δⱼ'`
/// ([`right_distrib`]), refactor the resulting sum back through `ofNat i`
/// ([`CRealPrelude::left_distrib`], reversed), close the `Δⱼ' + Δⱼ' ~ Δⱼ`
/// gap via [`mesh_delta_halve`], then lift across the shared `a +` via
/// [`CRealPrelude::add_congr`].
fn mesh_sample_transport(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    j: ExprId,
    i: ExprId,
) -> ExprId {
    let mlc_j = d.const_app(p.mesh_level_count, &[j]);
    let sj = d.succ(j);
    let mlc_sj = d.const_app(p.mesh_level_count, &[sj]);
    let delta_j = mesh_delta(d, p, a, b, mlc_j);
    let delta_sj = mesh_delta(d, p, a, b, mlc_sj);
    let ii = NatOps::add(d, i, i);

    let of_nat_i = d.const_app(p.of_nat, &[i]);
    let of_nat_ii = d.const_app(p.of_nat, &[ii]);
    let sum_oi = cadd(d, p, of_nat_i, of_nat_i);

    let of_nat_add_step = d.lemma(p.of_nat_add, &[i, i]);
    // of_nat_add_step : Equiv (ofNat (add i i)) (add (ofNat i) (ofNat i))

    let refl_delta_sj = d.lemma(p.equiv_refl, &[delta_sj]);
    let term_a = cmul(d, p, of_nat_ii, delta_sj); // ofNat(i+i) * delta_sj
    let term_b = cmul(d, p, sum_oi, delta_sj);
    let step2 = d.lemma(
        p.mul_congr,
        &[
            of_nat_ii,
            sum_oi,
            delta_sj,
            delta_sj,
            of_nat_add_step,
            refl_delta_sj,
        ],
    );
    // step2 : Equiv term_a term_b

    let step3 = right_distrib(d, p, of_nat_i, of_nat_i, delta_sj);
    // step3 : Equiv term_b (add (mul of_nat_i delta_sj) (mul of_nat_i delta_sj))
    let oi_delta_sj = cmul(d, p, of_nat_i, delta_sj);
    let term_c = cadd(d, p, oi_delta_sj, oi_delta_sj);
    let step23 = d.lemma(p.equiv_trans, &[term_a, term_b, term_c, step2, step3]);
    // step23 : Equiv term_a term_c

    let sum_delta_sj = cadd(d, p, delta_sj, delta_sj);
    let oi_sum_delta_sj = cmul(d, p, of_nat_i, sum_delta_sj);
    let dist2 = d.lemma(p.left_distrib, &[of_nat_i, delta_sj, delta_sj]);
    // dist2 : Equiv oi_sum_delta_sj term_c
    let dist2_symm = d.lemma(p.equiv_symm, &[oi_sum_delta_sj, term_c, dist2]);
    // dist2_symm : Equiv term_c oi_sum_delta_sj

    let step234 = d.lemma(
        p.equiv_trans,
        &[term_a, term_c, oi_sum_delta_sj, step23, dist2_symm],
    );
    // step234 : Equiv term_a oi_sum_delta_sj

    let halve = mesh_delta_halve(d, p, a, b, j); // Equiv sum_delta_sj delta_j
    let refl_oi = d.lemma(p.equiv_refl, &[of_nat_i]);
    let term_final = cmul(d, p, of_nat_i, delta_j); // ofNat(i) * delta_j
    let step6 = d.lemma(
        p.mul_congr,
        &[of_nat_i, of_nat_i, sum_delta_sj, delta_j, refl_oi, halve],
    );
    // step6 : Equiv oi_sum_delta_sj term_final

    let step2346 = d.lemma(
        p.equiv_trans,
        &[term_a, oi_sum_delta_sj, term_final, step234, step6],
    );
    // step2346 : Equiv term_a term_final

    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let step_final = d.lemma(p.add_congr, &[a, a, term_a, term_final, refl_a, step2346]);
    // step_final : Equiv (add a term_a) (add a term_final)
    //            = Equiv (meshSamplePoint a delta_sj ii) (meshSamplePoint a delta_j i)

    let sp_sj = mesh_sample_point(d, p, a, delta_sj, ii);
    let sp_j = mesh_sample_point(d, p, a, delta_j, i);
    d.lemma(p.equiv_symm, &[sp_sj, sp_j, step_final])
    // : Equiv sp_j sp_sj
}

/// `CReal.meshMax_step_le : ∀ F a b j, UniformlyContinuousOn F a b → le a b →
/// le (meshMax F a b j) (meshMax F a b (Nat.succ j))` -- rung 3.
///
/// Instantiates [`CRealPrelude::max_range_transport`] at the two mesh
/// samplers (`f := fun i => F (meshSamplePoint a Δⱼ i)`, `g := fun i => F
/// (meshSamplePoint a Δⱼ' i)`), bounds `n := meshLevelCount j`, `n' :=
/// meshLevelCount (succ j)`, and index embedding `e := fun i => add i i`.
/// `hbound` is pure `Nat` order algebra (`add_le_add_left/_right` plus
/// `le_succ`, `le_trans`); `heq` places both sample points in `[a, b]` via
/// [`CRealPrelude::riemann_sample_in_bounds`] (the same mesh-point shape
/// `riemannSum` uses) and closes with
/// [`CRealPrelude::congr_of_uniformly_continuous`] against
/// [`mesh_sample_transport`]'s point-level `Equiv`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_mesh_max_step_le_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);
    let nat_p = p.rat.int.nat;
    let logic = p.rat.int.logic;

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let mlc_j = d.const_app(p.mesh_level_count, &[j]);
    let sj = d.succ(j);
    let mlc_sj = d.const_app(p.mesh_level_count, &[sj]);
    let delta_j = mesh_delta(d, p, a, b, mlc_j);
    let delta_sj = mesh_delta(d, p, a, b, mlc_sj);

    let f_sampler = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = mesh_sample_point(d, p, a, delta_j, i);
        let fx = d.apply(f, &[sp]);
        d.lam_fv(i_fv, nat, fx)
    };
    let g_sampler = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let sp = mesh_sample_point(d, p, a, delta_sj, i);
        let fx = d.apply(f, &[sp]);
        d.lam_fv(i_fv, nat, fx)
    };
    let e_fn = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ei = NatOps::add(d, i, i);
        d.lam_fv(i_fv, nat, ei)
    };

    // hbound : ∀ i, Nat.le i mlc_j → Nat.le (add i i) mlc_sj.
    let hbound = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.le(i, mlc_j);

        let step1 = d.lemma(nat_p.add_le_add_right, &[i, i, mlc_j, hi]);
        // step1 : Le (add i i) (add mlc_j i)
        let step2 = d.lemma(nat_p.add_le_add_left, &[mlc_j, i, mlc_j, hi]);
        // step2 : Le (add mlc_j i) (add mlc_j mlc_j)
        let ii = NatOps::add(d, i, i);
        let mm = NatOps::add(d, mlc_j, i);
        let mm2 = NatOps::add(d, mlc_j, mlc_j);
        let combined = d.lemma(nat_p.le_trans, &[ii, mm, mm2, step1, step2]);
        let step3 = d.lemma(nat_p.le_succ, &[mm2]);
        let smm2 = d.succ(mm2);
        let final_le = d.lemma(nat_p.le_trans, &[ii, mm2, smm2, combined, step3]);
        // final_le : Le (add i i) (succ (add mlc_j mlc_j)) -- defeq mlc_sj

        let body = d.lam_fv(hi_fv, hi_ty, final_le);
        d.lam_fv(i_fv, nat, body)
    };

    // heq : ∀ i, Nat.le i mlc_j → Equiv (f_sampler i) (g_sampler (add i i)).
    let heq = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.le(i, mlc_j);

        let sp_j = mesh_sample_point(d, p, a, delta_j, i);
        let ii = NatOps::add(d, i, i);
        let sp_sj = mesh_sample_point(d, p, a, delta_sj, ii);

        let hlt_i = d.lemma(nat_p.lt_succ_of_le, &[i, mlc_j, hi]);
        let and_j = d.const_app(p.riemann_sample_in_bounds, &[a, b, mlc_j, i, hab, hlt_i]);
        let a_le_spj = cle(d, p, a, sp_j);
        let spj_le_b = cle(d, p, sp_j, b);
        let hax_j = d.const_app(logic.and_left, &[a_le_spj, spj_le_b, and_j]);
        let hxb_j = d.const_app(logic.and_right, &[a_le_spj, spj_le_b, and_j]);

        let hbound_i = d.apply(hbound, &[i, hi]);
        let hlt_ii = d.lemma(nat_p.lt_succ_of_le, &[ii, mlc_sj, hbound_i]);
        let and_sj = d.const_app(p.riemann_sample_in_bounds, &[a, b, mlc_sj, ii, hab, hlt_ii]);
        let a_le_spsj = cle(d, p, a, sp_sj);
        let spsj_le_b = cle(d, p, sp_sj, b);
        let hay_sj = d.const_app(logic.and_left, &[a_le_spsj, spsj_le_b, and_sj]);
        let hyb_sj = d.const_app(logic.and_right, &[a_le_spsj, spsj_le_b, and_sj]);

        let point_equiv = mesh_sample_transport(d, p, a, b, j, i);

        let concl = d.lemma(
            p.congr_of_uniformly_continuous,
            &[
                f,
                a,
                b,
                u,
                sp_j,
                sp_sj,
                hax_j,
                hxb_j,
                hay_sj,
                hyb_sj,
                point_equiv,
            ],
        );

        let body = d.lam_fv(hi_fv, hi_ty, concl);
        d.lam_fv(i_fv, nat, body)
    };

    let transport_applied = d.const_app(
        p.max_range_transport,
        &[f_sampler, g_sampler, mlc_j, mlc_sj, e_fn, hbound, heq],
    );

    let mesh_j = d.const_app(p.mesh_max, &[f, a, b, j]);
    let mesh_sj = d.const_app(p.mesh_max, &[f, a, b, sj]);
    let conclusion = cle(d, p, mesh_j, mesh_sj);

    let ty = {
        let after_hab = d.arrow(hab_ty, conclusion);
        let after_u = d.arrow(u_ty, after_hab);
        let over_j = d.pi_fv(j_fv, nat, after_u);
        let over_b = d.pi_fv(b_fv, carrier, over_j);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, func_ty, over_a)
    };
    let value = {
        let after_hab = d.lam_fv(hab_fv, hab_ty, transport_applied);
        let after_u = d.lam_fv(u_fv, u_ty, after_hab);
        let over_j = d.lam_fv(j_fv, nat, after_u);
        let over_b = d.lam_fv(b_fv, carrier, over_j);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, func_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_max_step_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.meshMax_step_le` alone (a one-declaration `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_max_step_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_max_step_le_thm(d, p)
}

/// `CReal.meshMax_mono : ∀ F a b, UniformlyContinuousOn F a b → le a b → ∀ j
/// j', Nat.le j j' → le (meshMax F a b j) (meshMax F a b j')` -- rung 4,
/// general monotonicity, for free from rung 3 via
/// [`CRealPrelude::mono_of_le_succ`] applied to `fun k => meshMax F a b k`
/// with [`declare_mesh_max_step_le`]'s theorem as the adjacent step --
/// EXACTLY [`declare_max_range_mono`]'s own construction, one level up (`F`,
/// `a`, `b`, `u`, `hab` closed over rather than varying).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
fn declare_mesh_max_mono_thm(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let func_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let hab_ty = cle(d, p, a, b);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    let mesh_f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.mesh_max, &[f, a, b, k]);
        d.lam_fv(k_fv, nat, body)
    };
    let adjacent = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.const_app(p.mesh_max_step_le, &[f, a, b, n, u, hab]);
        d.lam_fv(n_fv, nat, body)
    };
    let mono = d.const_app(p.mono_of_le_succ, &[mesh_f, adjacent]);

    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let jp_fv = d.fresh_fvar();
    let jp = d.kernel().fvar(jp_fv);
    let hjj_fv = d.fresh_fvar();
    let hjj = d.kernel().fvar(hjj_fv);
    let hjj_ty = d.le(j, jp);
    let applied = d.apply(mono, &[j, jp, hjj]);

    let mesh_j = d.const_app(p.mesh_max, &[f, a, b, j]);
    let mesh_jp = d.const_app(p.mesh_max, &[f, a, b, jp]);
    let conclusion = cle(d, p, mesh_j, mesh_jp);

    let ty = {
        let anon = d.anon_name();
        let out = d
            .kernel()
            .pi(anon, hjj_ty, conclusion, crate::BinderInfo::Default);
        let out = d.pi_fv(jp_fv, nat, out);
        let out = d.pi_fv(j_fv, nat, out);
        let out = d.arrow(hab_ty, out);
        let out = d.arrow(u_ty, out);
        let out = d.pi_fv(b_fv, carrier, out);
        let out = d.pi_fv(a_fv, carrier, out);
        d.pi_fv(f_fv, func_ty, out)
    };
    let value = {
        let out = d.lam_fv(hjj_fv, hjj_ty, applied);
        let out = d.lam_fv(jp_fv, nat, out);
        let out = d.lam_fv(j_fv, nat, out);
        let out = d.lam_fv(hab_fv, hab_ty, out);
        let out = d.lam_fv(u_fv, u_ty, out);
        let out = d.lam_fv(b_fv, carrier, out);
        let out = d.lam_fv(a_fv, carrier, out);
        d.lam_fv(f_fv, func_ty, out)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mesh_max_mono,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.meshMax_mono` alone (a one-declaration `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_mesh_max_mono(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_mesh_max_mono_thm(d, p)
}

// ---------------------------------------------------------------------------
// `CReal.expOfModulus` / `CReal.trueExpOfModulus` -- rung 5, the
// accuracy-selection scheme (where continuity's quantitative content, the
// modulus, first enters). See this module's own documentation, "Rung 5, the
// accuracy-selection scheme", for the harmonic-vs-summable finding this
// schedule exists to fix.
// ---------------------------------------------------------------------------

/// `CReal.expOfModulus : (Nat → Nat) → Nat → Nat := fun m k => Nat.size (m
/// (meshLevelCount k))` — the per-level accuracy request: `Nat.size` turns
/// an arbitrary modulus value `m (meshLevelCount k)` into a power-of-two
/// EXPONENT that dominates it via `Nat.lt_pow_size : ∀ n, Lt n (pow 2 (size
/// n))`, with no `Nat.div`/search. Left generic over `m : Nat → Nat` rather
/// than tied to a specific `UniformlyContinuousOn` witness — callers apply
/// it at `m := UniformlyContinuousOn.modulus F a b u` — so this and
/// [`declare_true_exp_of_modulus`] are pure `Nat`-level machinery, reusable
/// beyond this file's own `F`/`a`/`b`.
fn declare_exp_of_modulus_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);
    let nat_p = p.rat.int.nat;

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let mlc_k = d.const_app(p.mesh_level_count, &[k]);
    let m_at = d.apply(m, &[mlc_k]);
    let sized = d.const_app(nat_p.size, &[m_at]);

    let value = {
        let with_k = d.lam_fv(k_fv, nat, sized);
        d.lam_fv(m_fv, nat_fn, with_k)
    };
    let ty = {
        let over_k = d.arrow(nat, nat);
        d.arrow(nat_fn, over_k)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.exp_of_modulus,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// Land `CReal.expOfModulus` alone (a one-declaration `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_exp_of_modulus(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_exp_of_modulus_def(d, p)
}

/// `CReal.trueExpOfModulus : (Nat → Nat) → Nat → Nat`, `Nat.rec`-structured
/// on the level and closed over `m` (mirrors [`declare_max_range_def`]'s own
/// shape, one type down): `trueExpOfModulus m 0 := expOfModulus m 0`,
/// `trueExpOfModulus m (succ k) := add (trueExpOfModulus m k) (expOfModulus
/// m (succ k))` — the running-sum accumulator that forces monotonicity onto
/// [`declare_exp_of_modulus_def`]'s own not-necessarily-monotone sequence
/// (an arbitrary modulus need not itself be monotone). Built with
/// `Nat.add`, never `Nat.max`: **this kernel's `Nat` prelude has no
/// `Nat.max`**.
fn declare_true_exp_of_modulus_def(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);
    let anon = d.anon_name();
    let one_level = d.level_one();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = d.kernel().lam(anon, nat, nat, crate::BinderInfo::Default);
    let zero_n = d.zero();
    let minor_zero = d.const_app(p.exp_of_modulus, &[m, zero_n]);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let sj = d.succ(j);
        let exp_sj = d.const_app(p.exp_of_modulus, &[m, sj]);
        let body = NatOps::add(d, ih, exp_sj);
        let inner = d.lam_fv(ih_fv, nat, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, k]);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        d.lam_fv(m_fv, nat_fn, with_k)
    };
    let ty = {
        let over_k = d.arrow(nat, nat);
        d.arrow(nat_fn, over_k)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.true_exp_of_modulus,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAX_RANGE_HEIGHT),
    })
}

/// `CReal.trueExpOfModulus_zero`/`CReal.trueExpOfModulus_succ`: the defining
/// equations of [`declare_true_exp_of_modulus_def`], each closed by
/// `Eq.refl` alone since `trueExpOfModulus`'s `Nat.rec` application
/// ι-reduces on both minor premises (mirrors
/// [`declare_max_range_equations`]).
fn declare_true_exp_of_modulus_equations(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);

    // trueExpOfModulus_zero : ∀ m,
    //   Eq Nat (trueExpOfModulus m zero) (expOfModulus m zero).
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let zero_n = d.zero();
        let lhs = d.const_app(p.true_exp_of_modulus, &[m, zero_n]);
        let rhs = d.const_app(p.exp_of_modulus, &[m, zero_n]);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        let value = d.lam_fv(m_fv, nat_fn, proof);
        let ty = d.pi_fv(m_fv, nat_fn, stmt);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.true_exp_of_modulus_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // trueExpOfModulus_succ : ∀ m k,
    //   Eq Nat (trueExpOfModulus m (succ k))
    //          (add (trueExpOfModulus m k) (expOfModulus m (succ k))).
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let lhs = d.const_app(p.true_exp_of_modulus, &[m, sk]);
        let te_k = d.const_app(p.true_exp_of_modulus, &[m, k]);
        let exp_sk = d.const_app(p.exp_of_modulus, &[m, sk]);
        let rhs = NatOps::add(d, te_k, exp_sk);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        let value = {
            let with_k = d.lam_fv(k_fv, nat, proof);
            d.lam_fv(m_fv, nat_fn, with_k)
        };
        let ty = {
            let over_k = d.pi_fv(k_fv, nat, stmt);
            d.pi_fv(m_fv, nat_fn, over_k)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.true_exp_of_modulus_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// Land `CReal.trueExpOfModulus` and its two defining equations.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_true_exp_of_modulus(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_true_exp_of_modulus_def(d, p)?;
    declare_true_exp_of_modulus_equations(d, p)
}

/// `CReal.trueExpOfModulus_step_le : ∀ m k, Nat.le (trueExpOfModulus m k)
/// (trueExpOfModulus m (succ k))` — the adjacent-step half of
/// monotonicity. `trueExpOfModulus m (succ k)` ι-reduces to `add
/// (trueExpOfModulus m k) (expOfModulus m (succ k))`
/// ([`declare_true_exp_of_modulus_equations`]'s own `_succ` statement, by
/// that same ι-reduction), and `Nat.le_add_right (trueExpOfModulus m k)
/// (expOfModulus m (succ k))` is already exactly the needed bound — no
/// rewriting needed, only defeq (mirrors the `hbound` step in
/// [`declare_mesh_max_step_le_thm`]).
fn declare_true_exp_of_modulus_step_le_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);
    let nat_p = p.rat.int.nat;

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let te_k = d.const_app(p.true_exp_of_modulus, &[m, k]);
    let sk = d.succ(k);
    let exp_sk = d.const_app(p.exp_of_modulus, &[m, sk]);
    // bound : Le te_k (add te_k exp_sk) -- defeq to Le te_k (trueExpOfModulus m (succ k)).
    let bound = d.lemma(nat_p.le_add_right, &[te_k, exp_sk]);

    let te_sk = d.const_app(p.true_exp_of_modulus, &[m, sk]);
    let conclusion = d.le(te_k, te_sk);

    let ty = {
        let over_k = d.pi_fv(k_fv, nat, conclusion);
        d.pi_fv(m_fv, nat_fn, over_k)
    };
    let value = {
        let with_k = d.lam_fv(k_fv, nat, bound);
        d.lam_fv(m_fv, nat_fn, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.true_exp_of_modulus_step_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.trueExpOfModulus_step_le` alone (a one-declaration
/// `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_true_exp_of_modulus_step_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_true_exp_of_modulus_step_le_thm(d, p)
}

/// `CReal.trueExpOfModulus_mono : ∀ m j j', Nat.le j j' → Nat.le
/// (trueExpOfModulus m j) (trueExpOfModulus m j')` — general monotonicity,
/// free from [`declare_true_exp_of_modulus_step_le`] via
/// `Nat.monotone_of_le_succ` (the `Nat`-level twin of
/// [`CRealPrelude::mono_of_le_succ`]) — EXACTLY
/// [`declare_mesh_max_mono_thm`]'s own construction, one type down
/// (`Nat`-valued rather than `CReal`-valued, so `m` is closed over instead
/// of `F`/`a`/`b`/the continuity witness/`le a b`).
fn declare_true_exp_of_modulus_mono_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);
    let nat_p = p.rat.int.nat;

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let te_f = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.const_app(p.true_exp_of_modulus, &[m, k]);
        d.lam_fv(k_fv, nat, body)
    };
    let adjacent = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.const_app(p.true_exp_of_modulus_step_le, &[m, n]);
        d.lam_fv(n_fv, nat, body)
    };
    let mono = d.lemma(nat_p.monotone_of_le_succ, &[te_f, adjacent]);

    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let jp_fv = d.fresh_fvar();
    let jp = d.kernel().fvar(jp_fv);
    let hjj_fv = d.fresh_fvar();
    let hjj = d.kernel().fvar(hjj_fv);
    let hjj_ty = d.le(j, jp);
    let applied = d.apply(mono, &[j, jp, hjj]);

    let te_j = d.const_app(p.true_exp_of_modulus, &[m, j]);
    let te_jp = d.const_app(p.true_exp_of_modulus, &[m, jp]);
    let conclusion = d.le(te_j, te_jp);

    let ty = {
        let anon = d.anon_name();
        let out = d
            .kernel()
            .pi(anon, hjj_ty, conclusion, crate::BinderInfo::Default);
        let out = d.pi_fv(jp_fv, nat, out);
        let out = d.pi_fv(j_fv, nat, out);
        d.pi_fv(m_fv, nat_fn, out)
    };
    let value = {
        let out = d.lam_fv(hjj_fv, hjj_ty, applied);
        let out = d.lam_fv(jp_fv, nat, out);
        let out = d.lam_fv(j_fv, nat, out);
        d.lam_fv(m_fv, nat_fn, out)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.true_exp_of_modulus_mono,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.trueExpOfModulus_mono` alone (a one-declaration `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_true_exp_of_modulus_mono(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_true_exp_of_modulus_mono_thm(d, p)
}

/// `CReal.expOfModulus_le_trueExpOfModulus : ∀ m k, Nat.le (expOfModulus m
/// k) (trueExpOfModulus m k)` — the accumulator is always at least as fine
/// as the single level it was built to cover (needed by rung 6's per-level
/// gap bound: the modulus's own spec is stated at accuracy request
/// `meshLevelCount k`, i.e. in terms of [`declare_exp_of_modulus_def`]
/// alone, but the mesh actually sampled at level `k` is
/// `meshMax F a b (trueExpOfModulus m k)`).
///
/// Proof by induction on `k` (via [`NatOps::induct`], mirrors
/// [`declare_max_range_self_le`]'s own use of it one type up): the base
/// case is `Nat.le_refl` against [`declare_true_exp_of_modulus_equations`]'s
/// `_zero` ι-reduction (`trueExpOfModulus m 0 ≡ expOfModulus m 0`); the
/// step case needs `Le x (add y x)` from `Nat.le_add_right : Le x (add x
/// y)`, a genuine commute — no `Nat.le_add_left` exists in this kernel's
/// `Nat` prelude — closed by
/// [`crate::rat_prelude::ops::nat_rewrite_prop`] rewriting along
/// `Nat.add_comm x y : Eq Nat (add x y) (add y x)`. The inductive
/// hypothesis is available but unused: the bound holds at `succ k`
/// independently of what held at `k`, since `trueExpOfModulus m (succ k)`
/// always contains `expOfModulus m (succ k)` as an addend by construction.
fn declare_exp_of_modulus_le_true_exp_of_modulus_thm(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let nat_fn = d.arrow(nat, nat);
    let nat_p = p.rat.int.nat;

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let exp_x = d.const_app(p.exp_of_modulus, &[m, x]);
        let te_x = d.const_app(p.true_exp_of_modulus, &[m, x]);
        d.le(exp_x, te_x)
    };

    let proof = d.induct(
        &motive,
        &|d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            let exp0 = d.const_app(p.exp_of_modulus, &[m, zero_n]);
            d.lemma(nat_p.le_refl, &[exp0])
        },
        &|d: &mut IntDev<'_>, j: ExprId, _ih: ExprId| -> ExprId {
            let sj = d.succ(j);
            let x = d.const_app(p.exp_of_modulus, &[m, sj]);
            let y = d.const_app(p.true_exp_of_modulus, &[m, j]);
            let base = d.lemma(nat_p.le_add_right, &[x, y]);
            let hcomm = d.lemma(nat_p.add_comm, &[x, y]);
            let axy = NatOps::add(d, x, y);
            let ayx = NatOps::add(d, y, x);
            nat_rewrite_prop(d, axy, ayx, hcomm, base, &|d, z| d.le(x, z))
        },
        k,
    );

    let stmt = motive(d, k);
    let ty = {
        let inner = d.pi_fv(k_fv, nat, stmt);
        d.pi_fv(m_fv, nat_fn, inner)
    };
    let value = {
        let inner = d.lam_fv(k_fv, nat, proof);
        d.lam_fv(m_fv, nat_fn, inner)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.exp_of_modulus_le_true_exp_of_modulus,
        uparams: vec![],
        ty,
        value,
    })
}

/// Land `CReal.expOfModulus_le_trueExpOfModulus` alone (a one-declaration
/// `BuildStep`).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_exp_of_modulus_le_true_exp_of_modulus(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_exp_of_modulus_le_true_exp_of_modulus_thm(d, p)
}
