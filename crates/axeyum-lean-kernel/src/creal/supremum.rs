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
//! **Not landed this session: `CReal.supOn` itself**, and therefore none of
//! deliverables (a)/(b)/(c) the assignment names. This is not a hedge —
//! it is the honest outcome of a real attempt, and the obstruction is
//! concrete enough to write down precisely, which is the point of recording
//! it here rather than leaving a silent gap.
//!
//! ### Why `supOn` did not land, precisely
//!
//! `supOn` needs `CReal.mk (speedup f_lambda K) (regularity proof)`, built
//! **without** `Exists.rec` (kernel fact 1 — `K` and `f_lambda` must be
//! *concrete* data, never extracted from an existential, since they feed
//! `speedup`, a `Type`-level construction). Landing that regularity proof —
//! `∀ p q, Within (seq (f_lambda p) p − seq (f_lambda q) q) (natDivSucc K p +
//! natDivSucc K q)` for `f_lambda n := maxRange (fun i => F(meshPoint a b n
//! i)) (meshCount n)` — needs, for two *independent* accuracies `p`/`q`, a
//! bound relating `maxRange` over mesh `p` to `maxRange` over mesh `q`. That
//! bound needs, for an arbitrary point of one mesh, the *nearest point of the
//! other mesh* — a genuine "which cell" lookup.
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
//!    genuine new proof, not a two-line application.
//! 2. **A NESTED-REFINEMENT construction avoiding bucket-index entirely**,
//!    using [`Rat.natDivSucc_scale`](crate::RatPrelude::nat_div_succ_scale)
//!    and [`Rat.natDivSucc_mul`](crate::RatPrelude::nat_div_succ_mul) to make
//!    consecutive mesh levels *exactly* nest (so a refined mesh's new points
//!    are related to the coarser mesh's points by closed-form rational
//!    algebra, never a `Nat.div` search), then telescoping the resulting
//!    one-step bound (`f(n+1) ≤ f(n) + magBound(n)`, `magBound` geometric so
//!    the telescoped sum stays finite) via the *already-public*
//!    [`CReal.sumRange_cauchy_of_dominated`](super::CRealPrelude::sum_range_cauchy_of_dominated)
//!    family (`creal/series.rs`) — a genuine comparison test for `Cauchy`
//!    that exists exactly for this shape. This route was worked out in full
//!    on paper (the block-splitting `maxRange` identity, the displacement
//!    algebra, the telescoping) and involves no unproved mathematics, but
//!    assembling roughly fifteen to twenty more kernel declarations correctly
//!    — a `maxRange_block_split` combinatorial identity, the geometric mesh-
//!    count recursion, the one-step estimate, and wiring the telescope
//!    through to `regular_of_scaled_cauchy` — is comparable in scope to
//!    `creal/integral.rs`'s own cross-mesh development (`riemannSumDeepCauchy`
//!    and friends) and did not fit the remainder of this session on top of
//!    the investigation above.
//!
//! Route 2 is the one to pick up: it needs no bucket-index reuse, no
//! `Nat.div`, and every lemma it calls (`nat_div_succ_scale`,
//! `nat_div_succ_mul`, `nat_div_succ_le_scaled`, `nat_div_succ_antitone`,
//! `mono_of_le_succ`, `sum_range_telescope`, `sum_range_cauchy_of_dominated`)
//! already exists and is public.

#![allow(clippy::doc_markdown, clippy::too_many_arguments)]

use super::{CRealPrelude, cle, creal_ty};
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
