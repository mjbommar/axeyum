//! The **Archimedean crossing index**: given a positive rational step `Δ`, a
//! base point `a : CReal` and a target `c : CReal`, a COMPUTED `Nat` index
//! `i0` such that `a + i0·Δ` lands within a small, fixed slack of `c`.
//!
//! ## Why the naive statement is not what gets built
//!
//! `CReal.le` is not decidable (`creal/cotransitivity.rs`'s own module
//! documentation is the standing reference: there is no `lt_total` over the
//! reals), so `i0` cannot be found by *comparing* candidate multiples of `Δ`
//! against `c`. It has to be **computed from rational data** instead, exactly
//! the move `creal/ivt.rs`'s `ivt_bisect` and `creal/uniform_continuity.rs`'s
//! `bucketIndex` both make: sample the real value at one accuracy index,
//! read a `Rat`, and decide everything else with `Nat`/`Int` arithmetic,
//! which *is* decidable.
//!
//! `bucketIndex w k : Nat` already computes exactly this for the FIXED grid
//! `1/(k+1)` — [`bucket_index_floor_lower`](super::CRealPrelude::bucket_index_floor_lower)/
//! [`bucket_index_floor_upper`](super::CRealPrelude::bucket_index_floor_upper)
//! sandwich `w`'s clamped sample between two adjacent multiples of that grid,
//! and [`bucket_clamp_upper`](super::CRealPrelude::bucket_clamp_upper)/
//! [`bucket_clamp_lower`](super::CRealPrelude::bucket_clamp_lower) relate the
//! clamped sample back to `w` itself, within a further fixed slack. An
//! arbitrary positive rational step `Δ` is not generally a unit fraction
//! `1/(k+1)`, so this file does not extend `bucketIndex`'s recipe — it
//! **reduces to it**: rescale `w := c − a` by `Δ⁻¹` and read `bucketIndex`
//! at the FIXED grid `k := 0` (step `1`), which is exactly "which multiple of
//! `Δ` does `c − a` sit at". Composing the four `bucketIndex` closeness
//! lemmas with the algebraic identity `Δ · Δ⁻¹ = 1` (`Rat.mul_inv_cancel`)
//! turns that into a bound on `c − a` itself, hence on `c`.
//!
//! **The result is a slack statement, not the naive
//! `a + i0·Δ ≤ c ≤ a + (i0+1)·Δ`, and deliberately so** — Chapter 7's
//! `ivt_approx`/`ivt_bisect` pair (`creal/ivt.rs`) is the precedent:
//! `bucketIndex`'s own two clamp lemmas already carry a fixed slack of
//! `2/(j+1)` and `3/(j+1)` at their OWN grid (`j` the accuracy index they
//! sample at), and rescaling by `Δ⁻¹` before applying them does not remove
//! that slack, it just relocates it onto `Δ`'s own scale. Concretely, at
//! `k := 0` the accuracy index is `j = 1`, so the slack is a small constant
//! multiple of `Δ` (`≤ 2Δ` above, `≤ 1.5Δ` below) rather than shrinking with
//! any parameter the caller controls. **This is the exact pair of bounds
//! this file can actually build**; see [`declare_crossing_upper`] and
//! [`declare_crossing_lower`] for the two halves.
//!
//! ## `crossingIndex` is computed, never `∃`-derived
//!
//! `Exists.rec` is `Prop`-only and cannot produce a term whose type mentions
//! the extracted witness (`docs/mathematics-2026-08/diary-exact-root-obstruction.md`
//! is the standing reference), so `i0` cannot come from eliminating a proof
//! of `∃ i, …`. [`CrossingNames::crossing_index`] is a `Definition` — one
//! `CReal.bucketIndex` application on a rescaled argument, built the SAME
//! way for every `a`, `c`, `Δ` — never a search and never an elimination.
//!
//! ## What needs which hypothesis, and why the split is genuine
//!
//! [`declare_crossing_upper`] needs `0 < Δ` **and nothing else** — no
//! `a ≤ c` hypothesis at all. `bucketIndex`'s upper closeness lemmas
//! (`bucket_index_floor_upper`, `bucket_clamp_upper`) are both unconditional
//! (see their own doc comments: `bucket_clamp_upper` needs no sign
//! hypothesis on its argument), and scaling a `CReal.le` fact by a *positive*
//! rational preserves it regardless of `c − a`'s own sign. So `c ≤ a +
//! (crossingIndex+1+slack)·Δ` holds even when `c < a`.
//!
//! [`declare_crossing_lower`] genuinely needs `a ≤ c`, because
//! `bucket_clamp_lower`'s hypothesis is `0 ≤ w` for the value being bucketed
//! — here `w := (c−a)·Δ⁻¹`, whose sign follows `c − a`'s (since `Δ⁻¹ > 0`),
//! which is exactly what `a ≤ c` supplies (`CReal.mul_nonneg` on the two
//! nonnegative factors).
//!
//! ## Where this generalizes beyond one interval
//!
//! Every existing "combine several riemannSums" construction in
//! `creal/integral.rs` (`common_refinement`, `sharedIndexToCanonical`, the
//! `sumRange_reblock` chain, …) is pure `Nat`-refinement algebra over ONE
//! fixed interval: a refined step is an exact algebraic multiple of the
//! coarse step, and none of them relate a count on `[a,c]` to a count on
//! `[a,b]` for a general `c`. `crossingIndex` is the missing piece that
//! *does* — "which sample index does `c` fall at, counting in steps of `Δ`
//! from `a`" — landed here as a standalone, reusable fact rather than wired
//! into `CReal.integral_split`, which needs a second, larger fact (a
//! cross-width term-by-term Riemann-sum comparison via uniform continuity)
//! this file does not attempt.

use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rmul, rneg, rone, rzero};

use super::{CRealPrelude, creal_ty, sample};
use crate::Kernel;
use crate::name::NameId;

// --- small local term builders (mirrors `ring_helpers.rs`'s own convention
// of small per-module copies rather than reaching across a sibling module
// boundary for a private helper) -------------------------------------------

fn cadd(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.add, &[x, y])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn embed(d: &mut IntDev<'_>, p: CRealPrelude, r: ExprId) -> ExprId {
    d.const_app(p.of_rat, &[r])
}

fn cle(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.le, &[x, y])
}

fn cequiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.equiv, &[x, y])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn cone(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.one, vec![])
}

/// Chain `Equiv start …` through `(next, step)` pairs. Local copy of
/// `ring_helpers.rs`'s private `echain` (that module cannot be reached from
/// here — see its own doc comment on why these small chain helpers are
/// duplicated per module rather than promoted).
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

/// `w := c + (-a)` ("`c - a`"), and a proof that `Equiv (add w a) c` —
/// `(c + (-a)) + a ~ c`, via `add_assoc`, `add_comm`, `add_neg` and
/// `add_zero`. Shared by [`declare_crossing_upper`] and
/// [`declare_crossing_lower`], which both need to move the `a` they added
/// back across to the other side of a `CReal.le`.
fn base_shift(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, c: ExprId) -> (ExprId, ExprId) {
    let na = cneg(d, p, a);
    let w = cadd(d, p, c, na);

    // (-a) + a ~ a + (-a) ~ 0
    let na_a = cadd(d, p, na, a);
    let a_na = cadd(d, p, a, na);
    let h_comm = d.lemma(p.add_comm, &[na, a]); // Equiv na_a a_na
    let czero_e = czero(d, p);
    let h_addneg = d.lemma(p.add_neg, &[a]); // Equiv a_na czero
    let h_na_a_zero = echain(d, p, na_a, &[(a_na, h_comm), (czero_e, h_addneg)]);

    // c + (na + a) ~ c + 0 ~ c
    let c_naa = cadd(d, p, c, na_a);
    let c_zero = cadd(d, p, c, czero_e);
    let refl_c = d.lemma(p.equiv_refl, &[c]);
    let h_congr = d.lemma(p.add_congr, &[c, c, na_a, czero_e, refl_c, h_na_a_zero]);
    let h_addzero = d.lemma(p.add_zero, &[c]); // Equiv c_zero c

    // (w + a) ~ c + (na + a) ~ c
    let w_a = cadd(d, p, w, a);
    let h_assoc = d.lemma(p.add_assoc, &[c, na, a]); // Equiv (add (add c na) a) (add c (add na a))
    //                                                  = Equiv w_a c_naa
    let proof = echain(
        d,
        p,
        w_a,
        &[(c_naa, h_assoc), (c_zero, h_congr), (c, h_addzero)],
    );
    (w, proof)
}

/// The shared rescaled value `s := ofRat(Δ⁻¹) · (c + (-a))`, its recorded
/// pieces (`delta_embed`, `w`, `r`, `r_embed`), and `crossingIndex a c Δ :=
/// bucketIndex s 0` itself. Built identically everywhere it is needed so
/// that `CReal.crossingIndex a c delta` (a `Definition` unfolding to exactly
/// this recipe) is the SAME `ExprId` shape as what each theorem's own proof
/// constructs — see the module documentation on why two structurally
/// different representations of one value are expensive here.
struct Scaled {
    delta_embed: ExprId,
    w: ExprId,
    r: ExprId,
    r_embed: ExprId,
    s: ExprId,
    zero_nat: ExprId,
    i0: ExprId,
}

fn build_scaled(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    c: ExprId,
    delta: ExprId,
) -> Scaled {
    let na = cneg(d, p, a);
    let w = cadd(d, p, c, na);
    let r = d.const_app(p.rat.inv, &[delta]);
    let r_embed = embed(d, p, r);
    let s = cmul(d, p, r_embed, w);
    let zero_nat = d.num(0);
    let i0 = d.const_app(p.bucket_index, &[s, zero_nat]);
    let delta_embed = embed(d, p, delta);
    Scaled {
        delta_embed,
        w,
        r,
        r_embed,
        s,
        zero_nat,
        i0,
    }
}

/// `k1 := succ 0 = 1`, `j := k1*k1 = 1`, `q := max (seq s j) 0` — the SAME
/// three terms `CReal.bucketIndex`/`bucketIndexFloorLower`/`Upper`/
/// `bucketClampUpper`/`Lower` build internally at `k := 0`, rebuilt here so
/// this file's own combination steps mention the identical `ExprId`s those
/// theorems' stated types do.
fn setup0(d: &mut IntDev<'_>, p: CRealPrelude, s: ExprId, zero_nat: ExprId) -> (ExprId, ExprId) {
    let k1 = d.succ(zero_nat);
    let j = NatOps::mul(d, k1, k1);
    let wj = sample(d, p, s, j);
    let zero_rat = rzero(d, p.rat);
    let q = d.const_app(p.rat.max, &[wj, zero_rat]);
    (j, q)
}

/// `Equiv (mul delta_embed s) w`, where `s = mul (ofRat (inv delta)) w` and
/// `delta_embed = ofRat delta` — the algebraic cancellation
/// `Δ · (Δ⁻¹ · w) ~ w`, via `mul_assoc`, `Rat.mul_inv_cancel`, `of_rat_mul`,
/// `mul_congr`, `mul_comm` and `mul_one`. Needs `hpos : Rat.lt Rat.zero
/// delta` (`Rat.mul_inv_cancel`'s own hypothesis).
fn scale_cancels(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    delta: ExprId,
    delta_embed: ExprId,
    r: ExprId,
    r_embed: ExprId,
    w: ExprId,
    hpos: ExprId,
) -> ExprId {
    let s = cmul(d, p, r_embed, w);
    let a0 = cmul(d, p, delta_embed, s); // mul delta_embed s
    let mul_delta_r = cmul(d, p, delta_embed, r_embed);
    let a1 = cmul(d, p, mul_delta_r, w); // mul (mul delta_embed r_embed) w
    let h_assoc = d.lemma(p.mul_assoc, &[delta_embed, r_embed, w]); // Equiv a1 a0
    let h_assoc_rev = d.lemma(p.equiv_symm, &[a1, a0, h_assoc]); // Equiv a0 a1

    let cancel_eq = d.lemma(p.rat.mul_inv_cancel, &[delta, hpos]); // Eq (rmul delta r) rat_one
    let rmul_delta_r = rmul(d, delta, r);
    let rat_one = rone(d, p.rat);
    let of_rat_mul_step = d.lemma(p.of_rat_mul, &[delta, r]); // Equiv mul_delta_r (ofRat rmul_delta_r)

    let step_c = rat_eq_rewrite(
        d,
        rmul_delta_r,
        rat_one,
        cancel_eq,
        of_rat_mul_step,
        &|d, x| {
            let ofx = embed(d, p, x);
            cequiv(d, p, mul_delta_r, ofx)
        },
    ); // Equiv mul_delta_r (ofRat rat_one), and (ofRat rat_one) is defeq to `p.one`

    let one_e = cone(d, p);
    let refl_w = d.lemma(p.equiv_refl, &[w]);
    let a2 = cmul(d, p, one_e, w);
    let h_congr1 = d.lemma(p.mul_congr, &[mul_delta_r, one_e, w, w, step_c, refl_w]); // Equiv a1 a2

    let a3 = cmul(d, p, w, one_e);
    let h_comm2 = d.lemma(p.mul_comm, &[one_e, w]); // Equiv a2 a3
    let h_mulone = d.lemma(p.mul_one, &[w]); // Equiv a3 w

    echain(
        d,
        p,
        a0,
        &[
            (a1, h_assoc_rev),
            (a2, h_congr1),
            (a3, h_comm2),
            (w, h_mulone),
        ],
    )
}

/// `CReal.le (ofRat Rat.zero) (ofRat r)`, from `Rat.le Rat.zero r`. Shared
/// tiny lift used for both `Δ ≥ 0` and `Δ⁻¹ ≥ 0`.
fn embed_nonneg(d: &mut IntDev<'_>, p: CRealPrelude, r: ExprId, hr: ExprId) -> ExprId {
    let zero_rat = rzero(d, p.rat);
    d.lemma(p.of_rat_le, &[zero_rat, r, hr])
}

/// Admit [`CrossingNames::crossing_index`]. See the module documentation for
/// the recipe and why it is a `Definition`, never an `Exists`-derived value.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_crossing_index(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_ty_ = crate::rat_prelude::ops::rat_ty(d);
    let nat_ty = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let delta_fv = d.fresh_fvar();
    let delta = d.kernel().fvar(delta_fv);

    let scaled = build_scaled(d, p, a, c, delta);

    let value = {
        let with_delta = d.lam_fv(delta_fv, rat_ty_, scaled.i0);
        let with_c = d.lam_fv(c_fv, carrier, with_delta);
        d.lam_fv(a_fv, carrier, with_c)
    };
    let ty = {
        let inner = d.arrow(rat_ty_, nat_ty);
        let with_c = d.arrow(carrier, inner);
        d.arrow(carrier, with_c)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.crossing.crossing_index,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 100),
    })
}

/// Admit [`CrossingNames::crossing_upper`]. See the module documentation for
/// why this half needs only `0 < Δ`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_crossing_upper(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_ty_ = crate::rat_prelude::ops::rat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let delta_fv = d.fresh_fvar();
    let delta = d.kernel().fvar(delta_fv);
    let zero_rat = rzero(d, p.rat);
    let hpos_ty = d.const_app(p.rat.lt, &[zero_rat, delta]);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let scaled = build_scaled(d, p, a, c, delta);
    let (j, q) = setup0(d, p, scaled.s, scaled.zero_nat);

    let delta_le = d.lemma(p.rat.le_of_lt, &[zero_rat, delta, hpos]);
    let delta_nonneg = embed_nonneg(d, p, delta, delta_le);

    let fu = d.lemma(p.bucket_index_floor_upper, &[scaled.s, scaled.zero_nat]);
    // : Rat.le q (natDivSucc (succ i0) 0)
    let cu = d.lemma(p.bucket_clamp_upper, &[scaled.s, scaled.zero_nat]);
    // : CReal.le s (ofRat (radd q bound2j))

    let two_nat = d.num(2);
    let bound2j = d.const_app(p.rat.nat_div_succ, &[two_nat, j]);
    let succ_i0 = d.succ(scaled.i0);
    let succ_i0_over_1 = d.const_app(p.rat.nat_div_succ, &[succ_i0, scaled.zero_nat]);

    let refl_bound2j = d.lemma(p.rat.le_refl, &[bound2j]);
    let fu_plus = d.lemma(
        p.rat.add_le_add,
        &[q, succ_i0_over_1, bound2j, bound2j, fu, refl_bound2j],
    );
    // : Rat.le (radd q bound2j) (radd succ_i0_over_1 bound2j)
    let q_plus = radd(d, q, bound2j);
    let rhs_plus = radd(d, succ_i0_over_1, bound2j);
    let fu_embed = d.lemma(p.of_rat_le, &[q_plus, rhs_plus, fu_plus]);
    let q_plus_embed = embed(d, p, q_plus);
    let rhs_plus_embed = embed(d, p, rhs_plus);
    let s_upper = d.lemma(
        p.le_trans,
        &[scaled.s, q_plus_embed, rhs_plus_embed, cu, fu_embed],
    );
    // : CReal.le s rhs_plus_embed

    let scaled_upper = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[
            scaled.delta_embed,
            scaled.s,
            rhs_plus_embed,
            delta_nonneg,
            s_upper,
        ],
    );
    // : CReal.le (mul delta_embed s) (mul delta_embed rhs_plus_embed)

    let cancel_proof = scale_cancels(
        d,
        p,
        delta,
        scaled.delta_embed,
        scaled.r,
        scaled.r_embed,
        scaled.w,
        hpos,
    );
    // : Equiv (mul delta_embed s) w

    let rhs_scaled = cmul(d, p, scaled.delta_embed, rhs_plus_embed);
    let refl_rhs_scaled = d.lemma(p.equiv_refl, &[rhs_scaled]);
    let delta_times_s = cmul(d, p, scaled.delta_embed, scaled.s);
    let w_le_rhs = d.lemma(
        p.le_congr,
        &[
            delta_times_s,
            scaled.w,
            rhs_scaled,
            rhs_scaled,
            cancel_proof,
            refl_rhs_scaled,
            scaled_upper,
        ],
    );
    // : CReal.le w rhs_scaled

    let (w2, w_a_eq_c) = base_shift(d, p, a, c);
    debug_assert_eq!(w2, scaled.w, "base_shift must rebuild the same `w`");

    let refl_a = d.lemma(p.le_refl, &[a]);
    let step1 = d.lemma(
        p.add_le_add,
        &[scaled.w, rhs_scaled, a, a, w_le_rhs, refl_a],
    );
    // : CReal.le (add w a) (add rhs_scaled a)
    let rhs_scaled_a = cadd(d, p, rhs_scaled, a);
    let a_rhs_scaled = cadd(d, p, a, rhs_scaled);
    let h_comm_final = d.lemma(p.add_comm, &[rhs_scaled, a]); // Equiv rhs_scaled_a a_rhs_scaled

    let w_a = cadd(d, p, scaled.w, a);
    let final_proof = d.lemma(
        p.le_congr,
        &[
            w_a,
            c,
            rhs_scaled_a,
            a_rhs_scaled,
            w_a_eq_c,
            h_comm_final,
            step1,
        ],
    );
    // : CReal.le c a_rhs_scaled

    let ty_body = cle(d, p, c, a_rhs_scaled);
    let ty_with_hyp = d.arrow(hpos_ty, ty_body);
    let ty = {
        let with_delta = d.pi_fv(delta_fv, rat_ty_, ty_with_hyp);
        let with_c = d.pi_fv(c_fv, carrier, with_delta);
        d.pi_fv(a_fv, carrier, with_c)
    };
    let value = {
        let with_hpos = d.lam_fv(hpos_fv, hpos_ty, final_proof);
        let with_delta = d.lam_fv(delta_fv, rat_ty_, with_hpos);
        let with_c = d.lam_fv(c_fv, carrier, with_delta);
        d.lam_fv(a_fv, carrier, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.crossing.crossing_upper,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit [`CrossingNames::crossing_lower`]. See the module documentation for
/// why this half genuinely needs `a ≤ c` (unlike
/// [`declare_crossing_upper`]).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_crossing_lower(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_ty_ = crate::rat_prelude::ops::rat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let delta_fv = d.fresh_fvar();
    let delta = d.kernel().fvar(delta_fv);
    let zero_rat = rzero(d, p.rat);
    let hpos_ty = d.const_app(p.rat.lt, &[zero_rat, delta]);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let scaled = build_scaled(d, p, a, c, delta);
    let hac_ty = cle(d, p, a, c);
    let hac_fv = d.fresh_fvar();
    let hac = d.kernel().fvar(hac_fv);

    let (j, q) = setup0(d, p, scaled.s, scaled.zero_nat);

    // `Δ ≥ 0` and `Δ⁻¹ ≥ 0`, both from `hpos`.
    let delta_le = d.lemma(p.rat.le_of_lt, &[zero_rat, delta, hpos]);
    let delta_nonneg = embed_nonneg(d, p, delta, delta_le);
    let r_pos = d.lemma(p.rat.inv_pos, &[delta, hpos]);
    let r_le = d.lemma(p.rat.le_of_lt, &[zero_rat, scaled.r, r_pos]);
    let r_nonneg = embed_nonneg(d, p, scaled.r, r_le);

    // `w = c + (-a) ≥ 0`, from `hac : le a c`.
    let na = cneg(d, p, a);
    let refl_na = d.lemma(p.le_refl, &[na]);
    let step_hac = d.lemma(p.add_le_add, &[a, c, na, na, hac, refl_na]);
    // : CReal.le (add a na) (add c na) = CReal.le (add a na) w
    let a_na = cadd(d, p, a, na);
    let addneg_a = d.lemma(p.add_neg, &[a]); // Equiv a_na czero
    let refl_w = d.lemma(p.equiv_refl, &[scaled.w]);
    let czero_e = czero(d, p);
    let w_nonneg = d.lemma(
        p.le_congr,
        &[
            a_na, czero_e, scaled.w, scaled.w, addneg_a, refl_w, step_hac,
        ],
    );
    // : CReal.le czero w

    let s_nonneg = d.lemma(
        p.mul_nonneg,
        &[scaled.r_embed, scaled.w, r_nonneg, w_nonneg],
    );
    // : CReal.le czero s

    let cl = d.lemma(p.bucket_clamp_lower, &[scaled.s, scaled.zero_nat, s_nonneg]);
    // : CReal.le (ofRat (rsub q bound3j)) s
    let fl = d.lemma(p.bucket_index_floor_lower, &[scaled.s, scaled.zero_nat]);
    // : Rat.le (natDivSucc i0 0) q

    let three_nat = d.num(3);
    let bound3j = d.const_app(p.rat.nat_div_succ, &[three_nat, j]);
    let i0_over_1 = d.const_app(p.rat.nat_div_succ, &[scaled.i0, scaled.zero_nat]);
    let neg_bound3j = rneg(d, bound3j);
    let refl_neg_bound3j = d.lemma(p.rat.le_refl, &[neg_bound3j]);
    let fl_minus = d.lemma(
        p.rat.add_le_add,
        &[i0_over_1, q, neg_bound3j, neg_bound3j, fl, refl_neg_bound3j],
    );
    // : Rat.le (radd i0_over_1 neg_bound3j) (radd q neg_bound3j)
    let lhs_rat = radd(d, i0_over_1, neg_bound3j);
    let rhs_rat = radd(d, q, neg_bound3j);
    let fl_minus_embed = d.lemma(p.of_rat_le, &[lhs_rat, rhs_rat, fl_minus]);
    let lhs_embed = embed(d, p, lhs_rat);
    let rhs_embed = embed(d, p, rhs_rat);
    let lower_bound_on_s = d.lemma(
        p.le_trans,
        &[lhs_embed, rhs_embed, scaled.s, fl_minus_embed, cl],
    );
    // : CReal.le lhs_embed s

    let scaled_lower = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[
            scaled.delta_embed,
            lhs_embed,
            scaled.s,
            delta_nonneg,
            lower_bound_on_s,
        ],
    );
    // : CReal.le (mul delta_embed lhs_embed) (mul delta_embed s)

    let cancel_proof = scale_cancels(
        d,
        p,
        delta,
        scaled.delta_embed,
        scaled.r,
        scaled.r_embed,
        scaled.w,
        hpos,
    );
    // : Equiv (mul delta_embed s) w

    let lhs_scaled = cmul(d, p, scaled.delta_embed, lhs_embed);
    let refl_lhs_scaled = d.lemma(p.equiv_refl, &[lhs_scaled]);
    let delta_times_s = cmul(d, p, scaled.delta_embed, scaled.s);
    let lower_final = d.lemma(
        p.le_congr,
        &[
            lhs_scaled,
            lhs_scaled,
            delta_times_s,
            scaled.w,
            refl_lhs_scaled,
            cancel_proof,
            scaled_lower,
        ],
    );
    // : CReal.le lhs_scaled w

    let (w2, w_a_eq_c) = base_shift(d, p, a, c);
    debug_assert_eq!(w2, scaled.w, "base_shift must rebuild the same `w`");

    let refl_a = d.lemma(p.le_refl, &[a]);
    let step1 = d.lemma(
        p.add_le_add,
        &[lhs_scaled, scaled.w, a, a, lower_final, refl_a],
    );
    // : CReal.le (add lhs_scaled a) (add w a)
    let lhs_scaled_a = cadd(d, p, lhs_scaled, a);
    let a_lhs_scaled = cadd(d, p, a, lhs_scaled);
    let h_comm_final = d.lemma(p.add_comm, &[lhs_scaled, a]); // Equiv lhs_scaled_a a_lhs_scaled

    let w_a = cadd(d, p, scaled.w, a);
    let final_proof = d.lemma(
        p.le_congr,
        &[
            lhs_scaled_a,
            a_lhs_scaled,
            w_a,
            c,
            h_comm_final,
            w_a_eq_c,
            step1,
        ],
    );
    // : CReal.le a_lhs_scaled c

    let ty_body = cle(d, p, a_lhs_scaled, c);
    let ty_with_hac = d.arrow(hac_ty, ty_body);
    let ty_with_hpos = d.arrow(hpos_ty, ty_with_hac);
    let ty = {
        let with_delta = d.pi_fv(delta_fv, rat_ty_, ty_with_hpos);
        let with_c = d.pi_fv(c_fv, carrier, with_delta);
        d.pi_fv(a_fv, carrier, with_c)
    };
    let value = {
        let with_hac = d.lam_fv(hac_fv, hac_ty, final_proof);
        let with_hpos = d.lam_fv(hpos_fv, hpos_ty, with_hac);
        let with_delta = d.lam_fv(delta_fv, rat_ty_, with_hpos);
        let with_c = d.lam_fv(c_fv, carrier, with_delta);
        d.lam_fv(a_fv, carrier, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.crossing.crossing_lower,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.le zero (CReal.ofNat n)` — local copy of `integral.rs`'s private
/// `zero_le_of_nat` (this file cannot reach it — see the module
/// documentation's per-module small-helper convention). Just
/// [`embed_nonneg`] applied to `natDivSucc n 0` via
/// [`CRealPrelude::zero_le_nat_div_succ`] on the `Rat` side.
fn zero_le_of_nat(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let zero_nat = d.num(0);
    let rat_n = d.const_app(p.rat.nat_div_succ, &[n, zero_nat]);
    let rle = d.lemma(p.rat.zero_le_nat_div_succ, &[n, zero_nat]);
    embed_nonneg(d, p, rat_n, rle)
}

/// `CReal.le x (add x w)`, given `hw : CReal.le zero w` — local copy of
/// `integral.rs`'s private `shift_le_of_nonneg` (same reason as
/// [`zero_le_of_nat`]).
fn shift_le_of_nonneg(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    w: ExprId,
    hw: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let refl_x = d.lemma(p.le_refl, &[x]);
    let grown = d.lemma(p.add_le_add, &[x, x, zero_c, w, refl_x, hw]);
    // grown : le (add x zero) (add x w)
    let padded = cadd(d, p, x, zero_c);
    let target = cadd(d, p, x, w);
    let trim = d.lemma(p.add_zero, &[x]); // Equiv (add x zero) x
    let refl_target = d.lemma(p.equiv_refl, &[target]);
    d.lemma(
        p.le_congr,
        &[padded, x, target, target, trim, refl_target, grown],
    )
    // : le x (add x w)
}

/// Admit [`CrossingNames::crossing_sample_ge_a`]. See that field's own doc
/// comment for the statement and scope: `samplePt := a + ofNat(crossingIndex
/// a c delta)·ofRat(delta)` never falls below its own base point `a`, needing
/// only `0 < Δ`. The SAME `sample_term`/`sample_point` shape
/// [`declare_crossing_sample_upper`]/[`declare_crossing_sample_lower`] build,
/// rebuilt here via [`build_scaled`] so `CReal.crossingIndex a c delta`'s own
/// `ExprId` matches.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_crossing_sample_ge_a(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_ty_ = crate::rat_prelude::ops::rat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let delta_fv = d.fresh_fvar();
    let delta = d.kernel().fvar(delta_fv);
    let zero_rat = rzero(d, p.rat);
    let hpos_ty = d.const_app(p.rat.lt, &[zero_rat, delta]);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let scaled = build_scaled(d, p, a, c, delta);
    let of_nat_i0 = d.const_app(p.of_nat, &[scaled.i0]);
    let sample_term = cmul(d, p, of_nat_i0, scaled.delta_embed);
    let sample_point = cadd(d, p, a, sample_term);

    let delta_le = d.lemma(p.rat.le_of_lt, &[zero_rat, delta, hpos]);
    let delta_nonneg = embed_nonneg(d, p, delta, delta_le);
    let i0_nonneg = zero_le_of_nat(d, p, scaled.i0);
    let term_nonneg = d.lemma(
        p.mul_nonneg,
        &[of_nat_i0, scaled.delta_embed, i0_nonneg, delta_nonneg],
    );
    let proof = shift_le_of_nonneg(d, p, a, sample_term, term_nonneg);

    let ty_body = cle(d, p, a, sample_point);
    let ty = {
        let with_hpos = d.arrow(hpos_ty, ty_body);
        let with_delta = d.pi_fv(delta_fv, rat_ty_, with_hpos);
        let with_c = d.pi_fv(c_fv, carrier, with_delta);
        d.pi_fv(a_fv, carrier, with_c)
    };
    let value = {
        let with_hpos = d.lam_fv(hpos_fv, hpos_ty, proof);
        let with_delta = d.lam_fv(delta_fv, rat_ty_, with_hpos);
        let with_c = d.lam_fv(c_fv, carrier, with_delta);
        d.lam_fv(a_fv, carrier, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.crossing.crossing_sample_ge_a,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `crossingSampleUpper`/`crossingSampleLower`: restating the two halves
// above against an ORDINARY Riemann-sum sample point `a + ofNat(i)·Δ`
// (`integral.rs`'s own `sample_point` shape, rebuilt locally since that
// helper is private to its file and this file's own convention -- see the
// module documentation -- is small per-module copies) rather than the raw
// rational expression `crossingUpper`/`crossingLower` compute internally.
// This is the piece the task briefing asked for: "a sample point of the
// `[a,c]` mesh is within a bounded distance of SOME sample point of the
// `[a,b]` mesh, given the crossing index" -- instantiate `c` at a sample
// point of a DIFFERENT interval's mesh and `delta` at the `[a,b]` mesh's own
// step to get exactly that statement; nothing here is specific to
// `riemannSum` or to any particular `c`.
//
// Route: `crossingUpper`/`crossingLower` are cited as LEMMAS (their own
// proofs are not redone), and only the ADDITIVE SHAPE of their conclusions
// is rebuilt (recomputing `j`, `bound2j`/`bound3j`, `succ_i0_over_1`/
// `i0_over_1` via the exact same term-construction calls `declare_crossing_upper`/
// `declare_crossing_lower` use, so the rebuilt `ExprId`s match). The
// conversion from there to a `sample_point`-shaped conclusion is ordinary
// ring algebra (`of_rat_add`, `left_distrib`, `mul_comm`, `mul_one`,
// `add_assoc`), plus ONE local restatement, [`of_nat_succ_equiv_local`],
// needed only on the upper side (`crossingUpper`'s own bound carries a
// `Nat.succ` the lower bound does not).
//
// `CReal.ofNat n := CReal.ofRat (Rat.natDivSucc n 0)` is a `Definition`, so
// `embed (Rat.natDivSucc k 0)` and `CReal.ofNat k` are DEFEQ (same value,
// one delta-unfold apart) without any extra proof -- the exact move
// `scale_cancels`'s own `step_c` comment already relies on ("`(ofRat
// rat_one)` is defeq to `p.one`"). Every place below that supplies a proof
// stated in terms of `CReal.ofNat` where the surrounding term mentions the
// unfolded `embed (Rat.natDivSucc _ 0)` form (and vice versa) leans on
// exactly that established idiom, not on a fresh assumption.

/// `Equiv (ofNat (Nat.succ Nat.zero)) one` — local restatement of
/// `integral.rs`'s private `of_nat_one_equiv_local` (itself a restatement of
/// `derivative.rs`'s private `of_nat_one_equiv`); this file cannot reach
/// either. See the module documentation for why a third small copy is the
/// established move here rather than exposing either.
fn of_nat_one_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let one_rat = rone(d, rat);
    let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
    let unit_embed = embed(d, p, unit);
    let refl_start = d.lemma(p.equiv_refl, &[unit_embed]);
    rat_eq_rewrite(d, unit, one_rat, unit_eq_one, refl_start, &|d, t| {
        let embedded = embed(d, p, t);
        cequiv(d, p, unit_embed, embedded)
    })
}

/// `Equiv (ofNat (Nat.succ m)) (add (ofNat m) one)` — local restatement of
/// `integral.rs`'s private `of_nat_succ_equiv_local`. See this section's
/// header comment and [`of_nat_one_equiv_local`].
fn of_nat_succ_equiv_local(d: &mut IntDev<'_>, p: CRealPrelude, m: ExprId) -> ExprId {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let one_c = cone(d, p);

    let m_rat = d.const_app(rat.nat_div_succ, &[m, zero_nat]);
    let one_ratdiv = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let sum_rat = radd(d, m_rat, one_ratdiv);
    let succ_m = d.succ(m);
    let succ_rat = d.const_app(rat.nat_div_succ, &[succ_m, zero_nat]);
    let add_eq = d.lemma(rat.nat_div_succ_add, &[m, one_nat, zero_nat]);

    let of_nat_m = d.const_app(p.of_nat, &[m]);
    let of_nat_1 = d.const_app(p.of_nat, &[one_nat]);
    let of_nat_succ_m = d.const_app(p.of_nat, &[succ_m]);
    let add_of_nat_m_1 = cadd(d, p, of_nat_m, of_nat_1);

    let add_step = d.lemma(p.of_rat_add, &[m_rat, one_ratdiv]);
    let rewritten = rat_eq_rewrite(d, sum_rat, succ_rat, add_eq, add_step, &|d, t| {
        let embedded = embed(d, p, t);
        cequiv(d, p, add_of_nat_m_1, embedded)
    });
    let flipped = d.lemma(p.equiv_symm, &[add_of_nat_m_1, of_nat_succ_m, rewritten]);

    let one_eq = of_nat_one_equiv_local(d, p);
    let refl_m = d.lemma(p.equiv_refl, &[of_nat_m]);
    let congr_step = d.lemma(
        p.add_congr,
        &[of_nat_m, of_nat_m, of_nat_1, one_c, refl_m, one_eq],
    );
    let add_of_nat_m_one = cadd(d, p, of_nat_m, one_c);
    d.lemma(
        p.equiv_trans,
        &[
            of_nat_succ_m,
            add_of_nat_m_1,
            add_of_nat_m_one,
            flipped,
            congr_step,
        ],
    )
}

// NOTE: the sample point built below, `add a (mul (ofNat i) delta)`, is
// spelled out inline at each construction site rather than through a
// separate helper, because both proofs also need its inner `mul (ofNat i)
// delta` term on its own (as an intermediate in the ring-algebra chain) —
// matches `integral.rs`'s private `sample_point` EXACTLY (same argument
// order in the inner `mul`) so a future caller relating this file's output
// to a `riemannSum` term needs no extra commuting step.

/// Admit [`CrossingNames::crossing_sample_upper`]: `∀ a c Δ, Rat.lt Rat.zero
/// Δ → CReal.le c (add (sample_point a Δ (crossingIndex a c Δ)) (add Δ (mul
/// Δ (ofRat (Rat.natDivSucc 2 j)))))`, `j` the same closed term
/// `crossingUpper` itself samples at (`(succ 0)*(succ 0)`, definitionally
/// `1`) — so the additive slack is, unreduced, `Δ + Δ·1`, i.e. exactly `2Δ`
/// at every instance, just not folded to that literal shape here (no
/// concrete-rational-comparison lemma is spent proving `bound2j = 1`; the
/// unreduced term is equally usable downstream).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_crossing_sample_upper(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_ty_ = crate::rat_prelude::ops::rat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let delta_fv = d.fresh_fvar();
    let delta = d.kernel().fvar(delta_fv);
    let zero_rat = rzero(d, p.rat);
    let hpos_ty = d.const_app(p.rat.lt, &[zero_rat, delta]);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let scaled = build_scaled(d, p, a, c, delta);

    // `j`, the SAME closed term `crossing_upper`'s own type mentions (see
    // `setup0`); only `j` is needed here, not its sibling `q`, which is
    // internal to `crossing_upper`'s own PROOF, not to its stated type.
    let k1 = d.succ(scaled.zero_nat);
    let j = NatOps::mul(d, k1, k1);

    let two_nat = d.num(2);
    let bound2j = d.const_app(p.rat.nat_div_succ, &[two_nat, j]);
    let succ_i0 = d.succ(scaled.i0);
    let succ_i0_over_1 = d.const_app(p.rat.nat_div_succ, &[succ_i0, scaled.zero_nat]);
    let rhs_plus = radd(d, succ_i0_over_1, bound2j);
    let rhs_plus_embed = embed(d, p, rhs_plus);
    let rhs_scaled = cmul(d, p, scaled.delta_embed, rhs_plus_embed);
    let a_rhs_scaled = cadd(d, p, a, rhs_scaled);

    // `hu : CReal.le c a_rhs_scaled` — `crossing_upper` cited as a lemma.
    let hu = d.lemma(p.crossing.crossing_upper, &[a, c, delta, hpos]);

    let of_nat_i0 = d.const_app(p.of_nat, &[scaled.i0]);
    let embed_succ_i0 = embed(d, p, succ_i0_over_1);
    let embed_bound2j = embed(d, p, bound2j);
    let one_c = cone(d, p);
    let sample_term = cmul(d, p, of_nat_i0, scaled.delta_embed);
    let bound2j_term = cmul(d, p, scaled.delta_embed, embed_bound2j);
    let slack_upper = cadd(d, p, scaled.delta_embed, bound2j_term);
    let sample_point = cadd(d, p, a, sample_term);
    let target = cadd(d, p, sample_point, slack_upper);

    let refl_delta = d.lemma(p.equiv_refl, &[scaled.delta_embed]);

    // rhs_plus_embed ~ add embed_succ_i0 embed_bound2j (`of_rat_add`'s own
    // direction is the reverse of this, hence the `equiv_symm`).
    let sum_embed = cadd(d, p, embed_succ_i0, embed_bound2j);
    let step_a_raw = d.lemma(p.of_rat_add, &[succ_i0_over_1, bound2j]);
    let step_a = d.lemma(p.equiv_symm, &[sum_embed, rhs_plus_embed, step_a_raw]);

    // rhs_scaled ~ mul delta_embed sum_embed
    let step_b = d.lemma(
        p.mul_congr,
        &[
            scaled.delta_embed,
            scaled.delta_embed,
            rhs_plus_embed,
            sum_embed,
            refl_delta,
            step_a,
        ],
    );

    // mul delta_embed sum_embed ~ add (mul delta_embed embed_succ_i0) bound2j_term
    let step_c = d.lemma(
        p.left_distrib,
        &[scaled.delta_embed, embed_succ_i0, embed_bound2j],
    );
    let mul_delta_succ = cmul(d, p, scaled.delta_embed, embed_succ_i0);

    // mul delta_embed embed_succ_i0 ~ mul delta_embed (add of_nat_i0 one_c)
    // -- `embed_succ_i0` is DEFEQ `ofNat (succ i0)`, per this section's
    // header comment.
    let succ_eq = of_nat_succ_equiv_local(d, p, scaled.i0);
    let add_i0_one = cadd(d, p, of_nat_i0, one_c);
    let step_d = d.lemma(
        p.mul_congr,
        &[
            scaled.delta_embed,
            scaled.delta_embed,
            embed_succ_i0,
            add_i0_one,
            refl_delta,
            succ_eq,
        ],
    );

    // mul delta_embed (add of_nat_i0 one_c) ~ add (mul delta_embed of_nat_i0)(mul delta_embed one_c)
    let step_e = d.lemma(p.left_distrib, &[scaled.delta_embed, of_nat_i0, one_c]);
    let mul_delta_i0 = cmul(d, p, scaled.delta_embed, of_nat_i0);
    let mul_delta_one = cmul(d, p, scaled.delta_embed, one_c);

    // mul delta_embed one_c ~ delta_embed
    let step_f = d.lemma(p.mul_one, &[scaled.delta_embed]);
    // mul delta_embed of_nat_i0 ~ sample_term (mul_comm)
    let step_g = d.lemma(p.mul_comm, &[scaled.delta_embed, of_nat_i0]);

    let step_de_combined = {
        let refl_mdo = d.lemma(p.equiv_refl, &[mul_delta_one]);
        d.lemma(
            p.add_congr,
            &[
                mul_delta_i0,
                sample_term,
                mul_delta_one,
                mul_delta_one,
                step_g,
                refl_mdo,
            ],
        )
    };
    let sample_plus_delta = cadd(d, p, sample_term, scaled.delta_embed);
    let step_fg_combined = {
        let refl_st = d.lemma(p.equiv_refl, &[sample_term]);
        d.lemma(
            p.add_congr,
            &[
                sample_term,
                sample_term,
                mul_delta_one,
                scaled.delta_embed,
                refl_st,
                step_f,
            ],
        )
    };
    let mul_delta_i0_plus_one = cadd(d, p, mul_delta_i0, mul_delta_one);
    let mul_delta_add_i0_one = cmul(d, p, scaled.delta_embed, add_i0_one);
    let sample_plus_mul_delta_one = cadd(d, p, sample_term, mul_delta_one);

    // mul delta_embed embed_succ_i0 ~ add sample_term delta_embed
    let step_i0 = echain(
        d,
        p,
        mul_delta_succ,
        &[
            (mul_delta_add_i0_one, step_d),
            (mul_delta_i0_plus_one, step_e),
            (sample_plus_mul_delta_one, step_de_combined),
            (sample_plus_delta, step_fg_combined),
        ],
    );

    let refl_bound2j_term = d.lemma(p.equiv_refl, &[bound2j_term]);
    let step_h = d.lemma(
        p.add_congr,
        &[
            mul_delta_succ,
            sample_plus_delta,
            bound2j_term,
            bound2j_term,
            step_i0,
            refl_bound2j_term,
        ],
    );
    let sum_after_c = cadd(d, p, mul_delta_succ, bound2j_term);
    let sum_after_h = cadd(d, p, sample_plus_delta, bound2j_term);

    let step_reassoc = d.lemma(
        p.add_assoc,
        &[sample_term, scaled.delta_embed, bound2j_term],
    );
    let rhs_final = cadd(d, p, sample_term, slack_upper);

    let mul_delta_sum_embed_upper = cmul(d, p, scaled.delta_embed, sum_embed);
    let rhs_chain = echain(
        d,
        p,
        rhs_scaled,
        &[
            (mul_delta_sum_embed_upper, step_b),
            (sum_after_c, step_c),
            (sum_after_h, step_h),
            (rhs_final, step_reassoc),
        ],
    );

    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let a_plus_final = cadd(d, p, a, rhs_final);
    let step_add_a = d.lemma(
        p.add_congr,
        &[a, a, rhs_scaled, rhs_final, refl_a, rhs_chain],
    );
    let assoc_a = d.lemma(p.add_assoc, &[a, sample_term, slack_upper]);
    let step_reassoc_a = d.lemma(p.equiv_symm, &[target, a_plus_final, assoc_a]);

    let full_chain = echain(
        d,
        p,
        a_rhs_scaled,
        &[(a_plus_final, step_add_a), (target, step_reassoc_a)],
    );

    let refl_c = d.lemma(p.equiv_refl, &[c]);
    let final_proof = d.lemma(
        p.le_congr,
        &[c, c, a_rhs_scaled, target, refl_c, full_chain, hu],
    );

    let ty_body = cle(d, p, c, target);
    let ty_with_hyp = d.arrow(hpos_ty, ty_body);
    let ty = {
        let with_delta = d.pi_fv(delta_fv, rat_ty_, ty_with_hyp);
        let with_c = d.pi_fv(c_fv, carrier, with_delta);
        d.pi_fv(a_fv, carrier, with_c)
    };
    let value = {
        let with_hpos = d.lam_fv(hpos_fv, hpos_ty, final_proof);
        let with_delta = d.lam_fv(delta_fv, rat_ty_, with_hpos);
        let with_c = d.lam_fv(c_fv, carrier, with_delta);
        d.lam_fv(a_fv, carrier, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.crossing.crossing_sample_upper,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit [`CrossingNames::crossing_sample_lower`]: `∀ a c Δ, Rat.lt Rat.zero
/// Δ → CReal.le a c → CReal.le (add (sample_point a Δ (crossingIndex a c Δ))
/// (mul Δ (ofRat (Rat.neg (Rat.natDivSucc 3 j))))) c` — the mirror of
/// [`declare_crossing_sample_upper`], simpler because `crossingLower`'s own
/// bound carries no `Nat.succ` to split (`i0_over_1` is already `ofNat i0`,
/// up to the same delta-unfold [`declare_crossing_sample_upper`]'s header
/// comment names). The slack term is left as `Δ · (negative rational)`
/// rather than rewritten to `neg (Δ · positive)` — mathematically identical,
/// and avoids needing a `mul`-distributes-over-`neg` lemma this prelude does
/// not have.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
fn declare_crossing_sample_lower(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let rat_ty_ = crate::rat_prelude::ops::rat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let delta_fv = d.fresh_fvar();
    let delta = d.kernel().fvar(delta_fv);
    let zero_rat = rzero(d, p.rat);
    let hpos_ty = d.const_app(p.rat.lt, &[zero_rat, delta]);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let scaled = build_scaled(d, p, a, c, delta);
    let hac_ty = cle(d, p, a, c);
    let hac_fv = d.fresh_fvar();
    let hac = d.kernel().fvar(hac_fv);

    let k1 = d.succ(scaled.zero_nat);
    let j = NatOps::mul(d, k1, k1);

    let three_nat = d.num(3);
    let bound3j = d.const_app(p.rat.nat_div_succ, &[three_nat, j]);
    let neg_bound3j = rneg(d, bound3j);
    let i0_over_1 = d.const_app(p.rat.nat_div_succ, &[scaled.i0, scaled.zero_nat]);
    let lhs_rat = radd(d, i0_over_1, neg_bound3j);
    let lhs_embed = embed(d, p, lhs_rat);
    let lhs_scaled = cmul(d, p, scaled.delta_embed, lhs_embed);
    let a_lhs_scaled = cadd(d, p, a, lhs_scaled);

    // `hl : CReal.le a_lhs_scaled c` — `crossing_lower` cited as a lemma.
    let hl = d.lemma(p.crossing.crossing_lower, &[a, c, delta, hpos, hac]);

    let of_nat_i0 = d.const_app(p.of_nat, &[scaled.i0]);
    let embed_i0_over_1 = embed(d, p, i0_over_1);
    let embed_neg_bound3j = embed(d, p, neg_bound3j);
    let sample_term = cmul(d, p, of_nat_i0, scaled.delta_embed);
    let slack_lower = cmul(d, p, scaled.delta_embed, embed_neg_bound3j);
    let sample_point = cadd(d, p, a, sample_term);
    let target = cadd(d, p, sample_point, slack_lower);

    let refl_delta = d.lemma(p.equiv_refl, &[scaled.delta_embed]);

    let sum_embed = cadd(d, p, embed_i0_over_1, embed_neg_bound3j);
    let step_a_raw = d.lemma(p.of_rat_add, &[i0_over_1, neg_bound3j]);
    let step_a = d.lemma(p.equiv_symm, &[sum_embed, lhs_embed, step_a_raw]);

    let step_b = d.lemma(
        p.mul_congr,
        &[
            scaled.delta_embed,
            scaled.delta_embed,
            lhs_embed,
            sum_embed,
            refl_delta,
            step_a,
        ],
    );

    let step_c = d.lemma(
        p.left_distrib,
        &[scaled.delta_embed, embed_i0_over_1, embed_neg_bound3j],
    );
    let mul_delta_i0raw = cmul(d, p, scaled.delta_embed, embed_i0_over_1);
    let sum_after_c = cadd(d, p, mul_delta_i0raw, slack_lower);

    // `mul_delta_i0raw` is DEFEQ `mul delta_embed of_nat_i0`, per
    // `declare_crossing_sample_upper`'s header comment.
    let step_g = d.lemma(p.mul_comm, &[scaled.delta_embed, of_nat_i0]);
    let refl_slack = d.lemma(p.equiv_refl, &[slack_lower]);
    let step_h = d.lemma(
        p.add_congr,
        &[
            mul_delta_i0raw,
            sample_term,
            slack_lower,
            slack_lower,
            step_g,
            refl_slack,
        ],
    );
    let lhs_final = cadd(d, p, sample_term, slack_lower);

    let mul_delta_sum_embed_lower = cmul(d, p, scaled.delta_embed, sum_embed);
    let lhs_chain = echain(
        d,
        p,
        lhs_scaled,
        &[
            (mul_delta_sum_embed_lower, step_b),
            (sum_after_c, step_c),
            (lhs_final, step_h),
        ],
    );

    let refl_a = d.lemma(p.equiv_refl, &[a]);
    let a_plus_final = cadd(d, p, a, lhs_final);
    let step_add_a = d.lemma(
        p.add_congr,
        &[a, a, lhs_scaled, lhs_final, refl_a, lhs_chain],
    );
    let assoc_a = d.lemma(p.add_assoc, &[a, sample_term, slack_lower]);
    let step_reassoc_a = d.lemma(p.equiv_symm, &[target, a_plus_final, assoc_a]);

    let full_chain = echain(
        d,
        p,
        a_lhs_scaled,
        &[(a_plus_final, step_add_a), (target, step_reassoc_a)],
    );

    let refl_c = d.lemma(p.equiv_refl, &[c]);
    let final_proof = d.lemma(
        p.le_congr,
        &[a_lhs_scaled, target, c, c, full_chain, refl_c, hl],
    );

    let ty_body = cle(d, p, target, c);
    let ty_with_hac = d.arrow(hac_ty, ty_body);
    let ty_with_hpos = d.arrow(hpos_ty, ty_with_hac);
    let ty = {
        let with_delta = d.pi_fv(delta_fv, rat_ty_, ty_with_hpos);
        let with_c = d.pi_fv(c_fv, carrier, with_delta);
        d.pi_fv(a_fv, carrier, with_c)
    };
    let value = {
        let with_hac = d.lam_fv(hac_fv, hac_ty, final_proof);
        let with_hpos = d.lam_fv(hpos_fv, hpos_ty, with_hac);
        let with_delta = d.lam_fv(delta_fv, rat_ty_, with_hpos);
        let with_c = d.lam_fv(c_fv, carrier, with_delta);
        d.lam_fv(a_fv, carrier, with_c)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.crossing.crossing_sample_lower,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.crossingIndex`, `CReal.crossingUpper` and
/// `CReal.crossingLower`. See the module documentation for the statements
/// and the exact hypotheses each half needs.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_crossing(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_crossing_index(d, p)?;
    declare_crossing_upper(d, p)?;
    declare_crossing_lower(d, p)?;
    declare_crossing_sample_ge_a(d, p)
}

/// Admit `CReal.crossingSampleUpper` and `CReal.crossingSampleLower`. Split
/// out from [`declare_crossing`] (rather than folded into it) because these
/// two need [`CRealPrelude::rat_unit_eq_one`] (via the local
/// `of_nat_one_equiv_local`/`of_nat_succ_equiv_local` restatements above),
/// which `mul_self_zero::declare_mul_self_zero` does not admit until AFTER
/// `crossing::declare_crossing` runs — so the caller must dispatch this
/// function later in the build sequence, once that dependency exists.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_crossing_sample(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_crossing_sample_upper(d, p)?;
    declare_crossing_sample_lower(d, p)
}

// --- roadmap: bridging the crossing sample point to `F` via uniform
// continuity -- the ANALYTIC half of the cross-width Riemann comparison's
// single block (see `integral.rs`'s 2026-08-27 module doc entry) ----------

/// `Equiv (add (add s y) (neg s)) y` — cancelling a term added on the LEFT
/// back off, via `add_comm`, `add_assoc`, `add_neg`, `add_zero`. Shared by
/// [`le_sub_of_le_add`] and [`le_sub_of_add_le_left`], the two directions
/// [`declare_crossing_close`] needs to move `samplePt` across a `CReal.le`.
fn cancel_added_left(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    s: ExprId,
    y: ExprId,
) -> (ExprId, ExprId) {
    let neg_s = cneg(d, p, s);
    let sy = cadd(d, p, s, y);
    let start = cadd(d, p, sy, neg_s);

    let ys = cadd(d, p, y, s);
    let h_comm = d.lemma(p.add_comm, &[s, y]); // Equiv sy ys
    let refl_neg_s = d.lemma(p.equiv_refl, &[neg_s]);
    let step_a = d.lemma(p.add_congr, &[sy, ys, neg_s, neg_s, h_comm, refl_neg_s]);
    let next1 = cadd(d, p, ys, neg_s);

    let s_negs = cadd(d, p, s, neg_s);
    let step_b = d.lemma(p.add_assoc, &[y, s, neg_s]); // Equiv next1 (add y s_negs)
    let next2 = cadd(d, p, y, s_negs);

    let zero_c = czero(d, p);
    let h_addneg = d.lemma(p.add_neg, &[s]); // Equiv s_negs zero_c
    let refl_y = d.lemma(p.equiv_refl, &[y]);
    let step_c = d.lemma(p.add_congr, &[y, y, s_negs, zero_c, refl_y, h_addneg]);
    let next3 = cadd(d, p, y, zero_c);

    let step_d = d.lemma(p.add_zero, &[y]); // Equiv next3 y

    let proof = echain(
        d,
        p,
        start,
        &[
            (next1, step_a),
            (next2, step_b),
            (next3, step_c),
            (y, step_d),
        ],
    );
    (start, proof)
}

/// `le x (add s y) -> le (add x (neg s)) y` — move `s` from the right of a
/// sum across to cancel against a matching `neg s` on the left.
pub(super) fn le_sub_of_le_add(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    s: ExprId,
    y: ExprId,
    h: ExprId,
) -> ExprId {
    let (start, cancel_proof) = cancel_added_left(d, p, s, y);
    let neg_s = cneg(d, p, s);
    let refl_neg_s = d.lemma(p.le_refl, &[neg_s]);
    let sy = cadd(d, p, s, y);
    let step1 = d.lemma(p.add_le_add, &[x, sy, neg_s, neg_s, h, refl_neg_s]);
    // step1 : le (add x neg_s) start
    let lhs = cadd(d, p, x, neg_s);
    let refl_lhs = d.lemma(p.equiv_refl, &[lhs]);
    d.lemma(
        p.le_congr,
        &[lhs, lhs, start, y, refl_lhs, cancel_proof, step1],
    )
}

/// `le (add s y) x -> le y (add x (neg s))` — the mirror direction:
/// [`declare_crossing_close`] needs this for `crossingSampleLower`'s own
/// shape, `add samplePt slackLower ≤ c`.
fn le_sub_of_add_le_left(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    s: ExprId,
    y: ExprId,
    x: ExprId,
    h: ExprId,
) -> ExprId {
    let (start, cancel_proof) = cancel_added_left(d, p, s, y);
    let neg_s = cneg(d, p, s);
    let refl_neg_s = d.lemma(p.le_refl, &[neg_s]);
    let sy = cadd(d, p, s, y);
    let step1 = d.lemma(p.add_le_add, &[sy, x, neg_s, neg_s, h, refl_neg_s]);
    // step1 : le start (add x neg_s)
    let rhs = cadd(d, p, x, neg_s);
    let refl_rhs = d.lemma(p.equiv_refl, &[rhs]);
    d.lemma(
        p.le_congr,
        &[start, y, rhs, rhs, cancel_proof, refl_rhs, step1],
    )
}

/// `CReal.close (x y : CReal) (q : Rat) : Prop := le (abs (add x (neg y)))
/// (ofRat q)` — reproduced locally (`uniform_continuity.rs`/`integral.rs`
/// both keep their own private copy of this same shape, per this file's own
/// convention of small per-module copies rather than reaching across a
/// sibling module boundary for a private helper).
fn close_within(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, q: ExprId) -> ExprId {
    let ny = cneg(d, p, y);
    let diff = cadd(d, p, x, ny);
    let magnitude = d.const_app(p.abs, &[diff]);
    let target = embed(d, p, q);
    cle(d, p, magnitude, target)
}

/// The coarse mesh's crossing-index sample point and the two closed slack
/// terms `crossingSampleUpper`/`crossingSampleLower` place `c` within,
/// rebuilt via the SAME [`build_scaled`] recipe those two theorems' own
/// proofs use, so [`declare_crossing_close`]'s proof cites the identical
/// `ExprId` shapes their stated types already carry.
struct SampleSlack {
    sample_pt: ExprId,
    slack_upper: ExprId,
    slack_lower: ExprId,
}

fn sample_slack(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    c: ExprId,
    delta: ExprId,
) -> SampleSlack {
    let scaled = build_scaled(d, p, a, c, delta);
    let k1 = d.succ(scaled.zero_nat);
    let j = NatOps::mul(d, k1, k1);
    let two_nat = d.num(2);
    let three_nat = d.num(3);
    let bound2j = d.const_app(p.rat.nat_div_succ, &[two_nat, j]);
    let bound3j = d.const_app(p.rat.nat_div_succ, &[three_nat, j]);
    let embed_bound2j = embed(d, p, bound2j);
    let neg_bound3j = rneg(d, bound3j);
    let embed_neg_bound3j = embed(d, p, neg_bound3j);
    let of_nat_i0 = d.const_app(p.of_nat, &[scaled.i0]);
    let sample_term = cmul(d, p, of_nat_i0, scaled.delta_embed);
    let sample_pt = cadd(d, p, a, sample_term);
    let bound2j_term = cmul(d, p, scaled.delta_embed, embed_bound2j);
    let slack_upper = cadd(d, p, scaled.delta_embed, bound2j_term);
    let slack_lower = cmul(d, p, scaled.delta_embed, embed_neg_bound3j);
    SampleSlack {
        sample_pt,
        slack_upper,
        slack_lower,
    }
}

/// Admit [`CrossingNames::crossing_close`]. See that field's own doc comment
/// for the exact statement and for what this does NOT derive (the
/// Archimedean smallness of the two slacks from a mesh count, and
/// `samplePt`'s own domain membership) — both are explicit hypotheses here.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_crossing_close(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rat_ty_ = crate::rat_prelude::ops::rat_ty(d);
    let fn_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let delta_fv = d.fresh_fvar();
    let delta = d.kernel().fvar(delta_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let zero_rat = rzero(d, p.rat);
    let hpos_ty = d.const_app(p.rat.lt, &[zero_rat, delta]);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let hac_ty = cle(d, p, a, c);
    let hac_fv = d.fresh_fvar();
    let hac = d.kernel().fvar(hac_fv);
    let hcb_ty = cle(d, p, c, b);
    let hcb_fv = d.fresh_fvar();
    let hcb = d.kernel().fvar(hcb_fv);

    let slack = sample_slack(d, p, a, c, delta);

    let hap_ty = cle(d, p, a, slack.sample_pt);
    let hap_fv = d.fresh_fvar();
    let hap = d.kernel().fvar(hap_fv);
    let hpb_ty = cle(d, p, slack.sample_pt, b);
    let hpb_fv = d.fresh_fvar();
    let hpb = d.kernel().fvar(hpb_fv);

    let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let outer = d.apply(modulus_fn, &[e]);
    let one_nat = d.num(1);
    let bound_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, outer]);
    let bound_embed = embed(d, p, bound_rat);

    let h_upper_ty = cle(d, p, slack.slack_upper, bound_embed);
    let h_upper_fv = d.fresh_fvar();
    let h_upper = d.kernel().fvar(h_upper_fv);
    let neg_slack_lower = cneg(d, p, slack.slack_lower);
    let h_lower_ty = cle(d, p, neg_slack_lower, bound_embed);
    let h_lower_fv = d.fresh_fvar();
    let h_lower = d.kernel().fvar(h_lower_fv);

    // --- the proof body -------------------------------------------------

    let hu_sample = d.lemma(p.crossing.crossing_sample_upper, &[a, c, delta, hpos]);
    // hu_sample : le c (add samplePt slackUpper)
    let hl_sample = d.lemma(p.crossing.crossing_sample_lower, &[a, c, delta, hpos, hac]);
    // hl_sample : le (add samplePt slackLower) c

    let neg_sample_pt = cneg(d, p, slack.sample_pt);
    let x_val = cadd(d, p, c, neg_sample_pt);

    let h1 = le_sub_of_le_add(d, p, c, slack.sample_pt, slack.slack_upper, hu_sample);
    // h1 : le x_val slackUpper
    let h1p = d.lemma(
        p.le_trans,
        &[x_val, slack.slack_upper, bound_embed, h1, h_upper],
    );

    let h2 = le_sub_of_add_le_left(d, p, slack.sample_pt, slack.slack_lower, c, hl_sample);
    // h2 : le slackLower x_val
    let h2n = d.lemma(p.neg_le_neg, &[slack.slack_lower, x_val, h2]);
    // h2n : le (neg x_val) (neg slackLower)
    let neg_x_val = cneg(d, p, x_val);
    let h2p = d.lemma(
        p.le_trans,
        &[neg_x_val, neg_slack_lower, bound_embed, h2n, h_lower],
    );

    let abs_bound = d.lemma(p.abs_le, &[x_val, bound_embed, h1p, h2p]);
    // abs_bound : le (abs x_val) bound_embed == close_within c samplePt bound_rat

    let uc_spec_term = d.const_app(p.uc_spec, &[f, a, b, u]);
    let conclusion_proof = d.apply(
        uc_spec_term,
        &[e, c, slack.sample_pt, hac, hcb, hap, hpb, abs_bound],
    );

    let out_rat_e = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let fc = d.apply(f, &[c]);
    let f_sample = d.apply(f, &[slack.sample_pt]);
    let conclusion_ty = close_within(d, p, fc, f_sample, out_rat_e);

    let ty = {
        let after_hlower = d.arrow(h_lower_ty, conclusion_ty);
        let after_hupper = d.arrow(h_upper_ty, after_hlower);
        let after_hpb = d.arrow(hpb_ty, after_hupper);
        let after_hap = d.arrow(hap_ty, after_hpb);
        let after_hcb = d.arrow(hcb_ty, after_hap);
        let after_hac = d.arrow(hac_ty, after_hcb);
        let after_hpos = d.arrow(hpos_ty, after_hac);
        let after_u = d.pi_fv(u_fv, u_ty, after_hpos);
        let over_e = d.pi_fv(e_fv, nat, after_u);
        let over_delta = d.pi_fv(delta_fv, rat_ty_, over_e);
        let over_c = d.pi_fv(c_fv, carrier, over_delta);
        let over_b = d.pi_fv(b_fv, carrier, over_c);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, fn_ty, over_a)
    };
    let value = {
        let with_hlower = d.lam_fv(h_lower_fv, h_lower_ty, conclusion_proof);
        let with_hupper = d.lam_fv(h_upper_fv, h_upper_ty, with_hlower);
        let with_hpb = d.lam_fv(hpb_fv, hpb_ty, with_hupper);
        let with_hap = d.lam_fv(hap_fv, hap_ty, with_hpb);
        let with_hcb = d.lam_fv(hcb_fv, hcb_ty, with_hap);
        let with_hac = d.lam_fv(hac_fv, hac_ty, with_hcb);
        let with_hpos = d.lam_fv(hpos_fv, hpos_ty, with_hac);
        let with_u = d.lam_fv(u_fv, u_ty, with_hpos);
        let over_e = d.lam_fv(e_fv, nat, with_u);
        let over_delta = d.lam_fv(delta_fv, rat_ty_, over_e);
        let over_c = d.lam_fv(c_fv, carrier, over_delta);
        let over_b = d.lam_fv(b_fv, carrier, over_c);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, fn_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.crossing.crossing_close,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `crossingCloseClamped`: `samplePt` replaced by `clampedPt := min
// samplePt b`, discharging BOTH domain-membership hypotheses by
// construction instead of assuming them -- see the module documentation's
// "what needs which hypothesis" section and `integral.rs`'s 2026-08-27
// entry on why `samplePt ≤ b` is not provable outright. ---------------------
//
// `min_le_right` gives `clampedPt ≤ b` unconditionally, no case split. `a ≤
// clampedPt` follows from `le_min` applied to `a ≤ samplePt`
// ([`CrossingNames::crossing_sample_ge_a`]) and `a ≤ b` (`le_trans hac hcb`).
// The closeness bound survives the substitution too, via the SAME `le_min`
// move applied to `c − bound_embed`: showing `c − bound_embed ≤ samplePt`
// (from `crossingSampleUpper` widened by `h_upper`) and `c − bound_embed ≤
// b` (from `hcb` widened by `le_add_of_nonneg`) gives, by `le_min`, `c −
// bound_embed ≤ clampedPt` -- and adding `bound_embed` back gives `c −
// clampedPt ≤ bound_embed`, the upper half `abs_le` needs. The lower half
// needs no `le_min` at all: `clampedPt ≤ samplePt` (`min_le_left`) transfers
// `crossingSampleLower`'s existing bound on `c − samplePt` up to `c −
// clampedPt` by plain transitivity.

/// `Equiv (add (add u v) (neg v)) u` — "(u+v)−v ~ u", cancelling a term
/// added on the RIGHT. Built from [`cancel_added_left`] (which cancels a
/// term added on the LEFT) via one `add_comm` swap: cheaper than re-deriving
/// `add_assoc`/`add_neg`/`add_zero` from scratch for the mirror shape.
fn cancel_added_right(d: &mut IntDev<'_>, p: CRealPrelude, u: ExprId, v: ExprId) -> ExprId {
    let uv = cadd(d, p, u, v);
    let vu = cadd(d, p, v, u);
    let comm = d.lemma(p.add_comm, &[u, v]); // Equiv uv vu
    let neg_v = cneg(d, p, v);
    let refl_neg_v = d.lemma(p.equiv_refl, &[neg_v]);
    let congr_step = d.lemma(p.add_congr, &[uv, vu, neg_v, neg_v, comm, refl_neg_v]);
    // congr_step : Equiv (add uv neg_v) (add vu neg_v)
    let (_, base_proof) = cancel_added_left(d, p, v, u); // Equiv (add vu neg_v) u
    let lhs = cadd(d, p, uv, neg_v);
    let rhs = cadd(d, p, vu, neg_v);
    d.lemma(p.equiv_trans, &[lhs, rhs, u, congr_step, base_proof])
}

/// `Equiv (add (neg s) s) zero` — the mirror of `add_neg`'s own order, via
/// one `add_comm` swap.
fn neg_then_add_to_zero(d: &mut IntDev<'_>, p: CRealPrelude, s: ExprId) -> ExprId {
    let neg_s = cneg(d, p, s);
    let neg_s_s = cadd(d, p, neg_s, s);
    let s_neg_s = cadd(d, p, s, neg_s);
    let comm = d.lemma(p.add_comm, &[neg_s, s]); // Equiv neg_s_s s_neg_s
    let cancel = d.lemma(p.add_neg, &[s]); // Equiv s_neg_s zero
    let zero_c = czero(d, p);
    d.lemma(p.equiv_trans, &[neg_s_s, s_neg_s, zero_c, comm, cancel])
}

/// `Equiv (add (add x (neg s)) s) x` — "(x−s)+s ~ x", adding back a
/// subtracted term. The inverse cancellation [`cancel_added_right`] does not
/// give (that one cancels a term added, not subtracted).
fn sub_then_add_cancel(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, s: ExprId) -> ExprId {
    let neg_s = cneg(d, p, s);
    let x_negs = cadd(d, p, x, neg_s);
    let start = cadd(d, p, x_negs, s); // (x + (-s)) + s

    let neg_s_s = cadd(d, p, neg_s, s);
    let s1 = cadd(d, p, x, neg_s_s); // x + ((-s)+s)
    let assoc = d.lemma(p.add_assoc, &[x, neg_s, s]); // Equiv start s1

    let zero_c = czero(d, p);
    let s2 = cadd(d, p, x, zero_c); // x + 0
    let cancel = neg_then_add_to_zero(d, p, s); // Equiv neg_s_s zero
    let refl_x = d.lemma(p.equiv_refl, &[x]);
    let congr = d.lemma(p.add_congr, &[x, x, neg_s_s, zero_c, refl_x, cancel]); // Equiv s1 s2

    let final_step = d.lemma(p.add_zero, &[x]); // Equiv s2 x

    echain(d, p, start, &[(s1, assoc), (s2, congr), (x, final_step)])
}

/// `le x (add y s) -> le (add x (neg s)) y` — move `s`, added on the RIGHT
/// of the sum, across to cancel against a matching `neg s`. Mirrors
/// [`le_sub_of_le_add`], which handles `s` added on the LEFT.
fn le_sub_of_le_add_right(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    s: ExprId,
    h: ExprId,
) -> ExprId {
    let neg_s = cneg(d, p, s);
    let ys = cadd(d, p, y, s);
    let refl_neg_s = d.lemma(p.le_refl, &[neg_s]);
    let step1 = d.lemma(p.add_le_add, &[x, ys, neg_s, neg_s, h, refl_neg_s]);
    // step1 : le (add x neg_s) (add ys neg_s)
    let lhs = cadd(d, p, x, neg_s);
    let rhs = cadd(d, p, ys, neg_s);
    let cancel = cancel_added_right(d, p, y, s); // Equiv rhs y
    let refl_lhs = d.lemma(p.equiv_refl, &[lhs]);
    d.lemma(p.le_congr, &[lhs, lhs, rhs, y, refl_lhs, cancel, step1])
}

/// `le (add x (neg s)) y -> le x (add y s)` — the inverse of
/// [`le_sub_of_le_add_right`]: add `s` back to recover the un-subtracted
/// bound.
pub(super) fn le_add_of_le_sub_right(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    s: ExprId,
    y: ExprId,
    h: ExprId,
) -> ExprId {
    let refl_s = d.lemma(p.le_refl, &[s]);
    let neg_s = cneg(d, p, s);
    let x_negs = cadd(d, p, x, neg_s);
    let step1 = d.lemma(p.add_le_add, &[x_negs, y, s, s, h, refl_s]);
    // step1 : le (add x_negs s) (add y s)
    let lhs = cadd(d, p, x_negs, s);
    let rhs = cadd(d, p, y, s);
    let cancel = sub_then_add_cancel(d, p, x, s); // Equiv lhs x
    let refl_rhs = d.lemma(p.equiv_refl, &[rhs]);
    d.lemma(p.le_congr, &[lhs, x, rhs, rhs, cancel, refl_rhs, step1])
}

/// Admit [`CrossingNames::crossing_close_clamped`]. See the module
/// documentation section just above and that field's own doc comment for
/// the statement and for why both domain-membership hypotheses
/// [`declare_crossing_close`] needs (`a ≤ samplePt`, `samplePt ≤ b`) are
/// gone from this theorem's signature rather than merely re-derived inside
/// it.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here
/// means the kernel **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_crossing_close_clamped(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rat_ty_ = crate::rat_prelude::ops::rat_ty(d);
    let fn_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let delta_fv = d.fresh_fvar();
    let delta = d.kernel().fvar(delta_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let zero_rat = rzero(d, p.rat);
    let hpos_ty = d.const_app(p.rat.lt, &[zero_rat, delta]);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let hac_ty = cle(d, p, a, c);
    let hac_fv = d.fresh_fvar();
    let hac = d.kernel().fvar(hac_fv);
    let hcb_ty = cle(d, p, c, b);
    let hcb_fv = d.fresh_fvar();
    let hcb = d.kernel().fvar(hcb_fv);

    let slack = sample_slack(d, p, a, c, delta);
    let clamped_pt = d.const_app(p.min, &[slack.sample_pt, b]);

    let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let outer = d.apply(modulus_fn, &[e]);
    let one_nat = d.num(1);
    let bound_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, outer]);
    let bound_embed = embed(d, p, bound_rat);

    let h_upper_ty = cle(d, p, slack.slack_upper, bound_embed);
    let h_upper_fv = d.fresh_fvar();
    let h_upper = d.kernel().fvar(h_upper_fv);
    let neg_slack_lower = cneg(d, p, slack.slack_lower);
    let h_lower_ty = cle(d, p, neg_slack_lower, bound_embed);
    let h_lower_fv = d.fresh_fvar();
    let h_lower = d.kernel().fvar(h_lower_fv);

    // --- the proof body -------------------------------------------------

    let hu_sample = d.lemma(p.crossing.crossing_sample_upper, &[a, c, delta, hpos]);
    // hu_sample : le c (add samplePt slackUpper)
    let hl_sample = d.lemma(p.crossing.crossing_sample_lower, &[a, c, delta, hpos, hac]);
    // hl_sample : le (add samplePt slackLower) c

    // --- domain membership: `a ≤ clampedPt` and `clampedPt ≤ b`, both
    // unconditional on the mesh, no case split -----------------------------

    let a_le_samplept = d.lemma(p.crossing.crossing_sample_ge_a, &[a, c, delta, hpos]);
    let a_le_b = d.lemma(p.le_trans, &[a, c, b, hac, hcb]);
    let hap_clamped = d.lemma(p.le_min, &[slack.sample_pt, b, a, a_le_samplept, a_le_b]);
    let hpb_clamped = d.lemma(p.min_le_right, &[slack.sample_pt, b]);

    // --- upper half: `c - clampedPt ≤ bound_embed`, via `le_min` on
    // `c - bound_embed` -----------------------------------------------------

    let refl_samplept = d.lemma(p.le_refl, &[slack.sample_pt]);
    let samplept_plus_upper = cadd(d, p, slack.sample_pt, slack.slack_upper);
    let samplept_plus_bound = cadd(d, p, slack.sample_pt, bound_embed);
    let widen_upper = d.lemma(
        p.add_le_add,
        &[
            slack.sample_pt,
            slack.sample_pt,
            slack.slack_upper,
            bound_embed,
            refl_samplept,
            h_upper,
        ],
    );
    let hs_direct = d.lemma(
        p.le_trans,
        &[
            c,
            samplept_plus_upper,
            samplept_plus_bound,
            hu_sample,
            widen_upper,
        ],
    );
    // hs_direct : le c (add samplePt bound_embed)

    let nonneg_bound = d.lemma(p.rat.zero_le_nat_div_succ, &[one_nat, outer]);
    let b_plus_bound = cadd(d, p, b, bound_embed);
    let b_le_b_plus = d.lemma(p.le_add_of_nonneg, &[b, bound_rat, nonneg_bound]);
    let hb_direct = d.lemma(p.le_trans, &[c, b, b_plus_bound, hcb, b_le_b_plus]);
    // hb_direct : le c (add b bound_embed)

    let hs_prime = le_sub_of_le_add_right(d, p, c, slack.sample_pt, bound_embed, hs_direct);
    // hs_prime : le (add c (neg bound_embed)) samplePt
    let hb_prime = le_sub_of_le_add_right(d, p, c, b, bound_embed, hb_direct);
    // hb_prime : le (add c (neg bound_embed)) b

    let neg_bound_embed = cneg(d, p, bound_embed);
    let z_val = cadd(d, p, c, neg_bound_embed);
    let hz = d.lemma(p.le_min, &[slack.sample_pt, b, z_val, hs_prime, hb_prime]);
    // hz : le z_val clampedPt

    let h_a_bound = le_add_of_le_sub_right(d, p, c, bound_embed, clamped_pt, hz);
    // h_a_bound : le c (add clampedPt bound_embed)
    let h1p = le_sub_of_le_add(d, p, c, clamped_pt, bound_embed, h_a_bound);
    // h1p : le (add c (neg clampedPt)) bound_embed

    let x_val_clamped = {
        let neg_clamped = cneg(d, p, clamped_pt);
        cadd(d, p, c, neg_clamped)
    };

    // --- lower half: `clampedPt - c ≤ bound_embed`, via `min_le_left` and
    // plain transitivity, no `le_min` needed -------------------------------

    let h2 = le_sub_of_add_le_left(d, p, slack.sample_pt, slack.slack_lower, c, hl_sample);
    // h2 : le slackLower x_val   (x_val = add c (neg samplePt))
    let x_val = {
        let neg_samplept_local = cneg(d, p, slack.sample_pt);
        cadd(d, p, c, neg_samplept_local)
    };

    let min_le_left_inst = d.lemma(p.min_le_left, &[slack.sample_pt, b]);
    // min_le_left_inst : le clampedPt samplePt
    let neg_samplept = cneg(d, p, slack.sample_pt);
    let neg_clamped = cneg(d, p, clamped_pt);
    let neg_le_neg_inst = d.lemma(
        p.neg_le_neg,
        &[clamped_pt, slack.sample_pt, min_le_left_inst],
    );
    // neg_le_neg_inst : le (neg samplePt) (neg clampedPt)
    let refl_c2 = d.lemma(p.le_refl, &[c]);
    let x_to_xclamped = d.lemma(
        p.add_le_add,
        &[c, c, neg_samplept, neg_clamped, refl_c2, neg_le_neg_inst],
    );
    // x_to_xclamped : le x_val x_val_clamped
    let h2_chain = d.lemma(
        p.le_trans,
        &[slack.slack_lower, x_val, x_val_clamped, h2, x_to_xclamped],
    );
    // h2_chain : le slackLower x_val_clamped
    let neg_x_val_clamped = cneg(d, p, x_val_clamped);
    let h2n = d.lemma(p.neg_le_neg, &[slack.slack_lower, x_val_clamped, h2_chain]);
    // h2n : le (neg x_val_clamped) (neg slackLower)
    let h2p = d.lemma(
        p.le_trans,
        &[
            neg_x_val_clamped,
            neg_slack_lower,
            bound_embed,
            h2n,
            h_lower,
        ],
    );
    // h2p : le (neg x_val_clamped) bound_embed

    let abs_bound = d.lemma(p.abs_le, &[x_val_clamped, bound_embed, h1p, h2p]);
    // abs_bound : le (abs x_val_clamped) bound_embed

    let uc_spec_term = d.const_app(p.uc_spec, &[f, a, b, u]);
    let conclusion_proof = d.apply(
        uc_spec_term,
        &[
            e,
            c,
            clamped_pt,
            hac,
            hcb,
            hap_clamped,
            hpb_clamped,
            abs_bound,
        ],
    );

    let out_rat_e = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let fc = d.apply(f, &[c]);
    let f_clamped = d.apply(f, &[clamped_pt]);
    let conclusion_ty = close_within(d, p, fc, f_clamped, out_rat_e);

    let ty = {
        let after_hlower = d.arrow(h_lower_ty, conclusion_ty);
        let after_hupper = d.arrow(h_upper_ty, after_hlower);
        let after_hcb = d.arrow(hcb_ty, after_hupper);
        let after_hac = d.arrow(hac_ty, after_hcb);
        let after_hpos = d.arrow(hpos_ty, after_hac);
        let after_u = d.pi_fv(u_fv, u_ty, after_hpos);
        let over_e = d.pi_fv(e_fv, nat, after_u);
        let over_delta = d.pi_fv(delta_fv, rat_ty_, over_e);
        let over_c = d.pi_fv(c_fv, carrier, over_delta);
        let over_b = d.pi_fv(b_fv, carrier, over_c);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, fn_ty, over_a)
    };
    let value = {
        let with_hlower = d.lam_fv(h_lower_fv, h_lower_ty, conclusion_proof);
        let with_hupper = d.lam_fv(h_upper_fv, h_upper_ty, with_hlower);
        let with_hcb = d.lam_fv(hcb_fv, hcb_ty, with_hupper);
        let with_hac = d.lam_fv(hac_fv, hac_ty, with_hcb);
        let with_hpos = d.lam_fv(hpos_fv, hpos_ty, with_hac);
        let with_u = d.lam_fv(u_fv, u_ty, with_hpos);
        let over_e = d.lam_fv(e_fv, nat, with_u);
        let over_delta = d.lam_fv(delta_fv, rat_ty_, over_e);
        let over_c = d.lam_fv(c_fv, carrier, over_delta);
        let over_b = d.lam_fv(b_fv, carrier, over_c);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, fn_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.crossing.crossing_close_clamped,
        uparams: vec![],
        ty,
        value,
    })
}

// --- `riemannSampleCrossingClose`: the FIRST SLICE of the cross-mesh
// whole-sum bound (`integral.rs`'s SEVENTH 2026-08-27 module doc entry) --
// [`declare_crossing_close_clamped`] specialized at `c := ptI`, an ordinary
// Riemann-sum sample point, RESTRICTED to a rational `deltaAc` -- see
// [`CrossingNames::crossing_sample_pairing_close`]'s own doc comment for why
// the restriction is load-bearing (`crossingIndex`'s step is `Rat`, not
// `CReal`) and precisely what would be needed to lift it. -----------------

/// Admit [`CrossingNames::crossing_sample_pairing_close`]. See that field's
/// own doc comment for the statement and for the general (non-rational
/// `deltaAc`) case this does NOT attempt.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here
/// means the kernel **refused** a proof, not that a script gave up.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_crossing_sample_pairing_close(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rat_ty_ = crate::rat_prelude::ops::rat_ty(d);
    let fn_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let u_ty = d.const_app(p.uniformly_continuous_on, &[f, a, b]);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);

    let step_ab_fv = d.fresh_fvar();
    let step_ab = d.kernel().fvar(step_ab_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let delta_ac_fv = d.fresh_fvar();
    let delta_ac = d.kernel().fvar(delta_ac_fv);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);

    // pt_i := a + (ofNat i) * step_ab -- the [a,b]-mesh's i-th sample point
    // for an ARBITRARY CReal step `step_ab` (not necessarily `riemannSum`'s
    // own `delta_of`, which this file cannot see -- reproduced verbatim from
    // `integral.rs`'s private `sample_point`, per this file's own
    // per-module-copy convention).
    let of_nat_i = d.const_app(p.of_nat, &[i]);
    let i_step = cmul(d, p, of_nat_i, step_ab);
    let pt_i = cadd(d, p, a, i_step);

    let zero_rat = rzero(d, p.rat);
    let hpos_ty = d.const_app(p.rat.lt, &[zero_rat, delta_ac]);
    let hpos_fv = d.fresh_fvar();
    let hpos = d.kernel().fvar(hpos_fv);

    let hai_ty = cle(d, p, a, pt_i);
    let hai_fv = d.fresh_fvar();
    let hai = d.kernel().fvar(hai_fv);
    let hib_ty = cle(d, p, pt_i, b);
    let hib_fv = d.fresh_fvar();
    let hib = d.kernel().fvar(hib_fv);

    // Same recipe `declare_crossing_close_clamped` uses internally at
    // `(a, c, delta) := (a, pt_i, delta_ac)`, rebuilt here so this
    // declaration's own hypothesis/conclusion types are the IDENTICAL
    // `ExprId` shapes the `crossing_close_clamped` application below
    // produces by substitution.
    let slack = sample_slack(d, p, a, pt_i, delta_ac);
    let clamped_pt = d.const_app(p.min, &[slack.sample_pt, b]);

    let modulus_fn = d.const_app(p.uc_modulus, &[f, a, b, u]);
    let outer = d.apply(modulus_fn, &[e]);
    let one_nat = d.num(1);
    let bound_rat = d.const_app(p.rat.nat_div_succ, &[one_nat, outer]);
    let bound_embed = embed(d, p, bound_rat);

    let h_upper_ty = cle(d, p, slack.slack_upper, bound_embed);
    let h_upper_fv = d.fresh_fvar();
    let h_upper = d.kernel().fvar(h_upper_fv);
    let neg_slack_lower = cneg(d, p, slack.slack_lower);
    let h_lower_ty = cle(d, p, neg_slack_lower, bound_embed);
    let h_lower_fv = d.fresh_fvar();
    let h_lower = d.kernel().fvar(h_lower_fv);

    // --- the proof body: a direct application of `crossing_close_clamped`
    // at `c := pt_i`, `delta := delta_ac` -----------------------------------

    let proof_body = d.lemma(
        p.crossing.crossing_close_clamped,
        &[
            f, a, b, pt_i, delta_ac, e, u, hpos, hai, hib, h_upper, h_lower,
        ],
    );

    let out_rat_e = d.const_app(p.rat.nat_div_succ, &[one_nat, e]);
    let f_pt_i = d.apply(f, &[pt_i]);
    let f_clamped = d.apply(f, &[clamped_pt]);
    let conclusion_ty = close_within(d, p, f_pt_i, f_clamped, out_rat_e);

    let ty = {
        let after_hlower = d.arrow(h_lower_ty, conclusion_ty);
        let after_hupper = d.arrow(h_upper_ty, after_hlower);
        let after_hib = d.arrow(hib_ty, after_hupper);
        let after_hai = d.arrow(hai_ty, after_hib);
        let after_hpos = d.arrow(hpos_ty, after_hai);
        let over_e = d.pi_fv(e_fv, nat, after_hpos);
        let over_delta_ac = d.pi_fv(delta_ac_fv, rat_ty_, over_e);
        let over_i = d.pi_fv(i_fv, nat, over_delta_ac);
        let over_step_ab = d.pi_fv(step_ab_fv, carrier, over_i);
        let after_u = d.pi_fv(u_fv, u_ty, over_step_ab);
        let over_b = d.pi_fv(b_fv, carrier, after_u);
        let over_a = d.pi_fv(a_fv, carrier, over_b);
        d.pi_fv(f_fv, fn_ty, over_a)
    };
    let value = {
        let with_hlower = d.lam_fv(h_lower_fv, h_lower_ty, proof_body);
        let with_hupper = d.lam_fv(h_upper_fv, h_upper_ty, with_hlower);
        let with_hib = d.lam_fv(hib_fv, hib_ty, with_hupper);
        let with_hai = d.lam_fv(hai_fv, hai_ty, with_hib);
        let with_hpos = d.lam_fv(hpos_fv, hpos_ty, with_hai);
        let over_e = d.lam_fv(e_fv, nat, with_hpos);
        let over_delta_ac = d.lam_fv(delta_ac_fv, rat_ty_, over_e);
        let over_i = d.lam_fv(i_fv, nat, over_delta_ac);
        let over_step_ab = d.lam_fv(step_ab_fv, carrier, over_i);
        let with_u = d.lam_fv(u_fv, u_ty, over_step_ab);
        let over_b = d.lam_fv(b_fv, carrier, with_u);
        let over_a = d.lam_fv(a_fv, carrier, over_b);
        d.lam_fv(f_fv, fn_ty, over_a)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.crossing.crossing_sample_pairing_close,
        uparams: vec![],
        ty,
        value,
    })
}

/// The kernel names `creal/crossing.rs` declares.
///
/// One of ADR-1512's per-module registries behind the [`CRealPrelude`]
/// facade: the field, its documentation and its interning all live
/// beside the `declare_*` that uses them, so a declaration added here
/// does not touch `creal.rs` at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CrossingNames {
    /// `CReal.crossingIndex : CReal → CReal → Rat → Nat` — the Archimedean
    /// **crossing index**: given a base `a`, a target `c` and a positive
    /// rational step `Δ`, the computed count of `Δ`-steps from `a` at which
    /// `c` is reached, within a small fixed slack. `crossingIndex a c delta
    /// := bucketIndex (mul (ofRat (Rat.inv delta)) (add c (neg a))) 0` —
    /// rescale `c − a` by `Δ⁻¹` and read [`super::CRealPrelude::bucket_index`] at the FIXED
    /// grid `k := 0` (step `1`), reducing an arbitrary step to the one
    /// `bucketIndex` already handles. Computed, never `Exists`-derived. See
    /// `creal/crossing.rs`.
    pub crossing_index: NameId,
    /// `CReal.crossingUpper : ∀ a c delta, Rat.lt Rat.zero delta →
    /// CReal.le c (CReal.add a (CReal.mul (CReal.ofRat delta) (CReal.ofRat
    /// (Rat.add (Rat.natDivSucc (Nat.succ (CReal.crossingIndex a c delta)) 0)
    /// (Rat.natDivSucc 2 j)))))`, `j` the closed term `bucketIndex` samples
    /// at when `k = 0` (`(succ 0)*(succ 0)`, definitionally `1`).
    ///
    /// **Needs only `0 < Δ` — no `a ≤ c` hypothesis at all.** Both
    /// `bucketIndexFloorUpper` and `bucketClampUpper` are unconditional, and
    /// scaling a `CReal.le` fact by a positive rational preserves it
    /// regardless of `c − a`'s sign. See `creal/crossing.rs`.
    pub crossing_upper: NameId,
    /// `CReal.crossingLower : ∀ a c delta, Rat.lt Rat.zero delta →
    /// CReal.le a c → CReal.le (CReal.add a (CReal.mul (CReal.ofRat delta)
    /// (CReal.ofRat (Rat.sub (Rat.natDivSucc (CReal.crossingIndex a c delta)
    /// 0) (Rat.natDivSucc 3 j))))) c`.
    ///
    /// **Genuinely needs `a ≤ c`** (unlike [`super::CrossingNames::crossing_upper`]):
    /// `bucketClampLower`'s hypothesis is `0 ≤` the value being bucketed —
    /// here `(c−a)·Δ⁻¹` — which `a ≤ c` supplies via `CReal.mul_nonneg` on
    /// the two nonnegative factors. See `creal/crossing.rs`.
    pub crossing_lower: NameId,
    /// `CReal.crossingSampleGeA : ∀ a c delta, Rat.lt Rat.zero delta →
    /// CReal.le a (CReal.add a (CReal.mul (CReal.ofNat (CReal.crossingIndex a
    /// c delta)) (CReal.ofRat delta)))` — `samplePt` (the SAME closed term
    /// [`super::CrossingNames::crossing_sample_upper`]/[`super::CrossingNames::crossing_sample_lower`] use)
    /// never falls BELOW its own base point `a`.
    ///
    /// **Needs only `0 < Δ` — no `a ≤ c` hypothesis at all**, unlike
    /// [`super::CrossingNames::crossing_lower`]: `crossingIndex` embeds as a nonnegative
    /// `Nat` regardless of `c`'s position, and `Δ > 0` makes the product
    /// nonnegative too, via [`super::CRealPrelude::mul_nonneg`] — the same shape
    /// `integral.rs`'s `riemannSum_sample_in_bounds` already proves for an
    /// ordinary mesh sample. This is HALF of `crossingClose`'s domain
    /// membership hypothesis pair; the other half, `samplePt ≤ b`, is
    /// discharged nowhere in this prelude — see `creal/integral.rs`'s
    /// 2026-08-27 module doc entries (the fifth: it is not a `+3`-slack
    /// artifact of [`super::CRealPrelude::bucket_index_bound`] and cannot be fixed by
    /// tightening that bound, however far). See `creal/crossing.rs`.
    pub crossing_sample_ge_a: NameId,
    /// `CReal.crossingSampleUpper : ∀ a c delta, Rat.lt Rat.zero delta →
    /// CReal.le c (CReal.add (CReal.add a (CReal.mul (CReal.ofNat
    /// (CReal.crossingIndex a c delta)) delta)) (CReal.add delta (CReal.mul
    /// delta (CReal.ofRat (Rat.natDivSucc 2 j)))))` — [`super::CrossingNames::crossing_upper`]
    /// restated against an ORDINARY Riemann-sum sample point `a + ofNat(i)·Δ`
    /// (`integral.rs`'s own `sample_point` shape) rather than the raw
    /// rational bound `crossingUpper` computes internally: `c` is within a
    /// fixed slack (unreduced here, but equal to `2Δ`) ABOVE the coarse
    /// mesh's `crossingIndex`-th sample point. See `creal/crossing.rs`.
    pub crossing_sample_upper: NameId,
    /// `CReal.crossingSampleLower : ∀ a c delta, Rat.lt Rat.zero delta →
    /// CReal.le a c → CReal.le (CReal.add (CReal.add a (CReal.mul (CReal.ofNat
    /// (CReal.crossingIndex a c delta)) delta)) (CReal.mul delta (CReal.ofRat
    /// (Rat.neg (Rat.natDivSucc 3 j))))) c` — the mirror of
    /// [`super::CrossingNames::crossing_sample_upper`]: `c` is no more than a fixed slack
    /// (`1.5Δ`, left as `Δ·(negative rational)` rather than rewritten to
    /// `neg(Δ·positive)`) BELOW the same sample point. See
    /// `creal/crossing.rs`.
    pub crossing_sample_lower: NameId,
    /// `CReal.crossingClose : ∀ F a b c delta e (u : UniformlyContinuousOn F
    /// a b), Rat.lt Rat.zero delta → CReal.le a c → CReal.le c b → CReal.le a
    /// samplePt → CReal.le samplePt b → CReal.le slackUpper (CReal.ofRat
    /// (Rat.natDivSucc 1 (UniformlyContinuousOn.modulus F a b u e))) →
    /// CReal.le (CReal.neg slackLower) (CReal.ofRat (Rat.natDivSucc 1
    /// (UniformlyContinuousOn.modulus F a b u e))) → CReal.le (CReal.abs
    /// (CReal.add (F c) (CReal.neg (F samplePt)))) (CReal.ofRat
    /// (Rat.natDivSucc 1 e))`, `samplePt`/`slackUpper`/`slackLower` the SAME
    /// closed terms [`super::CrossingNames::crossing_sample_upper`]/
    /// [`super::CrossingNames::crossing_sample_lower`] place `c` within.
    ///
    /// The analytic half of the cross-width Riemann comparison's single
    /// block: `F(c)` is close to `F` at the coarse mesh's crossing-index
    /// sample point, PROVIDED the two crossing slacks (`≈2Δ`, `≈1.5Δ`) are
    /// already within `UniformlyContinuousOn`'s modulus at accuracy `e`.
    /// Does **not** derive that Archimedean smallness from a mesh count, nor
    /// `samplePt`'s own domain membership — both are explicit hypotheses
    /// here. The first is now DISCHARGEABLE in general via
    /// [`super::CRealPrelude::mesh_scaled_le_of_ge`] (not yet wired into this theorem's own
    /// statement). The second remains open, and is NOT merely unattempted —
    /// `integral.rs`'s third 2026-08-27 module doc entry works through the
    /// natural reading of "a mesh count `m`" for this theorem's `Rat`-typed
    /// `Δ` and finds it does not make `samplePt ≤ b` provable from `m`
    /// alone without also bounding the interval's own Archimedean constant,
    /// which is data about `[a,b]`, not about `m`. See `creal/crossing.rs`
    /// and `creal/integral.rs`'s 2026-08-27 module doc entries (all five —
    /// the fourth tests and REFUTES, with an exact worked bound, the
    /// hypothesis that fixing `[a,b]` (so `magnitude` is a known constant)
    /// rescues this via `bucket_index_bound`'s `+4` slack; the fifth then
    /// builds the tighter, purpose-built `crossingIndex` bound the fourth
    /// called for — a genuine, ZERO-excess replacement — and shows it STILL
    /// does not rescue `samplePt ≤ b`, because the real obstruction is
    /// `CReal.bound`'s own non-tight over-estimate of `b − a`
    /// (`magnitude`), independent of `crossingIndex`'s tightness, plus
    /// `crossingLower`'s own already-fixed `1.5Δ` closeness slack). Still
    /// open, and not reachable by any further `crossingIndex`-side
    /// tightening — [`super::CrossingNames::crossing_sample_ge_a`] discharges the OTHER half
    /// of this pair (`a ≤ samplePt`, unconditionally on `0 < Δ`).
    pub crossing_close: NameId,
    /// `CReal.crossingCloseClamped : ...` -- `crossingClose` with `samplePt`
    /// replaced by `clampedPt := CReal.min samplePt b`.
    ///
    /// Both domain-membership hypotheses `crossingClose` needs (`a <=
    /// samplePt`, `samplePt <= b`) are GONE from this statement, discharged
    /// by construction rather than assumed: `clampedPt <= b` is
    /// `min_le_right`, unconditional; `a <= clampedPt` is `le_min` applied
    /// to `crossingSampleGeA` (`a <= samplePt`) and `a <= b` (`le_trans` on
    /// the two hypotheses this theorem already carries). `samplePt <= b` is
    /// not itself provable (per `integral.rs`'s 2026-08-27 module doc
    /// entries), but the theorem never needed `samplePt` un-clamped --
    /// clamping into range costs nothing (`min` is fully constructive, no
    /// comparison decided) and the closeness bound survives the
    /// substitution via the SAME `le_min` move applied to `c - bound_embed`:
    /// `c - bound_embed <= samplePt` (from `crossingSampleUpper` widened by
    /// the `h_upper` hypothesis) and `c - bound_embed <= b` (from `hcb`
    /// widened by `le_add_of_nonneg`) give, by `le_min`, `c - bound_embed <=
    /// clampedPt`, and adding `bound_embed` back gives the upper half
    /// `abs_le` needs. The lower half needs no `le_min` at all: `clampedPt
    /// <= samplePt` (`min_le_left`) transfers `crossingSampleLower`'s
    /// existing bound on `c - samplePt` up to `c - clampedPt` by plain
    /// transitivity, no case split anywhere. See `creal/crossing.rs`.
    pub crossing_close_clamped: NameId,
    /// `CReal.riemannSampleCrossingClose : ∀ F a b (u : UniformlyContinuousOn
    /// F a b) stepAb i deltaAc e, Rat.lt Rat.zero deltaAc → CReal.le a ptI →
    /// CReal.le ptI b → CReal.le slackUpper bound → CReal.le (CReal.neg
    /// slackLower) bound → CReal.le (CReal.abs (CReal.add (F ptI) (CReal.neg
    /// (F clampedPt)))) (CReal.ofRat (Rat.natDivSucc 1 e))`, where `ptI := a +
    /// (ofNat i)·stepAb` is an ORDINARY Riemann-sum sample point (`stepAb` an
    /// arbitrary `CReal`, not necessarily `riemannSum`'s own mesh step) and
    /// `clampedPt`/`slackUpper`/`slackLower` are [`super::CrossingNames::crossing_close_clamped`]'s
    /// own terms at `c := ptI`, `delta := deltaAc`.
    ///
    /// `integral.rs`'s SEVENTH 2026-08-27 module doc entry's proposed
    /// term-pairing lemma — literally [`super::CrossingNames::crossing_close_clamped`]
    /// specialized at `c := ptI` — **restricted to the one case that
    /// type-checks against this file's existing machinery**: `crossingIndex`
    /// (hence `crossingCloseClamped`) takes its step as a `Rat`, not a
    /// `CReal` (`declare_crossing_index`'s `delta` parameter is `rat_ty_`
    /// itself, not `creal_ty`). The natural cross-mesh step for an ARBITRARY
    /// split point `c`, `deltaAc := (c−a)·ofRat(natDivSucc 1 m_ac)`, is
    /// `CReal`-valued whenever `c−a` is not itself rational — the same "not a
    /// computable rational multiple" fact `integral.rs`'s module doc already
    /// names, sharpened here to the exact type-level obstruction: this
    /// theorem is only USABLE when the caller already has a **rational**
    /// `deltaAc` in hand (e.g. `c := a + ofRat q` for some `Rat q`, giving
    /// `deltaAc := q·natDivSucc(1,m_ac)`, itself `Rat`), not for a fully
    /// general `CReal c`.
    ///
    /// The only `CReal`-level inverse in this prelude,
    /// [`super::CRealPrelude::inv`] `(x : CReal) (k : Nat) (h : PosBound x k) : CReal`,
    /// could in principle build `(c−a)⁻¹` given an explicit positivity
    /// witness, but none of `crossing.rs`'s internal recipe (`build_scaled`,
    /// `scale_cancels`, the four `bucketIndex` closeness lemmas'
    /// composition) is stated against it — it is hard-wired to `Rat.inv`.
    /// Pre-rescaling `ptI` by `(c−a)⁻¹` before calling `crossingIndex` (so
    /// `crossingIndex` itself only ever sees a plain `Rat` delta) is possible
    /// in principle, but translating the resulting NORMALIZED-coordinate
    /// closeness bound back into a bound on `|ptI − ptAc(j(i))|` in ORIGINAL
    /// units needs multiplying back through by the `CReal` factor `(c−a)`,
    /// which is a REAL (not `Nat`, unlike [`super::CRealPrelude::mesh_scaled_le_of_ge`])
    /// scaling step with no existing lemma covering it — a second gap on top
    /// of `crossingCloseClamped`'s own already-flagged ones. See
    /// `creal/crossing.rs`.
    pub crossing_sample_pairing_close: NameId,
}

impl CrossingNames {
    /// Interns this module's names under the `CReal` root.
    ///
    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel
    /// spelling of each name sits in the file that declares it.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            crossing_index: kernel.name_str(creal, "crossingIndex"),
            crossing_upper: kernel.name_str(creal, "crossingUpper"),
            crossing_lower: kernel.name_str(creal, "crossingLower"),
            crossing_sample_ge_a: kernel.name_str(creal, "crossingSampleGeA"),
            crossing_sample_upper: kernel.name_str(creal, "crossingSampleUpper"),
            crossing_sample_lower: kernel.name_str(creal, "crossingSampleLower"),
            crossing_close: kernel.name_str(creal, "crossingClose"),
            crossing_close_clamped: kernel.name_str(creal, "crossingCloseClamped"),
            crossing_sample_pairing_close: kernel.name_str(creal, "riemannSampleCrossingClose"),
        }
    }
}
