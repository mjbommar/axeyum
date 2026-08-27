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
//! of `∃ i, …`. [`CRealPrelude::crossing_index`] is a `Definition` — one
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

/// Admit [`CRealPrelude::crossing_index`]. See the module documentation for
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
        name: p.crossing_index,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(super::DERIVED_HEIGHT + 100),
    })
}

/// Admit [`CRealPrelude::crossing_upper`]. See the module documentation for
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
        name: p.crossing_upper,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit [`CRealPrelude::crossing_lower`]. See the module documentation for
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
        name: p.crossing_lower,
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

/// Admit [`CRealPrelude::crossing_sample_upper`]: `∀ a c Δ, Rat.lt Rat.zero
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
    let hu = d.lemma(p.crossing_upper, &[a, c, delta, hpos]);

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
        name: p.crossing_sample_upper,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit [`CRealPrelude::crossing_sample_lower`]: `∀ a c Δ, Rat.lt Rat.zero
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
    let hl = d.lemma(p.crossing_lower, &[a, c, delta, hpos, hac]);

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
        name: p.crossing_sample_lower,
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
    declare_crossing_lower(d, p)
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
