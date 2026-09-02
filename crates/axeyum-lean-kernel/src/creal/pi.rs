//! **`CReal.pi`** — π as a constructed real, with `3 ≤ π ≤ 4`.
//!
//! ## The obstruction this file does NOT hit
//!
//! π is routinely *defined* as twice the first positive root of `cos`, and
//! `creal/ivt.rs` refutes the exact-root construction constructively
//! ([`IvtBoundaryNames::ivt_exact_root_decides_sign`]). That refutation is a
//! statement about **one definition of π**, not about π: the number itself is
//! the sum of a rational series, and a series needs no root, no intermediate
//! value theorem, and no case analysis on a sign. This file builds it that
//! way, by `CReal.mk` on an explicit regular sequence — exactly as
//! `creal/exponential.rs` builds [`CRealPrelude::e`] and `creal/trig.rs`
//! builds [`CRealPrelude::cos_one`].
//!
//! ## Which series, and why not the obvious one
//!
//! Not Leibniz (`π/4 = Σ (−1)ᵏ/(2k+1)`). Its terms are **not** dominated by
//! any geometric series, so the one piece of machinery that makes a
//! constructed-real series cheap here — `Cauchy (sumRange expDominant)` at a
//! CONCRETE witness, reused unchanged from `CReal.e` — does not apply to it,
//! and its slow convergence puts every numeric bound out of reach of this
//! kernel's unary `Nat` arithmetic (`3 ≤ π` would need 14 terms and a common
//! denominator over five digits).
//!
//! This file uses **Euler's transform of Leibniz**:
//!
//! ```text
//!   π/2  =  Σ_{k≥0}  2ᵏ (k!)² / (2k+1)!
//!        =  1 + 1/3 + 2/15 + 2/35 + …
//! ```
//!
//! Three properties make it the right choice here, and each was checked
//! numerically before any Rust was written
//! (`scripts/check-pi-series-numeric.py`, re-runnable, with mutations that
//! must be refuted):
//!
//! 1. **The terms are defined by a RECURSION, so the ratio is definitional.**
//!    [`PiNames::pi_half_coef`] is `t 0 = 1/1`, `t (k+1) = t k ·
//!    (k+1)/(2k+3)`, a `Nat.rec` into `Rat`. Nothing has to be proved to get
//!    from `t k` to `t (k+1)`: ι-reduction does it. The closed form
//!    `2ᵏ(k!)²/(2k+1)!` is never built, so no factorial identity is ever
//!    needed.
//! 2. **The ratio is `≤ 1/2` at every `k`** — `(k+1)/(2k+3) ≤ 1/2` is
//!    `2k+2 ≤ 2k+3`, with no case split — so `t k ≤ (1/2)ᵏ` by a short
//!    induction, and the domination `abs (piHalfTerm k) ≤ expDominant k` that
//!    `CReal.e`'s concrete Cauchy witness consumes follows immediately.
//!    **All terms are positive**, so there is no sign factor, no `(−1)ᵏ`, and
//!    none of `creal/alternating.rs`'s pairing machinery is needed.
//! 3. **It converges fast enough that both bounds stay in small `Nat`s.**
//!    `π ≤ 4` needs no terms at all (every partial sum is `≤ 2` by the same
//!    geometric bound, via [`CRealPrelude::sum_pow_half_closed_form`]), and
//!    `3 ≤ π` needs four. Every numeral this prelude builds is unary and the
//!    kernel's binary-literal fast path never fires, so a four-digit
//!    `Nat.gcd` costs tens of seconds — the reason the series choice is
//!    driven by arithmetic size and not only by convergence.
//!
//! ## The doubled index
//!
//! Written `Nat.add k k`, never `Nat.mul 2 k`. `Nat.add` recurses on its
//! RIGHT argument, so with the symbolic side on the left the term is stuck
//! rather than half-reduced, and the one index identity this file needs
//! (`(k+1)·1 + k = Nat.succ (Nat.add k k)`) is one `Nat.mul_one` plus one
//! `Nat.succ_add`.
//!
//! ## What this file deliberately does NOT build
//!
//! - **`CReal.sin`/`CReal.cos` at a general argument, and π as a root.** The
//!   general power-series row needs a bound depending on `|x|`;
//!   `CReal.cosFnWide` exists for that, and relating `pi` to it is a
//!   separate, larger task.
//! - **A sharper bound than `3 ≤ π ≤ 4`.** Tightening the top needs the tail
//!   bounded from index 4 rather than from index 0 — a re-indexed domination,
//!   not a corollary of what is here. The identical call
//!   `exponential.rs::declare_e_le_four` makes for `e ≤ 4` versus `e ≤ 3`.

use super::convergence::{
    converges_applied, converges_predicate, div_succ_at, exists_intro, kregular_of_cauchy_proof,
};
use super::series::sum_range_cauchy_body;
use super::trig::{
    cabs, cadd, cle, cmul, cneg, czero, exp_dominant_cauchy_body_concrete, one_c,
    promote_ordered_half_to_full, two, two_normalize,
};
use super::{CRealPrelude, DERIVED_HEIGHT, creal_ty, div_succ, embed, sample, within};
use crate::Kernel;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::{BinderInfo, ExprId};
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{nat_rewrite_prop, radd, rat_eq_rewrite, rat_ty, rle, rmul, rzero};

/// Height for the `pi` family's thin definitional wrappers, mirroring
/// `trig.rs::TRIG_HEIGHT`.
const PI_HEIGHT: u16 = DERIVED_HEIGHT + 1;

/// Admit the whole `CReal.pi` family. Run after `trig::declare_trig` (this
/// file reuses that module's `pub(super)` concrete Cauchy witness for
/// `Cauchy (sumRange expDominant)`, which is `CReal.e`'s own).
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_pi_family(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_pi_half_coef(d, p)?;
    declare_pi_half_term(d, p)?;
    declare_pi_half_series_partial(d, p)?;
    declare_pi_half_coef_nonneg(d, p)?;
    declare_pi_half_term_nonneg(d, p)?;
    declare_pi_half_term_le_pow_half(d, p)?;
    declare_pi_half_term_abs_le_dominant(d, p)?;
    // The ingredients are computed ONCE and threaded into BOTH
    // `declare_pi_half` and `declare_pi_half_converges` -- mirroring
    // `exponential.rs::declare_e_family`'s own sharing exactly, and for the
    // identical reason: the `Converges` witness must be built from the SAME
    // concrete values `piHalf` itself was constructed from, not a second,
    // independently-derived (merely value-equal) copy.
    let (raw, k_final, body) = pi_half_ingredients(d, p);
    declare_pi_half(d, p, raw, k_final, body)?;
    declare_pi_half_converges(d, p, raw, k_final, body)?;
    declare_pi(d, p)?;
    declare_pi_half_le_two(d, p)?;
    declare_pi_le_four(d, p)?;
    declare_two_le_pi(d, p)?;
    declare_three_le_pi(d, p)
}

// ---------------------------------------------------------------------------
// Local term builders. Each is reproduced verbatim from `trig.rs`'s own
// private copy -- that file's own precedent, taken rather than widening a
// sibling module's visibility.
// ---------------------------------------------------------------------------

fn cpow(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.pow, &[x, n])
}

/// `Rat.natDivSucc 1 1` — `1/2`.
fn half_rat(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let one_nat = d.num(1);
    div_succ(d, p, 1, one_nat)
}

/// `CReal.ofRat (Rat.natDivSucc 1 1)` — the constant `1/2`.
fn half(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let hr = half_rat(d, p);
    embed(d, p, hr)
}

/// `le zero half`.
fn half_nonneg_proof(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rp = p.rat;
    let zero_rat = rzero(d, rp);
    let one_nat = d.num(1);
    let half_ge_zero = d.lemma(rp.zero_le_nat_div_succ, &[one_nat, one_nat]);
    let hr = half_rat(d, p);
    d.lemma(p.of_rat_le, &[zero_rat, hr, half_ge_zero])
}

/// `Rat.le a b`, decided by `Rat.ble`'s own ι-reduction.
///
/// A **small-numbers** tool, deliberately: every call in this file compares
/// rationals whose largest formed `Nat` is under a thousand, because in this
/// kernel every numeral is unary and `Rat.normalize`'s `Nat.gcd` is the
/// dominant cost of any bigger comparison.
fn rat_le_by_ble(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let rp = p.rat;
    let ble_val = d.const_app(rp.ble, &[a, b]);
    let _ = ble_val; // documents the decided fact; the proof is `Eq.refl true`
    let true_c = d.bool_true();
    let refl_true = d.bool_refl(true_c);
    d.lemma(rp.le_of_ble_eq_true, &[a, b, refl_true])
}

/// `le zero two`.
fn two_nonneg_proof(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let rp = p.rat;
    let zero_rat = rzero(d, rp);
    let (two_r, _, _) = two_normalize(d, p);
    let rat_proof = rat_le_by_ble(d, p, zero_rat, two_r);
    d.lemma(p.of_rat_le, &[zero_rat, two_r, rat_proof])
}

/// `λ i, CReal.pow half i`.
fn pow_half_fn(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let h = half(d, p);
    let body = cpow(d, p, h, i);
    let nat = d.nat_ty();
    d.lam_fv(i_fv, nat, body)
}

/// `mul two (pow half n)` — the `CReal.pow`-based reading of
/// `CReal.expDominant n`.
fn exp_dominant_at(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let h = half(d, p);
    let t = two(d, p);
    let pw = cpow(d, p, h, n);
    cmul(d, p, t, pw)
}

/// `λ n, CReal.seq (f n) n` — the diagonal representative.
fn diagonal_seq(d: &mut IntDev<'_>, p: CRealPrelude, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let fn_term = d.apply(f, &[n]);
    let body = sample(d, p, fn_term, n);
    d.lam_fv(n_fv, nat, body)
}

/// `Equiv (neg zero) zero` — reproduced from `exponential.rs`'s own private
/// `neg_zero_equiv_local`.
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]);
    let step1 = d.lemma(p.equiv_symm, &[padded, nz, h1]);
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]);
    let h3 = d.lemma(p.add_neg, &[zero_c]);
    let t1 = d.lemma(p.equiv_trans, &[nz, padded, flipped, step1, h2]);
    d.lemma(p.equiv_trans, &[nz, flipped, zero_c, t1, h3])
}

// ---------------------------------------------------------------------------
// `CReal.piHalfCoef`, `CReal.piHalfTerm`, `CReal.piHalfSeriesPartial`.
// ---------------------------------------------------------------------------

/// `Rat.natDivSucc (Nat.succ k) (Nat.succ (Nat.succ (Nat.add k k)))` —
/// `(k+1)/(2k+3)`, the ratio `t (k+1) / t k`.
fn ratio_rat(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let sk = d.succ(k);
    let kk = NatOps::add(d, k, k);
    let j1 = d.succ(kk);
    let j2 = d.succ(j1);
    d.const_app(p.rat.nat_div_succ, &[sk, j2])
}

/// `CReal.piHalfCoef : Nat → Rat`, `t 0 = 1/1`, `t (k+1) = t k · (k+1)/(2k+3)`.
///
/// The base is `Rat.natDivSucc 1 0` (which IS `1`) rather than `Rat.one`, so
/// that [`RatPrelude::zero_le_nat_div_succ`](crate::RatPrelude::zero_le_nat_div_succ)
/// closes the nonnegativity base case directly and
/// [`CRealPrelude::rat_index_ratio_le_one`] closes the domination base case
/// directly — neither needs a `Rat.one` bridge.
fn declare_pi_half_coef(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let rat = rat_ty(d);
    let anon = d.anon_name();
    let one_level = d.level_one();

    let motive = d.kernel().lam(anon, nat, rat, BinderInfo::Default);
    let zero_nat = d.num(0);
    let minor_zero = div_succ(d, p, 1, zero_nat);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let c = ratio_rat(d, p, j);
        let body = rmul(d, ih, c);
        let inner = d.lam_fv(ih_fv, rat, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, rat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pi.pi_half_coef,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(PI_HEIGHT),
    })
}

/// `CReal.piHalfTerm : Nat → CReal := fun k => ofRat (piHalfCoef k)`.
fn declare_pi_half_term(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let coef = d.const_app(p.pi.pi_half_coef, &[k]);
    let body = embed(d, p, coef);
    let value = d.lam_fv(k_fv, nat, body);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pi.pi_half_term,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(PI_HEIGHT),
    })
}

/// `CReal.piHalfSeriesPartial : Nat → CReal := CReal.sumRange CReal.piHalfTerm`.
fn declare_pi_half_series_partial(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let term = d.kernel().const_(p.pi.pi_half_term, vec![]);
    let value = d.const_app(p.sum_range, &[term]);
    let ty = d.arrow(nat, carrier);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pi.pi_half_series_partial,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(PI_HEIGHT),
    })
}

// ---------------------------------------------------------------------------
// The ratio bound `(k+1)/(2k+3) ≤ 1/2`, and the two inductions over it.
// ---------------------------------------------------------------------------

/// `Rat.le (ratio k) (natDivSucc 1 1)`, i.e. `(k+1)/(2k+3) ≤ 1/2`.
///
/// **No cross-multiplication.**
/// [`RatPrelude::nat_div_succ_antitone`](crate::RatPrelude::nat_div_succ_antitone)
/// is stated only at numerator `1`, so this factors the numerator out first
/// ([`RatPrelude::nat_div_succ_mul`](crate::RatPrelude::nat_div_succ_mul) read
/// backwards: `natDivSucc a j = natDivSucc a 0 · natDivSucc 1 j`), compares
/// the two `natDivSucc 1 ·` factors by antitonicity at `Nat.le (2k+1)
/// (2k+2)`, scales back by the nonnegative `natDivSucc (k+1) 0`, and then
/// reads the right-hand side `natDivSucc (k+1) (2k+1)` as exactly `1/2`
/// through
/// [`RatPrelude::nat_div_succ_scale`](crate::RatPrelude::nat_div_succ_scale)
/// at `(c, m) := (k, 1)`, whose index `(k+1)·1 + k` becomes `Nat.succ
/// (Nat.add k k)` after one `Nat.mul_one` and one `Nat.succ_add`.
fn ratio_le_half(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let rp = p.rat;
    let nat_mul_one = d.prelude().mul_one;
    let nat_succ_add = d.prelude().succ_add;
    let nat_le_succ = d.prelude().le_succ;

    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let sk = d.succ(k);
    let kk = NatOps::add(d, k, k);
    let j1 = d.succ(kk);
    let j2 = d.succ(j1);

    // `natDivSucc 1 j2 ≤ natDivSucc 1 j1`, from `Nat.le j1 j2`.
    let h_nat = d.lemma(nat_le_succ, &[j1]);
    let h_anti = d.lemma(rp.nat_div_succ_antitone, &[j1, j2, h_nat]);

    // Scale by the nonnegative `A := natDivSucc (k+1) 0`.
    let a_unit = d.const_app(rp.nat_div_succ, &[sk, zero_nat]);
    let a_nonneg = d.lemma(rp.zero_le_nat_div_succ, &[sk, zero_nat]);
    let d2 = d.const_app(rp.nat_div_succ, &[one_nat, j2]);
    let d1 = d.const_app(rp.nat_div_succ, &[one_nat, j1]);
    let scaled = d.lemma(
        rp.mul_le_mul_of_nonneg_left,
        &[a_unit, d2, d1, a_nonneg, h_anti],
    );
    // scaled : Rat.le (A · d2) (A · d1)

    // Fuse each side into a single `natDivSucc`.
    let fused_numerator = NatOps::mul(d, sk, one_nat);
    let left_raw = rmul(d, a_unit, d2);
    let right_raw = rmul(d, a_unit, d1);
    let left_fused = d.const_app(rp.nat_div_succ, &[fused_numerator, j2]);
    let right_fused = d.const_app(rp.nat_div_succ, &[fused_numerator, j1]);

    let fuse_left = d.lemma(rp.nat_div_succ_mul, &[sk, one_nat, j2]);
    let step_left = rat_eq_rewrite(d, left_raw, left_fused, fuse_left, scaled, &|d, t| {
        rle(d, rp, t, right_raw)
    });
    let fuse_right = d.lemma(rp.nat_div_succ_mul, &[sk, one_nat, j1]);
    let step_right = rat_eq_rewrite(d, right_raw, right_fused, fuse_right, step_left, &|d, t| {
        rle(d, rp, left_fused, t)
    });

    // Trim `(k+1)·1` to `k+1` on BOTH sides at once.
    let trim = d.lemma(nat_mul_one, &[sk]);
    let trimmed = nat_rewrite_prop(d, fused_numerator, sk, trim, step_right, &|d, t| {
        let l = d.const_app(rp.nat_div_succ, &[t, j2]);
        let r = d.const_app(rp.nat_div_succ, &[t, j1]);
        rle(d, rp, l, r)
    });
    // trimmed : Rat.le (natDivSucc (k+1) j2) (natDivSucc (k+1) j1)

    // `natDivSucc (k+1) j1 = natDivSucc 1 1`, via `nat_div_succ_scale` at
    // `(c, m) = (k, 1)` whose index is `(k+1)·1 + k`.
    let half_r = half_rat(d, p);
    let scale_eq = d.lemma(rp.nat_div_succ_scale, &[k, one_nat]);
    let trim2 = d.lemma(nat_mul_one, &[sk]);
    let at_mid = nat_rewrite_prop(d, fused_numerator, sk, trim2, scale_eq, &|d, t| {
        let idx = NatOps::add(d, t, k);
        let lhs = d.const_app(rp.nat_div_succ, &[sk, idx]);
        let one_one = {
            let o = d.num(1);
            d.const_app(rp.nat_div_succ, &[o, o])
        };
        crate::rat_prelude::ops::req(d, lhs, one_one)
    });
    // at_mid : natDivSucc (k+1) (Nat.add (k+1) k) = natDivSucc 1 1
    let sk_plus_k = NatOps::add(d, sk, k);
    let succ_add_eq = d.lemma(nat_succ_add, &[k, k]);
    let right_is_half = nat_rewrite_prop(d, sk_plus_k, j1, succ_add_eq, at_mid, &|d, t| {
        let lhs = d.const_app(rp.nat_div_succ, &[sk, t]);
        let one_one = {
            let o = d.num(1);
            d.const_app(rp.nat_div_succ, &[o, o])
        };
        crate::rat_prelude::ops::req(d, lhs, one_one)
    });
    // right_is_half : natDivSucc (k+1) j1 = natDivSucc 1 1

    let trimmed_left = d.const_app(rp.nat_div_succ, &[sk, j2]);
    let trimmed_right = d.const_app(rp.nat_div_succ, &[sk, j1]);
    rat_eq_rewrite(d, trimmed_right, half_r, right_is_half, trimmed, &|d, t| {
        rle(d, rp, trimmed_left, t)
    })
}

/// `CReal.piHalfCoefNonneg : ∀ k, Rat.le Rat.zero (piHalfCoef k)`.
fn declare_pi_half_coef_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rp = p.rat;
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, m: ExprId| -> ExprId {
        let zero_r = rzero(d, rp);
        let coef = d.const_app(p.pi.pi_half_coef, &[m]);
        rle(d, rp, zero_r, coef)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let one_nat = d.num(1);
        let zero_nat = d.num(0);
        d.lemma(rp.zero_le_nat_div_succ, &[one_nat, zero_nat])
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let coef = d.const_app(p.pi.pi_half_coef, &[j]);
        let c = ratio_rat(d, p, j);
        let c_nonneg = {
            let sj = d.succ(j);
            let jj = NatOps::add(d, j, j);
            let a = d.succ(jj);
            let b = d.succ(a);
            d.lemma(rp.zero_le_nat_div_succ, &[sj, b])
        };
        d.lemma(rp.mul_nonneg, &[coef, c, ih, c_nonneg])
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let value_at_k = d.induct(&motive, &base, &step, k);
    let stmt_at_k = motive(d, k);
    let value = d.lam_fv(k_fv, nat, value_at_k);
    let ty = d.pi_fv(k_fv, nat, stmt_at_k);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pi.pi_half_coef_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.piHalfTermNonneg : ∀ k, le zero (piHalfTerm k)` — the `CReal`
/// reading of [`declare_pi_half_coef_nonneg`] through
/// [`CRealPrelude::of_rat_le`] (`CReal.zero` IS `ofRat Rat.zero` and
/// `piHalfTerm k` IS `ofRat (piHalfCoef k)`, both by delta).
fn declare_pi_half_term_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rp = p.rat;
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let zero_r = rzero(d, rp);
    let coef = d.const_app(p.pi.pi_half_coef, &[k]);
    let rat_proof = d.const_app(p.pi.pi_half_coef_nonneg, &[k]);
    let body = d.lemma(p.of_rat_le, &[zero_r, coef, rat_proof]);

    let zero_c = czero(d, p);
    let term = d.const_app(p.pi.pi_half_term, &[k]);
    let stmt = cle(d, p, zero_c, term);

    let value = d.lam_fv(k_fv, nat, body);
    let ty = d.pi_fv(k_fv, nat, stmt);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pi.pi_half_term_nonneg,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.piHalfTermLePowHalf : ∀ k, le (piHalfTerm k) (pow half k)`.
///
/// Induction on `k`. The base is `piHalfTerm 0 = ofRat (natDivSucc 1 0)` and
/// `pow half 0 = one` (ι-reduction), so
/// [`CRealPrelude::rat_index_ratio_le_one`] at index `0` closes it directly.
/// The step is `t (k+1) = t k · c k ≤ (pow half k) · (1/2) = pow half (succ
/// k)`: [`CRealPrelude::of_rat_mul`] moves the product out of `ofRat`, then
/// two applications of [`CRealPrelude::mul_le_mul_of_nonneg_left`] (one per
/// factor, with `mul_comm` between them) do the rest.
fn declare_pi_half_term_le_pow_half(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rp = p.rat;
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, m: ExprId| -> ExprId {
        let term = d.const_app(p.pi.pi_half_term, &[m]);
        let hp = half(d, p);
        let pw = cpow(d, p, hp, m);
        cle(d, p, term, pw)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        // `piHalfTerm 0` is `ofRat (natDivSucc 1 0)` and `pow half 0` is
        // `CReal.one = ofRat Rat.one` (both by delta/iota), and
        // `Rat.normalize 1 1` reduces to `Rat.one`'s own `Rat.mk` -- so
        // `le_refl` at `one` type-checks against the goal directly, the same
        // defeq `exponential.rs::declare_two_le_e` leans on for
        // `expSeriesPartial 2 = two`.
        //
        // NOT `rat_index_ratio_le_one` at index 0: that lemma is
        // `Rat.le (natDivSucc a a) (natDivSucc 1 0)`, so `a := 0` gives
        // `0 <= 1`, not `1 <= 1`. (`trig.rs::half_le_one_proof`'s doc comment
        // states it as `natDivSucc 1 j <= Rat.one`, which is wrong about the
        // numerator and happens not to matter at `a = 1`.)
        let one_cc = one_c(d, p);
        d.lemma(p.le_refl, &[one_cc])
    };
    let step = |d: &mut IntDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let coef = d.const_app(p.pi.pi_half_coef, &[j]);
        let c = ratio_rat(d, p, j);
        let prod_rat = rmul(d, coef, c);
        let lhs = embed(d, p, prod_rat);
        let term_j = embed(d, p, coef);
        let c_c = embed(d, p, c);
        let hp = half(d, p);
        let pw_j = cpow(d, p, hp, j);

        // split : Equiv (mul (ofRat coef) (ofRat c)) (ofRat (coef · c))
        let split = d.lemma(p.of_rat_mul, &[coef, c]);

        let ratio_bound = ratio_le_half(d, p, j);
        let half_r = half_rat(d, p);
        let c_le_half = d.lemma(p.of_rat_le, &[c, half_r, ratio_bound]);
        let coef_nonneg_rat = d.const_app(p.pi.pi_half_coef_nonneg, &[j]);
        let zero_r = rzero(d, rp);
        let term_nonneg = d.lemma(p.of_rat_le, &[zero_r, coef, coef_nonneg_rat]);

        // A : mul term_j (ofRat c) ≤ mul term_j half.
        let step_a = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[term_j, c_c, hp, term_nonneg, c_le_half],
        );
        // B : mul half term_j ≤ mul half (pow half j).
        let half_nn = half_nonneg_proof(d, p);
        let step_b = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[hp, term_j, pw_j, half_nn, ih],
        );

        let mul_tj_c = cmul(d, p, term_j, c_c);
        let mul_tj_h = cmul(d, p, term_j, hp);
        let mul_h_tj = cmul(d, p, hp, term_j);
        let comm1 = d.lemma(p.mul_comm, &[term_j, hp]);
        let refl_l = d.lemma(p.equiv_refl, &[mul_tj_c]);
        let step_a2 = d.lemma(
            p.le_congr,
            &[
                mul_tj_c, mul_tj_c, mul_tj_h, mul_h_tj, refl_l, comm1, step_a,
            ],
        );

        let mul_h_pw = cmul(d, p, hp, pw_j);
        let chained = d.lemma(p.le_trans, &[mul_tj_c, mul_h_tj, mul_h_pw, step_a2, step_b]);

        // Bridge both ends: lhs ← mul term_j (ofRat c); rhs → mul (pow half j) half.
        let mul_pw_h = cmul(d, p, pw_j, hp);
        let comm2 = d.lemma(p.mul_comm, &[hp, pw_j]);
        d.lemma(
            p.le_congr,
            &[mul_tj_c, lhs, mul_h_pw, mul_pw_h, split, comm2, chained],
        )
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let value_at_k = d.induct(&motive, &base, &step, k);
    let stmt_at_k = motive(d, k);
    let value = d.lam_fv(k_fv, nat, value_at_k);
    let ty = d.pi_fv(k_fv, nat, stmt_at_k);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pi.pi_half_term_le_pow_half,
        uparams: vec![],
        ty,
        value,
    })
}

/// `le (pow half k) (expDominant k)` — `P ≤ 2·P` for a nonnegative `P`,
/// written as `mul P one ≤ mul P two` and folded by `mul_one`/`mul_comm`.
fn pow_half_le_dominant(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let h = half(d, p);
    let pw = cpow(d, p, h, k);
    let one_cc = one_c(d, p);
    let two_c = two(d, p);

    let half_nn = half_nonneg_proof(d, p);
    let pw_nonneg = d.lemma(p.pow_nonneg, &[h, half_nn, k]);

    let one_r = d.kernel().const_(p.rat.one, vec![]);
    let (two_r, _, _) = two_normalize(d, p);
    let one_le_two_rat = rat_le_by_ble(d, p, one_r, two_r);
    let one_le_two = d.lemma(p.of_rat_le, &[one_r, two_r, one_le_two_rat]);

    let scaled = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[pw, one_cc, two_c, pw_nonneg, one_le_two],
    );
    // scaled : le (mul pw one) (mul pw two)

    let mul_pw_one = cmul(d, p, pw, one_cc);
    let mul_pw_two = cmul(d, p, pw, two_c);
    let mul_two_pw = cmul(d, p, two_c, pw);
    let fold_left = d.lemma(p.mul_one, &[pw]);
    let comm = d.lemma(p.mul_comm, &[pw, two_c]);
    d.lemma(
        p.le_congr,
        &[
            mul_pw_one, pw, mul_pw_two, mul_two_pw, fold_left, comm, scaled,
        ],
    )
}

/// `CReal.piHalfTermAbsLeDominant : ∀ k, le (abs (piHalfTerm k)) (expDominant k)`
/// — the domination hypothesis
/// [`CRealPrelude::sum_range_cauchy_dominated_ordered_normalized`] consumes,
/// stated against the SAME dominant series `CReal.e` uses so that its
/// concrete Cauchy witness is reusable unchanged.
fn declare_pi_half_term_abs_le_dominant(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let term = d.const_app(p.pi.pi_half_term, &[k]);
    let h = half(d, p);
    let pw = cpow(d, p, h, k);
    let dom = exp_dominant_at(d, p, k);
    let zero_c = czero(d, p);

    let le_pw = d.const_app(p.pi.pi_half_term_le_pow_half, &[k]);
    let pw_le_dom = pow_half_le_dominant(d, p, k);
    let le_dom = d.lemma(p.le_trans, &[term, pw, dom, le_pw, pw_le_dom]);

    // `abs_le` wants `le (neg term) dom`, from `0 ≤ term` and `0 ≤ dom`.
    let nonneg = d.const_app(p.pi.pi_half_term_nonneg, &[k]);
    let dom_nonneg = {
        let half_nn = half_nonneg_proof(d, p);
        let pw_nonneg = d.lemma(p.pow_nonneg, &[h, half_nn, k]);
        let two_c = two(d, p);
        let two_nn = two_nonneg_proof(d, p);
        d.lemma(p.mul_nonneg, &[two_c, pw, two_nn, pw_nonneg])
    };
    let neg_term = cneg(d, p, term);
    let neg_le = d.lemma(p.neg_le_neg, &[zero_c, term, nonneg]);
    // neg_le : le (neg term) (neg zero)
    let neg_zero = cneg(d, p, zero_c);
    let nz = neg_zero_equiv(d, p);
    let refl_neg_term = d.lemma(p.equiv_refl, &[neg_term]);
    let neg_term_le_zero = d.lemma(
        p.le_congr,
        &[
            neg_term,
            neg_term,
            neg_zero,
            zero_c,
            refl_neg_term,
            nz,
            neg_le,
        ],
    );
    let neg_term_le_dom = d.lemma(
        p.le_trans,
        &[neg_term, zero_c, dom, neg_term_le_zero, dom_nonneg],
    );

    let body = d.lemma(p.abs_le, &[term, dom, le_dom, neg_term_le_dom]);
    let abs_term = cabs(d, p, term);
    let stmt = cle(d, p, abs_term, dom);
    let value = d.lam_fv(k_fv, nat, body);
    let ty = d.pi_fv(k_fv, nat, stmt);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pi.pi_half_term_abs_le_dominant,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// `CReal.piHalf` (the `CReal.mk`), its `Converges` witness, and `CReal.pi`.
// ---------------------------------------------------------------------------

/// `(raw, k_final, body)` — mirrors `exponential.rs::e_ingredients` exactly,
/// with `CReal.piHalfTermAbsLeDominant` in place of
/// `exp_term_abs_le_dominant` and `piHalfSeriesPartial` in place of
/// `expSeriesPartial`. The dominant is UNCHANGED, so
/// `trig.rs::exp_dominant_cauchy_body_concrete`'s witness is reused verbatim
/// rather than re-derived.
fn pi_half_ingredients(d: &mut IntDev<'_>, p: CRealPrelude) -> (ExprId, ExprId, ExprId) {
    let (k_dom, hyp2) = exp_dominant_cauchy_body_concrete(d, p);

    let term_c = d.kernel().const_(p.pi.pi_half_term, vec![]);
    let dominant_c = d.kernel().const_(p.exp_dominant, vec![]);
    let partial_c = d.kernel().const_(p.pi.pi_half_series_partial, vec![]);
    let hyp1 = d.lemma(p.pi.pi_half_term_abs_le_dominant, &[]);

    let ordered_half = |d: &mut IntDev<'_>, a: ExprId, b: ExprId, hab: ExprId| -> ExprId {
        d.lemma(
            p.sum_range_cauchy_dominated_ordered_normalized,
            &[term_c, dominant_c, k_dom, a, b, hyp1, hyp2, hab],
        )
    };

    let mut k_final = k_dom;
    for _ in 0..8 {
        k_final = d.succ(k_final);
    }

    let body = promote_ordered_half_to_full(d, p, partial_c, k_final, &ordered_half);
    let raw = diagonal_seq(d, p, partial_c);
    (raw, k_final, body)
}

/// `CReal.piHalf := CReal.mk (speedup (diagonal piHalfSeriesPartial) K) (…)`.
fn declare_pi_half(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    raw: ExprId,
    k_final: ExprId,
    body: ExprId,
) -> Result<(), KernelError> {
    let partial_c = d.kernel().const_(p.pi.pi_half_series_partial, vec![]);
    let speedup_term = d.const_app(p.speedup, &[raw, k_final]);
    let regularity_proof = d.lemma(p.regular_of_scaled_cauchy, &[partial_c, k_final, body]);
    let constructor = d.kernel().const_(p.mk, vec![]);
    let value = d.apply(constructor, &[speedup_term, regularity_proof]);
    let ty = creal_ty(d, p);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pi.pi_half,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 40),
    })
}

/// `CReal.piHalfConverges : Converges piHalfSeriesPartial piHalf` — built
/// GENERICALLY over a BOUND `(k, h)` and applied at the concrete pair only at
/// the very end, for the reason `exponential.rs::declare_e_converges` records
/// at length: a partially-concrete `speedup(raw, k_final)` drives the
/// kernel's lazy-delta `is_def_eq` into a lock-step unfold that overflows a
/// 1 GiB release stack.
fn declare_pi_half_converges(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    raw: ExprId,
    k_final: ExprId,
    body_concrete: ExprId,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let partial_c = d.kernel().const_(p.pi.pi_half_series_partial, vec![]);
    let pi_half_c = d.kernel().const_(p.pi.pi_half, vec![]);

    let generic = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hp_ty = sum_range_cauchy_body(d, p, partial_c, k);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);

        let kregular_proof = kregular_of_cauchy_proof(d, p, raw, k, hp);
        let speedup_term = d.const_app(p.speedup, &[raw, k]);
        let sc = d.const_app(p.speedup_close, &[raw, k, kregular_proof]);

        let regularity_proof = d.lemma(p.regular_of_scaled_cauchy, &[partial_c, k, hp]);
        let constructor = d.kernel().const_(p.mk, vec![]);
        let l_val = d.apply(constructor, &[speedup_term, regularity_proof]);

        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let raw_n = d.apply(raw, &[n]);
        let speedup_n = d.apply(speedup_term, &[n]);
        let diff_n = rsub(d, rat, raw_n, speedup_n);

        let succ_k = d.succ(k);
        let one_nat = d.num(1);
        let bound_left_n = div_succ_at(d, p, succ_k, n);
        let bound_right_n = div_succ_at(d, p, one_nat, n);
        let sc_n_bound = radd(d, bound_left_n, bound_right_n);

        let sc_n = d.apply(sc, &[n]);

        let fuse = d.lemma(rat.nat_div_succ_add, &[succ_k, one_nat, n]);
        let k2 = NatOps::add(d, succ_k, one_nat);
        let target_bound_n = div_succ_at(d, p, k2, n);
        let step = rat_eq_rewrite(d, sc_n_bound, target_bound_n, fuse, sc_n, &|d, t| {
            within(d, p, diff_n, t)
        });

        let over_n = d.lam_fv(n_fv, nat, step);
        let converges_pred = converges_predicate(d, p, partial_c, l_val);
        let converges_proof = exists_intro(d, p, nat, converges_pred, k2, over_n);

        let with_hp = d.lam_fv(hp_fv, hp_ty, converges_proof);
        d.lam_fv(k_fv, nat, with_hp)
    };

    let value = d.apply(generic, &[k_final, body_concrete]);
    let ty = converges_applied(d, p, partial_c, pi_half_c);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pi.pi_half_converges,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.pi := CReal.mul two piHalf`.
///
/// A product with the rational constant `2`, not a second `CReal.mk`: every
/// bound on `piHalf` then transfers by one
/// [`CRealPrelude::mul_le_mul_of_nonneg_left`], and no second regularity
/// proof has to be built.
fn declare_pi(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let two_c = two(d, p);
    let pi_half_c = d.kernel().const_(p.pi.pi_half, vec![]);
    let value = cmul(d, p, two_c, pi_half_c);
    let ty = creal_ty(d, p);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pi.pi,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 41),
    })
}

// ---------------------------------------------------------------------------
// The bounds.
// ---------------------------------------------------------------------------

/// `CReal.piHalfLeTwo : le piHalf two`.
///
/// Every partial sum is `≤ two`: termwise `piHalfTerm k ≤ pow half k`
/// ([`PiNames::pi_half_term_le_pow_half`]) through
/// [`CRealPrelude::sum_range_le`], then
/// [`CRealPrelude::sum_pow_half_closed_form`] reads the geometric partial sum
/// as `mul two (one − (1/2)ⁿ) ≤ mul two one ~ two`. Holds at every `n`
/// including `0`, so [`CRealPrelude::converges_upper_bound`] applies with no
/// shift.
fn declare_pi_half_le_two(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let term_c = d.kernel().const_(p.pi.pi_half_term, vec![]);
    let partial_c = d.kernel().const_(p.pi.pi_half_series_partial, vec![]);
    let le_pow_const = d.kernel().const_(p.pi.pi_half_term_le_pow_half, vec![]);
    let pi_half_c = d.kernel().const_(p.pi.pi_half, vec![]);
    let converges = d.kernel().const_(p.pi.pi_half_converges, vec![]);

    let per_n = |d: &mut IntDev<'_>, n: ExprId| -> ExprId {
        let zero_c = czero(d, p);
        let one_cc = one_c(d, p);
        let two_c = two(d, p);
        let h = half(d, p);
        let pow_fn = pow_half_fn(d, p);

        let ptwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt_fv = d.fresh_fvar();
            let lt_ty = d.lt(i, n);
            let body = d.apply(le_pow_const, &[i]);
            let with_lt = d.lam_fv(lt_fv, lt_ty, body);
            d.lam_fv(i_fv, nat, with_lt)
        };
        let step_a = d.const_app(p.sum_range_le, &[term_c, pow_fn, n, ptwise]);

        let sum_pow = d.const_app(p.sum_range, &[pow_fn, n]);
        let n_pow = cpow(d, p, h, n);
        let neg_pow = cneg(d, p, n_pow);
        let y_n = cadd(d, p, one_cc, neg_pow);
        let mul_two_y = cmul(d, p, two_c, y_n);
        let closed = d.const_app(p.sum_pow_half_closed_form, &[n]);
        // closed : Equiv sum_pow mul_two_y

        let half_nn = half_nonneg_proof(d, p);
        let pow_nonneg_n = d.lemma(p.pow_nonneg, &[h, half_nn, n]);
        let neg_step = d.lemma(p.neg_le_neg, &[zero_c, n_pow, pow_nonneg_n]);
        let neg_zero_c = cneg(d, p, zero_c);
        let nz = neg_zero_equiv(d, p);
        let refl_neg_pow = d.lemma(p.equiv_refl, &[neg_pow]);
        let neg_pow_le_zero = d.lemma(
            p.le_congr,
            &[
                neg_pow,
                neg_pow,
                neg_zero_c,
                zero_c,
                refl_neg_pow,
                nz,
                neg_step,
            ],
        );
        let refl_one = d.lemma(p.le_refl, &[one_cc]);
        let grown = d.lemma(
            p.add_le_add,
            &[one_cc, one_cc, neg_pow, zero_c, refl_one, neg_pow_le_zero],
        );
        let padded_one = cadd(d, p, one_cc, zero_c);
        let add_zero_eq = d.lemma(p.add_zero, &[one_cc]);
        let refl_y = d.lemma(p.equiv_refl, &[y_n]);
        let y_le_one = d.lemma(
            p.le_congr,
            &[y_n, y_n, padded_one, one_cc, refl_y, add_zero_eq, grown],
        );

        let two_nn = two_nonneg_proof(d, p);
        let mul_le = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[two_c, y_n, one_cc, two_nn, y_le_one],
        );
        let mul_two_one = cmul(d, p, two_c, one_cc);
        let fold = d.lemma(p.mul_one, &[two_c]);
        let refl_mty = d.lemma(p.equiv_refl, &[mul_two_y]);
        let two_y_le_two = d.lemma(
            p.le_congr,
            &[
                mul_two_y,
                mul_two_y,
                mul_two_one,
                two_c,
                refl_mty,
                fold,
                mul_le,
            ],
        );

        let closed_symm = d.lemma(p.equiv_symm, &[sum_pow, mul_two_y, closed]);
        let refl_two = d.lemma(p.equiv_refl, &[two_c]);
        let sum_pow_le_two = d.lemma(
            p.le_congr,
            &[
                mul_two_y,
                sum_pow,
                two_c,
                two_c,
                closed_symm,
                refl_two,
                two_y_le_two,
            ],
        );

        let sum_term = d.const_app(p.sum_range, &[term_c, n]);
        d.lemma(
            p.le_trans,
            &[sum_term, sum_pow, two_c, step_a, sum_pow_le_two],
        )
    };

    let hyp = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = per_n(d, n);
        d.lam_fv(n_fv, nat, body)
    };

    let two_c = two(d, p);
    let value = d.const_app(
        p.converges_upper_bound,
        &[partial_c, pi_half_c, two_c, hyp, converges],
    );
    let ty = cle(d, p, pi_half_c, two_c);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pi.pi_half_le_two,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.piLeFour : le pi (mul two two)` — one
/// [`CRealPrelude::mul_le_mul_of_nonneg_left`] off
/// [`declare_pi_half_le_two`], since `pi` IS `mul two piHalf`.
fn declare_pi_le_four(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let two_c = two(d, p);
    let two_nn = two_nonneg_proof(d, p);
    let pi_half_c = d.kernel().const_(p.pi.pi_half, vec![]);
    let bound = d.kernel().const_(p.pi.pi_half_le_two, vec![]);
    let value = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[two_c, pi_half_c, two_c, two_nn, bound],
    );
    let pi_c = d.kernel().const_(p.pi.pi, vec![]);
    let four = cmul(d, p, two_c, two_c);
    let ty = cle(d, p, pi_c, four);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pi.pi_le_four,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.natDivSucc num idx`, both literals.
fn ndiv(d: &mut IntDev<'_>, p: CRealPrelude, num: u32, idx: u32) -> ExprId {
    let n = d.num(num);
    let j = d.num(idx);
    d.const_app(p.rat.nat_div_succ, &[n, j])
}

/// `∀ n, le b (piHalfSeriesPartial (Nat.add n s))` from `base : le b
/// (sumRange piHalfTerm s)`, by [`CRealPrelude::sum_range_mono_outer`] at the
/// nonnegative `piHalfTerm` — the shape
/// [`CRealPrelude::converges_lower_bound_shift`] consumes. Reproduced in
/// shape from `exponential.rs::declare_two_le_e`'s own `h1_shift`.
fn shifted_lower_bound(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    bound: ExprId,
    shift: ExprId,
    base: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let term_c = d.kernel().const_(p.pi.pi_half_term, vec![]);
    let nonneg_c = d.kernel().const_(p.pi.pi_half_term_nonneg, vec![]);
    let zero_nat = d.num(0);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let shifted = NatOps::add(d, n, shift);
    let zero_le_n = {
        let np = d.prelude();
        d.lemma(np.zero_le, &[n])
    };
    let shift_le_shifted = {
        let np = d.prelude();
        d.lemma(np.add_le_add_right, &[shift, zero_nat, n, zero_le_n])
    };
    let mono = d.const_app(
        p.sum_range_mono_outer,
        &[term_c, nonneg_c, shift, shifted, shift_le_shifted],
    );
    let sum_at_shift = d.const_app(p.sum_range, &[term_c, shift]);
    let sum_shifted = d.const_app(p.sum_range, &[term_c, shifted]);
    let step = d.lemma(p.le_trans, &[bound, sum_at_shift, sum_shifted, base, mono]);
    d.lam_fv(n_fv, nat, step)
}

/// `le (mul two b) (mul two piHalf)` from `lower : le b piHalf` — one
/// [`CRealPrelude::mul_le_mul_of_nonneg_left`], and `mul two piHalf` IS `pi`.
fn scale_lower_bound_to_pi(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    bound: ExprId,
    lower: ExprId,
) -> ExprId {
    let two_c = two(d, p);
    let two_nn = two_nonneg_proof(d, p);
    let pi_half_c = d.kernel().const_(p.pi.pi_half, vec![]);
    d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[two_c, bound, pi_half_c, two_nn, lower],
    )
}

/// `CReal.twoLePi : le two pi`.
///
/// The cheapest honest lower bound, and the exact analogue of
/// `exponential.rs::declare_two_le_e`: `piHalfSeriesPartial 1` is
/// `add zero (piHalfTerm 0)`, which δι-reduces to `CReal.one`'s own `Rat.mk`
/// (`Rat.add Rat.zero (natDivSucc 1 0)` normalises to `1/1`), so `le_refl one`
/// type-checks against `le one (sumRange piHalfTerm 1)` with no rewrite. Every
/// partial sum from there on is at least as large
/// ([`CRealPrelude::sum_range_mono_outer`], all terms nonnegative), so
/// [`CRealPrelude::converges_lower_bound_shift`] at shift `1` gives
/// `1 ≤ piHalf`, and scaling by `two` gives `2 ≤ pi`.
fn declare_two_le_pi(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let partial_c = d.kernel().const_(p.pi.pi_half_series_partial, vec![]);
    let pi_half_c = d.kernel().const_(p.pi.pi_half, vec![]);
    let converges = d.kernel().const_(p.pi.pi_half_converges, vec![]);

    let one_nat = d.num(1);
    let one_cc = one_c(d, p);
    let base = d.lemma(p.le_refl, &[one_cc]);
    let shift_hyp = shifted_lower_bound(d, p, one_cc, one_nat, base);

    let lower = d.const_app(
        p.converges_lower_bound_shift,
        &[one_nat, one_cc, partial_c, pi_half_c, shift_hyp, converges],
    );
    // lower : le one piHalf

    let scaled = scale_lower_bound_to_pi(d, p, one_cc, lower);
    // scaled : le (mul two one) (mul two piHalf)

    let two_c = two(d, p);
    let mul_two_one = cmul(d, p, two_c, one_cc);
    let fold = d.lemma(p.mul_one, &[two_c]); // Equiv (mul two one) two
    let pi_c = d.kernel().const_(p.pi.pi, vec![]);
    let refl_pi = d.lemma(p.equiv_refl, &[pi_c]);
    let mul_two_pi_half = cmul(d, p, two_c, pi_half_c);
    let value = d.lemma(
        p.le_congr,
        &[
            mul_two_one,
            two_c,
            mul_two_pi_half,
            pi_c,
            fold,
            refl_pi,
            scaled,
        ],
    );
    let ty = cle(d, p, two_c, pi_c);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pi.two_le_pi,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.threeLePi : le (ofRat (natDivSucc 3 0)) pi`.
///
/// **Four terms, and every rational in the argument is chosen to keep the
/// formed `Nat`s small.** The exact partial sum is
/// `S 4 = 1 + 1/3 + 2/15 + 2/35 = 32/21`, and asking the kernel to see that
/// directly is what the first attempt did — it ran **past 600 s and 5.9 GB
/// RSS** before being killed, while everything else in this file built the
/// whole `creal` prelude in 118 s. The cost is `Rat.normalize 800 525`: this
/// kernel's numerals are unary, so `Nat.gcd 800 525` runs Euclid by repeated
/// unary subtraction and the two `Nat.div`s that follow are 32 and 21
/// iterations over 800- and 525-deep `Nat.succ` towers.
///
/// So the terms are weakened FIRST, to bounds whose running sums have short
/// divisions: `t0 ≥ 1`, `t1 ≥ 1/3`, `t2 ≥ 1/9` (against the exact `2/15`) and
/// `t3 ≥ 1/18` (against `2/35`), whose partial sums are `1`, `4/3`, `13/9`
/// and exactly `3/2`. Both weakenings are tight — `1·35 ≤ 18·2` is `35 ≤ 36`
/// — which is what keeps the denominators small enough to matter. The largest
/// `Nat` formed is **243**, normalised by `gcd 243 162 = 81` in two remainder
/// steps and divisions of 3 and 2 iterations, against 53 division iterations
/// over 800-deep towers for the exact route.
///
/// Same lesson as the `587 s → 113 s` case in `CLAUDE.md`: choose the
/// intermediate bound that lands on what the next step needs, not the exact
/// quotient.
fn declare_three_le_pi(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let partial_c = d.kernel().const_(p.pi.pi_half_series_partial, vec![]);
    let pi_half_c = d.kernel().const_(p.pi.pi_half, vec![]);
    let converges = d.kernel().const_(p.pi.pi_half_converges, vec![]);
    let term_c = d.kernel().const_(p.pi.pi_half_term, vec![]);

    // Per-term lower bounds, and the running sums they add up to.
    let b1 = ndiv(d, p, 1, 2); //  1/3
    let b2 = ndiv(d, p, 1, 8); //  1/9   <=  2/15   (1*15 = 15 <= 9*2 = 18)
    let b3 = ndiv(d, p, 1, 17); // 1/18  <=  2/35   (1*35 = 35 <= 18*2 = 36)
    let c1 = ndiv(d, p, 1, 0); //  1
    let c2 = ndiv(d, p, 4, 2); //  4/3
    let c3 = ndiv(d, p, 13, 8); // 13/9
    let c4 = ndiv(d, p, 3, 1); //  3/2   -- exactly 13/9 + 1/18

    // `le (ofRat b_i) (piHalfTerm i)`, each decided by `Rat.ble` on operands
    // under 50 (`1·3 ≤ 3·1`, `1·15 ≤ 8·2`, `1·35 ≤ 24·2`).
    let term_bound = |d: &mut IntDev<'_>, i: u32, b: ExprId| -> ExprId {
        let idx = d.num(i);
        let coef = d.const_app(p.pi.pi_half_coef, &[idx]);
        let rat_proof = rat_le_by_ble(d, p, b, coef);
        d.lemma(p.of_rat_le, &[b, coef, rat_proof])
    };
    let h1 = term_bound(d, 1, b1);
    let h2 = term_bound(d, 2, b2);
    let h3 = term_bound(d, 3, b3);

    // `g_k : le (ofRat c_k) (sumRange piHalfTerm k)`.
    //
    // `sumRange f (succ k)` IS `add (sumRange f k) (f k)` by iota, and
    // `add (ofRat a) (ofRat b)` is `Equiv` to `ofRat (a + b)`
    // ([`CRealPrelude::of_rat_add`]) whose value is defeq to the next `c`.
    let step = |d: &mut IntDev<'_>,
                c_prev: ExprId,
                b_here: ExprId,
                c_next: ExprId,
                k_prev: u32,
                g_prev: ExprId,
                h_here: ExprId|
     -> ExprId {
        let prev_c = embed(d, p, c_prev);
        let here_c = embed(d, p, b_here);
        let next_c = embed(d, p, c_next);
        let k_nat = d.num(k_prev);
        let idx = d.num(k_prev);
        let sum_prev = d.const_app(p.sum_range, &[term_c, k_nat]);
        let term_here = d.const_app(p.pi.pi_half_term, &[idx]);

        let grown = d.lemma(
            p.add_le_add,
            &[prev_c, sum_prev, here_c, term_here, g_prev, h_here],
        );
        // grown : le (add prev_c here_c) (add sum_prev term_here), and the
        // right-hand side IS `sumRange piHalfTerm (k_prev + 1)`.

        let lhs = cadd(d, p, prev_c, here_c);
        let rhs = cadd(d, p, sum_prev, term_here);
        // `of_rat_add c_prev b_here : Equiv lhs (ofRat (c_prev + b_here))`,
        // ascribed at `Equiv lhs next_c` -- the two right-hand sides are the
        // same `Rat.mk` after normalisation.
        let fold = d.lemma(p.of_rat_add, &[c_prev, b_here]);
        let refl_rhs = d.lemma(p.equiv_refl, &[rhs]);
        d.lemma(p.le_congr, &[lhs, next_c, rhs, rhs, fold, refl_rhs, grown])
    };

    // `sumRange f 1` IS `add zero (f 0)`, and `Rat.add Rat.zero (natDivSucc 1
    // 0)` normalises to `1/1` -- the same `Rat.mk` as `ofRat c1`, so `le_refl`
    // type-checks directly.
    let c1_c = embed(d, p, c1);
    let g1 = d.lemma(p.le_refl, &[c1_c]);
    let g2 = step(d, c1, b1, c2, 1, g1, h1);
    let g3 = step(d, c2, b2, c3, 2, g2, h2);
    let g4 = step(d, c3, b3, c4, 3, g3, h3);

    let four_nat = d.num(4);
    let c4_c = embed(d, p, c4);
    let shift_hyp = shifted_lower_bound(d, p, c4_c, four_nat, g4);
    let lower = d.const_app(
        p.converges_lower_bound_shift,
        &[four_nat, c4_c, partial_c, pi_half_c, shift_hyp, converges],
    );
    // lower : le (ofRat 3/2) piHalf

    let scaled = scale_lower_bound_to_pi(d, p, c4_c, lower);
    // scaled : le (mul two (ofRat 3/2)) (mul two piHalf)

    // `mul two (ofRat 3/2) ~ ofRat (2 · 3/2)`, whose value normalises to
    // `Rat.mk 3 1` -- the same value `natDivSucc 3 0` reduces to, so
    // `of_rat_mul` ascribes directly at `Equiv (mul two (ofRat 3/2))
    // (ofRat (natDivSucc 3 0))`.
    let two_c = two(d, p);
    let (two_r, _, _) = two_normalize(d, p);
    let three_r = ndiv(d, p, 3, 0);
    let three_c = embed(d, p, three_r);
    let split = d.lemma(p.of_rat_mul, &[two_r, c4]);
    let mul_two_c4 = cmul(d, p, two_c, c4_c);
    let pi_c = d.kernel().const_(p.pi.pi, vec![]);
    let refl_pi = d.lemma(p.equiv_refl, &[pi_c]);
    let mul_two_pi_half = cmul(d, p, two_c, pi_half_c);
    let value = d.lemma(
        p.le_congr,
        &[
            mul_two_c4,
            three_c,
            mul_two_pi_half,
            pi_c,
            split,
            refl_pi,
            scaled,
        ],
    );
    let ty = cle(d, p, three_c, pi_c);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.pi.three_le_pi,
        uparams: vec![],
        ty,
        value,
    })
}

// ---------------------------------------------------------------------------
// Evaluation tests.
//
// `CReal.piHalfCoef` is a `Definition`, and `Kernel::add_declaration` cannot
// tell anyone it is WRONG: a function that computes the wrong rational still
// has type `Nat → Rat`. Every guard this development leans on — the prelude
// build, `axiom_footprint`,
// `every_creal_declaration_is_checked_and_axiom_free` — is blind to that. The
// mathematics of this file lives entirely in that one recursion, so it is
// pinned here by reduction at concrete indices against independently computed
// values, with negative controls chosen to separate the specific typos that
// would otherwise type-check.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::super::creal_tests::built;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{normalize, one_le_succ};

    /// `Rat.normalize (ofNat num) den _`, built independently of anything in
    /// `pi.rs`.
    fn rat_literal(d: &mut IntDev<'_>, num_val: u32, den_val: u32) -> crate::expr::ExprId {
        assert!(den_val >= 1, "denominator must be positive");
        let k = d.num(den_val - 1);
        let denominator = d.succ(k);
        let positive = one_le_succ(d, k);
        let num_nat = d.num(num_val);
        let numerator = d.of_nat(num_nat);
        normalize(d, numerator, denominator, positive)
    }

    /// `piHalfCoef k` reduces to `2ᵏ(k!)²/(2k+1)!` at `k = 0..3` — `1`, `1/3`,
    /// `2/15`, `2/35`, the values `scripts/check-pi-series-numeric.py` pins
    /// against the closed form and against `π/2`.
    ///
    /// Two negative controls, each aimed at a mutation that would type-check:
    ///
    /// - `piHalfCoef 2` must NOT be `1/15`. That is what a numerator typo in
    ///   the ratio (`natDivSucc k` for `natDivSucc (succ k)`) produces, and it
    ///   would still be a well-typed `Nat → Rat`.
    /// - `piHalfCoef 3` must NOT equal `piHalfCoef 2`. That separates a
    ///   recursion which advances from one whose step silently returns its
    ///   own input — the shape a wrong `Nat.rec` minor premise gives.
    #[test]
    fn pi_half_coef_computes_its_first_four_values() {
        let (mut kernel, p) = built();
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        for (k_val, num_val, den_val) in [(0u32, 1u32, 1u32), (1, 1, 3), (2, 2, 15), (3, 2, 35)] {
            let k = d.num(k_val);
            let coef = d.const_app(p.pi.pi_half_coef, &[k]);
            let expected = rat_literal(&mut d, num_val, den_val);
            assert!(
                d.kernel().def_eq(coef, expected),
                "piHalfCoef {k_val} should reduce to {num_val}/{den_val}"
            );
        }

        let two = d.num(2);
        let coef2 = d.const_app(p.pi.pi_half_coef, &[two]);
        let one_fifteenth = rat_literal(&mut d, 1, 15);
        assert!(
            !d.kernel().def_eq(coef2, one_fifteenth),
            "piHalfCoef 2 must NOT be 1/15 -- that is the value a numerator \
             typo in the ratio gives, and it would type-check; if this \
             passes, the positive checks above are not discriminating"
        );

        let three = d.num(3);
        let coef3 = d.const_app(p.pi.pi_half_coef, &[three]);
        assert!(
            !d.kernel().def_eq(coef3, coef2),
            "piHalfCoef 3 must differ from piHalfCoef 2 -- a step that \
             returned its own input would be well-typed and would make every \
             bound in this file vacuous"
        );
    }

    /// The two WEAKENED bounds `declare_three_le_pi` uses are tight, and the
    /// next tighter rational fails.
    ///
    /// `1/9 ≤ 2/15` is `15 ≤ 18` and `1/18 ≤ 2/35` is `35 ≤ 36` — one step
    /// from false in each case. That tightness is the whole reason the
    /// theorem reaches `3/2` at four terms, so an off-by-one in either
    /// denominator would either break the proof (harmless) or, if it went the
    /// other way, leave a bound too weak to be worth stating. The negative
    /// halves check the FIRST of those: `1/8 ≤ 2/15` still holds, so the
    /// controls here are the ones one step past what is used.
    #[test]
    fn the_weakened_term_bounds_are_one_step_from_false() {
        let (mut kernel, p) = built();
        let mut d = IntDev::new(&mut kernel, p.rat.int);
        let rat = p.rat;

        let ble = |d: &mut IntDev<'_>, a: crate::expr::ExprId, b: crate::expr::ExprId| -> bool {
            let value = d.const_app(rat.ble, &[a, b]);
            let true_c = d.bool_true();
            d.kernel().def_eq(value, true_c)
        };

        let two_nat = d.num(2);
        let three_nat = d.num(3);
        let coef2 = d.const_app(p.pi.pi_half_coef, &[two_nat]);
        let coef3 = d.const_app(p.pi.pi_half_coef, &[three_nat]);

        let ninth = rat_literal(&mut d, 1, 9);
        assert!(ble(&mut d, ninth, coef2), "1/9 <= 2/15 (15 <= 18)");
        let eighth_of_a_ninth = rat_literal(&mut d, 1, 8);
        assert!(
            ble(&mut d, eighth_of_a_ninth, coef2),
            "1/8 <= 2/15 (15 <= 16) -- the looser bound also holds, so the \
             choice of 1/9 is about arithmetic size, not about truth"
        );
        let seventh = rat_literal(&mut d, 1, 7);
        assert!(
            !ble(&mut d, seventh, coef2),
            "1/7 <= 2/15 must be FALSE (15 <= 14) -- if it passes, this \
             comparison is not deciding anything"
        );

        let eighteenth = rat_literal(&mut d, 1, 18);
        assert!(ble(&mut d, eighteenth, coef3), "1/18 <= 2/35 (35 <= 36)");
        let seventeenth = rat_literal(&mut d, 1, 17);
        assert!(
            !ble(&mut d, seventeenth, coef3),
            "1/17 <= 2/35 must be FALSE (35 <= 34) -- one step from the bound \
             the proof uses, which is what makes 3/2 reachable at four terms"
        );
    }
}

/// The kernel names `creal/pi.rs` declares.
///
/// One of ADR-1512's per-module registries behind the [`CRealPrelude`]
/// facade: the field, its documentation and its interning all live
/// beside the `declare_*` that uses them, so a declaration added here
/// does not touch `creal.rs` at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PiNames {
    /// `CReal.piHalfCoef : Nat -> Rat` -- `t 0 = 1/1`,
    /// `t (k+1) = t k * (k+1)/(2k+3)`. The terms of Euler's transform of
    /// Leibniz, `pi/2 = sum_k 2^k (k!)^2/(2k+1)!`, defined by the RECURSION
    /// rather than the closed form so the ratio is definitional.
    pub pi_half_coef: NameId,
    /// `CReal.piHalfTerm : Nat -> CReal := fun k => ofRat (piHalfCoef k)`.
    pub pi_half_term: NameId,
    /// `CReal.piHalfSeriesPartial : Nat -> CReal := sumRange piHalfTerm`.
    pub pi_half_series_partial: NameId,
    /// `CReal.piHalfCoefNonneg : forall k, Rat.le Rat.zero (piHalfCoef k)`.
    pub pi_half_coef_nonneg: NameId,
    /// `CReal.piHalfTermNonneg : forall k, le zero (piHalfTerm k)`.
    pub pi_half_term_nonneg: NameId,
    /// `CReal.piHalfTermLePowHalf : forall k, le (piHalfTerm k) (pow half k)`
    /// -- the geometric domination, by induction on the definitional ratio
    /// `(k+1)/(2k+3) <= 1/2`.
    pub pi_half_term_le_pow_half: NameId,
    /// `CReal.piHalfTermAbsLeDominant : forall k,
    /// le (abs (piHalfTerm k)) (expDominant k)` -- stated against `CReal.e`'s
    /// OWN dominant series so that its concrete Cauchy witness is reusable
    /// unchanged.
    pub pi_half_term_abs_le_dominant: NameId,
    /// `CReal.piHalf : CReal` -- `pi/2`, by `CReal.mk` on an explicit regular
    /// sequence. No root, no IVT: `creal/ivt.rs` refutes the exact-root
    /// construction, and that refutation is about one DEFINITION of pi, not
    /// about pi.
    pub pi_half: NameId,
    /// `CReal.piHalfConverges : Converges piHalfSeriesPartial piHalf`.
    pub pi_half_converges: NameId,
    /// `CReal.pi : CReal := mul two piHalf`.
    pub pi: NameId,
    /// `CReal.piHalfLeTwo : le piHalf two`.
    pub pi_half_le_two: NameId,
    /// `CReal.piLeFour : le pi (mul two two)`.
    pub pi_le_four: NameId,
    /// `CReal.twoLePi : le two pi`.
    pub two_le_pi: NameId,
    /// `CReal.threeLePi : le (ofRat (Rat.natDivSucc 3 0)) pi`.
    pub three_le_pi: NameId,
}

impl PiNames {
    /// Interns this module's names under the `CReal` root.
    ///
    /// Split out of `creal.rs`'s `intern_names` by ADR-1512: the kernel
    /// spelling of each name sits in the file that declares it.
    pub(super) fn intern(kernel: &mut Kernel, creal: NameId) -> Self {
        Self {
            pi_half_coef: kernel.name_str(creal, "piHalfCoef"),
            pi_half_term: kernel.name_str(creal, "piHalfTerm"),
            pi_half_series_partial: kernel.name_str(creal, "piHalfSeriesPartial"),
            pi_half_coef_nonneg: kernel.name_str(creal, "piHalfCoefNonneg"),
            pi_half_term_nonneg: kernel.name_str(creal, "piHalfTermNonneg"),
            pi_half_term_le_pow_half: kernel.name_str(creal, "piHalfTermLePowHalf"),
            pi_half_term_abs_le_dominant: kernel.name_str(creal, "piHalfTermAbsLeDominant"),
            pi_half: kernel.name_str(creal, "piHalf"),
            pi_half_converges: kernel.name_str(creal, "piHalfConverges"),
            pi: kernel.name_str(creal, "pi"),
            pi_half_le_two: kernel.name_str(creal, "piHalfLeTwo"),
            pi_le_four: kernel.name_str(creal, "piLeFour"),
            two_le_pi: kernel.name_str(creal, "twoLePi"),
            three_le_pi: kernel.name_str(creal, "threeLePi"),
        }
    }
}
