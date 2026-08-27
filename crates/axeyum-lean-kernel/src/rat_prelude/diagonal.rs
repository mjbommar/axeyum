//! The `ℚ`-valued diagonal reindexing and rectangle=triangle+corner
//! decomposition a finite Cauchy product needs — the direct port of
//! [`crate::nat_prelude::diagonal`] / [`crate::nat_prelude::rectangle`] to a
//! `Nat → Nat → Rat` summand, replacing `Nat`'s `sumRange`, `add`, `zero`
//! everywhere the SUM'S VALUE is at stake, while every INDEX-level fact
//! (`Nat.le`, `Nat.lt`, `Nat.sub`, `Nat.succ`, and the round-trip lemmas
//! `succ_sub_of_le`/`sub_self`/`sub_add_cancel`/`le_succ`/`le_trans`/`le_refl`)
//! stays exactly `Nat`'s own, reached through [`crate::nat_prelude::NatPrelude`]
//! via `d.prelude()` — the same split [`super::sum::declare_sum_range_congr_lt`]
//! already uses (`np` for index facts, the local prelude for value facts).
//!
//! # Does this port mechanically?
//!
//! Yes, with exactly one recurring translation rule: every place `Nat`'s
//! script writes `d.sum_range`/`d.add`/`d.zero`/`d.refl`/`d.congr`/`d.chain`/
//! `d.trans`/`d.symm`/`d.eq` to talk about the SUM'S VALUE becomes
//! `rsum_range`/`radd`/`rzero`/`rrefl`/`rcongr`/`rchain`/`rtrans`/`rsymm`/`req`
//! (this file's `ops.rs` imports), while every occurrence talking about an
//! INDEX (`Nat.sub`, `Nat.succ`, bounds) is untouched. The one place this
//! needs a NEW combinator rather than a substitution: `Nat`'s own `d.congr`
//! is hard-wired to conclude `Eq Nat (f a) (f b)`
//! (`nat_prelude::ops::NatOps::congr`), which type-checked there only because
//! `Nat`'s `F` was `Nat → Nat → Nat` — codomain `Nat`. Here `F : Nat → Nat →
//! Rat`, so lifting an INDEX equality (`Eq Nat a b`, e.g. from
//! `succ_sub_of_le`) through a VALUE-returning closure needs
//! [`super::ops::nat_eq_to_rat`] in place of `d.congr` at exactly the three
//! sites where `Nat`'s script congruences over a `sum_range`/`apply ff`
//! closure: [`diagonal_pointwise`]'s `h_sub_lift`, [`boundary_peel`]'s
//! `h_lift`, and [`rect_pointwise`]'s `h_lift`. Every other congruence in
//! this file is either purely INDEX-level (stays `d.congr`) or purely
//! VALUE-level (`rcongr`, since both its hypothesis and its closure are
//! already `Eq Rat`). No other divergence from the `Nat` source was needed —
//! the antidiagonal reindexing, the triangle/corner split, and every proof
//! SHAPE (which lemma closes which step) transcribe unchanged.
//!
//! `Rat.sumRange_split` and `Rat.sumRange_congr_lt`/`Rat.sumRange_add` (this
//! file's other two value-level prerequisites) already exist on `Rat` for the
//! `sumRange_split` case new here and for the other two already declared in
//! `rat_prelude::sum` (`Rat.sumRange_congr_lt` for
//! [`super::probability::declare_covariance_sum_vars_left`], `Rat.sumRange_add`
//! from the start) — so this file supplies exactly `sumRange_split`,
//! `sumRange_diagonal`, and `sumRange_rect_eq_diag_add_corner`, nothing
//! `sum.rs` did not already have a use for.
//!
//! # What this file does NOT establish
//!
//! `Rat.sumRange_rect_eq_diag_add_corner` is the SAME-bound `n×n` square
//! decomposition `Nat`'s version is (`rect_row`/`corner_row` both take the
//! single bound `n`). The Cauchy product target `polyEval_mul` needs a
//! TWO-different-bounds statement (`polyEval a m x * polyEval b n x`, `m ≠ n`
//! in general), and porting a same-bound square to a same-bound square does
//! not by itself supply that — see `rat_prelude/polynomial.rs`'s module doc
//! for the counterexample showing why the literal Cauchy-product statement
//! needs additional hypotheses (or a differently-bounded `conv`) beyond what
//! this file's machinery alone gives.

use super::RatPrelude;
use super::ops::{
    nat_eq_to_rat, radd, rat_ty, rchain, rcongr, req, rmul, rrefl, rsum_range, rsymm, rtrans,
    rzero,
};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::{NatOps, NatPrelude};

// ---------------------------------------------------------------------------
// Term builders shared by the diagonal reindexing and the rectangle/corner
// decomposition — the `Rat`-valued analogues of
// `nat_prelude::diagonal::{row_inner, row_fn, combined_fn, triangle_sum,
// row_sum}`.
// ---------------------------------------------------------------------------

/// `fun j => F i j`, `F` partially applied at the fixed row index `i`.
fn row_inner(d: &mut IntDev<'_>, ff: ExprId, i: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let fij = d.apply(ff, &[i, j]);
    d.lam_fv(j_fv, nat, fij)
}

/// `fun i => sumRange (fun j => F i j) (sub bound i)` — one row of the
/// row-major reindexing, out to `bound`.
fn row_fn(d: &mut IntDev<'_>, p: RatPrelude, ff: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let inner = row_inner(d, ff, i);
    let b = d.sub(bound, i);
    let sr = rsum_range(d, p, inner, b);
    d.lam_fv(i_fv, nat, sr)
}

/// `fun i => F i (sub k i)` — the antidiagonal `k`'s per-position summand.
fn diag_inner(d: &mut IntDev<'_>, ff: ExprId, k: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ki = d.sub(k, i);
    let fiki = d.apply(ff, &[i, ki]);
    d.lam_fv(i_fv, nat, fiki)
}

/// `fun k => sumRange (diag_inner F k) (succ k)` — one antidiagonal's sum.
fn t_fn(d: &mut IntDev<'_>, p: RatPrelude, ff: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let inner = diag_inner(d, ff, k);
    let sk = d.succ(k);
    let sr = rsum_range(d, p, inner, sk);
    d.lam_fv(k_fv, nat, sr)
}

/// The triangle sum by ANTIDIAGONAL: `sumRange (t_fn F) n`.
fn triangle_sum(d: &mut IntDev<'_>, p: RatPrelude, ff: ExprId, n: ExprId) -> ExprId {
    let t = t_fn(d, p, ff);
    rsum_range(d, p, t, n)
}

/// The triangle sum by ROW: `sumRange (row_fn F n) n`.
fn row_sum(d: &mut IntDev<'_>, p: RatPrelude, ff: ExprId, n: ExprId) -> ExprId {
    let r = row_fn(d, p, ff, n);
    rsum_range(d, p, r, n)
}

/// `fun i => add (apply f i) (apply g i)` — matches `sumRange_add`'s own
/// internal combined function shape exactly.
fn combined_fn(d: &mut IntDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let body = radd(d, fi, gi);
    d.lam_fv(i_fv, nat, body)
}

/// `fun k => f (add m k)` — `f` shifted so its own zero sits at `m`. Shared by
/// [`declare_sum_range_split`] (the tail function) and [`corner_inner`] (the
/// corner's own reindexing).
fn shifted(d: &mut IntDev<'_>, f: ExprId, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let mk = d.add(m, k);
    let fmk = d.apply(f, &[mk]);
    d.lam_fv(k_fv, nat, fmk)
}

// ---------------------------------------------------------------------------
// `Rat.sumRange_split`.
// ---------------------------------------------------------------------------

/// `Rat.sumRange_split : ∀ f m j,`
/// `sumRange f (add m j) = add (sumRange f m) (sumRange (fun k => f (add m k)) j)`.
///
/// By induction on `j`, `f` and `m` held fixed — every step uses only
/// `Nat.add`'s and `Rat.sumRange`'s own defining equations plus
/// `Rat.add_zero`/`Rat.add_assoc`, never `Nat.sub`. The `Rat` port of
/// `nat_prelude::rectangle::declare_sum_range_split`.
pub(super) fn declare_sum_range_split(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let g = shifted(d, f, m);
    let sum_f_m = rsum_range(d, p, f, m);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let bound = d.add(m, x);
        let lhs = rsum_range(d, p, f, bound);
        let tail = rsum_range(d, p, g, x);
        let rhs = radd(d, sum_f_m, tail);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, j);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_r = rzero(d, p);
            let rhs = radd(d, sum_f_m, zero_r);
            // add_zero sum_f_m : Eq(add sum_f_m zero, sum_f_m); flip it.
            let h = d.lemma(p.add_zero, &[sum_f_m]);
            rsymm(d, rhs, sum_f_m, h)
        },
        &|d, k, ih| {
            // ih : Eq Rat (sumRange f (add m k)) (add sum_f_m (sumRange g k))
            let mk = d.add(m, k);
            let f_mk = d.apply(f, &[mk]);
            let sum_f_mk = rsum_range(d, p, f, mk);
            let sum_g_k = rsum_range(d, p, g, k);
            let sum_f_m_g_k = radd(d, sum_f_m, sum_g_k);

            let start = radd(d, sum_f_mk, f_mk);
            let mid = radd(d, sum_f_m_g_k, f_mk);
            let h1 = rcongr(d, sum_f_mk, sum_f_m_g_k, ih, &|d, t| radd(d, t, f_mk));

            let inner = radd(d, sum_g_k, f_mk);
            let end = radd(d, sum_f_m, inner);
            let h2 = d.lemma(p.add_assoc, &[sum_f_m, sum_g_k, f_mk]);

            let (_e, chained) = rchain(d, start, &[(mid, h1), (end, h2)]);
            chained
        },
        j,
    );

    let ty = {
        let over_j = d.pi_fv(j_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_j);
        d.pi_fv(f_fv, fn_ty, over_m)
    };
    let value = {
        let over_j = d.lam_fv(j_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_j);
        d.lam_fv(f_fv, fn_ty, over_m)
    };
    d.declare_theorem(p.sum_range_split, ty, value)
}

// ---------------------------------------------------------------------------
// Successor-case pieces for `sumRange_diagonal`.
// ---------------------------------------------------------------------------

/// `∀ i, Lt i n → Eq Rat (row_fn F (succ n) applied i) (add (row_fn F n applied i) (diag_inner F n applied i))`.
fn diagonal_pointwise(
    d: &mut IntDev<'_>,
    np: NatPrelude,
    rp: RatPrelude,
    ff: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let sn = d.succ(n);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp_ty = d.lt(i, n);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    // Le i n, from Lt i n (definitionally Le (succ i) n) via le_succ + le_trans.
    let si = d.succ(i);
    let le_succ_i = d.lemma(np.le_succ, &[i]);
    let le_i_n = d.lemma(np.le_trans, &[i, si, n, le_succ_i, hi]);

    // sub (succ n) i = succ (sub n i) -- INDEX-level, Nat's own lemma.
    let h_sub = d.lemma(np.succ_sub_of_le, &[n, i, le_i_n]);
    let sub_n_i = d.sub(n, i);
    let succ_sub_n_i = d.succ(sub_n_i);
    let sub_sn_i = d.sub(sn, i);

    let row_inner_i = row_inner(d, ff, i);
    // Lift the INDEX equality h_sub into a VALUE (Rat) equality: `d.congr`
    // cannot do this (it is hard-wired to `Eq Nat`), since `sum_range` here
    // is Rat-valued.
    let h_sub_lift = nat_eq_to_rat(d, sub_sn_i, succ_sub_n_i, h_sub, &|d, x| {
        rsum_range(d, rp, row_inner_i, x)
    });
    let next1 = rsum_range(d, rp, row_inner_i, succ_sub_n_i);

    // sumRange(row_inner_i, succ (sub n i)) = sumRange(row_inner_i, sub n i) + row_inner_i(sub n i)
    let h_succ = d.lemma(rp.sum_range_succ, &[row_inner_i, sub_n_i]);
    let sum_row_inner_i_subni = rsum_range(d, rp, row_inner_i, sub_n_i);
    let row_inner_i_subni = d.apply(row_inner_i, &[sub_n_i]);
    let target_sum = radd(d, sum_row_inner_i_subni, row_inner_i_subni);

    let start = rsum_range(d, rp, row_inner_i, sub_sn_i);
    let (_e, body_eq) = rchain(d, start, &[(next1, h_sub_lift), (target_sum, h_succ)]);

    let with_hi = d.lam_fv(hi_fv, hyp_ty, body_eq);
    d.lam_fv(i_fv, nat, with_hi)
}

/// `Eq Rat (row_fn F (succ n) applied n) (F n zero)` — the row-major side's
/// new `i = n` boundary term collapses to `F n 0`.
fn boundary_peel(
    d: &mut IntDev<'_>,
    np: NatPrelude,
    rp: RatPrelude,
    ff: ExprId,
    n: ExprId,
) -> ExprId {
    let sn = d.succ(n);
    let row_inner_n = row_inner(d, ff, n);

    let le_refl_n = d.const_app(np.le_refl, &[n]);
    let h_b1 = d.lemma(np.succ_sub_of_le, &[n, n, le_refl_n]);
    let sub_sn_n = d.sub(sn, n);
    let sub_nn = d.sub(n, n);
    let succ_sub_nn = d.succ(sub_nn);

    let h_b2 = d.lemma(np.sub_self, &[n]);
    let zero = d.zero();
    // INDEX-only congruence (Nat -> Nat via succ): stays Nat's own `d.congr`.
    let h_b2_lift = d.congr(sub_nn, zero, h_b2, &|d, x| d.succ(x));
    let succ_zero = d.succ(zero);

    let (_e1, h_sub_chain) = d.chain(sub_sn_n, &[(succ_sub_nn, h_b1), (succ_zero, h_b2_lift)]);

    // Lift the INDEX chain result into a VALUE (Rat) equality.
    let h_lift = nat_eq_to_rat(d, sub_sn_n, succ_zero, h_sub_chain, &|d, x| {
        rsum_range(d, rp, row_inner_n, x)
    });
    let start = rsum_range(d, rp, row_inner_n, sub_sn_n);
    let next1 = rsum_range(d, rp, row_inner_n, succ_zero);

    let h_b3 = d.lemma(rp.sum_range_succ, &[row_inner_n, zero]);
    let sum_row_inner_n_zero = rsum_range(d, rp, row_inner_n, zero);
    let row_inner_n_zero = d.apply(row_inner_n, &[zero]);
    let next2 = radd(d, sum_row_inner_n_zero, row_inner_n_zero);

    let h_zero_sum = d.lemma(rp.sum_range_zero, &[row_inner_n]);
    let zero_r = rzero(d, rp);
    let h_zero_lift = rcongr(d, sum_row_inner_n_zero, zero_r, h_zero_sum, &|d, x| {
        radd(d, x, row_inner_n_zero)
    });
    let next3 = radd(d, zero_r, row_inner_n_zero);

    let h_za = d.lemma(rp.zero_add, &[row_inner_n_zero]);

    let (_e2, proof) = rchain(
        d,
        start,
        &[
            (next1, h_lift),
            (next2, h_b3),
            (next3, h_zero_lift),
            (row_inner_n_zero, h_za),
        ],
    );
    proof
}

/// The successor step: given `ih : T(n) = R(n)`, prove `T(succ n) = R(succ n)`.
fn diagonal_step(
    d: &mut IntDev<'_>,
    np: NatPrelude,
    rp: RatPrelude,
    ff: ExprId,
    n: ExprId,
    ih: ExprId,
) -> ExprId {
    let sn = d.succ(n);
    let zero = d.zero();

    // ---- shared pieces ----
    let t_fn_ff = t_fn(d, rp, ff);
    let t_n = rsum_range(d, rp, t_fn_ff, n);
    let t_sn = rsum_range(d, rp, t_fn_ff, sn);

    let row_fn_n = row_fn(d, rp, ff, n);
    let r_n = rsum_range(d, rp, row_fn_n, n);

    let row_fn_sn = row_fn(d, rp, ff, sn);
    let r_sn = rsum_range(d, rp, row_fn_sn, sn);

    let dinner_n = diag_inner(d, ff, n);
    let s_term = rsum_range(d, rp, dinner_n, n);

    let f_n_zero = d.apply(ff, &[n, zero]);

    // ================= LHS: T(succ n) = r_n + (s_term + f_n_zero) =================
    let h_l1 = d.lemma(rp.sum_range_succ, &[t_fn_ff, n]);
    let t_fn_ff_n = d.apply(t_fn_ff, &[n]);
    let l_mid1 = radd(d, t_n, t_fn_ff_n);

    let h_l2 = d.lemma(rp.sum_range_succ, &[dinner_n, n]);
    let dinner_n_n = d.apply(dinner_n, &[n]);
    let s_plus_dinner_n_n = radd(d, s_term, dinner_n_n);
    let h_l2_lift = rcongr(d, t_fn_ff_n, s_plus_dinner_n_n, h_l2, &|d, x| {
        radd(d, t_n, x)
    });
    let l_mid2 = radd(d, t_n, s_plus_dinner_n_n);

    let sub_nn = d.sub(n, n);
    let h_sub_self = d.lemma(np.sub_self, &[n]);
    // INDEX equality (sub n n = zero) lifted through a VALUE-returning
    // closure (F n _).
    let h_l3 = nat_eq_to_rat(d, sub_nn, zero, h_sub_self, &|d, x| d.apply(ff, &[n, x]));
    let h_l3_lift = rcongr(d, dinner_n_n, f_n_zero, h_l3, &|d, x| radd(d, s_term, x));
    let s_plus_fn0 = radd(d, s_term, f_n_zero);
    let h_l3_final = rcongr(d, s_plus_dinner_n_n, s_plus_fn0, h_l3_lift, &|d, x| {
        radd(d, t_n, x)
    });
    let l_mid3 = radd(d, t_n, s_plus_fn0);

    let r_plus_s_fn0 = radd(d, r_n, s_plus_fn0);
    let h_ih_lift = rcongr(d, t_n, r_n, ih, &|d, x| radd(d, x, s_plus_fn0));

    let (_e_l, lhs_proof) = rchain(
        d,
        t_sn,
        &[
            (l_mid1, h_l1),
            (l_mid2, h_l2_lift),
            (l_mid3, h_l3_final),
            (r_plus_s_fn0, h_ih_lift),
        ],
    );
    // lhs_proof : Eq Rat(t_sn, r_plus_s_fn0)

    // ================= RHS: R(succ n) = (r_n + s_term) + f_n_zero =================
    let h_r1 = d.lemma(rp.sum_range_succ, &[row_fn_sn, n]);
    let sum_row_sn_n = rsum_range(d, rp, row_fn_sn, n);
    let row_fn_sn_n = d.apply(row_fn_sn, &[n]);
    let r_mid1 = radd(d, sum_row_sn_n, row_fn_sn_n);

    let combined_g = combined_fn(d, row_fn_n, dinner_n);
    let pointwise = diagonal_pointwise(d, np, rp, ff, n);
    let h_r2 = d.lemma(
        rp.sum_range_congr_lt,
        &[row_fn_sn, combined_g, n, pointwise],
    );
    let sum_combined_n = rsum_range(d, rp, combined_g, n);

    let h_r3 = d.lemma(rp.sum_range_add, &[row_fn_n, dinner_n, n]);
    let r_plus_s = radd(d, r_n, s_term);

    let (_e_r0, h_r_sum) = rchain(d, sum_row_sn_n, &[(sum_combined_n, h_r2), (r_plus_s, h_r3)]);
    let h_r1_lift = rcongr(d, sum_row_sn_n, r_plus_s, h_r_sum, &|d, x| {
        radd(d, x, row_fn_sn_n)
    });
    let r_mid2 = radd(d, r_plus_s, row_fn_sn_n);

    let h_bnd = boundary_peel(d, np, rp, ff, n);
    let h_bnd_lift = rcongr(d, row_fn_sn_n, f_n_zero, h_bnd, &|d, x| {
        radd(d, r_plus_s, x)
    });
    let r_mid3 = radd(d, r_plus_s, f_n_zero);

    let (_e_r, rhs_proof) = rchain(
        d,
        r_sn,
        &[(r_mid1, h_r1), (r_mid2, h_r1_lift), (r_mid3, h_bnd_lift)],
    );
    // rhs_proof : Eq Rat(r_sn, r_mid3)

    // ================= assemble via add_assoc =================
    let h_assoc = d.lemma(rp.add_assoc, &[r_n, s_term, f_n_zero]);

    let r_sn_eq_r_plus_s_fn0 = rtrans(d, r_sn, r_mid3, r_plus_s_fn0, rhs_proof, h_assoc);
    let r_plus_s_fn0_eq_r_sn = rsymm(d, r_sn, r_plus_s_fn0, r_sn_eq_r_plus_s_fn0);

    rtrans(d, t_sn, r_plus_s_fn0, r_sn, lhs_proof, r_plus_s_fn0_eq_r_sn)
}

/// `Rat.sumRange_diagonal : ∀ F n,`
/// `sumRange (fun k => sumRange (fun i => F i (sub k i)) (succ k)) n`
/// `= sumRange (fun i => sumRange (fun j => F i j) (sub n i)) n`.
///
/// The `Rat` port of `nat_prelude::diagonal::declare_sum_range_diagonal`. The
/// base case (`n = 0`) is `Eq.refl Rat.zero`: both sides `δι`-reduce to
/// `Rat.zero` regardless of `F`, exactly as `Nat`'s own base case does.
pub(super) fn declare_sum_range_diagonal(
    d: &mut IntDev<'_>,
    np: NatPrelude,
    rp: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn2_ty = {
        let inner = d.arrow(nat, carrier);
        d.arrow(nat, inner)
    };
    let f_fv = d.fresh_fvar();
    let ff = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let lhs = triangle_sum(d, rp, ff, x);
        let rhs = row_sum(d, rp, ff, x);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero_r = rzero(d, rp);
            rrefl(d, zero_r)
        },
        &|d, j, ih| diagonal_step(d, np, rp, ff, j, ih),
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn2_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn2_ty, over_n)
    };
    d.declare_theorem(rp.sum_range_diagonal, ty, value)
}

// ---------------------------------------------------------------------------
// The rectangle, and the corner (`Rat` port of `nat_prelude::rectangle`).
// ---------------------------------------------------------------------------

/// `fun i => sumRange (fun j => F i j) n` — one row of the RECTANGLE sum, at
/// its full width `n` (unlike [`row_fn`], which stops at `n−i`).
fn rect_row(d: &mut IntDev<'_>, p: RatPrelude, ff: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let inner = row_inner(d, ff, i);
    let sr = rsum_range(d, p, inner, n);
    d.lam_fv(i_fv, nat, sr)
}

/// The rectangle sum `Σ_{i<n} Σ_{j<n} F i j`.
fn rectangle_sum(d: &mut IntDev<'_>, p: RatPrelude, ff: ExprId, n: ExprId) -> ExprId {
    let r = rect_row(d, p, ff, n);
    rsum_range(d, p, r, n)
}

/// Row `i`'s corner summand: `shifted(row_inner F i, sub n i)`, i.e.
/// `fun k => F i (add (sub n i) k)`.
fn corner_inner(d: &mut IntDev<'_>, ff: ExprId, i: ExprId, n: ExprId) -> ExprId {
    let row_inner_i = row_inner(d, ff, i);
    let sub_ni = d.sub(n, i);
    shifted(d, row_inner_i, sub_ni)
}

/// `fun i => sumRange (corner_inner F i n) i` — row `i`'s corner mass.
fn corner_row(d: &mut IntDev<'_>, p: RatPrelude, ff: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let inner = corner_inner(d, ff, i, n);
    let sr = rsum_range(d, p, inner, i);
    d.lam_fv(i_fv, nat, sr)
}

/// The corner sum `Σ_{i<n} Σ_{k<i} F i ((n−i)+k)`.
fn corner_sum(d: &mut IntDev<'_>, p: RatPrelude, ff: ExprId, n: ExprId) -> ExprId {
    let c = corner_row(d, p, ff, n);
    rsum_range(d, p, c, n)
}

/// `∀ i, Lt i n → Eq Rat (sumRange (row_inner F i) n)`
/// `(add (sumRange (row_inner F i) (sub n i)) (sumRange (corner_inner F i n) i))`.
fn rect_pointwise(
    d: &mut IntDev<'_>,
    np: NatPrelude,
    rp: RatPrelude,
    ff: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hyp_ty = d.lt(i, n);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);

    // Le i n, from Lt i n via le_succ + le_trans.
    let si = d.succ(i);
    let le_succ_i = d.lemma(np.le_succ, &[i]);
    let le_i_n = d.lemma(np.le_trans, &[i, si, n, le_succ_i, hi]);

    let row_inner_i = row_inner(d, ff, i);
    let sub_ni = d.sub(n, i);

    // sub_add_cancel i n le_i_n : add (sub n i) i = n -- INDEX-level.
    let h_restore = d.lemma(np.sub_add_cancel, &[i, n, le_i_n]);
    let add_sub_i = d.add(sub_ni, i);
    let n_eq = d.symm(add_sub_i, n, h_restore);
    // n_eq : Eq Nat n add_sub_i

    let sum_row_i_n = rsum_range(d, rp, row_inner_i, n);
    let sum_row_i_addsubi = rsum_range(d, rp, row_inner_i, add_sub_i);
    // Lift the INDEX equality n_eq into a VALUE (Rat) equality.
    let h_lift = nat_eq_to_rat(d, n, add_sub_i, n_eq, &|d, x| {
        rsum_range(d, rp, row_inner_i, x)
    });

    let h_split = d.lemma(rp.sum_range_split, &[row_inner_i, sub_ni, i]);

    let sum_row_i_subni = rsum_range(d, rp, row_inner_i, sub_ni);
    let corner_i = shifted(d, row_inner_i, sub_ni);
    let sum_corner_i = rsum_range(d, rp, corner_i, i);
    let rhs = radd(d, sum_row_i_subni, sum_corner_i);

    let (_e, body) = rchain(
        d,
        sum_row_i_n,
        &[(sum_row_i_addsubi, h_lift), (rhs, h_split)],
    );

    let with_hi = d.lam_fv(hi_fv, hyp_ty, body);
    d.lam_fv(i_fv, nat, with_hi)
}

/// `Eq Rat (rectangle_sum F n) (add (row_sum F n) (corner_sum F n))`.
fn rectangle_split_step(
    d: &mut IntDev<'_>,
    np: NatPrelude,
    rp: RatPrelude,
    ff: ExprId,
    n: ExprId,
) -> ExprId {
    let rect_row_n = rect_row(d, rp, ff, n);
    let row_fn_n = row_fn(d, rp, ff, n);
    let corner_row_n = corner_row(d, rp, ff, n);
    let combined = combined_fn(d, row_fn_n, corner_row_n);

    let pointwise = rect_pointwise(d, np, rp, ff, n);
    let h1 = d.lemma(rp.sum_range_congr_lt, &[rect_row_n, combined, n, pointwise]);

    let h2 = d.lemma(rp.sum_range_add, &[row_fn_n, corner_row_n, n]);

    let rect_sum = rsum_range(d, rp, rect_row_n, n);
    let sum_combined = rsum_range(d, rp, combined, n);
    let row_sum_n = rsum_range(d, rp, row_fn_n, n);
    let corner_sum_n = rsum_range(d, rp, corner_row_n, n);
    let final_rhs = radd(d, row_sum_n, corner_sum_n);

    let (_e, proof) = rchain(d, rect_sum, &[(sum_combined, h1), (final_rhs, h2)]);
    proof
}

/// `Rat.sumRange_rect_eq_diag_add_corner : ∀ F n,`
/// `sumRange (fun i => sumRange (fun j => F i j) n) n`
/// `= add (sumRange (fun k => sumRange (fun i => F i (sub k i)) (succ k)) n)`
/// `      (sumRange (fun i => sumRange (fun k => F i (add (sub n i) k)) i) n)`
/// — rectangle = (antidiagonal triangle) + corner, same-bound `n×n` square,
/// the `Rat` port of `nat_prelude::rectangle::declare_sum_range_rect_eq_diag_add_corner`.
pub(super) fn declare_sum_range_rect_eq_diag_add_corner(
    d: &mut IntDev<'_>,
    np: NatPrelude,
    rp: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn2_ty = {
        let inner = d.arrow(nat, carrier);
        d.arrow(nat, inner)
    };
    let f_fv = d.fresh_fvar();
    let ff = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let rect = rectangle_sum(d, rp, ff, n);
    let tri = triangle_sum(d, rp, ff, n);
    let corner = corner_sum(d, rp, ff, n);
    let rhs_stmt = radd(d, tri, corner);
    let stmt = req(d, rect, rhs_stmt);

    let split_proof = rectangle_split_step(d, np, rp, ff, n);

    let row_sum_n = row_sum(d, rp, ff, n);
    let corner_sum_n = corner_sum(d, rp, ff, n);
    let mid = radd(d, row_sum_n, corner_sum_n);

    // sum_range_diagonal ff n : Eq Rat(triangle_sum, row_sum)  [T(n) = R(n)]
    let h_diag = d.lemma(rp.sum_range_diagonal, &[ff, n]);
    let h_diag_symm = rsymm(d, tri, row_sum_n, h_diag);

    let h_lift = rcongr(d, row_sum_n, tri, h_diag_symm, &|d, x| {
        radd(d, x, corner_sum_n)
    });

    let (_e, proof) = rchain(d, rect, &[(mid, split_proof), (rhs_stmt, h_lift)]);

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn2_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn2_ty, over_n)
    };
    d.declare_theorem(rp.sum_range_rect_eq_diag_add_corner, ty, value)
}

// ---------------------------------------------------------------------------
// The PRODUCT of two finite sums, and its honest Cauchy decomposition.
//
// Everything above this line is generic in `F : Nat → Nat → Rat`. Everything
// below specialises it to the SEPARABLE summand `F i j := f i * g j`, which is
// the only shape a product of two `sumRange`s ever produces — and the shape
// both blocked consumers (`Rat.polyEval_mul`, general-degree `Rat` Taylor)
// need. The `Rat` port of `Complex.sumRange_mul` /
// `Complex.sumRange_mul_double` / `Complex.sumRange_mul_eq_diag_add_corner`
// (`complex.rs`), which already ran this exact argument over `ℂ`'s setoid:
// `Equiv`/`equiv_trans` there become `Eq`/[`rchain`] here, and `ℂ`'s
// `const_app(p.mul, …)`/`const_app(p.sum_range, …)` become `rmul`/`rsum_range`.
// No step of the argument changes, because none of it touches `Nat.sub` or any
// other index arithmetic — see this module's `# Does this port mechanically?`
// note, which applies to the `ℂ → ℚ` direction for the same reason.
// ---------------------------------------------------------------------------

/// `fun i => mul (f i) c` — each summand scaled on the RIGHT by a constant.
fn scaled_right(d: &mut IntDev<'_>, f: ExprId, c: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let body = rmul(d, fi, c);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => mul c (f i)` — each summand scaled on the LEFT, which is the
/// shape [`RatPrelude::mul_sum_range`](super::RatPrelude::mul_sum_range)'s own
/// right-hand side is built in. The only reason both this and
/// [`scaled_right`] exist is that `Rat` has a left-distribution lemma and no
/// right one; `mul_comm` under the sum converts between them.
fn scaled_left(d: &mut IntDev<'_>, f: ExprId, c: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let body = rmul(d, c, fi);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => sumRange (fun j => mul (f i) (g j)) n` — one row of the separable
/// rectangle, written DIRECTLY rather than as an `F i j` application.
fn double_fn(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    f: ExprId,
    g: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let gj = d.apply(g, &[j]);
    let body = rmul(d, fi, gj);
    let inner = d.lam_fv(j_fv, nat, body);
    let row = rsum_range(d, p, inner, n);
    d.lam_fv(i_fv, nat, row)
}

/// `fun i => fun j => mul (f i) (g j)` — the same separable summand CURRIED,
/// i.e. the `F : Nat → Nat → Rat` that
/// [`declare_sum_range_rect_eq_diag_add_corner`] quantifies over.
fn separable_fn(d: &mut IntDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let gj = d.apply(g, &[j]);
    let body = rmul(d, fi, gj);
    let inner = d.lam_fv(j_fv, nat, body);
    d.lam_fv(i_fv, nat, inner)
}

/// `sumRange (fun k => sumRange (fun i => mul (f i) (g (sub k i))) (succ k)) n`
/// — the antidiagonal-grouped convolution `Σ_{k<n} Σ_{i≤k} f i · g (k−i)`,
/// written WITHOUT the `F i (k−i)` redex [`triangle_sum`] leaves behind.
///
/// Building the STATEMENT this way and the PROOF through [`triangle_sum`] is
/// deliberate: the two are beta-equivalent, and paying one beta bridge in the
/// kernel buys every downstream consumer a statement it can read and match
/// against without first reducing a redex. `Complex` kept the applied form and
/// its pinned type carries `(fun x5 x6 => Complex.mul (x0 x5) (x1 x6)) x4
/// (AxNat.sub x3 x4)` in the middle of the convolution — legible to nobody.
fn separable_triangle(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    f: ExprId,
    g: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let ki = d.sub(k, i);
    let gki = d.apply(g, &[ki]);
    let cell = rmul(d, fi, gki);
    let inner = d.lam_fv(i_fv, nat, cell);
    let sk = d.succ(k);
    let row = rsum_range(d, p, inner, sk);
    let t = d.lam_fv(k_fv, nat, row);
    rsum_range(d, p, t, n)
}

/// `sumRange (fun i => sumRange (fun k => mul (f i) (g (add (sub n i) k))) i) n`
/// — the corner mass the naive finite Cauchy identity silently drops, in the
/// same redex-free shape [`separable_triangle`] uses.
///
/// Note the `Nat.add` operand order: `add (sub n i) k`, the shifted index
/// LEFT and the running index right, matching [`shifted`] exactly. This is
/// not cosmetic — reversing it changes which argument `Nat.add`'s recursion
/// is stuck on.
fn separable_corner(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    f: ExprId,
    g: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let fi = d.apply(f, &[i]);
    let sub_ni = d.sub(n, i);
    let idx = d.add(sub_ni, k);
    let gidx = d.apply(g, &[idx]);
    let cell = rmul(d, fi, gidx);
    let inner = d.lam_fv(k_fv, nat, cell);
    let row = rsum_range(d, p, inner, i);
    let c = d.lam_fv(i_fv, nat, row);
    rsum_range(d, p, c, n)
}

/// `Rat.sumRange_mul : ∀ f g m n,`
/// `mul (sumRange f m) (sumRange g n) = sumRange (fun i => mul (f i) (sumRange g n)) m`.
///
/// **Not an induction.** `S := sumRange g n` plays exactly the "constant"
/// role [`RatPrelude::mul_sum_range`](super::RatPrelude::mul_sum_range)
/// already handles, on the other side of the product: `mul_comm` swaps the
/// product, `mul_sumRange S f m` distributes `S` through the sum, and
/// `sumRange_congr` commutes each summand back. Three existing lemmas chained
/// by `Eq.trans`.
///
/// TWO independent bounds `m`, `n` — nothing here requires them equal, and
/// the two-bound form is what a general-degree polynomial product needs.
pub(super) fn declare_sum_range_mul(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let s = rsum_range(d, p, g, n);
    let sf = rsum_range(d, p, f, m);
    let lhs = rmul(d, sf, s);
    let scaled_r = scaled_right(d, f, s);
    let rhs = rsum_range(d, p, scaled_r, m);
    let stmt = req(d, lhs, rhs);

    // mul (sumRange f m) S = mul S (sumRange f m)
    let mid = rmul(d, s, sf);
    let h1 = d.lemma(p.mul_comm, &[sf, s]);

    // mul S (sumRange f m) = sumRange (fun i => mul S (f i)) m
    let scaled_l = scaled_left(d, f, s);
    let mid2 = rsum_range(d, p, scaled_l, m);
    let h2 = d.lemma(p.mul_sum_range, &[s, f, m]);

    // pointwise mul_comm puts the constant back on the right.
    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = d.lemma(p.mul_comm, &[s, fi]);
        d.lam_fv(i_fv, nat, body)
    };
    let h3 = d.lemma(p.sum_range_congr, &[scaled_l, scaled_r, m, pointwise]);

    let (_e, proof) = rchain(d, lhs, &[(mid, h1), (mid2, h2), (rhs, h3)]);

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_g = d.pi_fv(g_fv, fn_ty, over_m);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_g = d.lam_fv(g_fv, fn_ty, over_m);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.sum_range_mul, ty, value)
}

/// `Rat.sumRange_mul_double : ∀ f g m n,`
/// `mul (sumRange f m) (sumRange g n)`
/// `= sumRange (fun i => sumRange (fun j => mul (f i) (g j)) n) m`.
///
/// The un-grouped, **subtraction-free** rectangle form of the Cauchy product:
/// a product of two finite sums as one double sum with `f i * g j` at every
/// pair `(i, j)`, `i < m`, `j < n`. From [`declare_sum_range_mul`] (whose RHS
/// is already `sumRange (fun i => mul (f i) (sumRange g n)) m`) plus
/// `sumRange_congr` moving `mul_sumRange` (at `c := f i`) under the outer sum.
///
/// This is NOT the diagonal-grouped convolution — see
/// [`declare_sum_range_mul_eq_diag_add_corner`], which is.
pub(super) fn declare_sum_range_mul_double(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let s = rsum_range(d, p, g, n);
    let sf = rsum_range(d, p, f, m);
    let lhs = rmul(d, sf, s);
    let double = double_fn(d, p, f, g, n);
    let rhs = rsum_range(d, p, double, m);
    let stmt = req(d, lhs, rhs);

    let h1 = d.lemma(p.sum_range_mul, &[f, g, m, n]);
    let scaled = scaled_right(d, f, s);
    let mid = rsum_range(d, p, scaled, m);

    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let fi = d.apply(f, &[i]);
        let body = d.lemma(p.mul_sum_range, &[fi, g, n]);
        d.lam_fv(i_fv, nat, body)
    };
    let h2 = d.lemma(p.sum_range_congr, &[scaled, double, m, pointwise]);

    let (_e, proof) = rchain(d, lhs, &[(mid, h1), (rhs, h2)]);

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_g = d.pi_fv(g_fv, fn_ty, over_m);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_g = d.lam_fv(g_fv, fn_ty, over_m);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.sum_range_mul_double, ty, value)
}

/// `Rat.sumRange_mul_eq_diag_add_corner : ∀ f g n,`
/// `mul (sumRange f n) (sumRange g n)`
/// `= add (sumRange (fun k => sumRange (fun i => mul (f i) (g (sub k i))) (succ k)) n)`
/// `      (sumRange (fun i => sumRange (fun k => mul (f i) (g (add (sub n i) k))) i) n)`
///
/// **The finite Cauchy product's honest form over `ℚ`**: a product of two
/// partial sums equals the antidiagonal-grouped convolution PLUS a corner term
/// that the naive (false) identity silently drops. The corner is not an
/// artefact of the proof — `nat_prelude`'s development records that the naive
/// identity is refuted already at `n = 2`.
///
/// Composes [`declare_sum_range_mul_double`] at `[f, g, n, n]` (product =
/// rectangle) with [`declare_sum_range_rect_eq_diag_add_corner`] at
/// `[fun i j => f i * g j, n]` (rectangle = triangle + corner).
///
/// Two beta bridges, both discharged by the kernel's own defeq and neither
/// requiring a lemma: `sum_range_mul_double`'s rectangle is built from the
/// UNCURRIED summand while the rectangle theorem's is `F` applied through this
/// module's curried helpers; and the statement's triangle/corner are written
/// redex-free ([`separable_triangle`]/[`separable_corner`]) while the proof's
/// come from [`triangle_sum`]/[`corner_sum`] applied to the curried `F`.
/// `Complex.sumRange_mul_eq_diag_add_corner` already relies on the first;
/// the second is this port's own, and is what keeps the `ℚ` statement
/// readable where `ℂ`'s is not.
pub(super) fn declare_sum_range_mul_eq_diag_add_corner(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sf = rsum_range(d, p, f, n);
    let sg = rsum_range(d, p, g, n);
    let lhs = rmul(d, sf, sg);

    let tri = separable_triangle(d, p, f, g, n);
    let corner = separable_corner(d, p, f, g, n);
    let rhs_stmt = radd(d, tri, corner);
    let stmt = req(d, lhs, rhs_stmt);

    let big_f = separable_fn(d, f, g);
    let rect = rectangle_sum(d, p, big_f, n);

    let h1 = d.lemma(p.sum_range_mul_double, &[f, g, n, n]);
    let h2 = d.lemma(p.sum_range_rect_eq_diag_add_corner, &[big_f, n]);

    let (_e, proof) = rchain(d, lhs, &[(rect, h1), (rhs_stmt, h2)]);

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.sum_range_mul_eq_diag_add_corner, ty, value)
}

/// Declare this module's results in order: the general split lemma
/// [`declare_sum_range_split`] (which [`rect_pointwise`] needs), the diagonal
/// reindexing [`declare_sum_range_diagonal`] (which the rectangle theorem's
/// final assembly needs), the rectangle/corner headline
/// [`declare_sum_range_rect_eq_diag_add_corner`], and then the three
/// separable-summand consumers that turn it into a statement about a PRODUCT
/// of two sums ([`declare_sum_range_mul`], [`declare_sum_range_mul_double`],
/// [`declare_sum_range_mul_eq_diag_add_corner`]).
pub(super) fn declare_diagonal(d: &mut IntDev<'_>, rp: RatPrelude) -> Result<(), KernelError> {
    let np = d.prelude();
    declare_sum_range_split(d, rp)?;
    declare_sum_range_diagonal(d, np, rp)?;
    declare_sum_range_rect_eq_diag_add_corner(d, np, rp)?;
    declare_sum_range_mul(d, rp)?;
    declare_sum_range_mul_double(d, rp)?;
    declare_sum_range_mul_eq_diag_add_corner(d, rp)?;
    Ok(())
}
