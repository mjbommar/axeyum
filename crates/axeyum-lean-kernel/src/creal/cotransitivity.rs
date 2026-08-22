//! **Cotransitivity of `<` and `#`** (ADR-0512 phase R7): Bishop's
//! constructive replacement for trichotomy.
//!
//! ## Why `lt` needs this
//!
//! [`CReal.lt`](super::CRealPrelude::lt) is not decidable and no `lt_total`
//! is assumed or provable over `CReal` (`Rat.le_or_lt` holds for `ℚ` and does
//! not lift). Cotransitivity — `x < y → ∀ z, x < z ∨ z < y` — is what makes
//! the order usable anyway: it lets a proof compare an arbitrary third real
//! against the *rational* gap a `lt` witness already carries, and `ℚ`'s
//! order **is** decidable ([`RatPrelude::le_or_lt`](crate::RatPrelude::le_or_lt)).
//!
//! ## The estimate, at a single index `N`
//!
//! Given `lt x y` with gap `q > 0`, choose (via
//! [`RatPrelude::nat_div_succ_lt_of_pos`](crate::RatPrelude::nat_div_succ_lt_of_pos)
//! at numerator `10`) an index `N` with `10/(N+1) < q`. Put `P := 4/(N+1)`,
//! `g := 2/(N+1)`, `b := seq x (2N+1)`, `c := seq z N`, and decide
//! `Rat.le_or_lt (b+P) c`:
//!
//! - **`b+P ≤ c`**: `x < z` at gap `g`. The estimate needs no relation
//!   between `q` and `N` at all — regularity of `x` between `2m+1` and
//!   `2N+1`, the branch hypothesis, and regularity of `z` between `N` and
//!   `m` sum to *exactly* `2/(m+1)`, with the `P`-vs-`g` slack absorbing
//!   every `N`-indexed remainder. This branch would close for *any* `N`.
//! - **`c < b+P`**: `z < y` at gap `g`. This is the branch that consumes the
//!   `10/(N+1) < q` margin: combining the branch hypothesis with the
//!   original `lt x y` witness (read at index `N`) gives `c+P ≤ (seq y N)`,
//!   and from there the estimate is the mirror image of the first branch.
//!
//! Both branches share [`build_gap_proof`], parameterised over which real is
//! sampled at the shifted index and which pair of samples plays the role of
//! `(b, c)`.
//!
//! ## Apartness is free
//!
//! [`CReal.Apart`](super::CRealPrelude::apart) is *defined* as `lt x y ∨ lt y
//! x`, so `apart_cotrans` is a four-way case split on [`declare_lt_cotrans`]'s
//! output and the two disjuncts of `Apart`'s own definition — no new
//! estimate.

#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::{
    CRealPrelude, and_intro, cadd, cle, clt, creal_ty, div_succ, embed, gap_elim, gap_halves,
    gap_intro, halves, modulus, sample, shift,
};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{
    den, radd, rat_eq_rewrite, rat_ty, rchain, rcongr, rle, rlt, rneg, rsymm, rtrans, rzero,
};

/// Admit `CReal.lt_cotrans` and `CReal.apart_cotrans`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_cotransitivity(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_lt_cotrans(d, p)?;
    declare_apart_cotrans(d, p)
}

// --- small `Rat` algebra ------------------------------------------------

/// `Eq Rat ((u + k) + (-k)) u`.
fn add_then_neg_cancel_eq(d: &mut IntDev<'_>, p: CRealPrelude, u: ExprId, k: ExprId) -> ExprId {
    let rat = p.rat;
    let neg_k = rneg(d, k);
    let assoc = d.lemma(rat.add_assoc, &[u, k, neg_k]); // (u+k)+(-k) = u+(k+(-k))
    let vanish = d.lemma(rat.add_neg, &[k]); // k+(-k) = 0
    let zero = rzero(d, rat);
    let k_plus_negk = radd(d, k, neg_k);
    let inner = rcongr(d, k_plus_negk, zero, vanish, &|d, t| radd(d, u, t));
    let trim = d.lemma(rat.add_zero, &[u]); // u+0 = u
    let u_plus_k = radd(d, u, k);
    let start = radd(d, u_plus_k, neg_k);
    let mid1 = radd(d, u, k_plus_negk);
    let mid2 = radd(d, u, zero);
    let (_, proof) = rchain(d, start, &[(mid1, assoc), (mid2, inner), (u, trim)]);
    proof
}

/// From `hyp : Rat.le (u+k) v`, derive `Rat.le (u-v) (-k)`.
fn le_sub_neg_of_le_add(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    k: ExprId,
    hyp: ExprId,
) -> ExprId {
    let rat = p.rat;
    let neg_k = rneg(d, k);
    let refl_k = d.lemma(rat.le_refl, &[neg_k]);
    let u_plus_k = radd(d, u, k);
    let shifted = d.lemma(rat.add_le_add, &[u_plus_k, v, neg_k, neg_k, hyp, refl_k]);
    let cancel_eq = add_then_neg_cancel_eq(d, p, u, k); // (u+k)+(-k) = u
    let from_expr = radd(d, u_plus_k, neg_k);
    let to_expr = radd(d, v, neg_k);
    let rewritten = rat_eq_rewrite(d, from_expr, u, cancel_eq, shifted, &|d, t| {
        rle(d, rat, t, to_expr)
    }); // Rat.le u (v + (-k))
    d.lemma(rat.sub_le_of_le, &[u, v, neg_k, rewritten])
}

/// From `hyp : Rat.le (x+k) (y+k)`, derive `Rat.le x y`.
fn cancel_add_right(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    k: ExprId,
    hyp: ExprId,
) -> ExprId {
    let rat = p.rat;
    let neg_k = rneg(d, k);
    let refl_k = d.lemma(rat.le_refl, &[neg_k]);
    let x_plus_k = radd(d, x, k);
    let y_plus_k = radd(d, y, k);
    let shifted = d.lemma(
        rat.add_le_add,
        &[x_plus_k, y_plus_k, neg_k, neg_k, hyp, refl_k],
    );
    let eqx = add_then_neg_cancel_eq(d, p, x, k);
    let eqy = add_then_neg_cancel_eq(d, p, y, k);
    let from_x = radd(d, x_plus_k, neg_k);
    let from_y = radd(d, y_plus_k, neg_k);
    let step1 = rat_eq_rewrite(d, from_x, x, eqx, shifted, &|d, t| rle(d, rat, t, from_y));
    rat_eq_rewrite(d, from_y, y, eqy, step1, &|d, t| rle(d, rat, x, t))
}

/// `Eq Rat ((u-v)+w) ((u+w)-v)`.
fn sub_add_swap_eq(d: &mut IntDev<'_>, p: CRealPrelude, u: ExprId, v: ExprId, w: ExprId) -> ExprId {
    let rat = p.rat;
    let neg_v = rneg(d, v);
    let u_minus_v = rsub(d, rat, u, v);
    let start = radd(d, u_minus_v, w);
    let assoc1 = d.lemma(rat.add_assoc, &[u, neg_v, w]); // (u+(-v))+w = u+((-v)+w)
    let negv_plus_w = radd(d, neg_v, w);
    let mid1 = radd(d, u, negv_plus_w);
    let comm1 = d.lemma(rat.add_comm, &[neg_v, w]); // (-v)+w = w+(-v)
    let w_plus_negv = radd(d, w, neg_v);
    let mid2 = radd(d, u, w_plus_negv);
    let step2 = rcongr(d, negv_plus_w, w_plus_negv, comm1, &|d, t| radd(d, u, t));
    let assoc2 = d.lemma(rat.add_assoc, &[u, w, neg_v]); // (u+w)+(-v) = u+(w+(-v))
    let u_plus_w = radd(d, u, w);
    let target_unfolded = radd(d, u_plus_w, neg_v);
    let step3 = rsymm(d, target_unfolded, mid2, assoc2);
    let (_, proof) = rchain(
        d,
        start,
        &[(mid1, assoc1), (mid2, step2), (target_unfolded, step3)],
    );
    proof
}

/// `Eq Rat ((u+v)+w) ((u+w)+v)`.
fn regroup_swap_last_two_eq(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    u: ExprId,
    v: ExprId,
    w: ExprId,
) -> ExprId {
    let rat = p.rat;
    let u_plus_v = radd(d, u, v);
    let start = radd(d, u_plus_v, w);
    let assoc1 = d.lemma(rat.add_assoc, &[u, v, w]); // (u+v)+w = u+(v+w)
    let v_plus_w = radd(d, v, w);
    let mid1 = radd(d, u, v_plus_w);
    let comm1 = d.lemma(rat.add_comm, &[v, w]); // v+w = w+v
    let w_plus_v = radd(d, w, v);
    let cong = rcongr(d, v_plus_w, w_plus_v, comm1, &|d, t| radd(d, u, t));
    let mid2 = radd(d, u, w_plus_v);
    let assoc2 = d.lemma(rat.add_assoc, &[u, w, v]); // (u+w)+v = u+(w+v)
    let u_plus_w = radd(d, u, w);
    let target = radd(d, u_plus_w, v);
    let step3 = rsymm(d, target, mid2, assoc2);
    let (_, proof) = rchain(d, start, &[(mid1, assoc1), (mid2, cong), (target, step3)]);
    proof
}

/// `Eq Rat (u + ((v+v)+w)) ((u+v)+(v+w))`.
fn regroup3_eq(d: &mut IntDev<'_>, p: CRealPrelude, u: ExprId, v: ExprId, w: ExprId) -> ExprId {
    let rat = p.rat;
    let vv = radd(d, v, v);
    let mid1 = radd(d, u, vv);
    let uv = radd(d, u, v);
    let vv_plus_w = radd(d, vv, w);
    let start = radd(d, u, vv_plus_w);

    let assoc1 = d.lemma(rat.add_assoc, &[u, vv, w]); // (u+vv)+w = u+(vv+w) = start
    let mid1_plus_w = radd(d, mid1, w);
    let step1 = rsymm(d, mid1_plus_w, start, assoc1); // start = mid1+w

    let assoc2 = d.lemma(rat.add_assoc, &[u, v, v]); // (u+v)+v = u+(v+v) = mid1
    let uv_plus_v = radd(d, uv, v);
    let flip2 = rsymm(d, uv_plus_v, mid1, assoc2); // mid1 = (u+v)+v
    let cong_b = rcongr(d, mid1, uv_plus_v, flip2, &|d, t| radd(d, t, w));
    let uv_v_w = radd(d, uv_plus_v, w);

    let assoc3 = d.lemma(rat.add_assoc, &[uv, v, w]); // ((u+v)+v)+w = (u+v)+(v+w)
    let v_plus_w = radd(d, v, w);
    let target = radd(d, uv, v_plus_w);

    let (_, proof) = rchain(
        d,
        start,
        &[(mid1_plus_w, step1), (uv_v_w, cong_b), (target, assoc3)],
    );
    proof
}

/// `Rat.le (natDivSucc 1 idx) target`, given `halve : Eq Rat (natDivSucc 2
/// idx) target`.
fn one_div_succ_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    idx: ExprId,
    target: ExprId,
    halve: ExprId,
) -> ExprId {
    let rat = p.rat;
    let n1 = d.num(1);
    let step = d.lemma(rat.nat_div_succ_le_add_left, &[n1, n1, idx]);
    let from_expr = div_succ(d, p, 2, idx);
    let to_expr = div_succ(d, p, 1, idx);
    rat_eq_rewrite(d, from_expr, target, halve, step, &|d, t| {
        rle(d, rat, to_expr, t)
    })
}

/// The quantity identity [`build_gap_proof`] rewrites through:
/// `Eq Rat ((t1+t3)+(t2+g)) ((a+g)-e)`, with `t1 := a-b`, `t2 := b-c`,
/// `t3 := c-e`.
fn quantity_identity(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    e: ExprId,
    g: ExprId,
) -> ExprId {
    let rat = p.rat;
    let t1 = rsub(d, rat, a, b);
    let t2 = rsub(d, rat, b, c);
    let t3 = rsub(d, rat, c, e);
    let ae = rsub(d, rat, a, e);
    let t1_t2 = radd(d, t1, t2);
    let c1234 = radd(d, t1_t2, t3);

    // telescope : c1234 = a-e
    let step_a = d.lemma(rat.sub_add_sub, &[a, b, c]); // (a-b)+(b-c) = a-c
    let ac = rsub(d, rat, a, c);
    let cong_a = rcongr(d, t1_t2, ac, step_a, &|d, t| radd(d, t, t3));
    let ac_t3 = radd(d, ac, t3);
    let step_b = d.lemma(rat.sub_add_sub, &[a, c, e]); // (a-c)+(c-e) = a-e
    let (_, telescope) = rchain(d, c1234, &[(ac_t3, cong_a), (ae, step_b)]);

    // swap23 : c1234 = (t1+t3)+t2
    let swap23 = regroup_swap_last_two_eq(d, p, t1, t2, t3);
    let t13 = radd(d, t1, t3);
    let mid4 = radd(d, t13, t2);

    let flip = rsymm(d, c1234, mid4, swap23);
    let mid4_eq_ae = rtrans(d, mid4, c1234, ae, flip, telescope);

    // ((t1+t3)+t2)+g = (a+g)-e
    let t2_g = radd(d, t2, g);
    let start = radd(d, t13, t2_g);
    let assoc_y = d.lemma(rat.add_assoc, &[t13, t2, g]); // (t13+t2)+g = t13+(t2+g) = start
    let mid4_g = radd(d, mid4, g);
    let step_y = rsymm(d, mid4_g, start, assoc_y); // start = mid4+g
    let cong_x = rcongr(d, mid4, ae, mid4_eq_ae, &|d, t| radd(d, t, g)); // mid4+g = ae+g
    let ae_g = radd(d, ae, g);
    let swap_z = sub_add_swap_eq(d, p, a, e, g); // ae+g = (a+g)-e
    let a_g = radd(d, a, g);
    let target = rsub(d, rat, a_g, e);
    let (_, final_eq) = rchain(
        d,
        start,
        &[(mid4_g, step_y), (ae_g, cong_x), (target, swap_z)],
    );
    final_eq
}

/// `Eq Rat ((R1' + R3) + ((-P)+g)) (2/(m+1))`, where `R1' := 1/(m+1)+1/(N+1)`
/// and `R3 := 1/(N+1)+1/(m+1)` — the pure numeric identity both
/// cotransitivity branches close with, independent of which real is on
/// which side.
fn final_bound_eq(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    m: ExprId,
    big_n: ExprId,
    onn: ExprId,
    g: ExprId,
    p_offset: ExprId,
) -> ExprId {
    let rat = p.rat;
    let om = div_succ(d, p, 1, m);
    let two_m = div_succ(d, p, 2, m);
    let n1 = d.num(1);

    // r1_plus_r3_eq : (om+onn)+(onn+om) = two_m+g
    let r1 = radd(d, om, onn);
    let r3 = radd(d, onn, om);
    let start1 = radd(d, r1, r3);
    let step1 = d.lemma(rat.add_assoc, &[om, onn, r3]); // (om+onn)+r3 = om+(onn+r3)
    let onn_r3 = radd(d, onn, r3);
    let mid1 = radd(d, om, onn_r3);

    let onn_onn = radd(d, onn, onn);
    let assoc_onn = d.lemma(rat.add_assoc, &[onn, onn, om]); // (onn+onn)+om = onn+(onn+om)
    let onn_onn_om = radd(d, onn_onn, om);
    let flip_assoc_onn = rsymm(d, onn_onn_om, onn_r3, assoc_onn); // onn+r3 = (onn+onn)+om
    let cong2 = rcongr(d, onn_r3, onn_onn_om, flip_assoc_onn, &|d, t| {
        radd(d, om, t)
    });
    let mid2 = radd(d, om, onn_onn_om);

    let onn_onn_eq_g = d.lemma(rat.nat_div_succ_add, &[n1, n1, big_n]); // onn+onn = g
    let g_om = radd(d, g, om);
    let cong3 = rcongr(d, onn_onn, g, onn_onn_eq_g, &|d, t| {
        let t_om = radd(d, t, om);
        radd(d, om, t_om)
    });
    let mid3 = radd(d, om, g_om);

    let comm_g_om = d.lemma(rat.add_comm, &[g, om]); // g+om = om+g
    let om_g = radd(d, om, g);
    let cong4 = rcongr(d, g_om, om_g, comm_g_om, &|d, t| radd(d, om, t));
    let mid4 = radd(d, om, om_g);

    let om_om = radd(d, om, om);
    let assoc_om = d.lemma(rat.add_assoc, &[om, om, g]); // (om+om)+g = om+(om+g) = mid4
    let om_om_g = radd(d, om_om, g);
    let flip_assoc_om = rsymm(d, om_om_g, mid4, assoc_om);
    let mid5 = om_om_g;

    let om_om_eq_twom = d.lemma(rat.nat_div_succ_add, &[n1, n1, m]); // om+om = two_m
    let cong5 = rcongr(d, om_om, two_m, om_om_eq_twom, &|d, t| radd(d, t, g));
    let target1 = radd(d, two_m, g);

    let (_, r1_plus_r3_eq) = rchain(
        d,
        start1,
        &[
            (mid1, step1),
            (mid2, cong2),
            (mid3, cong3),
            (mid4, cong4),
            (mid5, flip_assoc_om),
            (target1, cong5),
        ],
    );

    // negp_plus_g_eq_negg : (-p_offset)+g = -g
    let n2 = d.num(2);
    let g_g = radd(d, g, g);
    let gg_eq_p = d.lemma(rat.nat_div_succ_add, &[n2, n2, big_n]); // g+g = p_offset
    let neg_p = rneg(d, p_offset);
    let neg_g = rneg(d, g);
    let flip_gg = rsymm(d, g_g, p_offset, gg_eq_p); // p_offset = g+g
    let neg_gg = rneg(d, g_g);
    let step_a = rcongr(d, p_offset, g_g, flip_gg, &|d, t| rneg(d, t)); // -p_offset = -(g+g)
    let split_neg = d.lemma(rat.neg_add, &[g, g]); // -(g+g) = (-g)+(-g)
    let neg_g_neg_g = radd(d, neg_g, neg_g);
    let (_, neg_p_eq) = rchain(d, neg_p, &[(neg_gg, step_a), (neg_g_neg_g, split_neg)]);

    let start2 = radd(d, neg_p, g);
    let cong6 = rcongr(d, neg_p, neg_g_neg_g, neg_p_eq, &|d, t| radd(d, t, g));
    let mid6 = radd(d, neg_g_neg_g, g);

    let assoc_negg = d.lemma(rat.add_assoc, &[neg_g, neg_g, g]); // (-g+-g)+g = -g+(-g+g)
    let neg_g_plus_g = radd(d, neg_g, g);
    let mid7 = radd(d, neg_g, neg_g_plus_g);

    let cancel = d.lemma(rat.neg_add_cancel, &[g]); // (-g)+g = 0
    let zero = rzero(d, rat);
    let cong7 = rcongr(d, neg_g_plus_g, zero, cancel, &|d, t| radd(d, neg_g, t));
    let mid8 = radd(d, neg_g, zero);
    let trim = d.lemma(rat.add_zero, &[neg_g]); // -g+0 = -g

    let (_, negp_plus_g_eq_negg) = rchain(
        d,
        start2,
        &[
            (mid6, cong6),
            (mid7, assoc_negg),
            (mid8, cong7),
            (neg_g, trim),
        ],
    );

    // combine : (r1+r3) + ((-p_offset)+g) = two_m
    let lhs_full = radd(d, start1, start2);
    let cong8 = rcongr(d, start1, target1, r1_plus_r3_eq, &|d, t| {
        radd(d, t, start2)
    });
    let mid9 = radd(d, target1, start2);
    let cong9 = rcongr(d, start2, neg_g, negp_plus_g_eq_negg, &|d, t| {
        radd(d, target1, t)
    });
    let mid10 = radd(d, target1, neg_g);

    let assoc_final = d.lemma(rat.add_assoc, &[two_m, g, neg_g]); // (two_m+g)+(-g) = two_m+(g+(-g))
    let g_negg = radd(d, g, neg_g);
    let mid11 = radd(d, two_m, g_negg);

    let vanish = d.lemma(rat.add_neg, &[g]); // g+(-g) = 0
    let cong10 = rcongr(d, g_negg, zero, vanish, &|d, t| radd(d, two_m, t));
    let mid12 = radd(d, two_m, zero);
    let trim2 = d.lemma(rat.add_zero, &[two_m]); // two_m+0 = two_m

    let (_, final_eq) = rchain(
        d,
        lhs_full,
        &[
            (mid9, cong8),
            (mid10, cong9),
            (mid11, assoc_final),
            (mid12, cong10),
            (two_m, trim2),
        ],
    );
    final_eq
}

/// The shared per-`m` estimate: given `left` sampled at `shift m` and at
/// `idx1` (with `weaken_mid1 : Rat.le (1/(idx1+1)) onn` supplying the one
/// weakening step [`declare_lt_cotrans`]'s two call sites differ on), and
/// `right` sampled at `big_n` and at `m`, plus `t2_bound : Rat.le
/// ((seq left idx1) - (seq right big_n)) (-p_offset)`, closes
/// `Rat.le ((seq left (shift m)) + g - (seq right m)) (2/(m+1))`.
fn build_gap_proof(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    m: ExprId,
    left: ExprId,
    idx1: ExprId,
    weaken_mid1: ExprId,
    right: ExprId,
    big_n: ExprId,
    t2_bound: ExprId,
    onn: ExprId,
    g: ExprId,
    p_offset: ExprId,
) -> ExprId {
    let rat = p.rat;
    let sm = shift(d, m);
    let left_far = sample(d, p, left, sm);
    let right_near = sample(d, p, right, m);
    let mid1 = sample(d, p, left, idx1);
    let mid2 = sample(d, p, right, big_n);

    let om = div_succ(d, p, 1, m);
    let two_m = div_succ(d, p, 2, m);

    // T1 ≤ R1' := om+onn.
    let t1 = rsub(d, rat, left_far, mid1);
    let reg_left = d.lemma(p.regular, &[left, sm, idx1]);
    let modulus_sm_idx1 = modulus(d, p, sm, idx1);
    let (_, t1_upper) = halves(d, p, t1, modulus_sm_idx1, reg_left);
    let one_sm = div_succ(d, p, 1, sm);
    let one_idx1 = div_succ(d, p, 1, idx1);
    let halve_m = d.lemma(rat.nat_div_succ_halve, &[m]);
    let fact_sm = one_div_succ_le(d, p, sm, om, halve_m);
    let r1 = radd(d, om, onn);
    let r1_bound = d.lemma(
        rat.add_le_add,
        &[one_sm, om, one_idx1, onn, fact_sm, weaken_mid1],
    );
    let t1_le_r1 = d.lemma(rat.le_trans, &[t1, modulus_sm_idx1, r1, t1_upper, r1_bound]);

    // T3 ≤ R3 := onn+om — no weakening needed, the indices are already big_n, m.
    let t3 = rsub(d, rat, mid2, right_near);
    let reg_right = d.lemma(p.regular, &[right, big_n, m]);
    let r3 = radd(d, onn, om);
    let (_, t3_le_r3) = halves(d, p, t3, r3, reg_right);

    let t13 = d.lemma(rat.add_le_add, &[t1, r1, t3, r3, t1_le_r1, t3_le_r3]);

    // (T2+g) ≤ ((-p_offset)+g).
    let t2 = rsub(d, rat, mid1, mid2);
    let neg_p = rneg(d, p_offset);
    let refl_g = d.lemma(rat.le_refl, &[g]);
    let t2g = d.lemma(rat.add_le_add, &[t2, neg_p, g, g, t2_bound, refl_g]);

    let t1_t3 = radd(d, t1, t3);
    let r1_r3 = radd(d, r1, r3);
    let t2_g = radd(d, t2, g);
    let negp_g = radd(d, neg_p, g);
    let combo = d.lemma(rat.add_le_add, &[t1_t3, r1_r3, t2_g, negp_g, t13, t2g]);

    let quantity_eq = quantity_identity(d, p, left_far, mid1, mid2, right_near, g);
    let left_far_g = radd(d, left_far, g);
    let q_target = rsub(d, rat, left_far_g, right_near);
    let combo_lhs = radd(d, t1_t3, t2_g);
    let combo_rhs = radd(d, r1_r3, negp_g);
    let step_q = rat_eq_rewrite(d, combo_lhs, q_target, quantity_eq, combo, &|d, t| {
        rle(d, rat, t, combo_rhs)
    });

    let bound_eq = final_bound_eq(d, p, m, big_n, onn, g, p_offset);
    rat_eq_rewrite(d, combo_rhs, two_m, bound_eq, step_q, &|d, t| {
        rle(d, rat, q_target, t)
    })
}

/// `Rat.lt 0 (natDivSucc 2 big_n)`.
fn positive_two_over(d: &mut IntDev<'_>, p: CRealPrelude, big_n: ExprId) -> ExprId {
    let rat = p.rat;
    let nat_p = rat.int.nat;
    let n1 = d.num(1);
    let refl1 = d.lemma(nat_p.le_refl, &[n1]);
    let one_le_two = d.lemma(nat_p.le_step, &[n1, n1, refl1]); // Nat.le 1 (succ 1) = Nat.le 1 2
    let n2 = d.num(2);
    d.lemma(rat.nat_div_succ_pos, &[n2, big_n, one_le_two])
}

/// `And (Rat.lt 0 g) bound`, packaged.
fn and_intro_positive(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    g: ExprId,
    bound_ty: ExprId,
    positive: ExprId,
    bound_proof: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero = rzero(d, rat);
    let positive_ty = rlt(d, rat, zero, g);
    and_intro(d, p, positive_ty, bound_ty, positive, bound_proof)
}

/// The `pivot ≤ seq z big_n` branch: produces `lt x z` at gap `g`.
fn cotrans_left_branch(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    b: ExprId,
    c: ExprId,
    onn: ExprId,
    g: ExprId,
    p_offset: ExprId,
    big_n: ExprId,
    h_left: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = d.nat_ty();
    let t2_bound = le_sub_neg_of_le_add(d, p, b, c, p_offset, h_left);
    let a_idx = shift(d, big_n);

    let le_proof = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let halve_n = d.lemma(rat.nat_div_succ_halve, &[big_n]);
        let weaken_mid1 = one_div_succ_le(d, p, a_idx, onn, halve_n);
        let body = build_gap_proof(
            d,
            p,
            m,
            x,
            a_idx,
            weaken_mid1,
            z,
            big_n,
            t2_bound,
            onn,
            g,
            p_offset,
        );
        d.lam_fv(m_fv, nat, body)
    };

    let positive_g = positive_two_over(d, p, big_n);
    let embedded = embed(d, p, g);
    let shifted = cadd(d, p, x, embedded);
    let bounded = cle(d, p, shifted, z);
    let pair = and_intro_positive(d, p, g, bounded, positive_g, le_proof);
    let lt_x_z = gap_intro(d, p, x, z, g, pair);

    let lxz = clt(d, p, x, z);
    let lzy = clt(d, p, z, y);
    d.or_inl(lxz, lzy, lt_x_z)
}

/// The `seq z big_n < pivot` branch: produces `lt z y` at gap `g`.
fn cotrans_right_branch(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    q: ExprId,
    holds: ExprId,
    b: ExprId,
    c: ExprId,
    onn: ExprId,
    g: ExprId,
    p_offset: ExprId,
    big_n: ExprId,
    lt_b10_q: ExprId,
    h_right: ExprId,
) -> ExprId {
    let rat = p.rat;
    let nat = d.nat_ty();

    let b_plus_p = radd(d, b, p_offset);
    let hb_le = d.lemma(rat.le_of_lt, &[c, b_plus_p, h_right]);
    let y_n = sample(d, p, y, big_n);
    let holds_at_n = d.apply(holds, &[big_n]); // Rat.le ((b+q)-y_n) g
    let b_plus_q = radd(d, b, q);
    let hh = d.lemma(rat.le_of_sub_le, &[b_plus_q, y_n, g, holds_at_n]); // Rat.le (b+q) (y_n+g)

    let refl_q = d.lemma(rat.le_refl, &[q]);
    let c_plus_q = radd(d, c, q);
    let step1 = d.lemma(rat.add_le_add, &[c, b_plus_p, q, q, hb_le, refl_q]);
    let b_plus_p_q = radd(d, b_plus_p, q);
    let b_q_p = radd(d, b_plus_q, p_offset);
    let regroup1 = regroup_swap_last_two_eq(d, p, b, p_offset, q); // (b+p_offset)+q = (b+q)+p_offset
    let step1p = rat_eq_rewrite(d, b_plus_p_q, b_q_p, regroup1, step1, &|d, t| {
        rle(d, rat, c_plus_q, t)
    });

    let refl_p = d.lemma(rat.le_refl, &[p_offset]);
    let y_n_g = radd(d, y_n, g);
    let y_n_g_p = radd(d, y_n_g, p_offset);
    let step2 = d.lemma(
        rat.add_le_add,
        &[b_plus_q, y_n_g, p_offset, p_offset, hh, refl_p],
    );

    let mid = d.lemma(rat.le_trans, &[c_plus_q, b_q_p, y_n_g_p, step1p, step2]);

    let g_p = radd(d, g, p_offset);
    let p_g = radd(d, p_offset, g);
    let y_n_gp = radd(d, y_n, g_p);
    let y_n_pg = radd(d, y_n, p_g);
    let assoc_r2 = d.lemma(rat.add_assoc, &[y_n, g, p_offset]); // (y_n+g)+p_offset = y_n+(g+p_offset)
    let comm_r2 = d.lemma(rat.add_comm, &[g, p_offset]); // g+p_offset = p_offset+g
    let cong_r2 = rcongr(d, g_p, p_g, comm_r2, &|d, t| radd(d, y_n, t));
    let (_, regroup2) = rchain(d, y_n_g_p, &[(y_n_gp, assoc_r2), (y_n_pg, cong_r2)]);
    let mid_p = rat_eq_rewrite(d, y_n_g_p, y_n_pg, regroup2, mid, &|d, t| {
        rle(d, rat, c_plus_q, t)
    }); // Rat.le (c+q) (y_n+(p_offset+g))

    let ten_over = div_succ(d, p, 10, big_n);
    let hq_le = d.lemma(rat.le_of_lt, &[ten_over, q, lt_b10_q]);

    let p_p = radd(d, p_offset, p_offset);
    let n4 = d.num(4);
    let pp_eq_eight = d.lemma(rat.nat_div_succ_add, &[n4, n4, big_n]); // p_offset+p_offset = 8/(N+1)
    let n8 = d.num(8);
    let n2 = d.num(2);
    let eight_over = div_succ(d, p, 8, big_n);
    let eight_g_eq_ten = d.lemma(rat.nat_div_succ_add, &[n8, n2, big_n]); // 8/(N+1)+g = 10/(N+1)
    let eight_g = radd(d, eight_over, g);
    let cong_b10 = rcongr(d, p_p, eight_over, pp_eq_eight, &|d, t| radd(d, t, g));
    let p_p_g = radd(d, p_p, g);
    let (_, eq_b10) = rchain(d, p_p_g, &[(eight_g, cong_b10), (ten_over, eight_g_eq_ten)]);
    // eq_b10 : (p_offset+p_offset)+g = 10/(N+1)

    let flip_b10 = rsymm(d, p_p_g, ten_over, eq_b10);
    let hq2 = rat_eq_rewrite(d, ten_over, p_p_g, flip_b10, hq_le, &|d, t| {
        rle(d, rat, t, q)
    });
    // hq2 : Rat.le ((p_offset+p_offset)+g) q

    let refl_c = d.lemma(rat.le_refl, &[c]);
    let c_ppg = radd(d, c, p_p_g);
    let step_ = d.lemma(rat.add_le_add, &[c, c, p_p_g, q, refl_c, hq2]);

    let c_p = radd(d, c, p_offset);
    let c_p_p_g = radd(d, c_p, p_g);
    let regroup3 = regroup3_eq(d, p, c, p_offset, g); // c+((p_offset+p_offset)+g) = (c+p_offset)+(p_offset+g)
    let step_p = rat_eq_rewrite(d, c_ppg, c_p_p_g, regroup3, step_, &|d, t| {
        rle(d, rat, t, c_plus_q)
    });

    let chained = d.lemma(rat.le_trans, &[c_p_p_g, c_plus_q, y_n_pg, step_p, mid_p]);

    let final2 = cancel_add_right(d, p, c_p, y_n, p_g, chained); // Rat.le (c+p_offset) y_n

    let t2_bound = le_sub_neg_of_le_add(d, p, c, y_n, p_offset, final2);

    let le_proof = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let weaken_mid1 = d.lemma(rat.le_refl, &[onn]);
        let body = build_gap_proof(
            d,
            p,
            m,
            z,
            big_n,
            weaken_mid1,
            y,
            big_n,
            t2_bound,
            onn,
            g,
            p_offset,
        );
        d.lam_fv(m_fv, nat, body)
    };

    let positive_g = positive_two_over(d, p, big_n);
    let embedded = embed(d, p, g);
    let shifted = cadd(d, p, z, embedded);
    let bounded = cle(d, p, shifted, y);
    let pair = and_intro_positive(d, p, g, bounded, positive_g, le_proof);
    let lt_z_y = gap_intro(d, p, z, y, g, pair);

    let lxz = clt(d, p, x, z);
    let lzy = clt(d, p, z, y);
    d.or_inr(lxz, lzy, lt_z_y)
}

/// The case split at `Rat.le_or_lt (pivot) (seq z big_n)`.
fn cotrans_case_split(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    z: ExprId,
    q: ExprId,
    strict: ExprId,
    holds: ExprId,
) -> ExprId {
    let rat = p.rat;

    let n10 = d.num(10);
    let den_q = den(d, q);
    let big_n = NatOps::mul(d, n10, den_q);
    let lt_b10_q = d.lemma(rat.nat_div_succ_lt_of_pos, &[n10, q, strict]);

    let onn = div_succ(d, p, 1, big_n);
    let g = div_succ(d, p, 2, big_n);
    let p_offset = div_succ(d, p, 4, big_n);

    let a_idx = shift(d, big_n);
    let b = sample(d, p, x, a_idx);
    let c = sample(d, p, z, big_n);

    let pivot = radd(d, b, p_offset);
    let case_split = d.lemma(rat.le_or_lt, &[pivot, c]);

    let lxz = clt(d, p, x, z);
    let lzy = clt(d, p, z, y);
    let target = d.or(lxz, lzy);
    let left_ty = rle(d, rat, pivot, c);
    let right_ty = rlt(d, rat, c, pivot);

    d.or_elim(
        left_ty,
        right_ty,
        target,
        case_split,
        &|d, h_left| cotrans_left_branch(d, p, x, y, z, b, c, onn, g, p_offset, big_n, h_left),
        &|d, h_right| {
            cotrans_right_branch(
                d, p, x, y, z, q, holds, b, c, onn, g, p_offset, big_n, lt_b10_q, h_right,
            )
        },
    )
}

/// `CReal.lt_cotrans : ∀ x y, lt x y → ∀ z, Or (lt x z) (lt z y)`.
fn declare_lt_cotrans(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let rat_carrier = rat_ty(d);
    let zero = rzero(d, rat);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let hyp_ty = clt(d, p, x, y);
    let lxz = clt(d, p, x, z);
    let lzy = clt(d, p, z, y);
    let target = d.or(lxz, lzy);

    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let positive = rlt(d, rat, zero, q);
        let embedded = embed(d, p, q);
        let shifted = cadd(d, p, x, embedded);
        let bounded = cle(d, p, shifted, y);
        let witness_ty = d.and(positive, bounded);
        let w_fv = d.fresh_fvar();
        let w = d.kernel().fvar(w_fv);
        let (strict, holds) = gap_halves(d, p, x, y, q, w);

        let body = cotrans_case_split(d, p, x, y, z, q, strict, holds);

        let with_w = d.lam_fv(w_fv, witness_ty, body);
        d.lam_fv(q_fv, rat_carrier, with_w)
    };
    let body = gap_elim(d, p, x, y, target, h, minor);

    let value = {
        let with_z = d.lam_fv(z_fv, carrier, body);
        let with_h = d.lam_fv(h_fv, hyp_ty, with_z);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let over_z = d.pi_fv(z_fv, carrier, target);
        let after_h = d.arrow(hyp_ty, over_z);
        let with_y = d.pi_fv(y_fv, carrier, after_h);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.lt_cotrans,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.Apart x y`.
fn apart(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.apart, &[x, y])
}

/// `CReal.apart_cotrans : ∀ x y, Apart x y → ∀ z, Or (Apart x z) (Apart z y)`.
///
/// `Apart x y := lt x y ∨ lt y x` (verbatim), so this is
/// [`declare_lt_cotrans`] read off in whichever direction the hypothesis
/// gives — no new estimate.
fn declare_apart_cotrans(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let hyp_ty = apart(d, p, x, y);
    let lt_xy = clt(d, p, x, y);
    let lt_yx = clt(d, p, y, x);

    let lt_xz = clt(d, p, x, z);
    let lt_zx = clt(d, p, z, x);
    let lt_zy = clt(d, p, z, y);
    let lt_yz = clt(d, p, y, z);

    let apart_xz = apart(d, p, x, z);
    let apart_zy = apart(d, p, z, y);
    let target = d.or(apart_xz, apart_zy);

    let body = d.or_elim(
        lt_xy,
        lt_yx,
        target,
        h,
        &|d, hxy| {
            let cot = d.lemma(p.lt_cotrans, &[x, y, hxy, z]); // lt x z ∨ lt z y
            d.or_elim(
                lt_xz,
                lt_zy,
                target,
                cot,
                &|d, hxz| {
                    let proof = d.or_inl(lt_xz, lt_zx, hxz);
                    d.or_inl(apart_xz, apart_zy, proof)
                },
                &|d, hzy| {
                    let proof = d.or_inl(lt_zy, lt_yz, hzy);
                    d.or_inr(apart_xz, apart_zy, proof)
                },
            )
        },
        &|d, hyx| {
            let cot = d.lemma(p.lt_cotrans, &[y, x, hyx, z]); // lt y z ∨ lt z x
            d.or_elim(
                lt_yz,
                lt_zx,
                target,
                cot,
                &|d, hyz| {
                    let proof = d.or_inr(lt_zy, lt_yz, hyz);
                    d.or_inr(apart_xz, apart_zy, proof)
                },
                &|d, hzx| {
                    let proof = d.or_inr(lt_xz, lt_zx, hzx);
                    d.or_inl(apart_xz, apart_zy, proof)
                },
            )
        },
    );

    let value = {
        let with_z = d.lam_fv(z_fv, carrier, body);
        let with_h = d.lam_fv(h_fv, hyp_ty, with_z);
        let with_y = d.lam_fv(y_fv, carrier, with_h);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let over_z = d.pi_fv(z_fv, carrier, target);
        let after_h = d.arrow(hyp_ty, over_z);
        let with_y = d.pi_fv(y_fv, carrier, after_h);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.apart_cotrans,
        uparams: vec![],
        ty,
        value,
    })
}
