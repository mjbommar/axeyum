//! The **multiplicative** half of the ordered-group toolkit, plus the two
//! magnitude facts `CReal.mul` needs before it can exist.
//!
//! [`group`](super::group) built everything an *additive* estimate needs:
//! `bounds_add` (the triangle inequality in the `−b ≤ a ∧ a ≤ b` encoding),
//! `natDivSucc_add`, and the two `natDivSucc` rearrangements Bishop's index
//! shift is paid with. Nothing there multiplies, because nothing before
//! `CReal.mul` did.
//!
//! Bishop's product needs three things this module supplies and `group` does
//! not:
//!
//! 1. **A product form of the triangle inequality.**
//!    [`bounds_mul`](super::RatPrelude::bounds_mul) is `|u| ≤ p → |v| ≤ q →
//!    |u·v| ≤ p·q` in the pair encoding. It is *not* four applications of
//!    monotonicity: with `|a| ≤ b` written as a pair and no `Rat.abs` to case
//!    on, the sign analysis has to happen once, here, on `Rat.le_or_lt` —
//!    which is **proved**, so no step of it is an argument by contradiction.
//!    `¬¬P → P` does not exist in this logic prelude and none of this needs it.
//! 2. **A canonical bound on an arbitrary rational.**
//!    [`bounds_num`](super::RatPrelude::bounds_num) says `|q| ≤ |num q|`,
//!    reading the right-hand side as `Rat.natDivSucc (natAbs (num q)) 0`. This
//!    is what turns `CReal.bound` from a search into a projection: a regular
//!    sequence's zeroth sample is a *rational*, its numerator is an *integer*,
//!    and `Int.natAbs` of that is the ℕ the sampling index is scaled by.
//!    Bishop, and Mathlib after him, reach this bound by extracting a modulus
//!    from an existential `CauSeq`; with the fixed modulus of ADR-0512 there is
//!    nothing to extract — regularity at `n = 0` gives `|x_m| ≤ |x_0| + 2`
//!    outright, and the only genuinely missing piece was the ℕ-valued `K`.
//! 3. **`natDivSucc` under multiplication.**
//!    [`natDivSucc_mul`](super::RatPrelude::nat_div_succ_mul) —
//!    `k/1 · a/(j+1) = k·a/(j+1)` — is what lets a bound scaled by a canonical
//!    magnitude stay a single `natDivSucc` instead of becoming a product whose
//!    projections are opaque. Together with
//!    [`natDivSucc_scale`](super::RatPrelude::nat_div_succ_scale) it is the
//!    whole reason `CReal.mul`'s regularity estimate closes *exactly*, with no
//!    slack and no weakening step.
//!
//! [`natDivSucc_le_one`](super::RatPrelude::nat_div_succ_le_one) is the fourth,
//! smallest piece: `1/(j+1) ≤ 1`. It is the one place `natDivSucc` has to be
//! compared at two different indices, and it is still not antitonicity — it is
//! `natDivSucc_le_add_left` (monotone in the numerator) composed with
//! `natDivSucc_scale` at `m = 0`, so the comparison happens at one denominator.

use super::RatPrelude;
use super::archimedean::mixed_theorem;
use super::group::{rsub, rsum, rsum_append, rsum_perm};
use super::ops::{
    den, den_pos, den_z, nat_eq_to_rat, nat_rewrite_prop, normalize, num, one_le_succ, radd,
    rat_eq_rewrite, rat_theorem, rchain, rcongr, req, rle, rlt, rmul, rneg, rsymm, rzero,
};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, Shape, case_split};
use crate::nat_prelude::NatOps;

/// Admit the multiplicative toolkit.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_product_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_signs(d, p)?;
    declare_bounds_mul(d, p)?;
    declare_nat_div_succ_product(d, p)?;
    declare_magnitude(d, p)
}

// --- signs and the right-hand monotonicity ----------------------------------

/// `mul_neg`, `neg_mul`, `mul_le_mul_of_nonneg_right` and `mul_sub_mul`.
///
/// The first two are one `neg_eq_of_add_eq_zero` and one `mul_comm`; the third
/// is `mul_le_mul_of_nonneg_left` read through `mul_comm`. `mul_sub_mul` is the
/// **algebraic identity the whole product estimate rests on**,
/// `a·b − c·e = a·(b − e) + (a − c)·e`, and it is stated rather than inlined
/// because both `CReal.mul`'s regularity and every law downstream of it split
/// exactly this way.
fn declare_signs(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    // mul_neg : a · (−b) = −(a·b).
    //
    // `neg_eq_of_add_eq_zero` turns this into `a·b + a·(−b) = 0`, which is
    // `left_distrib` backwards onto `a·(b + (−b))` and then `mul_zero`.
    rat_theorem(d, p.mul_neg, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let negated = rneg(d, b);
        let lhs = rmul(d, a, negated);
        let product = rmul(d, a, b);
        let rhs = rneg(d, product);
        let stmt = req(d, lhs, rhs);

        let sum = radd(d, product, lhs);
        let inner = radd(d, b, negated);
        let folded = rmul(d, a, inner);
        let distrib = d.lemma(p.left_distrib, &[a, b, negated]);
        let back = rsymm(d, folded, sum, distrib);
        let zero = rzero(d, p);
        let cancel = d.lemma(p.add_neg, &[b]);
        let collapse = rcongr(d, inner, zero, cancel, &|d, t| rmul(d, a, t));
        let scaled_zero = rmul(d, a, zero);
        let vanish = d.lemma(p.mul_zero, &[a]);
        let (_, chained) = rchain(
            d,
            sum,
            &[(folded, back), (scaled_zero, collapse), (zero, vanish)],
        );
        let forward = d.lemma(p.neg_eq_of_add_eq_zero, &[product, lhs, chained]);
        let proof = rsymm(d, rhs, lhs, forward);
        (stmt, proof)
    })?;

    // neg_mul : (−a) · b = −(a·b) — `mul_neg` through `mul_comm`.
    rat_theorem(d, p.neg_mul, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let negated = rneg(d, a);
        let lhs = rmul(d, negated, b);
        let product = rmul(d, a, b);
        let rhs = rneg(d, product);
        let stmt = req(d, lhs, rhs);

        let swapped = rmul(d, b, negated);
        let commute = d.lemma(p.mul_comm, &[negated, b]);
        let reversed = rmul(d, b, a);
        let pull = d.lemma(p.mul_neg, &[b, a]);
        let negated_reversed = rneg(d, reversed);
        let restore = {
            let inner = d.lemma(p.mul_comm, &[b, a]);
            rcongr(d, reversed, product, inner, &|d, t| rneg(d, t))
        };
        let (_, proof) = rchain(
            d,
            lhs,
            &[(swapped, commute), (negated_reversed, pull), (rhs, restore)],
        );
        (stmt, proof)
    })?;

    // mul_le_mul_of_nonneg_right : 0 ≤ c → a ≤ b → a·c ≤ b·c.
    rat_theorem(d, p.mul_le_mul_of_nonneg_right, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let zero = rzero(d, p);
        let nonneg_ty = rle(d, p, zero, c);
        let order_ty = rle(d, p, a, b);
        let left = rmul(d, a, c);
        let right = rmul(d, b, c);
        let conclusion = rle(d, p, left, right);
        let stmt = {
            let inner = d.arrow(order_ty, conclusion);
            d.arrow(nonneg_ty, inner)
        };

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let scaled_left = rmul(d, c, a);
        let scaled_right = rmul(d, c, b);
        let base = d.lemma(p.mul_le_mul_of_nonneg_left, &[c, a, b, h1, h2]);
        let flip_left = d.lemma(p.mul_comm, &[c, a]);
        let staged = rat_eq_rewrite(d, scaled_left, left, flip_left, base, &|d, t| {
            rle(d, p, t, scaled_right)
        });
        let flip_right = d.lemma(p.mul_comm, &[c, b]);
        let body = rat_eq_rewrite(d, scaled_right, right, flip_right, staged, &|d, t| {
            rle(d, p, left, t)
        });
        let proof = {
            let inner = d.lam_fv(h2_fv, order_ty, body);
            d.lam_fv(h1_fv, nonneg_ty, inner)
        };
        (stmt, proof)
    })?;

    // mul_sub_mul : a·b − c·e = a·(b − e) + (a − c)·e.
    //
    // Read right to left, this is the only way a difference of two products
    // ever becomes two bounded quantities: the first factor of each summand is
    // bounded by a canonical magnitude and the second by a regularity estimate.
    rat_theorem(d, p.mul_sub_mul, 4, &|d, v| {
        let (a, b, c, e) = (v[0], v[1], v[2], v[3]);
        let ab = rmul(d, a, b);
        let ce = rmul(d, c, e);
        let lhs = rsub(d, p, ab, ce);
        let first = {
            let gap = rsub(d, p, b, e);
            rmul(d, a, gap)
        };
        let second = {
            let gap = rsub(d, p, a, c);
            rmul(d, gap, e)
        };
        let rhs = radd(d, first, second);
        let stmt = req(d, lhs, rhs);

        let ae = rmul(d, a, e);
        let neg_ae = rneg(d, ae);
        let neg_ce = rneg(d, ce);
        // `a·(b − e) = a·b + −(a·e)`.
        let first_open = {
            let negated_e = rneg(d, e);
            let split = d.lemma(p.left_distrib, &[a, b, negated_e]);
            let scaled = rmul(d, a, negated_e);
            let opened = radd(d, ab, scaled);
            let pull = d.lemma(p.mul_neg, &[a, e]);
            let target = radd(d, ab, neg_ae);
            let tidy = rcongr(d, scaled, neg_ae, pull, &|d, t| radd(d, ab, t));
            let (_, proof) = rchain(d, first, &[(opened, split), (target, tidy)]);
            proof
        };
        let first_open_target = radd(d, ab, neg_ae);
        // `(a − c)·e = a·e + −(c·e)`.
        let second_open = {
            let negated_c = rneg(d, c);
            let gap = rsub(d, p, a, c);
            let swap = d.lemma(p.mul_comm, &[gap, e]);
            let swapped = rmul(d, e, gap);
            let split = d.lemma(p.left_distrib, &[e, a, negated_c]);
            let ea = rmul(d, e, a);
            let scaled = rmul(d, e, negated_c);
            let opened = radd(d, ea, scaled);
            let head = {
                let inner = d.lemma(p.mul_comm, &[e, a]);
                rcongr(d, ea, ae, inner, &|d, t| radd(d, t, scaled))
            };
            let headed = radd(d, ae, scaled);
            let ec = rmul(d, e, c);
            let neg_ec = rneg(d, ec);
            let tail = {
                let inner = d.lemma(p.mul_neg, &[e, c]);
                rcongr(d, scaled, neg_ec, inner, &|d, t| radd(d, ae, t))
            };
            let tailed = radd(d, ae, neg_ec);
            let flip = {
                let inner = d.lemma(p.mul_comm, &[e, c]);
                let negate = rcongr(d, ec, ce, inner, &|d, t| rneg(d, t));
                rcongr(d, neg_ec, neg_ce, negate, &|d, t| radd(d, ae, t))
            };
            let target = radd(d, ae, neg_ce);
            let (_, proof) = rchain(
                d,
                second,
                &[
                    (swapped, swap),
                    (opened, split),
                    (headed, head),
                    (tailed, tail),
                    (target, flip),
                ],
            );
            proof
        };
        let second_open_target = radd(d, ae, neg_ce);

        let opened_left = rcongr(d, first, first_open_target, first_open, &|d, t| {
            radd(d, t, second)
        });
        let staged = radd(d, first_open_target, second);
        let opened_right = rcongr(d, second, second_open_target, second_open, &|d, t| {
            radd(d, first_open_target, t)
        });
        let opened = radd(d, first_open_target, second_open_target);

        // `(ab + −ae) + (ae + −ce) = ab + (−ce + (−ae + ae)) = ab + −ce`.
        let flat_atoms = [ab, neg_ae, ae, neg_ce];
        let sorted_atoms = [ab, neg_ce, neg_ae, ae];
        let flatten = rsum_append(d, p, &flat_atoms[..2], &flat_atoms[2..]);
        let flat = rsum(d, p, &flat_atoms);
        let permute = rsum_perm(d, p, &flat_atoms, &sorted_atoms);
        let sorted = rsum(d, p, &sorted_atoms);
        let zero = rzero(d, p);
        let cancel = d.lemma(p.neg_add_cancel, &[ae]);
        let inner_sum = radd(d, neg_ae, ae);
        let cancelled = rcongr(d, inner_sum, zero, cancel, &|d, t| {
            let tail = radd(d, neg_ce, t);
            radd(d, ab, tail)
        });
        let padded = {
            let tail = radd(d, neg_ce, zero);
            radd(d, ab, tail)
        };
        let trim = d.lemma(p.add_zero, &[neg_ce]);
        let padding = radd(d, neg_ce, zero);
        let trimmed = rcongr(d, padding, neg_ce, trim, &|d, t| radd(d, ab, t));
        let target = radd(d, ab, neg_ce);
        let (_, backwards) = rchain(
            d,
            rhs,
            &[
                (staged, opened_left),
                (opened, opened_right),
                (flat, flatten),
                (sorted, permute),
                (padded, cancelled),
                (target, trimmed),
            ],
        );
        let proof = rsymm(d, rhs, target, backwards);
        (stmt, proof)
    })
}

// --- the product form of the triangle inequality ----------------------------

/// `|u·v| ≤ p·q` from `|u| ≤ p` and `|v| ≤ q`, in the pair encoding.
///
/// The upper half is a helper rather than a declaration because the lower half
/// **is the upper half at `−u`**: `(−u)·v = −(u·v)`, and `−u` satisfies the
/// same two-sided bound `u` does. Only `0 ≤ p` is needed — the sign of `q` never
/// enters, because the case split is on `v` and both branches multiply by a
/// quantity already known non-negative.
fn mul_upper(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    u: ExprId,
    v: ExprId,
    bu: ExprId,
    bv: ExprId,
    bu_nonneg: ExprId,
    lower_u: ExprId,
    upper_u: ExprId,
    lower_v: ExprId,
    upper_v: ExprId,
) -> ExprId {
    let zero = rzero(d, p);
    let product = rmul(d, u, v);
    let bound = rmul(d, bu, bv);
    let target = rle(d, p, product, bound);
    let nonneg_ty = rle(d, p, zero, v);
    let negative_ty = rlt(d, p, v, zero);
    let split = d.lemma(p.le_or_lt, &[zero, v]);
    d.or_elim(
        nonneg_ty,
        negative_ty,
        target,
        split,
        // `0 ≤ v`: scale `u ≤ bu` by `v`, then `v ≤ bv` by `bu`.
        &|d, hv| {
            let scaled = rmul(d, bu, v);
            let first = d.lemma(p.mul_le_mul_of_nonneg_right, &[u, bu, v, hv, upper_u]);
            let second = d.lemma(
                p.mul_le_mul_of_nonneg_left,
                &[bu, v, bv, bu_nonneg, upper_v],
            );
            d.lemma(p.le_trans, &[product, scaled, bound, first, second])
        },
        // `v < 0`: `u·v = (−u)·(−v)`, and `−u`, `−v` are both bounded the same
        // way with `−v` now non-negative.
        &|d, hv| {
            let negated_v = rneg(d, v);
            let negated_u = rneg(d, u);
            let nonneg_negated = {
                let weak = d.lemma(p.le_of_lt, &[v, zero, hv]);
                let flipped = d.lemma(p.neg_le_neg, &[v, zero, weak]);
                let negated_zero = rneg(d, zero);
                let collapse = d.lemma(p.neg_zero, &[]);
                rat_eq_rewrite(d, negated_zero, zero, collapse, flipped, &|d, t| {
                    rle(d, p, t, negated_v)
                })
            };
            let upper_negated_u = {
                let negated_bu = rneg(d, bu);
                let flipped = d.lemma(p.neg_le_neg, &[negated_bu, u, lower_u]);
                let doubled = rneg(d, negated_bu);
                let collapse = d.lemma(p.neg_neg, &[bu]);
                rat_eq_rewrite(d, doubled, bu, collapse, flipped, &|d, t| {
                    rle(d, p, negated_u, t)
                })
            };
            let upper_negated_v = {
                let negated_bv = rneg(d, bv);
                let flipped = d.lemma(p.neg_le_neg, &[negated_bv, v, lower_v]);
                let doubled = rneg(d, negated_bv);
                let collapse = d.lemma(p.neg_neg, &[bv]);
                rat_eq_rewrite(d, doubled, bv, collapse, flipped, &|d, t| {
                    rle(d, p, negated_v, t)
                })
            };
            let negated_product = rmul(d, negated_u, negated_v);
            let scaled = rmul(d, bu, negated_v);
            let first = d.lemma(
                p.mul_le_mul_of_nonneg_right,
                &[negated_u, bu, negated_v, nonneg_negated, upper_negated_u],
            );
            let second = d.lemma(
                p.mul_le_mul_of_nonneg_left,
                &[bu, negated_v, bv, bu_nonneg, upper_negated_v],
            );
            let chained = d.lemma(p.le_trans, &[negated_product, scaled, bound, first, second]);
            // `(−u)·(−v) = −(u·(−v)) = −(−(u·v)) = u·v`.
            let inner = rmul(d, u, negated_v);
            let step_one = d.lemma(p.neg_mul, &[u, negated_v]);
            let negated_inner = rneg(d, inner);
            let step_two = {
                let pull = d.lemma(p.mul_neg, &[u, v]);
                let negated_product_term = rneg(d, product);
                rcongr(d, inner, negated_product_term, pull, &|d, t| rneg(d, t))
            };
            let doubled = {
                let once = rneg(d, product);
                rneg(d, once)
            };
            let step_three = d.lemma(p.neg_neg, &[product]);
            let (_, restore) = rchain(
                d,
                negated_product,
                &[
                    (negated_inner, step_one),
                    (doubled, step_two),
                    (product, step_three),
                ],
            );
            rat_eq_rewrite(d, negated_product, product, restore, chained, &|d, t| {
                rle(d, p, t, bound)
            })
        },
    )
}

/// `bounds_mul` and `neg_mul_le_of_bounds`.
fn declare_bounds_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    // bounds_mul : 0 ≤ bu → |u| ≤ bu → |v| ≤ bv → |u·v| ≤ bu·bv.
    rat_theorem(d, p.bounds_mul, 4, &|d, v| {
        let (u, bu, w, bv) = (v[0], v[1], v[2], v[3]);
        let zero = rzero(d, p);
        let negated_bu = rneg(d, bu);
        let negated_bv = rneg(d, bv);
        let nonneg_ty = rle(d, p, zero, bu);
        let lower_u_ty = rle(d, p, negated_bu, u);
        let upper_u_ty = rle(d, p, u, bu);
        let lower_v_ty = rle(d, p, negated_bv, w);
        let upper_v_ty = rle(d, p, w, bv);
        let product = rmul(d, u, w);
        let bound = rmul(d, bu, bv);
        let negated_bound = rneg(d, bound);
        let low = rle(d, p, negated_bound, product);
        let high = rle(d, p, product, bound);
        let conclusion = d.and(low, high);
        let stmt = {
            let after_v = d.arrow(upper_v_ty, conclusion);
            let after_v_low = d.arrow(lower_v_ty, after_v);
            let after_u = d.arrow(upper_u_ty, after_v_low);
            let after_u_low = d.arrow(lower_u_ty, after_u);
            d.arrow(nonneg_ty, after_u_low)
        };

        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let lu_fv = d.fresh_fvar();
        let lu = d.kernel().fvar(lu_fv);
        let uu_fv = d.fresh_fvar();
        let uu = d.kernel().fvar(uu_fv);
        let lv_fv = d.fresh_fvar();
        let lv = d.kernel().fvar(lv_fv);
        let uv_fv = d.fresh_fvar();
        let uv = d.kernel().fvar(uv_fv);

        let upper = mul_upper(d, p, u, w, bu, bv, hn, lu, uu, lv, uv);
        let lower = {
            let negated_u = rneg(d, u);
            // `−u` carries the same two-sided bound, with the halves swapped.
            let lower_negated = d.lemma(p.neg_le_neg, &[u, bu, uu]);
            let upper_negated = {
                let flipped = d.lemma(p.neg_le_neg, &[negated_bu, u, lu]);
                let doubled = rneg(d, negated_bu);
                let collapse = d.lemma(p.neg_neg, &[bu]);
                rat_eq_rewrite(d, doubled, bu, collapse, flipped, &|d, t| {
                    rle(d, p, negated_u, t)
                })
            };
            let mirrored = mul_upper(
                d,
                p,
                negated_u,
                w,
                bu,
                bv,
                hn,
                lower_negated,
                upper_negated,
                lv,
                uv,
            );
            // `(−u)·v = −(u·v)`, so the mirrored bound is `−(u·v) ≤ bu·bv`.
            let negated_product = rmul(d, negated_u, w);
            let pull = d.lemma(p.neg_mul, &[u, w]);
            let negated_target = rneg(d, product);
            let moved = rat_eq_rewrite(
                d,
                negated_product,
                negated_target,
                pull,
                mirrored,
                &|d, t| rle(d, p, t, bound),
            );
            let flipped = d.lemma(p.neg_le_neg, &[negated_target, bound, moved]);
            let doubled = rneg(d, negated_target);
            let collapse = d.lemma(p.neg_neg, &[product]);
            rat_eq_rewrite(d, doubled, product, collapse, flipped, &|d, t| {
                rle(d, p, negated_bound, t)
            })
        };
        let paired = {
            let intro = p.int.logic.and_intro;
            d.const_app(intro, &[low, high, lower, upper])
        };
        let proof = {
            let after_uv = d.lam_fv(uv_fv, upper_v_ty, paired);
            let after_lv = d.lam_fv(lv_fv, lower_v_ty, after_uv);
            let after_uu = d.lam_fv(uu_fv, upper_u_ty, after_lv);
            let after_lu = d.lam_fv(lu_fv, lower_u_ty, after_uu);
            d.lam_fv(hn_fv, nonneg_ty, after_lu)
        };
        (stmt, proof)
    })?;

    // neg_mul_le_of_bounds : 0 ≤ e → 0 ≤ b → |u| ≤ b → −e ≤ v → v ≤ b →
    //                        −(e·b) ≤ u·v.
    //
    // The **one-sided** product estimate, and the reason `CReal.mul_nonneg` is
    // provable at all: `0 ≤ x` over the reals does not say any sample is
    // non-negative, only that each is bounded below by `−2/(n+1)`. A lower
    // bound on the product therefore has to trade that off against the *other*
    // factor's canonical magnitude, which is exactly what this does — and the
    // resulting `e·b` is one `natDivSucc` once `natDivSucc_mul` fuses it.
    rat_theorem(d, p.neg_mul_le_of_bounds, 4, &|d, args| {
        let (u, v, e, b) = (args[0], args[1], args[2], args[3]);
        let zero = rzero(d, p);
        let negated_b = rneg(d, b);
        let negated_e = rneg(d, e);
        let e_nonneg_ty = rle(d, p, zero, e);
        let b_nonneg_ty = rle(d, p, zero, b);
        let lower_u_ty = rle(d, p, negated_e, u);
        let upper_u_ty = rle(d, p, u, b);
        let lower_v_ty = rle(d, p, negated_e, v);
        let upper_v_ty = rle(d, p, v, b);
        let product = rmul(d, u, v);
        let bound = rmul(d, e, b);
        let negated_bound = rneg(d, bound);
        let conclusion = rle(d, p, negated_bound, product);
        let stmt = {
            let after_uv = d.arrow(upper_v_ty, conclusion);
            let after_lv = d.arrow(lower_v_ty, after_uv);
            let after_uu = d.arrow(upper_u_ty, after_lv);
            let after_lu = d.arrow(lower_u_ty, after_uu);
            let after_b = d.arrow(b_nonneg_ty, after_lu);
            d.arrow(e_nonneg_ty, after_b)
        };

        let he_fv = d.fresh_fvar();
        let he = d.kernel().fvar(he_fv);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);
        let lu_fv = d.fresh_fvar();
        let lu = d.kernel().fvar(lu_fv);
        let uu_fv = d.fresh_fvar();
        let uu = d.kernel().fvar(uu_fv);
        let lv_fv = d.fresh_fvar();
        let lv = d.kernel().fvar(lv_fv);
        let uv_fv = d.fresh_fvar();
        let uv = d.kernel().fvar(uv_fv);

        let nonneg_ty = rle(d, p, zero, v);
        let negative_ty = rlt(d, p, v, zero);
        let split = d.lemma(p.le_or_lt, &[zero, v]);
        let body = d.or_elim(
            nonneg_ty,
            negative_ty,
            conclusion,
            split,
            // `0 ≤ v`: `u·v ≥ (−e)·v = −(e·v) ≥ −(e·b)`.
            &|d, hv| {
                let scaled = rmul(d, negated_e, v);
                let first = d.lemma(p.mul_le_mul_of_nonneg_right, &[negated_e, u, v, hv, lu]);
                let ev = rmul(d, e, v);
                let pull = d.lemma(p.neg_mul, &[e, v]);
                let negated_ev = rneg(d, ev);
                let moved = rat_eq_rewrite(d, scaled, negated_ev, pull, first, &|d, t| {
                    rle(d, p, t, product)
                });
                let grow = d.lemma(p.mul_le_mul_of_nonneg_left, &[e, v, b, he, uv]);
                let shrink = d.lemma(p.neg_le_neg, &[ev, bound, grow]);
                d.lemma(
                    p.le_trans,
                    &[negated_bound, negated_ev, product, shrink, moved],
                )
            },
            // `v < 0`: `u·v = (−u)·(−v) ≥ (−b)·(−v) = −(b·(−v)) ≥ −(b·e)`.
            &|d, hv| {
                let negated_v = rneg(d, v);
                let negated_u = rneg(d, u);
                let nonneg_negated = {
                    let weak = d.lemma(p.le_of_lt, &[v, zero, hv]);
                    let flipped = d.lemma(p.neg_le_neg, &[v, zero, weak]);
                    let negated_zero = rneg(d, zero);
                    let collapse = d.lemma(p.neg_zero, &[]);
                    rat_eq_rewrite(d, negated_zero, zero, collapse, flipped, &|d, t| {
                        rle(d, p, t, negated_v)
                    })
                };
                let negated_upper = d.lemma(p.neg_le_neg, &[u, b, uu]);
                let negated_v_le_e = {
                    let flipped = d.lemma(p.neg_le_neg, &[negated_e, v, lv]);
                    let doubled = rneg(d, negated_e);
                    let collapse = d.lemma(p.neg_neg, &[e]);
                    rat_eq_rewrite(d, doubled, e, collapse, flipped, &|d, t| {
                        rle(d, p, negated_v, t)
                    })
                };
                let lower_scaled = rmul(d, negated_b, negated_v);
                let mirrored = rmul(d, negated_u, negated_v);
                let first = d.lemma(
                    p.mul_le_mul_of_nonneg_right,
                    &[
                        negated_b,
                        negated_u,
                        negated_v,
                        nonneg_negated,
                        negated_upper,
                    ],
                );
                // `(−b)·(−v) = −(b·(−v))`, and `b·(−v) ≤ b·e`.
                let scaled = rmul(d, b, negated_v);
                let pull = d.lemma(p.neg_mul, &[b, negated_v]);
                let negated_scaled = rneg(d, scaled);
                let moved =
                    rat_eq_rewrite(d, lower_scaled, negated_scaled, pull, first, &|d, t| {
                        rle(d, p, t, mirrored)
                    });
                let be = rmul(d, b, e);
                let grow = d.lemma(
                    p.mul_le_mul_of_nonneg_left,
                    &[b, negated_v, e, hb, negated_v_le_e],
                );
                let shrink = d.lemma(p.neg_le_neg, &[scaled, be, grow]);
                let negated_be = rneg(d, be);
                let commuted = {
                    let inner = d.lemma(p.mul_comm, &[b, e]);
                    rcongr(d, be, bound, inner, &|d, t| rneg(d, t))
                };
                let aligned =
                    rat_eq_rewrite(d, negated_be, negated_bound, commuted, shrink, &|d, t| {
                        rle(d, p, t, negated_scaled)
                    });
                let chained = d.lemma(
                    p.le_trans,
                    &[negated_bound, negated_scaled, mirrored, aligned, moved],
                );
                // `(−u)·(−v) = u·v`.
                let inner = rmul(d, u, negated_v);
                let step_one = d.lemma(p.neg_mul, &[u, negated_v]);
                let negated_inner = rneg(d, inner);
                let step_two = {
                    let inner_pull = d.lemma(p.mul_neg, &[u, v]);
                    let negated_product = rneg(d, product);
                    rcongr(d, inner, negated_product, inner_pull, &|d, t| rneg(d, t))
                };
                let doubled = {
                    let once = rneg(d, product);
                    rneg(d, once)
                };
                let step_three = d.lemma(p.neg_neg, &[product]);
                let (_, restore) = rchain(
                    d,
                    mirrored,
                    &[
                        (negated_inner, step_one),
                        (doubled, step_two),
                        (product, step_three),
                    ],
                );
                rat_eq_rewrite(d, mirrored, product, restore, chained, &|d, t| {
                    rle(d, p, negated_bound, t)
                })
            },
        );
        let proof = {
            let after_uv = d.lam_fv(uv_fv, upper_v_ty, body);
            let after_lv = d.lam_fv(lv_fv, lower_v_ty, after_uv);
            let after_uu = d.lam_fv(uu_fv, upper_u_ty, after_lv);
            let after_lu = d.lam_fv(lu_fv, lower_u_ty, after_uu);
            let after_b = d.lam_fv(hb_fv, b_nonneg_ty, after_lu);
            d.lam_fv(he_fv, e_nonneg_ty, after_b)
        };
        (stmt, proof)
    })
}

// --- `natDivSucc` under multiplication --------------------------------------

/// `natDivSucc_mul` and `natDivSucc_le_one`.
fn declare_nat_div_succ_product(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat_ty = d.nat_ty();
    let nat = p.int.nat;

    // natDivSucc_mul : (a/1) · (b/(j+1)) = (a·b)/(j+1).
    //
    // `normalize_mul_normalize` fuses the two into `normalize (a·b) (1·(j+1))`,
    // and the claim reduces to the ℕ identity `1·(j+1) = j+1`. The integer
    // product `ofNat a · ofNat b` IS `ofNat (a·b)` definitionally, so no
    // `Int` lemma appears at all.
    mixed_theorem(d, p.nat_div_succ_mul, &[nat_ty, nat_ty, nat_ty], &|d, v| {
        let (a, b, j) = (v[0], v[1], v[2]);
        let zero_nat = d.num(0);
        let left = d.const_app(p.nat_div_succ, &[a, zero_nat]);
        let right = d.const_app(p.nat_div_succ, &[b, j]);
        let total = rmul(d, left, right);
        let combined = NatOps::mul(d, a, b);
        let target = d.const_app(p.nat_div_succ, &[combined, j]);
        let stmt = req(d, total, target);

        let unit = d.succ(zero_nat);
        let unit_positive = one_le_succ(d, zero_nat);
        let denominator = d.succ(j);
        let positive = one_le_succ(d, j);
        let a_z = d.of_nat(a);
        let b_z = d.of_nat(b);
        let numerator = d.imul(a_z, b_z);
        let product_den = NatOps::mul(d, unit, denominator);
        let product_positive = d.lemma(
            nat.one_le_mul,
            &[unit, denominator, unit_positive, positive],
        );
        let fused = normalize(d, numerator, product_den, product_positive);
        let fuse = d.lemma(
            p.normalize_mul_normalize,
            &[a_z, unit, unit_positive, b_z, denominator, positive],
        );

        // `(a·b) · ofNat (j+1) = (a·b) · ofNat (1·(j+1))`.
        let combined_z = d.of_nat(combined);
        let collapse = d.lemma(nat.one_mul, &[denominator]);
        let back = NatOps::symm(d, product_den, denominator, collapse);
        let cross = d.nat_eq_to_int(denominator, product_den, back, &|d, t| {
            let scale = d.of_nat(t);
            d.imul(combined_z, scale)
        });
        let congr = d.lemma(
            p.normalize_congr,
            &[
                numerator,
                product_den,
                product_positive,
                combined_z,
                denominator,
                positive,
                cross,
            ],
        );
        let (_, proof) = rchain(d, total, &[(fused, fuse), (target, congr)]);
        (stmt, proof)
    })?;

    // nat_index_compose : (a+1)·((b+1)·n + b) + a = (D+1)·n + D, D = (a+1)·b + a.
    //
    // **Bishop's sampling indices are closed under composition, and this is the
    // ℕ identity that says so.** `CReal.mul` samples at `(c+1)·n + c` and
    // `CReal.add` at `2n+1`, which IS `(1+1)·n + 1`; every nested product —
    // `mul (mul x y) z`, `mul x (add y z)` — therefore samples at an index of
    // the same shape, and [`Self::nat_div_succ_le_scaled`] applies to it
    // unchanged. Without this each nesting would need its own ad-hoc index
    // arithmetic.
    mixed_theorem(
        d,
        p.nat_index_compose,
        &[nat_ty, nat_ty, nat_ty],
        &|d, v| {
            let (a, b, n) = (v[0], v[1], v[2]);
            let sa = d.succ(a);
            let sb = d.succ(b);
            let inner = {
                let scaled = NatOps::mul(d, sb, n);
                NatOps::add(d, scaled, b)
            };
            let outer = NatOps::mul(d, sa, inner);
            let start = NatOps::add(d, outer, a);
            let composed = {
                let scaled = NatOps::mul(d, sa, b);
                NatOps::add(d, scaled, a)
            };
            let target = {
                let factor = d.succ(composed);
                let scaled = NatOps::mul(d, factor, n);
                NatOps::add(d, scaled, composed)
            };
            let stmt = d.eq(start, target);

            let deep = NatOps::mul(d, sb, n);
            let head = NatOps::mul(d, sa, deep);
            let side = NatOps::mul(d, sa, b);
            let opened_inner = NatOps::add(d, head, side);
            let distrib = d.lemma(nat.left_distrib, &[sa, deep, b]);
            let opened = NatOps::add(d, opened_inner, a);
            let step_open = NatOps::congr(d, outer, opened_inner, distrib, &|d, t| {
                NatOps::add(d, t, a)
            });
            let regrouped = NatOps::add(d, head, composed);
            let step_assoc = d.lemma(nat.add_assoc, &[head, side, a]);
            let flat_head = NatOps::mul(d, sa, sb);
            let flattened = NatOps::mul(d, flat_head, n);
            let step_flat = {
                let forward = d.lemma(nat.mul_assoc, &[sa, sb, n]);
                let back = NatOps::symm(d, flattened, head, forward);
                NatOps::congr(d, head, flattened, back, &|d, t| {
                    NatOps::add(d, t, composed)
                })
            };
            let staged_flat = NatOps::add(d, flattened, composed);
            // `(a+1)·(b+1) = (a+1)·b + (a+1)`, and `Nat.add ((a+1)·b) (succ a)`
            // IS `succ ((a+1)·b + a)` = `succ D`.
            let successor = d.succ(composed);
            let step_succ = {
                let expand = d.lemma(nat.mul_succ, &[sa, b]);
                NatOps::congr(d, flat_head, successor, expand, &|d, t| {
                    let scaled = NatOps::mul(d, t, n);
                    NatOps::add(d, scaled, composed)
                })
            };
            let (_, proof) = NatOps::chain(
                d,
                start,
                &[
                    (opened, step_open),
                    (regrouped, step_assoc),
                    (staged_flat, step_flat),
                    (target, step_succ),
                ],
            );
            (stmt, proof)
        },
    )?;

    // nat_index_symm : (a+1)·b + a = (b+1)·a + b.
    //
    // **Bishop's sampling index is symmetric in its shift and its argument**,
    // and that is not decoration. `natDivSucc_le_scaled` reads a bound at
    // `(c+1)·n + c` back to `n` — the SECOND slot — because that is the slot
    // that shrinks. The real inverse needs the other reading: its samples are
    // bounded BELOW by a constant fixed by the modulus, so the same index has
    // to come back to the shift, and the only way there without a new lemma
    // about `natDivSucc` is to notice the index is already the right shape
    // with its arguments swapped.
    //
    // Degree 2 in the two variables and still not an induction: `succ_mul`
    // opens both sides to `a·b + b + a`, and `add_right_comm` and `mul_comm`
    // close the gap.
    mixed_theorem(d, p.nat_index_symm, &[nat_ty, nat_ty], &|d, v| {
        let (a, b) = (v[0], v[1]);
        let sa = d.succ(a);
        let sb = d.succ(b);
        let start = {
            let scaled = NatOps::mul(d, sa, b);
            NatOps::add(d, scaled, a)
        };
        let target = {
            let scaled = NatOps::mul(d, sb, a);
            NatOps::add(d, scaled, b)
        };
        let stmt = d.eq(start, target);

        let flat = NatOps::mul(d, a, b);
        let opened_head = NatOps::add(d, flat, b);
        let opened = NatOps::add(d, opened_head, a);
        let step_open = {
            let expand = d.lemma(nat.succ_mul, &[a, b]);
            let scaled = NatOps::mul(d, sa, b);
            NatOps::congr(d, scaled, opened_head, expand, &|d, t| NatOps::add(d, t, a))
        };
        let swapped_head = NatOps::add(d, flat, a);
        let regrouped = NatOps::add(d, swapped_head, b);
        let step_regroup = d.lemma(nat.add_right_comm, &[flat, b, a]);
        let mirrored = NatOps::mul(d, b, a);
        let mirrored_head = NatOps::add(d, mirrored, a);
        let commuted = NatOps::add(d, mirrored_head, b);
        let step_commute = {
            let swap = d.lemma(nat.mul_comm, &[a, b]);
            NatOps::congr(d, flat, mirrored, swap, &|d, t| {
                let head = NatOps::add(d, t, a);
                NatOps::add(d, head, b)
            })
        };
        let step_close = {
            let expand = d.lemma(nat.succ_mul, &[b, a]);
            let scaled = NatOps::mul(d, sb, a);
            let back = NatOps::symm(d, scaled, mirrored_head, expand);
            NatOps::congr(d, mirrored_head, scaled, back, &|d, t| NatOps::add(d, t, b))
        };
        let (_, proof) = NatOps::chain(
            d,
            start,
            &[
                (opened, step_open),
                (regrouped, step_regroup),
                (commuted, step_commute),
                (target, step_close),
            ],
        );
        (stmt, proof)
    })?;

    // natDivSucc_le_scaled : k/((c+1)·n + c + 1) ≤ k/(n+1).
    //
    // **The general index-comparison lemma, and it is still not antitonicity.**
    // A sampling index of the form `(c+1)·n + c` — Bishop's product index, and
    // every composite of it — is deeper than `n`, and the bound at that depth
    // has to be read back at `n`. `natDivSucc_le_add_left` widens the numerator
    // `k ↦ k·(c+1)` at the SAME index, `natDivSucc_mul` factors it as
    // `k/1 · (c+1)/(index+1)`, and `natDivSucc_scale` reads the second factor
    // as `1/(n+1)`. Three steps, one denominator each, and no ordering of
    // `natDivSucc` in its index is ever used.
    mixed_theorem(
        d,
        p.nat_div_succ_le_scaled,
        &[nat_ty, nat_ty, nat_ty],
        &|d, v| {
            let (k, c, n) = (v[0], v[1], v[2]);
            let factor = d.succ(c);
            let scaled = NatOps::mul(d, factor, n);
            let index = NatOps::add(d, scaled, c);
            let base = d.const_app(p.nat_div_succ, &[k, index]);
            let target = d.const_app(p.nat_div_succ, &[k, n]);
            let stmt = rle(d, p, base, target);

            let extra = NatOps::mul(d, k, c);
            let grown = d.lemma(p.nat_div_succ_le_add_left, &[k, extra, index]);
            let widened_numerator = NatOps::add(d, k, extra);
            let scaled_numerator = NatOps::mul(d, k, factor);
            let numerator_eq = {
                let commute = d.lemma(nat.add_comm, &[k, extra]);
                let mirrored = NatOps::add(d, extra, k);
                let expand = d.lemma(nat.mul_succ, &[k, c]);
                let back = NatOps::symm(d, scaled_numerator, mirrored, expand);
                NatOps::trans(
                    d,
                    widened_numerator,
                    mirrored,
                    scaled_numerator,
                    commute,
                    back,
                )
            };
            let at_scaled = nat_rewrite_prop(
                d,
                widened_numerator,
                scaled_numerator,
                numerator_eq,
                grown,
                &|d, t| {
                    let moved = d.const_app(p.nat_div_succ, &[t, index]);
                    rle(d, p, base, moved)
                },
            );

            let zero_nat = d.num(0);
            let unit_scale = d.const_app(p.nat_div_succ, &[k, zero_nat]);
            let deep = d.const_app(p.nat_div_succ, &[factor, index]);
            let factored = rmul(d, unit_scale, deep);
            let fused = d.const_app(p.nat_div_succ, &[scaled_numerator, index]);
            let fuse = d.lemma(p.nat_div_succ_mul, &[k, factor, index]);
            let split = rsymm(d, factored, fused, fuse);
            let at_factored = rat_eq_rewrite(d, fused, factored, split, at_scaled, &|d, t| {
                rle(d, p, base, t)
            });

            let one_nat = d.num(1);
            let shallow = d.const_app(p.nat_div_succ, &[one_nat, n]);
            let scale = d.lemma(p.nat_div_succ_scale, &[c, n]);
            let rescaled = rcongr(d, deep, shallow, scale, &|d, t| rmul(d, unit_scale, t));
            let inner = rmul(d, unit_scale, shallow);
            let final_fuse = d.lemma(p.nat_div_succ_mul, &[k, one_nat, n]);
            let final_numerator = NatOps::mul(d, k, one_nat);
            let almost = d.const_app(p.nat_div_succ, &[final_numerator, n]);
            let trim = d.lemma(nat.mul_one, &[k]);
            let tidy = nat_eq_to_rat(d, final_numerator, k, trim, &|d, t| {
                d.const_app(p.nat_div_succ, &[t, n])
            });
            let (_, chain) = rchain(
                d,
                factored,
                &[(inner, rescaled), (almost, final_fuse), (target, tidy)],
            );
            let proof = rat_eq_rewrite(d, factored, target, chain, at_factored, &|d, t| {
                rle(d, p, base, t)
            });
            (stmt, proof)
        },
    )?;

    // natDivSucc_le_one : 1/(j+1) ≤ 1/1.
    //
    // Not antitonicity of `natDivSucc` in its index — that lemma still does not
    // exist and is still not needed. `natDivSucc_le_add_left` widens the
    // numerator from `1` to `1 + j` at the same index, and `natDivSucc_scale`
    // at `m = 0` says `(j+1)/(j+1)` IS `1/1`. Both comparisons happen at one
    // denominator.
    mixed_theorem(d, p.nat_div_succ_le_one, &[nat_ty], &|d, v| {
        let j = v[0];
        let one_nat = d.num(1);
        let zero_nat = d.num(0);
        let base = d.const_app(p.nat_div_succ, &[one_nat, j]);
        let unit = d.const_app(p.nat_div_succ, &[one_nat, zero_nat]);
        let stmt = rle(d, p, base, unit);

        let widened_numerator = NatOps::add(d, one_nat, j);
        let widened = d.const_app(p.nat_div_succ, &[widened_numerator, j]);
        let grow = d.lemma(p.nat_div_succ_le_add_left, &[one_nat, j, j]);
        // `1 + j = succ j`, because `Nat.add j 1` IS `succ j`.
        let successor = d.succ(j);
        let commute = d.lemma(nat.add_comm, &[one_nat, j]);
        let at_successor = d.const_app(p.nat_div_succ, &[successor, j]);
        let staged = {
            let motive = NatOps::eq_motive(d, widened_numerator, &|d, t| {
                let moved = d.const_app(p.nat_div_succ, &[t, j]);
                rle(d, p, base, moved)
            });
            NatOps::transport(d, widened_numerator, motive, grow, successor, commute)
        };
        let _ = widened;
        let _ = at_successor;

        // `natDivSucc (succ j) j = natDivSucc (succ j) ((succ j)·0 + j) = 1/1`.
        let shifted = {
            let product = NatOps::mul(d, successor, zero_nat);
            NatOps::add(d, product, j)
        };
        let scale = d.lemma(p.nat_div_succ_scale, &[j, zero_nat]);
        let restore = {
            let collapse = d.lemma(nat.zero_add, &[j]);
            NatOps::symm(d, shifted, j, collapse)
        };
        let at_shifted = d.const_app(p.nat_div_succ, &[successor, shifted]);
        let moved = {
            let motive = NatOps::eq_motive(d, j, &|d, t| {
                let index = d.const_app(p.nat_div_succ, &[successor, t]);
                rle(d, p, base, index)
            });
            NatOps::transport(d, j, motive, staged, shifted, restore)
        };
        let proof = rat_eq_rewrite(d, at_shifted, unit, scale, moved, &|d, t| {
            rle(d, p, base, t)
        });
        (stmt, proof)
    })
}

// --- the canonical magnitude of a rational ----------------------------------

/// The two `Int` magnitude facts and the `ℚ` bound they carry.
fn declare_magnitude(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let nat = p.int.nat;

    // int_le_nat_abs : x ≤ ofNat (natAbs x).
    //
    // Both branches compute. `Int.le (ofNat n) (ofNat n)` reduces to
    // `Nat.le n n`, and `Int.le (negSucc m) (ofNat (succ m))` reduces to
    // `True` — the four-case definition of `Int.le` does all the work.
    d.int_theorem(p.int_le_nat_abs, 1, &|d, v| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let x = args[0];
            let magnitude = d.const_app(int.nat_abs, &[x]);
            let lifted = d.of_nat(magnitude);
            d.ile(x, lifted)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, b| {
            let magnitude = b[0].1;
            match b[0].0 {
                Shape::OfNat => d.lemma(nat.le_refl, &[magnitude]),
                Shape::NegSucc => d.true_intro(),
            }
        });
        (stmt, proof)
    })?;

    // int_neg_nat_abs_le : −ofNat (natAbs x) ≤ x.
    //
    // `Int.neg (ofNat n)` is `Int.negOfNat n`, which is a `Nat.rec` and so does
    // **not** reduce on a variable — the same trap `nat_abs_neg_of_nat`
    // documents. A case split on the natural fixes it: `negOfNat 0` is
    // `ofNat 0` and `negOfNat (succ i)` is `negSucc i`.
    d.int_theorem(p.int_neg_nat_abs_le, 1, &|d, v| {
        let statement = |d: &mut IntDev<'_>, args: &[ExprId]| {
            let x = args[0];
            let magnitude = d.const_app(int.nat_abs, &[x]);
            let lifted = d.of_nat(magnitude);
            let negated = d.ineg(lifted);
            d.ile(negated, x)
        };
        let stmt = statement(d, v);
        let proof = case_split(d, v, &statement, &|d, b| {
            let magnitude = b[0].1;
            match b[0].0 {
                Shape::OfNat => {
                    let claim = |d: &mut IntDev<'_>, x: ExprId| {
                        let value = d.of_nat(x);
                        let inner = d.const_app(int.nat_abs, &[value]);
                        let lifted = d.of_nat(inner);
                        let negated = d.ineg(lifted);
                        d.ile(negated, value)
                    };
                    let at_zero = |d: &mut IntDev<'_>| {
                        let zero_nat = d.zero();
                        d.lemma(nat.le_refl, &[zero_nat])
                    };
                    let at_succ = |d: &mut IntDev<'_>, _i: ExprId, _ih: ExprId| d.true_intro();
                    d.induct(&claim, &at_zero, &at_succ, magnitude)
                }
                // `natAbs (negSucc m)` is `succ m`, `neg (ofNat (succ m))` is
                // `negSucc m`, and `Int.le (negSucc m) (negSucc m)` reduces to
                // `Nat.le m m`.
                Shape::NegSucc => d.lemma(nat.le_refl, &[magnitude]),
            }
        });
        (stmt, proof)
    })?;

    // bounds_num : |q| ≤ natDivSucc (natAbs (num q)) 0.
    //
    // The magnitude of a rational, as a natural, without a `Rat.abs` and
    // without a search. Cross-multiplying, `q ≤ N/1` is
    // `num q · den (N/1) ≤ num (N/1) · den q`, and `normalize_cross` says
    // `num (N/1) = N · den (N/1)`; cancelling the common `den (N/1)` leaves
    // `num q ≤ N · den q`, which is `int_le_nat_abs` widened by the positive
    // denominator.
    rat_theorem(d, p.bounds_num, 1, &|d, v| {
        let q = v[0];
        let numerator = num(d, q);
        let magnitude = d.const_app(int.nat_abs, &[numerator]);
        let zero_nat = d.num(0);
        let bound = d.const_app(p.nat_div_succ, &[magnitude, zero_nat]);
        let negated_bound = rneg(d, bound);
        let low = rle(d, p, negated_bound, q);
        let high = rle(d, p, q, bound);
        let stmt = d.and(low, high);

        let upper = le_nat_abs(d, p, q);
        let lower = {
            let negated_q = rneg(d, q);
            let mirrored = le_nat_abs(d, p, negated_q);
            // `natAbs (num (−q))` IS `natAbs (−(num q))`, which `nat_abs_neg`
            // says is `natAbs (num q)`.
            let negated_numerator = num(d, negated_q);
            let negated_magnitude = d.const_app(int.nat_abs, &[negated_numerator]);
            let preserved = d.lemma(int.nat_abs_neg, &[numerator]);
            let mirrored_bound = d.const_app(p.nat_div_succ, &[negated_magnitude, zero_nat]);
            let aligned = {
                let motive = NatOps::eq_motive(d, negated_magnitude, &|d, t| {
                    let index = d.const_app(p.nat_div_succ, &[t, zero_nat]);
                    rle(d, p, negated_q, index)
                });
                NatOps::transport(d, negated_magnitude, motive, mirrored, magnitude, preserved)
            };
            let _ = mirrored_bound;
            let flipped = d.lemma(p.neg_le_neg, &[negated_q, bound, aligned]);
            let doubled = rneg(d, negated_q);
            let collapse = d.lemma(p.neg_neg, &[q]);
            rat_eq_rewrite(d, doubled, q, collapse, flipped, &|d, t| {
                rle(d, p, negated_bound, t)
            })
        };
        let intro = p.int.logic.and_intro;
        let proof = d.const_app(intro, &[low, high, lower, upper]);
        (stmt, proof)
    })
}

/// `q ≤ natDivSucc (natAbs (num q)) 0`, as a proof term.
///
/// A helper and not a declaration because [`declare_magnitude`] needs it twice —
/// once at `q` and once at `−q`, which is what makes the two-sided bound cost
/// nothing beyond `Int.natAbs_neg`.
fn le_nat_abs(d: &mut IntDev<'_>, p: RatPrelude, q: ExprId) -> ExprId {
    let int = p.int;
    let numerator = num(d, q);
    let magnitude = d.const_app(int.nat_abs, &[numerator]);
    let lifted = d.of_nat(magnitude);
    let zero_nat = d.num(0);
    let unit = d.succ(zero_nat);
    let unit_positive = one_le_succ(d, zero_nat);
    let bound = normalize(d, lifted, unit, unit_positive);
    let bound_den = den(d, bound);
    let bound_scale = den_z(d, bound);
    let bound_num = num(d, bound);
    let q_scale = den_z(d, q);

    // `num (N/1) · ofNat 1 = N · ofNat (den (N/1))`, and `mul_one` trims the
    // unit denominator, so `num (N/1)` IS `N · ofNat (den (N/1))`.
    let cross = d.lemma(p.normalize_cross, &[lifted, unit, unit_positive]);
    let widened = d.imul(lifted, bound_scale);
    let numerator_value = {
        let unit_z = d.of_nat(unit);
        let scaled_num = d.imul(bound_num, unit_z);
        let trim = d.lemma(int.mul_one, &[bound_num]);
        let back = d.isymm(scaled_num, bound_num, trim);
        d.itrans(bound_num, scaled_num, widened, back, cross)
    };

    // `num q ≤ N · ofNat (den q)`: the magnitude dominates the numerator, and
    // widening it by a denominator `≥ 1` only helps.
    let scaled = d.imul(lifted, q_scale);
    let core = {
        let reached = d.lemma(p.int_le_nat_abs, &[numerator]);
        let one_z = d.ione();
        let magnitude_nonneg = d.lemma(p.int_zero_le_of_nat, &[magnitude]);
        let den_positive = den_pos(d, q);
        let grown = d.lemma(
            int.mul_le_mul_of_nonneg_left,
            &[lifted, one_z, q_scale, magnitude_nonneg, den_positive],
        );
        let unit_scaled = d.imul(lifted, one_z);
        let unit_trim = d.lemma(int.mul_one, &[lifted]);
        let aligned = d.int_eq_rewrite(unit_scaled, lifted, unit_trim, grown, &|d, t| {
            d.ile(t, scaled)
        });
        d.lemma(int.le_trans, &[numerator, lifted, scaled, reached, aligned])
    };

    // Multiply through by `ofNat (den (N/1))`, which is where the cancelled
    // denominator has to reappear, and rearrange the product.
    let widened_core = d.lemma(
        p.int_mul_le_mul_right,
        &[numerator, scaled, bound_den, core],
    );
    let goal_left = d.imul(numerator, bound_scale);
    let from = d.imul(scaled, bound_scale);
    let regrouped = {
        let inner = d.imul(q_scale, bound_scale);
        d.imul(lifted, inner)
    };
    let regroup = d.lemma(int.mul_assoc, &[lifted, q_scale, bound_scale]);
    let swapped_inner = d.imul(bound_scale, q_scale);
    let swapped = d.imul(lifted, swapped_inner);
    let swap = {
        let inner = d.imul(q_scale, bound_scale);
        let commute = d.lemma(int.mul_comm, &[q_scale, bound_scale]);
        d.icongr(inner, swapped_inner, commute, &|d, t| d.imul(lifted, t))
    };
    let target = d.imul(widened, q_scale);
    let ungroup = {
        let forward = d.lemma(int.mul_assoc, &[lifted, bound_scale, q_scale]);
        d.isymm(target, swapped, forward)
    };
    let (_, rearranged) = d.ichain(
        from,
        &[(regrouped, regroup), (swapped, swap), (target, ungroup)],
    );
    let moved = d.int_eq_rewrite(from, target, rearranged, widened_core, &|d, t| {
        d.ile(goal_left, t)
    });
    let restore = d.isymm(bound_num, widened, numerator_value);
    d.int_eq_rewrite(widened, bound_num, restore, moved, &|d, t| {
        let right = d.imul(t, q_scale);
        d.ile(goal_left, right)
    })
}
