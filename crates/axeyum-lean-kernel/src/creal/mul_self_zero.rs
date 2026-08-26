//! `CReal.eq_zero_of_mul_self_zero : mul x x ~ zero → x ~ zero` (ADR-0512,
//! continued) — closing the gap the prior design pass identified: a purely
//! order-algebraic (`≤`-only) bound on `t` from `t·t ≤ δ` is only ever
//! `t ≤ δ + 1`, which does not shrink as `δ → 0`. The route here uses
//! [`RatPrelude::mul_pos`](crate::RatPrelude::mul_pos) (a genuinely *strict*
//! field lemma) plus a difference-of-squares identity, never a zero-divisor
//! split — so it needs no case analysis on which of two rational factors is
//! zero.
//!
//! ## The rational sandwich lemma
//!
//! [`declare_rat_sq_le`] proves, for **any** two rationals `u, s`:
//!
//! ```text
//! u·u ≤ s·s  →  0 ≤ s  →  u ≤ s.
//! ```
//!
//! The proof is [`RatPrelude::le_or_lt`](crate::RatPrelude::le_or_lt) on
//! `(u, s)`. The `u ≤ s` branch is immediate. In the `s < u` branch, `0 ≤ s`
//! and `s < u` force `0 < u`, hence `0 < u − s` and `0 < u + s`
//! ([`pos_of_lt`]/its mirror below), so
//! [`RatPrelude::mul_pos`](crate::RatPrelude::mul_pos) gives
//! `0 < (u−s)·(u+s)`. The identity `(u−s)·(u+s) = u·u − s·s`
//! ([`diff_of_squares`]) turns that into `s·s < u·u`, which contradicts the
//! hypothesis `u·u ≤ s·s` via `lt_of_lt_of_le` and `lt_irrefl`.
//!
//! [`declare_rat_sq_sandwich`] applies this once to `t` (giving `t ≤ s`) and
//! once to `−t` (giving `−t ≤ s`, i.e. `−s ≤ t` after `neg_le_neg`/`neg_neg`),
//! closing `CReal.Within t s` — the two-sided bound `equiv_of_bounded` already
//! consumes, so the sandwich composes directly with it.
//!
//! ## Closing the gap: `s·s` has no cheap closed form as a `natDivSucc`
//!
//! Turning the sandwich lemma into `eq_zero_of_mul_self_zero` needs, for every
//! target index `n`, a rational instance `t·t ≤ 2/(m+1)` (from `le_of_equiv`
//! read at a *chosen* index `m`) together with `s := natDivSucc 1 n` — and
//! `s·s` has no cheap closed form as a `natDivSucc`, because `Rat.mul`
//! normalises (ADR-0512's reduced-fraction representation) and no lemma in
//! `RatPrelude` multiplies two `natDivSucc`s at independent denominators.
//!
//! [`sq_bound`] closes it by scaling instead of computing: `r :=
//! natDivSucc(n+1,0) = 1/s` is a **whole number**
//! (`Rat.inv_natDivSucc`/`Rat.mul_inv_cancel` give `s·r = Rat.one`, bridged to
//! `natDivSucc 1 0` by [`declare_rat_unit_eq_one`] — `Rat.self_normalize`
//! applied to `Rat.one` itself, no gcd/cross-multiplication reasoning needed),
//! so `r·r` and `natDivSucc(2,m)·(r·r)` **are** single `natDivSucc`s
//! (`nat_div_succ_mul` twice). Choosing `m` so that numerator is `≤ m+1`
//! ([`index_ratio_le_one_at_mul_index`]) makes that product `≤ 1`, and
//! multiplying back through by `s·s` and cancelling the two `s·r` pairs
//! ([`cancel_sr_pairs`]) gives `natDivSucc(2,m) ≤ s·s` directly.
//!
//! `m` is built `mul_index`-shaped (not simply the bound-driving numerator)
//! so that [`super::product::composed_index_le`] — reused from `CReal.mul`'s
//! own regularity proof — relates `1/(m+1)` back to `1/(n+1)`, which
//! [`declare_eq_zero_of_mul_self_zero`] needs to fold the sandwich's `Within t
//! s` back into a bound on `seq x n` via [`super::product::regular_between`]
//! and [`super::product::fuse_at`].

use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::{rsum, rsum_append, rsum_perm};
use crate::rat_prelude::ops::{
    radd, rat_eq_rewrite, rchain, rcongr, rle, rlt, rmul, rneg, rsymm, rzero,
};

use super::product::{cmul, composed_index_le, fuse_at, mul_index, mul_shift, regular_between};
use super::{CRealPrelude, and_intro, creal_ty, equiv, sample, within};

// --- Rat-level algebra helpers ----------------------------------------------

/// From `h : Rat.lt a b`, derive `Rat.lt (Rat.add c a) (Rat.add c b)`.
fn shift_lt(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    c: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let rat = p.rat;
    let refl_c = d.lemma(rat.le_refl, &[c]);
    d.lemma(rat.add_lt_add_of_le_of_lt, &[c, c, a, b, refl_c, h])
}

/// From `h : Rat.lt a b`, derive `Rat.lt Rat.zero (Rat.add b (Rat.neg a))` —
/// `0 < b − a`, in `add`/`neg` form (defeq to `Rat.sub b a`, never
/// constructed: every step here goes through a named ring law, not the
/// representation).
fn pos_of_lt(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let rat = p.rat;
    let neg_a = rneg(d, a);
    let step = shift_lt(d, p, neg_a, a, b, h);
    // step : lt (neg_a + a) (neg_a + b)
    let lhs = radd(d, neg_a, a);
    let zero = rzero(d, rat);
    let cancel_chain = {
        let comm = d.lemma(rat.add_comm, &[neg_a, a]);
        let mirrored = radd(d, a, neg_a);
        let cancel = d.lemma(rat.add_neg, &[a]);
        let (_, e) = rchain(d, lhs, &[(mirrored, comm), (zero, cancel)]);
        e
    };
    let rhs = radd(d, neg_a, b);
    let stepped = rat_eq_rewrite(d, lhs, zero, cancel_chain, step, &|d, t| {
        rlt(d, rat, t, rhs)
    });
    // stepped : lt zero (neg_a + b)
    let comm2 = d.lemma(rat.add_comm, &[neg_a, b]);
    let swapped = radd(d, b, neg_a);
    rat_eq_rewrite(d, rhs, swapped, comm2, stepped, &|d, t| {
        rlt(d, rat, zero, t)
    })
}

/// From `h : Rat.lt Rat.zero (Rat.add x (Rat.neg y))` (i.e. `0 < x − y`),
/// derive `Rat.lt y x`.
fn lt_of_pos_diff(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId, h: ExprId) -> ExprId {
    let rat = p.rat;
    let neg_y = rneg(d, y);
    let diff = radd(d, x, neg_y);
    let zero_x = rzero(d, rat);
    let step = shift_lt(d, p, y, zero_x, diff, h);
    // step : lt (y + 0) (y + diff)
    let lhs = radd(d, y, zero_x);
    let az = d.lemma(rat.add_zero, &[y]);
    let rhs = radd(d, y, diff);
    let stepped = rat_eq_rewrite(d, lhs, y, az, step, &|d, t| rlt(d, rat, t, rhs));
    // stepped : lt y (y + (x + (-y)))

    // y + (x + (-y)) = x, via one permutation of the 3-term sum [y, x, -y].
    let atoms = [y, x, neg_y];
    let flat = rsum(d, rat, &atoms);
    // rsum([y,x,-y]) IS SYNTACTICALLY radd(y, radd(x,-y)) = rhs.
    let perm_order = [x, y, neg_y];
    let perm = rsum_perm(d, rat, &atoms, &perm_order);
    let permed = rsum(d, rat, &perm_order);
    // permed = radd(x, radd(y, -y))
    let inner_cancel = d.lemma(rat.add_neg, &[y]);
    let y_plus_neg_y = radd(d, y, neg_y);
    let zero_y = rzero(d, rat);
    let x_plus_zero = radd(d, x, zero_y);
    let cancel_congr = rcongr(d, y_plus_neg_y, zero_y, inner_cancel, &|d, t| radd(d, x, t));
    let final_eq = d.lemma(rat.add_zero, &[x]);
    let (_, tail) = rchain(
        d,
        flat,
        &[(permed, perm), (x_plus_zero, cancel_congr), (x, final_eq)],
    );
    rat_eq_rewrite(d, rhs, x, tail, stepped, &|d, t| rlt(d, rat, y, t))
}

/// `Eq Rat ((u + (-s)) * (u + s)) ((u*u) + (-(s*s)))` — the
/// difference-of-squares identity, built entirely from named ring laws (never
/// `Rat.sub`, since `Rat.mul` normalises and touching the representation is
/// exactly the friction independent work on `Rat.mul_eq_zero` hit).
///
/// `pub(super)` (not just this module's own [`declare_rat_sq_le`]): `sqrt.rs`'s
/// `declare_mul_self_sqrt` reuses this identity at `(u1, u)` to expand the
/// bracket's width term `u1_sq - u_sq` — the exact reuse this doc comment's
/// own history predicted.
pub(super) fn diff_of_squares(d: &mut IntDev<'_>, p: CRealPrelude, u: ExprId, s: ExprId) -> ExprId {
    let rat = p.rat;
    let neg_s = rneg(d, s);
    let a = radd(d, u, neg_s);
    let b = radd(d, u, s);
    let start = rmul(d, a, b);

    let distrib0 = d.lemma(rat.left_distrib, &[a, u, s]);
    let au = rmul(d, a, u);
    let as_ = rmul(d, a, s);
    let step1 = radd(d, au, as_);

    let uu = rmul(d, u, u);
    let us = rmul(d, u, s);
    let neg_us = rneg(d, us);
    let au_final = radd(d, uu, neg_us);
    let au_chain = {
        let comm = d.lemma(rat.mul_comm, &[a, u]);
        let ua = rmul(d, u, a);
        let dist = d.lemma(rat.left_distrib, &[u, u, neg_s]);
        let u_negs = rmul(d, u, neg_s);
        let opened = radd(d, uu, u_negs);
        let negeq = d.lemma(rat.mul_neg, &[u, s]);
        let closed = rcongr(d, u_negs, neg_us, negeq, &|d, t| radd(d, uu, t));
        let (_, e) = rchain(d, au, &[(ua, comm), (opened, dist), (au_final, closed)]);
        e
    };

    let ss = rmul(d, s, s);
    let neg_ss = rneg(d, ss);
    let su = rmul(d, s, u);
    let as_final = radd(d, su, neg_ss);
    let as_chain = {
        let comm = d.lemma(rat.mul_comm, &[a, s]);
        let sa = rmul(d, s, a);
        let dist = d.lemma(rat.left_distrib, &[s, u, neg_s]);
        let s_negs = rmul(d, s, neg_s);
        let opened = radd(d, su, s_negs);
        let negeq = d.lemma(rat.mul_neg, &[s, s]);
        let closed = rcongr(d, s_negs, neg_ss, negeq, &|d, t| radd(d, su, t));
        let (_, e) = rchain(d, as_, &[(sa, comm), (opened, dist), (as_final, closed)]);
        e
    };

    let step1_final = radd(d, au_final, as_final);
    let step1_eq = {
        let left = rcongr(d, au, au_final, au_chain, &|d, t| radd(d, t, as_));
        let mid = radd(d, au_final, as_);
        let right = rcongr(d, as_, as_final, as_chain, &|d, t| radd(d, au_final, t));
        let (_, e) = rchain(d, step1, &[(mid, left), (step1_final, right)]);
        e
    };

    // (uu + -us) + (su + -ss) = uu + -ss, via one permutation and a
    // cancellation: [uu,-us,su,-ss] -> [uu,-ss,-us,su], split into
    // (uu+-ss) + (-us+su), and -us+su = 0.
    let atoms4 = [uu, neg_us, su, neg_ss];
    let combine = rsum_append(d, rat, &[uu, neg_us], &[su, neg_ss]);
    let flat = rsum(d, rat, &atoms4);
    let perm_order = [uu, neg_ss, neg_us, su];
    let perm = rsum_perm(d, rat, &atoms4, &perm_order);
    let permed = rsum(d, rat, &perm_order);
    let final_target = radd(d, uu, neg_ss);
    let cross = radd(d, neg_us, su);
    let split_form = radd(d, final_target, cross);
    let split = rsum_append(d, rat, &[uu, neg_ss], &[neg_us, su]);
    let split_back = rsymm(d, split_form, permed, split);

    let cross_zero = {
        let comm_su = d.lemma(rat.mul_comm, &[s, u]);
        let su_to_us = rcongr(d, su, us, comm_su, &|d, t| radd(d, neg_us, t));
        let neg_us_plus_us = radd(d, neg_us, us);
        let comm_add = d.lemma(rat.add_comm, &[neg_us, us]);
        let us_plus_neg_us = radd(d, us, neg_us);
        let cancel = d.lemma(rat.add_neg, &[us]);
        let zero = rzero(d, rat);
        let (_, e) = rchain(
            d,
            cross,
            &[
                (neg_us_plus_us, su_to_us),
                (us_plus_neg_us, comm_add),
                (zero, cancel),
            ],
        );
        e
    };
    let zero = rzero(d, rat);
    let zeroed = radd(d, final_target, zero);
    let cross_zero_congr = rcongr(d, cross, zero, cross_zero, &|d, t| radd(d, final_target, t));
    let final_eq = d.lemma(rat.add_zero, &[final_target]);

    let (_, whole) = rchain(
        d,
        start,
        &[
            (step1, distrib0),
            (step1_final, step1_eq),
            (flat, combine),
            (permed, perm),
            (split_form, split_back),
            (zeroed, cross_zero_congr),
            (final_target, final_eq),
        ],
    );
    whole
}

/// `Rat.le (natDivSucc a a) Rat.one`, for **any** Nat `a` — a generalization of
/// `Rat.nat_div_succ_le_one` (which is the numerator-`1` case, arbitrary
/// index) to a numerator matched to its own index. Widen the numerator from
/// `a` to `a+1` at the *same* index `a`
/// ([`RatPrelude::nat_div_succ_le_add_left`](crate::RatPrelude::nat_div_succ_le_add_left)) —
/// `a+1` is `Nat.succ a` definitionally, no commute needed, unlike the `1+j`
/// case `nat_div_succ_le_one` widens — then `natDivSucc (succ a) a` IS `1/1`
/// via [`RatPrelude::nat_div_succ_scale`](crate::RatPrelude::nat_div_succ_scale)
/// at `m = 0` (mirrors its proof exactly, `j := a`).
fn index_ratio_le_one(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let rat = p.rat;
    let nat = rat.int.nat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let base = d.const_app(rat.nat_div_succ, &[a, a]);
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);

    // grow : le base (natDivSucc (a+1) a) -- `a+1` is defeq to `Nat.succ a`.
    let grow = d.lemma(rat.nat_div_succ_le_add_left, &[a, one_nat, a]);
    let successor = d.succ(a);

    // natDivSucc (succ a) (succ(a)*0 + a) = natDivSucc 1 0.
    let shifted = {
        let product = NatOps::mul(d, successor, zero_nat);
        NatOps::add(d, product, a)
    };
    let scale = d.lemma(rat.nat_div_succ_scale, &[a, zero_nat]);
    let restore = {
        let collapse = d.lemma(nat.zero_add, &[a]);
        NatOps::symm(d, shifted, a, collapse)
    };
    let at_shifted = d.const_app(rat.nat_div_succ, &[successor, shifted]);
    let moved = {
        let motive = NatOps::eq_motive(d, a, &|d, t| {
            let index = d.const_app(rat.nat_div_succ, &[successor, t]);
            rle(d, rat, base, index)
        });
        NatOps::transport(d, a, motive, grow, shifted, restore)
    };
    rat_eq_rewrite(d, at_shifted, unit, scale, moved, &|d, t| {
        rle(d, rat, base, t)
    })
}

// --- the sandwich lemma ------------------------------------------------------

/// `CReal.ratSqLe : ∀ u s, Rat.le (u*u) (s*s) → Rat.le Rat.zero s → Rat.le u s`.
///
/// See the module docs for the proof shape.
fn declare_rat_sq_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = crate::rat_prelude::ops::rat_ty(d);

    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);

    let uu = rmul(d, u, u);
    let ss = rmul(d, s, s);
    let h_ty = rle(d, rat, uu, ss);
    let zero_ = rzero(d, rat);
    let hs_ty = rle(d, rat, zero_, s);
    let goal = rle(d, rat, u, s);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let hs_fv = d.fresh_fvar();
    let hs = d.kernel().fvar(hs_fv);

    let case = d.lemma(rat.le_or_lt, &[u, s]);
    let case_left_ty = rle(d, rat, u, s);
    let case_right_ty = rlt(d, rat, s, u);
    let body = d.or_elim(
        case_left_ty,
        case_right_ty,
        goal,
        case,
        &|_d, hyp| hyp,
        &|d, hyp_lt| {
            // hyp_lt : lt s u
            let zero = rzero(d, rat);
            let pos_u = d.lemma(rat.lt_of_le_of_lt, &[zero, s, u, hs, hyp_lt]);
            let diff_pos = pos_of_lt(d, p, s, u, hyp_lt);
            // sum_pos : 0 < u + s
            let sum_pos = {
                let step = d.lemma(rat.add_lt_add_of_le_of_lt, &[zero, s, zero, u, hs, pos_u]);
                // step : lt (0+0) (s+u)
                let lhs = radd(d, zero, zero);
                let az = d.lemma(rat.add_zero, &[zero]);
                let rhs = radd(d, s, u);
                let stepped = rat_eq_rewrite(d, lhs, zero, az, step, &|d, t| rlt(d, rat, t, rhs));
                let comm = d.lemma(rat.add_comm, &[s, u]);
                let swapped = radd(d, u, s);
                rat_eq_rewrite(d, rhs, swapped, comm, stepped, &|d, t| rlt(d, rat, zero, t))
            };
            let neg_s = rneg(d, s);
            let diff = radd(d, u, neg_s);
            let sum = radd(d, u, s);
            let prod_pos = d.lemma(rat.mul_pos, &[diff, sum, diff_pos, sum_pos]);
            // prod_pos : lt 0 (diff * sum)
            let dsq = diff_of_squares(d, p, u, s);
            let neg_ss_ = rneg(d, ss);
            let target = radd(d, uu, neg_ss_);
            let diff_sum = rmul(d, diff, sum);
            let prod_pos2 = rat_eq_rewrite(d, diff_sum, target, dsq, prod_pos, &|d, t| {
                rlt(d, rat, zero, t)
            });
            let sq_gt = lt_of_pos_diff(d, p, uu, ss, prod_pos2);
            // sq_gt : lt ss uu
            let contra = d.lemma(rat.lt_of_lt_of_le, &[ss, uu, ss, sq_gt, h]);
            // contra : lt ss ss
            let irrefl = d.lemma(rat.lt_irrefl, &[ss]);
            let false_proof = d.apply(irrefl, &[contra]);
            d.absurd(goal, false_proof)
        },
    );

    let value = {
        let with_hs = d.lam_fv(hs_fv, hs_ty, body);
        let with_h = d.lam_fv(h_fv, h_ty, with_hs);
        let with_s = d.lam_fv(s_fv, carrier, with_h);
        d.lam_fv(u_fv, carrier, with_s)
    };
    let ty = {
        let inner_arrow = d.arrow(hs_ty, goal);
        let after_h = d.arrow(h_ty, inner_arrow);
        let with_s = d.pi_fv(s_fv, carrier, after_h);
        d.pi_fv(u_fv, carrier, with_s)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.rat_sq_le,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.ratSqSandwich : ∀ t s, Rat.le (t*t) (s*s) → Rat.le Rat.zero s →
/// CReal.Within t s`.
fn declare_rat_sq_sandwich(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = crate::rat_prelude::ops::rat_ty(d);

    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);

    let tt = rmul(d, t, t);
    let ss = rmul(d, s, s);
    let h_ty = rle(d, rat, tt, ss);
    let zero_ = rzero(d, rat);
    let hs_ty = rle(d, rat, zero_, s);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let hs_fv = d.fresh_fvar();
    let hs = d.kernel().fvar(hs_fv);

    // Upper half: t <= s, directly.
    let upper = d.lemma(p.rat_sq_le, &[t, s, h, hs]);

    // Lower half: -t <= s, via rat_sq_le at (-t), then neg_le_neg/neg_neg.
    let neg_t = rneg(d, t);
    let neg_t_sq = rmul(d, neg_t, neg_t);
    let neg_sq_eq = {
        // (-t)*(-t) = -(t*(-t)) = -(-(t*t)) = t*t
        let step1 = d.lemma(rat.neg_mul, &[t, neg_t]);
        // step1 : (-t)*(-t) = -(t*(-t))
        let inner = rmul(d, t, neg_t);
        let neg_inner = rneg(d, inner);
        let step2 = d.lemma(rat.mul_neg, &[t, t]);
        // step2 : t*(-t) = -(t*t)
        let neg_tt = rneg(d, tt);
        let doubled = rneg(d, neg_tt);
        let congr2 = rcongr(d, inner, neg_tt, step2, &|d, x| rneg(d, x));
        let step3 = d.lemma(rat.neg_neg, &[tt]);
        let (_, e) = rchain(
            d,
            neg_t_sq,
            &[(neg_inner, step1), (doubled, congr2), (tt, step3)],
        );
        e
    };
    // `h : le tt ss` rewritten backward along `neg_sq_eq : neg_t_sq = tt`
    // gives `le neg_t_sq ss`.
    let neg_sq_eq_back = rsymm(d, neg_t_sq, tt, neg_sq_eq);
    let h_for_neg = rat_eq_rewrite(d, tt, neg_t_sq, neg_sq_eq_back, h, &|d, t2| {
        rle(d, rat, t2, ss)
    });
    let neg_upper = d.lemma(p.rat_sq_le, &[neg_t, s, h_for_neg, hs]);
    // neg_upper : le (-t) s
    let flipped = d.lemma(rat.neg_le_neg, &[neg_t, s, neg_upper]);
    // flipped : le (-s) (-(-t))
    let double_neg = d.lemma(rat.neg_neg, &[t]);
    let neg_s = rneg(d, s);
    let neg_neg_t = rneg(d, neg_t);
    let lower = rat_eq_rewrite(d, neg_neg_t, t, double_neg, flipped, &|d, t2| {
        rle(d, rat, neg_s, t2)
    });

    let lower_ty = rle(d, rat, neg_s, t);
    let upper_ty = rle(d, rat, t, s);
    let body = and_intro(d, p, lower_ty, upper_ty, lower, upper);

    let value = {
        let with_hs = d.lam_fv(hs_fv, hs_ty, body);
        let with_h = d.lam_fv(h_fv, h_ty, with_hs);
        let with_s = d.lam_fv(s_fv, carrier, with_h);
        d.lam_fv(t_fv, carrier, with_s)
    };
    let ty = {
        let conclusion = within(d, p, t, s);
        let inner_arrow = d.arrow(hs_ty, conclusion);
        let after_h = d.arrow(h_ty, inner_arrow);
        let with_s = d.pi_fv(s_fv, carrier, after_h);
        d.pi_fv(t_fv, carrier, with_s)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.rat_sq_sandwich,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.ratSqLe` and `CReal.ratSqSandwich`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
/// `CReal.ratIndexRatioLeOne : ∀ a, Rat.le (natDivSucc a a) Rat.one`.
fn declare_rat_index_ratio_le_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let base = d.const_app(rat.nat_div_succ, &[a, a]);
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let stmt = rle(d, rat, base, unit);
    let proof = index_ratio_le_one(d, p, a);
    let value = d.lam_fv(a_fv, nat, proof);
    let ty = d.pi_fv(a_fv, nat, stmt);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.rat_index_ratio_le_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `CReal.ratUnitEqOne : Eq Rat (natDivSucc 1 0) Rat.one`.
///
/// `Rat.self_normalize` applied to `Rat.one` itself: `num`/`den` are
/// structure projections of `Rat.one`'s direct `Rat.mk`, so they reduce to
/// exactly `natDivSucc`'s own inputs, and `normalize`'s `1 ≤ den` argument is
/// proof-irrelevant — no gcd/cross-multiplication reasoning needed.
fn declare_rat_unit_eq_one(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let one_val = crate::rat_prelude::ops::rone(d, rat);
    let stmt = crate::rat_prelude::ops::req(d, unit, one_val);
    let proof = d.lemma(rat.self_normalize, &[one_val]);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.rat_unit_eq_one,
        uparams: vec![],
        ty: stmt,
        value: proof,
    })
}

/// `Eq Rat (Rat.mul Rat.one x) x`.
fn rat_one_mul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let rat = p.rat;
    let one_val = crate::rat_prelude::ops::rone(d, rat);
    let comm = d.lemma(rat.mul_comm, &[one_val, x]);
    let x_one = rmul(d, x, one_val);
    let mo = d.lemma(rat.mul_one, &[x]);
    let one_x = rmul(d, one_val, x);
    let (_, e) = rchain(d, one_x, &[(x_one, comm), (x, mo)]);
    e
}

/// `Eq Rat (Rat.mul (Rat.mul s s) (Rat.mul (Rat.mul r r) dd)) dd`, given
/// `sr1 : Eq Rat (Rat.mul s r) Rat.one` — cancel the two `s·r` pairs out of
/// the five-factor product `(s·s)·((r·r)·dd)`, in the order
/// `s·(s·((r·r)·dd)) -> s·(s·(r·(r·dd))) -> s·((s·r)·(r·dd)) ->
/// s·(1·(r·dd)) -> s·(r·dd) -> (s·r)·dd -> 1·dd -> dd`.
fn cancel_sr_pairs(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    s: ExprId,
    r: ExprId,
    dd: ExprId,
    sr1: ExprId,
) -> ExprId {
    let rat = p.rat;
    let one_val = crate::rat_prelude::ops::rone(d, rat);
    let rr = rmul(d, r, r);
    let rr_d = rmul(d, rr, dd); // (r*r)*dd, LEFT-associated -- matches `sq_bound`.
    let ss = rmul(d, s, s);
    let e0 = rmul(d, ss, rr_d);

    // E0 -> E1 : (s*s)*((r*r)*dd) = s*(s*((r*r)*dd))
    let assoc_01 = d.lemma(rat.mul_assoc, &[s, s, rr_d]);
    let s_rrd_left = rmul(d, s, rr_d);
    let e1 = rmul(d, s, s_rrd_left);

    // E1 -> E2 : (r*r)*dd -> r*(r*dd), inside the double `s*` wrapper.
    let assoc_rrd = d.lemma(rat.mul_assoc, &[r, r, dd]);
    // assoc_rrd : (r*r)*dd = r*(r*dd)
    let rd = rmul(d, r, dd);
    let r_rd = rmul(d, r, rd);
    let step_12 = rcongr(d, rr_d, r_rd, assoc_rrd, &|d, t| {
        let inner = rmul(d, s, t);
        rmul(d, s, inner)
    });
    let s_rrd_right = rmul(d, s, r_rd);
    let e2 = rmul(d, s, s_rrd_right);

    // E2 -> E3 : s*(r*(r*dd)) -> (s*r)*(r*dd), inside the outer `s*`.
    let assoc_sr = d.lemma(rat.mul_assoc, &[s, r, rd]);
    // assoc_sr : (s*r)*rd = s*(r*rd) = s*r_rd
    let sr = rmul(d, s, r);
    let sr_rd = rmul(d, sr, rd);
    let assoc_sr_rev = rsymm(d, sr_rd, s_rrd_right, assoc_sr);
    let step_23 = rcongr(d, s_rrd_right, sr_rd, assoc_sr_rev, &|d, t| rmul(d, s, t));
    let e3 = rmul(d, s, sr_rd);

    // E3 -> E4 : (s*r) -> 1, inside (·)*rd, inside the outer `s*`.
    let sr_to_one = rcongr(d, sr, one_val, sr1, &|d, t| rmul(d, t, rd));
    let one_rd = rmul(d, one_val, rd);
    let step_34 = rcongr(d, sr_rd, one_rd, sr_to_one, &|d, t| rmul(d, s, t));
    let e4 = rmul(d, s, one_rd);

    // E4 -> E5 : 1*rd -> rd, inside the outer `s*`.
    let one_mul_rd = rat_one_mul(d, p, rd);
    let step_45 = rcongr(d, one_rd, rd, one_mul_rd, &|d, t| rmul(d, s, t));
    let e5 = rmul(d, s, rd);

    // E5 -> E6 : s*(r*dd) -> (s*r)*dd.
    let assoc_srd = d.lemma(rat.mul_assoc, &[s, r, dd]);
    // assoc_srd : (s*r)*dd = s*(r*dd) = e5
    let e6 = rmul(d, sr, dd);
    let step_56 = rsymm(d, e6, e5, assoc_srd);

    // E6 -> E7 : (s*r) -> 1.
    let step_67 = rcongr(d, sr, one_val, sr1, &|d, t| rmul(d, t, dd));
    let e7 = rmul(d, one_val, dd);

    // E7 -> E8 : 1*dd -> dd.
    let step_78 = rat_one_mul(d, p, dd);

    let (_, whole) = rchain(
        d,
        e0,
        &[
            (e1, assoc_01),
            (e2, step_12),
            (e3, step_23),
            (e4, step_34),
            (e5, step_45),
            (e6, step_56),
            (e7, step_67),
            (dd, step_78),
        ],
    );
    whole
}

/// For `a n : Nat`, produces `(m, proof)` where `m := mul_index a n` and
/// `proof : Rat.le (natDivSucc a m) Rat.one`.
///
/// `mul_index a n = (a+1)*n + a = X + a` where `X := (a+1)*n`, so
/// `a + succ(X) = succ(m)` directly (`Nat.add_succ` plus `Nat.add_comm` on
/// `a+X = X+a = m`) — an *explicit* witness, so
/// [`RatPrelude::nat_div_succ_le_add_left`] widens the numerator straight to
/// `succ m`, and [`RatPrelude::nat_div_succ_scale`] at index `m` reads
/// `natDivSucc (succ m) m` as `1`, exactly as [`index_ratio_le_one`] closes
/// the `a = m` case.
fn index_ratio_le_one_at_mul_index(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    n: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let nat = rat.int.nat;
    let one_nat = d.num(1);
    let zero_nat = d.num(0);

    let succ_a = d.succ(a);
    let x_val = NatOps::mul(d, succ_a, n);
    let m = NatOps::add(d, x_val, a);
    let base = d.const_app(rat.nat_div_succ, &[a, m]);
    let unit = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);

    // a + succ(x_val) = succ(m).
    let succ_x = d.succ(x_val);
    let a_succ_x = NatOps::add(d, a, succ_x);
    let step1 = d.lemma(nat.add_succ, &[a, x_val]);
    let ax = NatOps::add(d, a, x_val);
    let succ_ax = d.succ(ax);
    let comm_ax = d.lemma(nat.add_comm, &[a, x_val]);
    let step2 = NatOps::congr(d, ax, m, comm_ax, &|d, t| d.succ(t));
    let succ_m = d.succ(m);
    let (_, e_witness_eq) = NatOps::chain(d, a_succ_x, &[(succ_ax, step1), (succ_m, step2)]);

    let grow = d.lemma(rat.nat_div_succ_le_add_left, &[a, succ_x, m]);
    let at_succ_m = {
        let motive = NatOps::eq_motive(d, a_succ_x, &|d, t| {
            let idx = d.const_app(rat.nat_div_succ, &[t, m]);
            rle(d, rat, base, idx)
        });
        NatOps::transport(d, a_succ_x, motive, grow, succ_m, e_witness_eq)
    };

    // natDivSucc(succ m, m) = natDivSucc(succ m, (succ m)*0+m) = 1.
    let shifted = {
        let product = NatOps::mul(d, succ_m, zero_nat);
        NatOps::add(d, product, m)
    };
    let scale = d.lemma(rat.nat_div_succ_scale, &[m, zero_nat]);
    let restore = {
        let collapse = d.lemma(nat.zero_add, &[m]);
        NatOps::symm(d, shifted, m, collapse)
    };
    let moved = {
        let motive = NatOps::eq_motive(d, m, &|d, t| {
            let index = d.const_app(rat.nat_div_succ, &[succ_m, t]);
            rle(d, rat, base, index)
        });
        NatOps::transport(d, m, motive, at_succ_m, shifted, restore)
    };
    let at_shifted = d.const_app(rat.nat_div_succ, &[succ_m, shifted]);
    let proof = rat_eq_rewrite(d, at_shifted, unit, scale, moved, &|d, t| {
        rle(d, rat, base, t)
    });
    (m, proof)
}

/// For a target index `n`, produces `(m, proof)` where `m := mul_index a n`
/// (`a := 2*(n+1)*(n+1)`) and `proof :
/// Rat.le (natDivSucc 2 m) (Rat.mul (natDivSucc 1 n) (natDivSucc 1 n))`.
///
/// `m` is `mul_index`-shaped (not simply `a`) so that
/// [`super::product::composed_index_le`] can later relate `1/(m+1)` back to
/// `1/(n+1)` through the same composed-index machinery `CReal.mul` itself
/// uses. The proof scales `natDivSucc(a,m) ≤ 1`
/// ([`index_ratio_le_one_at_mul_index`]) by `s*s` (nonneg), using the
/// identity `(s*s)*((r*r)*natDivSucc(2,m)) = natDivSucc(a,m)`
/// (`r := natDivSucc(n+1,0) = 1/s`, `nat_div_succ_mul` twice) and
/// `s*r = Rat.one` (`mul_inv_cancel`/`inv_nat_div_succ`, bridged to
/// `natDivSucc(1,0)` by [`declare_rat_unit_eq_one`]) to cancel the `r`s back
/// out.
fn sq_bound(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> (ExprId, ExprId, ExprId) {
    let rat = p.rat;
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let zero_nat = d.num(0);

    let nplus1 = d.succ(n);
    let sq = NatOps::mul(d, nplus1, nplus1);
    let a = NatOps::mul(d, sq, two_nat);
    let (m, a_m_le_unit) = index_ratio_le_one_at_mul_index(d, p, a, n);

    let s = d.const_app(rat.nat_div_succ, &[one_nat, n]);
    let r = d.const_app(rat.nat_div_succ, &[nplus1, zero_nat]);
    let dd = d.const_app(rat.nat_div_succ, &[two_nat, m]);

    // r*r = natDivSucc(sq, 0).
    let rr_eq = d.lemma(rat.nat_div_succ_mul, &[nplus1, nplus1, zero_nat]);
    let rr = rmul(d, r, r);
    let sq0 = d.const_app(rat.nat_div_succ, &[sq, zero_nat]);

    // natDivSucc(sq,0) * dd = natDivSucc(a, m).
    let combine_eq = d.lemma(rat.nat_div_succ_mul, &[sq, two_nat, m]);
    let a_m = d.const_app(rat.nat_div_succ, &[a, m]);

    let rr_d = rmul(d, rr, dd);
    let sq0_d = rmul(d, sq0, dd);
    let step1 = rcongr(d, rr, sq0, rr_eq, &|d, t| rmul(d, t, dd));
    let (_, rrd_to_am) = rchain(d, rr_d, &[(sq0_d, step1), (a_m, combine_eq)]);

    // natDivSucc(a,m) ≤ natDivSucc(1,0), bridged to ≤ Rat.one.
    let unit_val = d.const_app(rat.nat_div_succ, &[one_nat, zero_nat]);
    let one_val = crate::rat_prelude::ops::rone(d, rat);
    let unit_eq_one = d.lemma(p.rat_unit_eq_one, &[]);
    let am_le_one = rat_eq_rewrite(d, unit_val, one_val, unit_eq_one, a_m_le_unit, &|d, t| {
        rle(d, rat, a_m, t)
    });

    // r*r*dd ≤ Rat.one, via the reverse of rrd_to_am.
    let am_to_rrd = rsymm(d, rr_d, a_m, rrd_to_am);
    let rrd_le_one = rat_eq_rewrite(d, a_m, rr_d, am_to_rrd, am_le_one, &|d, t| {
        rle(d, rat, t, one_val)
    });

    // s > 0, and s*r = Rat.one.
    let one_le_one_nat = crate::rat_prelude::ops::one_le_succ(d, zero_nat);
    let s_pos = d.lemma(rat.nat_div_succ_pos, &[one_nat, n, one_le_one_nat]);
    let mic = d.lemma(rat.mul_inv_cancel, &[s, s_pos]);
    let inv_s = d.const_app(rat.inv, &[s]);
    let inv_eq = d.lemma(rat.inv_nat_div_succ, &[n]);
    let sr1 = rat_eq_rewrite(d, inv_s, r, inv_eq, mic, &|d, t| {
        let prod = rmul(d, s, t);
        crate::rat_prelude::ops::req(d, prod, one_val)
    });

    // Scale rrd_le_one by ss := s*s (nonneg).
    let ss = rmul(d, s, s);
    let ss_nonneg = d.lemma(rat.sq_nonneg, &[s]);
    let scaled = d.lemma(
        rat.mul_le_mul_of_nonneg_left,
        &[ss, rr_d, one_val, ss_nonneg, rrd_le_one],
    );
    // scaled : ss*rr_d <= ss*one_val
    let ss_one = rmul(d, ss, one_val);
    let ss_one_eq_ss = d.lemma(rat.mul_one, &[ss]);
    let ss_rrd = rmul(d, ss, rr_d);
    let scaled2 = rat_eq_rewrite(d, ss_one, ss, ss_one_eq_ss, scaled, &|d, t| {
        rle(d, rat, ss_rrd, t)
    });
    // scaled2 : ss*rr_d <= ss

    let cancel = cancel_sr_pairs(d, p, s, r, dd, sr1);
    // cancel : ss*rr_d = dd
    let final_proof = rat_eq_rewrite(d, ss_rrd, dd, cancel, scaled2, &|d, t| rle(d, rat, t, ss));
    (a, m, final_proof)
}

/// `Eq Rat (Rat.add a (Rat.neg Rat.zero)) a` — `a - 0 = a`, in `add`/`neg`
/// form (defeq to `Rat.sub a Rat.zero`).
fn sub_zero_eq(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let rat = p.rat;
    let zero_rat = rzero(d, rat);
    let neg_zero_eq = d.lemma(rat.neg_zero, &[]);
    let neg_zero_val = rneg(d, zero_rat);
    let step1 = rcongr(d, neg_zero_val, zero_rat, neg_zero_eq, &|d, t| {
        radd(d, a, t)
    });
    let a_zero = radd(d, a, zero_rat);
    let step2 = d.lemma(rat.add_zero, &[a]);
    let a_neg_zero = radd(d, a, neg_zero_val);
    let (_, e) = rchain(d, a_neg_zero, &[(a_zero, step1), (a, step2)]);
    e
}

/// `CReal.eq_zero_of_mul_self_zero : ∀ x, Equiv (mul x x) zero → Equiv x
/// zero`.
///
/// For each target index `n`: [`sq_bound`] picks `m` (and its numerator `a`)
/// with `natDivSucc 2 m ≤ s*s` (`s := natDivSucc 1 n`); `h`'s upper half
/// (`CReal.le_of_equiv`) read at `m` gives the rational fact `t*t ≤ natDivSucc
/// 2 m` (`t := seq x j`, `j := mul_index (mulShift x x) m`, both `seq (mul x
/// x) m` and `seq zero m` reducing definitionally); chaining gives `t*t ≤
/// s*s`, and [`declare_rat_sq_sandwich`] turns that into `Within t s`.
/// [`composed_index_le`] (reused from `CReal.mul`'s own regularity proof,
/// widened to `pub(super)`) reads `j`'s modulus back to `n` because `m` was
/// built `mul_index`-shaped, so [`regular_between`] gives `Within (seq x n -
/// t) (natDivSucc 2 n)`; [`fuse_at`] adds the two `Within`s and a telescoping
/// cancellation (`(seq x n - t) + t = seq x n`) closes the `K = 3` bound
/// [`CReal.equiv_of_bounded`] asks for.
fn declare_eq_zero_of_mul_self_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let rat = p.rat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let zero_real = d.kernel().const_(p.zero, vec![]);
    let xx = cmul(d, p, x, x);
    let h_ty = equiv(d, p, xx, zero_real);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let le_h = d.lemma(p.le_of_equiv, &[xx, zero_real, h]);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let three_nat = d.num(3);
    let zero_rat = rzero(d, rat);

    let bound_hyp = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let (a_param, m, d_le_ss) = sq_bound(d, p, n);
        let s = d.const_app(rat.nat_div_succ, &[one_nat, n]);
        let ss = rmul(d, s, s);

        let le_h_at_m = d.apply(le_h, &[m]);
        // le_h_at_m : le (sub (seq xx m) (seq zero_real m)) (natDivSucc 2 m)
        //   -- treated via defeq as le (sub tt zero_rat) dd.
        let shift = mul_shift(d, p, x, x);
        let j = mul_index(d, shift, m);
        let t = sample(d, p, x, j);
        let tt = rmul(d, t, t);
        let dd = d.const_app(rat.nat_div_succ, &[two_nat, m]);
        let neg_zero_tt = rneg(d, zero_rat);
        let sub_tt_zero = radd(d, tt, neg_zero_tt);
        let cleanup = sub_zero_eq(d, p, tt);
        let tt_le_dd = rat_eq_rewrite(d, sub_tt_zero, tt, cleanup, le_h_at_m, &|d, t2| {
            rle(d, rat, t2, dd)
        });

        let tt_le_ss = d.lemma(rat.le_trans, &[tt, dd, ss, tt_le_dd, d_le_ss]);
        let s_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, n]);
        let within_t_s = d.lemma(p.rat_sq_sandwich, &[t, s, tt_le_ss, s_nonneg]);

        // Within (seq x n - t) (natDivSucc 2 n), via regular_between(x, n, j).
        let high_bound = d.const_app(rat.nat_div_succ, &[one_nat, n]);
        let high_le = d.lemma(rat.le_refl, &[high_bound]);
        let low_le = composed_index_le(d, p, one_nat, shift, a_param, n);
        let seq_x_n = sample(d, p, x, n);
        let gap_within = regular_between(d, p, x, n, j, high_le, low_le, n);
        // gap_within : Within (seq_x_n + (-t)) (natDivSucc 2 n) (rsub defeq).

        let neg_t = rneg(d, t);
        let gap_quantity = radd(d, seq_x_n, neg_t);
        let combined = fuse_at(
            d,
            p,
            gap_quantity,
            two_nat,
            t,
            one_nat,
            n,
            gap_within,
            within_t_s,
        );
        // combined : Within ((seq_x_n + neg_t) + t) (natDivSucc 3 n).

        // (seq_x_n + neg_t) + t = seq_x_n.
        let assoc = d.lemma(rat.add_assoc, &[seq_x_n, neg_t, t]);
        let inner = radd(d, neg_t, t);
        let regrouped = radd(d, seq_x_n, inner);
        let cancel = {
            let comm = d.lemma(rat.add_comm, &[neg_t, t]);
            let t_neg_t = radd(d, t, neg_t);
            let vanish = d.lemma(rat.add_neg, &[t]);
            let zero_val = rzero(d, rat);
            let (_, e) = rchain(d, inner, &[(t_neg_t, comm), (zero_val, vanish)]);
            e
        };
        let zero_val2 = rzero(d, rat);
        let cancel_congr = rcongr(d, inner, zero_val2, cancel, &|d, t2| radd(d, seq_x_n, t2));
        let padded = radd(d, seq_x_n, zero_val2);
        let trim = d.lemma(rat.add_zero, &[seq_x_n]);
        let quantity_left = radd(d, gap_quantity, t);
        let (_, tail) = rchain(
            d,
            quantity_left,
            &[(regrouped, assoc), (padded, cancel_congr), (seq_x_n, trim)],
        );
        let at_seq_x_n = rat_eq_rewrite(d, quantity_left, seq_x_n, tail, combined, &|d, t2| {
            let bound3 = d.const_app(rat.nat_div_succ, &[three_nat, n]);
            within(d, p, t2, bound3)
        });
        // at_seq_x_n : Within (seq x n) (natDivSucc 3 n)

        // Restate as Within (seq x n - seq zero n) (natDivSucc 3 n)
        // (seq zero n reduces by defeq to zero_rat).
        let neg_zero_sx = rneg(d, zero_rat);
        let sub_form = radd(d, seq_x_n, neg_zero_sx);
        let sub_cleanup = sub_zero_eq(d, p, seq_x_n);
        let sub_cleanup_rev = rsymm(d, sub_form, seq_x_n, sub_cleanup);
        let at_sub_form = {
            let bound3 = d.const_app(rat.nat_div_succ, &[three_nat, n]);
            rat_eq_rewrite(
                d,
                seq_x_n,
                sub_form,
                sub_cleanup_rev,
                at_seq_x_n,
                &|d, t2| within(d, p, t2, bound3),
            )
        };
        d.lam_fv(n_fv, nat, at_sub_form)
    };

    let body = d.lemma(p.equiv_of_bounded, &[x, zero_real, three_nat, bound_hyp]);

    let value = {
        let with_h = d.lam_fv(h_fv, h_ty, body);
        d.lam_fv(x_fv, carrier, with_h)
    };
    let ty = {
        let concl = equiv(d, p, x, zero_real);
        let after_h = d.arrow(h_ty, concl);
        d.pi_fv(x_fv, carrier, after_h)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.eq_zero_of_mul_self_zero,
        uparams: vec![],
        ty,
        value,
    })
}

pub(super) fn declare_mul_self_zero(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    declare_rat_sq_le(d, p)?;
    declare_rat_sq_sandwich(d, p)?;
    declare_rat_index_ratio_le_one(d, p)?;
    declare_rat_unit_eq_one(d, p)?;
    declare_eq_zero_of_mul_self_zero(d, p)
}
