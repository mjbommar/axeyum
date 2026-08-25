//! Multiplicative cancellation for `CReal.le` (ADR-0512 lineage), and the
//! `CReal.inv_nonneg` prerequisite it needs.
//!
//! ## Why `PosBound` as data, not `0 < c` as a hypothesis
//!
//! The classical statement is `0 < c → c·x ≤ c·y → x ≤ y`. Over `CReal`,
//! `0 < c` (`CReal.lt`) is an `Exists` — a rational gap witness wrapped in a
//! `Prop` — and `Exists.rec` eliminates only into `Prop`. Building
//! `CReal.inv c k h` needs the modulus `k` as **data** (see `inverse.rs`'s own
//! rationale, which this module does not repeat), and cancellation's proof
//! route goes through exactly that inverse. So this theorem takes the same
//! `PosBound c k` data `CReal.inv` does, rather than `CReal.lt zero c`: no new
//! assumption is introduced by asking for it, since a caller holding
//! `0 < c` already has one (`CReal.pos_bound_of_lt`), and a caller who does not
//! could not build `inv c` either.
//!
//! ## `inv_nonneg`
//!
//! `mul_le_mul_of_nonneg_left` needs its left factor nonnegative, and the
//! natural left factor here is `inv c k h`. Nothing already declared says an
//! inverse (over a `PosBound` modulus) is nonnegative, so this module proves
//! it first. The proof cannot be assembled from already-`pub` `CReal`
//! theorems alone — it has to look at `inv`'s *representative*, exactly as
//! `inverse.rs`'s own `mul_inv_cancel` and regularity proofs do — but the
//! helpers that do that (`sample_lower`, `index_modulus_le`, and the small
//! natural-number index builders) are private to `inverse.rs`. They are
//! reproduced verbatim here rather than promoted, per this slice's
//! constraint of not editing `inverse.rs`; a byte-for-byte comparison against
//! the private originals is how their correctness is trusted (mirroring the
//! precedent `ring_helpers.rs` sets for exactly this situation).
//!
//! ## The cancellation route
//!
//! `mul_le_mul_of_nonneg_left (inv c k h) (mul c x) (mul c y) inv_nonneg hxy`
//! gives `le (mul inv (mul c x)) (mul inv (mul c y))`. Each side is `Equiv`
//! to the bare variable — `mul inv (mul c w) ≈ mul (mul inv c) w`
//! (`mul_assoc`, reversed) `≈ mul (mul c inv) w` (`mul_comm`) `≈ mul one w`
//! (`mul_inv_cancel`) `≈ mul w one` (`mul_comm`) `≈ w` (`mul_one`) — and
//! [`CRealPrelude::le_congr`] transports the inequality across both chains at
//! once.

use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{
    nat_rewrite_prop, radd, rat_eq_rewrite, rchain, rcongr, rle, rneg, rsymm, rzero,
};

use super::{CRealPrelude, creal_ty, div_succ, sample};

// --- small local restatements of `inverse.rs` privates -----------------------
//
// `inverse.rs` cannot be edited in this slice, and these are `fn`, not
// `pub(super) fn`, there. Each is reproduced verbatim (only renamed to avoid
// any accidental shadowing surprise) so `CReal.inv`'s representative at index
// `n` — `(x_{inv_index(k,n)})⁻¹` — is built here as the *identical* term the
// kernel already accepted when it checked `inv`, `mul_inv_cancel`, etc. That
// identity is what lets the kernel's own defeq check bridge
// `CReal.seq (CReal.inv x k h) n` and the raw term below without any extra
// lemma.

/// `2k+1` — the index of `L`, the half of the hypothesis' bound. Verbatim
/// copy of `inverse.rs::half_index`.
fn inv_half_index(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let two = d.num(2);
    let doubled = NatOps::mul(d, two, k);
    d.succ(doubled)
}

/// `4k+3`. Verbatim copy of `inverse.rs::deep_index`.
fn inv_deep_index(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let two = d.num(2);
    let half = inv_half_index(d, k);
    let doubled = NatOps::mul(d, two, half);
    d.succ(doubled)
}

/// `4k+4`. Verbatim copy of `inverse.rs::deep_step`.
fn inv_deep_step(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let deep = inv_deep_index(d, k);
    d.succ(deep)
}

/// `CReal.invShift k`. Verbatim copy of `inverse.rs::inv_shift`.
fn inv_shift_of(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    d.const_app(p.inv_shift, &[k])
}

/// `(C+1)·n + C` — the index `CReal.inv` samples at. Verbatim copy of
/// `inverse.rs::inv_index`.
fn inv_index_of(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, n: ExprId) -> ExprId {
    let shift = inv_shift_of(d, p, k);
    let factor = d.succ(shift);
    let scaled = NatOps::mul(d, factor, n);
    NatOps::add(d, scaled, shift)
}

/// `L = 1/(2k+2)`. Verbatim copy of `inverse.rs::low_bound`.
fn inv_low_bound(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let half = inv_half_index(d, k);
    div_succ(d, p, 1, half)
}

/// `Rat.inv q`.
fn rinv(d: &mut IntDev<'_>, p: CRealPrelude, q: ExprId) -> ExprId {
    d.const_app(p.rat.inv, &[q])
}

/// `CReal.mul x y`.
fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

/// `CReal.inv x k h`.
fn cinv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId, h: ExprId) -> ExprId {
    d.const_app(p.inv, &[x, k, h])
}

/// `CReal.PosBound x k`.
fn pos_bound_of(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.pos_bound, &[x, k])
}

/// `2/(j(n)+1) ≤ L`. Verbatim copy of `inverse.rs::index_modulus_le`.
fn inv_index_modulus_le(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, n: ExprId) -> ExprId {
    let rat = p.rat;
    let index = inv_index_of(d, p, k, n);
    let deep = inv_deep_index(d, k);
    let step = inv_deep_step(d, k);
    let successor = d.succ(k);

    let inner = {
        let factor = d.succ(successor);
        let scaled = NatOps::mul(d, factor, n);
        NatOps::add(d, scaled, successor)
    };
    let composed = {
        let scaled = NatOps::mul(d, step, inner);
        NatOps::add(d, scaled, deep)
    };
    let swapped = {
        let factor = d.succ(inner);
        let scaled = NatOps::mul(d, factor, deep);
        NatOps::add(d, scaled, inner)
    };
    let compose = d.lemma(rat.nat_index_compose, &[deep, successor, n]);
    let symmetric = d.lemma(rat.nat_index_symm, &[deep, inner]);
    let back = NatOps::symm(d, composed, swapped, symmetric);
    let (_, identity) = NatOps::chain(d, swapped, &[(composed, back), (index, compose)]);

    let two = d.num(2);
    let scaled = d.lemma(rat.nat_div_succ_le_scaled, &[two, inner, deep]);
    let half = inv_half_index(d, k);
    let low = inv_low_bound(d, p, k);
    let halve = d.lemma(rat.nat_div_succ_halve, &[half]);
    let at_deep = div_succ(d, p, 2, deep);
    let at_swapped = div_succ(d, p, 2, swapped);
    let bounded = rat_eq_rewrite(d, at_deep, low, halve, scaled, &|d, t| {
        rle(d, rat, at_swapped, t)
    });
    nat_rewrite_prop(d, swapped, index, identity, bounded, &|d, t| {
        let sampled = div_succ(d, p, 2, t);
        rle(d, rat, sampled, low)
    })
}

/// `L ≤ x_{j(n)}`. Verbatim copy of `inverse.rs::sample_lower`.
fn inv_sample_lower(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    k: ExprId,
    h: ExprId,
    n: ExprId,
) -> ExprId {
    let rat = p.rat;
    let index = inv_index_of(d, p, k, n);
    let value = sample(d, p, x, index);
    let bound = div_succ(d, p, 1, k);
    let low = inv_low_bound(d, p, k);
    let zero = rzero(d, rat);

    let at_index = d.apply(h, &[index]);
    let gap = rsub(d, rat, bound, value);
    let deep = div_succ(d, p, 2, index);
    let narrow = inv_index_modulus_le(d, p, k, n);
    let bounded = d.lemma(rat.le_trans, &[gap, deep, low, at_index, narrow]);

    // `c = L + L`.
    let sum = radd(d, low, low);
    let half = inv_half_index(d, k);
    let one_nat = d.num(1);
    let fuse = d.lemma(rat.nat_div_succ_add, &[one_nat, one_nat, half]);
    let doubled = div_succ(d, p, 2, half);
    let halve = d.lemma(rat.nat_div_succ_halve, &[k]);
    let (_, folded) = rchain(d, sum, &[(doubled, fuse), (bound, halve)]);
    let unfolded = rsymm(d, sum, bound, folded);
    let opened = rat_eq_rewrite(d, bound, sum, unfolded, bounded, &|d, t| {
        let difference = rsub(d, rat, t, value);
        rle(d, rat, difference, low)
    });

    // `(L + L − x) + x = L + L`.
    let residue = rsub(d, rat, sum, value);
    let reflexive = d.lemma(rat.le_refl, &[value]);
    let padded = d.lemma(
        rat.add_le_add,
        &[residue, low, value, value, opened, reflexive],
    );
    let negated = rneg(d, value);
    let restored = radd(d, residue, value);
    let associate = d.lemma(rat.add_assoc, &[sum, negated, value]);
    let cancelled = radd(d, negated, value);
    let regrouped = radd(d, sum, cancelled);
    let vanish = d.lemma(rat.neg_add_cancel, &[value]);
    let step_zero = rcongr(d, cancelled, zero, vanish, &|d, t| radd(d, sum, t));
    let with_zero = radd(d, sum, zero);
    let strip = d.lemma(rat.add_zero, &[sum]);
    let (_, collapse) = rchain(
        d,
        restored,
        &[(regrouped, associate), (with_zero, step_zero), (sum, strip)],
    );
    let shifted = radd(d, low, value);
    let reached = rat_eq_rewrite(d, restored, sum, collapse, padded, &|d, t| {
        rle(d, rat, t, shifted)
    });

    // Cancel one `L` on the left of `L + L ≤ L + x`.
    let neg_low = rneg(d, low);
    let reflexive_low = d.lemma(rat.le_refl, &[neg_low]);
    let cancelling = d.lemma(
        rat.add_le_add,
        &[neg_low, neg_low, sum, shifted, reflexive_low, reached],
    );
    let vanish_low = d.lemma(rat.neg_add_cancel, &[low]);
    let unit = radd(d, neg_low, low);
    let left_start = radd(d, neg_low, sum);
    let left_regrouped = radd(d, unit, low);
    let left_associate = d.lemma(rat.add_assoc, &[neg_low, low, low]);
    let left_back = rsymm(d, left_regrouped, left_start, left_associate);
    let left_zero = rcongr(d, unit, zero, vanish_low, &|d, t| radd(d, t, low));
    let left_with_zero = radd(d, zero, low);
    let left_strip = d.lemma(rat.zero_add, &[low]);
    let (_, left_eq) = rchain(
        d,
        left_start,
        &[
            (left_regrouped, left_back),
            (left_with_zero, left_zero),
            (low, left_strip),
        ],
    );
    let right_start = radd(d, neg_low, shifted);
    let right_regrouped = radd(d, unit, value);
    let right_associate = d.lemma(rat.add_assoc, &[neg_low, low, value]);
    let right_back = rsymm(d, right_regrouped, right_start, right_associate);
    let right_zero = rcongr(d, unit, zero, vanish_low, &|d, t| radd(d, t, value));
    let right_with_zero = radd(d, zero, value);
    let right_strip = d.lemma(rat.zero_add, &[value]);
    let (_, right_eq) = rchain(
        d,
        right_start,
        &[
            (right_regrouped, right_back),
            (right_with_zero, right_zero),
            (value, right_strip),
        ],
    );
    let stepped = rat_eq_rewrite(d, left_start, low, left_eq, cancelling, &|d, t| {
        rle(d, rat, t, right_start)
    });
    rat_eq_rewrite(d, right_start, value, right_eq, stepped, &|d, t| {
        rle(d, rat, low, t)
    })
}

/// Turn `Rat.le (−v) (2/(n+1))` into the `CReal.le zero _` body shape
/// `Rat.le (seq zero n − v) (2/(n+1))`. Verbatim copy of
/// `product.rs::restate_as_difference` (private there too).
fn restate_as_difference(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    value: ExprId,
    n: ExprId,
    proof: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero_rat = rzero(d, rat);
    let negated = rneg(d, value);
    let bound = div_succ(d, p, 2, n);
    let difference = rsub(d, rat, zero_rat, value);
    let collapse = d.lemma(rat.zero_add, &[negated]);
    let restore = rsymm(d, difference, negated, collapse);
    rat_eq_rewrite(d, negated, difference, restore, proof, &|d, t| {
        rle(d, rat, t, bound)
    })
}

// --- `inv_nonneg` -------------------------------------------------------------

/// `CReal.inv_nonneg : ∀ x k (h : PosBound x k), le zero (inv x k h)`.
///
/// At every index `n`, `inv x k h`'s representative is `(x_{j(n)})⁻¹`
/// (`j := inv_index`). [`inv_sample_lower`] gives `L ≤ x_{j(n)}` with
/// `L = 1/(2k+2) > 0`, so `0 < x_{j(n)}` (`Rat.lt_of_lt_of_le`) and
/// `0 < (x_{j(n)})⁻¹` (`Rat.inv_pos`) — strictly more than `CReal.le`'s direct
/// `∀n` form needs.
fn declare_inv_nonneg(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat_prelude = rat.int.nat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hypothesis = pos_bound_of(d, p, x, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let inv_expr = cinv(d, p, x, k, h);
    let zero_real = d.kernel().const_(p.zero, vec![]);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let index = inv_index_of(d, p, k, n);
    let value = sample(d, p, x, index);
    let recip = rinv(d, p, value);

    let low = inv_low_bound(d, p, k);
    let lower = inv_sample_lower(d, p, x, k, h, n);

    let one_nat = d.num(1);
    let half = inv_half_index(d, k);
    let unit_le = d.lemma(nat_prelude.le_refl, &[one_nat]);
    let low_positive = d.lemma(rat.nat_div_succ_pos, &[one_nat, half, unit_le]);
    let zero_rat = rzero(d, rat);
    let positive = d.lemma(
        rat.lt_of_lt_of_le,
        &[zero_rat, low, value, low_positive, lower],
    );

    let reciprocal_positive = d.lemma(rat.inv_pos, &[value, positive]);
    let reciprocal_nonneg = d.lemma(rat.le_of_lt, &[zero_rat, recip, reciprocal_positive]);

    let bound = div_succ(d, p, 2, n);
    let negated = rneg(d, recip);
    let below = d.lemma(rat.neg_nonpos_of_nonneg, &[recip, reciprocal_nonneg]);
    let two = d.num(2);
    let bound_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
    let chained = d.lemma(
        rat.le_trans,
        &[negated, zero_rat, bound, below, bound_nonneg],
    );

    let at_index = restate_as_difference(d, p, recip, n, chained);

    let value_term = {
        let over_n = d.lam_fv(n_fv, nat, at_index);
        let with_h = d.lam_fv(h_fv, hypothesis, over_n);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(x_fv, carrier, with_k)
    };
    let ty = {
        let conclusion = d.const_app(p.le, &[zero_real, inv_expr]);
        // `conclusion` mentions `h_fv` (through `inv_expr`), so this Pi must
        // be genuinely dependent (`pi_fv`, binding `h_fv`) rather than
        // `d.arrow` — an anonymous-binder Pi whose codomain still refers to
        // the un-bound `h_fv` is an escaping free variable, not a valid type.
        // (`mul_inv_cancel` in `inverse.rs` is the precedent: its conclusion
        // is `Equiv (mul x (inv x k h)) one`, and its `ty` uses `pi_fv` for
        // `h` for exactly this reason.)
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(x_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.inv_nonneg,
        uparams: vec![],
        ty,
        value: value_term,
    })
}

// --- `le_of_mul_le_mul_left` --------------------------------------------------

/// `Equiv (mul inv (mul c w)) w`, given `cancel_proof : Equiv (mul c inv) one`.
///
/// `mul inv (mul c w) ≈ mul (mul inv c) w` (`mul_assoc`, reversed)
/// `≈ mul (mul c inv) w` (`mul_comm`) `≈ mul one w` (`cancel_proof`)
/// `≈ mul w one` (`mul_comm`) `≈ w` (`mul_one`).
fn cancel_left(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    inv_expr: ExprId,
    c: ExprId,
    w: ExprId,
    cancel_proof: ExprId,
) -> ExprId {
    let cw = cmul(d, p, c, w);
    let start = cmul(d, p, inv_expr, cw);

    let inv_c = cmul(d, p, inv_expr, c);
    let step_a_target = cmul(d, p, inv_c, w);
    let assoc = d.lemma(p.mul_assoc, &[inv_expr, c, w]);
    let step_a = d.lemma(p.equiv_symm, &[step_a_target, start, assoc]);

    let c_inv = cmul(d, p, c, inv_expr);
    let comm_ic = d.lemma(p.mul_comm, &[inv_expr, c]);
    let refl_w = d.lemma(p.equiv_refl, &[w]);
    let step_b_target = cmul(d, p, c_inv, w);
    let step_b = d.lemma(p.mul_congr, &[inv_c, c_inv, w, w, comm_ic, refl_w]);

    let one = d.kernel().const_(p.one, vec![]);
    let step_c_target = cmul(d, p, one, w);
    let step_c = d.lemma(p.mul_congr, &[c_inv, one, w, w, cancel_proof, refl_w]);

    let step_d_target = cmul(d, p, w, one);
    let step_d = d.lemma(p.mul_comm, &[one, w]);

    let step_e = d.lemma(p.mul_one, &[w]);

    echain(
        d,
        p,
        start,
        &[
            (step_a_target, step_a),
            (step_b_target, step_b),
            (step_c_target, step_c),
            (step_d_target, step_d),
            (w, step_e),
        ],
    )
}

/// `Equiv`-chain composition, identical in shape to `ring_helpers.rs::echain`
/// (private there).
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

/// `CReal.le_of_mul_le_mul_left : ∀ c x y k (h : PosBound c k),
/// le (mul c x) (mul c y) → le x y`.
fn declare_le_of_mul_le_mul_left(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hyp_pos_bound = pos_bound_of(d, p, c, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let cx = cmul(d, p, c, x);
    let cy = cmul(d, p, c, y);
    let hyp_le = d.const_app(p.le, &[cx, cy]);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);

    let inv_expr = cinv(d, p, c, k, h);
    let inv_nonneg_fact = d.lemma(p.inv_nonneg, &[c, k, h]);
    let step1 = d.lemma(
        p.mul_le_mul_of_nonneg_left,
        &[inv_expr, cx, cy, inv_nonneg_fact, hxy],
    );

    let cancel_c = d.lemma(p.mul_inv_cancel, &[c, k, h]);
    let eqx = cancel_left(d, p, inv_expr, c, x, cancel_c);
    let eqy = cancel_left(d, p, inv_expr, c, y, cancel_c);

    let mul_inv_cx = cmul(d, p, inv_expr, cx);
    let mul_inv_cy = cmul(d, p, inv_expr, cy);
    let result = d.lemma(p.le_congr, &[mul_inv_cx, x, mul_inv_cy, y, eqx, eqy, step1]);

    let value = {
        let over_hxy = d.lam_fv(hxy_fv, hyp_le, result);
        let with_h = d.lam_fv(h_fv, hyp_pos_bound, over_hxy);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        let with_y = d.lam_fv(y_fv, carrier, with_k);
        let with_x = d.lam_fv(x_fv, carrier, with_y);
        d.lam_fv(c_fv, carrier, with_x)
    };
    let ty = {
        let conclusion = d.const_app(p.le, &[x, y]);
        let after_hxy = d.arrow(hyp_le, conclusion);
        let after_h = d.arrow(hyp_pos_bound, after_hxy);
        let with_k = d.pi_fv(k_fv, nat, after_h);
        let with_y = d.pi_fv(y_fv, carrier, with_k);
        let with_x = d.pi_fv(x_fv, carrier, with_y);
        d.pi_fv(c_fv, carrier, with_x)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.le_of_mul_le_mul_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `CReal.inv_nonneg` and `CReal.le_of_mul_le_mul_left`.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_cancellation(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_inv_nonneg(d, p)?;
    declare_le_of_mul_le_mul_left(d, p)
}
