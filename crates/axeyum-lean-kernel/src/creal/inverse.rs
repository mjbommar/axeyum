//! **The multiplicative inverse of a real number, with its modulus as data**
//! (ADR-0481, phase F3).
//!
//! ## What is data, and what is only a proof
//!
//! [`CReal.Apart`](super::CRealPrelude::apart) is an `Or`, so
//! `inv : (x : CReal) → Apart x zero → CReal` is undefinable: choosing which of
//! the two reciprocals to compute eliminates a disjunction into `Type`. The
//! reading that follows — "a `Prop` hypothesis blocks a `Type`-valued
//! definition" — is **wrong**, and getting it wrong is what kept this operation
//! out of the development. A function may *take* a `Prop` and return a `Type`;
//! what it may not do is *branch* on one. So
//!
//! ```text
//! CReal.inv : (x : CReal) → (k : Nat) → CReal.PosBound x k → CReal
//! ```
//!
//! **is** definable. The representative sequence depends on `k` alone, and the
//! hypothesis is only ever used to discharge `CReal.mk`'s `Prop`-valued
//! regularity field. What has to be data is the **modulus**, not the proof —
//! and [`pos_bound_of_lt`](super::CRealPrelude::pos_bound_of_lt) is the other
//! half of that story, saying the modulus always exists inside an `Exists`,
//! which is a `Prop`, so no amount of proof gets it out.
//!
//! ## The sampling index, and why it is that one
//!
//! Write `c := 1/(k+1)` for the hypothesis' bound and `L := 1/(2k+2)`, so that
//! `L + L = c` by
//! [`natDivSucc_add`](crate::RatPrelude::nat_div_succ_add) and
//! [`natDivSucc_halve`](crate::RatPrelude::nat_div_succ_halve). Set
//!
//! ```text
//! A := 4k+3        u := 2k+2 = A/2 rounded up, the reciprocal of L
//! C := (A+1)·(k+1) + A          so   C + 1 = (4k+4)·(k+2)
//! j(n) := (C+1)·n + C
//! ```
//!
//! and `invSeq x k n := (x_{j(n)})⁻¹`. The whole trick is that this one index
//! reads back **two** ways through
//! [`natDivSucc_le_scaled`](crate::RatPrelude::nat_div_succ_le_scaled), so that
//! `Rat.natDivSucc` still never has to be antitone in its index — the lemma
//! this development has now dodged five times:
//!
//! 1. *A constant lower bound.* `nat_index_compose` says `j(n)` is
//!    `(A+1)·e + A` with `e := (k+2)·n + (k+1)`, and
//!    [`nat_index_symm`](crate::RatPrelude::nat_index_symm) says **that** is
//!    `(e+1)·A + e` — a sampling index in `A`, not in `n`. So
//!    `2/(j(n)+1) ≤ 2/(A+1) = L` for **every** `n`, and with `PosBound` at
//!    index `j(n)` and `c = L + L` that gives `L ≤ x_{j(n)}` outright. This is
//!    the reading that needs the index symmetric in its two arguments, and it
//!    is the reason that lemma exists.
//! 2. *A shrinking bound.* `j(n) = (C+1)·n + C` directly, so
//!    `K/(j(n)+1) ≤ (C+1)/(j(n)+1) = 1/(n+1)` for any `K ≤ C+1` by
//!    `natDivSucc_le_add_left` then `natDivSucc_scale`. The `K` the regularity
//!    estimate produces is `u²`, and `C + 1 = u² + (4k+4)` exactly — which is
//!    why the factor `(k+2)` is in `C` at all.
//!
//! ## What each theorem costs
//!
//! - **regularity** is [`Rat.inv_sub_inv`](crate::RatPrelude::inv_sub_inv) (two
//!   reciprocals differ by their arguments' difference scaled by both), the
//!   regularity of `x`, and `bounds_mul` twice, fused by `natDivSucc_mul` and
//!   read back by (2);
//! - **`mul_inv_cancel`** is
//!   [`Rat.mul_inv_sub_one`](crate::RatPrelude::mul_inv_sub_one) at the
//!   product's own sampling index `J`, closed through
//!   [`Equiv.of_bounded`](super::CRealPrelude::equiv_of_bounded) rather than an
//!   exact estimate — the product's shift depends on `CReal.bound` of the two
//!   factors, which are opaque `natAbs` projections, so no relation between it
//!   and `u` is available. `of_bounded` does not care: the constant is free;
//! - **congruence** is not an estimate at all. `inv` respects `Equiv` because
//!   an inverse in a commutative monoid is unique:
//!   `u ≈ u·(y·v) ≈ (u·y)·v ≈ (u·x)·v ≈ 1·v ≈ v`. That argument needs
//!   `mul_inv_cancel` on both sides and nothing else, so the whole
//!   well-definedness of `x⁻¹` as a function on `ℝ` — including the part
//!   nobody asks about, that two different **moduli** for the same `x` give
//!   `Equiv` results — is sixty lines of `mul_congr`.
//!
//! ## What is deliberately not here
//!
//! No inverse for `x < 0`: `Rat.mul_inv_cancel`'s hypothesis is `0 < q` and the
//! negative branch of `Rat.inv` is unproved. The general `x # 0` case cannot be
//! reduced to the positive one by *branching* on the disjunction (§1), so it
//! has to be `inv (neg x)` under a separate hypothesis, or the caller picks the
//! sign. And no Markov's principle in any disguise: `¬(x ≈ 0) → x # 0` is not
//! proved, not assumed, and not used.

use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::group::rsub;
use crate::rat_prelude::ops::{
    nat_eq_to_rat, nat_rewrite_prop, radd, rat_eq_rewrite, rchain, rcongr, rle, rmul, rneg, rone,
    rsymm, rzero,
};

use super::{
    CRealPrelude, DERIVED_HEIGHT, and_intro, creal_ty, div_succ, equiv, halves, modulus, sample,
    weaken, within,
};

/// Admit `CReal.invShift`, `CReal.inv`, and the three theorems that make it a
/// function on `ℝ` rather than on representatives.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_inverse(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_inv_shift(d, p)?;
    declare_inv(d, p)?;
    declare_mul_inv_cancel(d, p)?;
    declare_inv_congr(d, p)?;
    declare_inv_index_irrelevant(d, p)
}

// --- the ℕ skeleton of the modulus ------------------------------------------

/// `2k+1` — the index of `L`, the half of the hypothesis' bound.
fn half_index(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let two = d.num(2);
    let doubled = NatOps::mul(d, two, k);
    d.succ(doubled)
}

/// `2k+2` — the **reciprocal of `L` as a natural number**, and the constant
/// every sample's reciprocal is bounded by.
fn whole_bound(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let half = half_index(d, k);
    d.succ(half)
}

/// `4k+3` — the index at which `2/(index+1)` **is** `L`, by `natDivSucc_halve`.
fn deep_index(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let two = d.num(2);
    let half = half_index(d, k);
    let doubled = NatOps::mul(d, two, half);
    d.succ(doubled)
}

/// `4k+4`, written as `succ (4k+3)` so that no ℕ-subtraction appears.
fn deep_step(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let deep = deep_index(d, k);
    d.succ(deep)
}

/// `(4k+4)·(k+1) + (4k+3)` — the body of [`CRealPrelude::inv_shift`], written
/// as `(A+1)·b + A` so that `Rat.nat_index_compose` applies to it verbatim.
fn shift_body(d: &mut IntDev<'_>, k: ExprId) -> ExprId {
    let deep = deep_index(d, k);
    let step = deep_step(d, k);
    let successor = d.succ(k);
    let scaled = NatOps::mul(d, step, successor);
    NatOps::add(d, scaled, deep)
}

/// `CReal.invShift k`.
fn inv_shift(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    d.const_app(p.inv_shift, &[k])
}

/// `(C+1)·n + C` — the index `CReal.inv` samples at.
fn inv_index(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, n: ExprId) -> ExprId {
    let shift = inv_shift(d, p, k);
    let factor = d.succ(shift);
    let scaled = NatOps::mul(d, factor, n);
    NatOps::add(d, scaled, shift)
}

/// `Rat.natDivSucc k j` with a **symbolic** numerator.
fn div_succ_at(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.rat.nat_div_succ, &[k, j])
}

/// `L = 1/(2k+2)`, the lower bound every sample of `x` clears.
fn low_bound(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let half = half_index(d, k);
    div_succ(d, p, 1, half)
}

/// `(2k+2)/1`, the upper bound every sample's reciprocal clears.
fn recip_bound(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId) -> ExprId {
    let whole = whole_bound(d, k);
    let zero = d.num(0);
    div_succ_at(d, p, whole, zero)
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
fn pos_bound(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.pos_bound, &[x, k])
}

// --- the two readings of the sampling index ---------------------------------

/// `2/(j(n)+1) ≤ L` — **the constant lower bound**, and the reading that needs
/// [`Rat.nat_index_symm`](crate::RatPrelude::nat_index_symm).
///
/// `nat_index_compose` says `j(n)` is `(A+1)·e + A` with `e = (k+2)·n + (k+1)`;
/// `nat_index_symm` says that **is** `(e+1)·A + e`, a sampling index whose
/// shrinking argument is `A` rather than `n`. So `natDivSucc_le_scaled` reads
/// it back to `A`, where `natDivSucc_halve` says `2/(A+1)` is exactly `L`, and
/// the bound holds at every `n` with no dependence on `n` at all.
fn index_modulus_le(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, n: ExprId) -> ExprId {
    let rat = p.rat;
    let index = inv_index(d, p, k, n);
    let deep = deep_index(d, k);
    let step = deep_step(d, k);
    let successor = d.succ(k);

    // `e := (k+2)·n + (k+1)`, the inner index of the composition.
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
    let half = half_index(d, k);
    let low = low_bound(d, p, k);
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

/// `u²/(j(n)+1) ≤ 1/(n+1)` — **the shrinking bound**, and the reason `C+1` has
/// the factor `(k+2)` in it.
///
/// `natDivSucc_le_add_left` widens the numerator `u² ↦ u² + (4k+4)` at the same
/// index; that sum **is** `C+1` (`u·(u+2) = 2u·(k+2)`, which is associativity
/// and commutativity and not an induction); and `natDivSucc_scale` reads
/// `(C+1)/((C+1)·n + C + 1)` as `1/(n+1)` outright.
fn read_back(d: &mut IntDev<'_>, p: CRealPrelude, k: ExprId, n: ExprId) -> ExprId {
    let rat = p.rat;
    let nat = rat.int.nat;
    let index = inv_index(d, p, k, n);
    let whole = whole_bound(d, k);
    let square = NatOps::mul(d, whole, whole);
    let step = deep_step(d, k);
    let grown = d.lemma(rat.nat_div_succ_le_add_left, &[square, step, index]);
    let widened = NatOps::add(d, square, step);

    // `u² + 2u = u·(u+2) = u·(2·(k+2)) = (u·2)·(k+2) = (2u)·(k+2) = C+1`.
    let two = d.num(2);
    let scaled_whole = NatOps::mul(d, two, whole);
    let mirrored = NatOps::mul(d, whole, two);
    let staged = NatOps::add(d, square, mirrored);
    let commute = d.lemma(nat.mul_comm, &[two, whole]);
    let step_commute = NatOps::congr(d, scaled_whole, mirrored, commute, &|d, t| {
        NatOps::add(d, square, t)
    });
    let raised = {
        let once = d.succ(k);
        d.succ(once)
    };
    let doubled = NatOps::mul(d, two, raised);
    let joined = NatOps::mul(d, whole, doubled);
    let step_join = {
        let widened_factor = NatOps::add(d, whole, two);
        let source = NatOps::mul(d, whole, widened_factor);
        let distribute = d.lemma(nat.left_distrib, &[whole, whole, two]);
        NatOps::symm(d, source, staged, distribute)
    };
    let flat = NatOps::mul(d, mirrored, raised);
    let step_flatten = {
        let associate = d.lemma(nat.mul_assoc, &[whole, two, raised]);
        NatOps::symm(d, flat, joined, associate)
    };
    let successor = {
        let shift = inv_shift(d, p, k);
        d.succ(shift)
    };
    let step_close = {
        let back = NatOps::symm(d, scaled_whole, mirrored, commute);
        NatOps::congr(d, mirrored, scaled_whole, back, &|d, t| {
            NatOps::mul(d, t, raised)
        })
    };
    let (_, identity) = NatOps::chain(
        d,
        widened,
        &[
            (staged, step_commute),
            (joined, step_join),
            (flat, step_flatten),
            (successor, step_close),
        ],
    );

    let base = div_succ_at(d, p, square, index);
    let at_shift = nat_rewrite_prop(d, widened, successor, identity, grown, &|d, t| {
        let wider = div_succ_at(d, p, t, index);
        rle(d, rat, base, wider)
    });
    let shift = inv_shift(d, p, k);
    let scale = d.lemma(rat.nat_div_succ_scale, &[shift, n]);
    let deep_modulus = div_succ_at(d, p, successor, index);
    let target = div_succ(d, p, 1, n);
    rat_eq_rewrite(d, deep_modulus, target, scale, at_shift, &|d, t| {
        rle(d, rat, base, t)
    })
}

// --- what the hypothesis buys at every sampled index ------------------------

/// `L ≤ x_{j(n)}` — a sample of `x` at the inverse's own index clears the
/// hypothesis' half-bound.
///
/// `PosBound x k` at index `j(n)` gives `c − x_{j(n)} ≤ 2/(j(n)+1)`, and
/// [`index_modulus_le`] says that right-hand side is at most `L`. With
/// `c = L + L` — `natDivSucc_add` then `natDivSucc_halve` — the slack is
/// exactly one `L`, and the rest is the ordered group: add `x_{j(n)}`, then
/// cancel one `L` on the left.
fn sample_lower(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    k: ExprId,
    h: ExprId,
    n: ExprId,
) -> ExprId {
    let rat = p.rat;
    let index = inv_index(d, p, k, n);
    let value = sample(d, p, x, index);
    let bound = div_succ(d, p, 1, k);
    let low = low_bound(d, p, k);
    let zero = rzero(d, rat);

    let at_index = d.apply(h, &[index]);
    let gap = rsub(d, rat, bound, value);
    let deep = div_succ(d, p, 2, index);
    let narrow = index_modulus_le(d, p, k, n);
    let bounded = d.lemma(rat.le_trans, &[gap, deep, low, at_index, narrow]);

    // `c = L + L`.
    let sum = radd(d, low, low);
    let half = half_index(d, k);
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

/// `0 < x_{j(n)}` and `|1/x_{j(n)}| ≤ u`, together — the two facts every
/// estimate below needs at every sampled index.
///
/// The upper bound is [`Rat.inv_le_of_pos_le`](crate::RatPrelude::inv_le_of_pos_le)
/// (the inverse is antitone on the positives) composed with
/// [`Rat.inv_natDivSucc`](crate::RatPrelude::inv_nat_div_succ), which is what
/// turns `L⁻¹` into the **natural number** `2k+2` rather than an opaque `Rat`.
/// The lower bound is free: a reciprocal of a positive is positive, and `−u` is
/// below zero.
fn reciprocal_bounds(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    k: ExprId,
    h: ExprId,
    n: ExprId,
) -> (ExprId, ExprId) {
    let rat = p.rat;
    let index = inv_index(d, p, k, n);
    let value = sample(d, p, x, index);
    let low = low_bound(d, p, k);
    let wide = recip_bound(d, p, k);
    let zero = rzero(d, rat);
    let half = half_index(d, k);
    let one_nat = d.num(1);

    let lower = sample_lower(d, p, x, k, h, n);
    let unit_le = {
        let nat = rat.int.nat;
        d.lemma(nat.le_refl, &[one_nat])
    };
    let low_positive = d.lemma(rat.nat_div_succ_pos, &[one_nat, half, unit_le]);
    let positive = d.lemma(rat.lt_of_lt_of_le, &[zero, low, value, low_positive, lower]);

    let reciprocal = rinv(d, p, value);
    let antitone = d.lemma(rat.inv_le_of_pos_le, &[low, value, low_positive, lower]);
    let reciprocal_low = rinv(d, p, low);
    let computed = d.lemma(rat.inv_nat_div_succ, &[half]);
    let upper = rat_eq_rewrite(d, reciprocal_low, wide, computed, antitone, &|d, t| {
        rle(d, rat, reciprocal, t)
    });

    let reciprocal_positive = d.lemma(rat.inv_pos, &[value, positive]);
    let reciprocal_nonneg = d.lemma(rat.le_of_lt, &[zero, reciprocal, reciprocal_positive]);
    let whole = whole_bound(d, k);
    let zero_nat = d.num(0);
    let wide_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[whole, zero_nat]);
    let negated = rneg(d, wide);
    let below = d.lemma(rat.neg_nonpos_of_nonneg, &[wide, wide_nonneg]);
    let deep = d.lemma(
        rat.le_trans,
        &[negated, zero, reciprocal, below, reciprocal_nonneg],
    );
    let lower_ty = rle(d, rat, negated, reciprocal);
    let upper_ty = rle(d, rat, reciprocal, wide);
    let bounded = and_intro(d, p, lower_ty, upper_ty, deep, upper);
    (positive, bounded)
}

// --- the definition ----------------------------------------------------------

/// `CReal.invShift k := (4k+4)·(k+1) + (4k+3)`.
///
/// Written as `(A+1)·b + A` rather than as the polynomial `4k²+12k+7`, because
/// that is the shape [`Rat.nat_index_compose`](crate::RatPrelude::nat_index_compose)
/// recognises — and it is the shape in which `C+1` is *definitionally*
/// `(4k+4)·(k+2)`, with no ℕ-subtraction and no lemma.
fn declare_inv_shift(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let body = shift_body(d, k);
    let value = d.lam_fv(k_fv, nat, body);
    let ty = d.arrow(nat, nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.inv_shift,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 9),
    })
}

/// `CReal.inv : (x : CReal) → (k : Nat) → PosBound x k → CReal`.
///
/// **The dependent `Prop` argument is the whole point.** `h` is consumed only
/// inside `CReal.mk`'s regularity field, which is a `Prop`; the representative
/// `fun n => (x_{j(n)})⁻¹` mentions `k` and nothing else. So the definition
/// never eliminates a `Prop` into `Type`, and the kernel accepts it for exactly
/// the reason an `Apart`-indexed inverse would be refused.
///
/// Regularity is [`Rat.inv_sub_inv`](crate::RatPrelude::inv_sub_inv) —
/// `a⁻¹ − b⁻¹ = (b − a)·(a⁻¹·b⁻¹)` — with the difference bounded by the
/// regularity of `x` and the reciprocal product by `u²`, fused into a single
/// `natDivSucc` by `natDivSucc_mul` and read back at `n` by [`read_back`].
fn declare_inv(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat_prelude = rat.int.nat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hypothesis = pos_bound(d, p, x, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let representative = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let index = inv_index(d, p, k, n);
        let value = sample(d, p, x, index);
        let body = rinv(d, p, value);
        d.lam_fv(n_fv, nat, body)
    };

    let regularity = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let high = inv_index(d, p, k, m);
        let low = inv_index(d, p, k, n);
        let a = sample(d, p, x, high);
        let b = sample(d, p, x, low);
        let (a_positive, a_bounded) = reciprocal_bounds(d, p, x, k, h, m);
        let (b_positive, b_bounded) = reciprocal_bounds(d, p, x, k, h, n);
        let ua = rinv(d, p, a);
        let ub = rinv(d, p, b);
        let split = d.lemma(rat.inv_sub_inv, &[a, b, a_positive, b_positive]);

        let gap = rsub(d, rat, b, a);
        let joint = rmul(d, ua, ub);
        let wide = recip_bound(d, p, k);
        let whole = whole_bound(d, k);
        let zero_nat = d.num(0);
        let one_nat = d.num(1);
        let wide_nonneg = d.lemma(rat.zero_le_nat_div_succ, &[whole, zero_nat]);
        let (a_low, a_high) = halves(d, p, ua, wide, a_bounded);
        let (b_low, b_high) = halves(d, p, ub, wide, b_bounded);
        let joint_bound = d.lemma(
            rat.bounds_mul,
            &[
                ua,
                wide,
                ub,
                wide,
                wide_nonneg,
                a_low,
                a_high,
                b_low,
                b_high,
            ],
        );
        let square = rmul(d, wide, wide);

        let spread = modulus(d, p, low, high);
        let gap_bound = d.lemma(p.regular, &[x, low, high]);
        let spread_nonneg = {
            let left = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, low]);
            let right = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, high]);
            let left_atom = div_succ(d, p, 1, low);
            let right_atom = div_succ(d, p, 1, high);
            d.lemma(rat.add_nonneg, &[left_atom, right_atom, left, right])
        };
        let (gap_low, gap_high) = halves(d, p, gap, spread, gap_bound);
        let (joint_low, joint_high) = halves(d, p, joint, square, joint_bound);
        let product = d.lemma(
            rat.bounds_mul,
            &[
                gap,
                spread,
                joint,
                square,
                spread_nonneg,
                gap_low,
                gap_high,
                joint_low,
                joint_high,
            ],
        );

        let quantity = rsub(d, rat, ua, ub);
        let scaled = rmul(d, gap, joint);
        let bound = rmul(d, spread, square);
        let back = rsymm(d, quantity, scaled, split);
        let at_quantity = rat_eq_rewrite(d, scaled, quantity, back, product, &|d, t| {
            within(d, p, t, bound)
        });

        // `spread · u²` opens into two moduli whose numerator is the single
        // natural `u·u`, which is what `read_back` is stated about.
        let numerator = NatOps::mul(d, whole, whole);
        let atom = div_succ_at(d, p, numerator, zero_nat);
        let fuse = d.lemma(rat.nat_div_succ_mul, &[whole, whole, zero_nat]);
        let step_atom = rcongr(d, square, atom, fuse, &|d, t| rmul(d, spread, t));
        let staged = rmul(d, spread, atom);
        let swap = d.lemma(rat.mul_comm, &[spread, atom]);
        let swapped = rmul(d, atom, spread);
        let one_low = div_succ(d, p, 1, low);
        let one_high = div_succ(d, p, 1, high);
        let distribute = d.lemma(rat.left_distrib, &[atom, one_low, one_high]);
        let left_term = rmul(d, atom, one_low);
        let right_term = rmul(d, atom, one_high);
        let opened = radd(d, left_term, right_term);
        let at_low = div_succ_at(d, p, numerator, low);
        let at_high = div_succ_at(d, p, numerator, high);
        let scaled_numerator = NatOps::mul(d, numerator, one_nat);
        let collapse = d.lemma(nat_prelude.mul_one, &[numerator]);
        let fuse_low = {
            let raw = d.lemma(rat.nat_div_succ_mul, &[numerator, one_nat, low]);
            let raw_target = div_succ_at(d, p, scaled_numerator, low);
            let shrink = nat_eq_to_rat(d, scaled_numerator, numerator, collapse, &|d, t| {
                div_succ_at(d, p, t, low)
            });
            let (_, chained) = rchain(d, left_term, &[(raw_target, raw), (at_low, shrink)]);
            chained
        };
        let step_low = rcongr(d, left_term, at_low, fuse_low, &|d, t| {
            radd(d, t, right_term)
        });
        let staged_low = radd(d, at_low, right_term);
        let fuse_high = {
            let raw = d.lemma(rat.nat_div_succ_mul, &[numerator, one_nat, high]);
            let raw_target = div_succ_at(d, p, scaled_numerator, high);
            let shrink = nat_eq_to_rat(d, scaled_numerator, numerator, collapse, &|d, t| {
                div_succ_at(d, p, t, high)
            });
            let (_, chained) = rchain(d, right_term, &[(raw_target, raw), (at_high, shrink)]);
            chained
        };
        let step_high = rcongr(d, right_term, at_high, fuse_high, &|d, t| {
            radd(d, at_low, t)
        });
        let both = radd(d, at_low, at_high);
        let reorder = d.lemma(rat.add_comm, &[at_low, at_high]);
        let ordered = radd(d, at_high, at_low);
        let (_, bound_eq) = rchain(
            d,
            bound,
            &[
                (staged, step_atom),
                (swapped, swap),
                (opened, distribute),
                (staged_low, step_low),
                (both, step_high),
                (ordered, reorder),
            ],
        );
        let moved = rat_eq_rewrite(d, bound, ordered, bound_eq, at_quantity, &|d, t| {
            within(d, p, quantity, t)
        });

        let target = modulus(d, p, m, n);
        let high_back = read_back(d, p, k, m);
        let low_back = read_back(d, p, k, n);
        let goal_high = div_succ(d, p, 1, m);
        let goal_low = div_succ(d, p, 1, n);
        let order = d.lemma(
            rat.add_le_add,
            &[at_high, goal_high, at_low, goal_low, high_back, low_back],
        );
        let widened = weaken(d, p, quantity, ordered, target, moved, order);
        let over_n = d.lam_fv(n_fv, nat, widened);
        d.lam_fv(m_fv, nat, over_n)
    };

    let constructor = d.kernel().const_(p.mk, vec![]);
    let body = d.apply(constructor, &[representative, regularity]);
    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(x_fv, carrier, with_k)
    };
    let ty = {
        let inner = d.arrow(hypothesis, carrier);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(x_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.inv,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 13),
    })
}

// --- the law ----------------------------------------------------------------

/// `CReal.mulShift x y` — the `c` of `CReal.mul`'s sampling index `(c+1)·n + c`.
fn mul_shift(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul_shift, &[x, y])
}

/// `(c+1)·n + c`, the index `CReal.mul` samples at.
fn mul_index(d: &mut IntDev<'_>, c: ExprId, n: ExprId) -> ExprId {
    let factor = d.succ(c);
    let scaled = NatOps::mul(d, factor, n);
    NatOps::add(d, scaled, c)
}

/// `mul_inv_cancel : ∀ x k (h : PosBound x k), Equiv (mul x (inv x k h)) one`.
///
/// **The field law, on the positive branch**, and the first theorem in this
/// development whose two sides sample `x` at indices with *no* relation to each
/// other: `CReal.mul`'s shift is built from `CReal.bound` of the two factors,
/// which are opaque `Int.natAbs` projections, and `CReal.inv`'s shift is built
/// from `k`. Nothing connects them.
///
/// It does not have to. [`Rat.mul_inv_sub_one`](crate::RatPrelude::mul_inv_sub_one)
/// says the residue of `x_J · (x_{j(J)})⁻¹` from `1` is `(x_J − x_{j(J)})`
/// scaled by the reciprocal — a regularity gap times a constant — and
/// [`Equiv.of_bounded`](super::CRealPrelude::equiv_of_bounded) accepts any
/// `O(1/n)` bound whatsoever. The constant that comes out is `2u = 4k+4`, and
/// nobody has to know what `CReal.mulShift` evaluates to.
fn declare_mul_inv_cancel(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let rat = p.rat;
    let nat_prelude = rat.int.nat;
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hypothesis = pos_bound(d, p, x, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let reciprocal = cinv(d, p, x, k, h);
    let product = cmul(d, p, x, reciprocal);
    let one = d.kernel().const_(p.one, vec![]);
    let whole = whole_bound(d, k);
    let total = NatOps::add(d, whole, whole);
    let shift = mul_shift(d, p, x, reciprocal);

    let witness = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let outer = mul_index(d, shift, n);
        let inner = inv_index(d, p, k, outer);
        let value = sample(d, p, x, outer);
        let deep = sample(d, p, x, inner);
        let (deep_positive, deep_bounded) = reciprocal_bounds(d, p, x, k, h, outer);
        let deep_inverse = rinv(d, p, deep);
        let scaled = rmul(d, value, deep_inverse);
        let unit = rone(d, rat);
        let quantity = rsub(d, rat, scaled, unit);
        let split = d.lemma(rat.mul_inv_sub_one, &[value, deep, deep_positive]);

        let gap = rsub(d, rat, value, deep);
        let residue = rmul(d, gap, deep_inverse);
        let spread = modulus(d, p, outer, inner);
        let gap_bound = d.lemma(p.regular, &[x, outer, inner]);
        let one_nat = d.num(1);
        let spread_nonneg = {
            let left = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, outer]);
            let right = d.lemma(rat.zero_le_nat_div_succ, &[one_nat, inner]);
            let left_atom = div_succ(d, p, 1, outer);
            let right_atom = div_succ(d, p, 1, inner);
            d.lemma(rat.add_nonneg, &[left_atom, right_atom, left, right])
        };
        let wide = recip_bound(d, p, k);
        let (gap_low, gap_high) = halves(d, p, gap, spread, gap_bound);
        let (deep_low, deep_high) = halves(d, p, deep_inverse, wide, deep_bounded);
        let bounded = d.lemma(
            rat.bounds_mul,
            &[
                gap,
                spread,
                deep_inverse,
                wide,
                spread_nonneg,
                gap_low,
                gap_high,
                deep_low,
                deep_high,
            ],
        );
        let bound = rmul(d, spread, wide);
        let back = rsymm(d, quantity, residue, split);
        let at_quantity = rat_eq_rewrite(d, residue, quantity, back, bounded, &|d, t| {
            within(d, p, t, bound)
        });

        // `spread · (u/1)` opens into `u/(J+1) + u/(j(J)+1)`.
        let swap = d.lemma(rat.mul_comm, &[spread, wide]);
        let swapped = rmul(d, wide, spread);
        let one_outer = div_succ(d, p, 1, outer);
        let one_inner = div_succ(d, p, 1, inner);
        let distribute = d.lemma(rat.left_distrib, &[wide, one_outer, one_inner]);
        let left_term = rmul(d, wide, one_outer);
        let right_term = rmul(d, wide, one_inner);
        let opened = radd(d, left_term, right_term);
        let at_outer = div_succ_at(d, p, whole, outer);
        let at_inner = div_succ_at(d, p, whole, inner);
        let scaled_numerator = NatOps::mul(d, whole, one_nat);
        let collapse = d.lemma(nat_prelude.mul_one, &[whole]);
        let fuse_outer = {
            let raw = d.lemma(rat.nat_div_succ_mul, &[whole, one_nat, outer]);
            let raw_target = div_succ_at(d, p, scaled_numerator, outer);
            let shrink = nat_eq_to_rat(d, scaled_numerator, whole, collapse, &|d, t| {
                div_succ_at(d, p, t, outer)
            });
            let (_, chained) = rchain(d, left_term, &[(raw_target, raw), (at_outer, shrink)]);
            chained
        };
        let step_outer = rcongr(d, left_term, at_outer, fuse_outer, &|d, t| {
            radd(d, t, right_term)
        });
        let staged_outer = radd(d, at_outer, right_term);
        let fuse_inner = {
            let raw = d.lemma(rat.nat_div_succ_mul, &[whole, one_nat, inner]);
            let raw_target = div_succ_at(d, p, scaled_numerator, inner);
            let shrink = nat_eq_to_rat(d, scaled_numerator, whole, collapse, &|d, t| {
                div_succ_at(d, p, t, inner)
            });
            let (_, chained) = rchain(d, right_term, &[(raw_target, raw), (at_inner, shrink)]);
            chained
        };
        let step_inner = rcongr(d, right_term, at_inner, fuse_inner, &|d, t| {
            radd(d, at_outer, t)
        });
        let pair = radd(d, at_outer, at_inner);
        let (_, bound_eq) = rchain(
            d,
            bound,
            &[
                (swapped, swap),
                (opened, distribute),
                (staged_outer, step_outer),
                (pair, step_inner),
            ],
        );
        let moved = rat_eq_rewrite(d, bound, pair, bound_eq, at_quantity, &|d, t| {
            within(d, p, quantity, t)
        });

        // `u/(j(J)+1) ≤ u/(J+1)`, then the doubled modulus back to `n`.
        let inverse_shift = inv_shift(d, p, k);
        let deepened = d.lemma(rat.nat_div_succ_le_scaled, &[whole, inverse_shift, outer]);
        let reflexive = d.lemma(rat.le_refl, &[at_outer]);
        let doubled = radd(d, at_outer, at_outer);
        let paired = d.lemma(
            rat.add_le_add,
            &[at_outer, at_outer, at_inner, at_outer, reflexive, deepened],
        );
        let fuse = d.lemma(rat.nat_div_succ_add, &[whole, whole, outer]);
        let total_outer = div_succ_at(d, p, total, outer);
        let fused = rat_eq_rewrite(d, doubled, total_outer, fuse, paired, &|d, t| {
            rle(d, rat, pair, t)
        });
        let target = div_succ_at(d, p, total, n);
        let shallow = d.lemma(rat.nat_div_succ_le_scaled, &[total, shift, n]);
        let order = d.lemma(rat.le_trans, &[pair, total_outer, target, fused, shallow]);
        let widened = weaken(d, p, quantity, pair, target, moved, order);
        d.lam_fv(n_fv, nat, widened)
    };

    let proof = d.lemma(p.equiv_of_bounded, &[product, one, total, witness]);
    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, proof);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(x_fv, carrier, with_k)
    };
    let ty = {
        let conclusion = equiv(d, p, product, one);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(x_fv, carrier, with_k)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mul_inv_cancel,
        uparams: vec![],
        ty,
        value,
    })
}

// --- and it is a function on ℝ, not on representatives ----------------------

/// Chain `Equiv start …` through `(next, step)` pairs.
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

/// `inv_congr : ∀ x y k₁ k₂ h₁ h₂, Equiv x y → Equiv (inv x k₁ h₁) (inv y k₂ h₂)`.
///
/// **Without this `CReal.inv` is not a function on `ℝ` at all**, only on
/// representatives — and the modulus makes the obligation *larger* than the
/// usual congruence, because two callers who supply different `k` for the same
/// `x` build genuinely different sequences. Both are covered here: the
/// statement quantifies over `k₁` and `k₂` independently, and
/// [`inv_index_irrelevant`](CRealPrelude::inv_index_irrelevant) is this theorem
/// at `y := x` with `Equiv.refl`.
///
/// It is **not** an estimate. An inverse in a commutative monoid is unique, so
///
/// ```text
/// u ≈ u·1 ≈ u·(y·v) ≈ (u·y)·v ≈ (u·x)·v ≈ (x·u)·v ≈ 1·v ≈ v·1 ≈ v
/// ```
///
/// closes on [`mul_inv_cancel`] at both ends plus `mul_congr`, `mul_assoc`,
/// `mul_comm` and `mul_one`. No index arithmetic appears, and none can: the two
/// sequences are compared only through the operation they invert.
fn declare_inv_congr(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let left_fv = d.fresh_fvar();
    let left_k = d.kernel().fvar(left_fv);
    let right_fv = d.fresh_fvar();
    let right_k = d.kernel().fvar(right_fv);
    let left_bound = pos_bound(d, p, x, left_k);
    let right_bound = pos_bound(d, p, y, right_k);
    let hl_fv = d.fresh_fvar();
    let hl = d.kernel().fvar(hl_fv);
    let hr_fv = d.fresh_fvar();
    let hr = d.kernel().fvar(hr_fv);
    let related = equiv(d, p, x, y);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);

    let u = cinv(d, p, x, left_k, hl);
    let v = cinv(d, p, y, right_k, hr);
    let one = d.kernel().const_(p.one, vec![]);

    let left_cancel = d.lemma(p.mul_inv_cancel, &[x, left_k, hl]);
    let right_cancel = d.lemma(p.mul_inv_cancel, &[y, right_k, hr]);
    let refl_u = d.lemma(p.equiv_refl, &[u]);
    let refl_v = d.lemma(p.equiv_refl, &[v]);

    // `u ≈ u·1`.
    let u_one = cmul(d, p, u, one);
    let strip_u = d.lemma(p.mul_one, &[u]);
    let open_u = d.lemma(p.equiv_symm, &[u_one, u, strip_u]);

    // `u·1 ≈ u·(y·v)`.
    let yv = cmul(d, p, y, v);
    let reopen = d.lemma(p.equiv_symm, &[yv, one, right_cancel]);
    let u_yv = cmul(d, p, u, yv);
    let step_reopen = d.lemma(p.mul_congr, &[u, u, one, yv, refl_u, reopen]);

    // `u·(y·v) ≈ (u·y)·v`.
    let uy = cmul(d, p, u, y);
    let uy_v = cmul(d, p, uy, v);
    let associate = d.lemma(p.mul_assoc, &[u, y, v]);
    let step_associate = d.lemma(p.equiv_symm, &[uy_v, u_yv, associate]);

    // `u·y ≈ u·x ≈ x·u ≈ 1`.
    let flipped = d.lemma(p.equiv_symm, &[x, y, he]);
    let ux = cmul(d, p, u, x);
    let to_ux = d.lemma(p.mul_congr, &[u, u, y, x, refl_u, flipped]);
    let xu = cmul(d, p, x, u);
    let commute = d.lemma(p.mul_comm, &[u, x]);
    let to_xu = d.lemma(p.equiv_trans, &[uy, ux, xu, to_ux, commute]);
    let uy_one = d.lemma(p.equiv_trans, &[uy, xu, one, to_xu, left_cancel]);

    // `(u·y)·v ≈ 1·v ≈ v·1 ≈ v`.
    let one_v = cmul(d, p, one, v);
    let step_collapse = d.lemma(p.mul_congr, &[uy, one, v, v, uy_one, refl_v]);
    let v_one = cmul(d, p, v, one);
    let commute_v = d.lemma(p.mul_comm, &[one, v]);
    let strip_v = d.lemma(p.mul_one, &[v]);
    let step_strip = d.lemma(p.equiv_trans, &[one_v, v_one, v, commute_v, strip_v]);

    let chained = echain(
        d,
        p,
        u,
        &[
            (u_one, open_u),
            (u_yv, step_reopen),
            (uy_v, step_associate),
            (one_v, step_collapse),
            (v, step_strip),
        ],
    );

    let value = {
        let with_he = d.lam_fv(he_fv, related, chained);
        let with_hr = d.lam_fv(hr_fv, right_bound, with_he);
        let with_hl = d.lam_fv(hl_fv, left_bound, with_hr);
        let with_right = d.lam_fv(right_fv, nat, with_hl);
        let with_left = d.lam_fv(left_fv, nat, with_right);
        let with_y = d.lam_fv(y_fv, carrier, with_left);
        d.lam_fv(x_fv, carrier, with_y)
    };
    let ty = {
        let conclusion = equiv(d, p, u, v);
        let with_he = d.arrow(related, conclusion);
        let with_hr = d.pi_fv(hr_fv, right_bound, with_he);
        let with_hl = d.pi_fv(hl_fv, left_bound, with_hr);
        let with_right = d.pi_fv(right_fv, nat, with_hl);
        let with_left = d.pi_fv(left_fv, nat, with_right);
        let with_y = d.pi_fv(y_fv, carrier, with_left);
        d.pi_fv(x_fv, carrier, with_y)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.inv_congr,
        uparams: vec![],
        ty,
        value,
    })
}

/// `inv_index_irrelevant : ∀ x k₁ k₂ h₁ h₂, Equiv (inv x k₁ h₁) (inv x k₂ h₂)`.
///
/// **The modulus is data, and this is the price of that.** Two callers holding
/// different separating moduli for the *same* real build different sequences —
/// `k = 0` samples at index `7n+7`, `k = 1` at `32n+31` — and nothing in
/// `CReal.inv`'s type says the results agree. This does, so `x⁻¹` denotes a
/// single element of `ℝ` and the choice of `k` is an implementation detail of
/// the *representative* rather than of the value.
///
/// [`declare_inv_congr`] at `y := x` with `Equiv.refl`.
fn declare_inv_index_irrelevant(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let left_fv = d.fresh_fvar();
    let left_k = d.kernel().fvar(left_fv);
    let right_fv = d.fresh_fvar();
    let right_k = d.kernel().fvar(right_fv);
    let left_bound = pos_bound(d, p, x, left_k);
    let right_bound = pos_bound(d, p, x, right_k);
    let hl_fv = d.fresh_fvar();
    let hl = d.kernel().fvar(hl_fv);
    let hr_fv = d.fresh_fvar();
    let hr = d.kernel().fvar(hr_fv);

    let reflexive = d.lemma(p.equiv_refl, &[x]);
    let instance = d.lemma(p.inv_congr, &[x, x, left_k, right_k, hl, hr, reflexive]);
    let value = {
        let with_hr = d.lam_fv(hr_fv, right_bound, instance);
        let with_hl = d.lam_fv(hl_fv, left_bound, with_hr);
        let with_right = d.lam_fv(right_fv, nat, with_hl);
        d.lam_fv(left_fv, nat, with_right)
    };
    let ty = {
        let u = cinv(d, p, x, left_k, hl);
        let v = cinv(d, p, x, right_k, hr);
        let conclusion = equiv(d, p, u, v);
        let with_hr = d.pi_fv(hr_fv, right_bound, conclusion);
        let with_hl = d.pi_fv(hl_fv, left_bound, with_hr);
        let with_right = d.pi_fv(right_fv, nat, with_hl);
        d.pi_fv(left_fv, nat, with_right)
    };
    let value = d.lam_fv(x_fv, carrier, value);
    let ty = d.pi_fv(x_fv, carrier, ty);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.inv_index_irrelevant,
        uparams: vec![],
        ty,
        value,
    })
}
