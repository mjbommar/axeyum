//! The **ordered-group** toolkit over `ℚ`: negation, subtraction, and the
//! two-sided bounds a `|a| ≤ b` statement is written as.
//!
//! ## Why these are cheap, and why that matters
//!
//! Everything in this module is derived from the **22 ordered-commutative-ring
//! laws alone** — `add_comm`, `add_assoc`, `add_zero`, `add_neg`, `le_refl`,
//! `add_le_add` — and never touches a numerator, a denominator, or a
//! cross-multiplication. That is deliberate, and it is the first dividend of
//! `super::laws` having closed all 22: a lemma proved this way is a theorem of
//! *ordered groups*, so when ADR-0468's `CReal` needs the same reasoning one
//! level up it can be transcribed rather than re-derived, and when ADR-0457's
//! telescope is instantiated at a setoid carrier these are exactly the shapes
//! that have to be re-stated over `Equiv`.
//!
//! Two lemmas are the exception and say so in their comments:
//! [`Rat.natDivSucc_add`](super::RatPrelude::nat_div_succ_add) and
//! [`Rat.zero_le_natDivSucc`](super::RatPrelude::zero_le_nat_div_succ) are about
//! the *representation*, so they go through `normalize_congr` and
//! `normalize_cross` like everything in `super::scaling`.
//!
//! ## `|a| ≤ b` is a pair, not an operator
//!
//! ADR-0468 states every closeness bound as `−b ≤ a ∧ a ≤ b` rather than
//! introducing `Rat.abs`. [`Rat.bounds_add`](super::RatPrelude::bounds_add) is
//! the only fact about that encoding the real construction needs — the triangle
//! inequality, in the form "two bounded quantities have a bounded sum" — and it
//! is two applications of `add_le_add` with `neg_add` in between. An `abs`
//! operator would have needed a case split on the sign, a congruence lemma, and
//! its own monotonicity theory; this needs none of them.

use super::RatPrelude;
use super::ops::{
    normalize, num, one_le_succ, radd, rat_theorem, rchain, rcongr, req, rle, rneg, rsymm, rzero,
};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// `Rat.sub a b` — stated through the constant, so a theorem's *type* mentions
/// `Rat.sub`; the proofs below work in the `add a (neg b)` form it unfolds to.
pub(crate) fn rsub(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    d.const_app(p.sub, &[a, b])
}

/// Admit the ordered-group toolkit.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_group_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_additive(d, p)?;
    declare_negation(d, p)?;
    declare_subtraction(d, p)?;
    declare_bounds(d, p)?;
    declare_representation(d, p)
}

/// `0 + a = a` and `(−a) + a = 0`: the two orientations `add_zero`/`add_neg` do
/// not give, needed constantly below and each one `add_comm` away.
fn declare_additive(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.zero_add, 1, &|d, v| {
        let a = v[0];
        let zero = rzero(d, p);
        let left = radd(d, zero, a);
        let stmt = req(d, left, a);
        let flipped = radd(d, a, zero);
        let commute = d.lemma(p.add_comm, &[zero, a]);
        let collapse = d.lemma(p.add_zero, &[a]);
        let (_, proof) = rchain(d, left, &[(flipped, commute), (a, collapse)]);
        (stmt, proof)
    })?;

    rat_theorem(d, p.neg_add_cancel, 1, &|d, v| {
        let a = v[0];
        let opposite = rneg(d, a);
        let left = radd(d, opposite, a);
        let zero = rzero(d, p);
        let stmt = req(d, left, zero);
        let flipped = radd(d, a, opposite);
        let commute = d.lemma(p.add_comm, &[opposite, a]);
        let collapse = d.lemma(p.add_neg, &[a]);
        let (_, proof) = rchain(d, left, &[(flipped, commute), (zero, collapse)]);
        (stmt, proof)
    })
}

/// Uniqueness of the additive inverse, and the three consequences that make
/// negation usable: `−(−a) = a`, `−(a+b) = −a + −b`, and `a ≤ b → −b ≤ −a`.
///
/// Uniqueness is the load-bearing one. Without it `neg_neg` and `neg_add` are
/// each a separate rearrangement; with it they are one line apiece, because
/// each is "exhibit a partner summing to zero".
fn declare_negation(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    // neg_eq_of_add_eq_zero : a + b = 0 → neg a = b.
    //   -a = -a + 0 = -a + (a + b) = (-a + a) + b = 0 + b = b
    rat_theorem(d, p.neg_eq_of_add_eq_zero, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = rzero(d, p);
        let sum = radd(d, a, b);
        let hypothesis = req(d, sum, zero);
        let opposite = rneg(d, a);
        let conclusion = req(d, opposite, b);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let padded = radd(d, opposite, zero);
        let unpad = {
            let forward = d.lemma(p.add_zero, &[opposite]);
            rsymm(d, padded, opposite, forward)
        };
        let expanded = radd(d, opposite, sum);
        let reopen = {
            let back = rsymm(d, sum, zero, h);
            rcongr(d, zero, sum, back, &|d, t| radd(d, opposite, t))
        };
        let cancel_head = radd(d, opposite, a);
        let regrouped = radd(d, cancel_head, b);
        let regroup = {
            let forward = d.lemma(p.add_assoc, &[opposite, a, b]);
            rsymm(d, regrouped, expanded, forward)
        };
        let zeroed = radd(d, zero, b);
        let vanish = {
            let cancel = d.lemma(p.neg_add_cancel, &[a]);
            rcongr(d, cancel_head, zero, cancel, &|d, t| radd(d, t, b))
        };
        let strip = d.lemma(p.zero_add, &[b]);
        let (_, chained) = rchain(
            d,
            opposite,
            &[
                (padded, unpad),
                (expanded, reopen),
                (regrouped, regroup),
                (zeroed, vanish),
                (b, strip),
            ],
        );
        let proof = d.lam_fv(h_fv, hypothesis, chained);
        (stmt, proof)
    })?;

    // neg_neg : neg (neg a) = a, because `(-a) + a = 0`.
    rat_theorem(d, p.neg_neg, 1, &|d, v| {
        let a = v[0];
        let opposite = rneg(d, a);
        let twice = rneg(d, opposite);
        let stmt = req(d, twice, a);
        let cancel = d.lemma(p.neg_add_cancel, &[a]);
        let proof = d.lemma(p.neg_eq_of_add_eq_zero, &[opposite, a, cancel]);
        (stmt, proof)
    })?;

    // neg_zero : neg 0 = 0, because `0 + 0 = 0`.
    rat_theorem(d, p.neg_zero, 0, &|d, v| {
        let _ = v;
        let zero = rzero(d, p);
        let negated = rneg(d, zero);
        let stmt = req(d, negated, zero);
        let cancel = d.lemma(p.add_zero, &[zero]);
        let proof = d.lemma(p.neg_eq_of_add_eq_zero, &[zero, zero, cancel]);
        (stmt, proof)
    })?;

    // neg_add : neg (a + b) = neg a + neg b, because
    //   (a+b) + (-a + -b) = ((a+b) + -a) + -b = (b + (a + -a)) + -b
    //                     = (b + 0) + -b = b + -b = 0
    rat_theorem(d, p.neg_add, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let sum = radd(d, a, b);
        let negated_a = rneg(d, a);
        let negated_b = rneg(d, b);
        let opposites = radd(d, negated_a, negated_b);
        let negated_sum = rneg(d, sum);
        let stmt = req(d, negated_sum, opposites);
        let zero = rzero(d, p);

        let total = radd(d, sum, opposites);
        let head = radd(d, sum, negated_a);
        let flat = radd(d, head, negated_b);
        let flatten = {
            let forward = d.lemma(p.add_assoc, &[sum, negated_a, negated_b]);
            rsymm(d, flat, total, forward)
        };
        let commuted_sum = radd(d, b, a);
        let commute = {
            let step = d.lemma(p.add_comm, &[a, b]);
            let inner = rcongr(d, sum, commuted_sum, step, &|d, t| radd(d, t, negated_a));
            let commuted_head = radd(d, commuted_sum, negated_a);
            rcongr(d, head, commuted_head, inner, &|d, t| radd(d, t, negated_b))
        };
        let commuted_head = radd(d, commuted_sum, negated_a);
        let commuted_flat = radd(d, commuted_head, negated_b);
        let inner_cancel = radd(d, a, negated_a);
        let nested = radd(d, b, inner_cancel);
        let regroup = {
            let forward = d.lemma(p.add_assoc, &[b, a, negated_a]);
            rcongr(d, commuted_head, nested, forward, &|d, t| {
                radd(d, t, negated_b)
            })
        };
        let nested_flat = radd(d, nested, negated_b);
        let padded = radd(d, b, zero);
        let vanish = {
            let cancel = d.lemma(p.add_neg, &[a]);
            let inner = rcongr(d, inner_cancel, zero, cancel, &|d, t| radd(d, b, t));
            rcongr(d, nested, padded, inner, &|d, t| radd(d, t, negated_b))
        };
        let padded_flat = radd(d, padded, negated_b);
        let stripped = radd(d, b, negated_b);
        let strip = {
            let drop = d.lemma(p.add_zero, &[b]);
            rcongr(d, padded, b, drop, &|d, t| radd(d, t, negated_b))
        };
        let close = d.lemma(p.add_neg, &[b]);
        let (_, vanishes) = rchain(
            d,
            total,
            &[
                (flat, flatten),
                (commuted_flat, commute),
                (nested_flat, regroup),
                (padded_flat, vanish),
                (stripped, strip),
                (zero, close),
            ],
        );
        let proof = d.lemma(p.neg_eq_of_add_eq_zero, &[sum, opposites, vanishes]);
        (stmt, proof)
    })?;

    // neg_le_neg : a ≤ b → neg b ≤ neg a.
    //   a + ((-a) + (-b)) ≤ b + ((-a) + (-b)), and the two sides collapse.
    rat_theorem(d, p.neg_le_neg, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let negated_a = rneg(d, a);
        let negated_b = rneg(d, b);
        let hypothesis = rle(d, p, a, b);
        let conclusion = rle(d, p, negated_b, negated_a);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let zero = rzero(d, p);

        let tail = radd(d, negated_a, negated_b);
        let reflexive = d.lemma(p.le_refl, &[tail]);
        let scaled = d.lemma(p.add_le_add, &[a, b, tail, tail, h, reflexive]);

        // Left: a + (-a + -b) = (a + -a) + -b = 0 + -b = -b.
        let left_start = radd(d, a, tail);
        let left_head = radd(d, a, negated_a);
        let left_flat = radd(d, left_head, negated_b);
        let left_flatten = {
            let forward = d.lemma(p.add_assoc, &[a, negated_a, negated_b]);
            rsymm(d, left_flat, left_start, forward)
        };
        let left_zeroed = radd(d, zero, negated_b);
        let left_vanish = {
            let cancel = d.lemma(p.add_neg, &[a]);
            rcongr(d, left_head, zero, cancel, &|d, t| radd(d, t, negated_b))
        };
        let left_strip = d.lemma(p.zero_add, &[negated_b]);
        let (_, left_chain) = rchain(
            d,
            left_start,
            &[
                (left_flat, left_flatten),
                (left_zeroed, left_vanish),
                (negated_b, left_strip),
            ],
        );

        // Right: b + (-a + -b) = b + (-b + -a) = (b + -b) + -a = 0 + -a = -a.
        let right_start = radd(d, b, tail);
        let swapped = radd(d, negated_b, negated_a);
        let right_swapped = radd(d, b, swapped);
        let right_swap = {
            let commute = d.lemma(p.add_comm, &[negated_a, negated_b]);
            rcongr(d, tail, swapped, commute, &|d, t| radd(d, b, t))
        };
        let right_head = radd(d, b, negated_b);
        let right_flat = radd(d, right_head, negated_a);
        let right_flatten = {
            let forward = d.lemma(p.add_assoc, &[b, negated_b, negated_a]);
            rsymm(d, right_flat, right_swapped, forward)
        };
        let right_zeroed = radd(d, zero, negated_a);
        let right_vanish = {
            let cancel = d.lemma(p.add_neg, &[b]);
            rcongr(d, right_head, zero, cancel, &|d, t| radd(d, t, negated_a))
        };
        let right_strip = d.lemma(p.zero_add, &[negated_a]);
        let (_, right_chain) = rchain(
            d,
            right_start,
            &[
                (right_swapped, right_swap),
                (right_flat, right_flatten),
                (right_zeroed, right_vanish),
                (negated_a, right_strip),
            ],
        );

        let at_left =
            super::ops::rat_eq_rewrite(d, left_start, negated_b, left_chain, scaled, &|d, x| {
                rle(d, p, x, right_start)
            });
        let body =
            super::ops::rat_eq_rewrite(d, right_start, negated_a, right_chain, at_left, &|d, x| {
                rle(d, p, negated_b, x)
            });
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })
}

/// Subtraction: `a − a = 0`, `−(a − b) = b − a`, and the telescoping identity
/// `(a − b) + (b − c) = a − c`.
///
/// All three are stated with `Rat.sub` and proved in the `add`/`neg` form it
/// unfolds to, which is why none of them needs an equation lemma.
fn declare_subtraction(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    // sub_self : sub a a = 0 — `sub a a` IS `a + (-a)`, so this is `add_neg`.
    rat_theorem(d, p.sub_self, 1, &|d, v| {
        let a = v[0];
        let difference = rsub(d, p, a, a);
        let zero = rzero(d, p);
        let stmt = req(d, difference, zero);
        let proof = d.lemma(p.add_neg, &[a]);
        (stmt, proof)
    })?;

    // neg_sub : neg (sub a b) = sub b a.
    //   -(a + -b) = -a + --b = -a + b = b + -a
    rat_theorem(d, p.neg_sub, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let difference = rsub(d, p, a, b);
        let negated = rneg(d, difference);
        let target = rsub(d, p, b, a);
        let stmt = req(d, negated, target);

        let negated_b = rneg(d, b);
        let negated_a = rneg(d, a);
        let split = d.lemma(p.neg_add, &[a, negated_b]);
        let twice = rneg(d, negated_b);
        let opened = radd(d, negated_a, twice);
        let restored = radd(d, negated_a, b);
        let unfold = {
            let cancel = d.lemma(p.neg_neg, &[b]);
            rcongr(d, twice, b, cancel, &|d, t| radd(d, negated_a, t))
        };
        let commute = d.lemma(p.add_comm, &[negated_a, b]);
        let commuted = radd(d, b, negated_a);
        let (_, proof) = rchain(
            d,
            negated,
            &[(opened, split), (restored, unfold), (commuted, commute)],
        );
        (stmt, proof)
    })?;

    // sub_add_sub : (a - b) + (b - c) = a - c.
    //   (a + -b) + (b + -c) = a + (-b + (b + -c)) = a + ((-b + b) + -c)
    //                       = a + (0 + -c) = a + -c
    rat_theorem(d, p.sub_add_sub, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let left = rsub(d, p, a, b);
        let right = rsub(d, p, b, c);
        let total = radd(d, left, right);
        let target = rsub(d, p, a, c);
        let stmt = req(d, total, target);

        let negated_b = rneg(d, b);
        let negated_c = rneg(d, c);
        let zero = rzero(d, p);
        let inner = radd(d, negated_b, right);
        let nested = radd(d, a, inner);
        let regroup = d.lemma(p.add_assoc, &[a, negated_b, right]);
        let cancel_head = radd(d, negated_b, b);
        let flat_inner = radd(d, cancel_head, negated_c);
        let flatten = {
            let forward = d.lemma(p.add_assoc, &[negated_b, b, negated_c]);
            let back = rsymm(d, flat_inner, inner, forward);
            rcongr(d, inner, flat_inner, back, &|d, t| radd(d, a, t))
        };
        let zeroed_inner = radd(d, zero, negated_c);
        let vanish = {
            let cancel = d.lemma(p.neg_add_cancel, &[b]);
            let step = rcongr(d, cancel_head, zero, cancel, &|d, t| radd(d, t, negated_c));
            rcongr(d, flat_inner, zeroed_inner, step, &|d, t| radd(d, a, t))
        };
        let stripped = radd(d, a, negated_c);
        let strip = {
            let drop = d.lemma(p.zero_add, &[negated_c]);
            rcongr(d, zeroed_inner, negated_c, drop, &|d, t| radd(d, a, t))
        };
        let nested_flat = radd(d, a, flat_inner);
        let nested_zeroed = radd(d, a, zeroed_inner);
        let (_, proof) = rchain(
            d,
            total,
            &[
                (nested, regroup),
                (nested_flat, flatten),
                (nested_zeroed, vanish),
                (stripped, strip),
            ],
        );
        (stmt, proof)
    })
}

/// The triangle inequality and the two one-sided facts about the `|a| ≤ b`
/// encoding ADR-0468 uses.
///
/// `bounds_add : −p ≤ u → u ≤ p → −q ≤ v → v ≤ q → −(p+q) ≤ u+v ∧ u+v ≤ p+q`.
/// The upper half is `add_le_add` outright; the lower half is `add_le_add` on
/// the two negated bounds followed by `neg_add`, which is the only place the
/// encoding costs anything at all.
fn declare_bounds(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.bounds_add, 4, &|d, v| {
        let (u, pp, vv, q) = (v[0], v[1], v[2], v[3]);
        let negated_p = rneg(d, pp);
        let negated_q = rneg(d, q);
        let sum = radd(d, u, vv);
        let total = radd(d, pp, q);
        let negated_total = rneg(d, total);
        let lower = rle(d, p, negated_total, sum);
        let upper = rle(d, p, sum, total);
        let conclusion = d.and(lower, upper);

        let h1_ty = rle(d, p, negated_p, u);
        let h2_ty = rle(d, p, u, pp);
        let h3_ty = rle(d, p, negated_q, vv);
        let h4_ty = rle(d, p, vv, q);
        let stmt = {
            let after_h4 = d.arrow(h4_ty, conclusion);
            let after_h3 = d.arrow(h3_ty, after_h4);
            let after_h2 = d.arrow(h2_ty, after_h3);
            d.arrow(h1_ty, after_h2)
        };

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h3_fv = d.fresh_fvar();
        let h3 = d.kernel().fvar(h3_fv);
        let h4_fv = d.fresh_fvar();
        let h4 = d.kernel().fvar(h4_fv);

        let upper_proof = d.lemma(p.add_le_add, &[u, pp, vv, q, h2, h4]);
        let negated_sum = radd(d, negated_p, negated_q);
        let lower_raw = d.lemma(p.add_le_add, &[negated_p, u, negated_q, vv, h1, h3]);
        let split = d.lemma(p.neg_add, &[pp, q]);
        let back = rsymm(d, negated_total, negated_sum, split);
        let lower_proof =
            super::ops::rat_eq_rewrite(d, negated_sum, negated_total, back, lower_raw, &|d, x| {
                rle(d, p, x, sum)
            });
        let pair = {
            let intro = p.int.logic.and_intro;
            d.const_app(intro, &[lower, upper, lower_proof, upper_proof])
        };
        let proof = {
            let with4 = d.lam_fv(h4_fv, h4_ty, pair);
            let with3 = d.lam_fv(h3_fv, h3_ty, with4);
            let with2 = d.lam_fv(h2_fv, h2_ty, with3);
            d.lam_fv(h1_fv, h1_ty, with2)
        };
        (stmt, proof)
    })?;

    // neg_nonpos_of_nonneg : 0 ≤ a → neg a ≤ 0.
    rat_theorem(d, p.neg_nonpos_of_nonneg, 1, &|d, v| {
        let a = v[0];
        let zero = rzero(d, p);
        let opposite = rneg(d, a);
        let hypothesis = rle(d, p, zero, a);
        let conclusion = rle(d, p, opposite, zero);
        let stmt = d.arrow(hypothesis, conclusion);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let flipped = d.lemma(p.neg_le_neg, &[zero, a, h]);
        let negated_zero = rneg(d, zero);
        let collapse = d.lemma(p.neg_zero, &[]);
        let body = super::ops::rat_eq_rewrite(d, negated_zero, zero, collapse, flipped, &|d, x| {
            rle(d, p, opposite, x)
        });
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })?;

    // add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b.
    rat_theorem(d, p.add_nonneg, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = rzero(d, p);
        let sum = radd(d, a, b);
        let first_ty = rle(d, p, zero, a);
        let second_ty = rle(d, p, zero, b);
        let conclusion = rle(d, p, zero, sum);
        let stmt = {
            let after_second = d.arrow(second_ty, conclusion);
            d.arrow(first_ty, after_second)
        };
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let raw = d.lemma(p.add_le_add, &[zero, a, zero, b, h1, h2]);
        let doubled = radd(d, zero, zero);
        let collapse = d.lemma(p.add_zero, &[zero]);
        let body =
            super::ops::rat_eq_rewrite(d, doubled, zero, collapse, raw, &|d, x| rle(d, p, x, sum));
        let proof = {
            let with2 = d.lam_fv(h2_fv, second_ty, body);
            d.lam_fv(h1_fv, first_ty, with2)
        };
        (stmt, proof)
    })?;

    // bounds_neg : -q ≤ r → r ≤ q → (-q ≤ -r ∧ -r ≤ q).
    //
    // Negating a two-sided bound keeps it, which is the whole of
    // `CReal.Equiv.symm` once `neg_sub` has turned `−(a − b)` into `b − a`.
    rat_theorem(d, p.bounds_neg, 2, &|d, v| {
        let (r, q) = (v[0], v[1]);
        let negated_q = rneg(d, q);
        let negated_r = rneg(d, r);
        let lower_ty = rle(d, p, negated_q, r);
        let upper_ty = rle(d, p, r, q);
        let lower = rle(d, p, negated_q, negated_r);
        let upper = rle(d, p, negated_r, q);
        let conclusion = d.and(lower, upper);
        let stmt = {
            let after_upper = d.arrow(upper_ty, conclusion);
            d.arrow(lower_ty, after_upper)
        };
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let lower_proof = d.lemma(p.neg_le_neg, &[r, q, h2]);
        let upper_raw = d.lemma(p.neg_le_neg, &[negated_q, r, h1]);
        let twice = rneg(d, negated_q);
        let cancel = d.lemma(p.neg_neg, &[q]);
        let upper_proof = super::ops::rat_eq_rewrite(d, twice, q, cancel, upper_raw, &|d, x| {
            rle(d, p, negated_r, x)
        });
        let pair = {
            let intro = p.int.logic.and_intro;
            d.const_app(intro, &[lower, upper, lower_proof, upper_proof])
        };
        let proof = {
            let with2 = d.lam_fv(h2_fv, upper_ty, pair);
            d.lam_fv(h1_fv, lower_ty, with2)
        };
        (stmt, proof)
    })
}

/// The two facts about `Rat.natDivSucc` that are about the **representation**
/// rather than about the group: same-denominator additivity, and
/// nonnegativity.
///
/// `natDivSucc_add` is what makes ADR-0468's bookkeeping close — Bishop's
/// estimate produces `1/(n+1) + 1/(j+1) + 2/(j+1) + 2/(j+1) + 1/(j+1) + 1/(n+1)`
/// and the Archimedean lemma consumes `2/(n+1) + 6/(j+1)`, so the six terms have
/// to fuse in two groups.
fn declare_representation(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let nat = p.int.nat;
    let nat_ty = d.nat_ty();

    // natDivSucc_add : a/(j+1) + b/(j+1) = (a+b)/(j+1).
    //
    // `normalize_add_normalize` fuses the two into
    // `normalize (a·S + b·S) (S·S)`, and `normalize_congr` reduces the claim to
    // one identity in ℤ: `(a·S + b·S)·S = (a+b)·(S·S)`.
    super::archimedean::mixed_theorem(
        d,
        p.nat_div_succ_add,
        &[nat_ty, nat_ty, nat_ty],
        &|d, v| {
            let (a, b, j) = (v[0], v[1], v[2]);
            let left = d.const_app(p.nat_div_succ, &[a, j]);
            let right = d.const_app(p.nat_div_succ, &[b, j]);
            let total = radd(d, left, right);
            let combined = NatOps::add(d, a, b);
            let target = d.const_app(p.nat_div_succ, &[combined, j]);
            let stmt = req(d, total, target);

            let denominator = d.succ(j);
            let positive = one_le_succ(d, j);
            let a_z = d.of_nat(a);
            let b_z = d.of_nat(b);
            let denominator_z = d.of_nat(denominator);
            let scaled_a = d.imul(a_z, denominator_z);
            let scaled_b = d.imul(b_z, denominator_z);
            let numerator = d.iadd(scaled_a, scaled_b);
            let square = NatOps::mul(d, denominator, denominator);
            let square_positive = d.lemma(
                nat.one_le_mul,
                &[denominator, denominator, positive, positive],
            );
            let fused = normalize(d, numerator, square, square_positive);
            let fuse = d.lemma(
                p.normalize_add_normalize,
                &[a_z, denominator, positive, b_z, denominator, positive],
            );

            // `(a·S + b·S)·S = (a+b)·(S·S)`.
            let combined_z = d.of_nat(combined);
            let square_z = d.of_nat(square);
            let cross_left = d.imul(numerator, denominator_z);
            let cross_right = d.imul(combined_z, square_z);
            let factored = d.imul(combined_z, denominator_z);
            let factor = {
                let expand = d.lemma(p.int_right_distrib, &[a_z, b_z, denominator_z]);
                d.isymm(factored, numerator, expand)
            };
            let lifted_factor = d.icongr(numerator, factored, factor, &|d, t| {
                d.imul(t, denominator_z)
            });
            let regrouped = {
                let inner = d.imul(denominator_z, denominator_z);
                d.imul(combined_z, inner)
            };
            let regroup = d.lemma(int.mul_assoc, &[combined_z, denominator_z, denominator_z]);
            let flat = d.imul(factored, denominator_z);
            let (_, cross) = d.ichain(cross_left, &[(flat, lifted_factor), (regrouped, regroup)]);
            let _ = cross_right;
            let congr = d.lemma(
                p.normalize_congr,
                &[
                    numerator,
                    square,
                    square_positive,
                    combined_z,
                    denominator,
                    positive,
                    cross,
                ],
            );
            let (_, proof) = rchain(d, total, &[(fused, fuse), (target, congr)]);
            (stmt, proof)
        },
    )?;

    // zero_le_natDivSucc : 0 ≤ k/(j+1).
    //
    // `normalize_cross` says `num r · S = ofNat k · ofNat (den r)`, whose right
    // side is `ofNat (k · den r)` and therefore nonnegative; cancelling the
    // positive `S` leaves `0 ≤ num r`, which is the bridge's hypothesis.
    super::archimedean::mixed_theorem(d, p.zero_le_nat_div_succ, &[nat_ty, nat_ty], &|d, v| {
        let (k, j) = (v[0], v[1]);
        let value = d.const_app(p.nat_div_succ, &[k, j]);
        let zero_rat = rzero(d, p);
        let stmt = rle(d, p, zero_rat, value);

        let numerator = d.of_nat(k);
        let denominator = d.succ(j);
        let positive = one_le_succ(d, j);
        let representative = normalize(d, numerator, denominator, positive);
        let actual = num(d, representative);
        let actual_den = super::ops::den(d, representative);
        let actual_den_z = super::ops::den_z(d, representative);
        let denominator_z = d.of_nat(denominator);
        let zero = d.izero();

        let cross = d.lemma(p.normalize_cross, &[numerator, denominator, positive]);
        let product = d.imul(numerator, actual_den_z);
        let product_nonneg = {
            let magnitude = NatOps::mul(d, k, actual_den);
            d.lemma(p.int_zero_le_of_nat, &[magnitude])
        };
        let scaled = d.imul(actual, denominator_z);
        let back = d.isymm(scaled, product, cross);
        let scaled_nonneg = d.int_eq_rewrite(product, scaled, back, product_nonneg, &|d, x| {
            d.ile(zero, x)
        });
        let zero_scaled = d.imul(zero, denominator_z);
        let restore = d.lemma(p.int_zero_mul, &[denominator_z]);
        let rebalanced = {
            let inverse = d.isymm(zero_scaled, zero, restore);
            d.int_eq_rewrite(zero, zero_scaled, inverse, scaled_nonneg, &|d, x| {
                d.ile(x, scaled)
            })
        };
        let cancelled = d.lemma(
            p.int_le_of_mul_le_mul_right,
            &[zero, actual, denominator, positive, rebalanced],
        );
        let proof = d.const_app(p.nonneg_of_int_nonneg, &[value, cancelled]);
        (stmt, proof)
    })?;

    Ok(())
}

// --- sums, as multisets of summands -----------------------------------------
//
// The mirror image of `super::ops::iprod` and friends, at `Rat.add` instead of
// `Int.mul`. It exists for exactly one reason, and the reason is worth stating
// because it is the shape of the whole real construction: Bishop's estimate
// produces
//
//     (1/(n+1) + 1/(j+1)) + (2/(j+1) + (2/(j+1) + (1/(j+1) + 1/(n+1))))
//
// and the Archimedean lemma consumes `2/(n+1) + 6/(j+1)`. Those are the same
// rational, but the kernel does not know that a sum is a multiset — and doing
// the reassociation inline is where a proof of this size goes wrong silently.
// `rsum_perm` panics on a non-permutation, so a mis-derived rearrangement fails
// with a Rust message naming the two lists rather than as an opaque
// `TypeMismatch` a thousand terms deep.

/// `a0 + (a1 + (… + a_{n-1}))`, right-nested.
///
/// # Panics
///
/// Panics on an empty summand list — a sum with no summands would need a unit
/// and nothing here ever wants one.
pub(crate) fn rsum(d: &mut IntDev<'_>, p: RatPrelude, atoms: &[ExprId]) -> ExprId {
    let _ = p;
    let (&last, front) = atoms.split_last().expect("a sum needs a summand");
    let mut acc = last;
    for &atom in front.iter().rev() {
        acc = radd(d, atom, acc);
    }
    acc
}

/// `Eq Rat (rsum xs) (xs[i] + rsum rest)`, where `rest` is `xs` with position
/// `i` removed. Requires `xs.len() >= 2`.
fn rsum_pull(d: &mut IntDev<'_>, p: RatPrelude, xs: &[ExprId], i: usize) -> ExprId {
    if i == 0 {
        let whole = rsum(d, p, xs);
        return super::ops::rrefl(d, whole);
    }
    let head = xs[0];
    let tail = &xs[1..];
    let chosen = xs[i];
    if tail.len() == 1 {
        return d.lemma(p.add_comm, &[head, chosen]);
    }
    let mut tail_rest: Vec<ExprId> = tail.to_vec();
    tail_rest.remove(i - 1);
    let inner = rsum_pull(d, p, tail, i - 1);
    let tail_sum = rsum(d, p, tail);
    let rest_sum = rsum(d, p, &tail_rest);
    let pulled = radd(d, chosen, rest_sum);
    let first = rcongr(d, tail_sum, pulled, inner, &|d, t| radd(d, head, t));
    let nested = radd(d, head, pulled);
    let flat_head = radd(d, head, chosen);
    let flat = radd(d, flat_head, rest_sum);
    let assoc = d.lemma(p.add_assoc, &[head, chosen, rest_sum]);
    let second = rsymm(d, flat, nested, assoc);
    let commuted_head = radd(d, chosen, head);
    let commute = d.lemma(p.add_comm, &[head, chosen]);
    let third = rcongr(d, flat_head, commuted_head, commute, &|d, t| {
        radd(d, t, rest_sum)
    });
    let commuted = radd(d, commuted_head, rest_sum);
    let fourth = d.lemma(p.add_assoc, &[chosen, head, rest_sum]);
    let regrouped = {
        let inner_sum = radd(d, head, rest_sum);
        radd(d, chosen, inner_sum)
    };
    let start = radd(d, head, tail_sum);
    let (_, chained) = rchain(
        d,
        start,
        &[
            (nested, first),
            (flat, second),
            (commuted, third),
            (regrouped, fourth),
        ],
    );
    chained
}

/// `Eq Rat (rsum xs) (rsum ys)` when `ys` is a permutation of `xs`.
///
/// # Panics
///
/// Panics if `ys` is not a permutation of `xs` — that is a bug in the caller,
/// not a provable-or-not question, and the kernel would reject the term anyway.
pub(crate) fn rsum_perm(d: &mut IntDev<'_>, p: RatPrelude, xs: &[ExprId], ys: &[ExprId]) -> ExprId {
    assert_eq!(xs.len(), ys.len(), "rsum_perm needs equal lengths");
    if xs.len() == 1 {
        assert_eq!(xs[0], ys[0], "rsum_perm was given a non-permutation");
        let single = xs[0];
        return super::ops::rrefl(d, single);
    }
    let index = xs
        .iter()
        .position(|&atom| atom == ys[0])
        .expect("rsum_perm was given a non-permutation");
    let mut rest: Vec<ExprId> = xs.to_vec();
    rest.remove(index);
    let pulled = rsum_pull(d, p, xs, index);
    let inner = rsum_perm(d, p, &rest, &ys[1..]);
    let rest_sum = rsum(d, p, &rest);
    let tail_sum = rsum(d, p, &ys[1..]);
    let chosen = ys[0];
    let middle = radd(d, chosen, rest_sum);
    let step = rcongr(d, rest_sum, tail_sum, inner, &|d, t| radd(d, chosen, t));
    let start = rsum(d, p, xs);
    let target = rsum(d, p, ys);
    let (_, chained) = rchain(d, start, &[(middle, pulled), (target, step)]);
    chained
}

/// `Eq Rat ((rsum xs) + (rsum ys)) (rsum (xs ++ ys))`.
pub(crate) fn rsum_append(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    xs: &[ExprId],
    ys: &[ExprId],
) -> ExprId {
    if xs.len() == 1 {
        let head = xs[0];
        let tail = rsum(d, p, ys);
        let joined = radd(d, head, tail);
        return super::ops::rrefl(d, joined);
    }
    let head = xs[0];
    let rest = &xs[1..];
    let rest_sum = rsum(d, p, rest);
    let ys_sum = rsum(d, p, ys);
    let xs_sum = rsum(d, p, xs);
    let start = radd(d, xs_sum, ys_sum);
    let opened = d.lemma(p.add_assoc, &[head, rest_sum, ys_sum]);
    let inner_start = radd(d, rest_sum, ys_sum);
    let nested = radd(d, head, inner_start);
    let joined_rest: Vec<ExprId> = rest.iter().chain(ys.iter()).copied().collect();
    let rest_joined = rsum(d, p, &joined_rest);
    let inner = rsum_append(d, p, rest, ys);
    let step = rcongr(d, inner_start, rest_joined, inner, &|d, t| radd(d, head, t));
    let target = radd(d, head, rest_joined);
    let (_, chained) = rchain(d, start, &[(nested, opened), (target, step)]);
    chained
}
