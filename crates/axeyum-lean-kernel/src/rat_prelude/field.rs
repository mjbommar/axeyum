//! **ℚ is a field**: the one law that makes `Rat.inv` an inverse, and the
//! ordered-field toolkit derived from it (ADR-0510, phase F2).
//!
//! ## What was missing, and why it was not noticed
//!
//! [`Rat.inv`](super::RatPrelude::inv) has existed since the rational prelude
//! was first built, as a *definition* — a three-way dispatch on the sign of the
//! numerator, with `inv 0 = 0` by the usual total convention. Nothing anywhere
//! said it inverts anything. `Rat.div` is defined through it, and it too was
//! unconstrained. So the development had 22 ordered-**ring** laws and an
//! operation named `inv`, and the gap between those two is exactly the gap
//! between a ring and a field.
//!
//! [`Rat.mul_inv_cancel`](super::RatPrelude::mul_inv_cancel) closes it:
//! `0 < q → q · q⁻¹ = 1`. Everything else in this module is derived from that
//! and the 22 laws alone, in `group`'s style — no numerator, no denominator, no
//! cross-multiplication — so each is a theorem of ordered fields that
//! [`crate::creal`] can transcribe one level up.
//!
//! ## The one proof that is about the representation
//!
//! `mul_inv_cancel` cannot be. `Rat.inv q` is stuck until `Rat.num q` is in
//! constructor form, so the proof is a three-way case split on the numerator
//! (`Int.rec` under a `Nat.rec`), with the two bad branches killed by the
//! positivity hypothesis:
//!
//! - `num q = ofNat 0` — then `q = 0` by
//!   [`eq_zero_of_num_zero`](super::RatPrelude::eq_zero_of_num_zero), and
//!   `0 < 0` is refuted by `lt_irrefl`;
//! - `num q = negSucc m` — then `Int.lt Int.zero (negSucc m)` **ι-reduces to
//!   `False`**, because `Int.lt` is a four-case definition and this is the
//!   mixed-constructor case. No lemma is needed, only `False.rec`.
//!
//! The surviving branch `num q = ofNat (k+1)` has `q⁻¹ = normalize (den q)
//! (k+1)`, and the identity is three cross-multiplications composed:
//!
//! ```text
//! num q · num q⁻¹ = ofNat (k+1) · num q⁻¹        (the branch equation)
//!                 = ofNat (den q) · ofNat (den q⁻¹)   (normalize_cross)
//!                 = ofNat (den q · den q⁻¹)           (Int.mul of two ofNats, by ι)
//! ```
//!
//! and then [`mul_cross`](super::RatPrelude::mul_cross) reads the left-hand
//! side as `num (q·q⁻¹) · ofNat (den q · den q⁻¹)`, so cancelling that positive
//! factor ([`int_mul_right_cancel`](super::RatPrelude::int_mul_right_cancel),
//! whose positivity is `Nat.one_le_mul` of the two denominators) leaves
//! `num (q·q⁻¹) = ofNat (den (q·q⁻¹))` — which is
//! [`eq_of_cross`](super::RatPrelude::eq_of_cross) against `1 = 1/1`.
//!
//! **`Rat.inv`'s dispatch is not duplicated here.** `super::defs::inv_body` is
//! the shared term builder, and `Rat.inv q` is `inv_body q (num q)` by
//! definition, so the motive of the case split mentions the same construction
//! the definition does rather than a transcription of it.
//!
//! ## Why the hypothesis is `0 < q` and not `q ≠ 0`
//!
//! Over `ℚ` the two are interchangeable — `Rat.le_or_lt` is *proved*, so the
//! order is decidable and a `q ≠ 0` version is one case split away. They are
//! **not** interchangeable one level up, which is the whole difficulty of the
//! real inverse (see [`crate::creal::field`]), and stating the rational law
//! positively is what lets the real construction consume it without ever
//! needing a sign decision it cannot make.
//!
//! `Rat.mul_inv_cancel` itself still only covers `q > 0`.
//! [`Rat.mul_inv_cancel_of_neg`](super::RatPrelude::mul_inv_cancel_of_neg) is
//! the companion for `q < 0` — a **second**, independent three-way case split
//! on `Rat.num q`, not a reduction to this one via
//! `inv q = -(inv (-q))`: that identity needs `Rat.normalize` to interact with
//! a negated numerator, which is exactly as representation-heavy to establish
//! as the companion theorem is directly, so reducing to it buys nothing.
//! Together the two cover every `q ≠ 0` (decidably, via `Rat.lt_trichotomy`),
//! and `Rat.inv`'s value at `q = 0` remains the only case with no cancellation
//! law — the usual total-operator convention, not a gap.

use super::RatPrelude;
use super::defs::inv_body;
use super::group::rsub;
use super::ops::{
    den, den_pos, den_z, nat_eq_to_rat, nat_rewrite_prop, normalize, num, one_le_succ, radd,
    rat_eq_rewrite, rat_theorem, rat_ty, rchain, rcongr, req, rle, rlt, rmul, rone, rsymm, rtrans,
    rzero,
};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.IsField`: above everything else this prelude has
/// declared by the time `field::declare_field_laws` runs (`POLY_EVAL_HEIGHT`,
/// 43, is the highest constant any `rat_prelude` module uses), following the
/// same "single monotone sequence over the whole prelude" convention
/// `probability.rs`'s own height constants document — even though `IsField`'s
/// value never unfolds through a named `Definition` (its six operations are
/// caller-supplied free variables, never called), so no earlier height is
/// actually reachable from it.
const FIELD_HEIGHT: u16 = 44;

/// Admit `Rat.mul_inv_cancel` and the ordered-field lemmas derived from it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_field_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_mul_inv_cancel(d, p)?;
    declare_mul_inv_cancel_of_neg(d, p)?;
    declare_mul_inv_cancel_of_ne_zero(d, p)?;
    declare_inv_pos(d, p)?;
    declare_sub_mul(d, p)?;
    declare_inverse_identities(d, p)?;
    declare_inv_antitone(d, p)?;
    declare_mul_pos(d, p)?;
    declare_nat_div_succ_pos(d, p)?;
    declare_inv_nat_div_succ(d, p)?;
    declare_one_ne_zero(d, p)?;
    declare_is_field(d, &p)?;
    declare_rat_is_field(d, p)?;
    declare_mul_left_cancel_of_ne_zero(d, p)?;
    declare_is_ordered_field(d, &p)?;
    declare_rat_is_ordered_field(d, p)
}

/// `Rat.mul_pos : ∀ a b, 0 < a → 0 < b → 0 < a·b`.
///
/// Not one of the 22: they give `mul_nonneg` (`0 ≤ a → 0 ≤ b → 0 ≤ a·b`) and
/// stop there, and the strict version does **not** follow from it by any
/// rearrangement — `0 ≤ a·b` holds of the zero product too. It follows from the
/// *inverse*: were `a·b ≤ 0`, scaling by the nonnegative `a⁻¹` would give
/// `b = a⁻¹·(a·b) ≤ a⁻¹·0 = 0`, contradicting `0 < b`. The case split is
/// [`Rat.le_or_lt`](super::RatPrelude::le_or_lt), which is proved.
///
/// So this is a lemma a *field* has and a ring does not, which is why it lands
/// here rather than in `laws`.
fn declare_mul_pos(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.mul_pos, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = rzero(d, p);
        let one = rone(d, p);
        let left_hypothesis = rlt(d, p, zero, a);
        let right_hypothesis = rlt(d, p, zero, b);
        let product = rmul(d, a, b);
        let claim = rlt(d, p, zero, product);
        let stmt = {
            let inner = d.arrow(right_hypothesis, claim);
            d.arrow(left_hypothesis, inner)
        };

        let la_fv = d.fresh_fvar();
        let la = d.kernel().fvar(la_fv);
        let lb_fv = d.fresh_fvar();
        let lb = d.kernel().fvar(lb_fv);

        let nonpositive = rle(d, p, product, zero);
        let positive = rlt(d, p, zero, product);
        let decision = d.lemma(p.le_or_lt, &[product, zero]);
        let body = d.or_elim(
            nonpositive,
            positive,
            claim,
            decision,
            &|d, bounded| {
                let reciprocal = d.const_app(p.inv, &[a]);
                let reciprocal_positive = d.lemma(p.inv_pos, &[a, la]);
                let reciprocal_nonneg =
                    d.lemma(p.le_of_lt, &[zero, reciprocal, reciprocal_positive]);
                let scaled = d.lemma(
                    p.mul_le_mul_of_nonneg_left,
                    &[reciprocal, product, zero, reciprocal_nonneg, bounded],
                );

                // `a⁻¹·(a·b) = b`.
                let left = rmul(d, reciprocal, product);
                let head = rmul(d, reciprocal, a);
                let regrouped = rmul(d, head, b);
                let regroup = {
                    let forward = d.lemma(p.mul_assoc, &[reciprocal, a, b]);
                    rsymm(d, regrouped, left, forward)
                };
                let flipped = rmul(d, a, reciprocal);
                let commuted = rmul(d, flipped, b);
                let commute = {
                    let swap = d.lemma(p.mul_comm, &[reciprocal, a]);
                    rcongr(d, head, flipped, swap, &|d, t| rmul(d, t, b))
                };
                let unit = rmul(d, one, b);
                let cancel = {
                    let law = d.lemma(p.mul_inv_cancel, &[a, la]);
                    rcongr(d, flipped, one, law, &|d, t| rmul(d, t, b))
                };
                let strip = one_mul(d, p, b);
                let (_, to_b) = rchain(
                    d,
                    left,
                    &[
                        (regrouped, regroup),
                        (commuted, commute),
                        (unit, cancel),
                        (b, strip),
                    ],
                );

                // `a⁻¹·0 = 0`.
                let right = rmul(d, reciprocal, zero);
                let annihilate = d.lemma(p.mul_zero, &[reciprocal]);

                let at_left = rat_eq_rewrite(d, left, b, to_b, scaled, &|d, t| rle(d, p, t, right));
                let at_right =
                    rat_eq_rewrite(d, right, zero, annihilate, at_left, &|d, t| rle(d, p, b, t));
                let degenerate = d.lemma(p.lt_of_lt_of_le, &[zero, b, zero, lb, at_right]);
                let refuted = d.lemma(p.lt_irrefl, &[zero]);
                let contradiction = d.apply(refuted, &[degenerate]);
                d.absurd(claim, contradiction)
            },
            &|_d, strict| strict,
        );
        let proof = {
            let with_b = d.lam_fv(lb_fv, right_hypothesis, body);
            d.lam_fv(la_fv, left_hypothesis, with_b)
        };
        (stmt, proof)
    })
}

/// `Rat.natDivSucc_pos : ∀ (k j : Nat), 1 ≤ k → 0 < k/(j+1)`.
///
/// The **strict** companion of
/// [`zero_le_natDivSucc`](super::RatPrelude::zero_le_nat_div_succ), and the
/// same proof with `le` replaced by `lt` throughout: `normalize_cross` reads
/// `num r · (j+1)` as `ofNat (k · den r)`, which is positive because both
/// factors are, and cancelling the positive `(j+1)` leaves `0 < num r`.
///
/// It exists because the real inverse's domain is stated as
/// `1/(k+1) ≤ x`, and turning that back into `0 < x` needs the rational bound
/// to be strictly positive — the non-strict version would make the witnessed
/// form of positivity strictly weaker than positivity.
fn declare_nat_div_succ_pos(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = p.int.nat;
    let nat_ty = d.nat_ty();
    super::archimedean::mixed_theorem(d, p.nat_div_succ_pos, &[nat_ty, nat_ty], &|d, v| {
        let (k, j) = (v[0], v[1]);
        let value = d.const_app(p.nat_div_succ, &[k, j]);
        let zero_rat = rzero(d, p);
        let positive_hypothesis = {
            let unit = d.num(1);
            NatOps::le(d, unit, k)
        };
        let claim = rlt(d, p, zero_rat, value);
        let stmt = d.arrow(positive_hypothesis, claim);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let numerator = d.of_nat(k);
        let denominator = d.succ(j);
        let positive = one_le_succ(d, j);
        let representative = normalize(d, numerator, denominator, positive);
        let actual = num(d, representative);
        let actual_den = den(d, representative);
        let actual_den_z = d.of_nat(actual_den);
        let denominator_z = d.of_nat(denominator);
        let zero = d.izero();

        // `num r · (j+1) = ofNat k · ofNat (den r) = ofNat (k · den r) > 0`.
        let cross = d.lemma(p.normalize_cross, &[numerator, denominator, positive]);
        let product = d.imul(numerator, actual_den_z);
        let product_positive = {
            let magnitude = NatOps::mul(d, k, actual_den);
            let den_positive = den_pos(d, representative);
            let magnitude_positive = d.lemma(nat.one_le_mul, &[k, actual_den, h, den_positive]);
            d.lemma(p.int_of_nat_pos, &[magnitude, magnitude_positive])
        };
        let scaled = d.imul(actual, denominator_z);
        let back = d.isymm(scaled, product, cross);
        let scaled_positive = d.int_eq_rewrite(product, scaled, back, product_positive, &|d, x| {
            d.ilt(zero, x)
        });
        let zero_scaled = d.imul(zero, denominator_z);
        let restore = d.lemma(p.int_zero_mul, &[denominator_z]);
        let rebalanced = {
            let inverse = d.isymm(zero_scaled, zero, restore);
            d.int_eq_rewrite(zero, zero_scaled, inverse, scaled_positive, &|d, x| {
                d.ilt(x, scaled)
            })
        };
        let cancelled = d.lemma(
            p.int_lt_of_mul_lt_mul_right,
            &[zero, actual, denominator, positive, rebalanced],
        );

        // `0 < num r` IS `0 < r`, after unpadding both cross-products.
        let unit_nat = d.num(1);
        let unit = d.of_nat(unit_nat);
        let padded_right = d.imul(actual, unit);
        let strip_right = d.lemma(p.int.mul_one, &[actual]);
        let at_right = {
            let inverse = d.isymm(padded_right, actual, strip_right);
            d.int_eq_rewrite(actual, padded_right, inverse, cancelled, &|d, x| {
                d.ilt(zero, x)
            })
        };
        let padded_left = d.imul(zero, actual_den_z);
        let strip_left = d.lemma(p.int_zero_mul, &[actual_den_z]);
        let at_left = {
            let inverse = d.isymm(padded_left, zero, strip_left);
            d.int_eq_rewrite(zero, padded_left, inverse, at_right, &|d, x| {
                d.ilt(x, padded_right)
            })
        };
        let proof = d.lam_fv(h_fv, positive_hypothesis, at_left);
        (stmt, proof)
    })
}

/// `1 · a = a`, as a proof term. There is no `Rat.one_mul` — the 22 name
/// `mul_one` only — and every rearrangement below needs the other side.
fn one_mul(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId) -> ExprId {
    let one = rone(d, p);
    let start = rmul(d, one, a);
    let flipped = rmul(d, a, one);
    let commute = d.lemma(p.mul_comm, &[one, a]);
    let collapse = d.lemma(p.mul_one, &[a]);
    let (_, proof) = rchain(d, start, &[(flipped, commute), (a, collapse)]);
    proof
}

/// `Rat.sub_mul : ∀ a b w, (a·w) − (b·w) = (a − b)·w`.
///
/// The right-hand distributive law over a difference, and it is
/// [`mul_sub_mul`](super::RatPrelude::mul_sub_mul) with its first summand
/// collapsed: `a·(w − w)` is `a·0` is `0`. Everything else in this module is a
/// rearrangement on top of it.
fn declare_sub_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.sub_mul, 3, &|d, v| {
        let (a, b, w) = (v[0], v[1], v[2]);
        let zero = rzero(d, p);
        let left = rmul(d, a, w);
        let right = rmul(d, b, w);
        let start = rsub(d, p, left, right);
        let difference = rsub(d, p, a, b);
        let result = rmul(d, difference, w);
        let stmt = req(d, start, result);

        let residue = rsub(d, p, w, w);
        let head = rmul(d, a, residue);
        let split = d.lemma(p.mul_sub_mul, &[a, w, b, w]);
        let decomposed = radd(d, head, result);
        let vanishes = d.lemma(p.sub_self, &[w]);
        let annihilated = rmul(d, a, zero);
        let collapse_head = rcongr(d, residue, zero, vanishes, &|d, t| {
            let scaled = rmul(d, a, t);
            radd(d, scaled, result)
        });
        let with_zero_head = radd(d, annihilated, result);
        let kill = d.lemma(p.mul_zero, &[a]);
        let headless = radd(d, zero, result);
        let strip_head = rcongr(d, annihilated, zero, kill, &|d, t| radd(d, t, result));
        let unpad = d.lemma(p.zero_add, &[result]);
        let (_, proof) = rchain(
            d,
            start,
            &[
                (decomposed, split),
                (with_zero_head, collapse_head),
                (headless, strip_head),
                (result, unpad),
            ],
        );
        (stmt, proof)
    })
}

/// The two identities the real inverse's estimates are written in.
fn declare_inverse_identities(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    // mul_inv_sub_one : ∀ a b, 0 < b → a·b⁻¹ − 1 = (a − b)·b⁻¹.
    rat_theorem(d, p.mul_inv_sub_one, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = rzero(d, p);
        let one = rone(d, p);
        let hypothesis = rlt(d, p, zero, b);
        let reciprocal = d.const_app(p.inv, &[b]);
        let scaled = rmul(d, a, reciprocal);
        let start = rsub(d, p, scaled, one);
        let difference = rsub(d, p, a, b);
        let result = rmul(d, difference, reciprocal);
        let claim = req(d, start, result);
        let stmt = d.arrow(hypothesis, claim);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let unit = rmul(d, b, reciprocal);
        let cancel = d.lemma(p.mul_inv_cancel, &[b, h]);
        let reopen = {
            let back = rsymm(d, unit, one, cancel);
            rcongr(d, one, unit, back, &|d, t| rsub(d, p, scaled, t))
        };
        let paired = rsub(d, p, scaled, unit);
        let distribute = d.lemma(p.sub_mul, &[a, b, reciprocal]);
        let (_, chained) = rchain(d, start, &[(paired, reopen), (result, distribute)]);
        let proof = d.lam_fv(h_fv, hypothesis, chained);
        (stmt, proof)
    })?;

    // inv_sub_inv : ∀ a b, 0 < a → 0 < b → a⁻¹ − b⁻¹ = (b − a)·(a⁻¹·b⁻¹).
    rat_theorem(d, p.inv_sub_inv, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = rzero(d, p);
        let one = rone(d, p);
        let left_hypothesis = rlt(d, p, zero, a);
        let right_hypothesis = rlt(d, p, zero, b);
        let u = d.const_app(p.inv, &[a]);
        let w = d.const_app(p.inv, &[b]);
        let joint = rmul(d, u, w);
        let start = rsub(d, p, u, w);
        let difference = rsub(d, p, b, a);
        let result = rmul(d, difference, joint);
        let claim = req(d, start, result);
        let stmt = {
            let inner = d.arrow(right_hypothesis, claim);
            d.arrow(left_hypothesis, inner)
        };

        let la_fv = d.fresh_fvar();
        let la = d.kernel().fvar(la_fv);
        let lb_fv = d.fresh_fvar();
        let lb = d.kernel().fvar(lb_fv);

        // `b·(a⁻¹·b⁻¹) = a⁻¹`: regroup, cancel `b·b⁻¹`, strip the unit.
        let scaled_b = rmul(d, b, joint);
        let head_b = rmul(d, b, u);
        let regrouped_b = rmul(d, head_b, w);
        let regroup_b = {
            let forward = d.lemma(p.mul_assoc, &[b, u, w]);
            rsymm(d, regrouped_b, scaled_b, forward)
        };
        let flipped_b = rmul(d, u, b);
        let commuted_b = rmul(d, flipped_b, w);
        let commute_b = {
            let swap = d.lemma(p.mul_comm, &[b, u]);
            let head = rmul(d, b, u);
            let flipped = rmul(d, u, b);
            rcongr(d, head, flipped, swap, &|d, t| rmul(d, t, w))
        };
        let tail_b = rmul(d, b, w);
        let reassociated_b = rmul(d, u, tail_b);
        let reassociate_b = d.lemma(p.mul_assoc, &[u, b, w]);
        let unit_b = rmul(d, u, one);
        let cancel_b = {
            let inner = rmul(d, b, w);
            let law = d.lemma(p.mul_inv_cancel, &[b, lb]);
            rcongr(d, inner, one, law, &|d, t| rmul(d, u, t))
        };
        let strip_b = d.lemma(p.mul_one, &[u]);
        let (_, to_u) = rchain(
            d,
            scaled_b,
            &[
                (regrouped_b, regroup_b),
                (commuted_b, commute_b),
                (reassociated_b, reassociate_b),
                (unit_b, cancel_b),
                (u, strip_b),
            ],
        );

        // `a·(a⁻¹·b⁻¹) = b⁻¹`: regroup, cancel `a·a⁻¹`, strip the unit.
        let scaled_a = rmul(d, a, joint);
        let head_a = rmul(d, a, u);
        let regrouped_a = rmul(d, head_a, w);
        let regroup_a = {
            let forward = d.lemma(p.mul_assoc, &[a, u, w]);
            rsymm(d, regrouped_a, scaled_a, forward)
        };
        let unit_a = rmul(d, one, w);
        let cancel_a = {
            let head = rmul(d, a, u);
            let law = d.lemma(p.mul_inv_cancel, &[a, la]);
            rcongr(d, head, one, law, &|d, t| rmul(d, t, w))
        };
        let strip_a = one_mul(d, p, w);
        let (_, to_w) = rchain(
            d,
            scaled_a,
            &[(regrouped_a, regroup_a), (unit_a, cancel_a), (w, strip_a)],
        );

        // `a⁻¹ − b⁻¹ = b·joint − a·joint = (b − a)·joint`.
        let restored_left = {
            let back = rsymm(d, scaled_b, u, to_u);
            rcongr(d, u, scaled_b, back, &|d, t| rsub(d, p, t, w))
        };
        let half = rsub(d, p, scaled_b, w);
        let restored_right = {
            let back = rsymm(d, scaled_a, w, to_w);
            rcongr(d, w, scaled_a, back, &|d, t| rsub(d, p, scaled_b, t))
        };
        let paired = rsub(d, p, scaled_b, scaled_a);
        let distribute = d.lemma(p.sub_mul, &[b, a, joint]);
        let (_, chained) = rchain(
            d,
            start,
            &[
                (half, restored_left),
                (paired, restored_right),
                (result, distribute),
            ],
        );
        let proof = {
            let with_b = d.lam_fv(lb_fv, right_hypothesis, chained);
            d.lam_fv(la_fv, left_hypothesis, with_b)
        };
        (stmt, proof)
    })
}

/// `Rat.inv_le_of_pos_le : ∀ c a, 0 < c → c ≤ a → a⁻¹ ≤ c⁻¹`.
///
/// The inverse is **antitone on the positives**, which is the bound the real
/// inverse's regularity estimate needs: a sample bounded below by `1/(k+1)` has
/// a reciprocal bounded above by `k+1`. Derived from
/// [`mul_inv_cancel`](super::RatPrelude::mul_inv_cancel),
/// [`inv_pos`](super::RatPrelude::inv_pos) and the 22 laws alone — scale
/// `c ≤ a` by the nonnegative `a⁻¹·c⁻¹` and both sides collapse.
fn declare_inv_antitone(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.inv_le_of_pos_le, 2, &|d, v| {
        let (c, a) = (v[0], v[1]);
        let zero = rzero(d, p);
        let one = rone(d, p);
        let positive = rlt(d, p, zero, c);
        let ordered = rle(d, p, c, a);
        let u = d.const_app(p.inv, &[a]);
        let w = d.const_app(p.inv, &[c]);
        let claim = rle(d, p, u, w);
        let stmt = {
            let inner = d.arrow(ordered, claim);
            d.arrow(positive, inner)
        };

        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let ho_fv = d.fresh_fvar();
        let ho = d.kernel().fvar(ho_fv);

        let a_positive = d.lemma(p.lt_of_lt_of_le, &[zero, c, a, hp, ho]);
        let u_positive = d.lemma(p.inv_pos, &[a, a_positive]);
        let w_positive = d.lemma(p.inv_pos, &[c, hp]);
        let u_nonneg = d.lemma(p.le_of_lt, &[zero, u, u_positive]);
        let w_nonneg = d.lemma(p.le_of_lt, &[zero, w, w_positive]);
        let joint = rmul(d, u, w);
        let joint_nonneg = d.lemma(p.mul_nonneg, &[u, w, u_nonneg, w_nonneg]);
        let scaled = d.lemma(
            p.mul_le_mul_of_nonneg_left,
            &[joint, c, a, joint_nonneg, ho],
        );

        // `(a⁻¹·c⁻¹)·c = a⁻¹`.
        let left = rmul(d, joint, c);
        let tail_left = rmul(d, w, c);
        let reassociated_left = rmul(d, u, tail_left);
        let reassociate_left = d.lemma(p.mul_assoc, &[u, w, c]);
        let tail_left_flipped = rmul(d, c, w);
        let commuted_left = rmul(d, u, tail_left_flipped);
        let commute_left = {
            let inner = rmul(d, w, c);
            let flipped = rmul(d, c, w);
            let swap = d.lemma(p.mul_comm, &[w, c]);
            rcongr(d, inner, flipped, swap, &|d, t| rmul(d, u, t))
        };
        let unit_left = rmul(d, u, one);
        let cancel_left = {
            let inner = rmul(d, c, w);
            let law = d.lemma(p.mul_inv_cancel, &[c, hp]);
            rcongr(d, inner, one, law, &|d, t| rmul(d, u, t))
        };
        let strip_left = d.lemma(p.mul_one, &[u]);
        let (_, to_u) = rchain(
            d,
            left,
            &[
                (reassociated_left, reassociate_left),
                (commuted_left, commute_left),
                (unit_left, cancel_left),
                (u, strip_left),
            ],
        );

        // `(a⁻¹·c⁻¹)·a = c⁻¹`.
        let right = rmul(d, joint, a);
        let head_right = rmul(d, w, u);
        let swapped = rmul(d, head_right, a);
        let swap_head = {
            let flipped = rmul(d, w, u);
            let law = d.lemma(p.mul_comm, &[u, w]);
            rcongr(d, joint, flipped, law, &|d, t| rmul(d, t, a))
        };
        let tail_right = rmul(d, u, a);
        let reassociated_right = rmul(d, w, tail_right);
        let reassociate_right = d.lemma(p.mul_assoc, &[w, u, a]);
        let tail_right_flipped = rmul(d, a, u);
        let commuted_right = rmul(d, w, tail_right_flipped);
        let commute_right = {
            let inner = rmul(d, u, a);
            let flipped = rmul(d, a, u);
            let law = d.lemma(p.mul_comm, &[u, a]);
            rcongr(d, inner, flipped, law, &|d, t| rmul(d, w, t))
        };
        let unit_right = rmul(d, w, one);
        let cancel_right = {
            let inner = rmul(d, a, u);
            let law = d.lemma(p.mul_inv_cancel, &[a, a_positive]);
            rcongr(d, inner, one, law, &|d, t| rmul(d, w, t))
        };
        let strip_right = d.lemma(p.mul_one, &[w]);
        let (_, to_w) = rchain(
            d,
            right,
            &[
                (swapped, swap_head),
                (reassociated_right, reassociate_right),
                (commuted_right, commute_right),
                (unit_right, cancel_right),
                (w, strip_right),
            ],
        );

        let at_left = rat_eq_rewrite(d, left, u, to_u, scaled, &|d, t| rle(d, p, t, right));
        let at_right = rat_eq_rewrite(d, right, w, to_w, at_left, &|d, t| rle(d, p, u, t));
        let proof = {
            let with_order = d.lam_fv(ho_fv, ordered, at_right);
            d.lam_fv(hp_fv, positive, with_order)
        };
        (stmt, proof)
    })
}

/// `Rat.mul_inv_cancel : ∀ q, 0 < q → q · q⁻¹ = 1`.
fn declare_mul_inv_cancel(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let carrier = rat_ty(d);
    let nat_ty = d.nat_ty();
    let int_ty = d.int_ty();
    let prop_level = d.kernel().level_zero();

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let zero = rzero(d, p);
    let one = rone(d, p);
    let hypothesis = rlt(d, p, zero, q);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let numerator = num(d, q);
    let sign = d.lemma(p.int_pos_of_pos, &[q, h]);

    // `fun z => num q = z → q · (inv_body q z) = 1`, the motive of the split.
    let motive = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let equation = d.ieq(numerator, z);
        let reciprocal = inv_body(d, p, q, z);
        let product = rmul(d, q, reciprocal);
        let claim = req(d, product, one);
        let inner = d.arrow(equation, claim);
        d.lam_fv(z_fv, int_ty, inner)
    };

    // `num q = negSucc m` — `Int.lt Int.zero (negSucc m)` IS `False` by ι.
    let minor_neg_succ = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let target = d.neg_succ(m);
        let equation = d.ieq(numerator, target);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let reciprocal = inv_body(d, p, q, target);
        let product = rmul(d, q, reciprocal);
        let claim = req(d, product, one);
        let impossible = {
            let izero = d.izero();
            d.int_eq_rewrite(numerator, target, e, sign, &|d, x| d.ilt(izero, x))
        };
        let body = d.absurd(claim, impossible);
        let with_e = d.lam_fv(e_fv, equation, body);
        d.lam_fv(m_fv, nat_ty, with_e)
    };

    // `num q = ofNat n`, split again on `n`.
    let minor_of_nat = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let nat_motive = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let target = d.of_nat(j);
            let equation = d.ieq(numerator, target);
            let reciprocal = inv_body(d, p, q, target);
            let product = rmul(d, q, reciprocal);
            let claim = req(d, product, one);
            let inner = d.arrow(equation, claim);
            d.lam_fv(j_fv, nat_ty, inner)
        };

        // n = 0: the numerator vanishes, so `q = 0`, contradicting `0 < q`.
        let zero_case = {
            let nat_zero = d.zero();
            let target = d.of_nat(nat_zero);
            let equation = d.ieq(numerator, target);
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let reciprocal = inv_body(d, p, q, target);
            let product = rmul(d, q, reciprocal);
            let claim = req(d, product, one);
            let vanishes = d.lemma(p.eq_zero_of_num_zero, &[q, e]);
            let degenerate = rat_eq_rewrite(d, q, zero, vanishes, h, &|d, t| rlt(d, p, zero, t));
            let refuted = d.lemma(p.lt_irrefl, &[zero]);
            let contradiction = d.apply(refuted, &[degenerate]);
            let body = d.absurd(claim, contradiction);
            d.lam_fv(e_fv, equation, body)
        };

        // n = k+1: the real proof.
        let succ_case = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let ih_fv = d.fresh_fvar();
            let magnitude = d.succ(k);
            let target = d.of_nat(magnitude);
            let equation = d.ieq(numerator, target);
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);

            let body = cancel_at_positive_numerator(d, p, q, k, e);

            let with_e = d.lam_fv(e_fv, equation, body);
            let previous = {
                let j = d.kernel().fvar(k_fv);
                let target = d.of_nat(j);
                let inner_equation = d.ieq(numerator, target);
                let reciprocal = inv_body(d, p, q, target);
                let product = rmul(d, q, reciprocal);
                let claim = req(d, product, one);
                d.arrow(inner_equation, claim)
            };
            let with_ih = d.lam_fv(ih_fv, previous, with_e);
            d.lam_fv(k_fv, nat_ty, with_ih)
        };

        let rec_name = d.prelude().rec;
        let rec = d.kernel().const_(rec_name, vec![prop_level]);
        let body = d.apply(rec, &[nat_motive, zero_case, succ_case, n]);
        d.lam_fv(n_fv, nat_ty, body)
    };

    let rec = d.kernel().const_(int.rec, vec![prop_level]);
    let split = d.apply(rec, &[motive, minor_of_nat, minor_neg_succ, numerator]);
    let reflexive = d.irefl(numerator);
    let applied = d.apply(split, &[reflexive]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, applied);
        d.lam_fv(q_fv, carrier, with_h)
    };
    let ty = {
        let reciprocal = d.const_app(p.inv, &[q]);
        let product = rmul(d, q, reciprocal);
        let claim = req(d, product, one);
        let inner = d.arrow(hypothesis, claim);
        d.pi_fv(q_fv, carrier, inner)
    };
    d.kernel()
        .add_declaration(crate::env::Declaration::Theorem {
            name: p.mul_inv_cancel,
            uparams: vec![],
            ty,
            value,
        })
}

/// The surviving branch: `num q = ofNat (k+1)`, so `q⁻¹` **is**
/// `normalize (ofNat (den q)) (k+1)` and the identity is three
/// cross-multiplications and one cancellation.
fn cancel_at_positive_numerator(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    q: ExprId,
    k: ExprId,
    equation: ExprId,
) -> ExprId {
    let nat = p.int.nat;
    let int = p.int;
    let one = rone(d, p);
    let numerator = num(d, q);
    let denominator = den(d, q);

    let magnitude = d.succ(k);
    let target = d.of_nat(magnitude);
    let positive = one_le_succ(d, k);
    let lifted_den = d.of_nat(denominator);
    let reciprocal = normalize(d, lifted_den, magnitude, positive);

    let product = rmul(d, q, reciprocal);
    let product_num = num(d, product);
    let product_den = den(d, product);
    let lifted_product_den = d.of_nat(product_den);
    let reciprocal_num = num(d, reciprocal);
    let reciprocal_den = den(d, reciprocal);
    let lifted_reciprocal_den = d.of_nat(reciprocal_den);
    let common = NatOps::mul(d, denominator, reciprocal_den);
    let scale = d.of_nat(common);

    // (iii) `num q · num q⁻¹ = ofNat (den q · den q⁻¹)`.
    let cross_start = d.imul(numerator, reciprocal_num);
    let shifted = d.imul(target, reciprocal_num);
    let by_branch = d.icongr(numerator, target, equation, &|d, t| {
        d.imul(t, reciprocal_num)
    });
    let commuted_form = d.imul(reciprocal_num, target);
    let commute = d.lemma(int.mul_comm, &[target, reciprocal_num]);
    let normalized = d.imul(lifted_den, lifted_reciprocal_den);
    let by_normalize = d.lemma(p.normalize_cross, &[lifted_den, magnitude, positive]);
    let fuse = d.irefl(normalized);
    let (_, to_scale) = d.ichain(
        cross_start,
        &[
            (shifted, by_branch),
            (commuted_form, commute),
            (normalized, by_normalize),
            (scale, fuse),
        ],
    );

    // `num (q·q⁻¹) · ofNat (den q · den q⁻¹) = ofNat (den (q·q⁻¹)) · ofNat (…)`.
    let cancel_left = d.imul(product_num, scale);
    let via_cross = d.lemma(p.mul_cross, &[q, reciprocal]);
    let cross_image = d.imul(cross_start, lifted_product_den);
    let scaled_image = d.imul(scale, lifted_product_den);
    let by_scale = d.icongr(cross_start, scale, to_scale, &|d, t| {
        d.imul(t, lifted_product_den)
    });
    let cancel_right = d.imul(lifted_product_den, scale);
    let final_commute = d.lemma(int.mul_comm, &[scale, lifted_product_den]);
    let (_, cancellable) = d.ichain(
        cancel_left,
        &[
            (cross_image, via_cross),
            (scaled_image, by_scale),
            (cancel_right, final_commute),
        ],
    );

    // Cancel the positive `ofNat (den q · den q⁻¹)`.
    let den_q_positive = den_pos(d, q);
    let den_r_positive = den_pos(d, reciprocal);
    let common_positive = d.lemma(
        nat.one_le_mul,
        &[denominator, reciprocal_den, den_q_positive, den_r_positive],
    );
    let projections_agree = d.lemma(
        p.int_mul_right_cancel,
        &[
            product_num,
            lifted_product_den,
            common,
            common_positive,
            cancellable,
        ],
    );

    // `num (q·q⁻¹) · ofNat (den 1) = num 1 · ofNat (den (q·q⁻¹))`.
    let unit_nat = d.num(1);
    let unit = d.of_nat(unit_nat);
    let left = d.imul(product_num, unit);
    let strip_left = d.lemma(int.mul_one, &[product_num]);
    let (_, left_side) = d.ichain(
        left,
        &[
            (product_num, strip_left),
            (lifted_product_den, projections_agree),
        ],
    );
    let right = d.imul(unit, lifted_product_den);
    let flipped = d.imul(lifted_product_den, unit);
    let flip = d.lemma(int.mul_comm, &[unit, lifted_product_den]);
    let strip_right = d.lemma(int.mul_one, &[lifted_product_den]);
    let (_, right_side) = d.ichain(right, &[(flipped, flip), (lifted_product_den, strip_right)]);
    let back = d.isymm(right, lifted_product_den, right_side);
    let crossed = d.itrans(left, lifted_product_den, right, left_side, back);

    d.lemma(p.eq_of_cross, &[product, one, crossed])
}

/// `Int.lt (num q) Int.zero`, given `q < 0`.
///
/// The mirror of `int_pos_of_pos` (`archimedean.rs`): `Rat.lt q Rat.zero`
/// unfolds to `Int.lt (num q * ofNat (den Rat.zero)) (num Rat.zero * ofNat
/// (den q))`, and `int.mul_one`/`p.int_zero_mul` collapse the two sides —
/// exactly the rewrite `int_pos_of_pos` uses, with the two sides swapped
/// because the zero sits on the other side of `lt` here.
fn int_neg_of_neg(d: &mut IntDev<'_>, p: RatPrelude, q: ExprId, h: ExprId) -> ExprId {
    let int = p.int;
    let numerator = num(d, q);
    let zero = d.izero();
    let unit = d.ione();
    let denominator = den_z(d, q);
    let left_scaled = d.imul(numerator, unit);
    let right_scaled = d.imul(zero, denominator);
    let left_collapse = d.lemma(int.mul_one, &[numerator]);
    let right_collapse = d.lemma(p.int_zero_mul, &[denominator]);
    let at_left = d.int_eq_rewrite(left_scaled, numerator, left_collapse, h, &|d, x| {
        d.ilt(x, right_scaled)
    });
    d.int_eq_rewrite(right_scaled, zero, right_collapse, at_left, &|d, x| {
        d.ilt(numerator, x)
    })
}

/// The surviving branch of [`declare_mul_inv_cancel_of_neg`]: `num q =
/// negSucc m`, so `q⁻¹` **is** `normalize (Int.neg (ofNat (den q))) (m+1) _`.
///
/// Unlike [`cancel_at_positive_numerator`], `target` here (`negSucc m`) is
/// not itself `ofNat` of the magnitude `normalize_cross` multiplies by, so
/// that lemma cannot be read off the cross-product directly. Instead: scale
/// both sides of the wanted cross-equation by `ofNat (m+1)` (which *is* the
/// shape `normalize_cross` wants), collapse `negSucc m * negOfNat (den q)`
/// with `mul_neg_succ_neg_of_nat` (`Int.neg (ofNat (den q))` is `ι`-equal to
/// `negOfNat (den q)`, its exact left argument), then cancel the scale factor
/// back off with `int_mul_right_cancel`. Once `cross_start = scale` is in
/// hand the rest is identical to the positive branch.
fn cancel_at_negative_numerator(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    q: ExprId,
    m: ExprId,
    equation: ExprId,
) -> ExprId {
    let nat = p.int.nat;
    let int = p.int;
    let one = rone(d, p);
    let numerator = num(d, q);
    let denominator = den(d, q);

    let magnitude = d.succ(m);
    let target = d.neg_succ(m);
    let positive = one_le_succ(d, m);
    let lifted_den = d.of_nat(denominator);
    let negated_den = d.ineg(lifted_den);
    let reciprocal = normalize(d, negated_den, magnitude, positive);

    let product = rmul(d, q, reciprocal);
    let product_num = num(d, product);
    let product_den = den(d, product);
    let lifted_product_den = d.of_nat(product_den);
    let reciprocal_num = num(d, reciprocal);
    let reciprocal_den = den(d, reciprocal);
    let lifted_reciprocal_den = d.of_nat(reciprocal_den);
    let common = NatOps::mul(d, denominator, reciprocal_den);
    let scale = d.of_nat(common);

    // cross_start = numerator * reciprocal_num, rewritten via the branch
    // equation to `target * reciprocal_num`.
    let cross_start = d.imul(numerator, reciprocal_num);
    let shifted = d.imul(target, reciprocal_num);
    let by_branch = d.icongr(numerator, target, equation, &|d, t| {
        d.imul(t, reciprocal_num)
    });

    // Scale `shifted` by `ofNat magnitude` and reduce it to a plain `Nat`
    // cast, in lockstep with `scale * ofNat magnitude`.
    let magnitude_z = d.of_nat(magnitude);
    let shifted_scaled = d.imul(shifted, magnitude_z);

    let inner1 = d.imul(reciprocal_num, magnitude_z);
    let regrouped1 = d.imul(target, inner1);
    let regroup1 = d.lemma(int.mul_assoc, &[target, reciprocal_num, magnitude_z]);

    let inner2 = d.imul(negated_den, lifted_reciprocal_den);
    let regrouped2 = d.imul(target, inner2);
    let by_normalize = d.lemma(p.normalize_cross, &[negated_den, magnitude, positive]);
    let step2 = d.icongr(inner1, inner2, by_normalize, &|d, t| d.imul(target, t));

    let head = d.imul(target, negated_den);
    let regrouped3 = d.imul(head, lifted_reciprocal_den);
    let regroup2 = d.lemma(int.mul_assoc, &[target, negated_den, lifted_reciprocal_den]);
    let regroup2_symm = d.isymm(regrouped3, regrouped2, regroup2);

    let head_value = {
        let scaled_denominator = NatOps::mul(d, magnitude, denominator);
        d.of_nat(scaled_denominator)
    };
    let head_eq = d.lemma(int.mul_neg_succ_neg_of_nat, &[m, denominator]);
    let step4 = d.icongr(head, head_value, head_eq, &|d, t| {
        d.imul(t, lifted_reciprocal_den)
    });
    let final_left_raw = d.imul(head_value, lifted_reciprocal_den);

    let nat_grouped = {
        let scaled_denominator = NatOps::mul(d, magnitude, denominator);
        NatOps::mul(d, scaled_denominator, reciprocal_den)
    };
    let final_left_reduced = d.of_nat(nat_grouped);
    let fuse_left = d.irefl(final_left_reduced);

    let nat_target = NatOps::mul(d, common, magnitude);
    let scale_scaled_reduced = d.of_nat(nat_target);
    let rhs_target = d.imul(scale, magnitude_z);

    // Nat rearrangement: (magnitude*denominator)*reciprocal_den =
    // magnitude*common = common*magnitude.
    let magnitude_common = NatOps::mul(d, magnitude, common);
    let nat_eq1 = d.lemma(nat.mul_assoc, &[magnitude, denominator, reciprocal_den]);
    let nat_eq2 = d.lemma(nat.mul_comm, &[magnitude, common]);
    let (_, nat_eq_final) = d.chain(
        nat_grouped,
        &[(magnitude_common, nat_eq1), (nat_target, nat_eq2)],
    );
    let nat_lift = d.nat_eq_to_int(nat_grouped, nat_target, nat_eq_final, &|d, t| d.of_nat(t));
    let fuse_right = d.irefl(rhs_target);

    let (_, big_proof) = d.ichain(
        shifted_scaled,
        &[
            (regrouped1, regroup1),
            (regrouped2, step2),
            (regrouped3, regroup2_symm),
            (final_left_raw, step4),
            (final_left_reduced, fuse_left),
            (scale_scaled_reduced, nat_lift),
            (rhs_target, fuse_right),
        ],
    );

    let shifted_eq_scale = d.lemma(
        p.int_mul_right_cancel,
        &[shifted, scale, magnitude, positive, big_proof],
    );
    let to_scale = d.itrans(cross_start, shifted, scale, by_branch, shifted_eq_scale);

    // From here on, identical to `cancel_at_positive_numerator`: cancel the
    // shared positive denominator factor and close with `eq_of_cross`.
    let cancel_left = d.imul(product_num, scale);
    let via_cross = d.lemma(p.mul_cross, &[q, reciprocal]);
    let cross_image = d.imul(cross_start, lifted_product_den);
    let scaled_image = d.imul(scale, lifted_product_den);
    let by_scale = d.icongr(cross_start, scale, to_scale, &|d, t| {
        d.imul(t, lifted_product_den)
    });
    let cancel_right = d.imul(lifted_product_den, scale);
    let final_commute = d.lemma(int.mul_comm, &[scale, lifted_product_den]);
    let (_, cancellable) = d.ichain(
        cancel_left,
        &[
            (cross_image, via_cross),
            (scaled_image, by_scale),
            (cancel_right, final_commute),
        ],
    );

    let den_q_positive = den_pos(d, q);
    let den_r_positive = den_pos(d, reciprocal);
    let common_positive = d.lemma(
        nat.one_le_mul,
        &[denominator, reciprocal_den, den_q_positive, den_r_positive],
    );
    let projections_agree = d.lemma(
        p.int_mul_right_cancel,
        &[
            product_num,
            lifted_product_den,
            common,
            common_positive,
            cancellable,
        ],
    );

    let unit_nat = d.num(1);
    let unit = d.of_nat(unit_nat);
    let left = d.imul(product_num, unit);
    let strip_left = d.lemma(int.mul_one, &[product_num]);
    let (_, left_side) = d.ichain(
        left,
        &[
            (product_num, strip_left),
            (lifted_product_den, projections_agree),
        ],
    );
    let right = d.imul(unit, lifted_product_den);
    let flipped = d.imul(lifted_product_den, unit);
    let flip = d.lemma(int.mul_comm, &[unit, lifted_product_den]);
    let strip_right = d.lemma(int.mul_one, &[lifted_product_den]);
    let (_, right_side) = d.ichain(right, &[(flipped, flip), (lifted_product_den, strip_right)]);
    let back = d.isymm(right, lifted_product_den, right_side);
    let crossed = d.itrans(left, lifted_product_den, right, left_side, back);

    d.lemma(p.eq_of_cross, &[product, one, crossed])
}

/// `Rat.mul_inv_cancel_of_neg : ∀ q, q < 0 → q · q⁻¹ = 1` — the companion of
/// [`declare_mul_inv_cancel`] for a negative `q`.
///
/// A **second** three-way case split on `Rat.num q`, not a reduction to the
/// positive case via `Rat.inv (Rat.neg q) = Rat.neg (Rat.inv q)`: that
/// identity is exactly as representation-heavy to establish as this theorem
/// is directly (both need to know how `Rat.normalize` interacts with a
/// negated numerator), so reducing to it buys nothing. The good branch is
/// `num q = negSucc m`; the single dead branch — `num q = ofNat n`, for
/// *any* `n` — is refuted in one shot by [`int_neg_of_neg`] plus
/// `Nat.not_lt_zero`, unlike the positive proof's two dead branches (which
/// need `eq_zero_of_num_zero` for `n = 0` and an `ι`-reduction to `False` for
/// `negSucc`, i.e. two different arguments).
fn declare_mul_inv_cancel_of_neg(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let int = p.int;
    let carrier = rat_ty(d);
    let nat_ty = d.nat_ty();
    let int_ty = d.int_ty();
    let prop_level = d.kernel().level_zero();

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let zero = rzero(d, p);
    let one = rone(d, p);
    let hypothesis = rlt(d, p, q, zero);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let numerator = num(d, q);
    let sign = int_neg_of_neg(d, p, q, h);

    // `fun z => num q = z → q · (inv_body q z) = 1`, the motive of the split.
    let motive = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let equation = d.ieq(numerator, z);
        let reciprocal = inv_body(d, p, q, z);
        let product = rmul(d, q, reciprocal);
        let claim = req(d, product, one);
        let inner = d.arrow(equation, claim);
        d.lam_fv(z_fv, int_ty, inner)
    };

    // `num q = ofNat n`, for any `n`: `Int.lt (ofNat n) Int.zero` is `ι`-equal
    // to `Nat.lt n 0`, refuted directly — no nested split on `n`.
    let minor_of_nat = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let target = d.of_nat(n);
        let equation = d.ieq(numerator, target);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let reciprocal = inv_body(d, p, q, target);
        let product = rmul(d, q, reciprocal);
        let claim = req(d, product, one);
        let impossible = {
            let izero = d.izero();
            let shifted = d.int_eq_rewrite(numerator, target, e, sign, &|d, x| d.ilt(x, izero));
            let refuted = d.lemma(int.nat.not_lt_zero, &[n]);
            d.apply(refuted, &[shifted])
        };
        let body = d.absurd(claim, impossible);
        let with_e = d.lam_fv(e_fv, equation, body);
        d.lam_fv(n_fv, nat_ty, with_e)
    };

    // `num q = negSucc m` — the real proof.
    let minor_neg_succ = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let target = d.neg_succ(m);
        let equation = d.ieq(numerator, target);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let body = cancel_at_negative_numerator(d, p, q, m, e);
        let with_e = d.lam_fv(e_fv, equation, body);
        d.lam_fv(m_fv, nat_ty, with_e)
    };

    let rec = d.kernel().const_(int.rec, vec![prop_level]);
    let split = d.apply(rec, &[motive, minor_of_nat, minor_neg_succ, numerator]);
    let reflexive = d.irefl(numerator);
    let applied = d.apply(split, &[reflexive]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, applied);
        d.lam_fv(q_fv, carrier, with_h)
    };
    let ty = {
        let reciprocal = d.const_app(p.inv, &[q]);
        let product = rmul(d, q, reciprocal);
        let claim = req(d, product, one);
        let inner = d.arrow(hypothesis, claim);
        d.pi_fv(q_fv, carrier, inner)
    };
    d.kernel()
        .add_declaration(crate::env::Declaration::Theorem {
            name: p.mul_inv_cancel_of_neg,
            uparams: vec![],
            ty,
            value,
        })
}

/// `Rat.mul_inv_cancel_of_ne_zero : ∀ q, Not (Eq Rat q Rat.zero) →
/// Eq Rat (Rat.mul q (Rat.inv q)) Rat.one`.
///
/// The single unlock this module was blocked on: `mul_inv_cancel` and
/// `mul_inv_cancel_of_neg` each cover one sign, and `Rat.lt_trichotomy`
/// (`declare_trichotomy`, constructive — built from the *proved*
/// `Rat.le_or_lt` and `Rat.le_antisymm`, no excluded middle) is exactly what
/// closes the gap. `lt_trichotomy q 0` gives
/// `Or (lt q 0) (Or (q = 0) (lt 0 q))`: the first disjunct is verbatim
/// [`declare_mul_inv_cancel_of_neg`]'s hypothesis, the last is verbatim
/// [`declare_mul_inv_cancel`]'s, and the middle disjunct is refuted by
/// applying the `q ≠ 0` hypothesis to the equality it supplies.
fn declare_mul_inv_cancel_of_ne_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let zero = rzero(d, p);
    let one = rone(d, p);

    let equal = req(d, q, zero);
    let hypothesis = d.not(equal);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let reciprocal = d.const_app(p.inv, &[q]);
    let product = rmul(d, q, reciprocal);
    let conclusion = req(d, product, one);

    let lt_q_zero = rlt(d, p, q, zero);
    let lt_zero_q = rlt(d, p, zero, q);
    let right_or = d.or(equal, lt_zero_q);
    let trichotomy = d.lemma(p.lt_trichotomy, &[q, zero]);

    let body = d.or_elim(
        lt_q_zero,
        right_or,
        conclusion,
        trichotomy,
        &|d, h_neg| d.lemma(p.mul_inv_cancel_of_neg, &[q, h_neg]),
        &|d, h_rest| {
            d.or_elim(
                equal,
                lt_zero_q,
                conclusion,
                h_rest,
                &|d, h_eq| {
                    let false_proof = d.apply(h, &[h_eq]);
                    d.absurd(conclusion, false_proof)
                },
                &|d, h_pos| d.lemma(p.mul_inv_cancel, &[q, h_pos]),
            )
        },
    );

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, body);
        d.lam_fv(q_fv, carrier, with_h)
    };
    let ty = {
        let inner = d.arrow(hypothesis, conclusion);
        d.pi_fv(q_fv, carrier, inner)
    };
    d.kernel()
        .add_declaration(crate::env::Declaration::Theorem {
            name: p.mul_inv_cancel_of_ne_zero,
            uparams: vec![],
            ty,
            value,
        })
}

/// `Rat.inv_pos : ∀ q, 0 < q → 0 < q⁻¹`.
///
/// Derived from `mul_inv_cancel` and the 22 laws alone: were `q⁻¹ ≤ 0`, then
/// `1 = q·q⁻¹ ≤ q·0 = 0` by `mul_le_mul_of_nonneg_left`, and `0 < 1 ≤ 0` is
/// `lt_irrefl`. The case split is [`Rat.le_or_lt`](super::RatPrelude::le_or_lt),
/// which is *proved* — no excluded middle, no double negation.
fn declare_inv_pos(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.inv_pos, 1, &|d, v| {
        let q = v[0];
        let zero = rzero(d, p);
        let one = rone(d, p);
        let reciprocal = d.const_app(p.inv, &[q]);
        let hypothesis = rlt(d, p, zero, q);
        let conclusion = rlt(d, p, zero, reciprocal);
        let stmt = d.arrow(hypothesis, conclusion);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let nonpositive = rle(d, p, reciprocal, zero);
        let positive = rlt(d, p, zero, reciprocal);
        let decision = d.lemma(p.le_or_lt, &[reciprocal, zero]);
        let body = d.or_elim(
            nonpositive,
            positive,
            conclusion,
            decision,
            &|d, bounded| {
                // `1 = q·q⁻¹ ≤ q·0 = 0`, so `0 < 0`.
                let nonneg = d.lemma(p.le_of_lt, &[zero, q, h]);
                let scaled = d.lemma(
                    p.mul_le_mul_of_nonneg_left,
                    &[q, reciprocal, zero, nonneg, bounded],
                );
                let product = rmul(d, q, reciprocal);
                let annihilated = rmul(d, q, zero);
                let cancel = d.lemma(p.mul_inv_cancel, &[q, h]);
                let vanish = d.lemma(p.mul_zero, &[q]);
                let at_one = rat_eq_rewrite(d, product, one, cancel, scaled, &|d, t| {
                    rle(d, p, t, annihilated)
                });
                let at_zero = rat_eq_rewrite(d, annihilated, zero, vanish, at_one, &|d, t| {
                    rle(d, p, one, t)
                });
                let unit = d.lemma(p.zero_lt_one, &[]);
                let degenerate = d.lemma(p.lt_of_lt_of_le, &[zero, one, zero, unit, at_zero]);
                let refuted = d.lemma(p.lt_irrefl, &[zero]);
                let contradiction = d.apply(refuted, &[degenerate]);
                d.absurd(conclusion, contradiction)
            },
            &|_d, strict| strict,
        );
        let proof = d.lam_fv(h_fv, hypothesis, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Rat.inv_natDivSucc : ∀ m, (1/(m+1))⁻¹ = (m+1)/1`.
///
/// **The one place an inverse's *value* is computed rather than a property of
/// it derived**, and the real construction cannot do without it: every bound
/// there is a single `Rat.natDivSucc` whose numerator is a `Nat`, so a
/// reciprocal left as an opaque `Rat` would fuse with nothing and
/// `natDivSucc_mul` would have no numerator to multiply.
///
/// It is still not about the representation. `natDivSucc_mul` gives
/// `((m+1)/1)·(1/(m+1)) = (m+1)/(m+1)`, `natDivSucc_scale` at `m = 0` reads
/// that as `1/1`, `self_normalize` says `1/1` **is** `Rat.one`, and then the
/// uniqueness of a multiplicative inverse — `mul_inv_cancel` plus the 22 laws —
/// finishes: `w·c = 1` and `c·c⁻¹ = 1` force `c⁻¹ = w`.
fn declare_inv_nat_div_succ(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat_ty = d.nat_ty();
    let nat = p.int.nat;
    super::archimedean::mixed_theorem(d, p.inv_nat_div_succ, &[nat_ty], &|d, v| {
        let m = v[0];
        let one_nat = d.num(1);
        let zero_nat = d.num(0);
        let successor = d.succ(m);
        let modulus = d.const_app(p.nat_div_succ, &[one_nat, m]);
        let whole = d.const_app(p.nat_div_succ, &[successor, zero_nat]);
        let reciprocal = d.const_app(p.inv, &[modulus]);
        let stmt = req(d, reciprocal, whole);

        let one = rone(d, p);

        // `w·c = 1`, with `w := (m+1)/1` and `c := 1/(m+1)`.
        let product = rmul(d, whole, modulus);
        let fused = {
            let scaled = NatOps::mul(d, successor, one_nat);
            d.const_app(p.nat_div_succ, &[scaled, m])
        };
        let fuse = d.lemma(p.nat_div_succ_mul, &[successor, one_nat, m]);
        let collapsed = d.const_app(p.nat_div_succ, &[successor, m]);
        let collapse = {
            let scaled = NatOps::mul(d, successor, one_nat);
            let identity = d.lemma(nat.mul_one, &[successor]);
            nat_eq_to_rat(d, scaled, successor, identity, &|d, t| {
                d.const_app(p.nat_div_succ, &[t, m])
            })
        };
        // `natDivSucc_scale m 0 : (m+1)/((m+1)·0 + m + 1) = 1/1`, and the index
        // `(m+1)·0 + m` is `m` — `Nat.mul _ 0` by ι, then `zero_add`.
        let unit = d.const_app(p.nat_div_succ, &[one_nat, zero_nat]);
        let scale = {
            let deep = NatOps::mul(d, successor, zero_nat);
            let index = NatOps::add(d, deep, m);
            let law = d.lemma(p.nat_div_succ_scale, &[m, zero_nat]);
            let flatten = d.lemma(nat.zero_add, &[m]);
            nat_rewrite_prop(d, index, m, flatten, law, &|d, t| {
                let left = d.const_app(p.nat_div_succ, &[successor, t]);
                req(d, left, unit)
            })
        };
        let unit_is_one = d.const_app(p.self_normalize, &[one]);
        let (_, cancel) = rchain(
            d,
            product,
            &[
                (fused, fuse),
                (collapsed, collapse),
                (unit, scale),
                (one, unit_is_one),
            ],
        );

        // Uniqueness: `c⁻¹ = 1·c⁻¹ = (w·c)·c⁻¹ = w·(c·c⁻¹) = w·1 = w`.
        let modulus_positive = {
            let unit_le = d.lemma(nat.le_refl, &[one_nat]);
            d.lemma(p.nat_div_succ_pos, &[one_nat, m, unit_le])
        };
        let self_cancel = d.lemma(p.mul_inv_cancel, &[modulus, modulus_positive]);
        let padded = rmul(d, one, reciprocal);
        let restore = {
            let strip = d.lemma(p.mul_one, &[reciprocal]);
            let flipped = d.lemma(p.mul_comm, &[one, reciprocal]);
            let swapped = rmul(d, reciprocal, one);
            let (_, chained) = rchain(d, padded, &[(swapped, flipped), (reciprocal, strip)]);
            rsymm(d, padded, reciprocal, chained)
        };
        let reopened = rmul(d, product, reciprocal);
        let reopen = {
            let back = rsymm(d, product, one, cancel);
            rcongr(d, one, product, back, &|d, t| rmul(d, t, reciprocal))
        };
        let regrouped = {
            let inner = rmul(d, modulus, reciprocal);
            rmul(d, whole, inner)
        };
        let regroup = d.lemma(p.mul_assoc, &[whole, modulus, reciprocal]);
        let stripped = rmul(d, whole, one);
        let strip_inner = {
            let inner = rmul(d, modulus, reciprocal);
            rcongr(d, inner, one, self_cancel, &|d, t| rmul(d, whole, t))
        };
        let strip = d.lemma(p.mul_one, &[whole]);
        let (_, proof) = rchain(
            d,
            reciprocal,
            &[
                (padded, restore),
                (reopened, reopen),
                (regrouped, regroup),
                (stripped, strip_inner),
                (whole, strip),
            ],
        );
        (stmt, proof)
    })
}

// === `Rat.one_ne_zero` ======================================================

/// Admit `Rat.one_ne_zero : Not (Eq Rat Rat.one Rat.zero)`.
///
/// One transport: assume `h : one = zero`, rewrite `Rat.zero_lt_one : 0 < 1`
/// along `h` (replacing the `1` with `0`) to get `0 < 0`, refuted by
/// `Rat.lt_irrefl 0`. No case split, no representation reasoning — the same
/// route `Rat.inv_pos` uses to turn a `≤`/`<` contradiction into its goal,
/// except here the goal already **is** `False`, so no `absurd` step is
/// needed.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_one_ne_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let one = rone(d, p);
    let zero = rzero(d, p);
    let eq_ty = req(d, one, zero);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero_lt_one = d.lemma(p.zero_lt_one, &[]); // 0 < 1
    let rewritten = rat_eq_rewrite(d, one, zero, h, zero_lt_one, &|d, t| rlt(d, p, zero, t)); // 0 < 0
    let refuted = d.lemma(p.lt_irrefl, &[zero]); // Not (0 < 0)
    let false_proof = d.apply(refuted, &[rewritten]);

    let value = d.lam_fv(h_fv, eq_ty, false_proof);
    let ty = d.not(eq_ty);
    d.declare_theorem(p.one_ne_zero, ty, value)
}

// === `Rat.IsField` — the bundled-predicate shape ============================
//
// Mirrors `nat_prelude::group::declare_group_all`'s `Nat.IsGroupOn`: a plain
// `Prop`-valued `Definition` over caller-supplied operations, right-nested
// `And`. Unlike `IsGroupOn`, there is no bound `n` and no closure condition —
// `Rat` is already the whole carrier, so every operation is already total on
// it.

/// `Rat → Rat → Rat`.
fn field_binop_ty(d: &mut IntDev<'_>) -> ExprId {
    let r = rat_ty(d);
    let inner = d.arrow(r, r);
    d.arrow(r, inner)
}

/// `Rat → Rat`.
fn field_unop_ty(d: &mut IntDev<'_>) -> ExprId {
    let r = rat_ty(d);
    d.arrow(r, r)
}

/// `∀ a b, add a b = add b a`.
fn field_add_comm_prop(d: &mut IntDev<'_>, add: ExprId) -> ExprId {
    let r = rat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let ab = d.apply(add, &[a, b]);
    let ba = d.apply(add, &[b, a]);
    let eq = req(d, ab, ba);
    let with_b = d.pi_fv(b_fv, r, eq);
    d.pi_fv(a_fv, r, with_b)
}

/// `∀ a b c, add (add a b) c = add a (add b c)`.
fn field_add_assoc_prop(d: &mut IntDev<'_>, add: ExprId) -> ExprId {
    let r = rat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let ab = d.apply(add, &[a, b]);
    let ab_c = d.apply(add, &[ab, c]);
    let bc = d.apply(add, &[b, c]);
    let a_bc = d.apply(add, &[a, bc]);
    let eq = req(d, ab_c, a_bc);
    let with_c = d.pi_fv(c_fv, r, eq);
    let with_b = d.pi_fv(b_fv, r, with_c);
    d.pi_fv(a_fv, r, with_b)
}

/// `∀ a, add a zero = a`.
fn field_add_zero_prop(d: &mut IntDev<'_>, add: ExprId, zero: ExprId) -> ExprId {
    let r = rat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let az = d.apply(add, &[a, zero]);
    let eq = req(d, az, a);
    d.pi_fv(a_fv, r, eq)
}

/// `∀ a, add a (neg a) = zero`.
fn field_add_neg_prop(d: &mut IntDev<'_>, add: ExprId, neg: ExprId, zero: ExprId) -> ExprId {
    let r = rat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let na = d.apply(neg, &[a]);
    let a_na = d.apply(add, &[a, na]);
    let eq = req(d, a_na, zero);
    d.pi_fv(a_fv, r, eq)
}

/// `∀ a b, mul a b = mul b a`.
fn field_mul_comm_prop(d: &mut IntDev<'_>, mul: ExprId) -> ExprId {
    field_add_comm_prop(d, mul)
}

/// `∀ a b c, mul (mul a b) c = mul a (mul b c)`.
fn field_mul_assoc_prop(d: &mut IntDev<'_>, mul: ExprId) -> ExprId {
    field_add_assoc_prop(d, mul)
}

/// `∀ a, mul a one = a`.
fn field_mul_one_prop(d: &mut IntDev<'_>, mul: ExprId, one: ExprId) -> ExprId {
    field_add_zero_prop(d, mul, one)
}

/// `∀ a b c, mul a (add b c) = add (mul a b) (mul a c)`.
fn field_distrib_prop(d: &mut IntDev<'_>, add: ExprId, mul: ExprId) -> ExprId {
    let r = rat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let bc = d.apply(add, &[b, c]);
    let left = d.apply(mul, &[a, bc]);
    let ab = d.apply(mul, &[a, b]);
    let ac = d.apply(mul, &[a, c]);
    let right = d.apply(add, &[ab, ac]);
    let eq = req(d, left, right);
    let with_c = d.pi_fv(c_fv, r, eq);
    let with_b = d.pi_fv(b_fv, r, with_c);
    d.pi_fv(a_fv, r, with_b)
}

/// `Not (one = zero)`.
fn field_one_ne_zero_prop(d: &mut IntDev<'_>, one: ExprId, zero: ExprId) -> ExprId {
    let eq = req(d, one, zero);
    d.not(eq)
}

/// `∀ a, Not (a = zero) → mul a (inv a) = one`.
fn field_inv_cancel_prop(
    d: &mut IntDev<'_>,
    mul: ExprId,
    inv: ExprId,
    zero: ExprId,
    one: ExprId,
) -> ExprId {
    let r = rat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let a_ne_zero = {
        let eq = req(d, a, zero);
        d.not(eq)
    };
    let ia = d.apply(inv, &[a]);
    let prod = d.apply(mul, &[a, ia]);
    let concl = req(d, prod, one);
    let body = d.arrow(a_ne_zero, concl);
    d.pi_fv(a_fv, r, body)
}

/// `IsField add mul neg inv zero one`'s ten leaf components — the same
/// "rebuild the unfolded `Prop`s directly, never through the folded constant"
/// convention `nat_prelude::group::is_group_on_parts` uses, so a caller
/// decomposing a hypothesis or assembling an instance can name each
/// component's exact type.
struct FieldParts {
    add_comm: ExprId,
    add_assoc: ExprId,
    add_zero: ExprId,
    add_neg: ExprId,
    mul_comm: ExprId,
    mul_assoc: ExprId,
    mul_one: ExprId,
    distrib: ExprId,
    one_ne_zero: ExprId,
    inv_cancel: ExprId,
}

#[allow(clippy::too_many_arguments)]
fn field_parts(
    d: &mut IntDev<'_>,
    add: ExprId,
    mul: ExprId,
    neg: ExprId,
    inv: ExprId,
    zero: ExprId,
    one: ExprId,
) -> FieldParts {
    FieldParts {
        add_comm: field_add_comm_prop(d, add),
        add_assoc: field_add_assoc_prop(d, add),
        add_zero: field_add_zero_prop(d, add, zero),
        add_neg: field_add_neg_prop(d, add, neg, zero),
        mul_comm: field_mul_comm_prop(d, mul),
        mul_assoc: field_mul_assoc_prop(d, mul),
        mul_one: field_mul_one_prop(d, mul, one),
        distrib: field_distrib_prop(d, add, mul),
        one_ne_zero: field_one_ne_zero_prop(d, one, zero),
        inv_cancel: field_inv_cancel_prop(d, mul, inv, zero, one),
    }
}

/// Right-nested `And` of [`FieldParts`]'s ten leaves, in the order documented
/// on [`RatPrelude::is_field`]:
///
/// `add_comm ∧ (add_assoc ∧ (add_zero ∧ (add_neg ∧ (mul_comm ∧ (mul_assoc ∧
/// (mul_one ∧ (distrib ∧ (one_ne_zero ∧ inv_cancel))))))))`.
fn field_body(d: &mut IntDev<'_>, parts: &FieldParts) -> ExprId {
    let p9 = d.and(parts.one_ne_zero, parts.inv_cancel);
    let p8 = d.and(parts.distrib, p9);
    let p7 = d.and(parts.mul_one, p8);
    let p6 = d.and(parts.mul_assoc, p7);
    let p5 = d.and(parts.mul_comm, p6);
    let p4 = d.and(parts.add_neg, p5);
    let p3 = d.and(parts.add_zero, p4);
    let p2 = d.and(parts.add_assoc, p3);
    d.and(parts.add_comm, p2)
}

/// `d.const_app(p.is_field, &[add, mul, neg, inv, zero, one])`.
#[allow(clippy::too_many_arguments)]
fn is_field(
    d: &mut IntDev<'_>,
    p: &RatPrelude,
    add: ExprId,
    mul: ExprId,
    neg: ExprId,
    inv: ExprId,
    zero: ExprId,
    one: ExprId,
) -> ExprId {
    d.const_app(p.is_field, &[add, mul, neg, inv, zero, one])
}

/// `And.intro left right lp rp : And left right`.
fn field_and_intro(
    d: &mut IntDev<'_>,
    left: ExprId,
    right: ExprId,
    lp: ExprId,
    rp: ExprId,
) -> ExprId {
    let intro = d.int().logic.and_intro;
    d.const_app(intro, &[left, right, lp, rp])
}

/// Admit `Rat.IsField : (Rat → Rat → Rat) → (Rat → Rat → Rat) → (Rat → Rat) →
/// (Rat → Rat) → Rat → Rat → Prop`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the generated definition does not
/// type-check or the name is already taken.
fn declare_is_field(d: &mut IntDev<'_>, p: &RatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let r = rat_ty(d);
    let prop = d.kernel().sort_zero();
    let binop = field_binop_ty(d);
    let unop = field_unop_ty(d);

    let add_fv = d.fresh_fvar();
    let add = d.kernel().fvar(add_fv);
    let mul_fv = d.fresh_fvar();
    let mul = d.kernel().fvar(mul_fv);
    let neg_fv = d.fresh_fvar();
    let neg = d.kernel().fvar(neg_fv);
    let inv_fv = d.fresh_fvar();
    let inv = d.kernel().fvar(inv_fv);
    let zero_fv = d.fresh_fvar();
    let zero = d.kernel().fvar(zero_fv);
    let one_fv = d.fresh_fvar();
    let one = d.kernel().fvar(one_fv);

    let parts = field_parts(d, add, mul, neg, inv, zero, one);
    let body = field_body(d, &parts);

    let value = {
        let with_one = d.lam_fv(one_fv, r, body);
        let with_zero = d.lam_fv(zero_fv, r, with_one);
        let with_inv = d.lam_fv(inv_fv, unop, with_zero);
        let with_neg = d.lam_fv(neg_fv, unop, with_inv);
        let with_mul = d.lam_fv(mul_fv, binop, with_neg);
        d.lam_fv(add_fv, binop, with_mul)
    };
    let ty = {
        let over_one = d.arrow(r, prop);
        let over_zero = d.arrow(r, over_one);
        let over_inv = d.arrow(unop, over_zero);
        let over_neg = d.arrow(unop, over_inv);
        let over_mul = d.arrow(binop, over_neg);
        d.arrow(binop, over_mul)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_field,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(FIELD_HEIGHT),
    })
}

/// Admit `Rat.rat_isField : Rat.IsField Rat.add Rat.mul Rat.neg Rat.inv
/// Rat.zero Rat.one` — assembled entirely from already-admitted theorems.
/// Each of the ten leaves' STATED type already matches
/// [`field_parts`]'s corresponding component verbatim (`Rat.add_comm : ∀ a b,
/// add a b = add b a`, …, `Rat.mul_inv_cancel_of_ne_zero : ∀ a, a ≠ 0 → mul a
/// (inv a) = one`), so every leaf proof is a bare reference to the existing
/// constant (`d.lemma(name, &[])`) — no new algebra, only `And.intro`
/// bookkeeping.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the generated declaration does not
/// type-check or the name is already taken.
fn declare_rat_is_field(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let add = d.kernel().const_(p.int.rat_add, vec![]);
    let mul = d.kernel().const_(p.int.rat_mul, vec![]);
    let neg = d.kernel().const_(p.int.rat_neg, vec![]);
    let inv = d.kernel().const_(p.inv, vec![]);
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    let ty = is_field(d, &p, add, mul, neg, inv, zero, one);
    let parts = field_parts(d, add, mul, neg, inv, zero, one);

    let add_comm = d.lemma(p.add_comm, &[]);
    let add_assoc = d.lemma(p.add_assoc, &[]);
    let add_zero = d.lemma(p.add_zero, &[]);
    let add_neg = d.lemma(p.add_neg, &[]);
    let mul_comm = d.lemma(p.mul_comm, &[]);
    let mul_assoc = d.lemma(p.mul_assoc, &[]);
    let mul_one = d.lemma(p.mul_one, &[]);
    let distrib = d.lemma(p.left_distrib, &[]);
    let one_ne_zero = d.lemma(p.one_ne_zero, &[]);
    let inv_cancel = d.lemma(p.mul_inv_cancel_of_ne_zero, &[]);

    let t9 = d.and(parts.one_ne_zero, parts.inv_cancel);
    let t8 = d.and(parts.distrib, t9);
    let t7 = d.and(parts.mul_one, t8);
    let t6 = d.and(parts.mul_assoc, t7);
    let t5 = d.and(parts.mul_comm, t6);
    let t4 = d.and(parts.add_neg, t5);
    let t3 = d.and(parts.add_zero, t4);
    let t2 = d.and(parts.add_assoc, t3);

    let p9v = field_and_intro(
        d,
        parts.one_ne_zero,
        parts.inv_cancel,
        one_ne_zero,
        inv_cancel,
    );
    let p8v = field_and_intro(d, parts.distrib, t9, distrib, p9v);
    let p7v = field_and_intro(d, parts.mul_one, t8, mul_one, p8v);
    let p6v = field_and_intro(d, parts.mul_assoc, t7, mul_assoc, p7v);
    let p5v = field_and_intro(d, parts.mul_comm, t6, mul_comm, p6v);
    let p4v = field_and_intro(d, parts.add_neg, t5, add_neg, p5v);
    let p3v = field_and_intro(d, parts.add_zero, t4, add_zero, p4v);
    let p2v = field_and_intro(d, parts.add_assoc, t3, add_assoc, p3v);
    let value = field_and_intro(d, parts.add_comm, t2, add_comm, p2v);

    d.declare_theorem(p.rat_is_field, ty, value)
}

// === Consequences: cancellation ============================================
//
// `Rat.mul_eq_zero : ∀ a b, mul a b = zero → a = zero ∨ b = zero` already
// exists (`laws.rs`) — ℚ having no zero divisors was proved before this
// module, in service of `Rat.lt_trichotomy`. What was missing is the other
// fact a field gives that a ring does not: cancellation.

/// Admit `Rat.mul_left_cancel_of_ne_zero : ∀ a b c, Not (a = zero) → mul a b
/// = mul a c → b = c`.
///
/// `b = 1·b = (a⁻¹·a)·b = a⁻¹·(a·b) = a⁻¹·(a·c) = (a⁻¹·a)·c = 1·c = c` — the
/// same seven-step chain `nat_prelude::group::declare_group_left_cancel` runs
/// over an abstract `IsGroupOn` hypothesis, specialised to `Rat`'s own
/// commutative multiplication: only the one inverse law `a⁻¹·a = 1`
/// (`Rat.mul_inv_cancel_of_ne_zero` plus `Rat.mul_comm`) is needed, not a
/// bounded group's closure/membership side conditions.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_mul_left_cancel_of_ne_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let zero = rzero(d, p);
    let one = rone(d, p);

    let a_ne_zero = {
        let eq = req(d, a, zero);
        d.not(eq)
    };
    let ha_fv = d.fresh_fvar();
    let ha = d.kernel().fvar(ha_fv);

    let ab = rmul(d, a, b);
    let ac = rmul(d, a, c);
    let hab_ty = req(d, ab, ac);
    let hab_fv = d.fresh_fvar();
    let hab = d.kernel().fvar(hab_fv);

    // inv a, and both cancellation orientations.
    let inv_a = d.const_app(p.inv, &[a]);
    let a_inv_a = rmul(d, a, inv_a);
    let inv_a_a = rmul(d, inv_a, a);
    let a_inv_a_eq_one = d.lemma(p.mul_inv_cancel_of_ne_zero, &[a, ha]); // a*a⁻¹ = 1
    let comm_inv = d.lemma(p.mul_comm, &[inv_a, a]); // a⁻¹*a = a*a⁻¹
    let inv_a_a_eq_one = rtrans(d, inv_a_a, a_inv_a, one, comm_inv, a_inv_a_eq_one); // a⁻¹*a = 1

    // step1 : b = 1*b
    let mul_one_b = d.lemma(p.mul_one, &[b]); // b*1 = b
    let comm_one_b = d.lemma(p.mul_comm, &[one, b]); // 1*b = b*1
    let one_b = rmul(d, one, b);
    let b_one = rmul(d, b, one);
    let one_b_eq_b = rtrans(d, one_b, b_one, b, comm_one_b, mul_one_b);
    let step1 = rsymm(d, one_b, b, one_b_eq_b); // b = 1*b

    // step2 : 1*b = (a⁻¹*a)*b
    let one_eq_inv_a_a = rsymm(d, inv_a_a, one, inv_a_a_eq_one); // 1 = a⁻¹*a
    let inv_a_a_b = rmul(d, inv_a_a, b);
    let step2 = rcongr(d, one, inv_a_a, one_eq_inv_a_a, &|d, t| rmul(d, t, b));

    // step3 : (a⁻¹*a)*b = a⁻¹*(a*b)
    let step3 = d.lemma(p.mul_assoc, &[inv_a, a, b]);
    let inv_a_ab = rmul(d, inv_a, ab);

    // step4 : a⁻¹*(a*b) = a⁻¹*(a*c)
    let inv_a_ac = rmul(d, inv_a, ac);
    let step4 = rcongr(d, ab, ac, hab, &|d, t| rmul(d, inv_a, t));

    // step5 : a⁻¹*(a*c) = (a⁻¹*a)*c
    let assoc_iaac = d.lemma(p.mul_assoc, &[inv_a, a, c]);
    let inv_a_a_c = rmul(d, inv_a_a, c);
    let step5 = rsymm(d, inv_a_a_c, inv_a_ac, assoc_iaac);

    // step6 : (a⁻¹*a)*c = 1*c
    let one_c = rmul(d, one, c);
    let step6 = rcongr(d, inv_a_a, one, inv_a_a_eq_one, &|d, t| rmul(d, t, c));

    // step7 : 1*c = c
    let c_one = rmul(d, c, one);
    let mul_one_c = d.lemma(p.mul_one, &[c]); // c*1 = c
    let comm_one_c = d.lemma(p.mul_comm, &[one, c]); // 1*c = c*1
    let step7 = rtrans(d, one_c, c_one, c, comm_one_c, mul_one_c);

    let (_, proof_body) = rchain(
        d,
        b,
        &[
            (one_b, step1),
            (inv_a_a_b, step2),
            (inv_a_ab, step3),
            (inv_a_ac, step4),
            (inv_a_a_c, step5),
            (one_c, step6),
            (c, step7),
        ],
    );

    let concl = req(d, b, c);
    let stmt_inner = {
        let inner = d.arrow(hab_ty, concl);
        d.arrow(a_ne_zero, inner)
    };
    let value_inner = {
        let with_hab = d.lam_fv(hab_fv, hab_ty, proof_body);
        d.lam_fv(ha_fv, a_ne_zero, with_hab)
    };

    let binders = [(a_fv, carrier), (b_fv, carrier), (c_fv, carrier)];
    let mut ty = stmt_inner;
    let mut value = value_inner;
    for &(fv, vty) in binders.iter().rev() {
        ty = d.pi_fv(fv, vty, ty);
        value = d.lam_fv(fv, vty, value);
    }

    d.declare_theorem(p.mul_left_cancel_of_ne_zero, ty, value)
}

// === `Rat.IsOrderedField` — `IsField` plus the two order axioms ============
//
// Composition, not restatement: `IsOrderedField add mul neg inv zero one :=
// IsField add mul neg inv zero one ∧ (translation ∧ mul_nonneg)`. The ten
// field leaves are never rebuilt here. `Rat.rat_isField` (already proved) is
// reused VERBATIM as the instance's first component, and `Rat.IsField` (an
// existing named `Definition`) is reused VERBATIM as the bundle type's first
// component — the declared type of `Rat.rat_isField` is already the folded
// `Rat.IsField Rat.add Rat.mul Rat.neg Rat.inv Rat.zero Rat.one`, so it
// matches this bundle's first conjunct with no unfolding needed on either
// side. `Rat.le` is fixed, exactly as `Eq Rat` is fixed in `IsField`'s own
// leaves: the order relation is not a bundle parameter, only the six
// algebraic operations are — the same "no bound parameter" reason `IsField`
// gives for its own name (`Rat` is already the whole carrier).
//
// The alternative — restating all ten field leaves alongside the two order
// ones — would work too (the kernel does not care), but it would duplicate
// `field_parts`/`field_body`/`declare_is_field`'s ~120 lines for no benefit:
// nothing downstream needs to decompose `IsOrderedField` down to its field
// leaves directly, only to `IsField` (whose own decomposition already
// exists) and to the two order axioms.

/// Delta height for `Rat.IsOrderedField`, one above [`FIELD_HEIGHT`]. Unlike
/// `IsField`'s own note about its height (never reachable, since its value
/// only abstracts over caller-supplied operations), `IsOrderedField`'s value
/// DOES apply the `IsField` constant directly, so it must sit strictly above
/// it.
const ORDERED_FIELD_HEIGHT: u16 = FIELD_HEIGHT + 1;

/// `∀ x y z, le x y → le (add x z) (add y z)` — translation invariance,
/// `IsOrderedField`'s first order axiom.
fn field_translation_prop(d: &mut IntDev<'_>, p: RatPrelude, add: ExprId) -> ExprId {
    let r = rat_ty(d);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let hyp = rle(d, p, x, y);
    let xz = d.apply(add, &[x, z]);
    let yz = d.apply(add, &[y, z]);
    let concl = rle(d, p, xz, yz);
    let body = d.arrow(hyp, concl);
    let with_z = d.pi_fv(z_fv, r, body);
    let with_y = d.pi_fv(y_fv, r, with_z);
    d.pi_fv(x_fv, r, with_y)
}

/// `∀ x y, le zero x → le zero y → le zero (mul x y)` — closure of the
/// nonnegatives under multiplication, `IsOrderedField`'s second order axiom.
/// Verbatim [`RatPrelude::mul_nonneg`]'s statement, generalised to a
/// caller-supplied `mul`/`zero` rather than the fixed operations.
fn field_order_mul_nonneg_prop(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mul: ExprId,
    zero: ExprId,
) -> ExprId {
    let r = rat_ty(d);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);

    let hx = rle(d, p, zero, x);
    let hy = rle(d, p, zero, y);
    let xy = d.apply(mul, &[x, y]);
    let concl = rle(d, p, zero, xy);
    let body = d.arrow(hy, concl);
    let with_hx = d.arrow(hx, body);
    let with_y = d.pi_fv(y_fv, r, with_hx);
    d.pi_fv(x_fv, r, with_y)
}

/// `d.const_app(p.is_ordered_field, &[add, mul, neg, inv, zero, one])`.
#[allow(clippy::too_many_arguments)]
fn is_ordered_field(
    d: &mut IntDev<'_>,
    p: &RatPrelude,
    add: ExprId,
    mul: ExprId,
    neg: ExprId,
    inv: ExprId,
    zero: ExprId,
    one: ExprId,
) -> ExprId {
    d.const_app(p.is_ordered_field, &[add, mul, neg, inv, zero, one])
}

/// Admit `Rat.IsOrderedField : (Rat → Rat → Rat) → (Rat → Rat → Rat) → (Rat →
/// Rat) → (Rat → Rat) → Rat → Rat → Prop`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the generated definition does not
/// type-check or the name is already taken.
fn declare_is_ordered_field(d: &mut IntDev<'_>, p: &RatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let r = rat_ty(d);
    let prop = d.kernel().sort_zero();
    let binop = field_binop_ty(d);
    let unop = field_unop_ty(d);

    let add_fv = d.fresh_fvar();
    let add = d.kernel().fvar(add_fv);
    let mul_fv = d.fresh_fvar();
    let mul = d.kernel().fvar(mul_fv);
    let neg_fv = d.fresh_fvar();
    let neg = d.kernel().fvar(neg_fv);
    let inv_fv = d.fresh_fvar();
    let inv = d.kernel().fvar(inv_fv);
    let zero_fv = d.fresh_fvar();
    let zero = d.kernel().fvar(zero_fv);
    let one_fv = d.fresh_fvar();
    let one = d.kernel().fvar(one_fv);

    let field_component = is_field(d, &p, add, mul, neg, inv, zero, one);
    let translation = field_translation_prop(d, p, add);
    let mul_nonneg_prop = field_order_mul_nonneg_prop(d, p, mul, zero);
    let order_body = d.and(translation, mul_nonneg_prop);
    let body = d.and(field_component, order_body);

    let value = {
        let with_one = d.lam_fv(one_fv, r, body);
        let with_zero = d.lam_fv(zero_fv, r, with_one);
        let with_inv = d.lam_fv(inv_fv, unop, with_zero);
        let with_neg = d.lam_fv(neg_fv, unop, with_inv);
        let with_mul = d.lam_fv(mul_fv, binop, with_neg);
        d.lam_fv(add_fv, binop, with_mul)
    };
    let ty = {
        let over_one = d.arrow(r, prop);
        let over_zero = d.arrow(r, over_one);
        let over_inv = d.arrow(unop, over_zero);
        let over_neg = d.arrow(unop, over_inv);
        let over_mul = d.arrow(binop, over_neg);
        d.arrow(binop, over_mul)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_ordered_field,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(ORDERED_FIELD_HEIGHT),
    })
}

/// Proof of `∀ x y z, le x y → le (add x z) (add y z)` at the CONCRETE
/// `Rat.add`: `Rat.add_le_add x y z z h (Rat.le_refl z) : le (add x z) (add y
/// z)` — translation invariance falls out of `add_le_add` by pairing the real
/// hypothesis with a reflexive one on the shared `z`, exactly the
/// `lattice.rs` idiom (`d.lemma(p.add_le_add, &[a, b, c, c, h, reflexive])`)
/// used throughout this prelude already.
fn translation_invariance_proof(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    let r = rat_ty(d);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let hyp = rle(d, p, x, y);
    let refl_z = d.lemma(p.le_refl, &[z]);
    let step = d.lemma(p.add_le_add, &[x, y, z, z, h, refl_z]);

    let inner = d.lam_fv(h_fv, hyp, step);
    let with_z = d.lam_fv(z_fv, r, inner);
    let with_y = d.lam_fv(y_fv, r, with_z);
    d.lam_fv(x_fv, r, with_y)
}

/// Admit `Rat.rat_isOrderedField : Rat.IsOrderedField Rat.add Rat.mul
/// Rat.neg Rat.inv Rat.zero Rat.one`.
///
/// The field component is `Rat.rat_isField` verbatim — no new algebra. Of
/// the two order axioms, translation invariance is
/// [`translation_invariance_proof`] (two lines of `add_le_add`+`le_refl`) and
/// closure of the nonnegatives is [`RatPrelude::mul_nonneg`] verbatim: its
/// STATED type (`∀ a b, le 0 a → le 0 b → le 0 (mul a b)`, `statements.rs`)
/// already matches [`field_order_mul_nonneg_prop`] at the concrete `Rat.mul`
/// and `Rat.zero`, so it needs no new proof either.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the generated declaration does not
/// type-check or the name is already taken.
fn declare_rat_is_ordered_field(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let add = d.kernel().const_(p.int.rat_add, vec![]);
    let mul = d.kernel().const_(p.int.rat_mul, vec![]);
    let neg = d.kernel().const_(p.int.rat_neg, vec![]);
    let inv = d.kernel().const_(p.inv, vec![]);
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    let ty = is_ordered_field(d, &p, add, mul, neg, inv, zero, one);

    let field_component_ty = is_field(d, &p, add, mul, neg, inv, zero, one);
    let field_proof = d.lemma(p.rat_is_field, &[]);

    let translation_ty = field_translation_prop(d, p, add);
    let translation_proof = translation_invariance_proof(d, p);

    let mul_nonneg_ty = field_order_mul_nonneg_prop(d, p, mul, zero);
    let mul_nonneg_proof = d.lemma(p.mul_nonneg, &[]);

    let order_ty = d.and(translation_ty, mul_nonneg_ty);
    let order_proof = field_and_intro(
        d,
        translation_ty,
        mul_nonneg_ty,
        translation_proof,
        mul_nonneg_proof,
    );

    let value = field_and_intro(d, field_component_ty, order_ty, field_proof, order_proof);

    d.declare_theorem(p.rat_is_ordered_field, ty, value)
}
