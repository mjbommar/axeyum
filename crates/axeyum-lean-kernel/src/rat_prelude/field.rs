//! **ℚ is a field**: the one law that makes `Rat.inv` an inverse, and the
//! ordered-field toolkit derived from it (ADR-0474, phase F2).
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
//! The negative branch of `Rat.inv` is therefore left unproved, deliberately:
//! nothing needs it yet, and `inv q = -(inv (-q))` for `q < 0` recovers it when
//! something does.

use super::RatPrelude;
use super::defs::inv_body;
use super::group::rsub;
use super::ops::{
    den, den_pos, normalize, num, one_le_succ, radd, rat_eq_rewrite, rat_theorem, rat_ty, rchain,
    rcongr, req, rle, rlt, rmul, rone, rsymm, rzero,
};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Admit `Rat.mul_inv_cancel` and the ordered-field lemmas derived from it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_field_laws(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_mul_inv_cancel(d, p)?;
    declare_inv_pos(d, p)?;
    declare_sub_mul(d, p)?;
    declare_inverse_identities(d, p)?;
    declare_inv_antitone(d, p)?;
    declare_mul_pos(d, p)?;
    declare_nat_div_succ_pos(d, p)
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
