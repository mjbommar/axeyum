//! **ℚ is a field**: the one law that makes `Rat.inv` an inverse, and the
//! ordered-field toolkit derived from it (ADR-0473, phase F2).
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
use super::ops::{
    den, den_pos, normalize, num, one_le_succ, rat_eq_rewrite, rat_theorem, rat_ty, req, rle, rlt,
    rmul, rone, rzero,
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
    declare_inv_pos(d, p)
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
