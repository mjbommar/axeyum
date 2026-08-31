//! `Nat.land_div_two` (`F:ml430-nat-and-div-two-1a2f7c33`, Mathlib's `&&&`
//! for `Nat` is our `Nat.land`): `Nat.land a b / 2 = Nat.land (a / 2) (b / 2)`.
//!
//! Boundary cases (`a = 0`/`b = 0`) go through `land_zero_left`/
//! `land_zero_right` exactly as `land_low_bit.rs`'s `land_mod_two_eq_mul`
//! does. The genuinely bitwise case is that file's technique DUALIZED: where
//! `land_mod_two_eq_mul` erases the higher recursive term by taking `mod _
//! 2` of `2 * rec + bit`, this one erases the LOW bit by taking `div _ 2` of
//! the same shape (`div_two_mul_add_of_lt`, the `div` twin of `parity.rs`'s
//! `mod_two_mul_add_of_lt`, sharing its `div_mod_unique` construction but
//! projecting the OTHER component). What remains is showing the erased
//! recursive term `landAux pa half_a half_b` (fuel `pa`, the ORIGINAL
//! succ-row's predecessor) equals the CANONICAL `land half_a half_b`
//! (fuel `half_a`) -- fuel-irrelevance, `Nat.land_aux_agree_of_fuel`
//! (`rec_agreement.rs`), needing only `Le half_a pa`, which
//! `half_le_predecessor_of_succ` gives directly at `k := pa` via `le_refl`.

use super::NatPrelude;
use super::helpers::and_left;
use super::ops::{NatDev, NatOps, cases_mod_two, cases_zero_succ};
use super::rec_agreement::half_le_predecessor_of_succ;
use crate::KernelError;
use crate::expr::ExprId;

/// `Eq (div (add (mul two x) r) 2) x`, given `Lt r two` -- the `div` twin of
/// `parity.rs`'s `mod_two_mul_add_of_lt`, sharing its `div_mod_unique`
/// witness construction but projecting the QUOTIENT component instead of
/// the remainder.
fn div_two_mul_add_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    r: ExprId,
    r_lt_two: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let two = d.num(2);
    let mul_two_x = d.mul(two, x);
    let dividend = d.add(mul_two_x, r);

    let eq_ty = d.eq(dividend, dividend);
    let bound_ty = d.lt(r, two);
    let refl_eq = d.refl(dividend);
    let h_construct = d.const_app(p.logic.and_intro, &[eq_ty, bound_ty, refl_eq, r_lt_two]);

    let h_exec = d.lemma(p.div_mod_exec, &[one, dividend]);
    let q_exec = d.div(dividend, two);
    let r_exec = d.modulo(dividend, two);

    let unique = d.lemma(
        p.div_mod_unique,
        &[two, dividend, q_exec, r_exec, x, r, h_exec, h_construct],
    );
    let eq_q_ty = d.eq(q_exec, x);
    let eq_r_ty = d.eq(r_exec, r);
    and_left(d, eq_q_ty, eq_r_ty, unique)
}

/// `Lt (mul (mod sa 2) (mod orig_b 2)) 2` -- a product of two `{0, 1}`
/// values is `< 2`, decided by `cases_mod_two` on `sa` (the case
/// `land_low_bit.rs`'s own hard case needs, duplicated here rather than
/// exported since it is the only other caller).
fn bit_product_lt_two(d: &mut NatDev<'_>, p: &NatPrelude, sa: ExprId, orig_b: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let one = d.num(1);
    let bit_b = d.modulo(orig_b, two);
    let pos = d.zero_lt_succ(one);

    let at_zero = {
        let zero = d.zero();
        let m0 = d.mul(zero, bit_b);
        let zero_mul_eq = d.lemma(p.zero_mul, &[bit_b]);
        let lt_zero_two = d.zero_lt_succ(one);
        let eq_rev = d.symm(m0, zero, zero_mul_eq);
        let motive3 = d.eq_motive(zero, &|d, x| d.lt(x, two));
        d.transport(zero, motive3, lt_zero_two, m0, eq_rev)
    };
    let at_one = {
        let one2 = d.num(1);
        let m1 = d.mul(one2, bit_b);
        let one_mul_eq = d.lemma(p.one_mul, &[bit_b]);
        let lt_bitb_two = d.lemma(p.mod_lt, &[orig_b, two, pos]);
        let eq_rev = d.symm(m1, bit_b, one_mul_eq);
        let motive3 = d.eq_motive(bit_b, &|d, x| d.lt(x, two));
        d.transport(bit_b, motive3, lt_bitb_two, m1, eq_rev)
    };
    let motive2 = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let m = d.mul(x, bit_b);
        d.lt(m, two)
    };
    cases_mod_two(d, &p, sa, &motive2, at_zero, at_one)
}

/// `Nat.land_div_two : ∀ a b, Eq (div (land a b) 2) (land (div a 2) (div b 2))`.
fn declare_land_div_two(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.land_div_two, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let two = d.num(2);
        let goal_at = |d: &mut NatDev<'_>, aa: ExprId, bb: ExprId| -> ExprId {
            let land_ab = d.const_app(p.land, &[aa, bb]);
            let lhs = d.div(land_ab, two);
            let div_a = d.div(aa, two);
            let div_b = d.div(bb, two);
            let rhs = d.const_app(p.land, &[div_a, div_b]);
            d.eq(lhs, rhs)
        };
        let motive = |d: &mut NatDev<'_>, aa: ExprId| -> ExprId { goal_at(d, aa, b) };
        let proof = cases_zero_succ(
            d,
            a,
            &motive,
            &|d| {
                // a = 0: `land 0 b = 0`; both sides reduce to `0`.
                let zero = d.zero();
                let land0b = d.const_app(p.land, &[zero, b]);
                let div_land0b = d.div(land0b, two);
                let land0b_eq_zero = d.lemma(p.land_zero_left, &[b]);
                let step_a = d.congr(land0b, zero, land0b_eq_zero, &|d, h| d.div(h, two));
                let div0_2 = d.div(zero, two);
                let div0_2_eq_zero = d.lemma(p.zero_div, &[two]);
                let lhs_chain = d.trans(div_land0b, div0_2, zero, step_a, div0_2_eq_zero);

                let div_b = d.div(b, two);
                let rhs = d.const_app(p.land, &[div0_2, div_b]);
                let step_r = d.congr(div0_2, zero, div0_2_eq_zero, &|d, h| {
                    d.const_app(p.land, &[h, div_b])
                });
                let land0_divb = d.const_app(p.land, &[zero, div_b]);
                let land0_divb_eq_zero = d.lemma(p.land_zero_left, &[div_b]);
                let rhs_chain = d.trans(rhs, land0_divb, zero, step_r, land0_divb_eq_zero);
                let rhs_chain_rev = d.symm(rhs, zero, rhs_chain);
                d.trans(div_land0b, zero, rhs, lhs_chain, rhs_chain_rev)
            },
            &|d, pa| {
                let sa = d.succ(pa);
                cases_zero_succ(
                    d,
                    b,
                    &|d, bb| goal_at(d, sa, bb),
                    &|d| {
                        // b = 0, a = succ pa: `land sa 0 = 0`.
                        let zero = d.zero();
                        let landa0 = d.const_app(p.land, &[sa, zero]);
                        let div_landa0 = d.div(landa0, two);
                        let landa0_eq_zero = d.lemma(p.land_zero_right, &[sa]);
                        let step_a = d.congr(landa0, zero, landa0_eq_zero, &|d, h| d.div(h, two));
                        let div0_2 = d.div(zero, two);
                        let div0_2_eq_zero = d.lemma(p.zero_div, &[two]);
                        let lhs_chain = d.trans(div_landa0, div0_2, zero, step_a, div0_2_eq_zero);

                        let div_a = d.div(sa, two);
                        let rhs = d.const_app(p.land, &[div_a, div0_2]);
                        let step_r = d.congr(div0_2, zero, div0_2_eq_zero, &|d, h| {
                            d.const_app(p.land, &[div_a, h])
                        });
                        let landa_0 = d.const_app(p.land, &[div_a, zero]);
                        let landa_0_eq_zero = d.lemma(p.land_zero_right, &[div_a]);
                        let rhs_chain = d.trans(rhs, landa_0, zero, step_r, landa_0_eq_zero);
                        let rhs_chain_rev = d.symm(rhs, zero, rhs_chain);
                        d.trans(div_landa0, zero, rhs, lhs_chain, rhs_chain_rev)
                    },
                    &|d, pb| {
                        // The genuinely bitwise case: one unfold on each side.
                        let sb = d.succ(pb);
                        let half_a = d.div(sa, two);
                        let half_b = d.div(sb, two);
                        let bit_a = d.modulo(sa, two);
                        let bit_b = d.modulo(sb, two);
                        let bit_and = d.mul(bit_a, bit_b);
                        let rec = d.const_app(p.land_aux, &[pa, half_a, half_b]);

                        let bit_and_lt_two = bit_product_lt_two(d, &p, sa, sb);
                        let div_land_ab_eq_rec =
                            div_two_mul_add_of_lt(d, &p, rec, bit_and, bit_and_lt_two);

                        let le_refl_sa = d.lemma(p.le_refl, &[sa]);
                        let half_le_pa = half_le_predecessor_of_succ(d, &p, pa, pa, le_refl_sa);
                        let le_refl_half_a = d.lemma(p.le_refl, &[half_a]);
                        let agree = d.lemma(
                            p.land_aux_agree_of_fuel,
                            &[pa, half_a, half_b, half_a, half_le_pa, le_refl_half_a],
                        );

                        let land_sa_sb = d.const_app(p.land, &[sa, sb]);
                        let div_land_ab = d.div(land_sa_sb, two);
                        let land_halves = d.const_app(p.land, &[half_a, half_b]);
                        d.trans(div_land_ab, rec, land_halves, div_land_ab_eq_rec, agree)
                    },
                )
            },
        );
        (goal_at(d, a, b), proof)
    })?;
    Ok(())
}

/// Declare [`declare_land_div_two`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_land_div_two_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_land_div_two(d, p)?;
    Ok(())
}
