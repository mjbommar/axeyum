//! `Nat.lcm`, the least common multiple, and its checked properties.
//!
//! `lcm a b := div (mul a b) (gcd a b)`. The only degenerate point is
//! `a = b = 0`, where `gcd 0 0 = 0` and `div _ 0 = 0` (this kernel's totality
//! convention), so `lcm 0 0` computes to `0` — matching Mathlib's convention —
//! and every theorem below is proved **unconditionally**, with the zero case
//! handled by `zero_mul`/`zero_div` alone (never by computing `gcd 0 b`, so
//! `Nat.gcd_zero_right` — which this prelude does not have — is never needed).
//!
//! `dvd_lcm_left`/`dvd_lcm_right` and `gcd_mul_lcm` all split on whether the
//! left argument is `zero` or `succ k`. At `succ k` the left argument is
//! positive, so `gcd (succ k) b` is positive too (`one_le_of_dvd_pos` against
//! `gcd_dvd_left`), and `div_mul_cancel_of_dvd` together with
//! `mul_left_cancel_of_pos` does the cancellation.
//!
//! `Nat.lcm_dvd` (the universal/"least" property: `a ∣ c → b ∣ c → lcm a b ∣ c`)
//! is **not** attempted here. Its standard proof needs a coprime-cancellation
//! ("Gauss's lemma") fact — `gcd x y = 1 ∧ x ∣ y*z → x ∣ z` — that is not yet
//! in this prelude, and building it from `gcd_bezout` is comparable in size to
//! `coprime_of_bezout_one`'s own ~250-line proof. `dvd_lcm_left`/`_right` (lcm
//! is *a* common multiple) and `gcd_mul_lcm` (the headline identity) land
//! without it.

use super::NatPrelude;
use super::helpers::transport_dvd_right;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

pub(super) fn declare_lcm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    declare_lcm_definition(d, &p)?;
    declare_lcm_zero_left(d, &p)?;
    declare_dvd_lcm_left(d, &p)?;
    declare_dvd_lcm_right(d, &p)?;
    declare_gcd_mul_lcm(d, &p)?;
    Ok(())
}

/// `Nat.lcm a b := div (mul a b) (gcd a b)`.
fn declare_lcm_definition(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let product = d.mul(a, b);
    let common = d.gcd(a, b);
    let quotient = d.div(product, common);
    let value = {
        let with_b = d.lam_fv(b_fv, nat, quotient);
        d.lam_fv(a_fv, nat, with_b)
    };
    let ty = {
        let inner = d.arrow(nat, nat);
        d.arrow(nat, inner)
    };
    // Strictly greater delta height than every definition it calls
    // (`gcd` is 10, `div` is 3, `mul` is 2).
    d.kernel().add_declaration(Declaration::Definition {
        name: p.lcm,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(11),
    })
}

/// `lcm_zero_left : ∀ b, lcm zero b = zero`.
///
/// `mul zero b = zero` (`zero_mul`) turns the numerator into `zero`, and
/// `div zero _ = zero` (`zero_div`) closes it from there — no need to compute
/// `gcd zero b` at all.
fn declare_lcm_zero_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.lcm_zero_left, 1, &|d, values| {
        let b = values[0];
        let zero = d.zero();
        let common = d.gcd(zero, b);
        let lcm0b = d.const_app(p.lcm, &[zero, b]);
        let product = d.mul(zero, b);

        let zero_mul_eq = d.lemma(p.zero_mul, &[b]); // Eq product zero
        let div_zero_side = d.div(zero, common);
        let step1 = d.congr(product, zero, zero_mul_eq, &|d, x| d.div(x, common));
        let div_zero_eq = d.lemma(p.zero_div, &[common]); // Eq div_zero_side zero
        let (_, proof) = d.chain(lcm0b, &[(div_zero_side, step1), (zero, div_zero_eq)]);
        (d.eq(lcm0b, zero), proof)
    })?;
    Ok(())
}

/// `dvd_lcm_left : ∀ a b, dvd a (lcm a b)`.
fn declare_dvd_lcm_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dvd_lcm_left, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let goal_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let lcm_xb = d.const_app(p.lcm, &[x, b]);
            d.dvd(x, lcm_xb)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let lcm0b = d.const_app(p.lcm, &[zero, b]);
            let lz = d.lemma(p.lcm_zero_left, &[b]); // Eq lcm0b zero
            let lz_rev = d.symm(lcm0b, zero, lz); // Eq zero lcm0b
            let dvd_zero_zero = d.lemma(p.dvd_zero, &[zero]); // dvd zero zero
            transport_dvd_right(d, zero, zero, lcm0b, lz_rev, dvd_zero_zero)
        };
        let step = |d: &mut NatDev<'_>, k: ExprId, _ih: ExprId| -> ExprId {
            let a = d.succ(k);
            let common = d.gcd(a, b);
            let lcm_ab = d.const_app(p.lcm, &[a, b]);
            let product = d.mul(a, b);
            let goal = d.dvd(a, lcm_ab);

            let a_pos = d.zero_lt_succ(k);
            let gcd_dvd_a = d.lemma(p.gcd_dvd_left, &[a, b]); // dvd common a
            let common_pos = d.lemma(p.one_le_of_dvd_pos, &[common, a, a_pos, gcd_dvd_a]);
            let gcd_dvd_b = d.lemma(p.gcd_dvd_right, &[a, b]); // dvd common b

            dvd_elim(d, common, b, goal, gcd_dvd_b, &|d, c, b_eq| {
                // b_eq : Eq b (mul common c)
                let g_c = d.mul(common, c);
                let step1 = d.congr(b, g_c, b_eq, &|d, x| d.mul(a, x));
                // step1 : Eq product (mul a g_c)
                let a_gc = d.mul(a, g_c);
                let reassoc = reassociate_a_gc(d, &p, a, common, c);
                // reassoc : Eq a_gc (mul common (mul a c))
                let ac = d.mul(a, c);
                let g_ac = d.mul(common, ac);
                let (_, product_eq_g_ac) = d.chain(product, &[(a_gc, step1), (g_ac, reassoc)]);

                let div_g_ac_common = d.div(g_ac, common);
                let step2 = d.congr(product, g_ac, product_eq_g_ac, &|d, x| d.div(x, common));
                let dvd_g_ac = d.lemma(p.dvd_mul, &[common, ac]); // dvd common g_ac
                let cancel = d.lemma(
                    p.div_mul_cancel_of_dvd,
                    &[common, g_ac, common_pos, dvd_g_ac],
                );
                // cancel : Eq (mul common div_g_ac_common) g_ac
                let cancel_final = d.lemma(
                    p.mul_left_cancel_of_pos,
                    &[common, div_g_ac_common, ac, common_pos, cancel],
                );
                // cancel_final : Eq div_g_ac_common ac
                let (_, lcm_eq_ac) =
                    d.chain(lcm_ab, &[(div_g_ac_common, step2), (ac, cancel_final)]);
                dvd_intro(d, a, lcm_ab, c, lcm_eq_ac)
            })
        };
        let proof = d.induct(&goal_at, &base, &step, a);
        (goal_at(d, a), proof)
    })?;
    Ok(())
}

/// `dvd_lcm_right : ∀ a b, dvd b (lcm a b)`.
fn declare_dvd_lcm_right(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dvd_lcm_right, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let goal_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let lcm_xb = d.const_app(p.lcm, &[x, b]);
            d.dvd(b, lcm_xb)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let lcm0b = d.const_app(p.lcm, &[zero, b]);
            let lz = d.lemma(p.lcm_zero_left, &[b]); // Eq lcm0b zero
            let lz_rev = d.symm(lcm0b, zero, lz); // Eq zero lcm0b
            let dvd_zero_b = d.lemma(p.dvd_zero, &[b]); // dvd b zero
            transport_dvd_right(d, b, zero, lcm0b, lz_rev, dvd_zero_b)
        };
        let step = |d: &mut NatDev<'_>, k: ExprId, _ih: ExprId| -> ExprId {
            let a = d.succ(k);
            let common = d.gcd(a, b);
            let lcm_ab = d.const_app(p.lcm, &[a, b]);
            let product = d.mul(a, b);
            let goal = d.dvd(b, lcm_ab);

            let a_pos = d.zero_lt_succ(k);
            let gcd_dvd_a = d.lemma(p.gcd_dvd_left, &[a, b]); // dvd common a
            let common_pos = d.lemma(p.one_le_of_dvd_pos, &[common, a, a_pos, gcd_dvd_a]);

            dvd_elim(d, common, a, goal, gcd_dvd_a, &|d, c, a_eq| {
                // a_eq : Eq a (mul common c)
                let g_c = d.mul(common, c);
                let step1 = d.congr(a, g_c, a_eq, &|d, x| d.mul(x, b));
                // step1 : Eq product (mul g_c b)
                let g_c_b = d.mul(g_c, b);
                let cb = d.mul(c, b);
                let g_cb = d.mul(common, cb);
                let assoc = d.lemma(p.mul_assoc, &[common, c, b]); // Eq g_c_b g_cb
                let (_, product_eq_g_cb) = d.chain(product, &[(g_c_b, step1), (g_cb, assoc)]);

                let div_g_cb_common = d.div(g_cb, common);
                let step2 = d.congr(product, g_cb, product_eq_g_cb, &|d, x| d.div(x, common));
                let dvd_g_cb = d.lemma(p.dvd_mul, &[common, cb]); // dvd common g_cb
                let cancel = d.lemma(
                    p.div_mul_cancel_of_dvd,
                    &[common, g_cb, common_pos, dvd_g_cb],
                );
                // cancel : Eq (mul common div_g_cb_common) g_cb
                let cancel_final = d.lemma(
                    p.mul_left_cancel_of_pos,
                    &[common, div_g_cb_common, cb, common_pos, cancel],
                );
                // cancel_final : Eq div_g_cb_common cb
                let (_, lcm_eq_cb) =
                    d.chain(lcm_ab, &[(div_g_cb_common, step2), (cb, cancel_final)]);
                let comm = d.lemma(p.mul_comm, &[c, b]); // Eq cb (mul b c)
                let bc = d.mul(b, c);
                let (_, lcm_eq_bc) = d.chain(lcm_ab, &[(cb, lcm_eq_cb), (bc, comm)]);
                dvd_intro(d, b, lcm_ab, c, lcm_eq_bc)
            })
        };
        let proof = d.induct(&goal_at, &base, &step, a);
        (goal_at(d, a), proof)
    })?;
    Ok(())
}

/// `gcd_mul_lcm : ∀ a b, gcd a b * lcm a b = a * b`, unconditional.
fn declare_gcd_mul_lcm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gcd_mul_lcm, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let goal_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let common = d.gcd(x, b);
            let lcm_xb = d.const_app(p.lcm, &[x, b]);
            let product = d.mul(x, b);
            let mul_common_lcm_xb = d.mul(common, lcm_xb);
            d.eq(mul_common_lcm_xb, product)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let common0 = d.gcd(zero, b);
            let lcm0 = d.const_app(p.lcm, &[zero, b]);
            let product0 = d.mul(zero, b);

            let zero_mul_eq = d.lemma(p.zero_mul, &[b]); // Eq product0 zero
            let div_zero_side = d.div(zero, common0);
            let step1 = d.congr(product0, zero, zero_mul_eq, &|d, x| d.div(x, common0));
            let div_zero_eq = d.lemma(p.zero_div, &[common0]); // Eq div_zero_side zero
            let (_, lcm0_is_zero) = d.chain(lcm0, &[(div_zero_side, step1), (zero, div_zero_eq)]);
            // lcm0_is_zero : Eq lcm0 zero

            let mul_common0_lcm0 = d.mul(common0, lcm0);
            let mul_common0_zero = d.mul(common0, zero);
            let mul_congr = d.congr(lcm0, zero, lcm0_is_zero, &|d, x| d.mul(common0, x));
            let mul_zero_eq = d.lemma(p.mul_zero, &[common0]); // Eq mul_common0_zero zero
            let zero_to_product0 = d.symm(product0, zero, zero_mul_eq); // Eq zero product0
            let (_, proof) = d.chain(
                mul_common0_lcm0,
                &[
                    (mul_common0_zero, mul_congr),
                    (zero, mul_zero_eq),
                    (product0, zero_to_product0),
                ],
            );
            proof
        };
        let step = |d: &mut NatDev<'_>, k: ExprId, _ih: ExprId| -> ExprId {
            let a = d.succ(k);
            let common = d.gcd(a, b);
            let product = d.mul(a, b);
            let a_pos = d.zero_lt_succ(k);
            let gcd_dvd_a = d.lemma(p.gcd_dvd_left, &[a, b]); // dvd common a
            let common_pos = d.lemma(p.one_le_of_dvd_pos, &[common, a, a_pos, gcd_dvd_a]);
            let common_dvd_product = d.lemma(p.dvd_mul_right_of_dvd, &[common, a, b, gcd_dvd_a]);
            // Eq (mul common (div product common)) product, and `div product
            // common` is `lcm a b` by definition — the goal, verbatim.
            d.lemma(
                p.div_mul_cancel_of_dvd,
                &[common, product, common_pos, common_dvd_product],
            )
        };
        let proof = d.induct(&goal_at, &base, &step, a);
        (goal_at(d, a), proof)
    })?;
    Ok(())
}

/// `Eq (mul a (mul g c)) (mul g (mul a c))` — reassociate the outer factor
/// past a nested product, via `mul_assoc` then `mul_comm` then `mul_assoc`.
fn reassociate_a_gc(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, g: ExprId, c: ExprId) -> ExprId {
    let p = *p;
    let gc = d.mul(g, c);
    let a_gc = d.mul(a, gc);
    let ag = d.mul(a, g);
    let ag_c = d.mul(ag, c);
    let assoc1 = d.lemma(p.mul_assoc, &[a, g, c]); // Eq ag_c a_gc
    let step1 = d.symm(ag_c, a_gc, assoc1); // Eq a_gc ag_c

    let ga = d.mul(g, a);
    let comm = d.lemma(p.mul_comm, &[a, g]); // Eq ag ga
    let step2 = d.congr(ag, ga, comm, &|d, x| d.mul(x, c)); // Eq ag_c ga_c
    let ga_c = d.mul(ga, c);

    let ac = d.mul(a, c);
    let g_ac = d.mul(g, ac);
    let assoc2 = d.lemma(p.mul_assoc, &[g, a, c]); // Eq ga_c g_ac

    let (_, chained) = d.chain(a_gc, &[(ag_c, step1), (ga_c, step2), (g_ac, assoc2)]);
    chained
}

/// Eliminate `dvd_hyp : dvd divisor dividend`, continuing with the witness `q`
/// and `eq_proof : Eq dividend (mul divisor q)` to build a proof of `goal`
/// (which must not mention `q`).
fn dvd_elim(
    d: &mut NatDev<'_>,
    divisor: ExprId,
    dividend: ExprId,
    goal: ExprId,
    dvd_hyp: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let predicate = d.dvd_predicate(divisor, dividend);
    let dvd_ty = d.dvd(divisor, dividend);
    let motive = d.kernel().lam(anon, dvd_ty, goal, BinderInfo::Default);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let divisor_q = d.mul(divisor, q);
        let eq_ty = d.eq(dividend, divisor_q);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);
        let body = continuation(d, q, eq_proof);
        let with_eq = d.lam_fv(eq_fv, eq_ty, body);
        d.lam_fv(q_fv, nat, with_eq)
    };
    let exists_rec_name = d.prelude().logic.exists_rec;
    let rec = d.kernel().const_(exists_rec_name, vec![one]);
    d.apply(rec, &[nat, predicate, motive, minor, dvd_hyp])
}

/// Build a proof of `dvd a n` from a witness `q` and `eq_proof : Eq n (mul a q)`.
fn dvd_intro(
    d: &mut NatDev<'_>,
    a: ExprId,
    n: ExprId,
    witness: ExprId,
    eq_proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = d.dvd_predicate(a, n);
    let intro_name = d.prelude().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[nat, predicate, witness, eq_proof])
}
