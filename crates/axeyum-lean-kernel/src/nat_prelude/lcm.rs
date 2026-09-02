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
//! `Nat.gauss_lemma` (`gcd x y = 1 → x ∣ y*z → x ∣ z`) is declared here too,
//! after `gcd_bezout` (see `nat_prelude.rs`'s call order: `declare_lcm` runs
//! *before* `declare_gcd_bezout`, since the plain lcm facts above don't need
//! it, but `declare_gauss_lemma` is a separate function called *after*
//! `declare_gcd_bezout`).
//!
//! It is built by induction on `x`: at `x = zero`, `gcd zero y = y`
//! (`gcd_zero_left`) forces `y = 1`, collapsing `dvd zero (mul y z)` to
//! `dvd zero z` via `one_mul`. At `x = succ k`, `gcd_bezout` transported
//! along the `gcd x y = 1` hypothesis gives a Bézout certificate
//! `(1 + x·mn) + y·nn = x·mp + y·np`; scaling by `z` and using `x ∣ y*z` on
//! the `y·nn·z`/`y·np·z` terms puts the identity in the shape `z + X = Y`
//! with `x ∣ X` and `x ∣ Y`, and `dvd_add_right_cancel_of_pos` (needing
//! `1 ≤ x`, free from `succ k`'s positivity) yields `x ∣ z`. This is exactly
//! the `g = 1` branch of `euclid_lemma`'s proof with the primality side
//! condition dropped — that branch already *is* Gauss's lemma, just inlined
//! under a hypothesis (`2 ≤ prime ∧ …`) stronger than the `gcd = 1` this
//! version starts from.
//!
//! `Nat.lcm_dvd` (the universal/"least" property:
//! `a ∣ c → b ∣ c → lcm a b ∣ c`) is landed below. The route
//! is: split on `a`. At `a = zero`, `lcm zero b = zero` (`lcm_zero_left`) and
//! the hypothesis `dvd zero c` is already the goal. At `a = succ k`,
//! `g := gcd a b` is positive (`one_le_of_dvd_pos` against `gcd_dvd_left`);
//! write `a = g·a1`, `b = g·b1` via `gcd_dvd_left`/`_right`, and
//! `gcd_cofactors_coprime` (already in `bezout.rs`, built for
//! `Rat.normalize`) gives `gcd a1 b1 = 1` since `gcd (g·a1) (g·b1) = gcd a b
//! = g` by construction. From `b ∣ c`, write `c = b·p = (g·b1)·p`; from
//! `a ∣ c`, `(g·a1) ∣ (g·b1)·p`, and cancelling `g`
//! (`mul_left_cancel_of_pos`, after reassociating) gives `a1 ∣ (b1·p)`.
//! `gauss_lemma` on `gcd a1 b1 = 1` then yields `a1 ∣ p`, say `p = a1·q`;
//! `lcm a b = g·a1·b1` (from `gcd_mul_lcm` cancelled by `g`), so
//! `c = (g·b1)·(a1·q) = (g·a1·b1)·q = lcm a b · q`. No `gcd_comm` is needed
//! because the witness taken from `c = b·p` is the one fed through the `a`
//! side's cancellation — the roles are asymmetric on purpose so the
//! coprimality order `gcd a1 b1 = 1` (matching `gcd_cofactors_coprime`'s
//! output order) is exactly what `gauss_lemma` consumes. A first attempt at
//! this landed as a deeply-nested `dvd_elim` chain that could not be
//! hand-verified to typecheck (several nested eliminations shared a `goal`
//! parameter that has to be the *same* fixed Prop at every level, which a
//! first draft got wrong more than once) and was reverted rather than risk
//! shipping something never run through `Kernel::add_declaration`. The
//! landed version below is exactly that deeply-nested `dvd_elim` chain
//! (five levels: `a1`, `b1`, `p`, `q`, `q2`), but every algebraic step
//! (coprimality of the cofactors, `lcm a b = g·a1·b1`, the `g`-cancellation,
//! and the final reassembly) is factored into its own top-level helper
//! function so each is checkable in isolation, and the single `goal`
//! `ExprId` is computed exactly once and threaded through unchanged, never
//! recomputed at a deeper level.

use super::NatPrelude;
use super::bezout::bezout_elim;
use super::crt::{gap_dvd, modeq_of_dvd_gap};
use super::helpers::{transport_dvd_left, transport_dvd_right};
use super::ops::{NatDev, NatOps};
use super::steps::dvd_elim;
use super::steps::dvd_intro;
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

/// `gauss_lemma : ∀ x y z, gcd x y = 1 → dvd x (mul y z) → dvd x z`.
///
/// Must run **after** `declare_gcd_bezout` (see the module doc); called
/// separately from `declare_lcm` in `nat_prelude.rs` for that reason.
pub(super) fn declare_gauss_lemma(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gauss_lemma, 3, &|d, values| {
        let (x, y, z) = (values[0], values[1], values[2]);
        let one = d.num(1);
        let yz = d.mul(y, z);
        let goal_at = |d: &mut NatDev<'_>, xv: ExprId| -> ExprId {
            let common = d.gcd(xv, y);
            let coprime_ty = d.eq(common, one);
            let hyp_ty = d.dvd(xv, yz);
            let concl = d.dvd(xv, z);
            let inner = d.arrow(hyp_ty, concl);
            d.arrow(coprime_ty, inner)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let common0 = d.gcd(zero, y);
            let coprime_ty = d.eq(common0, one);
            let hyp_ty = d.dvd(zero, yz);

            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hyp2_fv = d.fresh_fvar();
            let hyp2 = d.kernel().fvar(hyp2_fv);

            // `y = 1`: `common0 = y` (`gcd_zero_left`) and `common0 = 1` (`h`).
            let gzl = d.lemma(p.gcd_zero_left, &[y]); // Eq common0 y
            let y_eq_common0 = d.symm(common0, y, gzl); // Eq y common0
            let y_eq_one = d.trans(y, common0, one, y_eq_common0, h); // Eq y one

            // `mul y z = mul one z = z`.
            let one_z = d.mul(one, z);
            let mul_congr = d.congr(y, one, y_eq_one, &|d, t| d.mul(t, z));
            let one_mul_eq = d.lemma(p.one_mul, &[z]); // Eq one_z z
            let (_, yz_eq_z) = d.chain(yz, &[(one_z, mul_congr), (z, one_mul_eq)]);

            let motive = d.eq_motive(yz, &|d, v| d.dvd(zero, v));
            let concl_proof = d.transport(yz, motive, hyp2, z, yz_eq_z);

            let with_hyp2 = d.lam_fv(hyp2_fv, hyp_ty, concl_proof);
            d.lam_fv(h_fv, coprime_ty, with_hyp2)
        };
        let step = |d: &mut NatDev<'_>, k: ExprId, _ih: ExprId| -> ExprId {
            let xv = d.succ(k);
            let common = d.gcd(xv, y);
            let coprime_ty = d.eq(common, one);
            let hyp_ty = d.dvd(xv, yz);
            let concl = d.dvd(xv, z);

            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hyp2_fv = d.fresh_fvar();
            let hyp2 = d.kernel().fvar(hyp2_fv);

            // `0 < succ k`, defeq to `1 ≤ succ k` since `Lt a b := Le (succ a) b`.
            let one_le_x = d.zero_lt_succ(k);

            let certificate = {
                let base = d.lemma(p.gcd_bezout, &[xv, y]);
                let motive = d.eq_motive(common, &|d, v| d.bezout(xv, y, v));
                d.transport(common, motive, base, one, h)
            };

            let divides_z_proof = bezout_elim(
                d,
                xv,
                y,
                one,
                concl,
                certificate,
                &|d, mp, mn, np, nn, equation| {
                    let unit = d.num(1);
                    let x_mn = d.mul(xv, mn);
                    let y_nn = d.mul(y, nn);
                    let x_mp = d.mul(xv, mp);
                    let y_np = d.mul(y, np);
                    let left_head = d.add(unit, x_mn);
                    let left = d.add(left_head, y_nn);
                    let right = d.add(x_mp, y_np);

                    // Scale the identity by `z`.
                    let scaled = d.congr(left, right, equation, &|d, t| d.mul(t, z));
                    let left_z = d.mul(left, z);
                    let right_z = d.mul(right, z);

                    let x_mn_z = d.mul(x_mn, z);
                    let y_nn_z = d.mul(y_nn, z);
                    let x_mp_z = d.mul(x_mp, z);
                    let y_np_z = d.mul(y_np, z);

                    // `(x·k)·z = x·(k·z)`, so `dvd_mul` applies after reassociating.
                    let divides_x_multiple = |d: &mut NatDev<'_>, k: ExprId| {
                        let inner = d.mul(k, z);
                        let base = d.lemma(p.dvd_mul, &[xv, inner]);
                        let assoc = d.lemma(p.mul_assoc, &[xv, k, z]);
                        let head = d.mul(xv, k);
                        let flat = d.mul(head, z);
                        let nested = d.mul(xv, inner);
                        let back = d.symm(flat, nested, assoc);
                        let motive = d.eq_motive(nested, &|d, v| d.dvd(xv, v));
                        d.transport(nested, motive, base, flat, back)
                    };
                    // `(y·k)·z = (y·z)·k`, so `dvd x (y·z)` carries over.
                    let divides_y_multiple = |d: &mut NatDev<'_>, k: ExprId| {
                        let base = d.lemma(p.dvd_mul_right_of_dvd, &[xv, yz, k, hyp2]);
                        let yz_k = d.mul(yz, k);
                        let y_k = d.mul(y, k);
                        let flat = d.mul(y_k, z);
                        let z_k = d.mul(z, k);
                        let k_z = d.mul(k, z);
                        let step1 = d.lemma(p.mul_assoc, &[y, z, k]);
                        let nested_zk = d.mul(y, z_k);
                        let commute = d.lemma(p.mul_comm, &[z, k]);
                        let step2 = d.congr(z_k, k_z, commute, &|d, t| d.mul(y, t));
                        let nested_kz = d.mul(y, k_z);
                        let assoc_back = d.lemma(p.mul_assoc, &[y, k, z]);
                        let step3 = d.symm(flat, nested_kz, assoc_back);
                        let (_, chained) = d.chain(
                            yz_k,
                            &[(nested_zk, step1), (nested_kz, step2), (flat, step3)],
                        );
                        let motive = d.eq_motive(yz_k, &|d, v| d.dvd(xv, v));
                        d.transport(yz_k, motive, base, flat, chained)
                    };

                    let d_x_mn_z = divides_x_multiple(d, mn);
                    let d_y_nn_z = divides_y_multiple(d, nn);
                    let d_x_mp_z = divides_x_multiple(d, mp);
                    let d_y_np_z = divides_y_multiple(d, np);

                    // `X = x·mn·z + y·nn·z`, and `x ∣ X`.
                    let excess = d.add(x_mn_z, y_nn_z);
                    let divides_excess =
                        d.lemma(p.dvd_add, &[xv, x_mn_z, y_nn_z, d_x_mn_z, d_y_nn_z]);
                    // `Y = x·mp·z + y·np·z`, and `x ∣ Y`; `Y = right·z`.
                    let total = d.add(x_mp_z, y_np_z);
                    let divides_total =
                        d.lemma(p.dvd_add, &[xv, x_mp_z, y_np_z, d_x_mp_z, d_y_np_z]);
                    let right_expand = d.lemma(p.right_distrib, &[x_mp, y_np, z]);
                    let divides_right_z = {
                        let back = d.symm(right_z, total, right_expand);
                        let motive = d.eq_motive(total, &|d, v| d.dvd(xv, v));
                        d.transport(total, motive, divides_total, right_z, back)
                    };

                    // `left·z = (z + x·mn·z) + y·nn·z = z + X`.
                    let outer = d.lemma(p.right_distrib, &[left_head, y_nn, z]);
                    let head_z = d.mul(left_head, z);
                    let split_outer = d.add(head_z, y_nn_z);
                    let inner_expand = d.lemma(p.right_distrib, &[unit, x_mn, z]);
                    let unit_z = d.mul(unit, z);
                    let split_inner = d.add(unit_z, x_mn_z);
                    let step_inner =
                        d.congr(head_z, split_inner, inner_expand, &|d, t| d.add(t, y_nn_z));
                    let with_unit = d.add(split_inner, y_nn_z);
                    let one_mul = d.lemma(p.one_mul, &[z]);
                    let z_plus = d.add(z, x_mn_z);
                    let step_one = d.congr(unit_z, z, one_mul, &|d, t| {
                        let head = d.add(t, x_mn_z);
                        d.add(head, y_nn_z)
                    });
                    let flattened = d.add(z_plus, y_nn_z);
                    let assoc = d.lemma(p.add_assoc, &[z, x_mn_z, y_nn_z]);
                    let z_plus_excess = d.add(z, excess);
                    let (_, left_normalised) = d.chain(
                        left_z,
                        &[
                            (split_outer, outer),
                            (with_unit, step_inner),
                            (flattened, step_one),
                            (z_plus_excess, assoc),
                        ],
                    );

                    // `z + X = right·z`, so `x ∣ z + X`; commute to `X + z`.
                    let bridge = {
                        let back = d.symm(left_z, z_plus_excess, left_normalised);
                        let (_, joined) =
                            d.chain(z_plus_excess, &[(left_z, back), (right_z, scaled)]);
                        joined
                    };
                    let divides_z_plus = {
                        let back = d.symm(z_plus_excess, right_z, bridge);
                        let motive = d.eq_motive(right_z, &|d, v| d.dvd(xv, v));
                        d.transport(right_z, motive, divides_right_z, z_plus_excess, back)
                    };
                    let excess_plus_z = d.add(excess, z);
                    let commute = d.lemma(p.add_comm, &[z, excess]);
                    let divides_excess_plus = {
                        let motive = d.eq_motive(z_plus_excess, &|d, v| d.dvd(xv, v));
                        d.transport(
                            z_plus_excess,
                            motive,
                            divides_z_plus,
                            excess_plus_z,
                            commute,
                        )
                    };

                    d.lemma(
                        p.dvd_add_right_cancel_of_pos,
                        &[xv, excess, z, one_le_x, divides_excess, divides_excess_plus],
                    )
                },
            );

            let with_hyp2 = d.lam_fv(hyp2_fv, hyp_ty, divides_z_proof);
            d.lam_fv(h_fv, coprime_ty, with_hyp2)
        };
        let proof = d.induct(&goal_at, &base, &step, x);
        (goal_at(d, x), proof)
    })?;
    Ok(())
}

/// `Nat.lcm_dvd : ∀ a b c, dvd a c → dvd b c → dvd (lcm a b) c` — the
/// "least" half of the least common multiple's universal property. See the
/// module doc for the route.
pub(super) fn declare_lcm_dvd(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.lcm_dvd, 3, &|d, values| {
        let (a, b, c) = (values[0], values[1], values[2]);
        let goal_at = |d: &mut NatDev<'_>, xv: ExprId| -> ExprId {
            let lcm_xb = d.const_app(p.lcm, &[xv, b]);
            let hyp1 = d.dvd(xv, c);
            let hyp2 = d.dvd(b, c);
            let concl = d.dvd(lcm_xb, c);
            let inner = d.arrow(hyp2, concl);
            d.arrow(hyp1, inner)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let lcm0b = d.const_app(p.lcm, &[zero, b]);
            let hyp1_ty = d.dvd(zero, c);
            let hyp2_ty = d.dvd(b, c);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let h2_fv = d.fresh_fvar();

            let lz = d.lemma(p.lcm_zero_left, &[b]); // Eq lcm0b zero
            let zero_to_lcm0b = d.symm(lcm0b, zero, lz); // Eq zero lcm0b
            let concl = transport_dvd_left(d, zero, lcm0b, zero_to_lcm0b, c, h1);
            let with_h2 = d.lam_fv(h2_fv, hyp2_ty, concl);
            d.lam_fv(h1_fv, hyp1_ty, with_h2)
        };
        let step = |d: &mut NatDev<'_>, k: ExprId, _ih: ExprId| -> ExprId {
            let a = d.succ(k);
            let g = d.gcd(a, b);
            let lcm_ab = d.const_app(p.lcm, &[a, b]);
            let hyp1_ty = d.dvd(a, c);
            let hyp2_ty = d.dvd(b, c);
            // Computed exactly once, and threaded unchanged through every
            // nested `dvd_elim` below — never recomputed at a deeper level
            // (see the module doc's note on the reverted first attempt).
            let goal = d.dvd(lcm_ab, c);

            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv); // dvd a c
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv); // dvd b c

            let a_pos = d.zero_lt_succ(k);
            let gcd_dvd_a = d.lemma(p.gcd_dvd_left, &[a, b]); // dvd g a
            let gcd_dvd_b = d.lemma(p.gcd_dvd_right, &[a, b]); // dvd g b
            let g_pos = d.lemma(p.one_le_of_dvd_pos, &[g, a, a_pos, gcd_dvd_a]); // Le 1 g

            let body = dvd_elim(d, g, a, goal, gcd_dvd_a, &|d, a1, a_eq| {
                // a_eq : Eq a (mul g a1)
                dvd_elim(d, g, b, goal, gcd_dvd_b, &|d, b1, b_eq| {
                    // b_eq : Eq b (mul g b1)
                    let coprime = coprime_cofactors(d, &p, a, b, g, a1, b1, a_eq, b_eq, g_pos);
                    let lcm_ab_eq =
                        lcm_eq_scaled_cofactors(d, &p, a, b, g, lcm_ab, a1, b1, a_eq, b_eq, g_pos);

                    let g_a1 = d.mul(g, a1);
                    let dvd_ga1_c = transport_dvd_left(d, a, g_a1, a_eq, c, h1);

                    dvd_elim(d, b, c, goal, h2, &|d, p_, c_eq| {
                        // c_eq : Eq c (mul b p_)
                        let g_b1 = d.mul(g, b1);
                        let step3 = d.congr(b, g_b1, b_eq, &|d, x| d.mul(x, p_));
                        let b_p = d.mul(b, p_);
                        let gb1_p = d.mul(g_b1, p_);
                        let (_, c_eq2) = d.chain(c, &[(b_p, c_eq), (gb1_p, step3)]);
                        // c_eq2 : Eq c gb1_p

                        let dvd_ga1_gb1p = transport_dvd_right(d, g_a1, c, gb1_p, c_eq2, dvd_ga1_c);
                        // dvd g_a1 gb1_p

                        dvd_elim(d, g_a1, gb1_p, goal, dvd_ga1_gb1p, &|d, q, eq_q| {
                            // eq_q : Eq gb1_p (mul g_a1 q)
                            let dvd_a1_p =
                                a1_dvd_p_of_scaled(d, &p, g, a1, b1, p_, q, eq_q, g_pos, coprime);
                            // dvd_a1_p : dvd a1 p_

                            dvd_elim(d, a1, p_, goal, dvd_a1_p, &|d, q2, p_eq| {
                                // p_eq : Eq p_ (mul a1 q2)
                                let c_eq_final = c_eq_lcm_mul(
                                    d, &p, g, b1, a1, c, p_, q2, lcm_ab, c_eq2, p_eq, lcm_ab_eq,
                                );
                                // c_eq_final : Eq c (mul lcm_ab q2)
                                dvd_intro(d, lcm_ab, c, q2, c_eq_final)
                            })
                        })
                    })
                })
            });

            let with_h2 = d.lam_fv(h2_fv, hyp2_ty, body);
            d.lam_fv(h1_fv, hyp1_ty, with_h2)
        };
        let proof = d.induct(&goal_at, &base, &step, a);
        (goal_at(d, a), proof)
    })?;
    Ok(())
}

/// `Nat.dvd_antisymm : ∀ a b, dvd a b → dvd b a → Eq a b`.
///
/// Conceptually belongs beside `dvd_gcd`/`dvd_gcd_iff` in
/// `nat_prelude/divisibility.rs`, but lands here (flagged for promotion)
/// because it needs `le_of_dvd`, declared by `declare_primes` — called
/// *after* `declare_lcm` in `nat_prelude.rs`'s build order — and another
/// lane held `divisibility.rs` when this was built. Called separately from
/// `declare_lcm`/`declare_lcm_dvd` for exactly that ordering reason.
///
/// Double induction on `a` then `b` — both inner induction hypotheses are
/// unused, so this is a case split, not real recursion, exactly like
/// `two_le_succ_or_eq_one` in `primes.rs`. At `a = zero`, `dvd zero b`
/// forces `b = zero` directly via `zero_mul` (`b`'s own shape never needs
/// splitting, and `dvd b zero` is never used). At `a = succ k`, split on
/// `b`: `b = zero` forces `succ k = zero` from `dvd zero (succ k)` alone,
/// symmetrically — and that equation *is* the goal at that branch, so no
/// absurdity lemma is needed either. At `b = succ j` (both endpoints now
/// positive), `le_of_dvd` in both directions plus `le_antisymm` closes it.
pub(super) fn declare_dvd_antisymm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    d.theorem(p.dvd_antisymm, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let antisymm_at = |d: &mut NatDev<'_>, x: ExprId| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let xy = d.dvd(x, y);
            let yx = d.dvd(y, x);
            let equality = d.eq(x, y);
            let reverse = d.arrow(yx, equality);
            let body = d.arrow(xy, reverse);
            d.pi_fv(y_fv, nat, body)
        };
        let at_zero = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let zy = d.dvd(zero, y);
            let yz = d.dvd(y, zero);
            let target = d.eq(zero, y);

            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv); // dvd zero y
            let h2_fv = d.fresh_fvar();

            let body = dvd_elim(d, zero, y, target, h1, &|d, q, eq_proof| {
                // eq_proof : Eq y (mul zero q)
                let zero_q = d.mul(zero, q);
                let zm = d.lemma(p.zero_mul, &[q]); // Eq zero_q zero
                let (_, y_eq_zero) = d.chain(y, &[(zero_q, eq_proof), (zero, zm)]);
                d.symm(y, zero, y_eq_zero) // Eq zero y
            });
            let with_h2 = d.lam_fv(h2_fv, yz, body);
            let with_h1 = d.lam_fv(h1_fv, zy, with_h2);
            d.lam_fv(y_fv, nat, with_h1)
        };
        let step_a = |d: &mut NatDev<'_>, k: ExprId, _ih: ExprId| {
            let sx = d.succ(k);
            let a_pos = d.zero_lt_succ(k); // Le 1 sx
            let motive_y = |d: &mut NatDev<'_>, y: ExprId| {
                let sxy = d.dvd(sx, y);
                let ysx = d.dvd(y, sx);
                let equality = d.eq(sx, y);
                let reverse = d.arrow(ysx, equality);
                d.arrow(sxy, reverse)
            };
            let y_zero = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let sxz = d.dvd(sx, zero);
                let zsx = d.dvd(zero, sx);
                let target = d.eq(sx, zero);

                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv); // dvd zero sx

                let body = dvd_elim(d, zero, sx, target, h2, &|d, q, eq_proof| {
                    // eq_proof : Eq sx (mul zero q)
                    let zero_q = d.mul(zero, q);
                    let zm = d.lemma(p.zero_mul, &[q]); // Eq zero_q zero
                    let (_, sx_eq_zero) = d.chain(sx, &[(zero_q, eq_proof), (zero, zm)]);
                    sx_eq_zero // Eq sx zero -- the goal, verbatim
                });
                let with_h2 = d.lam_fv(h2_fv, zsx, body);
                d.lam_fv(h1_fv, sxz, with_h2)
            };
            let y_step = |d: &mut NatDev<'_>, j: ExprId, _inner_ih: ExprId| {
                let sy = d.succ(j);
                let b_pos = d.zero_lt_succ(j); // Le 1 sy
                let sxsy = d.dvd(sx, sy);
                let sysx = d.dvd(sy, sx);

                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv); // dvd sx sy
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv); // dvd sy sx

                let le1 = d.lemma(p.le_of_dvd, &[sx, sy, b_pos, h1]); // Le sx sy
                let le2 = d.lemma(p.le_of_dvd, &[sy, sx, a_pos, h2]); // Le sy sx
                let body = d.lemma(p.le_antisymm, &[sx, sy, le1, le2]); // Eq sx sy

                let with_h2 = d.lam_fv(h2_fv, sysx, body);
                d.lam_fv(h1_fv, sxsy, with_h2)
            };
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = d.induct(&motive_y, &y_zero, &y_step, y);
            d.lam_fv(y_fv, nat, body)
        };
        let all_b = d.induct(&antisymm_at, &at_zero, &step_a, a);
        let proof = d.apply(all_b, &[b]);
        let ab = d.dvd(a, b);
        let ba = d.dvd(b, a);
        let conclusion = d.eq(a, b);
        let reverse = d.arrow(ba, conclusion);
        let stmt = d.arrow(ab, reverse);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.lcm_comm : ∀ a b, lcm a b = lcm b a`. Direct from `dvd_antisymm`:
/// each of `lcm a b`/`lcm b a` divides the other via `lcm_dvd`, fed the
/// matching `dvd_lcm_left`/`dvd_lcm_right` witnesses with the endpoints
/// swapped.
pub(super) fn declare_lcm_comm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.lcm_comm, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let lcm_ab = d.const_app(p.lcm, &[a, b]);
        let lcm_ba = d.const_app(p.lcm, &[b, a]);

        // dvd (lcm a b) (lcm b a)
        let dvd_a_lcmba = d.lemma(p.dvd_lcm_right, &[b, a]); // dvd a (lcm b a)
        let dvd_b_lcmba = d.lemma(p.dvd_lcm_left, &[b, a]); // dvd b (lcm b a)
        let forward = d.lemma(p.lcm_dvd, &[a, b, lcm_ba, dvd_a_lcmba, dvd_b_lcmba]);

        // dvd (lcm b a) (lcm a b)
        let dvd_b_lcmab = d.lemma(p.dvd_lcm_right, &[a, b]); // dvd b (lcm a b)
        let dvd_a_lcmab = d.lemma(p.dvd_lcm_left, &[a, b]); // dvd a (lcm a b)
        let backward = d.lemma(p.lcm_dvd, &[b, a, lcm_ab, dvd_b_lcmab, dvd_a_lcmab]);

        let proof = d.lemma(p.dvd_antisymm, &[lcm_ab, lcm_ba, forward, backward]);
        (d.eq(lcm_ab, lcm_ba), proof)
    })?;
    Ok(())
}

/// `Nat.coprime_lcm_eq_mul : ∀ a b, gcd a b = 1 → lcm a b = a * b`. From the
/// unconditional `gcd_mul_lcm` (`gcd a b * lcm a b = a * b`), substitute the
/// coprimality hypothesis for `gcd a b` and cancel the leading `1` with
/// `one_mul`.
pub(super) fn declare_coprime_lcm_eq_mul(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_lcm_eq_mul, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let one = d.num(1);
        let gcd_ab = d.gcd(a, b);
        let lcm_ab = d.const_app(p.lcm, &[a, b]);
        let a_b = d.mul(a, b);
        let coprime_ty = d.eq(gcd_ab, one);
        let conclusion = d.eq(lcm_ab, a_b);
        let stmt = d.arrow(coprime_ty, conclusion);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv); // Eq gcd_ab one

        let gml = d.lemma(p.gcd_mul_lcm, &[a, b]); // Eq (mul gcd_ab lcm_ab) a_b
        let x = d.mul(gcd_ab, lcm_ab);
        let one_lcm = d.mul(one, lcm_ab);
        let step1 = d.congr(gcd_ab, one, h, &|d, t| d.mul(t, lcm_ab)); // Eq x one_lcm
        let one_mul_eq = d.lemma(p.one_mul, &[lcm_ab]); // Eq one_lcm lcm_ab

        let lcm_to_one_lcm = d.symm(one_lcm, lcm_ab, one_mul_eq); // Eq lcm_ab one_lcm
        let one_lcm_to_x = d.symm(x, one_lcm, step1); // Eq one_lcm x

        let (_, chained) = d.chain(
            lcm_ab,
            &[(one_lcm, lcm_to_one_lcm), (x, one_lcm_to_x), (a_b, gml)],
        );
        (stmt, d.lam_fv(h_fv, coprime_ty, chained))
    })?;
    Ok(())
}

/// `Eq (gcd a1 b1) 1`, given `a = g*a1`, `b = g*b1`, and `1 ≤ g`. Uses that
/// `g` **is** `gcd a b` by construction (the caller always passes the
/// literal `gcd a b` expression as `g`), so rewriting both arguments by
/// `a_eq`/`b_eq` turns `g` into `gcd (g*a1) (g*b1)`, which
/// `gcd_cofactors_coprime` consumes directly.
#[allow(clippy::too_many_arguments)]
fn coprime_cofactors(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    g: ExprId,
    a1: ExprId,
    b1: ExprId,
    a_eq: ExprId,
    b_eq: ExprId,
    g_pos: ExprId,
) -> ExprId {
    let p = *p;
    let g_a1 = d.mul(g, a1);
    let g_b1 = d.mul(g, b1);
    let step1 = d.congr(a, g_a1, a_eq, &|d, x| d.gcd(x, b)); // Eq (gcd a b) (gcd g_a1 b)
    let gcd_ga1_b = d.gcd(g_a1, b);
    let step2 = d.congr(b, g_b1, b_eq, &|d, x| d.gcd(g_a1, x)); // Eq (gcd g_a1 b) (gcd g_a1 g_b1)
    let gcd_ga1_gb1 = d.gcd(g_a1, g_b1);
    let (_, g_eq_scaled) = d.chain(g, &[(gcd_ga1_b, step1), (gcd_ga1_gb1, step2)]);
    // g_eq_scaled : Eq g (gcd g_a1 g_b1)  -- `g` here IS `gcd a b`.
    let scaled_eq_g = d.symm(g, gcd_ga1_gb1, g_eq_scaled);
    d.lemma(p.gcd_cofactors_coprime, &[g, a1, b1, g_pos, scaled_eq_g])
}

/// `Eq lcm_ab (mul g (mul a1 b1))`, given `a = g*a1`, `b = g*b1`, and
/// `1 ≤ g`. From `gcd_mul_lcm`, `g * lcm_ab = a * b = (g*a1)*(g*b1) =
/// g*(g*(a1*b1))`; cancelling one factor of `g` leaves `lcm_ab = g*(a1*b1)`.
#[allow(clippy::too_many_arguments)]
fn lcm_eq_scaled_cofactors(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    g: ExprId,
    lcm_ab: ExprId,
    a1: ExprId,
    b1: ExprId,
    a_eq: ExprId,
    b_eq: ExprId,
    g_pos: ExprId,
) -> ExprId {
    let p = *p;
    let g_a1 = d.mul(g, a1);
    let g_b1 = d.mul(g, b1);
    let a1_b1 = d.mul(a1, b1);
    let g_a1b1 = d.mul(g, a1_b1);

    let gml = d.lemma(p.gcd_mul_lcm, &[a, b]); // Eq (mul g lcm_ab) (mul a b)
    let g_lcm = d.mul(g, lcm_ab);
    let a_b = d.mul(a, b);

    let step_ab1 = d.congr(a, g_a1, a_eq, &|d, x| d.mul(x, b)); // Eq a_b (mul g_a1 b)
    let ga1_b = d.mul(g_a1, b);
    let step_ab2 = d.congr(b, g_b1, b_eq, &|d, x| d.mul(g_a1, x)); // Eq ga1_b (mul g_a1 g_b1)
    let ga1_gb1 = d.mul(g_a1, g_b1);

    let assoc1 = d.lemma(p.mul_assoc, &[g, a1, g_b1]); // Eq ga1_gb1 (mul g (mul a1 g_b1))
    let a1_gb1 = d.mul(a1, g_b1);
    let g_a1gb1 = d.mul(g, a1_gb1);

    let reassoc = reassociate_a_gc(d, &p, a1, g, b1); // Eq a1_gb1 g_a1b1
    let congr_reassoc = d.congr(a1_gb1, g_a1b1, reassoc, &|d, x| d.mul(g, x));
    // Eq g_a1gb1 (mul g g_a1b1)
    let g_g_a1b1 = d.mul(g, g_a1b1);

    let (_, glcm_eq_gg) = d.chain(
        g_lcm,
        &[
            (a_b, gml),
            (ga1_b, step_ab1),
            (ga1_gb1, step_ab2),
            (g_a1gb1, assoc1),
            (g_g_a1b1, congr_reassoc),
        ],
    );
    // glcm_eq_gg : Eq (mul g lcm_ab) (mul g g_a1b1)
    d.lemma(
        p.mul_left_cancel_of_pos,
        &[g, lcm_ab, g_a1b1, g_pos, glcm_eq_gg],
    )
    // : Eq lcm_ab g_a1b1
}

/// From `eq_q : Eq (mul (mul g b1) p) (mul (mul g a1) q)` (i.e. `(g*b1)*p =
/// (g*a1)*q`, produced by eliminating `(g*a1) ∣ (g*b1)*p`) and `coprime :
/// gcd a1 b1 = 1`, derive `dvd a1 p` by cancelling `g` (reassociating both
/// sides to expose it, then `mul_left_cancel_of_pos`) and applying
/// `gauss_lemma`.
#[allow(clippy::too_many_arguments)]
fn a1_dvd_p_of_scaled(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    a1: ExprId,
    b1: ExprId,
    p_: ExprId,
    q: ExprId,
    eq_q: ExprId,
    g_pos: ExprId,
    coprime: ExprId,
) -> ExprId {
    let p = *p;
    let g_b1 = d.mul(g, b1);
    let gb1_p = d.mul(g_b1, p_);
    let g_a1 = d.mul(g, a1);
    let ga1_q = d.mul(g_a1, q);

    let b1_p = d.mul(b1, p_);
    let g_b1p = d.mul(g, b1_p);
    let a1_q = d.mul(a1, q);
    let g_a1q = d.mul(g, a1_q);

    let lhs_assoc = d.lemma(p.mul_assoc, &[g, b1, p_]); // Eq gb1_p g_b1p
    let lhs_assoc_rev = d.symm(gb1_p, g_b1p, lhs_assoc); // Eq g_b1p gb1_p
    let rhs_assoc = d.lemma(p.mul_assoc, &[g, a1, q]); // Eq ga1_q g_a1q

    let (_, g_b1p_eq_g_a1q) = d.chain(
        g_b1p,
        &[(gb1_p, lhs_assoc_rev), (ga1_q, eq_q), (g_a1q, rhs_assoc)],
    );
    // g_b1p_eq_g_a1q : Eq (mul g b1_p) (mul g a1_q)

    let b1p_eq_a1q = d.lemma(
        p.mul_left_cancel_of_pos,
        &[g, b1_p, a1_q, g_pos, g_b1p_eq_g_a1q],
    );
    // b1p_eq_a1q : Eq b1_p a1_q
    let dvd_a1_b1p = dvd_intro(d, a1, b1_p, q, b1p_eq_a1q); // dvd a1 (mul b1 p_)
    d.lemma(p.gauss_lemma, &[a1, b1, p_, coprime, dvd_a1_b1p])
}

/// `Eq c (mul lcm_ab q2)`, given `c_eq2 : Eq c (mul (mul g b1) p)`,
/// `p_eq : Eq p (mul a1 q2)`, and `lcm_ab_eq : Eq lcm_ab (mul g (mul a1
/// b1))`. Substitutes `p`, then reassociates `(g*b1)*(a1*q2)` down to
/// `(g*(a1*b1))*q2 = lcm_ab*q2`.
#[allow(clippy::too_many_arguments)]
fn c_eq_lcm_mul(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    b1: ExprId,
    a1: ExprId,
    c: ExprId,
    p_: ExprId,
    q2: ExprId,
    lcm_ab: ExprId,
    c_eq2: ExprId,
    p_eq: ExprId,
    lcm_ab_eq: ExprId,
) -> ExprId {
    let p = *p;
    let g_b1 = d.mul(g, b1);
    let gb1_p = d.mul(g_b1, p_);
    let a1_q2 = d.mul(a1, q2);
    let gb1_a1q2 = d.mul(g_b1, a1_q2);

    let step_c1 = d.congr(p_, a1_q2, p_eq, &|d, x| d.mul(g_b1, x)); // Eq gb1_p gb1_a1q2

    let assoc_top = d.lemma(p.mul_assoc, &[g, b1, a1_q2]); // Eq gb1_a1q2 (mul g (mul b1 a1_q2))
    let b1_a1q2 = d.mul(b1, a1_q2);
    let g_b1a1q2 = d.mul(g, b1_a1q2);

    let assoc_inner = d.lemma(p.mul_assoc, &[b1, a1, q2]); // Eq (mul b1_a1 q2) b1_a1q2
    let b1_a1 = d.mul(b1, a1);
    let b1a1_q2 = d.mul(b1_a1, q2);
    let assoc_inner_rev = d.symm(b1a1_q2, b1_a1q2, assoc_inner); // Eq b1_a1q2 b1a1_q2

    let congr1 = d.congr(b1_a1q2, b1a1_q2, assoc_inner_rev, &|d, x| d.mul(g, x));
    // Eq g_b1a1q2 (mul g b1a1_q2)
    let g_b1a1_q2 = d.mul(g, b1a1_q2);

    let comm_b1a1 = d.lemma(p.mul_comm, &[b1, a1]); // Eq b1_a1 (mul a1 b1)
    let a1_b1 = d.mul(a1, b1);
    let congr2 = d.congr(b1_a1, a1_b1, comm_b1a1, &|d, x| d.mul(x, q2)); // Eq b1a1_q2 (mul a1_b1 q2)
    let a1b1_q2 = d.mul(a1_b1, q2);

    let congr3 = d.congr(b1a1_q2, a1b1_q2, congr2, &|d, x| d.mul(g, x));
    // Eq g_b1a1_q2 (mul g a1b1_q2)
    let g_a1b1_q2 = d.mul(g, a1b1_q2);

    let g_a1b1 = d.mul(g, a1_b1);
    let assoc_bottom = d.lemma(p.mul_assoc, &[g, a1_b1, q2]); // Eq (mul g_a1b1 q2) g_a1b1_q2
    let g_a1b1_q2_alt = d.mul(g_a1b1, q2);
    let assoc_bottom_rev = d.symm(g_a1b1_q2_alt, g_a1b1_q2, assoc_bottom); // Eq g_a1b1_q2 g_a1b1_q2_alt

    let congr4 = d.congr(lcm_ab, g_a1b1, lcm_ab_eq, &|d, x| d.mul(x, q2)); // Eq (mul lcm_ab q2) g_a1b1_q2_alt
    let lcm_q2 = d.mul(lcm_ab, q2);
    let congr4_rev = d.symm(lcm_q2, g_a1b1_q2_alt, congr4); // Eq g_a1b1_q2_alt lcm_q2

    let (_, chained) = d.chain(
        c,
        &[
            (gb1_p, c_eq2),
            (gb1_a1q2, step_c1),
            (g_b1a1q2, assoc_top),
            (g_b1a1_q2, congr1),
            (g_a1b1_q2, congr3),
            (g_a1b1_q2_alt, assoc_bottom_rev),
            (lcm_q2, congr4_rev),
        ],
    );
    chained
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

/// Given `hle : Le x y`, `hn : modEq n x y`, `hm : modEq m x y`, build a proof
/// of `modEq (lcm n m) x y`.
///
/// Closes ledger fact `F:ml430-nat-mod-lcm`: `modEq n a b ∧ modEq m a b →
/// modEq (lcm n m) a b`, **unconditionally** in `n`/`m` — unlike
/// `crt.rs`'s `crt_unique`, no `gcd n m = 1` hypothesis is needed, because
/// the divisibility combination step here is [`super::lcm::declare_lcm_dvd`]'s
/// `lcm_dvd : dvd n c → dvd m c → dvd (lcm n m) c`, which is already
/// unconditional (unlike `coprime_mul_dvd`, which needs coprimality to
/// rewrite `lcm n m` down to `n*m`). Route: extract `dvd n (sub y x)` and
/// `dvd m (sub y x)` from the two congruences via `crt.rs`'s `gap_dvd`,
/// combine with `lcm_dvd`, and repackage via `crt.rs`'s `modeq_of_dvd_gap`
/// — the same two helpers `crt_le` uses, reused here because the
/// gap-extraction/repackaging steps do not depend on how the two
/// divisibility facts were combined.
#[allow(clippy::too_many_arguments)]
fn mod_lcm_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    m: ExprId,
    x: ExprId,
    y: ExprId,
    hle: ExprId,
    hn: ExprId,
    hm: ExprId,
) -> ExprId {
    let p = *p;
    let dvd_n_gap = gap_dvd(d, &p, n, x, y, hle, hn);
    let dvd_m_gap = gap_dvd(d, &p, m, x, y, hle, hm);
    let gap = d.sub(y, x);
    let dvd_lcm_gap = d.lemma(p.lcm_dvd, &[n, m, gap, dvd_n_gap, dvd_m_gap]); // dvd (lcm n m) gap
    let lcm_nm = d.const_app(p.lcm, &[n, m]);
    modeq_of_dvd_gap(d, &p, lcm_nm, x, y, hle, dvd_lcm_gap)
}

/// `Nat.mod_lcm : ∀ n m x y, modEq n x y → modEq m x y → modEq (lcm n m) x y`
/// — combining two congruences into their lcm's, unconditionally. `le_total x
/// y` splits into the two orders, mirroring `crt_unique`'s own case split
/// exactly; the `y ≤ x` branch flips both hypotheses and the conclusion
/// through `mod_eq_symm`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_mod_lcm(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let anon = d.anon_name();
    d.theorem(p.mod_lcm, 4, &|d, values| {
        let (n, m, x, y) = (values[0], values[1], values[2], values[3]);

        let hn_ty = d.mod_eq(n, x, y);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);

        let hm_ty = d.mod_eq(m, x, y);
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);

        let lcm_nm = d.const_app(p.lcm, &[n, m]);
        let target = d.mod_eq(lcm_nm, x, y);

        let le_xy = d.le(x, y);
        let le_yx = d.le(y, x);
        let total = d.lemma(p.le_total, &[x, y]); // Or (Le x y) (Le y x)
        let total_ty = d.const_app(p.logic.or, &[le_xy, le_yx]);
        let motive = d.kernel().lam(anon, total_ty, target, BinderInfo::Default);

        let left_minor = {
            let hle_fv = d.fresh_fvar();
            let hle = d.kernel().fvar(hle_fv);
            let body = mod_lcm_le(d, &p, n, m, x, y, hle, hn, hm);
            d.lam_fv(hle_fv, le_xy, body)
        };
        let right_minor = {
            let hle_fv = d.fresh_fvar();
            let hle = d.kernel().fvar(hle_fv); // Le y x
            let hn_yx = d.lemma(p.mod_eq_symm, &[n, x, y, hn]); // modEq n y x
            let hm_yx = d.lemma(p.mod_eq_symm, &[m, x, y, hm]); // modEq m y x
            let proof_yx = mod_lcm_le(d, &p, n, m, y, x, hle, hn_yx, hm_yx); // modEq lcm_nm y x
            let body = d.lemma(p.mod_eq_symm, &[lcm_nm, y, x, proof_yx]); // modEq lcm_nm x y
            d.lam_fv(hle_fv, le_yx, body)
        };

        let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
        let case_proof = d.apply(
            or_rec,
            &[le_xy, le_yx, motive, left_minor, right_minor, total],
        );

        let with_hm = d.lam_fv(hm_fv, hm_ty, case_proof);
        let proof = d.lam_fv(hn_fv, hn_ty, with_hm);

        let hm_to_target = d.arrow(hm_ty, target);
        let stmt = d.arrow(hn_ty, hm_to_target);
        (stmt, proof)
    })?;
    Ok(())
}
