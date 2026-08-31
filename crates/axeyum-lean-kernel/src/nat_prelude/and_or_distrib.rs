//! `Nat.and_or_distrib_left`/`Nat.and_or_distrib_right` — bitwise AND
//! distributes over bitwise OR, both handed sides. Draw 11
//! (`F:ml430-nat-and-or-distrib-left-fe131f64`,
//! `F:ml430-nat-and-or-distrib-right-0daaa284`).
//!
//! # The route: extensionality + a per-bit `{0,1}` case split
//!
//! Exactly `xor_algebra.rs`'s `Nat.xor_assoc` recipe: reduce a value-level
//! equation about `land`/`lor` to a per-bit equation via
//! `Nat.testBit_land`/`Nat.testBit_lor` (`testbit_bitwise.rs`), then close
//! the bit-level identity and turn it back into a value-level one with
//! `Nat.eq_of_testBit_eq` (`xor_algebra.rs`).
//!
//! The bit-level combine is `mul` for AND (`Nat.testBit_land`) and
//! `lor_bit(x, y) := bool_select_nat (ble x y) y x` (`max`, via
//! `testbit_bitwise::lor_bit`) for OR. `mul a (max b c) = max (mul a b) (mul
//! a c)` is true for ALL `Nat` (multiplication by a nonnegative scalar
//! distributes over `max` unconditionally), but at a SYMBOLIC bit position
//! `a`, `b`, `c` are opaque `testBit` applications, not literal numerals, so
//! the general order-theoretic proof (`Nat.le_total` + `mul_le_mul_left`)
//! would need to handle the `x = y` boundary of `max`'s two branches
//! separately in each direction. Restricting to `{0, 1}` via
//! `Nat.testBit_le_one` sidesteps all of that: `bit_and_or_distrib`/
//! `bit_and_or_distrib_right` case-split each of the three bit values into
//! `0`/`1` (`cases_le_one`, `Nat.le_succ_succ` + `Nat.lt_two_cases` lifted
//! through `ops::cases_lt_bound` at `bound = 2` — the value-bounded twin of
//! `ops::cases_mod_two`, which splits `mod x 2` rather than an already-known
//! `<= 1` value), landing on 8 concrete leaves each closed by `refl` —
//! exactly `rec_agreement.rs`'s `lor_bit_assoc`/`lor_bit_comm` technique,
//! confirmed by a truth-table check before writing any of this: AND
//! distributes over OR at all 8 `{0,1}` triples on both sides.

use super::NatPrelude;
use super::ops::{NatDev, NatOps, cases_lt_bound};
use super::testbit_bitwise::lor_bit;
use crate::KernelError;
use crate::expr::ExprId;

/// Split `v` into `0`/`1` given a proof `v <= 1` — the value-bounded twin of
/// [`super::ops::cases_mod_two`] (which instead splits `mod x 2` for an
/// arbitrary `x`). `v` here is already known bounded (a `testBit` result,
/// via `Nat.testBit_le_one`), so no `mod` re-derivation is needed: `Nat.
/// le_succ_succ` lifts `Le v 1` to `Le (succ v) (succ 1)`, which IS (by
/// `refl`, both numerals built the same way) `Lt v 2`, and
/// [`cases_lt_bound`] at `bound = 2` does the rest.
fn cases_le_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    v: ExprId,
    h_le_one: ExprId,
    motive: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    at_zero: ExprId,
    at_one: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let lt_v_2 = d.lemma(p.le_succ_succ, &[v, one, h_le_one]); // Le (succ v) (succ one) ~ Lt v 2
    cases_lt_bound(d, &p, v, 2, lt_v_2, motive, &[at_zero, at_one])
}

/// `Eq (mul a (lor_bit b c)) (lor_bit (mul a b) (mul a c))`, given `a`, `b`,
/// `c` each bounded by `1` (e.g. `testBit` values). Nested [`cases_le_one`]
/// on `a`, then `b`, then `c`; 8 leaves, each a `refl` at a concrete `{0,1}`
/// triple (AND-distributes-over-OR truth table, checked in Python before
/// writing this).
#[allow(clippy::too_many_arguments)]
fn bit_and_or_distrib(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h_a: ExprId,
    h_b: ExprId,
    h_c: ExprId,
) -> ExprId {
    let p = *p;

    let combine_or = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let le = d.ble(x, y);
        d.bool_select_nat(le, y, x)
    };
    let claim = |d: &mut NatDev<'_>, x: ExprId, y: ExprId, z: ExprId| {
        let or_yz = combine_or(d, y, z);
        let lhs = d.mul(x, or_yz);
        let xy = d.mul(x, y);
        let xz = d.mul(x, z);
        let rhs = combine_or(d, xy, xz);
        d.eq(lhs, rhs)
    };
    // At concrete `{0,1}` operands both sides compute to the same literal.
    let leaf = |d: &mut NatDev<'_>, x: ExprId, y: ExprId, z: ExprId| {
        let or_yz = combine_or(d, y, z);
        let lhs = d.mul(x, or_yz);
        d.refl(lhs)
    };

    let zero = d.zero();
    let one = d.num(1);

    let inner_at = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let at_zero = leaf(d, x, y, zero);
        let at_one = leaf(d, x, y, one);
        cases_le_one(d, &p, c, h_c, &|d, z| claim(d, x, y, z), at_zero, at_one)
    };

    let middle_at = |d: &mut NatDev<'_>, x: ExprId| {
        let at_zero = inner_at(d, x, zero);
        let at_one = inner_at(d, x, one);
        cases_le_one(d, &p, b, h_b, &|d, y| claim(d, x, y, c), at_zero, at_one)
    };

    let outer_zero = middle_at(d, zero);
    let outer_one = middle_at(d, one);
    cases_le_one(
        d,
        &p,
        a,
        h_a,
        &|d, x| claim(d, x, b, c),
        outer_zero,
        outer_one,
    )
}

/// `Eq (mul (lor_bit a b) c) (lor_bit (mul a c) (mul b c))` — the
/// right-handed twin of [`bit_and_or_distrib`], same technique, `mul`
/// scaling each operand on the right of the `max` instead of the left.
#[allow(clippy::too_many_arguments)]
fn bit_and_or_distrib_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h_a: ExprId,
    h_b: ExprId,
    h_c: ExprId,
) -> ExprId {
    let p = *p;

    let combine_or = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let le = d.ble(x, y);
        d.bool_select_nat(le, y, x)
    };
    let claim = |d: &mut NatDev<'_>, x: ExprId, y: ExprId, z: ExprId| {
        let or_xy = combine_or(d, x, y);
        let lhs = d.mul(or_xy, z);
        let xz = d.mul(x, z);
        let yz = d.mul(y, z);
        let rhs = combine_or(d, xz, yz);
        d.eq(lhs, rhs)
    };
    let leaf = |d: &mut NatDev<'_>, x: ExprId, y: ExprId, z: ExprId| {
        let or_xy = combine_or(d, x, y);
        let lhs = d.mul(or_xy, z);
        d.refl(lhs)
    };

    let zero = d.zero();
    let one = d.num(1);

    let inner_at = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let at_zero = leaf(d, x, y, zero);
        let at_one = leaf(d, x, y, one);
        cases_le_one(d, &p, c, h_c, &|d, z| claim(d, x, y, z), at_zero, at_one)
    };

    let middle_at = |d: &mut NatDev<'_>, x: ExprId| {
        let at_zero = inner_at(d, x, zero);
        let at_one = inner_at(d, x, one);
        cases_le_one(d, &p, b, h_b, &|d, y| claim(d, x, y, c), at_zero, at_one)
    };

    let outer_zero = middle_at(d, zero);
    let outer_one = middle_at(d, one);
    cases_le_one(
        d,
        &p,
        a,
        h_a,
        &|d, x| claim(d, x, b, c),
        outer_zero,
        outer_one,
    )
}

/// `Nat.and_or_distrib_left : ∀ x y z, Eq (land x (lor y z)) (lor (land x y)
/// (land x z))`. `F:ml430-nat-and-or-distrib-left-fe131f64`.
fn declare_and_or_distrib_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.and_or_distrib_left, 3, &|d, values| {
        let (x, y, z) = (values[0], values[1], values[2]);
        let yz = d.const_app(p.lor, &[y, z]);
        let lhs = d.const_app(p.land, &[x, yz]);
        let xy = d.const_app(p.land, &[x, y]);
        let xz = d.const_app(p.land, &[x, z]);
        let rhs = d.const_app(p.lor, &[xy, xz]);
        let stmt = d.eq(lhs, rhs);

        let bits_hyp = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);

            let tb_x = d.const_app(p.test_bit, &[x, i]);
            let tb_y = d.const_app(p.test_bit, &[y, i]);
            let tb_z = d.const_app(p.test_bit, &[z, i]);

            // testBit lhs i = mul tb_x (testBit yz i) = mul tb_x (lor_bit tb_y tb_z)
            let tb_lhs_outer = d.lemma(p.test_bit_land, &[x, yz, i]);
            let tb_yz = d.const_app(p.test_bit, &[yz, i]);
            let tb_lhs_inner = d.lemma(p.test_bit_lor, &[y, z, i]);
            let lor_bit_yz = lor_bit(d, tb_y, tb_z);
            let mul_tbx_tbyz = d.mul(tb_x, tb_yz);
            let mul_tbx_lor = d.mul(tb_x, lor_bit_yz);
            let congr_lhs_inner = d.congr(tb_yz, lor_bit_yz, tb_lhs_inner, &|d, w| d.mul(tb_x, w));
            let tb_lhs = d.const_app(p.test_bit, &[lhs, i]);
            let (_, lhs_eq) = d.chain(
                tb_lhs,
                &[(mul_tbx_tbyz, tb_lhs_outer), (mul_tbx_lor, congr_lhs_inner)],
            );

            // testBit rhs i = lor_bit (testBit xy i) (testBit xz i)
            //               = lor_bit (mul tb_x tb_y) (mul tb_x tb_z)
            let tb_rhs_outer = d.lemma(p.test_bit_lor, &[xy, xz, i]);
            let tb_xy = d.const_app(p.test_bit, &[xy, i]);
            let tb_xz = d.const_app(p.test_bit, &[xz, i]);
            let tb_rhs_inner_l = d.lemma(p.test_bit_land, &[x, y, i]);
            let tb_rhs_inner_r = d.lemma(p.test_bit_land, &[x, z, i]);
            let mul_x_y = d.mul(tb_x, tb_y);
            let mul_x_z = d.mul(tb_x, tb_z);
            let lor_bit_txy_txz = lor_bit(d, tb_xy, tb_xz);
            let lor_bit_mid = lor_bit(d, mul_x_y, tb_xz);
            let lor_bit_final = lor_bit(d, mul_x_y, mul_x_z);
            let congr_rhs_l = d.congr(tb_xy, mul_x_y, tb_rhs_inner_l, &|d, w| {
                let tb_xz2 = tb_xz;
                lor_bit(d, w, tb_xz2)
            });
            let congr_rhs_r = d.congr(tb_xz, mul_x_z, tb_rhs_inner_r, &|d, w| {
                let mul_x_y2 = mul_x_y;
                lor_bit(d, mul_x_y2, w)
            });
            let tb_rhs = d.const_app(p.test_bit, &[rhs, i]);
            let (_, rhs_eq) = d.chain(
                tb_rhs,
                &[
                    (lor_bit_txy_txz, tb_rhs_outer),
                    (lor_bit_mid, congr_rhs_l),
                    (lor_bit_final, congr_rhs_r),
                ],
            );

            let h_tb_x = d.lemma(p.test_bit_le_one, &[x, i]);
            let h_tb_y = d.lemma(p.test_bit_le_one, &[y, i]);
            let h_tb_z = d.lemma(p.test_bit_le_one, &[z, i]);
            let bit_dist = bit_and_or_distrib(d, &p, tb_x, tb_y, tb_z, h_tb_x, h_tb_y, h_tb_z);

            let (_, bit_eq) = d.chain(tb_lhs, &[(mul_tbx_lor, lhs_eq), (lor_bit_final, bit_dist)]);
            let rhs_eq_symm = d.symm(tb_rhs, lor_bit_final, rhs_eq);
            let final_bit_eq = d.trans(tb_lhs, lor_bit_final, tb_rhs, bit_eq, rhs_eq_symm);
            d.lam_fv(i_fv, nat, final_bit_eq)
        };

        let proof = d.lemma(p.eq_of_test_bit_eq, &[lhs, rhs, bits_hyp]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.and_or_distrib_right : ∀ x y z, Eq (land (lor x y) z) (lor (land x
/// z) (land y z))`. `F:ml430-nat-and-or-distrib-right-0daaa284`.
fn declare_and_or_distrib_right(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.and_or_distrib_right, 3, &|d, values| {
        let (x, y, z) = (values[0], values[1], values[2]);
        let xy = d.const_app(p.lor, &[x, y]);
        let lhs = d.const_app(p.land, &[xy, z]);
        let xz = d.const_app(p.land, &[x, z]);
        let yz = d.const_app(p.land, &[y, z]);
        let rhs = d.const_app(p.lor, &[xz, yz]);
        let stmt = d.eq(lhs, rhs);

        let bits_hyp = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);

            let tb_x = d.const_app(p.test_bit, &[x, i]);
            let tb_y = d.const_app(p.test_bit, &[y, i]);
            let tb_z = d.const_app(p.test_bit, &[z, i]);

            // testBit lhs i = mul (testBit xy i) tb_z = mul (lor_bit tb_x tb_y) tb_z
            let tb_lhs_outer = d.lemma(p.test_bit_land, &[xy, z, i]);
            let tb_xy = d.const_app(p.test_bit, &[xy, i]);
            let tb_lhs_inner = d.lemma(p.test_bit_lor, &[x, y, i]);
            let lor_bit_xy = lor_bit(d, tb_x, tb_y);
            let mul_tbxy_tbz = d.mul(tb_xy, tb_z);
            let mul_lor_tbz = d.mul(lor_bit_xy, tb_z);
            let congr_lhs_inner = d.congr(tb_xy, lor_bit_xy, tb_lhs_inner, &|d, w| d.mul(w, tb_z));
            let tb_lhs = d.const_app(p.test_bit, &[lhs, i]);
            let (_, lhs_eq) = d.chain(
                tb_lhs,
                &[(mul_tbxy_tbz, tb_lhs_outer), (mul_lor_tbz, congr_lhs_inner)],
            );

            // testBit rhs i = lor_bit (testBit xz i) (testBit yz i)
            //               = lor_bit (mul tb_x tb_z) (mul tb_y tb_z)
            let tb_rhs_outer = d.lemma(p.test_bit_lor, &[xz, yz, i]);
            let tb_xz = d.const_app(p.test_bit, &[xz, i]);
            let tb_yz = d.const_app(p.test_bit, &[yz, i]);
            let tb_rhs_inner_l = d.lemma(p.test_bit_land, &[x, z, i]);
            let tb_rhs_inner_r = d.lemma(p.test_bit_land, &[y, z, i]);
            let mul_x_z = d.mul(tb_x, tb_z);
            let mul_y_z = d.mul(tb_y, tb_z);
            let lor_bit_txz_tyz = lor_bit(d, tb_xz, tb_yz);
            let lor_bit_mid = lor_bit(d, mul_x_z, tb_yz);
            let lor_bit_final = lor_bit(d, mul_x_z, mul_y_z);
            let congr_rhs_l = d.congr(tb_xz, mul_x_z, tb_rhs_inner_l, &|d, w| {
                let tb_yz2 = tb_yz;
                lor_bit(d, w, tb_yz2)
            });
            let congr_rhs_r = d.congr(tb_yz, mul_y_z, tb_rhs_inner_r, &|d, w| {
                let mul_x_z2 = mul_x_z;
                lor_bit(d, mul_x_z2, w)
            });
            let tb_rhs = d.const_app(p.test_bit, &[rhs, i]);
            let (_, rhs_eq) = d.chain(
                tb_rhs,
                &[
                    (lor_bit_txz_tyz, tb_rhs_outer),
                    (lor_bit_mid, congr_rhs_l),
                    (lor_bit_final, congr_rhs_r),
                ],
            );

            let h_tb_x = d.lemma(p.test_bit_le_one, &[x, i]);
            let h_tb_y = d.lemma(p.test_bit_le_one, &[y, i]);
            let h_tb_z = d.lemma(p.test_bit_le_one, &[z, i]);
            let bit_dist =
                bit_and_or_distrib_right(d, &p, tb_x, tb_y, tb_z, h_tb_x, h_tb_y, h_tb_z);

            let (_, bit_eq) = d.chain(tb_lhs, &[(mul_lor_tbz, lhs_eq), (lor_bit_final, bit_dist)]);
            let rhs_eq_symm = d.symm(tb_rhs, lor_bit_final, rhs_eq);
            let final_bit_eq = d.trans(tb_lhs, lor_bit_final, tb_rhs, bit_eq, rhs_eq_symm);
            d.lam_fv(i_fv, nat, final_bit_eq)
        };

        let proof = d.lemma(p.eq_of_test_bit_eq, &[lhs, rhs, bits_hyp]);
        (stmt, proof)
    })?;
    Ok(())
}

/// Everything this module declares.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_and_or_distrib_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_and_or_distrib_left(d, p)?;
    declare_and_or_distrib_right(d, p)?;
    Ok(())
}
