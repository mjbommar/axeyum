//! Low-bit facts about `Nat.land`: `Nat.land_one_is_mod`
//! (`F:ml430-nat-and-one-is-mod-d861e96b`), `Nat.land_mod_two_eq_mul` (an
//! internal arithmetic bridge), and `Nat.land_mod_two_eq_one`
//! (`F:ml430-nat-and-mod-two-eq-one-3e873792`, Mathlib's `&&&` is our
//! `Nat.land`).
//!
//! # `land_one_is_mod`
//!
//! `land x 1 = mod x 2` looks like it needs induction over `x`, but fixing
//! the SECOND operand at the concrete literal `1` — via `land_comm`, so the
//! fuel-supplying slot becomes `1` rather than `x` — collapses the whole
//! thing to ONE unfold: `land 1 x := landAux 1 1 x`, fuel `1 = succ 0` is
//! already a literal, and the succ-row's own recursive call lands at fuel
//! `0` (a LITERAL, not `x`'s predecessor), which is the base case for ANY
//! remaining arguments. So the recursive term is `0` by `refl`, with no
//! induction hypothesis anywhere.
//!
//! # `land_mod_two_eq_mul`
//!
//! `mod (land a b) 2 = mod a 2 * mod b 2` is `even_xor`'s technique
//! (`xor_parity.rs`) transplanted to `land`: the goal only mentions the LOW
//! BIT of `land a b`, so ONE unfold of `landAux`'s succ-row plus
//! `mod_two_mul_add_of_lt` (`parity.rs`) erases the higher recursive term
//! without any induction on it. Boundary cases (`a = 0`/`b = 0`) go through
//! `land_zero_left`/`land_zero_right` directly.
//!
//! # `land_mod_two_eq_one`
//!
//! `land_mod_two_eq_mul` reduces the goal to `Eq (mul p q) 1 <-> (Eq p 1
//! /\ Eq q 1)` for `p := mod a 2`, `q := mod b 2` — purely numeric, closed
//! by `cases_mod_two` on `a` then `b` (four leaves).

use super::NatPrelude;
use super::ops::{NatDev, NatOps, cases_mod_two, cases_zero_succ};
use super::parity::mod_two_mul_add_of_lt;
use super::xor_parity::{iff_of_false_false, iff_of_true_true, iff_trans};
use crate::KernelError;
use crate::expr::ExprId;

/// `Not (Eq zero one)`, via `succ_ne_zero` (`Not (Eq one zero)`, since
/// `one = succ zero`) and `symm`.
fn not_eq_zero_one(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let not_one_zero = d.lemma(p.succ_ne_zero, &[zero]); // Not (Eq one zero)
    let eq_ty = d.eq(zero, one);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let h_rev = d.symm(zero, one, h); // Eq one zero
    let false_proof = d.apply(not_one_zero, &[h_rev]);
    d.lam_fv(h_fv, eq_ty, false_proof)
}

/// `And left right` from proofs of each side.
fn and_intro(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left: ExprId,
    right: ExprId,
    l: ExprId,
    r: ExprId,
) -> ExprId {
    let p = *p;
    d.const_app(p.logic.and_intro, &[left, right, l, r])
}

/// `Not (And left right)` from `Not left` — project the left component and
/// apply the refutation.
fn not_and_of_left_false(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left: ExprId,
    right: ExprId,
    not_left: ExprId,
) -> ExprId {
    let p = *p;
    let and_ty = d.const_app(p.logic.and, &[left, right]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let l = super::helpers::and_left(d, left, right, h);
    let false_proof = d.apply(not_left, &[l]);
    d.lam_fv(h_fv, and_ty, false_proof)
}

/// `Not (And left right)` from `Not right` — the right-projecting twin.
fn not_and_of_right_false(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left: ExprId,
    right: ExprId,
    not_right: ExprId,
) -> ExprId {
    let p = *p;
    let and_ty = d.const_app(p.logic.and, &[left, right]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let r = super::helpers::and_right(d, left, right, h);
    let false_proof = d.apply(not_right, &[r]);
    d.lam_fv(h_fv, and_ty, false_proof)
}

/// `Nat.land_one_is_mod : ∀ x, Eq (land x 1) (mod x 2)`.
fn declare_land_one_is_mod(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.land_one_is_mod, 1, &|d, values| {
        let x = values[0];
        let one = d.num(1);
        let two = d.num(2);
        let stmt_at = |d: &mut NatDev<'_>, xx: ExprId| -> ExprId {
            let lhs = d.const_app(p.land, &[xx, one]);
            let rhs = d.modulo(xx, two);
            d.eq(lhs, rhs)
        };
        let proof = cases_zero_succ(
            d,
            x,
            &stmt_at,
            &|d| {
                // x = 0: `land 0 1 = 0` (`land_zero_left`), `mod 0 2 = 0` (`zero_mod`).
                let zero = d.zero();
                let land01 = d.const_app(p.land, &[zero, one]);
                let mod02 = d.modulo(zero, two);
                let land01_eq_zero = d.lemma(p.land_zero_left, &[one]);
                let mod02_eq_zero = d.lemma(p.zero_mod, &[two]);
                let mod02_eq_zero_rev = d.symm(mod02, zero, mod02_eq_zero);
                d.trans(land01, zero, mod02, land01_eq_zero, mod02_eq_zero_rev)
            },
            &|d, xp| {
                let sx = d.succ(xp);
                // `land sx 1 = land 1 sx` (commute so the fuel slot is the
                // LITERAL `1`, not the symbolic `sx`).
                let comm = d.lemma(p.land_comm, &[sx, one]);
                let land_1_sx = d.const_app(p.land, &[one, sx]);

                let zero = d.zero();
                let half_m = d.div(one, two);
                let half_n = d.div(sx, two);
                let bit_m = d.modulo(one, two);
                let bit_n = d.modulo(sx, two);
                let rec = d.const_app(p.land_aux, &[zero, half_m, half_n]);
                let bit_and = d.mul(bit_m, bit_n);

                let start = super::rec_agreement::guarded(d, one, sx, zero, zero, rec, bit_and);
                let mid1 = super::rec_agreement::guarded(d, one, sx, zero, zero, zero, bit_and);
                let rec_is_zero = d.refl(rec); // Eq rec zero, bridged by defeq (fuel literal 0)
                let step1 = d.congr(rec, zero, rec_is_zero, &|d, hole| {
                    super::rec_agreement::guarded(d, one, sx, zero, zero, hole, bit_and)
                });

                // `bit_m = mod 1 2 = 1` via `mod_eq_self_of_lt` (`Lt one two`
                // is `Le two two` up to defeq, `le_refl`).
                let lt_1_2 = d.lemma(p.le_refl, &[two]);
                let bit_m_eq_one = d.lemma(p.mod_eq_self_of_lt, &[one, two, lt_1_2]);
                let one_bit_n = d.mul(one, bit_n);
                let mid2 = super::rec_agreement::guarded(d, one, sx, zero, zero, zero, one_bit_n);
                let step2 = d.congr(bit_m, one, bit_m_eq_one, &|d, hole| {
                    let hole_bit_n = d.mul(hole, bit_n);
                    super::rec_agreement::guarded(d, one, sx, zero, zero, zero, hole_bit_n)
                });

                // `mid2` is still wrapped in `guarded`'s `bool_select_nat`
                // scaffolding; bridge it (via `refl`, both guards literal
                // `false`) to the raw `add (mul two zero) one_bit_n`, then
                // simplify algebraically: `mul two zero = zero` (refl),
                // `add zero one_bit_n = one_bit_n` (`zero_add`), `mul one
                // bit_n = bit_n` (`one_mul`).
                let mul_two_zero = d.mul(two, zero);
                let add_form1 = d.add(mul_two_zero, one_bit_n);
                let bridge_mid2 = d.refl(mid2); // Eq mid2 add_form1, bridged by defeq

                let mul_two_zero_is_zero = d.refl(mul_two_zero); // Eq mul_two_zero zero
                let add_form2 = d.add(zero, one_bit_n);
                let cong_a = d.congr(mul_two_zero, zero, mul_two_zero_is_zero, &|d, h| {
                    d.add(h, one_bit_n)
                }); // Eq add_form1 add_form2

                let zero_add_eq = d.lemma(p.zero_add, &[one_bit_n]); // Eq add_form2 one_bit_n
                let one_mul_eq = d.lemma(p.one_mul, &[bit_n]); // Eq one_bit_n bit_n

                let (_, land_1_sx_eq_bitn) = d.chain(
                    start,
                    &[
                        (mid1, step1),
                        (mid2, step2),
                        (add_form1, bridge_mid2),
                        (add_form2, cong_a),
                        (one_bit_n, zero_add_eq),
                        (bit_n, one_mul_eq),
                    ],
                );
                // `start` is defeq `land 1 sx` -- bridge, then chain with `comm`.
                let land_1_sx_is_start = d.refl(land_1_sx); // Eq land_1_sx start
                let land_1_sx_eq_bitn2 = d.trans(
                    land_1_sx,
                    start,
                    bit_n,
                    land_1_sx_is_start,
                    land_1_sx_eq_bitn,
                );
                let land_sx_1 = d.const_app(p.land, &[sx, one]);
                d.trans(land_sx_1, land_1_sx, bit_n, comm, land_1_sx_eq_bitn2)
            },
        );
        (stmt_at(d, x), proof)
    })?;
    Ok(())
}

/// `Nat.land_mod_two_eq_mul : ∀ a b, Eq (mod (land a b) 2) (mul (mod a 2)
/// (mod b 2))`.
fn declare_land_mod_two_eq_mul(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.land_mod_two_eq_mul, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let two = d.num(2);
        let goal_at = |d: &mut NatDev<'_>, aa: ExprId, bb: ExprId| -> ExprId {
            let land_ab = d.const_app(p.land, &[aa, bb]);
            let lhs = d.modulo(land_ab, two);
            let mod_aa = d.modulo(aa, two);
            let mod_bb = d.modulo(bb, two);
            let rhs = d.mul(mod_aa, mod_bb);
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
                let mod_land0b = d.modulo(land0b, two);
                let land0b_eq_zero = d.lemma(p.land_zero_left, &[b]);
                let step_a = d.congr(land0b, zero, land0b_eq_zero, &|d, h| d.modulo(h, two));
                let mod0_2 = d.modulo(zero, two);
                let mod0_2_eq_zero = d.lemma(p.zero_mod, &[two]);
                let lhs_chain = d.trans(mod_land0b, mod0_2, zero, step_a, mod0_2_eq_zero);

                let mod_b_2 = d.modulo(b, two);
                let rhs = d.mul(mod0_2, mod_b_2);
                let step_r = d.congr(mod0_2, zero, mod0_2_eq_zero, &|d, h| d.mul(h, mod_b_2));
                let zero_mod_b = d.mul(zero, mod_b_2);
                let zero_mul_eq = d.lemma(p.zero_mul, &[mod_b_2]);
                let rhs_chain = d.trans(rhs, zero_mod_b, zero, step_r, zero_mul_eq);
                let rhs_chain_rev = d.symm(rhs, zero, rhs_chain);
                d.trans(mod_land0b, zero, rhs, lhs_chain, rhs_chain_rev)
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
                        let land_a0 = d.const_app(p.land, &[sa, zero]);
                        let mod_landa0 = d.modulo(land_a0, two);
                        let land_a0_eq_zero = d.lemma(p.land_zero_right, &[sa]);
                        let step_a =
                            d.congr(land_a0, zero, land_a0_eq_zero, &|d, h| d.modulo(h, two));
                        let mod0_2 = d.modulo(zero, two);
                        let mod0_2_eq_zero = d.lemma(p.zero_mod, &[two]);
                        let lhs_chain = d.trans(mod_landa0, mod0_2, zero, step_a, mod0_2_eq_zero);

                        let mod_a_2 = d.modulo(sa, two);
                        let rhs = d.mul(mod_a_2, mod0_2);
                        let step_r =
                            d.congr(mod0_2, zero, mod0_2_eq_zero, &|d, h| d.mul(mod_a_2, h));
                        let a_mod_zero = d.mul(mod_a_2, zero);
                        let mul_zero_eq = d.lemma(p.mul_zero, &[mod_a_2]);
                        let rhs_chain = d.trans(rhs, a_mod_zero, zero, step_r, mul_zero_eq);
                        let rhs_chain_rev = d.symm(rhs, zero, rhs_chain);
                        d.trans(mod_landa0, zero, rhs, lhs_chain, rhs_chain_rev)
                    },
                    &|d, pb| {
                        // The genuinely bitwise case: one unfold, no induction.
                        let sb = d.succ(pb);
                        let bit_a = d.modulo(sa, two);
                        let bit_b = d.modulo(sb, two);
                        let bit_and = d.mul(bit_a, bit_b);
                        let half_a = d.div(sa, two);
                        let half_b = d.div(sb, two);
                        let rec = d.const_app(p.land_aux, &[pa, half_a, half_b]);

                        // `Lt bit_and two`: case on `bit_a` via `cases_mod_two` on `sa`.
                        let one = d.num(1);
                        let pos = d.zero_lt_succ(one);
                        let bit_and_lt_two = {
                            let motive2 = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                                let m = d.mul(x, bit_b);
                                d.lt(m, two)
                            };
                            let at_zero = {
                                let zero = d.zero();
                                let m0 = d.mul(zero, bit_b);
                                let zero_mul_eq = d.lemma(p.zero_mul, &[bit_b]); // Eq m0 zero
                                let lt_zero_two = d.zero_lt_succ(one);
                                let eq_rev = d.symm(m0, zero, zero_mul_eq); // Eq zero m0
                                let motive3 = d.eq_motive(zero, &|d, x| d.lt(x, two));
                                d.transport(zero, motive3, lt_zero_two, m0, eq_rev)
                            };
                            let at_one = {
                                let one2 = d.num(1);
                                let m1 = d.mul(one2, bit_b);
                                let one_mul_eq = d.lemma(p.one_mul, &[bit_b]); // Eq m1 bit_b
                                let lt_bitb_two = d.lemma(p.mod_lt, &[sb, two, pos]);
                                let eq_rev = d.symm(m1, bit_b, one_mul_eq); // Eq bit_b m1
                                let motive3 = d.eq_motive(bit_b, &|d, x| d.lt(x, two));
                                d.transport(bit_b, motive3, lt_bitb_two, m1, eq_rev)
                            };
                            cases_mod_two(d, &p, sa, &motive2, at_zero, at_one)
                        };

                        mod_two_mul_add_of_lt(d, &p, rec, bit_and, bit_and_lt_two)
                    },
                )
            },
        );
        (goal_at(d, a, b), proof)
    })?;
    Ok(())
}

/// `Iff (Eq (mul p q) 1) (And (Eq p 1) (Eq q 1))`, generalized over `p`, `q`
/// each already known to be `0` or `1` — the leaf `cases_mod_two` supplies.
fn land_bit_leaf(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    y: ExprId,
    x_is_one: bool,
    y_is_one: bool,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let mxy = d.mul(x, y);
    let mxy_eq_one_ty = d.eq(mxy, one);
    let x_eq_one_ty = d.eq(x, one);
    let y_eq_one_ty = d.eq(y, one);
    let and_ty = d.const_app(p.logic.and, &[x_eq_one_ty, y_eq_one_ty]);

    if x_is_one && y_is_one {
        // x = y = 1: mul 1 1 = 1 (refl), both conjuncts refl.
        let mxy_eq_one = d.refl(mxy); // bridged by defeq (mul one one = one)
        let x_eq_one = d.refl(one);
        let y_eq_one = d.refl(one);
        let and_proof = and_intro(d, &p, x_eq_one_ty, y_eq_one_ty, x_eq_one, y_eq_one);
        iff_of_true_true(d, &p, mxy_eq_one_ty, and_ty, mxy_eq_one, and_proof)
    } else {
        // At least one of x, y is 0: mul x y = 0, refuted against 1; the
        // `And` is refuted by projecting the zero side.
        let zero = d.zero();
        let not_mxy = {
            // `mxy` reduces to `0` on whichever side is zero: `mul` recurses
            // on the RIGHT argument, so `x = 0` needs `zero_mul` (the LEFT
            // absorbing case is a lemma, not `refl`) and `y = 0` needs
            // `mul_zero` (the right case, refl-adjacent but stated as a
            // lemma here for uniformity).
            let mxy_eq_zero = if x_is_one {
                d.lemma(p.mul_zero, &[x])
            } else {
                d.lemma(p.zero_mul, &[y])
            };
            let not_eq_zero_one_ty = not_eq_zero_one(d, &p);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            // h : Eq mxy one; combine with mxy_eq_zero (Eq mxy zero) via
            // symm/trans to get Eq zero one, then apply not_eq_zero_one.
            let mxy_eq_zero_rev = d.symm(mxy, zero, mxy_eq_zero); // Eq zero mxy
            let zero_eq_one = d.trans(zero, mxy, one, mxy_eq_zero_rev, h);
            let false_proof = d.apply(not_eq_zero_one_ty, &[zero_eq_one]);
            d.lam_fv(h_fv, mxy_eq_one_ty, false_proof)
        };
        let not_and = if x_is_one {
            let not_y = not_eq_zero_one(d, &p);
            not_and_of_right_false(d, &p, x_eq_one_ty, y_eq_one_ty, not_y)
        } else {
            let not_x = not_eq_zero_one(d, &p);
            not_and_of_left_false(d, &p, x_eq_one_ty, y_eq_one_ty, not_x)
        };
        iff_of_false_false(d, &p, mxy_eq_one_ty, and_ty, not_mxy, not_and)
    }
}

/// `Iff (Eq (mul (mod a 2) (mod b 2)) 1) (And (Eq (mod a 2) 1) (Eq (mod b 2)
/// 1))` — `cases_mod_two` on `a`, then on `b` inside each branch.
fn land_bit_numeric_iff(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let mod_b = d.modulo(b, two);

    let claim = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| -> ExprId {
        let one = d.num(1);
        let mxy = d.mul(x, y);
        let mxy_eq_one_ty = d.eq(mxy, one);
        let x_eq_one_ty = d.eq(x, one);
        let y_eq_one_ty = d.eq(y, one);
        let and_ty = d.const_app(p.logic.and, &[x_eq_one_ty, y_eq_one_ty]);
        d.const_app(p.logic.iff, &[mxy_eq_one_ty, and_ty])
    };

    let inner = |d: &mut NatDev<'_>, x: ExprId, x_is_one: bool| -> ExprId {
        let zero = d.zero();
        let one = d.num(1);
        let at_zero = land_bit_leaf(d, &p, x, zero, x_is_one, false);
        let at_one = land_bit_leaf(d, &p, x, one, x_is_one, true);
        cases_mod_two(d, &p, b, &|d, y| claim(d, x, y), at_zero, at_one)
    };

    let zero = d.zero();
    let one = d.num(1);
    let outer_zero = inner(d, zero, false);
    let outer_one = inner(d, one, true);
    cases_mod_two(d, &p, a, &|d, x| claim(d, x, mod_b), outer_zero, outer_one)
}

/// `Nat.land_mod_two_eq_one : ∀ a b, Iff (Eq (mod (land a b) 2) 1) (And (Eq
/// (mod a 2) 1) (Eq (mod b 2) 1))`.
fn declare_land_mod_two_eq_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.land_mod_two_eq_one, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let two = d.num(2);
        let one = d.num(1);
        let land_ab = d.const_app(p.land, &[a, b]);
        let mod_land_ab = d.modulo(land_ab, two);
        let lhs_ty = d.eq(mod_land_ab, one);
        let mod_a = d.modulo(a, two);
        let mod_b = d.modulo(b, two);
        let a_eq_one_ty = d.eq(mod_a, one);
        let b_eq_one_ty = d.eq(mod_b, one);
        let rhs_ty = d.const_app(p.logic.and, &[a_eq_one_ty, b_eq_one_ty]);

        // `mod (land a b) 2 = mod a 2 * mod b 2`, so `Eq (mod (land a b) 2) 1`
        // is `Iff`-equivalent (by substitution) to `Eq (mod a 2 * mod b 2) 1`.
        let bridge_eq = d.lemma(p.land_mod_two_eq_mul, &[a, b]);
        let mul_ab = d.mul(mod_a, mod_b);
        let mul_eq_one_ty = d.eq(mul_ab, one);
        let bridge_iff = {
            let mp = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let rev = d.symm(mod_land_ab, mul_ab, bridge_eq);
                let res = d.trans(mul_ab, mod_land_ab, one, rev, h);
                d.lam_fv(h_fv, lhs_ty, res)
            };
            let mpr = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let res = d.trans(mod_land_ab, mul_ab, one, bridge_eq, h);
                d.lam_fv(h_fv, mul_eq_one_ty, res)
            };
            d.const_app(p.logic.iff_intro, &[lhs_ty, mul_eq_one_ty, mp, mpr])
        };

        let numeric_iff = land_bit_numeric_iff(d, &p, a, b);
        let proof = iff_trans(
            d,
            &p,
            lhs_ty,
            mul_eq_one_ty,
            rhs_ty,
            bridge_iff,
            numeric_iff,
        );
        (d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]), proof)
    })?;
    Ok(())
}

/// Declare [`declare_land_one_is_mod`], [`declare_land_mod_two_eq_mul`], and
/// [`declare_land_mod_two_eq_one`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_land_low_bit_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_land_one_is_mod(d, p)?;
    declare_land_mod_two_eq_mul(d, p)?;
    declare_land_mod_two_eq_one(d, p)?;
    Ok(())
}
