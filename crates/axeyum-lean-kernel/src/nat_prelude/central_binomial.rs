//! `choose (2m+1) m ≤ 4^m` — the odd central binomial bound, the arithmetic
//! half of Erdős's proof of the primorial bound.
//!
//! ## Why `choose_le_two_pow` is not enough
//!
//! This prelude already has
//! `Nat.choose_le_two_pow : ∀ n k, k ≤ n → choose n k ≤ 2^n`. At `n = 2m+1`
//! that gives `choose (2m+1) m ≤ 2^(2m+1) = 2·4^m` — **off by a factor of
//! two**, and the factor of two is exactly what Erdős's induction cannot
//! afford (it is what makes the odd step `4^(m+1) · 4^m = 4^(2m+1)` close).
//!
//! The missing factor comes from the row sum having TWO equal terms at the
//! middle:
//!
//! ```text
//! choose (2m+1) m = choose (2m+1) (m+1)          -- choose_symm_of_eq_add
//! choose (2m+1) m + choose (2m+1) (m+1) ≤ 2^(2m+1) = 4^m + 4^m
//! ```
//!
//! so `2·choose (2m+1) m ≤ 2·4^m`. That is the whole content of this file.
//!
//! ## The two steps this prelude did not have
//!
//! 1. **Two DISTINCT terms of a `sumRange` are together at most the sum.**
//!    `Nat.le_sumRange_of_lt` is the one-term form and there was no two-term
//!    form. It is built here from `Nat.sumRange_succ` twice (peeling the two
//!    terms off the TOP of the truncated sum `sumRange f (m+2)`, where they
//!    sit at positions `m` and `m+1`) plus `Nat.sumRange_split` to bound that
//!    truncated sum by the full row.
//!
//!    The split direction matters. `sumRange_split f a j` states
//!    `sumRange f (a + j) = sumRange f a + sumRange (fun k => f (a+k)) j`, so
//!    with `a := m+2` and `j := m` the bound is `add (succ (succ m)) m` — and
//!    `Nat.add` recurses on its RIGHT argument, so that is STUCK at a symbolic
//!    `m`. One `add_comm` puts it as `add m (succ (succ m))`, which
//!    ι-reduces to `succ (succ (add m m))` = `succ (2m+1)` with no further
//!    work. This is the "symbolic side LEFT, literal RIGHT" rule applied to a
//!    bound rather than to an argument.
//!
//! 2. **`a + a ≤ b + b → a ≤ b`.** `Nat.le_of_add_le_add_right` cancels a
//!    COMMON summand and does not apply. `Nat.le_of_mul_le_mul_left` does,
//!    once `add a a` is spelled `mul 2 a` — which needs `mul a 2 = add a a`,
//!    itself one `zero_add` away because `mul x 2` reduces to
//!    `add (add zero x) x` and `add zero x` is stuck.
//!
//! ## What is declared
//!
//! | name | statement |
//! | --- | --- |
//! | `Nat.mul_two_eq_add_self` | `∀ a, mul a 2 = add a a` |
//! | `Nat.le_of_add_self_le_add_self` | `∀ a b, add a a ≤ add b b → a ≤ b` |
//! | `Nat.four_pow_eq_two_pow_add_self` | `∀ m, pow 4 m = pow 2 (add m m)` |
//! | `Nat.choose_two_mul_succ_le_two_pow` | `∀ m, choose (succ (add m m)) m ≤ pow 2 (add m m)` |
//! | `Nat.choose_two_mul_succ_le_four_pow` | `∀ m, choose (succ (add m m)) m ≤ pow 4 m` |
//!
//! `2m+1` is spelled `succ (add m m)` rather than `add (mul 2 m) 1`: `mul 2 m`
//! is stuck at a symbolic `m` (multiplication recurses on the right), whereas
//! `add m m` is the form `sumRange_split` and `choose_symm_of_eq_add` both
//! reduce against — `add m (succ m)` ι-reduces to `succ (add m m)`, which is
//! why the symmetry hypothesis is `Eq.refl`.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `h : Le from right ⊢ Le to right`, given `eq : Eq from to`.
fn rewrite_le_left(
    d: &mut NatDev<'_>,
    from: ExprId,
    to: ExprId,
    eq: ExprId,
    right: ExprId,
    h: ExprId,
) -> ExprId {
    let motive = d.eq_motive(from, &|d, x| d.le(x, right));
    d.transport(from, motive, h, to, eq)
}

/// `h : Le left from ⊢ Le left to`, given `eq : Eq from to`.
fn rewrite_le_right(
    d: &mut NatDev<'_>,
    from: ExprId,
    to: ExprId,
    eq: ExprId,
    left: ExprId,
    h: ExprId,
) -> ExprId {
    let motive = d.eq_motive(from, &|d, x| d.le(left, x));
    d.transport(from, motive, h, to, eq)
}

/// `Nat.mul_two_eq_add_self : ∀ a, Eq (mul a 2) (add a a)` and
/// `Nat.le_of_add_self_le_add_self : ∀ a b, Le (add a a) (add b b) → Le a b`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_add_self_cancellation(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // mul_two_eq_add_self : ∀ a, mul a 2 = add a a
    //
    // `mul a 2` delta/iota-reduces to `add (add zero a) a`, so the statement
    // is `zero_add` under one `add _ a` congruence and the left-hand side
    // needs no rewriting at all.
    {
        d.theorem(p.mul_two_eq_add_self, 1, &|d, vars| {
            let p = d.prelude();
            let a = vars[0];
            let two = d.num(2);
            let lhs = d.mul(a, two);
            let rhs = d.add(a, a);
            let stmt = d.eq(lhs, rhs);
            let zero = d.zero();
            let zero_plus = d.add(zero, a);
            let h = d.const_app(p.zero_add, &[a]);
            let proof = d.congr(zero_plus, a, h, &|d, x| d.add(x, a));
            (stmt, proof)
        })?;
    }

    // le_of_add_self_le_add_self : ∀ a b, Le (add a a) (add b b) → Le a b
    {
        let nat = d.nat_ty();
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let aa = d.add(a, a);
        let bb = d.add(b, b);
        let h_ty = d.le(aa, bb);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let two = d.num(2);
        let a2 = d.mul(a, two);
        let b2 = d.mul(b, two);
        let two_a = d.mul(two, a);
        let two_b = d.mul(two, b);

        // `add a a = mul a 2` and `add b b = mul b 2`, both flipped.
        let e_a = {
            let fwd = d.const_app(p.mul_two_eq_add_self, &[a]);
            d.symm(a2, aa, fwd)
        };
        let e_b = {
            let fwd = d.const_app(p.mul_two_eq_add_self, &[b]);
            d.symm(b2, bb, fwd)
        };
        let step1 = rewrite_le_left(d, aa, a2, e_a, bb, h);
        let step2 = rewrite_le_right(d, bb, b2, e_b, a2, step1);

        let c_a = d.const_app(p.mul_comm, &[a, two]);
        let c_b = d.const_app(p.mul_comm, &[b, two]);
        let step3 = rewrite_le_left(d, a2, two_a, c_a, b2, step2);
        let step4 = rewrite_le_right(d, b2, two_b, c_b, two_a, step3);

        let one_le_two = {
            let zero = d.zero();
            let one = d.num(1);
            let base = d.const_app(p.zero_le, &[one]);
            d.const_app(p.le_succ_succ, &[zero, one, base])
        };
        let proof = d.const_app(p.le_of_mul_le_mul_left, &[two, a, b, one_le_two, step4]);

        let concl = d.le(a, b);
        let ty = {
            let inner = d.arrow(h_ty, concl);
            let mid = d.pi_fv(b_fv, nat, inner);
            d.pi_fv(a_fv, nat, mid)
        };
        let value = {
            let inner = d.lam_fv(h_fv, h_ty, proof);
            let mid = d.lam_fv(b_fv, nat, inner);
            d.lam_fv(a_fv, nat, mid)
        };
        d.declare_theorem(p.le_of_add_self_le_add_self, ty, value)?;
    }
    Ok(())
}

/// `Nat.choose_two_mul_succ_le_two_pow : ∀ m,
/// Le (choose (succ (add m m)) m) (pow 2 (add m m))`.
///
/// The row sum `∑_{k ≤ 2m+1} choose (2m+1) k = 2^(2m+1)` carries the middle
/// coefficient TWICE (`choose (2m+1) m = choose (2m+1) (m+1)`), so twice the
/// coefficient is at most twice `4^m` — and `4^m` here is spelled
/// `pow 2 (add m m)`, which needs no `4^m = 2^(2m)` bridge at all. See the
/// module doc for the two missing steps and why the `sumRange_split` bound is
/// written `add (succ (succ m)) m` and then commuted.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_central_binomial_bound(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.choose_two_mul_succ_le_two_pow, 1, &|d, vars| {
        let p = d.prelude();
        let nat = d.nat_ty();
        let m = vars[0];
        let mm = d.add(m, m);
        let n = d.succ(mm);
        let sm = d.succ(m);
        let sm2 = d.succ(sm);
        let sn = d.succ(n);

        // f = fun k => choose n k, built to match `sum_choose_row`'s own body.
        let f = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = d.choose(n, k);
            d.lam_fv(k_fv, nat, body)
        };
        let fm = d.choose(n, m);
        let fsm = d.choose(n, sm);

        let two = d.num(2);
        let pow_n = d.pow(two, n);
        let pow_mm = d.pow(two, mm);
        let stmt = d.le(fm, pow_mm);

        // 1. the row sum
        let row = d.const_app(p.sum_choose_row, &[n]);
        let sum_full = d.sum_range(f, sn);

        // 2/3/4. split the row at `m+2`, after commuting the stuck bound.
        let split = d.const_app(p.sum_range_split, &[f, sm2, m]);
        let head = d.sum_range(f, sm2);
        let tail = {
            let g = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let shifted = d.add(sm2, k);
                let body = d.apply(f, &[shifted]);
                d.lam_fv(k_fv, nat, body)
            };
            d.sum_range(g, m)
        };
        let split_rhs = d.add(head, tail);
        let stuck_bound = d.add(sm2, m);
        let comm_bound = d.const_app(p.add_comm, &[sm2, m]);
        let commuted = d.add(m, sm2);
        let split_at_row = {
            let motive = d.eq_motive(stuck_bound, &|d, x| {
                let lhs = d.sum_range(f, x);
                d.eq(lhs, split_rhs)
            });
            d.transport(stuck_bound, motive, split, commuted, comm_bound)
        };
        // `split_at_row : sumRange f (m + (m+2)) = head + tail`, and
        // `m + (m+2)` iota-reduces to `succ (succ (add m m))` = `succ n`.

        // 5. head ≤ full row
        let head_le_sum = {
            let h = d.const_app(p.le_add_right, &[head, tail]);
            let flipped = d.symm(sum_full, split_rhs, split_at_row);
            rewrite_le_right(d, split_rhs, sum_full, flipped, head, h)
        };

        // 6. peel the two middle terms off the top of `sumRange f (m+2)`
        let s_m = d.sum_range(f, m);
        let s_sm = d.sum_range(f, sm);
        let peel_outer = d.const_app(p.sum_range_succ, &[f, sm]);
        let peel_inner = d.const_app(p.sum_range_succ, &[f, m]);
        let a2 = d.add(s_m, fm);
        let peel_congr = d.congr(s_sm, a2, peel_inner, &|d, x| d.add(x, fsm));
        let outer_rhs = d.add(s_sm, fsm);
        let peeled_rhs = d.add(a2, fsm);
        let peel = d.trans(head, outer_rhs, peeled_rhs, peel_outer, peel_congr);

        // 7. fm + fsm ≤ head
        let pair = d.add(fm, fsm);
        let fm_le_a2 = {
            let h = d.const_app(p.le_add_right, &[fm, s_m]);
            let flipped_from = d.add(fm, s_m);
            let comm = d.const_app(p.add_comm, &[fm, s_m]);
            rewrite_le_right(d, flipped_from, a2, comm, fm, h)
        };
        let pair_le_peeled = d.const_app(p.add_le_add_right, &[fsm, fm, a2, fm_le_a2]);
        let peel_flipped = d.symm(head, peeled_rhs, peel);
        let pair_le_head =
            rewrite_le_right(d, peeled_rhs, head, peel_flipped, pair, pair_le_peeled);

        // 8. the two middle coefficients are equal
        let symm_hyp = d.refl(n);
        let choose_symm = d.const_app(p.choose_symm_of_eq_add, &[n, m, sm, symm_hyp]);
        let fsm_eq_fm = d.symm(fm, fsm, choose_symm);

        // 9/10/11. double it, chain to the row sum, land on `2^(2m+1)`
        let doubled = d.add(fm, fm);
        let double_le_head = {
            let eq_pair = d.congr(fsm, fm, fsm_eq_fm, &|d, x| d.add(fm, x));
            rewrite_le_left(d, pair, doubled, eq_pair, head, pair_le_head)
        };
        let double_le_sum = d.const_app(
            p.le_trans,
            &[doubled, head, sum_full, double_le_head, head_le_sum],
        );
        let double_le_pow = rewrite_le_right(d, sum_full, pow_n, row, doubled, double_le_sum);

        // 12/13. `2^(2m+1) = 2^(2m) + 2^(2m)`
        let pow_split = {
            let step = d.const_app(p.pow_succ, &[two, mm]);
            let scaled = d.mul(pow_mm, two);
            let halve = d.const_app(p.mul_two_eq_add_self, &[pow_mm]);
            let target = d.add(pow_mm, pow_mm);
            d.trans(pow_n, scaled, target, step, halve)
        };
        let pow_pair = d.add(pow_mm, pow_mm);
        let double_le_double =
            rewrite_le_right(d, pow_n, pow_pair, pow_split, doubled, double_le_pow);

        // 14. cancel
        let proof = d.const_app(
            p.le_of_add_self_le_add_self,
            &[fm, pow_mm, double_le_double],
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.four_pow_eq_two_pow_add_self : ∀ m, Eq (pow 4 m) (pow 2 (add m m))`
/// and the `4^m` restatement
/// `Nat.choose_two_mul_succ_le_four_pow : ∀ m,
/// Le (choose (succ (add m m)) m) (pow 4 m)`.
///
/// Induction on `m`. The successor case's exponent is `add (succ m) (succ m)`,
/// which ι-reduces to `succ (add (succ m) m)` and then STOPS — `add (succ m) m`
/// is stuck at a symbolic `m` — so `succ_add` is applied under one `succ`
/// congruence before the two `pow_succ` steps line up. On the value side
/// `mul x 4` and `mul (mul x 2) 2` are related by `mul_assoc` alone: `mul 2 2`
/// is closed and reduces to `4`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_four_pow_bridge(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // four_pow_eq_two_pow_add_self : ∀ m, pow 4 m = pow 2 (add m m)
    {
        d.theorem(p.four_pow_eq_two_pow_add_self, 1, &|d, vars| {
            let m = vars[0];
            let claim = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
                let four = d.num(4);
                let two = d.num(2);
                let lhs = d.pow(four, x);
                let xx = d.add(x, x);
                let rhs = d.pow(two, xx);
                d.eq(lhs, rhs)
            };
            let stmt = claim(d, m);
            let proof = d.induct(
                &claim,
                &|d| {
                    let one = d.num(1);
                    d.refl(one)
                },
                &|d, j, ih| {
                    let p = d.prelude();
                    let two = d.num(2);
                    let four = d.num(4);
                    let jj = d.add(j, j);
                    let sj = d.succ(j);

                    // Left: pow 4 (succ j) ≡ mul (pow 4 j) 4, and `ih`
                    // rewrites `pow 4 j` to `pow 2 (j+j)`.
                    let pow4_j = d.pow(four, j);
                    let pow2_jj = d.pow(two, jj);
                    let left_start = d.mul(pow4_j, four);
                    let left_mid = d.mul(pow2_jj, four);
                    let left_step = d.congr(pow4_j, pow2_jj, ih, &|d, x| {
                        let four = d.num(4);
                        d.mul(x, four)
                    });

                    // `mul x 4 = mul (mul x 2) 2` is `mul_assoc` flipped:
                    // `mul 2 2` is closed and reduces to `4`.
                    let scaled = d.mul(pow2_jj, two);
                    let twice = d.mul(scaled, two);
                    let assoc = d.const_app(p.mul_assoc, &[pow2_jj, two, two]);
                    let assoc_flipped = d.symm(twice, left_mid, assoc);

                    // Right: pow 2 (add (succ j) (succ j))
                    //      ≡ pow 2 (succ (add (succ j) j))
                    //      = pow 2 (succ (succ (add j j)))   -- succ_add
                    //      ≡ mul (mul (pow 2 (j+j)) 2) 2
                    let stuck = d.add(sj, j);
                    let unstuck = d.succ(jj);
                    let succ_add = d.const_app(p.succ_add, &[j, j]);
                    let right_eq = d.congr(stuck, unstuck, succ_add, &|d, x| {
                        let two = d.num(2);
                        let bumped = d.succ(x);
                        d.pow(two, bumped)
                    });
                    // `right_eq : pow 2 (succ (add (succ j) j))
                    //            = pow 2 (succ (succ (add j j)))`, whose left
                    // side is definitionally `pow 2 (add (succ j) (succ j))`.

                    let target_left = {
                        let sj_sj = d.add(sj, sj);
                        d.pow(two, sj_sj)
                    };
                    let target_right = {
                        let bumped = d.succ(unstuck);
                        d.pow(two, bumped)
                    };
                    let right_flipped = d.symm(target_left, target_right, right_eq);
                    // `right_flipped : pow 2 (succ (succ (j+j)))
                    //                 = pow 2 (add (succ j) (succ j))`, and the
                    // left side is definitionally `twice`.

                    let chained = d.trans(left_start, left_mid, twice, left_step, assoc_flipped);
                    d.trans(left_start, twice, target_left, chained, right_flipped)
                },
                m,
            );
            (stmt, proof)
        })?;
    }

    // choose_two_mul_succ_le_four_pow : ∀ m, choose (2m+1) m ≤ 4^m
    {
        d.theorem(p.choose_two_mul_succ_le_four_pow, 1, &|d, vars| {
            let p = d.prelude();
            let m = vars[0];
            let mm = d.add(m, m);
            let n = d.succ(mm);
            let fm = d.choose(n, m);
            let four = d.num(4);
            let two = d.num(2);
            let pow4 = d.pow(four, m);
            let pow2 = d.pow(two, mm);
            let stmt = d.le(fm, pow4);
            let base = d.const_app(p.choose_two_mul_succ_le_two_pow, &[m]);
            let bridge = d.const_app(p.four_pow_eq_two_pow_add_self, &[m]);
            let flipped = d.symm(pow4, pow2, bridge);
            let proof = rewrite_le_right(d, pow2, pow4, flipped, fm, base);
            (stmt, proof)
        })?;
    }
    Ok(())
}
