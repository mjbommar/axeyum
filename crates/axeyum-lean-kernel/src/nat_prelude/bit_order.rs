//! `Nat.lt_of_testBit` (Nat-valued local analogue) and its supporting
//! arithmetic toolkit (`self_lt_two_pow`, `self_lt_two_pow_add`) — pieces
//! toward `F:ml430-nat-lt-xor-cases-c43a1e85`. See
//! `docs/plan/status/260-nat-lt-xor-cases.md` /
//! `docs/plan/status/263-nat-testbit-xor.md` for pieces 1 and the overall
//! plan; `docs/plan/status/265-nat-msb-order.md` for this lane's handoff.
//!
//! WORK IN PROGRESS scaffold: dispatch is a no-op until each declaration is
//! landed below.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `Eq (mul x (num 2)) (add x x)`. `mul x 2` reduces (`refl`, `mul_succ`
/// twice then `mul_zero`) to `add (add zero x) x`, NOT directly to
/// `add x x` -- `add` recurses on its SECOND argument, so `add zero x` does
/// not reduce for a symbolic `x`. `zero_add` closes exactly that gap; every
/// caller below only ever needs the RESULT type up to the kernel's own
/// `def_eq` (which sees straight through the `mul`/`pow_succ` unfolds), so
/// this is the one genuinely non-`refl` step in the whole "doubling" family.
fn double_eq(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let add_zero_x = d.add(zero, x);
    let zero_add_x = d.lemma(p.zero_add, &[x]);
    d.congr(add_zero_x, x, zero_add_x, &|d, y| d.add(y, x))
}

/// `Nat.self_lt_two_pow : ∀ n, Lt n (pow 2 n)`. Induction on `n`.
///
/// Base (`n=0`): `Lt 0 (pow 2 0)` is `def_eq` `Lt 0 1` (`pow_zero` is
/// `refl`), so `zero_lt_succ 0` closes it with no rewriting.
///
/// Step (`n=j` -> `n=succ j`, `ih : Lt j Pj` where `Pj := pow 2 j`, `def_eq`
/// `Le (succ j) Pj`): the target `Lt (succ j) (pow 2 (succ j))` is `def_eq`
/// `Le (succ (succ j)) (mul Pj 2)` (`pow_succ` is `refl`). Chain
/// `succ j ≤ Pj` (`ih`) with `1 ≤ Pj` (from `ih` again, via `le_trans`
/// through `zero_lt_succ j : 1 ≤ succ j`) to get, via `add_le_add_right`
/// then `add_le_add_left`, `add (succ j) 1 ≤ add Pj Pj`; `add (succ j) 1` is
/// `def_eq` `succ (succ j)` (two `refl` steps of `add`'s own recursion), and
/// [`double_eq`] bridges `add Pj Pj` up to `mul Pj 2`.
fn declare_self_lt_two_pow(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.self_lt_two_pow, 1, &|d, v| {
        let n = v[0];

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let two = d.num(2);
            let px = d.pow(two, x);
            d.lt(x, px)
        };

        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            d.zero_lt_succ(zero)
        };

        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let two = d.num(2);
            let pj = d.pow(two, j);
            let one = d.num(1);
            let succ_j = d.succ(j);

            // one_le_pj : Le one pj.
            let one_le_succ_j = d.zero_lt_succ(j); // Le 1 (succ j)
            let one_le_pj = d.lemma(p.le_trans, &[one, succ_j, pj, one_le_succ_j, ih]);

            // step1 : Le (add succ_j one) (add pj one), from `ih`.
            let step1 = d.lemma(p.add_le_add_right, &[one, succ_j, pj, ih]);
            // step2 : Le (add pj one) (add pj pj), from `one_le_pj`.
            let step2 = d.lemma(p.add_le_add_left, &[pj, one, pj, one_le_pj]);

            let add_succ_j_one = d.add(succ_j, one);
            let add_pj_one = d.add(pj, one);
            let add_pj_pj = d.add(pj, pj);
            let combined = d.lemma(
                p.le_trans,
                &[add_succ_j_one, add_pj_one, add_pj_pj, step1, step2],
            );
            // combined : Le add_succ_j_one add_pj_pj

            // Bridge `add pj pj` up to `mul pj 2` (== `pow 2 (succ j)` by
            // `refl`), and transport `combined` along it.
            let double_pj = double_eq(d, &p, pj); // Eq (add(add zero pj)pj) add_pj_pj
            let add_zero_pj = {
                let zero = d.zero();
                d.add(zero, pj)
            };
            let mul_pj_two = d.add(add_zero_pj, pj);
            let rev = d.symm(mul_pj_two, add_pj_pj, double_pj);
            let motive_t = d.eq_motive(add_pj_pj, &|d, x| d.le(add_succ_j_one, x));
            d.transport(add_pj_pj, motive_t, combined, mul_pj_two, rev)
            // result : Le add_succ_j_one mul_pj_two
            //   == Le (succ (succ j)) (mul pj 2)              [def_eq, add]
            //   == Lt (succ j) (pow 2 (succ j))                [def_eq, pow_succ/Lt]
        };

        let proof = d.induct(&motive, &base, &step, n);
        (motive(d, n), proof)
    })?;
    Ok(())
}

/// `Nat.self_lt_two_pow_add : ∀ a b, Lt a (pow 2 (add a b))`. Induction on
/// `b`, `a` held fixed throughout (never generalized to a DIFFERENT value,
/// unlike the `size`/`testBit` fuel proofs elsewhere in this prelude, so no
/// "generalize the other variable" device is needed here).
///
/// Base (`b=0`): `add a 0` is `refl`-`a`, so the target is `def_eq`
/// [`NatPrelude::self_lt_two_pow`] at `a` directly.
///
/// Step (`b=j` -> `b=succ j`, `ih : Lt a Qj` where `Qj := pow 2 (add a j)`,
/// `def_eq` `Le (succ a) Qj`): `add a (succ j)` is `refl`-`succ (add a j)`,
/// so the target is `def_eq` `Le (succ a) (mul Qj 2)`. `Qj ≤ add Qj Qj`
/// (`le_add_right`) composed with `ih` via `le_trans` gives
/// `succ a ≤ add Qj Qj`; [`double_eq`] bridges to `mul Qj 2`.
fn declare_self_lt_two_pow_add(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.self_lt_two_pow_add, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let two = d.num(2);
            let ax = d.add(a, x);
            let pax = d.pow(two, ax);
            d.lt(a, pax)
        };

        let base = |d: &mut NatDev<'_>| -> ExprId { d.lemma(p.self_lt_two_pow, &[a]) };

        let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
            let two = d.num(2);
            let aj = d.add(a, j);
            let qj = d.pow(two, aj);
            let succ_a = d.succ(a);

            // ih : Le succ_a qj (def_eq).
            let add_qj_qj = d.add(qj, qj);
            let le_qj_add = d.lemma(p.le_add_right, &[qj, qj]); // Le qj (add qj qj)
            let combined = d.lemma(p.le_trans, &[succ_a, qj, add_qj_qj, ih, le_qj_add]);
            // combined : Le succ_a (add qj qj)

            let double_qj = double_eq(d, &p, qj);
            let add_zero_qj = {
                let zero = d.zero();
                d.add(zero, qj)
            };
            let mul_qj_two = d.add(add_zero_qj, qj);
            let rev = d.symm(mul_qj_two, add_qj_qj, double_qj);
            let motive_t = d.eq_motive(add_qj_qj, &|d, x| d.le(succ_a, x));
            d.transport(add_qj_qj, motive_t, combined, mul_qj_two, rev)
            // result : Le succ_a mul_qj_two
            //   == Lt a (pow 2 (succ aj))       [def_eq]
            //   == Lt a (pow 2 (add a (succ j)))[def_eq, add's succ case]
        };

        let proof = d.induct(&motive, &base, &step, b);
        (motive(d, b), proof)
    })?;
    Ok(())
}

/// Everything this module declares, in dependency order.
pub(super) fn declare_bit_order_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_self_lt_two_pow(d, p)?;
    declare_self_lt_two_pow_add(d, p)?;
    Ok(())
}
