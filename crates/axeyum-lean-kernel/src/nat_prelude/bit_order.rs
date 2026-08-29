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

/// `fun i => mul (testBit n i) (pow 2 i)` -- duplicated from `binary.rs`'s
/// private `term_fn` (off-limits to edit; five lines, identical).
fn bit_term_fn(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let tb = d.const_app(p.test_bit, &[n, i]);
    let two = d.num(2);
    let p2i = d.pow(two, i);
    let body = d.mul(tb, p2i);
    d.lam_fv(i_fv, nat, body)
}

/// `fun x => f (add m x)` -- duplicated from `rectangle.rs`'s private
/// `shifted` (off-limits to edit; five lines, identical), renamed to avoid
/// a name clash with that module's own private helper of the same shape.
fn shifted_by(d: &mut NatDev<'_>, f: ExprId, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let mx = d.add(m, x);
    let fmx = d.apply(f, &[mx]);
    d.lam_fv(x_fv, nat, fmx)
}

/// `Eq (sumRange (bit_term_fn val) bound) val`, given a proof that
/// `val < pow 2 bound`: `sum_test_bit_lt` identifies the sum with
/// `mod val (pow 2 bound)`, and `mod_eq_self_of_lt` collapses that to
/// `val`.
fn value_eq_sum_range(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    val: ExprId,
    bound: ExprId,
    val_lt_pow: ExprId,
) -> ExprId {
    let p = *p;
    let two = d.num(2);
    let pow2b = d.pow(two, bound);
    let mod_eq = d.lemma(p.mod_eq_self_of_lt, &[val, pow2b, val_lt_pow]);
    let f_val = bit_term_fn(d, &p, val);
    let sum_lt = d.lemma(p.sum_test_bit_lt, &[bound, val]);
    let sum_f_val_bound = d.sum_range(f_val, bound);
    let mod_val = d.modulo(val, pow2b);
    let (_e, combined) = d.chain(sum_f_val_bound, &[(mod_val, sum_lt), (val, mod_eq)]);
    combined
}

/// `Nat.lt_of_testBit : ∀ n m i,
///   Eq (testBit n i) zero → Eq (testBit m i) one →
///   (∀ j, Lt i j → Eq (testBit n j) (testBit m j)) → Lt n m`.
///
/// Nat-valued (Mathlib's `testBit` returns `Bool`; the pinned mirror,
/// `F:ml430-nat-lt-of-testbit-72f64ab8`, stays `open` for that reason), so
/// this is a local fact, not an `ml430` flip.
///
/// Route: pick `N := add n (add m (succ i))` -- large enough (via
/// [`NatPrelude::self_lt_two_pow_add`]) to bound BOTH `n` and `m` by
/// `pow 2 N`, and, rearranged via `add_assoc`/`add_comm`/`add_right_comm`
/// (`eq_i`/`eq_m` below), already of the shape `add (succ i) (add n m)`
/// that `sum_range_split` needs to peel off everything up to and including
/// bit `i`. `n` and `m` are then each `(low bits below i) + (bit i's own
/// contribution) + (a TAIL over bits above i)`; the agreement hypothesis
/// makes the two tails LITERALLY equal (`sum_range_congr`), `H0`/`H1`
/// collapse bit `i`'s contribution to `0` for `n` and `pow 2 i` for `m`,
/// and `n`'s low bits are `< pow 2 i` (`sum_test_bit_lt` + `mod_lt`) while
/// `m`'s low bits contribute at least `0` -- so `n`'s total is strictly
/// below `m`'s.
fn declare_lt_of_test_bit(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.lt_of_test_bit, 3, &|d, v| {
        let (n, m, i) = (v[0], v[1], v[2]);
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let succ_i = d.succ(i);

        // Hypothesis types.
        let tb_n_i = d.const_app(p.test_bit, &[n, i]);
        let tb_m_i = d.const_app(p.test_bit, &[m, i]);
        let h0_ty = d.eq(tb_n_i, zero);
        let h1_ty = d.eq(tb_m_i, one);
        let hagree_ty = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let lt_i_j = d.lt(i, j);
            let tb_n_j = d.const_app(p.test_bit, &[n, j]);
            let tb_m_j = d.const_app(p.test_bit, &[m, j]);
            let eq_j = d.eq(tb_n_j, tb_m_j);
            let body = d.arrow(lt_i_j, eq_j);
            d.pi_fv(j_fv, nat, body)
        };

        let h0_fv = d.fresh_fvar();
        let h0 = d.kernel().fvar(h0_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let hagree_fv = d.fresh_fvar();
        let hagree = d.kernel().fvar(hagree_fv);

        // big_n := add n (add m succ_i).
        let m_plus_succ_i = d.add(m, succ_i);
        let big_n = d.add(n, m_plus_succ_i);

        // assoc_form := add (add n m) succ_i; eq_assoc : Eq big_n assoc_form.
        let n_plus_m = d.add(n, m);
        let assoc_form = d.add(n_plus_m, succ_i);
        let add_assoc_nm = d.lemma(p.add_assoc, &[n, m, succ_i]); // Eq assoc_form big_n
        let eq_assoc = d.symm(assoc_form, big_n, add_assoc_nm);

        // eq_i : Eq big_n (add succ_i (add n m)).
        let succ_i_plus_nm = d.add(succ_i, n_plus_m);
        let add_comm_nm_si = d.lemma(p.add_comm, &[n_plus_m, succ_i]);
        let (_e_i, eq_i) = d.chain(
            big_n,
            &[(assoc_form, eq_assoc), (succ_i_plus_nm, add_comm_nm_si)],
        );

        // eq_m : Eq big_n (add m (add n succ_i)).
        let m_plus_n = d.add(m, n);
        let add_comm_n_m = d.lemma(p.add_comm, &[n, m]);
        let mn_form = d.add(m_plus_n, succ_i);
        let congr_nm = d.congr(n_plus_m, m_plus_n, add_comm_n_m, &|d, x| d.add(x, succ_i));
        let n_plus_succ_i = d.add(n, succ_i);
        let m_form = d.add(m, n_plus_succ_i);
        let add_assoc_m = d.lemma(p.add_assoc, &[m, n, succ_i]);
        let (_e_m, eq_m) = d.chain(
            big_n,
            &[
                (assoc_form, eq_assoc),
                (mn_form, congr_nm),
                (m_form, add_assoc_m),
            ],
        );

        // n_lt_2n : Lt n (pow 2 big_n) -- DIRECT (big_n is literally
        // `add n (add m succ_i)`, self_lt_two_pow_add's own shape at a:=n).
        let n_lt_2n = d.lemma(p.self_lt_two_pow_add, &[n, m_plus_succ_i]);

        // m_lt_2n : Lt m (pow 2 big_n), via self_lt_two_pow_add at
        // (m, add n succ_i), transported along `eq_m`.
        let m_bound_raw = d.lemma(p.self_lt_two_pow_add, &[m, n_plus_succ_i]);
        let motive_m = d.eq_motive(m_form, &|d, x| {
            let two2 = d.num(2);
            let px = d.pow(two2, x);
            d.lt(m, px)
        });
        let eq_m_rev = d.symm(big_n, m_form, eq_m);
        let m_lt_2n = d.transport(m_form, motive_m, m_bound_raw, big_n, eq_m_rev);

        // n = sumRange f_n big_n ; m = sumRange f_m big_n.
        let n_sum_eq_val = value_eq_sum_range(d, &p, n, big_n, n_lt_2n);
        let m_sum_eq_val = value_eq_sum_range(d, &p, m, big_n, m_lt_2n);

        let f_n = bit_term_fn(d, &p, n);
        let f_m = bit_term_fn(d, &p, m);
        let sum_f_n_bign = d.sum_range(f_n, big_n);
        let sum_f_m_bign = d.sum_range(f_m, big_n);

        // Rewrite the bound to `add succ_i (add n m)`, then split.
        let sum_f_n_split_bound = d.sum_range(f_n, succ_i_plus_nm);
        let split_bound_n = d.congr(big_n, succ_i_plus_nm, eq_i, &|d, x| d.sum_range(f_n, x));
        let sum_f_m_split_bound = d.sum_range(f_m, succ_i_plus_nm);
        let split_bound_m = d.congr(big_n, succ_i_plus_nm, eq_i, &|d, x| d.sum_range(f_m, x));

        let shifted_f_n = shifted_by(d, f_n, succ_i);
        let shifted_f_m = shifted_by(d, f_m, succ_i);
        let tail_n = d.sum_range(shifted_f_n, n_plus_m);
        let tail_m = d.sum_range(shifted_f_m, n_plus_m);
        let sr_n_succ_i = d.sum_range(f_n, succ_i);
        let sr_m_succ_i = d.sum_range(f_m, succ_i);
        let split_n = d.lemma(p.sum_range_split, &[f_n, succ_i, n_plus_m]);
        let split_m = d.lemma(p.sum_range_split, &[f_m, succ_i, n_plus_m]);

        let n_sum_eq_val_rev = d.symm(sum_f_n_bign, n, n_sum_eq_val);
        let sr_n_succ_i_plus_tail_n = d.add(sr_n_succ_i, tail_n);
        let eq_n_decomp = d
            .chain(
                n,
                &[
                    (sum_f_n_bign, n_sum_eq_val_rev),
                    (sum_f_n_split_bound, split_bound_n),
                    (sr_n_succ_i_plus_tail_n, split_n),
                ],
            )
            .1;
        let m_sum_eq_val_rev = d.symm(sum_f_m_bign, m, m_sum_eq_val);
        let sr_m_succ_i_plus_tail_m = d.add(sr_m_succ_i, tail_m);
        let eq_m_decomp = d
            .chain(
                m,
                &[
                    (sum_f_m_bign, m_sum_eq_val_rev),
                    (sum_f_m_split_bound, split_bound_m),
                    (sr_m_succ_i_plus_tail_m, split_m),
                ],
            )
            .1;

        // sr_n_succ_i = sr_n_i (bit i contributes 0 for n).
        let pow2_i = d.pow(two, i);
        let f_n_i_app = d.apply(f_n, &[i]);
        let mul_tb_n_pow = d.mul(tb_n_i, pow2_i);
        let mul_zero_pow = d.mul(zero, pow2_i);
        let congr_h0 = d.congr(tb_n_i, zero, h0, &|d, y| d.mul(y, pow2_i));
        let zero_mul_pow2i = d.lemma(p.zero_mul, &[pow2_i]);
        let f_n_i_eq_zero = d
            .chain(
                f_n_i_app,
                &[(mul_zero_pow, congr_h0), (zero, zero_mul_pow2i)],
            )
            .1;
        let _ = mul_tb_n_pow;

        let sr_n_i = d.sum_range(f_n, i);
        let sr_n_succ_i_eq = d.lemma(p.sum_range_succ, &[f_n, i]);
        let congr_f_n_i_zero = d.congr(f_n_i_app, zero, f_n_i_eq_zero, &|d, x| d.add(sr_n_i, x));
        let add_zero_sr_n_i = d.lemma(p.add_zero, &[sr_n_i]);
        let sr_n_i_plus_f_n_i = d.add(sr_n_i, f_n_i_app);
        let sr_n_i_plus_zero = d.add(sr_n_i, zero);
        let sr_n_succ_i_eq_sr_n_i = d
            .chain(
                sr_n_succ_i,
                &[
                    (sr_n_i_plus_f_n_i, sr_n_succ_i_eq),
                    (sr_n_i_plus_zero, congr_f_n_i_zero),
                    (sr_n_i, add_zero_sr_n_i),
                ],
            )
            .1;

        // sr_m_succ_i = add sr_m_i pow2_i (bit i contributes pow2_i for m).
        let f_m_i_app = d.apply(f_m, &[i]);
        let mul_one_pow = d.mul(one, pow2_i);
        let congr_h1 = d.congr(tb_m_i, one, h1, &|d, y| d.mul(y, pow2_i));
        let one_mul_pow2i = d.lemma(p.one_mul, &[pow2_i]);
        let f_m_i_eq_pow2i = d
            .chain(
                f_m_i_app,
                &[(mul_one_pow, congr_h1), (pow2_i, one_mul_pow2i)],
            )
            .1;

        let sr_m_i = d.sum_range(f_m, i);
        let sr_m_succ_i_eq = d.lemma(p.sum_range_succ, &[f_m, i]);
        let congr_f_m_i = d.congr(f_m_i_app, pow2_i, f_m_i_eq_pow2i, &|d, x| d.add(sr_m_i, x));
        let sr_m_plus_pow2i = d.add(sr_m_i, pow2_i);
        let sr_m_i_plus_f_m_i = d.add(sr_m_i, f_m_i_app);
        let sr_m_succ_i_eq_final = d
            .chain(
                sr_m_succ_i,
                &[
                    (sr_m_i_plus_f_m_i, sr_m_succ_i_eq),
                    (sr_m_plus_pow2i, congr_f_m_i),
                ],
            )
            .1;

        // tail_n = tail_m, from Hagree.
        let pointwise = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let j = d.add(succ_i, x);
            let lt_i_j = d.lemma(p.le_add_right, &[succ_i, x]); // Le succ_i (add succ_i x)
            let tb_n_j = d.const_app(p.test_bit, &[n, j]);
            let tb_m_j = d.const_app(p.test_bit, &[m, j]);
            let tb_eq = d.apply(hagree, &[j, lt_i_j]);
            let pow2_j = d.pow(two, j);
            let result = d.congr(tb_n_j, tb_m_j, tb_eq, &|d, y| d.mul(y, pow2_j));
            d.lam_fv(x_fv, nat, result)
        };
        let tail_eq = d.lemma(
            p.sum_range_congr,
            &[shifted_f_n, shifted_f_m, n_plus_m, pointwise],
        );

        // Combine: n = add sr_n_i tail_n ; m = add sr_m_plus_pow2i tail_n.
        let congr_n_final = d.congr(sr_n_succ_i, sr_n_i, sr_n_succ_i_eq_sr_n_i, &|d, x| {
            d.add(x, tail_n)
        });
        let add_a_t = d.add(sr_n_i, tail_n);
        let eq_n_final = d
            .chain(
                n,
                &[
                    (sr_n_succ_i_plus_tail_n, eq_n_decomp),
                    (add_a_t, congr_n_final),
                ],
            )
            .1;

        let congr_m_final = d.congr(
            sr_m_succ_i,
            sr_m_plus_pow2i,
            sr_m_succ_i_eq_final,
            &|d, x| d.add(x, tail_m),
        );
        let tail_eq_rev = d.symm(tail_n, tail_m, tail_eq);
        let congr_m_tail = d.congr(tail_m, tail_n, tail_eq_rev, &|d, x| {
            d.add(sr_m_plus_pow2i, x)
        });
        let add_smp_tm = d.add(sr_m_plus_pow2i, tail_m);
        let add_smp_tn = d.add(sr_m_plus_pow2i, tail_n);
        let eq_m_final = d
            .chain(
                m,
                &[
                    (sr_m_succ_i_plus_tail_m, eq_m_decomp),
                    (add_smp_tm, congr_m_final),
                    (add_smp_tn, congr_m_tail),
                ],
            )
            .1;

        // Core inequality: Lt (add sr_n_i tail_n) (add sr_m_plus_pow2i tail_n).
        let eq_a_mod = d.lemma(p.sum_test_bit_lt, &[i, n]); // Eq sr_n_i (mod n pow2_i)
        let mod_n_pow2i = d.modulo(n, pow2_i);
        let pow2i_pos0 = d.zero_lt_succ(one); // Lt 0 (succ one) ~ Lt 0 two
        let pow2i_pos = d.lemma(p.pow_pos, &[two, i, pow2i_pos0]);
        let mod_lt_n = d.lemma(p.mod_lt, &[n, pow2_i, pow2i_pos]); // Lt mod_n_pow2i pow2_i
        let eq_a_mod_rev = d.symm(sr_n_i, mod_n_pow2i, eq_a_mod);
        let motive_a = d.eq_motive(mod_n_pow2i, &|d, x| d.lt(x, pow2_i));
        let a_lt_pow2i = d.transport(mod_n_pow2i, motive_a, mod_lt_n, sr_n_i, eq_a_mod_rev);

        let succ_a = d.succ(sr_n_i);
        let step_a = d.lemma(p.add_le_add_right, &[tail_n, succ_a, pow2_i, a_lt_pow2i]);

        let pow2i_plus_b = d.add(pow2_i, sr_m_i);
        let le_pow2i_add = d.lemma(p.le_add_right, &[pow2_i, sr_m_i]); // Le pow2_i pow2i_plus_b
        let add_comm_pow_b = d.lemma(p.add_comm, &[pow2_i, sr_m_i]);
        let motive_le = d.eq_motive(pow2i_plus_b, &|d, x| d.le(pow2_i, x));
        let le_pow2i_addbpow = d.transport(
            pow2i_plus_b,
            motive_le,
            le_pow2i_add,
            sr_m_plus_pow2i,
            add_comm_pow_b,
        );
        let step_b = d.lemma(
            p.add_le_add_right,
            &[tail_n, pow2_i, sr_m_plus_pow2i, le_pow2i_addbpow],
        );

        let add_succ_a_t = d.add(succ_a, tail_n);
        let add_pow2i_t = d.add(pow2_i, tail_n);
        let combined = d.lemma(
            p.le_trans,
            &[add_succ_a_t, add_pow2i_t, add_smp_tn, step_a, step_b],
        );

        let succ_add_at = d.lemma(p.succ_add, &[sr_n_i, tail_n]); // Eq add_succ_a_t (succ (add sr_n_i tail_n))
        let succ_add_a_t = d.succ(add_a_t);
        let motive_core = d.eq_motive(add_succ_a_t, &|d, x| d.le(x, add_smp_tn));
        let core_le = d.transport(
            add_succ_a_t,
            motive_core,
            combined,
            succ_add_a_t,
            succ_add_at,
        );
        // core_le : Le (succ add_a_t) add_smp_tn == Lt add_a_t add_smp_tn [def_eq]

        // Transport along eq_n_final, eq_m_final to get Lt n m.
        let eq_n_final_rev = d.symm(n, add_a_t, eq_n_final);
        let motive_n = d.eq_motive(add_a_t, &|d, x| d.lt(x, add_smp_tn));
        let step1 = d.transport(add_a_t, motive_n, core_le, n, eq_n_final_rev);

        let eq_m_final_rev = d.symm(m, add_smp_tn, eq_m_final);
        let motive_final = d.eq_motive(add_smp_tn, &|d, x| d.lt(n, x));
        let result = d.transport(add_smp_tn, motive_final, step1, m, eq_m_final_rev);

        let concl = d.lt(n, m);
        let stmt = {
            let with_hagree = d.arrow(hagree_ty, concl);
            let with_h1 = d.arrow(h1_ty, with_hagree);
            d.arrow(h0_ty, with_h1)
        };
        let proof = {
            let with_hagree = d.lam_fv(hagree_fv, hagree_ty, result);
            let with_h1 = d.lam_fv(h1_fv, h1_ty, with_hagree);
            d.lam_fv(h0_fv, h0_ty, with_h1)
        };
        (stmt, proof)
    })?;
    Ok(())
}

/// Everything this module declares, in dependency order.
pub(super) fn declare_bit_order_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_self_lt_two_pow(d, p)?;
    declare_self_lt_two_pow_add(d, p)?;
    declare_lt_of_test_bit(d, p)?;
    Ok(())
}
