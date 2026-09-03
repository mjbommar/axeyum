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
use super::helpers::{and_left, and_right, iff_forward};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `Eq (mul x (num 2)) (add x x)`. `mul x 2` reduces (`refl`, `mul_succ`
/// twice then `mul_zero`) to `add (add zero x) x`, NOT directly to
/// `add x x` -- `add` recurses on its SECOND argument, so `add zero x` does
/// not reduce for a symbolic `x`. `zero_add` closes exactly that gap; every
/// caller below only ever needs the RESULT type up to the kernel's own
/// `def_eq` (which sees straight through the `mul`/`pow_succ` unfolds), so
/// this is the one genuinely non-`refl` step in the whole "doubling" family.
/// Retired to the `simp` rewrite-chain producer (ADR-1586): `zero_add`
/// alone closes `Eq (add (add zero x) x) (add x x)`.
fn double_eq(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let zero = d.zero();
    let add_zero_x = d.add(zero, x);
    let lhs = d.add(add_zero_x, x);
    let rhs = d.add(x, x);
    let rules = crate::simp::nat::default_rules(p);
    crate::simp::nat::prove_eq(d, &rules, lhs, rhs)
        .unwrap_or_else(|e| panic!("double_eq: simp declined: {e:?}"))
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

/// `Nat.testBit_eq_zero_of_lt : ∀ n j, Lt n (pow 2 j) → Eq (testBit n j)
/// zero` — piece 2 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`
/// (`exists_most_significant_bit`'s "cheap half": above a value's own
/// magnitude bound every bit reads zero). See
/// `docs/plan/status/265-nat-msb-order.md` / `269-nat-msb-exists.md`.
///
/// Route: [`value_eq_sum_range`] at `bound := j` (directly from the
/// hypothesis) gives `sumRange f_n j = n`; the same helper at
/// `bound := succ j` needs `n < pow 2 (succ j)`, obtained from the
/// hypothesis via `pow_j <= pow_j + pow_j = mul pow_j 2`, which is
/// `pow 2 (succ j)` by `pow_succ`/`refl` (`le_add_right` +
/// [`double_eq`], the same bridge
/// [`declare_self_lt_two_pow_add`]'s step uses) composed with
/// `lt_of_lt_of_le`. `sum_range_succ` then forces
/// `n = add (sumRange f_n j) (f_n j) = add n (f_n j)` (substituting the
/// first equation), so `add_left_cancel` (against `n = add n 0`) collapses
/// `f_n j` to `0`; since `f_n j` is *literally* `mul (testBit n j) (pow 2
/// j)` (up to beta), `mul_eq_zero` splits into `testBit n j = 0` or
/// `pow 2 j = 0`, and the second is excluded by `pow_pos` +
/// `lt_irrefl`/`or_resolve_right`.
fn declare_test_bit_eq_zero_of_lt(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.test_bit_eq_zero_of_lt, 2, &|d, v| {
        let (n, j) = (v[0], v[1]);
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let succ_j = d.succ(j);
        let pow_j = d.pow(two, j);
        let pow_sj = d.pow(two, succ_j);

        let hyp_ty = d.lt(n, pow_j);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        // sum_j_eq_n : Eq (sumRange f_n j) n, directly from `hyp`.
        let f_n = bit_term_fn(d, &p, n);
        let sum_j = d.sum_range(f_n, j);
        let sum_j_eq_n = value_eq_sum_range(d, &p, n, j, hyp);

        // pow_j_le_pow_sj : Le pow_j (add pow_j pow_j), bridged up to
        // `mul pow_j 2` (== `pow 2 (succ j)` by refl) exactly as
        // `declare_self_lt_two_pow_add`'s step does.
        let le_add = d.lemma(p.le_add_right, &[pow_j, pow_j]);
        let double_pj = double_eq(d, &p, pow_j);
        let add_zero_pj = {
            let zero = d.zero();
            d.add(zero, pow_j)
        };
        let mul_pj_two = d.add(add_zero_pj, pow_j);
        let add_pj_pj = d.add(pow_j, pow_j);
        let rev = d.symm(mul_pj_two, add_pj_pj, double_pj);
        let motive_b = d.eq_motive(add_pj_pj, &|d, x| d.le(pow_j, x));
        let pow_j_le_mul = d.transport(add_pj_pj, motive_b, le_add, mul_pj_two, rev);

        // n_lt_sj : Lt n pow_sj, via lt_of_lt_of_le(n, pow_j, pow_sj, hyp,
        // pow_j_le_mul) -- `pow_j_le_mul`'s actual type ends in `mul_pj_two`,
        // def_eq to `pow_sj` by unfolding `pow`/`mul` twice, exactly as
        // `declare_self_lt_two_pow_add`'s own step relies on.
        let n_lt_sj = d.lemma(p.lt_of_lt_of_le, &[n, pow_j, pow_sj, hyp, pow_j_le_mul]);

        // sum_sj_eq_n : Eq (sumRange f_n succ_j) n.
        let sum_sj = d.sum_range(f_n, succ_j);
        let sum_sj_eq_n = value_eq_sum_range(d, &p, n, succ_j, n_lt_sj);

        // n = add sum_j (f_n j), via sum_range_succ then substituting
        // sum_j = n.
        let sr_succ_eq = d.lemma(p.sum_range_succ, &[f_n, j]); // Eq sum_sj (add sum_j (f_n j))
        let f_n_j = d.apply(f_n, &[j]);
        let add_sumj_fnj = d.add(sum_j, f_n_j);
        let n_eq_sum_sj = d.symm(sum_sj, n, sum_sj_eq_n);
        let (_e1, n_eq_add_sumj_fnj) =
            d.chain(n, &[(sum_sj, n_eq_sum_sj), (add_sumj_fnj, sr_succ_eq)]);

        let add_n_fnj = d.add(n, f_n_j);
        let congr_sumj = d.congr(sum_j, n, sum_j_eq_n, &|d, x| d.add(x, f_n_j));
        let (_e2, n_eq_add_n_fnj) = d.chain(
            n,
            &[(add_sumj_fnj, n_eq_add_sumj_fnj), (add_n_fnj, congr_sumj)],
        );

        // add_n_zero_eq_add_n_fnj : Eq (add n zero) (add n (f_n j)).
        let add_n_zero = d.add(n, zero);
        let add_zero_eq = d.lemma(p.add_zero, &[n]); // Eq add_n_zero n
        let (_e3, add_n_zero_eq_add_n_fnj) =
            d.chain(add_n_zero, &[(n, add_zero_eq), (add_n_fnj, n_eq_add_n_fnj)]);

        // zero_eq_fnj : Eq zero (f_n j), via add_left_cancel.
        let zero_eq_fnj = d.lemma(
            p.add_left_cancel,
            &[n, zero, f_n_j, add_n_zero_eq_add_n_fnj],
        );
        let fnj_eq_zero = d.symm(zero, f_n_j, zero_eq_fnj);

        // mul_eq_zero_h : Or (Eq (testBit n j) zero) (Eq pow_j zero) --
        // `fnj_eq_zero`'s actual type is `Eq (f_n j) zero`, def_eq to
        // `Eq (mul (testBit n j) pow_j) zero` by beta (`f_n j` unfolds to
        // exactly that `mul` application).
        let tb_n_j = d.const_app(p.test_bit, &[n, j]);
        let mul_eq_zero_h = d.lemma(p.mul_eq_zero, &[tb_n_j, pow_j, fnj_eq_zero]);

        // not_pow_j_zero : arrow (Eq pow_j zero) False, from `pow_pos` and
        // `lt_irrefl` (transport `Lt zero pow_j` along an assumed
        // `Eq pow_j zero` to `Lt zero zero`, then apply `lt_irrefl zero`).
        let zero_lt_two = d.zero_lt_succ(one); // Lt 0 (succ 1) ~ Lt 0 two
        let pow_j_pos = d.lemma(p.pow_pos, &[two, j, zero_lt_two]); // Lt zero pow_j
        let not_pow_j_zero = {
            let heq_ty = d.eq(pow_j, zero);
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let motive_z = d.eq_motive(pow_j, &|d, x| {
                let zero = d.zero();
                d.lt(zero, x)
            });
            let lt_zero_zero = d.transport(pow_j, motive_z, pow_j_pos, zero, heq);
            let no_loop = d.lemma(p.lt_irrefl, &[zero]);
            let absurd = d.apply(no_loop, &[lt_zero_zero]);
            d.lam_fv(heq_fv, heq_ty, absurd)
        };

        let eq_tb_zero = d.eq(tb_n_j, zero);
        let eq_pow_j_zero = d.eq(pow_j, zero);
        let result = d.const_app(
            p.logic.or_resolve_right,
            &[eq_tb_zero, eq_pow_j_zero, mul_eq_zero_h, not_pow_j_zero],
        );

        let stmt = d.arrow(hyp_ty, eq_tb_zero);
        let proof = d.lam_fv(hyp_fv, hyp_ty, result);
        (stmt, proof)
    })?;
    Ok(())
}

/// `False.rec (fun _ => target) false_proof : target` -- duplicated from
/// `order_more.rs`'s private `ex_falso` (off-limits to edit; five lines,
/// identical).
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `Eq (mul x (num 2)) (add x x)` bridge, but for the OPPOSITE direction the
/// `size` proof needs at half's positivity: `Lt zero n -> Lt n (mul two n)`
/// -- duplicated from `binary.rs`'s private `n_lt_mul_two` (off-limits to
/// edit; the third private copy of this helper in this prelude, matching
/// `powsq.rs`/`rec_agreement.rs`'s own duplicates rather than promoting it,
/// consistent with this codebase's existing convention for a ~20-line
/// helper reused by three unrelated proofs).
fn n_lt_mul_two(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, pos: ExprId) -> ExprId {
    // Retired to the `tactic` combinator (ADR-1589): `simp`'s default rules
    // rewrite `mul 2 n` to `add n n` (`succ_mul` twice, `zero_mul`,
    // `zero_add`), then `linarith` closes `Lt n (add n n)` from `pos : Lt
    // zero n` directly (`linarith::nat` also recognizes a literal-numeral
    // `mul` on its own -- this retirement keeps `Then(Simp, Linarith)`
    // because that is the hand proof's own shape, a rewrite step then an
    // order step, not because `Linarith` alone cannot reach it here).
    let p = *p;
    let zero = d.zero();
    let two = d.num(2);
    let mul_two_n = d.mul(two, n);
    let goal = d.lt(n, mul_two_n);
    let pos_ty = d.lt(zero, n);
    let assumptions = [(pos_ty, pos)];
    let rules = crate::simp::nat::default_rules(&p);
    let ctx = crate::tactic::Ctx {
        prelude: p,
        assumptions: &assumptions,
        rules: &rules,
    };
    let tactic = crate::tactic::Tactic::Then(
        Box::new(crate::tactic::Tactic::Simp),
        Box::new(crate::tactic::Tactic::Linarith),
    );
    crate::tactic::run(d, &ctx, &tactic, goal)
        .unwrap_or_else(|e| panic!("n_lt_mul_two: Then(Simp, Linarith) declined: {e:?}"))
}

/// `fun i => And (Eq (testBit n i) one) (∀ j, Lt i j → Eq (testBit n j)
/// zero)` -- the `exists_most_significant_bit` predicate at a fixed `n`.
fn msb_predicate(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let one = d.num(1);
    let zero = d.zero();
    let tb_i = d.const_app(p.test_bit, &[n, i]);
    let a = d.eq(tb_i, one);
    let b = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let lt_i_j = d.lt(i, j);
        let tb_j = d.const_app(p.test_bit, &[n, j]);
        let eq_j = d.eq(tb_j, zero);
        let body = d.arrow(lt_i_j, eq_j);
        d.pi_fv(j_fv, nat, body)
    };
    let and_ty = d.const_app(p.logic.and, &[a, b]);
    d.lam_fv(i_fv, nat, and_ty)
}

/// `Exists (msb_predicate n)`.
fn msb_exists_ty(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let predicate = msb_predicate(d, &p, n);
    let one_lvl = d.level_one();
    let exists_c = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
    d.apply(exists_c, &[nat, predicate])
}

/// `exists_intro (msb_predicate n) witness (and_intro proof_one proof_upper)
/// : Exists (msb_predicate n)`.
fn msb_intro(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    witness: ExprId,
    proof_one: ExprId,
    proof_upper: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.num(1);
    let zero = d.zero();
    let tb_w = d.const_app(p.test_bit, &[n, witness]);
    let a_ty = d.eq(tb_w, one);
    let b_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let lt_w_j = d.lt(witness, j);
        let tb_j = d.const_app(p.test_bit, &[n, j]);
        let eq_j = d.eq(tb_j, zero);
        let body = d.arrow(lt_w_j, eq_j);
        d.pi_fv(j_fv, nat, body)
    };
    let and_proof = d.const_app(p.logic.and_intro, &[a_ty, b_ty, proof_one, proof_upper]);
    let predicate = msb_predicate(d, &p, n);
    let one_lvl = d.level_one();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
    d.apply(intro, &[nat, predicate, witness, and_proof])
}

/// `Nat.msb_exists_of_le_fuel : ∀ fuel n, Le n fuel → Not (Eq n zero) →
/// Exists (msb_predicate n)` -- the hard half of
/// `Nat.exists_most_significant_bit` (piece 2 of 4 toward
/// `F:ml430-nat-lt-xor-cases-c43a1e85`; see
/// `docs/plan/status/269-nat-msb-exists.md` for the "every bit above is
/// zero" cheap half already landed as `Nat.testBit_eq_zero_of_lt`, and
/// `docs/plan/status/265-nat-msb-order.md`/`docs/plan/status/271-nat-msb-hard.md`
/// for why `Nat.size` does NOT shortcut this: `size`'s own development
/// ([`NatPrelude::size_aux_lt_pow`], `binary.rs`) only ever proves an UPPER
/// bound (`n < 2^(size n)`), never the LOWER bound this needs, and has no
/// existing lemma relating `size n` to `size (n/2)`.
///
/// SAME fuel/half-recursion shape as `binary.rs`'s
/// `declare_size_aux_lt_pow` (off-limits to edit but read for the pattern):
/// induction on `fuel` generalized over `n`, splitting the step on
/// `beq half zero` (NOT `beq n zero` -- the recursion bottoms out when
/// `n`'s upper half vanishes, mirroring Mathlib's own `Nat.binaryRec` case
/// split read at the pinned v4.30 source
/// `Mathlib/Data/Nat/Bitwise.lean:176`, `by_cases h' : n = 0` on the
/// binary-recursion "rest").
///
/// The move that makes this tractable: `testBit n (succ i) ≡ testBit
/// (div n 2) i` is `refl` ([`NatPrelude::test_bit_succ`]'s own proof is
/// `d.refl`), so a proof about bit `i'` of `half := div n 2` is ALREADY,
/// with zero rewriting, a proof about bit `succ i'` of `n` -- the kernel's
/// `def_eq` check sees straight through it, for ANY value of `half`
/// (whether or not `half = 0` holds). Only the UNIVERSALLY QUANTIFIED
/// "every higher bit is zero" half needs an explicit rewrite, because
/// there the bit index `j` is an arbitrary bound variable, not
/// syntactically `succ`-shaped: `succ_pred_of_pos` turns `Lt zero j` into
/// `j = succ (pred j)`, and transporting along that equation is the one
/// genuinely new piece of machinery (inlined in both branches below rather
/// than factored out, since the two branches supply the "zero at half"
/// premise differently).
///
/// - **Base (`fuel=0`)**: `Le n 0` and `Not (Eq n 0)` are jointly
///   contradictory (`succ_pred_of_pos` turns the positivity into
///   `n = succ (pred n)`, transported into the bound gives
///   `Le (succ (pred n)) 0`, refuted by `not_succ_le_zero`).
/// - **Step (`fuel=succ f`)**, split on `beq half zero`:
///   - **`half = 0`** (so `n < 2`, `n != 0` forces `n = 1`, via the
///     `div_mod_exec` reconstruction `n = 2*half + (n mod 2)` collapsing to
///     `n = n mod 2 < 2`, then `le_antisymm` against `n`'s own positivity):
///     witness `0`; bit `0` is `1` via `test_bit_zero`/`mod_eq_self_of_lt`;
///     every `j > 0` bit is `0` via `test_bit_of_zero` transported along
///     `half = 0` then along `j = succ (pred j)`.
///   - **`half != 0`**: `half <= f` from `half < n <= succ f`
///     (`div_mod_lt_mul_iff` + [`n_lt_mul_two`], the SAME bound
///     `declare_size_aux_lt_pow`'s own step uses); the IH at `half`
///     supplies `i'`, and the witness is `succ i'` -- bit `succ i'` is `1`
///     by the `refl` bridge above (no rewriting at all), and every
///     `j > succ i'` bit is `0` via the IH's upper half applied at
///     `pred j` (justified by `Lt i' (pred j)`, obtained by transporting
///     the outer hypothesis along `j = succ (pred j)` and peeling one
///     `succ` with `le_of_succ_le_succ`) then transported along
///     `j = succ (pred j)` the same way.
fn declare_msb_exists_of_le_fuel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    let ne_ty_at = |d: &mut NatDev<'_>, n: ExprId| -> ExprId {
        let zero = d.zero();
        let eq_ty = d.eq(n, zero);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        d.arrow(eq_ty, false_ty)
    };

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let bound_ty = d.le(n, x);
        let ne_ty = ne_ty_at(d, n);
        let concl = msb_exists_ty(d, &p, n);
        let body = d.arrow(ne_ty, concl);
        let with_bound = d.arrow(bound_ty, body);
        d.pi_fv(n_fv, nat, with_bound)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let zero = d.zero();
        let bound_ty = d.le(n, zero);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let ne_ty = ne_ty_at(d, n);
        let ne_fv = d.fresh_fvar();
        let hne = d.kernel().fvar(ne_fv);

        // n = succ (pred n), from positivity via hne; transported into
        // `bound` this contradicts `not_succ_le_zero`.
        let pos = d.lemma(p.zero_lt_of_ne_zero, &[n, hne]);
        let eq_n_succ_pred = d.lemma(p.succ_pred_of_pos, &[n, pos]);
        let pred_n = d.pred(n);
        let succ_pred_n = d.succ(pred_n);
        let motive_b = d.eq_motive(n, &|d, x| {
            let zero = d.zero();
            d.le(x, zero)
        });
        let bound_transported = d.transport(n, motive_b, bound, succ_pred_n, eq_n_succ_pred);
        let contra = d.lemma(p.not_succ_le_zero, &[pred_n, bound_transported]);

        let target = msb_exists_ty(d, &p, n);
        let absurd = ex_falso(d, &p, target, contra);

        let with_ne = d.lam_fv(ne_fv, ne_ty, absurd);
        let with_bound = d.lam_fv(bound_fv, bound_ty, with_ne);
        d.lam_fv(n_fv, nat, with_bound)
    };

    let step = |d: &mut NatDev<'_>, f: ExprId, ih: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sf = d.succ(f);
        let bound_ty = d.le(n, sf);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let ne_ty = ne_ty_at(d, n);
        let ne_fv = d.fresh_fvar();
        let hne = d.kernel().fvar(ne_fv);

        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let half = d.div(n, two);
        let condition = d.beq(half, zero);
        let false_value = d.bool_false();
        let true_value = d.bool_true();
        let target_ty = msb_exists_ty(d, &p, n);

        let branch_for = |d: &mut NatDev<'_>, selector: ExprId| {
            let equality = d.bool_eq(condition, selector);
            d.arrow(equality, target_ty)
        };

        // beq half 0 = false -> half != 0 -> half <= f (same bound
        // `declare_size_aux_lt_pow`'s own step uses) -> IH at half,
        // eliminated to build the target at `n` via witness `succ i'`.
        let false_minor = {
            let false_equality_ty = d.bool_eq(condition, false_value);
            let false_equality_fv = d.fresh_fvar();
            let false_equality = d.kernel().fvar(false_equality_fv);

            let ne_half_zero = d.lemma(p.ne_of_beq_eq_false, &[half, zero, false_equality]);

            let pos = d.lemma(p.zero_lt_of_ne_zero, &[n, hne]);
            let h_exec = d.lemma(p.div_mod_exec, &[one, n]);
            let r1 = d.modulo(n, two);
            let iff_fn = d.lemma(p.div_mod_lt_mul_iff, &[two, n, half, r1, n]);
            let the_iff = d.apply(iff_fn, &[h_exec]);
            let mul_two_n = d.mul(two, n);
            let lt_n_2n_ty = d.lt(n, mul_two_n);
            let lt_half_n_ty = d.lt(half, n);
            let forward = iff_forward(d, lt_n_2n_ty, lt_half_n_ty, the_iff);
            let n_lt_2n = n_lt_mul_two(d, &p, n, pos);
            let half_lt_n = d.apply(forward, &[n_lt_2n]);

            let half_lt_sf = d.lemma(p.lt_of_lt_of_le, &[half, n, sf, half_lt_n, bound]);
            let half_le_f = d.lemma(p.le_of_succ_le_succ, &[half, f, half_lt_sf]);

            let ih_half = d.apply(ih, &[half]);
            let ih_half2 = d.apply(ih_half, &[half_le_f]);
            let ih_result = d.apply(ih_half2, &[ne_half_zero]);
            // ih_result : Exists (msb_predicate half)

            let source_ty = msb_exists_ty(d, &p, half);
            let anon = d.anon_name();
            let elim_motive = d
                .kernel()
                .lam(anon, source_ty, target_ty, BinderInfo::Default);

            let minor = {
                let i_fv = d.fresh_fvar();
                let i_p = d.kernel().fvar(i_fv);
                let hand_fv = d.fresh_fvar();
                let hand = d.kernel().fvar(hand_fv);
                let a_ty = {
                    let one2 = d.num(1);
                    let tb = d.const_app(p.test_bit, &[half, i_p]);
                    d.eq(tb, one2)
                };
                let b_ty = {
                    let jp_fv = d.fresh_fvar();
                    let jp = d.kernel().fvar(jp_fv);
                    let lt_i_jp = d.lt(i_p, jp);
                    let tb = d.const_app(p.test_bit, &[half, jp]);
                    let zero2 = d.zero();
                    let eq_j = d.eq(tb, zero2);
                    let body = d.arrow(lt_i_jp, eq_j);
                    d.pi_fv(jp_fv, nat, body)
                };
                let hand_ty = d.const_app(p.logic.and, &[a_ty, b_ty]);
                let hi = and_left(d, a_ty, b_ty, hand);
                let hi_upper = and_right(d, a_ty, b_ty, hand);

                let succ_i = d.succ(i_p);
                // proof_one : Eq (testBit half i_p) one -- defeq
                // Eq (testBit n succ_i) one, no wrapping needed.
                let proof_one = hi;

                let proof_upper = {
                    let j_fv = d.fresh_fvar();
                    let j = d.kernel().fvar(j_fv);
                    let hj_fv = d.fresh_fvar();
                    let hj = d.kernel().fvar(hj_fv);
                    let hj_ty = d.lt(succ_i, j);

                    let zero_le_succ_i = d.lemma(p.zero_le, &[succ_i]);
                    let lt_zero_j =
                        d.lemma(p.lt_of_le_of_lt, &[zero, succ_i, j, zero_le_succ_i, hj]);

                    let eq_j_succ_jp = d.lemma(p.succ_pred_of_pos, &[j, lt_zero_j]);
                    let jp = d.pred(j);
                    let succ_jp = d.succ(jp);

                    let motive_shift = d.eq_motive(j, &|d, x| d.lt(succ_i, x));
                    let h_shifted = d.transport(j, motive_shift, hj, succ_jp, eq_j_succ_jp);
                    // h_shifted : Lt succ_i succ_jp = Le (succ succ_i) succ_jp
                    let lt_i_jp = d.lemma(p.le_of_succ_le_succ, &[succ_i, jp, h_shifted]);
                    // lt_i_jp : Le succ_i jp == Lt i_p jp [def_eq]

                    let zero_at_half = d.apply(hi_upper, &[jp, lt_i_jp]);
                    // zero_at_half : Eq (testBit half jp) zero -- defeq
                    // Eq (testBit n succ_jp) zero, no wrapping needed.

                    let eq_succ_jp_j = d.symm(j, succ_jp, eq_j_succ_jp);
                    let motive_final = d.eq_motive(succ_jp, &|d, x| {
                        let tb = d.const_app(p.test_bit, &[n, x]);
                        let zero3 = d.zero();
                        d.eq(tb, zero3)
                    });
                    let result = d.transport(succ_jp, motive_final, zero_at_half, j, eq_succ_jp_j);
                    let with_hj = d.lam_fv(hj_fv, hj_ty, result);
                    d.lam_fv(j_fv, nat, with_hj)
                };

                let and_proof_n = msb_intro(d, &p, n, succ_i, proof_one, proof_upper);
                let with_hand = d.lam_fv(hand_fv, hand_ty, and_proof_n);
                d.lam_fv(i_fv, nat, with_hand)
            };

            let level_one = d.level_one();
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
            let half_predicate = msb_predicate(d, &p, half);
            let step_result = d.apply(
                exists_rec,
                &[nat, half_predicate, elim_motive, minor, ih_result],
            );

            d.lam_fv(false_equality_fv, false_equality_ty, step_result)
        };

        // beq half 0 = true -> half = 0 -> n < 2 -> (with n != 0) n = 1 ->
        // witness 0.
        let true_minor = {
            let true_equality_ty = d.bool_eq(condition, true_value);
            let true_equality_fv = d.fresh_fvar();
            let true_equality = d.kernel().fvar(true_equality_fv);

            let eq_half_zero = d.lemma(p.eq_of_beq_eq_true, &[half, zero, true_equality]);

            let h_exec = d.lemma(p.div_mod_exec, &[one, n]);
            let r1 = d.modulo(n, two);
            let mul_two_half = d.mul(two, half);
            let recon = d.add(mul_two_half, r1);
            let eq_ty = d.eq(n, recon);
            let bound_r_ty = d.lt(r1, two);
            let eq_n_recon = and_left(d, eq_ty, bound_r_ty, h_exec);
            let r1_lt_two = and_right(d, eq_ty, bound_r_ty, h_exec);

            let mul_two_zero = d.mul(two, zero);
            let congr_half = d.congr(half, zero, eq_half_zero, &|d, x| d.mul(two, x));
            let mul_zero_eq = d.lemma(p.mul_zero, &[two]);
            let mul_half_eq_zero = d
                .chain(
                    mul_two_half,
                    &[(mul_two_zero, congr_half), (zero, mul_zero_eq)],
                )
                .1;

            let congr_recon = d.congr(mul_two_half, zero, mul_half_eq_zero, &|d, x| d.add(x, r1));
            let add_zero_r1 = d.add(zero, r1);
            let zero_add_r1 = d.lemma(p.zero_add, &[r1]);
            let eq_n_r1 = d
                .chain(
                    n,
                    &[
                        (recon, eq_n_recon),
                        (add_zero_r1, congr_recon),
                        (r1, zero_add_r1),
                    ],
                )
                .1;

            let eq_r1_n = d.symm(n, r1, eq_n_r1);
            let motive_nt = d.eq_motive(r1, &|d, x| {
                let two = d.num(2);
                d.lt(x, two)
            });
            let n_lt_two = d.transport(r1, motive_nt, r1_lt_two, n, eq_r1_n);

            let tb0 = d.const_app(p.test_bit, &[n, zero]);
            let mod_n_two = d.modulo(n, two);
            let tb0_eq_mod = d.lemma(p.test_bit_zero, &[n]);
            let mod_eq_n = d.lemma(p.mod_eq_self_of_lt, &[n, two, n_lt_two]);
            let tb0_eq_n = d.chain(tb0, &[(mod_n_two, tb0_eq_mod), (n, mod_eq_n)]).1;

            let le_n_one = d.lemma(p.le_of_succ_le_succ, &[n, one, n_lt_two]);
            let lt_zero_n = d.lemma(p.zero_lt_of_ne_zero, &[n, hne]);
            let n_eq_one = d.lemma(p.le_antisymm, &[n, one, le_n_one, lt_zero_n]);
            let tb0_eq_one = d.chain(tb0, &[(n, tb0_eq_n), (one, n_eq_one)]).1;

            let proof_upper = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let hj_fv = d.fresh_fvar();
                let hj = d.kernel().fvar(hj_fv);
                let hj_ty = d.lt(zero, j);

                let eq_j_succ_jp = d.lemma(p.succ_pred_of_pos, &[j, hj]);
                let jp = d.pred(j);
                let succ_jp = d.succ(jp);

                let tb_half_jp = d.const_app(p.test_bit, &[half, jp]);
                let tb_zero_jp = d.const_app(p.test_bit, &[zero, jp]);
                let congr_tb = d.congr(half, zero, eq_half_zero, &|d, x| {
                    d.const_app(p.test_bit, &[x, jp])
                });
                let test_bit_of_zero_jp = d.lemma(p.test_bit_of_zero, &[jp]);
                let zero_at_half = d
                    .chain(
                        tb_half_jp,
                        &[(tb_zero_jp, congr_tb), (zero, test_bit_of_zero_jp)],
                    )
                    .1;
                // zero_at_half : Eq (testBit half jp) zero -- defeq
                // Eq (testBit n succ_jp) zero, no wrapping needed.

                let eq_succ_jp_j = d.symm(j, succ_jp, eq_j_succ_jp);
                let motive_final = d.eq_motive(succ_jp, &|d, x| {
                    let tb = d.const_app(p.test_bit, &[n, x]);
                    let zero2 = d.zero();
                    d.eq(tb, zero2)
                });
                let result = d.transport(succ_jp, motive_final, zero_at_half, j, eq_succ_jp_j);
                let with_hj = d.lam_fv(hj_fv, hj_ty, result);
                d.lam_fv(j_fv, nat, with_hj)
            };

            let and_proof_n = msb_intro(d, &p, n, zero, tb0_eq_one, proof_upper);
            d.lam_fv(true_equality_fv, true_equality_ty, and_proof_n)
        };

        let motive_bool = {
            let selector_fv = d.fresh_fvar();
            let selector = d.kernel().fvar(selector_fv);
            let body = branch_for(d, selector);
            d.lam_fv(selector_fv, bool_ty, body)
        };
        let level_zero = d.kernel().level_zero();
        let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
        let selected = d.apply(bool_rec, &[motive_bool, false_minor, true_minor, condition]);
        let condition_refl = d.bool_refl(condition);
        let step_result_final = d.apply(selected, &[condition_refl]);

        let with_ne = d.lam_fv(ne_fv, ne_ty, step_result_final);
        let with_bound = d.lam_fv(bound_fv, bound_ty, with_ne);
        d.lam_fv(n_fv, nat, with_bound)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof_fn = d.induct(&motive, &base, &step, fuel);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof = d.apply(proof_fn, &[n]);
    let stmt = {
        let bound_ty = d.le(n, fuel);
        let ne_ty = ne_ty_at(d, n);
        let concl = msb_exists_ty(d, &p, n);
        let with_ne = d.arrow(ne_ty, concl);
        d.arrow(bound_ty, with_ne)
    };
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(fuel_fv, nat, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(fuel_fv, nat, over_n)
    };
    d.declare_theorem(p.msb_exists_of_le_fuel, ty, value)
}

/// `Nat.exists_most_significant_bit : ∀ n, Not (Eq n zero) →
/// Exists (msb_predicate n)` -- the `fuel := n` instance of
/// [`declare_msb_exists_of_le_fuel`], via `le_refl`. Nat-valued (Mathlib's
/// `testBit` is `Bool`-valued, read at the pinned v4.30 source
/// `Mathlib/Data/Nat/Bitwise.lean:176`), so this is a local fact
/// (`F:nat-exists-most-significant-bit`), matching the
/// `F:nat-testbit-eq-zero-of-lt`/`F:nat-lt-of-testbit` precedent.
fn declare_exists_most_significant_bit(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.exists_most_significant_bit, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let eq_ty = d.eq(n, zero);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let ne_ty = d.arrow(eq_ty, false_ty);
        let ne_fv = d.fresh_fvar();
        let hne = d.kernel().fvar(ne_fv);

        let le_refl_n = d.lemma(p.le_refl, &[n]);
        let result = d.lemma(p.msb_exists_of_le_fuel, &[n, n, le_refl_n, hne]);

        let concl = msb_exists_ty(d, &p, n);
        let stmt = d.arrow(ne_ty, concl);
        let proof = d.lam_fv(ne_fv, ne_ty, result);
        (stmt, proof)
    })?;
    Ok(())
}

/// Everything this module declares, in dependency order.
pub(super) fn declare_bit_order_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_self_lt_two_pow(d, p)?;
    declare_self_lt_two_pow_add(d, p)?;
    declare_lt_of_test_bit(d, p)?;
    declare_test_bit_eq_zero_of_lt(d, p)?;
    declare_msb_exists_of_le_fuel(d, p)?;
    declare_exists_most_significant_bit(d, p)?;
    Ok(())
}
