//! Binary representation: `Nat.testBit` and the digit-sum decomposition
//! `Nat.sum_testBit_lt` — the foundation a computer-science reading of `Nat`
//! has been missing.
//!
//! `Nat.div`/`Nat.mod` in this kernel recurse STRUCTURALLY on the dividend
//! (see `division.rs`'s `declare_executable_division_spec`), not by
//! well-founded recursion on `n/2`. `testBit`, though, genuinely wants to
//! recurse on `n/2` (each bit index shifts the number right one place), and
//! that recursion is on a value that does not get syntactically smaller by
//! one constructor — the textbook well-founded-recursion trap. The FUEL route
//! sidesteps it: `testBitAux` recurses structurally on the bit INDEX `i`
//! (which genuinely does decrease by one constructor per step), carrying `n`
//! through as an ordinary parameter that gets replaced by `n/2` in the
//! function VALUE at each step — the same shape `pred`/`sum_range`/`factorial`
//! already use (`Nat.rec` with a non-`Prop` motive), just with the motive
//! `Nat -> Nat` instead of `Nat`.
//!
//! The real content is [`declare_sum_test_bit_lt`]: the low `k` bits of `n`,
//! read back as a number, equal `n mod 2^k`. Its induction has to match
//! `testBit`'s own recursive shift (`testBit n (succ i) ≡ testBit (n/2) i`),
//! so it front-peels the sum (`sum_range_shift_front`, already proved in
//! `binomial.rs`) rather than back-peeling it (`sum_range_succ`), and
//! generalizes over `n` while inducting on `k` — the standard "the recursive
//! step changes the OTHER variable" move. The one genuinely new piece of
//! arithmetic this needs, [`declare_mod_two_mul_split`], is proved by
//! constructing two `divMod` witnesses for the same `(n, m*2)` and comparing
//! them with `div_mod_unique` — it is not specific to `testBit` at all.

use super::NatPrelude;
use super::finite::pos_implies_succ_pred;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `divMod m dividend (div dividend m) (mod dividend m)`, for any `m` known
/// only to be positive (not necessarily a literal `succ` of something), via
/// [`pos_implies_succ_pred`] and one transport back from `succ (pred m)`.
fn div_mod_positive(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    dividend: ExprId,
    m: ExprId,
    pos: ExprId,
) -> ExprId {
    let pm = d.pred(m);
    let spm = d.succ(pm);
    let succ_pred_fn = pos_implies_succ_pred(d, p, m);
    let eq_m_spm = d.apply(succ_pred_fn, &[pos]);
    let h_spm = d.lemma(p.div_mod_exec, &[pm, dividend]);
    let eq_spm_m = d.symm(m, spm, eq_m_spm);
    let motive = d.eq_motive(spm, &|d, x| {
        let dv = d.div(dividend, x);
        let md = d.modulo(dividend, x);
        d.div_mod(x, dividend, dv, md)
    });
    d.transport(spm, motive, h_spm, m, eq_spm_m)
}

/// `Le 1 (pow 2 k)`, by induction on `k` via `Nat.one_le_mul`.
fn pow_two_pos(d: &mut NatDev<'_>, p: &NatPrelude, k: ExprId) -> ExprId {
    let p = *p;
    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let two = d.num(2);
        let one = d.num(1);
        let px = d.pow(two, x);
        d.le(one, px)
    };
    d.induct(
        &motive,
        &|d| {
            let one = d.num(1);
            d.lemma(p.le_refl, &[one])
        },
        &|d, j, ih| {
            let one = d.num(1);
            let two = d.num(2);
            let le1_two = {
                let zero = d.zero();
                let zle1 = d.lemma(p.zero_le, &[one]);
                d.lemma(p.le_succ_succ, &[zero, one, zle1])
            };
            let pow_two_j = d.pow(two, j);
            d.lemma(p.one_le_mul, &[pow_two_j, two, ih, le1_two])
        },
        k,
    )
}

/// `testBitAux`, `testBit`, and their two defining (refl) equations.
fn declare_test_bit_defs(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let fn_ty = d.arrow(nat, nat);

    // testBitAux 0 n ≡ mod n 2 ; testBitAux (succ i) n ≡ testBitAux i (div n 2)
    {
        let base_term = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let two = d.num(2);
            let body = d.modulo(n, two);
            d.lam_fv(n_fv, nat, body)
        };
        let step_term = {
            let j_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let two = d.num(2);
            let half = d.div(n, two);
            let applied = d.apply(ih, &[half]);
            let inner = d.lam_fv(n_fv, nat, applied);
            let with_ih = d.lam_fv(ih_fv, fn_ty, inner);
            d.lam_fv(j_fv, nat, with_ih)
        };
        let motive = d.kernel().lam(anon, nat, fn_ty, BinderInfo::Default);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let one = d.level_one();
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, base_term, step_term, i]);
        let value = d.lam_fv(i_fv, nat, body);
        let ty = d.arrow(nat, fn_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.test_bit_aux,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // testBit n i := testBitAux i n
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let applied = d.const_app(p.test_bit_aux, &[i, n]);
        let with_i = d.lam_fv(i_fv, nat, applied);
        let value = d.lam_fv(n_fv, nat, with_i);
        let ty = d.arrow(nat, fn_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.test_bit,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    // testBit_zero : ∀ n, testBit n 0 = mod n 2   (refl)
    d.theorem(p.test_bit_zero, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let lhs = d.const_app(p.test_bit, &[n, zero]);
        let two = d.num(2);
        let rhs = d.modulo(n, two);
        (d.eq(lhs, rhs), d.refl(rhs))
    })?;

    // testBit_succ : ∀ n i, testBit n (succ i) = testBit (div n 2) i   (refl)
    d.theorem(p.test_bit_succ, 2, &|d, v| {
        let (n, i) = (v[0], v[1]);
        let si = d.succ(i);
        let lhs = d.const_app(p.test_bit, &[n, si]);
        let two = d.num(2);
        let half = d.div(n, two);
        let rhs = d.const_app(p.test_bit, &[half, i]);
        (d.eq(lhs, rhs), d.refl(rhs))
    })?;

    Ok(())
}

/// `testBit_le_one : ∀ n i, Le (testBit n i) 1` — induction on `i`,
/// generalizing over `n` (the recursive step needs the hypothesis at `n/2`,
/// not at `n`), using `testBit n (succ i) ≡ testBit (n/2) i` by refl to close
/// the step with the generalized hypothesis applied to `n/2` directly — no
/// rewriting needed.
fn declare_test_bit_le_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let tb = d.const_app(p.test_bit, &[n, x]);
        let one = d.num(1);
        let body = d.le(tb, one);
        d.pi_fv(n_fv, nat, body)
    };
    let base = |d: &mut NatDev<'_>| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let one = d.num(1);
        let two = d.num(2);
        let zero_lt_two = d.zero_lt_succ(one);
        let r = d.modulo(n, two);
        let bound = d.lemma(p.mod_lt, &[n, two, zero_lt_two]);
        let le_r1 = d.lemma(p.le_of_succ_le_succ, &[r, one, bound]);
        d.lam_fv(n_fv, nat, le_r1)
    };
    let step = |d: &mut NatDev<'_>, _j: ExprId, ih: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let two = d.num(2);
        let half = d.div(n, two);
        let applied = d.apply(ih, &[half]);
        d.lam_fv(n_fv, nat, applied)
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let proof_fn = d.induct(&motive, &base, &step, i);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof = d.apply(proof_fn, &[n]);
    let stmt = {
        let tb = d.const_app(p.test_bit, &[n, i]);
        let one = d.num(1);
        d.le(tb, one)
    };
    let ty = {
        let over_i = d.pi_fv(i_fv, nat, stmt);
        d.pi_fv(n_fv, nat, over_i)
    };
    let value = {
        let over_i = d.lam_fv(i_fv, nat, proof);
        d.lam_fv(n_fv, nat, over_i)
    };
    d.declare_theorem(p.test_bit_le_one, ty, value)
}

/// `mod_two_mul_split : ∀ n m, Lt 0 m →
/// add (mul 2 (mod (div n 2) m)) (mod n 2) = mod n (mul m 2)`.
///
/// Two `divMod` witnesses for `(n, mul m 2)`: the executable one
/// (`div_mod_positive`), and a hand-built one whose remainder is exactly the
/// stated left-hand side — reconstructed by substituting the `divMod 2 n ...`
/// and `divMod m (n/2) ...` equations into each other and re-associating, and
/// bounded by chaining `mod`'s own bound at each divisor. `div_mod_unique`
/// then forces the two remainders equal.
fn declare_mod_two_mul_split(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_two_mul_split, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let zero = d.zero();
        let two = d.num(2);
        let one = d.num(1);

        let pos_ty = d.lt(zero, m);
        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);

        let half = d.div(n, two);
        let r2 = d.modulo(half, m);
        let r1 = d.modulo(n, two);
        let two_r2 = d.mul(two, r2);
        let r3 = d.add(two_r2, r1);
        let divisor = d.mul(m, two);
        let rhs = d.modulo(n, divisor);
        let target = d.eq(r3, rhs);

        // h1 : divMod 2 n half r1
        let h1 = d.lemma(p.div_mod_exec, &[one, n]);
        let mul_two_half = d.mul(two, half);
        let recon1 = d.add(mul_two_half, r1);
        let eq1_ty = d.eq(n, recon1);
        let bound1_ty = d.lt(r1, two);
        let eq1 = and_left(d, eq1_ty, bound1_ty, h1);
        let bound1 = and_right(d, eq1_ty, bound1_ty, h1);

        // h2 : divMod m half q2 r2
        let h2 = div_mod_positive(d, &p, half, m, pos);
        let q2 = d.div(half, m);
        let mul_m_q2 = d.mul(m, q2);
        let recon2 = d.add(mul_m_q2, r2);
        let eq2_ty = d.eq(half, recon2);
        let bound2_ty = d.lt(r2, m);
        let eq2 = and_left(d, eq2_ty, bound2_ty, h2);
        let bound2 = and_right(d, eq2_ty, bound2_ty, h2);

        // ---- equation: n = mul (mul m 2) q2 + r3 -----------------------
        let mul_two_recon2 = d.mul(two, recon2);
        let s_b = d.add(mul_two_recon2, r1);
        let h_b = d.congr(half, recon2, eq2, &|d, x| {
            let mx = d.mul(two, x);
            d.add(mx, r1)
        });

        let mul_two_mul_m_q2 = d.mul(two, mul_m_q2);
        let distributed = d.add(mul_two_mul_m_q2, two_r2);
        let s_c = d.add(distributed, r1);
        let distribute = d.lemma(p.left_distrib, &[two, mul_m_q2, r2]);
        let h_c = d.congr(mul_two_recon2, distributed, distribute, &|d, x| {
            d.add(x, r1)
        });

        let mul_two_m = d.mul(two, m);
        let mul_two_m_q2 = d.mul(mul_two_m, q2);
        let regrouped_left = d.add(mul_two_m_q2, two_r2);
        let s_d1 = d.add(regrouped_left, r1);
        let massoc = d.lemma(p.mul_assoc, &[two, m, q2]);
        let massoc_rev = d.symm(mul_two_m_q2, mul_two_mul_m_q2, massoc);
        let h_d1 = d.congr(mul_two_mul_m_q2, mul_two_m_q2, massoc_rev, &|d, x| {
            let inner = d.add(x, two_r2);
            d.add(inner, r1)
        });

        let s_d2 = d.add(mul_two_m_q2, r3);
        let h_d2 = d.lemma(p.add_assoc, &[mul_two_m_q2, two_r2, r1]);

        let mul_m_two = d.mul(m, two);
        let mul_m_two_q2 = d.mul(mul_m_two, q2);
        let s_d3 = d.add(mul_m_two_q2, r3);
        let comm_two_m = d.lemma(p.mul_comm, &[two, m]);
        let h_d3 = d.congr(mul_two_m, mul_m_two, comm_two_m, &|d, x| {
            let mx = d.mul(x, q2);
            d.add(mx, r3)
        });

        let (_final, eq_chain) = d.chain(
            n,
            &[
                (recon1, eq1),
                (s_b, h_b),
                (s_c, h_c),
                (s_d1, h_d1),
                (s_d2, h_d2),
                (s_d3, h_d3),
            ],
        );
        let eq3_ty = d.eq(n, s_d3);

        // ---- bound: Lt r3 (mul m 2) -------------------------------------
        let succ_r2 = d.succ(r2);
        let mul_two_succ_r2 = d.mul(two, succ_r2);
        let ineq_a0 = d.lemma(p.mul_le_mul_left, &[two, succ_r2, m, bound2]);
        let mul_succ_eq = d.lemma(p.mul_succ, &[two, r2]);
        let add_two_r2_two = d.add(two_r2, two);
        let ineq_a_motive = d.eq_motive(mul_two_succ_r2, &|d, x| d.le(x, mul_two_m));
        let ineq_a = d.transport(
            mul_two_succ_r2,
            ineq_a_motive,
            ineq_a0,
            add_two_r2_two,
            mul_succ_eq,
        );

        let succ_r1 = d.succ(r1);
        let add_two_r2_succ_r1 = d.add(two_r2, succ_r1);
        let ineq_b0 = d.lemma(p.add_le_add_left, &[two_r2, succ_r1, two, bound1]);
        let add_succ_eq = d.lemma(p.add_succ, &[two_r2, r1]);
        let succ_r3 = d.succ(r3);
        let ineq_b_motive = d.eq_motive(add_two_r2_succ_r1, &|d, x| d.le(x, add_two_r2_two));
        let ineq_b = d.transport(
            add_two_r2_succ_r1,
            ineq_b_motive,
            ineq_b0,
            succ_r3,
            add_succ_eq,
        );

        let ineq_c = d.lemma(
            p.le_trans,
            &[succ_r3, add_two_r2_two, mul_two_m, ineq_b, ineq_a],
        );

        let bound_motive = d.eq_motive(mul_two_m, &|d, x| d.le(succ_r3, x));
        let bound3 = d.transport(mul_two_m, bound_motive, ineq_c, mul_m_two, comm_two_m);
        let bound3_ty = d.lt(r3, divisor);

        let h_construct = d.const_app(p.logic.and_intro, &[eq3_ty, bound3_ty, eq_chain, bound3]);

        // ---- compare against the executable divMod for (n, mul m 2) ----
        let le1_two = {
            let zero = d.zero();
            let zle1 = d.lemma(p.zero_le, &[one]);
            d.lemma(p.le_succ_succ, &[zero, one, zle1])
        };
        let pos_divisor = d.lemma(p.one_le_mul, &[m, two, pos, le1_two]);

        let h_exec = div_mod_positive(d, &p, n, divisor, pos_divisor);
        let q_exec = d.div(n, divisor);
        let r_exec = d.modulo(n, divisor);

        let unique = d.lemma(
            p.div_mod_unique,
            &[divisor, n, q_exec, r_exec, q2, r3, h_exec, h_construct],
        );
        let eq_q_ty = d.eq(q_exec, q2);
        let eq_r_ty = d.eq(r_exec, r3);
        let r_eq = and_right(d, eq_q_ty, eq_r_ty, unique);
        let final_proof = d.symm(r_exec, r3, r_eq);

        let stmt = d.arrow(pos_ty, target);
        let proof = d.lam_fv(pos_fv, pos_ty, final_proof);
        (stmt, proof)
    })?;
    Ok(())
}

/// `fun i => mul (testBit n i) (pow 2 i)`.
fn term_fn(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let tb = d.const_app(p.test_bit, &[n, i]);
    let two = d.num(2);
    let p2i = d.pow(two, i);
    let body = d.mul(tb, p2i);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => f (succ i)`.
fn shifted(d: &mut NatDev<'_>, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let si = d.succ(i);
    let body = d.apply(f, &[si]);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => mul 2 (f i)`.
fn scaled_by_two(d: &mut NatDev<'_>, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let two = d.num(2);
    let body = d.mul(two, fi);
    d.lam_fv(i_fv, nat, body)
}

/// `sum_testBit_lt : ∀ k n,
/// sumRange (fun i => mul (testBit n i) (pow 2 i)) k = mod n (pow 2 k)`.
///
/// Induction on `k`, generalized over `n` (the step needs the hypothesis at
/// `n/2`, matching `testBit`'s own recursive shift): front-peel the sum
/// (`sum_range_shift_front`, since the LOW bit — index `0` — is what
/// `testBit n (succ i) ≡ testBit (n/2) i` peels off), fold the shifted tail
/// back into `two * sumRange (fun i => testBit (n/2) i * 2^i) k` via
/// `mul_assoc`/`mul_comm` and `sum_range_congr` + `mul_sum_range`, apply the
/// hypothesis at `n/2`, then close with [`declare_mod_two_mul_split`] and
/// `pow_succ`.
fn declare_sum_test_bit_lt(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let f_n = term_fn(d, &p, n);
        let lhs = d.sum_range(f_n, x);
        let two = d.num(2);
        let px = d.pow(two, x);
        let rhs = d.modulo(n, px);
        let body = d.eq(lhs, rhs);
        d.pi_fv(n_fv, nat, body)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let one = d.num(1);

        // divMod 1 n n 0 : n = mul 1 n + 0 ∧ 0 < 1
        let mul_one_n = d.mul(one, n);
        let one_mul_proof = d.lemma(p.one_mul, &[n]);
        let eq_proof = d.symm(mul_one_n, n, one_mul_proof);
        let zero = d.zero();
        let zero_bound = d.zero_lt_succ(zero);
        let recon = d.add(mul_one_n, zero);
        let eq_ty = d.eq(n, recon);
        let bound_ty = d.lt(zero, one);
        let h_zero = d.const_app(p.logic.and_intro, &[eq_ty, bound_ty, eq_proof, zero_bound]);

        let h_exec = d.lemma(p.div_mod_exec, &[zero, n]);
        let div_n_one = d.div(n, one);
        let mod_n_one = d.modulo(n, one);
        let unique = d.lemma(
            p.div_mod_unique,
            &[one, n, n, zero, div_n_one, mod_n_one, h_zero, h_exec],
        );
        let eq_q_ty = d.eq(n, div_n_one);
        let eq_r_ty = d.eq(zero, mod_n_one);
        let base_proof = and_right(d, eq_q_ty, eq_r_ty, unique);
        d.lam_fv(n_fv, nat, base_proof)
    };

    let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let two = d.num(2);
        let half = d.div(n, two);
        let sj = d.succ(j);

        let f_n = term_fn(d, &p, n);
        let f_half = term_fn(d, &p, half);
        let shifted_n = shifted(d, f_n);
        let g = scaled_by_two(d, f_half);

        // shift : sumRange f_n (succ j) = f_n 0 + sumRange shifted_n j
        let shift = d.lemma(p.sum_range_shift_front, &[f_n, j]);
        let zero = d.zero();
        let f_n0 = d.apply(f_n, &[zero]);
        let sum_shifted = d.sum_range(shifted_n, j);
        let t1 = d.add(f_n0, sum_shifted);

        // pointwise_eq : ∀ i, shifted_n i = mul 2 (f_half i)
        let pointwise_eq = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let half_tb = d.const_app(p.test_bit, &[half, i]);
            let pow_i = d.pow(two, i);
            let f_half_i = d.mul(half_tb, pow_i);
            let mul_f_half_i_two = d.mul(f_half_i, two);
            let inner = d.mul(pow_i, two);
            let shifted_form = d.mul(half_tb, inner);
            let massoc_i = d.lemma(p.mul_assoc, &[half_tb, pow_i, two]);
            let step1 = d.symm(mul_f_half_i_two, shifted_form, massoc_i);
            let mul_two_f_half_i = d.mul(two, f_half_i);
            let comm_i = d.lemma(p.mul_comm, &[f_half_i, two]);
            let point_eq_i = d.trans(
                shifted_form,
                mul_f_half_i_two,
                mul_two_f_half_i,
                step1,
                comm_i,
            );
            d.lam_fv(i_fv, nat, point_eq_i)
        };
        let congr_sum = d.lemma(p.sum_range_congr, &[shifted_n, g, j, pointwise_eq]);
        let sum_g = d.sum_range(g, j);
        let t2 = d.add(f_n0, sum_g);

        let sum_half = d.sum_range(f_half, j);
        let mul_two_sum_half = d.mul(two, sum_half);
        // mul_sum_range(a,f,n) : mul a (sumRange f n) = sumRange (fun i => a*f i) n
        let mul_sum = d.lemma(p.mul_sum_range, &[two, f_half, j]); // : mul_two_sum_half = sum_g
        let mul_sum_rev = d.symm(mul_two_sum_half, sum_g, mul_sum); // : sum_g = mul_two_sum_half
        let t3 = d.add(f_n0, mul_two_sum_half);

        let ih_half = d.apply(ih, &[half]);
        let pow_j = d.pow(two, j);
        let mod_half_j = d.modulo(half, pow_j);
        let mul_two_mod_half = d.mul(two, mod_half_j);
        let t4 = d.add(f_n0, mul_two_mod_half);

        let mod_n_two = d.modulo(n, two);
        let mul_one_proof = d.lemma(p.mul_one, &[mod_n_two]);
        let t5 = d.add(mod_n_two, mul_two_mod_half);

        let swap = d.lemma(p.add_comm, &[mod_n_two, mul_two_mod_half]);
        let t6 = d.add(mul_two_mod_half, mod_n_two);

        let pos_pow_j = pow_two_pos(d, &p, j);
        let split = d.lemma(p.mod_two_mul_split, &[n, pow_j, pos_pow_j]);
        let mul_pow_j_two = d.mul(pow_j, two);
        let t7 = d.modulo(n, mul_pow_j_two);

        let pow_succ_eq = d.lemma(p.pow_succ, &[two, j]);
        let pow_sj = d.pow(two, sj);
        let pow_succ_rev = d.symm(mul_pow_j_two, pow_sj, pow_succ_eq);
        let t8 = d.modulo(n, pow_sj);

        let h2 = d.congr(sum_shifted, sum_g, congr_sum, &|d, x| d.add(f_n0, x));
        let h3 = d.congr(sum_g, mul_two_sum_half, mul_sum_rev, &|d, x| d.add(f_n0, x));
        let h4 = d.congr(sum_half, mod_half_j, ih_half, &|d, x| {
            let mx = d.mul(two, x);
            d.add(f_n0, mx)
        });
        let h5 = d.congr(f_n0, mod_n_two, mul_one_proof, &|d, x| {
            d.add(x, mul_two_mod_half)
        });
        let h7 = d.congr(mul_pow_j_two, pow_sj, pow_succ_rev, &|d, x| d.modulo(n, x));

        let start = d.sum_range(f_n, sj);
        let (_last, proof) = d.chain(
            start,
            &[
                (t1, shift),
                (t2, h2),
                (t3, h3),
                (t4, h4),
                (t5, h5),
                (t6, swap),
                (t7, split),
                (t8, h7),
            ],
        );
        d.lam_fv(n_fv, nat, proof)
    };

    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let proof_fn = d.induct(&motive, &base, &step, k);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let proof = d.apply(proof_fn, &[n]);
    let stmt = {
        let f_n = term_fn(d, &p, n);
        let lhs = d.sum_range(f_n, k);
        let two = d.num(2);
        let pk = d.pow(two, k);
        let rhs = d.modulo(n, pk);
        d.eq(lhs, rhs)
    };
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(k_fv, nat, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(k_fv, nat, over_n)
    };
    d.declare_theorem(p.sum_test_bit_lt, ty, value)
}

/// Everything this module declares, in dependency order.
pub(super) fn declare_binary_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_test_bit_defs(d, p)?;
    declare_test_bit_le_one(d, p)?;
    declare_mod_two_mul_split(d, p)?;
    declare_sum_test_bit_lt(d, p)?;
    Ok(())
}
