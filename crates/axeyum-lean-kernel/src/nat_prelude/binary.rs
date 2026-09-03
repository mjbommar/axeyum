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
use super::helpers::{and_left, and_right, iff_forward};
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

/// `test_bit_of_zero : ∀ i, Eq (testBit 0 i) zero`. Induction on `i`: base
/// is `testBit 0 0 = mod 0 2 = 0` (`testBit_zero` then `zero_mod`); step
/// uses `testBit 0 (succ j) = testBit (div 0 2) j` (`testBit_succ`), and
/// `div 0 2 = 0` (`zero_div`) puts the recursive occurrence at the SAME `0`
/// the induction hypothesis already covers.
fn declare_test_bit_of_zero(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.test_bit_of_zero, 1, &|d, values| {
        let i = values[0];
        let zero = d.zero();
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let tb = d.const_app(p.test_bit, &[zero, candidate]);
            let zero = d.zero();
            d.eq(tb, zero)
        };
        let proof = d.induct(
            &statement_at,
            &|d| {
                let zero = d.zero();
                let tb0 = d.const_app(p.test_bit, &[zero, zero]);
                let tbz = d.lemma(p.test_bit_zero, &[zero]);
                let two = d.num(2);
                let mod02 = d.modulo(zero, two);
                let zmod = d.lemma(p.zero_mod, &[two]);
                let (_, combined) = d.chain(tb0, &[(mod02, tbz), (zero, zmod)]);
                combined
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let zero = d.zero();
                let tb_succ = d.const_app(p.test_bit, &[zero, sj]);
                let tbs = d.lemma(p.test_bit_succ, &[zero, j]);
                let two = d.num(2);
                let half = d.div(zero, two);
                let tb_half_j = d.const_app(p.test_bit, &[half, j]);
                let zdiv = d.lemma(p.zero_div, &[two]);
                let congr_half =
                    d.congr(half, zero, zdiv, &|d, x| d.const_app(p.test_bit, &[x, j]));
                let tb_zero_j = d.const_app(p.test_bit, &[zero, j]);
                let (_, combined) = d.chain(
                    tb_succ,
                    &[(tb_half_j, tbs), (tb_zero_j, congr_half), (zero, ih)],
                );
                combined
            },
            i,
        );
        (statement_at(d, i), proof)
    })?;
    Ok(())
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
    declare_test_bit_of_zero(d, p)?;
    declare_mod_two_mul_split(d, p)?;
    declare_sum_test_bit_lt(d, p)?;
    Ok(())
}

/// `sizeAux`, `size`, and `size_zero` — the number-of-binary-digits function.
///
/// `sizeAux` has the SAME fuel-recursion shape as `testBitAux` (`Nat.rec` on
/// the first argument with a `Nat -> Nat` motive, the second argument riding
/// through as an ordinary parameter), but adds the zero-check Boolean guard
/// `testBitAux` does not need: `sizeAux (succ f) n` must stop growing once
/// `n` itself hits `0`, or `size n := sizeAux n n` would overcount (e.g.
/// `size 0` would recurse `0` more steps regardless — actually the base case
/// alone already fixes `n = 0`, but the guard is what keeps `sizeAux fuel 0
/// = 0` true for every `fuel`, not just `fuel = 0`, which is what makes "is
/// `n` itself enough fuel" a provable, fuel-independent-once-past-zero
/// statement rather than a coincidence of `size`'s particular choice
/// `fuel := n`).
fn declare_size_defs(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let fn_ty = d.arrow(nat, nat);

    // sizeAux 0 n ≡ 0 ;
    // sizeAux (succ f) n ≡ if beq n 0 then 0 else succ (sizeAux f (n / 2))
    {
        let base_term = {
            let n_fv = d.fresh_fvar();
            let zero = d.zero();
            d.lam_fv(n_fv, nat, zero)
        };
        let step_term = {
            let f_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let zero = d.zero();
            let two = d.num(2);
            let condition = d.beq(n, zero);
            let half = d.div(n, two);
            let recursed = d.apply(ih, &[half]);
            let succ_recursed = d.succ(recursed);
            let selected = d.bool_select_nat(condition, zero, succ_recursed);
            let inner = d.lam_fv(n_fv, nat, selected);
            let with_ih = d.lam_fv(ih_fv, fn_ty, inner);
            d.lam_fv(f_fv, nat, with_ih)
        };
        let motive = d.kernel().lam(anon, nat, fn_ty, BinderInfo::Default);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let one = d.level_one();
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[motive, base_term, step_term, f]);
        let value = d.lam_fv(f_fv, nat, body);
        let ty = d.arrow(nat, fn_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.size_aux,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    // size n := sizeAux n n
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let value = {
            let applied = d.const_app(p.size_aux, &[n, n]);
            d.lam_fv(n_fv, nat, applied)
        };
        let ty = d.arrow(nat, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.size,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(7),
        })?;
    }

    // size_zero : size 0 = 0
    // size 0 ≡ sizeAux 0 0, and sizeAux's base case is `fun n => 0` applied
    // to any n — including 0 — so this is refl.
    d.theorem(p.size_zero, 0, &|d, _v| {
        let zero = d.zero();
        let lhs = d.const_app(p.size, &[zero]);
        (d.eq(lhs, zero), d.refl(zero))
    })?;

    Ok(())
}

/// `h : Lt zero n ⊢ Eq Nat n (add n n) → derive Lt n (mul two n)`... in fact
/// this builds `Lt n (mul two n)` directly (with `two` supplied by the
/// caller, so the result's stated multiplier matches whatever `two` the
/// surrounding proof already uses — the kernel's final `def_eq` check bridges
/// any residual mismatch against a literal `succ (succ zero)`, the same way
/// `mod_two_mul_split` already relies on `succ one ≡ two`).
///
/// `n < n+n` from `0 < n` via `add_lt_add_left` (at `add n zero`, restored to
/// `n` by `add_zero`), then `n+n = mul (succ one) n` via `succ_mul`/`one_mul`
/// (`mul two n` and `mul (succ one) n` being the same term up to `def_eq`).
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

/// `size_aux_lt_pow : ∀ fuel n, Le n fuel → Lt n (pow 2 (sizeAux fuel n))`.
///
/// Induction on `fuel`, generalized over `n` (the same "generalize the OTHER
/// variable" shape as `testBit_le_one`/`sum_testBit_lt`, since the step needs
/// the hypothesis at `n/2`, not at `n`).
///
/// This is deliberately NOT the `sizeAux n n = sizeAux (succ n) n` equality
/// the handover sketched. That statement is about two ADJACENT fuel values
/// and says nothing about why `n` itself is enough fuel to begin with — and
/// it is not actually what `lt_pow_size` needs. This bound (`Le n fuel`
/// suffices, for ANY sufficient fuel, not just adjacent pairs) is what
/// `lt_pow_size` needs, and specializing it at `fuel := n` (via `le_refl`)
/// both proves `lt_pow_size` and witnesses that `n` itself is sufficient
/// fuel for `size n := sizeAux n n` — the fuel-sufficiency fact item 2 of the
/// handover asked for, restated as a bound rather than an equation because
/// the bound is what the rest of the development actually consumes.
///
/// The base case (`fuel = 0`) needs `Le n 0 → Lt n 1`, via `lt_of_le_of_lt`
/// through `Lt 0 1`. The step case splits on `beq n 0` exactly like
/// `sizeAux`'s own definition does (mirroring
/// `division.rs::executable_division_spec_step`'s `Bool.rec` case-split
/// pattern): at `n = 0` the target is `Lt n 1`, immediate from `n = 0`; away
/// from `0`, `n/2 < f` follows from `n ≤ succ f` and `n/2 < n` (itself from
/// `n < 2*n` at positive `n`, via `div_mod_lt_mul_iff`), the induction
/// hypothesis at `n/2` gives `n/2 < 2^(sizeAux f (n/2))`, and reassembling
/// `n = 2*(n/2) + (n mod 2)` with `n mod 2 ≤ 1` bounds `n` below
/// `2 * 2^(sizeAux f (n/2)) = 2^(succ (sizeAux f (n/2)))` via `pow_succ`.
fn declare_size_aux_lt_pow(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();

    let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let bound_ty = d.le(n, x);
        let sz = d.const_app(p.size_aux, &[x, n]);
        let two = d.num(2);
        let pw = d.pow(two, sz);
        let concl = d.lt(n, pw);
        let body = d.arrow(bound_ty, concl);
        d.pi_fv(n_fv, nat, body)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let zero = d.zero();
        let bound_ty = d.le(n, zero);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let one = d.num(1);
        let zero_lt_one = d.zero_lt_succ(zero);
        let concl = d.lemma(p.lt_of_le_of_lt, &[n, zero, one, bound, zero_lt_one]);
        let with_bound = d.lam_fv(bound_fv, bound_ty, concl);
        d.lam_fv(n_fv, nat, with_bound)
    };

    let step = |d: &mut NatDev<'_>, f: ExprId, ih: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sf = d.succ(f);
        let bound_ty = d.le(n, sf);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);

        let zero = d.zero();
        let two = d.num(2);
        let condition = d.beq(n, zero);
        let half = d.div(n, two);
        let sz_f_half = d.const_app(p.size_aux, &[f, half]);
        let succ_recursed = d.succ(sz_f_half);

        let target_for = |d: &mut NatDev<'_>, selector: ExprId| {
            let selected = d.bool_select_nat(selector, zero, succ_recursed);
            let pw = d.pow(two, selected);
            d.lt(n, pw)
        };
        let branch_for = |d: &mut NatDev<'_>, selector: ExprId| {
            let equality = d.bool_eq(condition, selector);
            let target = target_for(d, selector);
            d.arrow(equality, target)
        };

        let false_value = d.bool_false();
        let true_value = d.bool_true();

        // beq n 0 = false ⟹ n ≠ 0 ⟹ 0 < n, and n/2 < f from n ≤ succ f.
        let false_minor = {
            let false_equality_ty = d.bool_eq(condition, false_value);
            let false_equality_fv = d.fresh_fvar();
            let false_equality = d.kernel().fvar(false_equality_fv);

            let not_eq = d.lemma(p.ne_of_beq_eq_false, &[n, zero, false_equality]);
            let pos = d.lemma(p.zero_lt_of_ne_zero, &[n, not_eq]);

            let one = d.num(1);
            let h_exec = d.lemma(p.div_mod_exec, &[one, n]);
            let r1 = d.modulo(n, two);
            let mul_two_half = d.mul(two, half);
            let recon = d.add(mul_two_half, r1);
            let eq_ty = d.eq(n, recon);
            let bound_r_ty = d.lt(r1, two);
            let eq_n_recon = and_left(d, eq_ty, bound_r_ty, h_exec);
            let r1_lt_two = and_right(d, eq_ty, bound_r_ty, h_exec);

            // half < n, via `n < 2*n` (positivity) through `div_mod_lt_mul_iff`.
            let iff_fn = d.lemma(p.div_mod_lt_mul_iff, &[two, n, half, r1, n]);
            let the_iff = d.apply(iff_fn, &[h_exec]);
            let mul_two_n = d.mul(two, n);
            let lt_n_2n_ty = d.lt(n, mul_two_n);
            let lt_half_n_ty = d.lt(half, n);
            let forward = iff_forward(d, lt_n_2n_ty, lt_half_n_ty, the_iff);
            let n_lt_2n = n_lt_mul_two(d, &p, n, pos);
            let half_lt_n = d.apply(forward, &[n_lt_2n]);

            // half < succ f (from half < n ≤ succ f), so half ≤ f.
            let half_lt_sf = d.lemma(p.lt_of_lt_of_le, &[half, n, sf, half_lt_n, bound]);
            let half_le_f = d.lemma(p.le_of_succ_le_succ, &[half, f, half_lt_sf]);

            // IH at half : Lt half (pow 2 (sizeAux f half))
            let ih_at_half = d.apply(ih, &[half]);
            let half_lt_x = d.apply(ih_at_half, &[half_le_f]);
            let pow_x = d.pow(two, sz_f_half);

            // n ≤ 2*half + 1 (from n = 2*half + r1, r1 < 2 ⟹ r1 ≤ 1).
            let r1_le_one = d.lemma(p.le_of_succ_le_succ, &[r1, one, r1_lt_two]);
            let recon_le_bound1 = d.lemma(p.add_le_add_left, &[mul_two_half, r1, one, r1_le_one]);
            let eq_recon_n = d.symm(n, recon, eq_n_recon);
            let add_bound1 = d.add(mul_two_half, one);
            let motive_a = d.eq_motive(recon, &|d, x| d.le(x, add_bound1));
            let n_le_bound1 = d.transport(recon, motive_a, recon_le_bound1, n, eq_recon_n);

            // 2*half + 1 < 2*half + 2 (from 1 < 2, i.e. le_refl two).
            let one_lt_two = d.lemma(p.le_refl, &[two]);
            let lt_from_b = d.lemma(p.add_lt_add_left, &[mul_two_half, one, two, one_lt_two]);
            let add_bound2 = d.add(mul_two_half, two);
            let n_lt_bound2 = d.lemma(
                p.lt_of_le_of_lt,
                &[n, add_bound1, add_bound2, n_le_bound1, lt_from_b],
            );

            // 2*half + 2 = 2*(succ half) ≤ 2*(pow 2 (sizeAux f half)) = 2*pow_x.
            let succ_half = d.succ(half);
            let mul_two_succ_half = d.mul(two, succ_half);
            let mul_le = d.lemma(p.mul_le_mul_left, &[two, succ_half, pow_x, half_lt_x]);
            let two_succ_half_eq = d.lemma(p.mul_succ, &[two, half]);
            let mul_two_pow_x = d.mul(two, pow_x);
            let motive_e = d.eq_motive(mul_two_succ_half, &|d, x| d.le(x, mul_two_pow_x));
            let bound2_le_mulx = d.transport(
                mul_two_succ_half,
                motive_e,
                mul_le,
                add_bound2,
                two_succ_half_eq,
            );

            let n_lt_mul_two_x = d.lemma(
                p.lt_of_lt_of_le,
                &[n, add_bound2, mul_two_pow_x, n_lt_bound2, bound2_le_mulx],
            );

            // 2*pow_x = pow_x*2 = pow 2 (succ (sizeAux f half)) via mul_comm/pow_succ.
            let mul_comm_eq = d.lemma(p.mul_comm, &[two, pow_x]);
            let mul_pow_x_two = d.mul(pow_x, two);
            let motive_g = d.eq_motive(mul_two_pow_x, &|d, x| d.lt(n, x));
            let n_lt_mul_x_two = d.transport(
                mul_two_pow_x,
                motive_g,
                n_lt_mul_two_x,
                mul_pow_x_two,
                mul_comm_eq,
            );

            let pow_succ_target = d.pow(two, succ_recursed);
            let pow_succ_eq = d.lemma(p.pow_succ, &[two, sz_f_half]);
            let pow_succ_eq_rev = d.symm(pow_succ_target, mul_pow_x_two, pow_succ_eq);
            let motive_h = d.eq_motive(mul_pow_x_two, &|d, x| d.lt(n, x));
            let final_false = d.transport(
                mul_pow_x_two,
                motive_h,
                n_lt_mul_x_two,
                pow_succ_target,
                pow_succ_eq_rev,
            );

            d.lam_fv(false_equality_fv, false_equality_ty, final_false)
        };

        // beq n 0 = true ⟹ n = 0 ⟹ Lt n 1 = Lt n (pow 2 0).
        let true_minor = {
            let true_equality_ty = d.bool_eq(condition, true_value);
            let true_equality_fv = d.fresh_fvar();
            let true_equality = d.kernel().fvar(true_equality_fv);
            let eq_n_zero = d.lemma(p.eq_of_beq_eq_true, &[n, zero, true_equality]);
            let eq_zero_n = d.symm(n, zero, eq_n_zero);
            let one = d.num(1);
            let zero_lt_one = d.zero_lt_succ(zero);
            let motive_t = d.eq_motive(zero, &|d, x| d.lt(x, one));
            let final_true = d.transport(zero, motive_t, zero_lt_one, n, eq_zero_n);
            d.lam_fv(true_equality_fv, true_equality_ty, final_true)
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
        let step_result = d.apply(selected, &[condition_refl]);

        let with_bound = d.lam_fv(bound_fv, bound_ty, step_result);
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
        let sz = d.const_app(p.size_aux, &[fuel, n]);
        let two = d.num(2);
        let pw = d.pow(two, sz);
        let concl = d.lt(n, pw);
        d.arrow(bound_ty, concl)
    };
    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(fuel_fv, nat, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(fuel_fv, nat, over_n)
    };
    d.declare_theorem(p.size_aux_lt_pow, ty, value)
}

/// `lt_pow_size : ∀ n, Lt n (pow 2 (size n))` — the `fuel := n` instance of
/// [`declare_size_aux_lt_pow`], via `le_refl`.
fn declare_lt_pow_size(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.lt_pow_size, 1, &|d, v| {
        let n = v[0];
        let le_refl_n = d.lemma(p.le_refl, &[n]);
        let bound_proof = d.lemma(p.size_aux_lt_pow, &[n, n, le_refl_n]);
        let sz = d.const_app(p.size, &[n]);
        let two = d.num(2);
        let pw = d.pow(two, sz);
        let stmt = d.lt(n, pw);
        (stmt, bound_proof)
    })?;
    Ok(())
}

/// `mod_eq_self_of_lt : ∀ n m, Lt n m → mod n m = n`.
///
/// A GENERAL division fact, not specific to binary representation (per the
/// handover: it belongs promoted out of `binary.rs` if another prelude wants
/// it, but this is where the theorem was needed first). `Lt n m` gives
/// `0 < m` (via `zero_le n` and transitivity), so `div_mod_positive` builds
/// the executable witness `divMod m n (n/m) (n%m)`. Comparing it against the
/// hand-built witness `divMod m n 0 n` (valid since `n = m*0+n` and `n < m`
/// is exactly the hypothesis) via `div_mod_unique` forces `n%m = n`.
fn declare_mod_eq_self_of_lt(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_eq_self_of_lt, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let hyp_ty = d.lt(n, m);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let zero = d.zero();

        let zero_le_n = d.lemma(p.zero_le, &[n]);
        let pos = d.lemma(p.lt_of_le_of_lt, &[zero, n, m, zero_le_n, hyp]);
        let h_exec = div_mod_positive(d, &p, n, m, pos);

        let mul_m_zero = d.mul(m, zero);
        let mul_zero_eq = d.lemma(p.mul_zero, &[m]);
        let recon = d.add(mul_m_zero, n);
        let add_zero_n = d.add(zero, n);
        let zero_add_eq = d.lemma(p.zero_add, &[n]);
        let congr1 = d.congr(mul_m_zero, zero, mul_zero_eq, &|d, x| d.add(x, n));
        let (_, recon_eq_n) = d.chain(recon, &[(add_zero_n, congr1), (n, zero_add_eq)]);
        let eq_n_recon = d.symm(recon, n, recon_eq_n);

        let eq_ty = d.eq(n, recon);
        let h_hand = d.const_app(p.logic.and_intro, &[eq_ty, hyp_ty, eq_n_recon, hyp]);

        let q_exec = d.div(n, m);
        let r_exec = d.modulo(n, m);
        let unique = d.lemma(
            p.div_mod_unique,
            &[m, n, q_exec, r_exec, zero, n, h_exec, h_hand],
        );
        let eq_q_ty = d.eq(q_exec, zero);
        let eq_r_ty = d.eq(r_exec, n);
        let r_eq = and_right(d, eq_q_ty, eq_r_ty, unique);

        let stmt = d.arrow(hyp_ty, eq_r_ty);
        let proof = d.lam_fv(hyp_fv, hyp_ty, r_eq);
        (stmt, proof)
    })?;
    Ok(())
}

/// `sum_testBit_eq : ∀ n,
/// sumRange (fun i => mul (testBit n i) (pow 2 i)) (size n) = n` — a natural
/// number IS the sum of its own bits. [`declare_sum_test_bit_lt`] at
/// `k := size n`, closed by `lt_pow_size` and `mod_eq_self_of_lt`.
fn declare_sum_test_bit_eq(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.sum_test_bit_eq, 1, &|d, v| {
        let n = v[0];
        let sz = d.const_app(p.size, &[n]);
        let two = d.num(2);
        let pow_sz = d.pow(two, sz);

        let f_n = term_fn(d, &p, n);
        let start = d.sum_range(f_n, sz);
        let mod_val = d.modulo(n, pow_sz);

        let step1 = d.lemma(p.sum_test_bit_lt, &[sz, n]);
        let lt_proof = d.lemma(p.lt_pow_size, &[n]);
        let step2 = d.lemma(p.mod_eq_self_of_lt, &[n, pow_sz, lt_proof]);

        let (_, combined) = d.chain(start, &[(mod_val, step1), (n, step2)]);
        let stmt = d.eq(start, n);
        (stmt, combined)
    })?;
    Ok(())
}

/// Everything this module's `size` addendum declares, in dependency order.
pub(super) fn declare_size_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_size_defs(d, p)?;
    declare_size_aux_lt_pow(d, p)?;
    declare_lt_pow_size(d, p)?;
    declare_mod_eq_self_of_lt(d, p)?;
    declare_sum_test_bit_eq(d, p)?;
    Ok(())
}

/// `fun _ => zero : Nat -> Nat` — the constant-zero function, used both by
/// [`declare_sum_range_const_zero`]'s own statement and by
/// [`declare_zero_of_test_bit`]'s call site, so both mention the SAME raw
/// term rather than two independently-built lambdas that merely happen to
/// coincide.
fn zero_fn(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let zero = d.zero();
    d.lam_fv(i_fv, nat, zero)
}

/// `sumRange_const_zero : ∀ k, Eq (sumRange (fun _ => zero) k) zero` — a
/// general arithmetic fact (not specific to `testBit`), by induction on `k`:
/// the base case is `sum_range_zero`; the step peels one term via
/// `sum_range_succ` (`sumRange g (succ j) = add (sumRange g j) (g j)`), the
/// induction hypothesis rewrites the first summand to `zero`, and
/// `add zero (g j)` is `refl` to `zero` (`g j` beta-reduces to the literal
/// `zero`, and `add` recurses on its SECOND argument, so `add_zero`'s
/// pattern fires directly). Needed by [`declare_zero_of_test_bit`].
fn declare_sum_range_const_zero(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let g = zero_fn(d);
    d.theorem(p.sum_range_const_zero, 1, &|d, values| {
        let k = values[0];
        let statement_at = |d: &mut NatDev<'_>, candidate: ExprId| -> ExprId {
            let lhs = d.sum_range(g, candidate);
            let zero = d.zero();
            d.eq(lhs, zero)
        };
        let proof = d.induct(
            &statement_at,
            &|d| d.lemma(p.sum_range_zero, &[g]),
            &|d, j, ih| {
                let sj = d.succ(j);
                let start = d.sum_range(g, sj);
                let sum_j = d.sum_range(g, j);
                let g_j = d.apply(g, &[j]);
                let step_eq = d.lemma(p.sum_range_succ, &[g, j]);
                let mid = d.add(sum_j, g_j);
                let zero = d.zero();
                let final_term = d.add(zero, g_j);
                let congr_ih = d.congr(sum_j, zero, ih, &|d, x| {
                    let g_j2 = d.apply(g, &[j]);
                    d.add(x, g_j2)
                });
                let refl_final = d.refl(final_term);
                let (_, combined) = d.chain(
                    start,
                    &[(mid, step_eq), (final_term, congr_ih), (zero, refl_final)],
                );
                combined
            },
            k,
        );
        (statement_at(d, k), proof)
    })?;
    Ok(())
}

/// `zero_of_testBit_eq_zero : ∀ n, (∀ i, Eq (testBit n i) zero) → Eq n
/// zero`. See [`NatPrelude::zero_of_test_bit_eq_zero`]'s doc for why this is
/// registered as a NEW local fact rather than used to flip the pinned
/// Bool-typed `ml430` mirror `Nat.zero_of_testBit_eq_false`.
///
/// Proof: the hypothesis makes every summand of `sum_testBit_eq`'s sum
/// (`fun i => mul (testBit n i) (pow 2 i)`) collapse to `zero` (via
/// `zero_mul`), so `sum_range_congr` identifies that sum with
/// `sumRange (fun _ => zero) (size n)`, which `sum_range_const_zero` gives
/// as `zero`; `sum_testBit_eq` itself identifies the original sum with `n`.
fn declare_zero_of_test_bit_inner(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let g = zero_fn(d);
    d.theorem(p.zero_of_test_bit_eq_zero, 1, &|d, values| {
        let n = values[0];
        let zero = d.zero();

        let hyp_ty = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let tb = d.const_app(p.test_bit, &[n, i]);
            let zero = d.zero();
            let body = d.eq(tb, zero);
            d.pi_fv(i_fv, nat, body)
        };
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let sz = d.const_app(p.size, &[n]);
        let f = term_fn(d, &p, n);

        // pointwise : ∀ i, Eq (f i) (g i)  --  g i beta-reduces to `zero`,
        // so the statement built here is defeq to `Eq (f i) zero`.
        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let tb = d.const_app(p.test_bit, &[n, i]);
            let two = d.num(2);
            let p2i = d.pow(two, i);
            let f_i = d.mul(tb, p2i);
            let tb_eq_zero = d.apply(hyp, &[i]);
            let mul_zero_p2i = d.mul(zero, p2i);
            let congr1 = d.congr(tb, zero, tb_eq_zero, &|d, x| {
                let two = d.num(2);
                let p2i_inner = d.pow(two, i);
                d.mul(x, p2i_inner)
            });
            let zero_mul_eq = d.lemma(p.zero_mul, &[p2i]);
            let (_, point_i) = d.chain(f_i, &[(mul_zero_p2i, congr1), (zero, zero_mul_eq)]);
            d.lam_fv(i_fv, nat, point_i)
        };

        let congr_sum = d.lemma(p.sum_range_congr, &[f, g, sz, pointwise]);
        let sum_f = d.sum_range(f, sz);
        let sum_g = d.sum_range(g, sz);
        let const_zero_eq = d.lemma(p.sum_range_const_zero, &[sz]);
        let (_, sum_f_eq_zero) = d.chain(sum_f, &[(sum_g, congr_sum), (zero, const_zero_eq)]);

        let sum_test_bit_eq_pf = d.lemma(p.sum_test_bit_eq, &[n]);
        let n_eq_sum_f = d.symm(sum_f, n, sum_test_bit_eq_pf);
        let n_eq_zero = d.trans(n, sum_f, zero, n_eq_sum_f, sum_f_eq_zero);

        let concl = d.eq(n, zero);
        let stmt = d.arrow(hyp_ty, concl);
        let proof = d.lam_fv(hyp_fv, hyp_ty, n_eq_zero);
        (stmt, proof)
    })?;
    Ok(())
}

/// [`declare_sum_range_const_zero`] then [`declare_zero_of_test_bit`], in
/// dependency order.
pub(super) fn declare_zero_of_test_bit(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_sum_range_const_zero(d, p)?;
    declare_zero_of_test_bit_inner(d, p)?;
    Ok(())
}
