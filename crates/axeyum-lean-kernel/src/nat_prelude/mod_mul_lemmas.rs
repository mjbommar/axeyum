//! The `ml430` `Nat` mod/mul family: `mod_mul`, `mod_mul_left_mod`,
//! `mod_mul_right_mod`, `mod_mul_left_div_self`, `mod_mul_right_div_self`.
//!
//! All five are "digit decomposition" facts about splitting a division by a
//! product `a*b` into a division by `a` followed by a division by `b`, and
//! all five route through two small pieces of shared machinery:
//!
//!   1. [`double_decompose`] reconstructs `divMod (a*b) x q r` for POSITIVE
//!      `a`, `b` directly, with `q := (x/a)/b` and `r := x%a + a*(x/a % b)`,
//!      by decomposing `x` at divisor `a` (`div_mod_exec`/
//!      `div_mod_reconstructed`, the established local-copy pattern from
//!      `div_mod_lemmas.rs` -- see that file's module doc for why this is a
//!      per-file copy rather than a shared export), then decomposing the
//!      quotient `x/a` at divisor `b`, and combining the two equations via
//!      `left_distrib`/`mul_assoc`/`add_assoc`/`add_comm`. Comparing this
//!      against the CANONICAL decomposition of `x` at divisor `a*b`
//!      (`div_mod_exec` again, positivity from `one_le_mul`) via
//!      `div_mod_unique` gives [`mod_mul_eq`] directly -- this closes
//!      `Nat.mod_mul` (`F:ml430-nat-mod-mul-beaccbad`) once `a`/`b` are both
//!      positive; the two degenerate cases (`a=0`, or `a>0` and `b=0`) fold
//!      away via `zero_mul`/`mul_zero`/`mod_zero`/`add_zero` congruence,
//!      never needing to know what `mod _ 0` denotes beyond the one
//!      declared equation.
//!
//!   2. [`mod_of_dvd_mod`] is the general "if `e` is a multiple of `dvsr`,
//!      then `a % e % dvsr = a % dvsr`" fact, proved directly (not via
//!      `mod_mul`): decompose `a` at `e` to get `a = e*qe + re`, then
//!      decompose the remainder `re` at `dvsr` to get `re = dvsr*qd + rd`;
//!      substituting gives `a = dvsr*(mult*qe+qd) + rd` (`e = dvsr*mult` by
//!      hypothesis) with `rd < dvsr`, a second valid `divMod dvsr a _ rd`
//!      decomposition, and `div_mod_unique` against the canonical one forces
//!      `rd = a % dvsr` -- but `rd` is *literally* `mod (mod a e) dvsr` by
//!      construction, which is the goal. This closes `mod_mul_left_mod` and
//!      `mod_mul_right_mod` (the `e := b*c` argument order differs between
//!      the two facts, bridged by `mul_comm` via the `e_eq` parameter, or by
//!      `refl` when the order already matches).
//!
//!   3. [`mod_mul_div_self`] answers `(m % (n*k)) / n = (m/n) % k`: chain
//!      [`mod_mul_eq`] (bridged by `mul_comm` when the fact's divisor order
//!      is `k*n` rather than `n*k`) to rewrite `m % (n*k)` as
//!      `m%n + n*(m/n%k)`, then `add_mul_div_left` to divide that by `n`,
//!      landing on `(m%n)/n + (m/n%k)`. [`div_of_lt`] (the generic "a value
//!      strictly below the divisor divides to `0`" fact, built the same way
//!      as the other two -- manufacture a second `divMod dvsr val 0 val` and
//!      compare) collapses `(m%n)/n` to `0` via `mod_lt`, and `zero_add`
//!      finishes. This closes `mod_mul_left_div_self` and
//!      `mod_mul_right_div_self`.
//!
//! Every positivity side condition needed along the way (`0 < a*b` from
//! `0 < a`, `0 < b`) comes from `one_le_mul` (`declare_divisibility`,
//! `Nat.one_le_mul : 1 ≤ a → 1 ≤ b → 1 ≤ a*b`) rather than any bespoke
//! multiplication-positivity lemma: `Le (succ zero) n` and `Lt zero n` are
//! definitionally the same proposition in this kernel, so `one_le_mul`'s
//! conclusion is directly usable wherever `Lt zero _` is expected.

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, cases_zero_succ};
use crate::KernelError;
use crate::expr::ExprId;

/// Reconstruct `divMod dd x (div x dd) (mod x dd)` for any `x`, given
/// `pos_dd : Lt zero dd`. A local copy of `div_mod_lemmas.rs`'s (itself a
/// local copy of `group.rs`'s private) `div_mod_reconstructed` -- see that
/// file's module doc for why this is copied rather than shared.
fn div_mod_reconstructed(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    dd: ExprId,
    pos_dd: ExprId,
    x: ExprId,
) -> ExprId {
    let p = *p;
    let succ_pred_witness = d.lemma(p.succ_pred_of_pos, &[dd]);
    let dd_eq_succ_pred = d.apply(succ_pred_witness, &[pos_dd]); // dd = succ (pred dd)
    let pred_dd = d.pred(dd);
    let succ_pred_dd = d.succ(pred_dd);
    let exec = d.lemma(p.div_mod_exec, &[pred_dd, x]); // divMod (succ pred_dd) x (div x (succ pred_dd)) (mod x (succ pred_dd))

    let motive = d.eq_motive(succ_pred_dd, &|d, y| {
        let q = d.div(x, y);
        let r = d.modulo(x, y);
        d.div_mod(y, x, q, r)
    });
    let eq_rev = d.symm(dd, succ_pred_dd, dd_eq_succ_pred); // succ_pred_dd = dd
    d.transport(succ_pred_dd, motive, exec, dd, eq_rev)
}

/// For positive `a`, `b`, reconstruct `divMod (a*b) x q r` with
/// `q := (x/a)/b`, `r := x%a + a*(x/a % b)`, returning `(relation, q, r)`.
/// See the module doc for the derivation.
fn double_decompose(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    pos_a: ExprId,
    b: ExprId,
    pos_b: ExprId,
    x: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let p = *p;

    // Decompose x at divisor a: x = a*qa + ra, ra < a.
    let qa = d.div(x, a);
    let ra = d.modulo(x, a);
    let exec_a = div_mod_reconstructed(d, &p, a, pos_a, x);
    let mul_a_qa = d.mul(a, qa);
    let sum_a = d.add(mul_a_qa, ra);
    let eq_a_ty = d.eq(x, sum_a);
    let bound_a_ty = d.lt(ra, a);
    let eq_a = and_left(d, eq_a_ty, bound_a_ty, exec_a); // x = mul a qa + ra
    let bound_a = and_right(d, eq_a_ty, bound_a_ty, exec_a); // ra < a

    // Decompose qa at divisor b: qa = b*qb + rb, rb < b.
    let qb = d.div(qa, b);
    let rb = d.modulo(qa, b);
    let exec_b = div_mod_reconstructed(d, &p, b, pos_b, qa);
    let mul_b_qb = d.mul(b, qb);
    let sum_b = d.add(mul_b_qb, rb);
    let eq_b_ty = d.eq(qa, sum_b);
    let bound_b_ty = d.lt(rb, b);
    let eq_b = and_left(d, eq_b_ty, bound_b_ty, exec_b); // qa = mul b qb + rb
    let bound_b = and_right(d, eq_b_ty, bound_b_ty, exec_b); // rb < b

    let mul_a_rb = d.mul(a, rb);
    let ab = d.mul(a, b);
    let ab_qb = d.mul(ab, qb);
    let remainder = d.add(ra, mul_a_rb);

    // x = mul a qa + ra
    //   = mul a (mul b qb + rb) + ra          [congr eq_b]
    //   = (mul a (mul b qb) + mul a rb) + ra  [left_distrib]
    //   = (mul (mul a b) qb + mul a rb) + ra  [mul_assoc, reversed]
    //   = mul (mul a b) qb + (mul a rb + ra)  [add_assoc]
    //   = mul (mul a b) qb + (ra + mul a rb)  [add_comm]
    let mul_a_sumb = d.mul(a, sum_b);
    let step1 = d.congr(qa, sum_b, eq_b, &|d, v| {
        let ma = d.mul(a, v);
        d.add(ma, ra)
    }); // sum_a = add(mul a sum_b, ra)
    let after_step1 = d.add(mul_a_sumb, ra);

    let distrib = d.lemma(p.left_distrib, &[a, mul_b_qb, rb]); // mul a sum_b = add(mul a mul_b_qb, mul a rb)
    let mul_a_mulbqb = d.mul(a, mul_b_qb);
    let add_mulamulbqb_mularb = d.add(mul_a_mulbqb, mul_a_rb);
    let step2 = d.congr(mul_a_sumb, add_mulamulbqb_mularb, distrib, &|d, v| {
        d.add(v, ra)
    });
    let after_step2 = d.add(add_mulamulbqb_mularb, ra);

    let assoc = d.lemma(p.mul_assoc, &[a, b, qb]); // mul (mul a b) qb = mul a (mul b qb)
    let assoc_rev = d.symm(ab_qb, mul_a_mulbqb, assoc); // mul a mul_b_qb = mul (mul a b) qb
    let step3 = d.congr(mul_a_mulbqb, ab_qb, assoc_rev, &|d, v| {
        let inner = d.add(v, mul_a_rb);
        d.add(inner, ra)
    });
    let add_abqb_mularb = d.add(ab_qb, mul_a_rb);
    let after_step3 = d.add(add_abqb_mularb, ra);

    let add_assoc_pf = d.lemma(p.add_assoc, &[ab_qb, mul_a_rb, ra]);
    let mularb_ra = d.add(mul_a_rb, ra);
    let after_add_assoc = d.add(ab_qb, mularb_ra);

    let comm = d.lemma(p.add_comm, &[mul_a_rb, ra]); // mularb_ra = add(ra, mul_a_rb)
    let step4 = d.congr(mularb_ra, remainder, comm, &|d, v| d.add(ab_qb, v));
    let final_rhs = d.add(ab_qb, remainder);

    let (_, eq_final) = d.chain(
        x,
        &[
            (sum_a, eq_a),
            (after_step1, step1),
            (after_step2, step2),
            (after_step3, step3),
            (after_add_assoc, add_assoc_pf),
            (final_rhs, step4),
        ],
    );
    // eq_final : x = mul (mul a b) qb + (ra + mul a rb) = mul ab qb + remainder

    // Bound: remainder < ab.
    let succ_rb = d.succ(rb);
    let mul_a_succ_rb = d.mul(a, succ_rb);
    let le1 = d.lemma(p.mul_le_mul_left, &[a, succ_rb, b, bound_b]); // mul a succ_rb <= ab
    let mul_succ_pf = d.lemma(p.mul_succ, &[a, rb]); // mul a succ_rb = add mul_a_rb a
    let add_mularb_a = d.add(mul_a_rb, a);
    let motive1 = d.eq_motive(mul_a_succ_rb, &|d, t| d.le(t, ab));
    let le2 = d.transport(mul_a_succ_rb, motive1, le1, add_mularb_a, mul_succ_pf); // add mul_a_rb a <= ab

    let step_lt = d.lemma(p.add_lt_add_left, &[mul_a_rb, ra, a, bound_a]); // add mul_a_rb ra < add mul_a_rb a
    let add_mularb_ra = d.add(mul_a_rb, ra);
    let lt_combined = d.lemma(
        p.lt_of_lt_of_le,
        &[add_mularb_ra, add_mularb_a, ab, step_lt, le2],
    ); // add mul_a_rb ra < ab

    let comm_bound = d.lemma(p.add_comm, &[mul_a_rb, ra]); // add mul_a_rb ra = add ra mul_a_rb
    let motive2 = d.eq_motive(add_mularb_ra, &|d, t| d.lt(t, ab));
    let bound_final = d.transport(add_mularb_ra, motive2, lt_combined, remainder, comm_bound);
    // bound_final : remainder < ab

    let eq_ty = d.eq(x, final_rhs);
    let bound_ty = d.lt(remainder, ab);
    let relation = d.const_app(p.logic.and_intro, &[eq_ty, bound_ty, eq_final, bound_final]);
    (relation, qb, remainder)
}

/// For positive `a`, `b`: `Eq (mod x (mul a b)) (add (mod x a) (mul a (mod
/// (div x a) b)))` -- `Nat.mod_mul`'s conclusion, unconditionally true once
/// both factors are positive (the degenerate cases are handled separately
/// at the call sites).
fn mod_mul_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    pos_a: ExprId,
    b: ExprId,
    pos_b: ExprId,
    x: ExprId,
) -> ExprId {
    let p = *p;
    let (relation, qb, remainder) = double_decompose(d, &p, a, pos_a, b, pos_b, x);
    let ab = d.mul(a, b);
    let pos_ab = d.lemma(p.one_le_mul, &[a, b, pos_a, pos_b]); // Lt zero (mul a b)
    let canonical = div_mod_reconstructed(d, &p, ab, pos_ab, x); // divMod ab x (div x ab) (mod x ab)
    let div_x_ab = d.div(x, ab);
    let mod_x_ab = d.modulo(x, ab);
    let both = d.lemma(
        p.div_mod_unique,
        &[ab, x, qb, remainder, div_x_ab, mod_x_ab, relation, canonical],
    );
    let q_eq_ty = d.eq(qb, div_x_ab);
    let r_eq_ty = d.eq(remainder, mod_x_ab);
    let r_eq = and_right(d, q_eq_ty, r_eq_ty, both); // remainder = mod x ab
    d.symm(remainder, mod_x_ab, r_eq) // mod x ab = remainder
}

/// `Eq (div val dvsr) zero`, given `pos_dvsr : Lt zero dvsr` and
/// `bound : Lt val dvsr`. Manufacture the trivial `divMod dvsr val zero val`
/// decomposition and compare it against the canonical one.
fn div_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    dvsr: ExprId,
    pos_dvsr: ExprId,
    val: ExprId,
    bound: ExprId,
) -> ExprId {
    let p = *p;
    let zero = d.zero();
    let mul_dvsr_zero = d.mul(dvsr, zero);
    let add_dvsrzero_val = d.add(mul_dvsr_zero, val);
    let mul_zero_pf = d.lemma(p.mul_zero, &[dvsr]); // mul dvsr zero = zero
    let step = d.congr(mul_dvsr_zero, zero, mul_zero_pf, &|d, v| d.add(v, val));
    let add_zero_val = d.add(zero, val);
    let zero_add_pf = d.lemma(p.zero_add, &[val]); // add zero val = val
    let (_, eq_pf) = d.chain(
        add_dvsrzero_val,
        &[(add_zero_val, step), (val, zero_add_pf)],
    );
    // eq_pf : add(mul dvsr zero, val) = val
    let manufactured_eq = d.symm(add_dvsrzero_val, val, eq_pf); // val = add(mul dvsr zero, val)
    let eq_ty = d.eq(val, add_dvsrzero_val);
    let bound_ty = d.lt(val, dvsr);
    let manufactured = d.const_app(p.logic.and_intro, &[eq_ty, bound_ty, manufactured_eq, bound]);

    let canonical = div_mod_reconstructed(d, &p, dvsr, pos_dvsr, val);
    let div_val_dvsr = d.div(val, dvsr);
    let mod_val_dvsr = d.modulo(val, dvsr);
    let both = d.lemma(
        p.div_mod_unique,
        &[dvsr, val, zero, val, div_val_dvsr, mod_val_dvsr, manufactured, canonical],
    );
    let q_eq_ty = d.eq(zero, div_val_dvsr);
    let r_eq_ty = d.eq(val, mod_val_dvsr);
    let q_eq = and_left(d, q_eq_ty, r_eq_ty, both); // zero = div val dvsr
    d.symm(zero, div_val_dvsr, q_eq) // div val dvsr = zero
}

/// For positive `dvsr` and `e = mul dvsr mult` (witnessed by `e_eq : Eq e
/// (mul dvsr mult)`, positive via `pos_e`): `Eq (mod (mod a e) dvsr) (mod a
/// dvsr)` -- if `e` is a multiple of `dvsr`, reducing modulo `e` first does
/// not change the further reduction modulo `dvsr`. See the module doc.
#[allow(clippy::too_many_arguments)]
fn mod_of_dvd_mod(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    dvsr: ExprId,
    pos_dvsr: ExprId,
    mult: ExprId,
    e: ExprId,
    e_eq: ExprId,
    pos_e: ExprId,
    a: ExprId,
) -> ExprId {
    let p = *p;

    // a = e*qe + re, re < e.
    let qe = d.div(a, e);
    let re = d.modulo(a, e);
    let exec_e = div_mod_reconstructed(d, &p, e, pos_e, a);
    let mul_e_qe = d.mul(e, qe);
    let sum_e = d.add(mul_e_qe, re);
    let eq_e_ty = d.eq(a, sum_e);
    let bound_e_ty = d.lt(re, e);
    let eq_e = and_left(d, eq_e_ty, bound_e_ty, exec_e); // a = mul e qe + re

    // re = dvsr*qd + rd, rd < dvsr. `rd` IS `mod (mod a e) dvsr` (re is
    // literally `mod a e`).
    let qd = d.div(re, dvsr);
    let rd = d.modulo(re, dvsr);
    let exec_d = div_mod_reconstructed(d, &p, dvsr, pos_dvsr, re);
    let mul_dvsr_qd = d.mul(dvsr, qd);
    let sum_d = d.add(mul_dvsr_qd, rd);
    let eq_d_ty = d.eq(re, sum_d);
    let bound_d_ty = d.lt(rd, dvsr);
    let eq_d = and_left(d, eq_d_ty, bound_d_ty, exec_d); // re = mul dvsr qd + rd
    let bound_d = and_right(d, eq_d_ty, bound_d_ty, exec_d); // rd < dvsr

    // a = mul e qe + re
    //   = mul e qe + (mul dvsr qd + rd)          [congr eq_d]
    //   = mul (mul dvsr mult) qe + (..)          [congr e_eq]
    //   = mul dvsr (mul mult qe) + (..)          [mul_assoc]
    //   = (mul dvsr (mul mult qe) + mul dvsr qd) + rd   [add_assoc, reversed]
    //   = mul dvsr (add (mul mult qe) qd) + rd    [left_distrib, reversed]
    let step1 = d.congr(re, sum_d, eq_d, &|d, v| {
        let me = d.mul(e, qe);
        d.add(me, v)
    });
    let after_step1 = d.add(mul_e_qe, sum_d);

    let dvsr_mult = d.mul(dvsr, mult);
    let mul_dvsrmult_qe = d.mul(dvsr_mult, qe);
    let step2 = d.congr(e, dvsr_mult, e_eq, &|d, v| {
        let m = d.mul(v, qe);
        d.add(m, sum_d)
    });
    let after_step2 = d.add(mul_dvsrmult_qe, sum_d);

    let mul_mult_qe = d.mul(mult, qe);
    let mul_dvsr_multqe = d.mul(dvsr, mul_mult_qe);
    let assoc = d.lemma(p.mul_assoc, &[dvsr, mult, qe]); // mul(mul dvsr mult) qe = mul dvsr (mul mult qe)
    let step3 = d.congr(mul_dvsrmult_qe, mul_dvsr_multqe, assoc, &|d, v| {
        d.add(v, sum_d)
    });
    let after_step3 = d.add(mul_dvsr_multqe, sum_d);

    let add_multqe_qd = d.add(mul_dvsr_multqe, mul_dvsr_qd);
    let before_assoc = d.add(add_multqe_qd, rd);
    let add_assoc_pf = d.lemma(p.add_assoc, &[mul_dvsr_multqe, mul_dvsr_qd, rd]);
    // Eq (add(add mul_dvsr_multqe mul_dvsr_qd) rd) (add mul_dvsr_multqe (add mul_dvsr_qd rd))
    let add_assoc_rev = d.symm(before_assoc, after_step3, add_assoc_pf);

    let distrib = d.lemma(p.left_distrib, &[dvsr, mul_mult_qe, qd]); // mul dvsr (add mul_mult_qe qd) = add(mul dvsr mul_mult_qe, mul dvsr qd)
    let sum_mult_qe_qd = d.add(mul_mult_qe, qd);
    let mul_dvsr_sum = d.mul(dvsr, sum_mult_qe_qd);
    let distrib_rev = d.symm(mul_dvsr_sum, add_multqe_qd, distrib);
    let step4 = d.congr(add_multqe_qd, mul_dvsr_sum, distrib_rev, &|d, v| {
        d.add(v, rd)
    });
    let final_rhs = d.add(mul_dvsr_sum, rd);

    let (_, eq_final) = d.chain(
        a,
        &[
            (sum_e, eq_e),
            (after_step1, step1),
            (after_step2, step2),
            (after_step3, step3),
            (before_assoc, add_assoc_rev),
            (final_rhs, step4),
        ],
    );
    // eq_final : a = mul dvsr sum_mult_qe_qd + rd

    let manufactured_eq_ty = d.eq(a, final_rhs);
    let manufactured_bound_ty = d.lt(rd, dvsr);
    let manufactured = d.const_app(
        p.logic.and_intro,
        &[manufactured_eq_ty, manufactured_bound_ty, eq_final, bound_d],
    );

    let canonical = div_mod_reconstructed(d, &p, dvsr, pos_dvsr, a);
    let div_a_dvsr = d.div(a, dvsr);
    let mod_a_dvsr = d.modulo(a, dvsr);
    let both = d.lemma(
        p.div_mod_unique,
        &[
            dvsr,
            a,
            sum_mult_qe_qd,
            rd,
            div_a_dvsr,
            mod_a_dvsr,
            manufactured,
            canonical,
        ],
    );
    let q_eq_ty = d.eq(sum_mult_qe_qd, div_a_dvsr);
    let r_eq_ty = d.eq(rd, mod_a_dvsr);
    and_right(d, q_eq_ty, r_eq_ty, both) // rd = mod a dvsr, i.e. mod (mod a e) dvsr = mod a dvsr
}

/// For positive `n`, `k`, and `e = mul n k` (witnessed by `e_eq : Eq e (mul n
/// k)`): `Eq (div (mod m e) n) (mod (div m n) k)`. See the module doc.
fn mod_mul_div_self(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    pos_n: ExprId,
    k: ExprId,
    pos_k: ExprId,
    m: ExprId,
    e: ExprId,
    e_eq: ExprId,
) -> ExprId {
    let p = *p;
    let nk = d.mul(n, k);
    let mod_m_e = d.modulo(m, e);
    let mod_m_nk = d.modulo(m, nk);
    let bridge = d.congr(e, nk, e_eq, &|d, v| d.modulo(m, v)); // mod m e = mod m nk

    let mod_eq = mod_mul_eq(d, &p, n, pos_n, k, pos_k, m); // mod m nk = add(mod m n, mul n (mod (div m n) k))
    let mod_m_n = d.modulo(m, n);
    let div_m_n = d.div(m, n);
    let z_val = d.modulo(div_m_n, k);
    let mul_n_z = d.mul(n, z_val);
    let rhs = d.add(mod_m_n, mul_n_z);

    let (_, eq1) = d.chain(mod_m_e, &[(mod_m_nk, bridge), (rhs, mod_eq)]);
    // eq1 : mod m e = add(mod m n, mul n z_val)

    let div_step = d.congr(mod_m_e, rhs, eq1, &|d, v| d.div(v, n));
    let div_rhs = d.div(rhs, n);
    // div_step : div(mod m e) n = div(rhs) n

    let add_div_pf = d.lemma(p.add_mul_div_left, &[mod_m_n, z_val, n, pos_n]);
    // div(add(mod_m_n, mul n z_val)) n = add(div mod_m_n n, z_val)
    let div_mod_m_n_n = d.div(mod_m_n, n);
    let sum_div = d.add(div_mod_m_n_n, z_val);

    let bound = d.lemma(p.mod_lt, &[m, n, pos_n]); // mod m n < n
    let div_zero_pf = div_of_lt(d, &p, n, pos_n, mod_m_n, bound); // div mod_m_n n = zero
    let zero = d.zero();
    let zero_add_pf = d.lemma(p.zero_add, &[z_val]); // add zero z_val = z_val
    let sum_step = d.congr(div_mod_m_n_n, zero, div_zero_pf, &|d, v| d.add(v, z_val));
    let add_zero_z = d.add(zero, z_val);
    let div_mod_m_e_n = d.div(mod_m_e, n);

    let (_, eq2) = d.chain(
        div_mod_m_e_n,
        &[
            (div_rhs, div_step),
            (sum_div, add_div_pf),
            (add_zero_z, sum_step),
            (z_val, zero_add_pf),
        ],
    );
    eq2 // div(mod m e) n = z_val = mod(div m n) k
}

/// Declare the five `ml430` `Nat` mod/mul mirrors. See the module doc.
///
/// Must run after `declare_euclidean_division` (`div_mod_unique`),
/// `declare_divisibility` (`div_mod_exec`, `one_le_mul`, `mod_lt`),
/// `declare_add_div_mod_shift_family` (`add_mul_div_left`),
/// `declare_succ_pred_of_pos`, and `declare_additive_theorems`/
/// `declare_multiplicative_theorems`/`declare_order`/`declare_order_more`
/// (`mul_assoc`/`left_distrib`/`add_assoc`/`add_comm`/`mul_succ`/
/// `mul_le_mul_left`/`add_lt_add_left`/`lt_of_lt_of_le`/`zero_mul`/`mul_zero`/
/// `add_zero`/`zero_add`/`mod_zero`/`div_zero`/`zero_mod`/`mul_comm`/
/// `zero_lt_succ`).
///
/// # Errors
///
/// Returns the kernel's rejection if a generated declaration does not
/// type-check or a name is already taken.
pub(super) fn declare_mod_mul_family(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // mod_mul : ∀ a b x, x % (a*b) = x%a + a*(x/a % b).
    d.theorem(p.mod_mul, 3, &|d, v| {
        let (a, b, x) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, aa: ExprId| -> ExprId {
            let ab = d.mul(aa, b);
            let lhs = d.modulo(x, ab);
            let ra = d.modulo(x, aa);
            let qa = d.div(x, aa);
            let rb = d.modulo(qa, b);
            let mul_aa_rb = d.mul(aa, rb);
            let rhs = d.add(ra, mul_aa_rb);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, a);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let zero_mul_b = d.lemma(p.zero_mul, &[b]); // mul zero b = zero
            let ab = d.mul(zero, b);
            let lhs = d.modulo(x, ab);
            let mod_x_zero = d.modulo(x, zero);
            let lhs_step = d.congr(ab, zero, zero_mul_b, &|d, v| d.modulo(x, v));
            let mod_zero_x = d.lemma(p.mod_zero, &[x]); // mod x zero = x
            let (_, lhs_eq) = d.chain(lhs, &[(mod_x_zero, lhs_step), (x, mod_zero_x)]);

            let qa0 = d.div(x, zero);
            let rb0 = d.modulo(qa0, b);
            let mul_zero_rb0 = d.mul(zero, rb0);
            let ra0 = d.modulo(x, zero);
            let rhs = d.add(ra0, mul_zero_rb0);
            let add_ra0_zero = d.add(ra0, zero);
            let zero_mul_rb0 = d.lemma(p.zero_mul, &[rb0]); // mul zero rb0 = zero
            let rhs_step = d.congr(mul_zero_rb0, zero, zero_mul_rb0, &|d, v| d.add(ra0, v));
            let add_zero_ra0 = d.lemma(p.add_zero, &[ra0]); // add ra0 zero = ra0
            let ra0_eq_x = d.lemma(p.mod_zero, &[x]); // mod x zero = x (ra0 IS mod x zero)
            let (_, rhs_eq) = d.chain(
                rhs,
                &[(add_ra0_zero, rhs_step), (ra0, add_zero_ra0), (x, ra0_eq_x)],
            );
            let x_eq_rhs = d.symm(rhs, x, rhs_eq);
            d.trans(lhs, x, rhs, lhs_eq, x_eq_rhs)
        };

        let at_succ = |d: &mut NatDev<'_>, apred: ExprId| -> ExprId {
            let a = d.succ(apred);
            let pos_a = d.lemma(p.zero_lt_succ, &[apred]);

            let motive_b = |d: &mut NatDev<'_>, bb: ExprId| -> ExprId {
                let ab = d.mul(a, bb);
                let lhs = d.modulo(x, ab);
                let ra = d.modulo(x, a);
                let qa = d.div(x, a);
                let rb = d.modulo(qa, bb);
                let mul_a_rb = d.mul(a, rb);
                let rhs = d.add(ra, mul_a_rb);
                d.eq(lhs, rhs)
            };
            let stmt_b = motive_b(d, b);
            let _ = &stmt_b;

            let at_zero_b = |d: &mut NatDev<'_>| -> ExprId {
                let zero = d.zero();
                let mul_a_zero = d.lemma(p.mul_zero, &[a]); // mul a zero = zero
                let ab = d.mul(a, zero);
                let lhs = d.modulo(x, ab);
                let mod_x_zero = d.modulo(x, zero);
                let lhs_step = d.congr(ab, zero, mul_a_zero, &|d, v| d.modulo(x, v));
                let mod_zero_x = d.lemma(p.mod_zero, &[x]); // mod x zero = x
                let (_, lhs_eq) = d.chain(lhs, &[(mod_x_zero, lhs_step), (x, mod_zero_x)]);

                let ra = d.modulo(x, a);
                let qa = d.div(x, a);
                let rb0 = d.modulo(qa, zero);
                let mul_a_rb0 = d.mul(a, rb0);
                let rhs = d.add(ra, mul_a_rb0);
                let mod_zero_qa = d.lemma(p.mod_zero, &[qa]); // mod qa zero = qa
                let rhs_step1 = d.congr(rb0, qa, mod_zero_qa, &|d, v| {
                    let m = d.mul(a, v);
                    d.add(ra, m)
                });
                let mul_a_qa = d.mul(a, qa);
                let add_ra_mulaqa = d.add(ra, mul_a_qa);

                let exec_a = div_mod_reconstructed(d, &p, a, pos_a, x);
                let sum_a = d.add(mul_a_qa, ra);
                let eq_a_ty = d.eq(x, sum_a);
                let bound_a_ty = d.lt(ra, a);
                let eq_a = and_left(d, eq_a_ty, bound_a_ty, exec_a); // x = mul a qa + ra
                let comm = d.lemma(p.add_comm, &[mul_a_qa, ra]); // mul_a_qa+ra = ra+mul_a_qa
                let (_, sum_eq_addcomm) = d.chain(sum_a, &[(add_ra_mulaqa, comm)]);
                let x_eq_addracomm = d.trans(x, sum_a, add_ra_mulaqa, eq_a, sum_eq_addcomm);
                // x = ra + mul_a_qa
                let addracomm_eq_x = d.symm(x, add_ra_mulaqa, x_eq_addracomm);

                let (_, rhs_eq) = d.chain(
                    rhs,
                    &[(add_ra_mulaqa, rhs_step1), (x, addracomm_eq_x)],
                );
                let x_eq_rhs = d.symm(rhs, x, rhs_eq);
                d.trans(lhs, x, rhs, lhs_eq, x_eq_rhs)
            };

            let at_succ_b = |d: &mut NatDev<'_>, bpred: ExprId| -> ExprId {
                let b = d.succ(bpred);
                let pos_b = d.lemma(p.zero_lt_succ, &[bpred]);
                mod_mul_eq(d, &p, a, pos_a, b, pos_b, x)
            };
            cases_zero_succ(d, b, &motive_b, &at_zero_b, &at_succ_b)
        };
        let proof = cases_zero_succ(d, a, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    // mod_mul_left_mod : ∀ a b c, a % (b*c) % c = a % c.
    d.theorem(p.mod_mul_left_mod, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, cc: ExprId| -> ExprId {
            let bc = d.mul(b, cc);
            let mod_a_bc = d.modulo(a, bc);
            let lhs = d.modulo(mod_a_bc, cc);
            let rhs = d.modulo(a, cc);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, c);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let mul_b_zero = d.lemma(p.mul_zero, &[b]); // mul b zero = zero
            let bc = d.mul(b, zero);
            let mod_a_bc = d.modulo(a, bc);
            let lhs = d.modulo(mod_a_bc, zero);
            let step1 = d.congr(bc, zero, mul_b_zero, &|d, v| {
                let inner = d.modulo(a, v);
                d.modulo(inner, zero)
            });
            let mod_a_zero = d.modulo(a, zero);
            let after1 = d.modulo(mod_a_zero, zero);
            let mod_zero_a = d.lemma(p.mod_zero, &[a]); // mod a zero = a
            // step2 : Eq (mod mod_a_zero zero) (mod a zero) = Eq(after1, mod_a_zero)
            let step2 = d.congr(mod_a_zero, a, mod_zero_a, &|d, v| d.modulo(v, zero));
            // final step reuses mod_zero_a: mod_a_zero = a.
            let (_, lhs_eq) = d.chain(lhs, &[(after1, step1), (mod_a_zero, step2), (a, mod_zero_a)]);
            // lhs_eq : Eq lhs a; rhs (motive at zero) is `mod_a_zero`, so bridge via mod_zero_a reversed.
            let a_eq_mod_a_zero = d.symm(mod_a_zero, a, mod_zero_a);
            d.trans(lhs, a, mod_a_zero, lhs_eq, a_eq_mod_a_zero)
        };

        let at_succ = |d: &mut NatDev<'_>, cpred: ExprId| -> ExprId {
            let c = d.succ(cpred);
            let pos_c = d.lemma(p.zero_lt_succ, &[cpred]);

            let motive_b = |d: &mut NatDev<'_>, bb: ExprId| -> ExprId {
                let bc = d.mul(bb, c);
                let mod_a_bc = d.modulo(a, bc);
                let lhs = d.modulo(mod_a_bc, c);
                let rhs = d.modulo(a, c);
                d.eq(lhs, rhs)
            };
            let stmt_b = motive_b(d, b);
            let _ = &stmt_b;

            let at_zero_b = |d: &mut NatDev<'_>| -> ExprId {
                let zero = d.zero();
                let zero_mul_c = d.lemma(p.zero_mul, &[c]); // mul zero c = zero
                let bc = d.mul(zero, c);
                let mod_a_bc = d.modulo(a, bc);
                let lhs = d.modulo(mod_a_bc, c);
                let step1 = d.congr(bc, zero, zero_mul_c, &|d, v| {
                    let inner = d.modulo(a, v);
                    d.modulo(inner, c)
                });
                let mod_a_zero = d.modulo(a, zero);
                let after1 = d.modulo(mod_a_zero, c);
                let mod_zero_a = d.lemma(p.mod_zero, &[a]); // mod a zero = a
                let step2 = d.congr(mod_a_zero, a, mod_zero_a, &|d, v| d.modulo(v, c));
                let mod_a_c = d.modulo(a, c);
                let (_, lhs_eq) = d.chain(lhs, &[(after1, step1), (mod_a_c, step2)]);
                lhs_eq
            };

            let at_succ_b = |d: &mut NatDev<'_>, bpred: ExprId| -> ExprId {
                let b = d.succ(bpred);
                let pos_b = d.lemma(p.zero_lt_succ, &[bpred]);
                let bc = d.mul(b, c);
                let e_eq = d.lemma(p.mul_comm, &[b, c]); // mul b c = mul c b
                let pos_e = d.lemma(p.one_le_mul, &[b, c, pos_b, pos_c]); // Lt zero (mul b c)
                mod_of_dvd_mod(d, &p, c, pos_c, b, bc, e_eq, pos_e, a)
            };
            cases_zero_succ(d, b, &motive_b, &at_zero_b, &at_succ_b)
        };
        let proof = cases_zero_succ(d, c, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    // mod_mul_right_mod : ∀ a b c, a % (b*c) % b = a % b.
    d.theorem(p.mod_mul_right_mod, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, bb: ExprId| -> ExprId {
            let bc = d.mul(bb, c);
            let mod_a_bc = d.modulo(a, bc);
            let lhs = d.modulo(mod_a_bc, bb);
            let rhs = d.modulo(a, bb);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, b);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let zero_mul_c = d.lemma(p.zero_mul, &[c]); // mul zero c = zero
            let bc = d.mul(zero, c);
            let mod_a_bc = d.modulo(a, bc);
            let lhs = d.modulo(mod_a_bc, zero);
            let step1 = d.congr(bc, zero, zero_mul_c, &|d, v| {
                let inner = d.modulo(a, v);
                d.modulo(inner, zero)
            });
            let mod_a_zero = d.modulo(a, zero);
            let after1 = d.modulo(mod_a_zero, zero);
            let mod_zero_ma = d.lemma(p.mod_zero, &[mod_a_zero]); // mod (mod a zero) zero = mod a zero
            let (_, lhs_eq) = d.chain(lhs, &[(after1, step1), (mod_a_zero, mod_zero_ma)]);
            lhs_eq
        };

        let at_succ = |d: &mut NatDev<'_>, bpred: ExprId| -> ExprId {
            let b = d.succ(bpred);
            let pos_b = d.lemma(p.zero_lt_succ, &[bpred]);

            let motive_c = |d: &mut NatDev<'_>, cc: ExprId| -> ExprId {
                let bc = d.mul(b, cc);
                let mod_a_bc = d.modulo(a, bc);
                let lhs = d.modulo(mod_a_bc, b);
                let rhs = d.modulo(a, b);
                d.eq(lhs, rhs)
            };
            let stmt_c = motive_c(d, c);
            let _ = &stmt_c;

            let at_zero_c = |d: &mut NatDev<'_>| -> ExprId {
                let zero = d.zero();
                let mul_b_zero = d.lemma(p.mul_zero, &[b]); // mul b zero = zero
                let bc = d.mul(b, zero);
                let mod_a_bc = d.modulo(a, bc);
                let lhs = d.modulo(mod_a_bc, b);
                let step1 = d.congr(bc, zero, mul_b_zero, &|d, v| {
                    let inner = d.modulo(a, v);
                    d.modulo(inner, b)
                });
                let mod_a_zero = d.modulo(a, zero);
                let after1 = d.modulo(mod_a_zero, b);
                let mod_zero_a = d.lemma(p.mod_zero, &[a]); // mod a zero = a
                let step2 = d.congr(mod_a_zero, a, mod_zero_a, &|d, v| d.modulo(v, b));
                let mod_a_b = d.modulo(a, b);
                let (_, lhs_eq) = d.chain(lhs, &[(after1, step1), (mod_a_b, step2)]);
                lhs_eq
            };

            let at_succ_c = |d: &mut NatDev<'_>, cpred: ExprId| -> ExprId {
                let c = d.succ(cpred);
                let pos_c = d.lemma(p.zero_lt_succ, &[cpred]);
                let bc = d.mul(b, c);
                let e_eq = d.refl(bc); // mul b c = mul b c
                let pos_e = d.lemma(p.one_le_mul, &[b, c, pos_b, pos_c]); // Lt zero (mul b c)
                mod_of_dvd_mod(d, &p, b, pos_b, c, bc, e_eq, pos_e, a)
            };
            cases_zero_succ(d, c, &motive_c, &at_zero_c, &at_succ_c)
        };
        let proof = cases_zero_succ(d, b, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    // mod_mul_left_div_self : ∀ m n k, m % (k*n) / n = m/n % k.
    d.theorem(p.mod_mul_left_div_self, 3, &|d, v| {
        let (m, n, k) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, nn: ExprId| -> ExprId {
            let kn = d.mul(k, nn);
            let mod_m_kn = d.modulo(m, kn);
            let lhs = d.div(mod_m_kn, nn);
            let div_m_nn = d.div(m, nn);
            let rhs = d.modulo(div_m_nn, k);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let mul_k_zero = d.lemma(p.mul_zero, &[k]); // mul k zero = zero
            let kn = d.mul(k, zero);
            let mod_m_kn = d.modulo(m, kn);
            let lhs = d.div(mod_m_kn, zero);
            let step1 = d.congr(kn, zero, mul_k_zero, &|d, v| {
                let inner = d.modulo(m, v);
                d.div(inner, zero)
            });
            let mod_m_zero = d.modulo(m, zero);
            let after1 = d.div(mod_m_zero, zero);
            let mod_zero_m = d.lemma(p.mod_zero, &[m]); // mod m zero = m
            let step2 = d.congr(mod_m_zero, m, mod_zero_m, &|d, v| d.div(v, zero));
            let div_m_zero = d.div(m, zero);
            let div_zero_m = d.lemma(p.div_zero, &[m]); // div m zero = zero
            let (_, lhs_eq) = d.chain(
                lhs,
                &[(after1, step1), (div_m_zero, step2), (zero, div_zero_m)],
            );

            let div_zero_m2 = d.lemma(p.div_zero, &[m]); // div m zero = zero
            let mod_div_m_zero_k = d.modulo(div_m_zero, k);
            let step3 = d.congr(div_m_zero, zero, div_zero_m2, &|d, v| d.modulo(v, k));
            let mod_zero_k = d.modulo(zero, k);
            let zero_mod_k = d.lemma(p.zero_mod, &[k]); // mod zero k = zero
            let (_, rhs_eq) = d.chain(mod_div_m_zero_k, &[(mod_zero_k, step3), (zero, zero_mod_k)]);

            let rhs_eq_rev = d.symm(mod_div_m_zero_k, zero, rhs_eq);
            d.trans(lhs, zero, mod_div_m_zero_k, lhs_eq, rhs_eq_rev)
        };

        let at_succ = |d: &mut NatDev<'_>, npred: ExprId| -> ExprId {
            let n = d.succ(npred);
            let pos_n = d.lemma(p.zero_lt_succ, &[npred]);

            let motive_k = |d: &mut NatDev<'_>, kk: ExprId| -> ExprId {
                let kn = d.mul(kk, n);
                let mod_m_kn = d.modulo(m, kn);
                let lhs = d.div(mod_m_kn, n);
                let div_m_n = d.div(m, n);
                let rhs = d.modulo(div_m_n, kk);
                d.eq(lhs, rhs)
            };
            let stmt_k = motive_k(d, k);
            let _ = &stmt_k;

            let at_zero_k = |d: &mut NatDev<'_>| -> ExprId {
                let zero = d.zero();
                let zero_mul_n = d.lemma(p.zero_mul, &[n]); // mul zero n = zero
                let kn = d.mul(zero, n);
                let mod_m_kn = d.modulo(m, kn);
                let lhs = d.div(mod_m_kn, n);
                let step1 = d.congr(kn, zero, zero_mul_n, &|d, v| {
                    let inner = d.modulo(m, v);
                    d.div(inner, n)
                });
                let mod_m_zero = d.modulo(m, zero);
                let after1 = d.div(mod_m_zero, n);
                let mod_zero_m = d.lemma(p.mod_zero, &[m]); // mod m zero = m
                let step2 = d.congr(mod_m_zero, m, mod_zero_m, &|d, v| d.div(v, n));
                let div_m_n = d.div(m, n);
                let mod_div_m_n_zero = d.modulo(div_m_n, zero);
                let mod_zero_divmn = d.lemma(p.mod_zero, &[div_m_n]); // mod (div m n) zero = div m n
                let (_, lhs_eq) = d.chain(lhs, &[(after1, step1), (div_m_n, step2)]);
                let mod_zero_divmn_rev = d.symm(mod_div_m_n_zero, div_m_n, mod_zero_divmn);
                d.trans(lhs, div_m_n, mod_div_m_n_zero, lhs_eq, mod_zero_divmn_rev)
            };

            let at_succ_k = |d: &mut NatDev<'_>, kpred: ExprId| -> ExprId {
                let k = d.succ(kpred);
                let pos_k = d.lemma(p.zero_lt_succ, &[kpred]);
                let kn = d.mul(k, n);
                let e_eq = d.lemma(p.mul_comm, &[k, n]); // mul k n = mul n k
                mod_mul_div_self(d, &p, n, pos_n, k, pos_k, m, kn, e_eq)
            };
            cases_zero_succ(d, k, &motive_k, &at_zero_k, &at_succ_k)
        };
        let proof = cases_zero_succ(d, n, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    // mod_mul_right_div_self : ∀ m n k, m % (n*k) / n = m/n % k.
    d.theorem(p.mod_mul_right_div_self, 3, &|d, v| {
        let (m, n, k) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, nn: ExprId| -> ExprId {
            let nk = d.mul(nn, k);
            let mod_m_nk = d.modulo(m, nk);
            let lhs = d.div(mod_m_nk, nn);
            let div_m_nn = d.div(m, nn);
            let rhs = d.modulo(div_m_nn, k);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let zero_mul_k = d.lemma(p.zero_mul, &[k]); // mul zero k = zero
            let nk = d.mul(zero, k);
            let mod_m_nk = d.modulo(m, nk);
            let lhs = d.div(mod_m_nk, zero);
            let step1 = d.congr(nk, zero, zero_mul_k, &|d, v| {
                let inner = d.modulo(m, v);
                d.div(inner, zero)
            });
            let mod_m_zero = d.modulo(m, zero);
            let after1 = d.div(mod_m_zero, zero);
            let mod_zero_m = d.lemma(p.mod_zero, &[m]); // mod m zero = m
            let step2 = d.congr(mod_m_zero, m, mod_zero_m, &|d, v| d.div(v, zero));
            let div_m_zero = d.div(m, zero);
            let div_zero_m = d.lemma(p.div_zero, &[m]); // div m zero = zero
            let (_, lhs_eq) = d.chain(
                lhs,
                &[(after1, step1), (div_m_zero, step2), (zero, div_zero_m)],
            );

            let div_zero_m2 = d.lemma(p.div_zero, &[m]); // div m zero = zero
            let mod_div_m_zero_k = d.modulo(div_m_zero, k);
            let step3 = d.congr(div_m_zero, zero, div_zero_m2, &|d, v| d.modulo(v, k));
            let mod_zero_k = d.modulo(zero, k);
            let zero_mod_k = d.lemma(p.zero_mod, &[k]); // mod zero k = zero
            let (_, rhs_eq) = d.chain(mod_div_m_zero_k, &[(mod_zero_k, step3), (zero, zero_mod_k)]);

            let rhs_eq_rev = d.symm(mod_div_m_zero_k, zero, rhs_eq);
            d.trans(lhs, zero, mod_div_m_zero_k, lhs_eq, rhs_eq_rev)
        };

        let at_succ = |d: &mut NatDev<'_>, npred: ExprId| -> ExprId {
            let n = d.succ(npred);
            let pos_n = d.lemma(p.zero_lt_succ, &[npred]);

            let motive_k = |d: &mut NatDev<'_>, kk: ExprId| -> ExprId {
                let nk = d.mul(n, kk);
                let mod_m_nk = d.modulo(m, nk);
                let lhs = d.div(mod_m_nk, n);
                let div_m_n = d.div(m, n);
                let rhs = d.modulo(div_m_n, kk);
                d.eq(lhs, rhs)
            };
            let stmt_k = motive_k(d, k);
            let _ = &stmt_k;

            let at_zero_k = |d: &mut NatDev<'_>| -> ExprId {
                let zero = d.zero();
                let mul_n_zero = d.lemma(p.mul_zero, &[n]); // mul n zero = zero
                let nk = d.mul(n, zero);
                let mod_m_nk = d.modulo(m, nk);
                let lhs = d.div(mod_m_nk, n);
                let step1 = d.congr(nk, zero, mul_n_zero, &|d, v| {
                    let inner = d.modulo(m, v);
                    d.div(inner, n)
                });
                let mod_m_zero = d.modulo(m, zero);
                let after1 = d.div(mod_m_zero, n);
                let mod_zero_m = d.lemma(p.mod_zero, &[m]); // mod m zero = m
                let step2 = d.congr(mod_m_zero, m, mod_zero_m, &|d, v| d.div(v, n));
                let div_m_n = d.div(m, n);
                let mod_div_m_n_zero = d.modulo(div_m_n, zero);
                let mod_zero_divmn = d.lemma(p.mod_zero, &[div_m_n]); // mod (div m n) zero = div m n
                let (_, lhs_eq) = d.chain(lhs, &[(after1, step1), (div_m_n, step2)]);
                let mod_zero_divmn_rev = d.symm(mod_div_m_n_zero, div_m_n, mod_zero_divmn);
                d.trans(lhs, div_m_n, mod_div_m_n_zero, lhs_eq, mod_zero_divmn_rev)
            };

            let at_succ_k = |d: &mut NatDev<'_>, kpred: ExprId| -> ExprId {
                let k = d.succ(kpred);
                let pos_k = d.lemma(p.zero_lt_succ, &[kpred]);
                let nk = d.mul(n, k);
                let e_eq = d.refl(nk); // mul n k = mul n k
                mod_mul_div_self(d, &p, n, pos_n, k, pos_k, m, nk, e_eq)
            };
            cases_zero_succ(d, k, &motive_k, &at_zero_k, &at_succ_k)
        };
        let proof = cases_zero_succ(d, n, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    Ok(())
}
