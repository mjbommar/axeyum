//! `ml430` mirrors for `Nat` divisibility/gcd facts that are cheap
//! compositions of already-proved lemmas.
//!
//! Every theorem here is either a direct rearrangement of an existing
//! `nat_prelude/gcd.rs` / `nat_prelude/divisibility.rs` lemma (commutativity
//! transport, a case split extending an existing positive-divisor lemma to
//! the zero corner) or a small new argument built from `gcd_dvd_left`/
//! `gcd_dvd_right`/`dvd_mul`/`dvd_mul_right_of_dvd`. No new induction
//! principle or algorithm is introduced.

use super::NatPrelude;
use super::helpers::{transport_dvd_left, transport_dvd_right};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::proof_plan::{self, Template};

/// `dvd(zero, x) -> eq(x, zero)`. `dvd 0 x` unfolds to `∃ q, x = 0*q`;
/// eliminate the witness and collapse `0*q` with `zero_mul`.
fn zero_dvd_elim(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, proof: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let zero = d.zero();
    let dvd_ty = d.dvd(zero, x);
    let target = d.eq(x, zero);
    let pred = d.dvd_predicate(zero, x);
    let motive = d.kernel().lam(anon, dvd_ty, target, BinderInfo::Default);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let mul_zero_q = d.mul(zero, q);
        let heq_ty = d.eq(x, mul_zero_q);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let zm = d.lemma(p.zero_mul, &[q]); // eq(mul(zero,q), zero)
        let xz = d.trans(x, mul_zero_q, zero, heq, zm);
        let with_heq = d.lam_fv(heq_fv, heq_ty, xz);
        d.lam_fv(q_fv, nat, with_heq)
    };
    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(exists_rec, &[nat, pred, motive, minor, proof])
}

/// The `Eq -> Iff` lift, the `Iff` chain, and the `Iff` flip below used to be
/// local `pred_iff_of_eq`/`iff_trans`/`iff_symm` copies (the same three this
/// file's sibling `gcd_mul_right_mirrors.rs` and `dvd_add_iff_left.rs` also
/// carried by hand); they now go through [`crate::proof_plan`] (L3 D5)
/// instead, which builds the identical term shape — see
/// `proof_plan::tests::rewrite_iff_matches_pred_iff_of_eq`.
///
/// Declare the `ml430` gcd/divisibility mirrors that are cheap compositions
/// of `declare_divisibility`/`declare_gcd_semantics`/`declare_lcm_gcd_lemmas`
/// output. Must run after all three (needs `dvd_gcd`, `dvd_gcd_iff`,
/// `gcd_dvd_left`, `gcd_dvd_right`, `dvd_mul`, `dvd_mul_right_of_dvd`,
/// `dvd_mod_iff`, `div_mul_cancel_of_dvd`, `div_mod_remainder_eq_zero_iff_dvd`,
/// `div_mod_exec`, `zero_mul`, `mul_zero`, `mul_comm`, `zero_le`,
/// `le_succ_succ`).
///
/// # Errors
///
/// Returns the kernel's rejection if any declaration fails to check.
pub(super) fn declare_gcd_dvd_mirrors(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // `Nat.dvd_mul_left : ∀ a b, dvd a (mul b a)` — `F:ml430-nat-dvd-mul-left-a1a8a4b8`.
    // `dvd_mul(a,b) : dvd a (mul a b)`, transported along `mul_comm a b`.
    d.theorem(p.dvd_mul_left, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let base = d.lemma(p.dvd_mul, &[a, b]); // dvd(a, mul(a,b))
        let mc = d.lemma(p.mul_comm, &[a, b]); // eq(mul(a,b), mul(b,a))
        let ab = d.mul(a, b);
        let ba = d.mul(b, a);
        let result = transport_dvd_right(d, a, ab, ba, mc, base);
        (d.dvd(a, ba), result)
    })?;

    // `Nat.dvd_mul_left_of_dvd : ∀ a b c, dvd a b -> dvd a (mul c b)` —
    // `F:ml430-nat-dvd-mul-left-of-dvd-200e20a4`. `dvd_mul_right_of_dvd`
    // gives `dvd a (mul b c)`; transport along `mul_comm b c`.
    d.theorem(p.dvd_mul_left_of_dvd, 3, &|d, values| {
        let (a, b, c) = (values[0], values[1], values[2]);
        let divides_ty = d.dvd(a, b);
        let divides_fv = d.fresh_fvar();
        let divides = d.kernel().fvar(divides_fv);
        let base = d.lemma(p.dvd_mul_right_of_dvd, &[a, b, c, divides]); // dvd(a, mul(b,c))
        let mc = d.lemma(p.mul_comm, &[b, c]); // eq(mul(b,c), mul(c,b))
        let bc = d.mul(b, c);
        let cb = d.mul(c, b);
        let result = transport_dvd_right(d, a, bc, cb, mc, base);
        let concl = d.dvd(a, cb);
        let proof = d.lam_fv(divides_fv, divides_ty, result);
        (d.arrow(divides_ty, concl), proof)
    })?;

    // `Nat.eq_zero_of_gcd_eq_zero_left : ∀ m n, eq (gcd m n) zero -> eq m zero`
    // — `F:ml430-nat-eq-zero-of-gcd-eq-zero-left-72cc4246`. `gcd m n` divides
    // `m`; transport that divisibility along the hypothesis to `dvd 0 m`,
    // then `zero_dvd_elim`.
    d.theorem(p.eq_zero_of_gcd_eq_zero_left, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let common = d.gcd(m, n);
        let zero = d.zero();
        let hyp_ty = d.eq(common, zero);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let gdl = d.lemma(p.gcd_dvd_left, &[m, n]); // dvd(common, m)
        let dvd0m = transport_dvd_left(d, common, zero, hyp, m, gdl); // dvd(zero, m)
        let result = zero_dvd_elim(d, &p, m, dvd0m); // eq(m, zero)
        let proof = d.lam_fv(hyp_fv, hyp_ty, result);
        let concl_ty = d.eq(m, zero);
        (d.arrow(hyp_ty, concl_ty), proof)
    })?;

    // `Nat.eq_zero_of_gcd_eq_zero_right : ∀ m n, eq (gcd m n) zero -> eq n zero`
    // — `F:ml430-nat-eq-zero-of-gcd-eq-zero-right-24054a86`. Mirror of the
    // above via `gcd_dvd_right`.
    d.theorem(p.eq_zero_of_gcd_eq_zero_right, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let common = d.gcd(m, n);
        let zero = d.zero();
        let hyp_ty = d.eq(common, zero);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let gdr = d.lemma(p.gcd_dvd_right, &[m, n]); // dvd(common, n)
        let dvd0n = transport_dvd_left(d, common, zero, hyp, n, gdr); // dvd(zero, n)
        let result = zero_dvd_elim(d, &p, n, dvd0n); // eq(n, zero)
        let proof = d.lam_fv(hyp_fv, hyp_ty, result);
        let concl_ty = d.eq(n, zero);
        (d.arrow(hyp_ty, concl_ty), proof)
    })?;

    // `Nat.dvd_mod_iff_gen : ∀ k m n, dvd k n -> (dvd k (mod m n) <-> dvd k m)`
    // — `F:ml430-nat-dvd-mod-iff-2d082f10`, the full-generality (all `n`,
    // including zero) form of the existing `dvd_mod_iff` (which only covers
    // positive `n`, represented as a successor). Case split on `n`:
    // `n = 0` collapses `mod m 0` to `m` (`mod_zero`) so the goal is a
    // reflexive `Iff`; `n = succ j` is exactly the existing `dvd_mod_iff`
    // applied at `(k, j, m)`.
    d.theorem(p.dvd_mod_iff_gen, 3, &|d, values| {
        let (k, m, n) = (values[0], values[1], values[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let dvd_k_x = d.dvd(k, x);
            let modmx = d.modulo(m, x);
            let dvd_k_modmx = d.dvd(k, modmx);
            let dvd_k_m = d.dvd(k, m);
            let inner = d.const_app(p.logic.iff, &[dvd_k_modmx, dvd_k_m]);
            d.arrow(dvd_k_x, inner)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let dvd_k_zero_ty = d.dvd(k, zero);
                let hyp_fv = d.fresh_fvar();
                let modm0 = d.modulo(m, zero);
                let mod_zero_m = d.lemma(p.mod_zero, &[m]); // eq(mod(m,0), m)
                let ctx = Template::App(p.dvd, vec![Template::Fixed(k), Template::Hole]);
                let iff_proof = proof_plan::iff_lift(d, ctx, modm0, m, mod_zero_m);
                d.lam_fv(hyp_fv, dvd_k_zero_ty, iff_proof)
            },
            &|d, j, _ih| d.lemma(p.dvd_mod_iff, &[k, j, m]),
            n,
        );
        (stmt, proof)
    })?;

    // `Nat.div_mul_cancel : ∀ n m, dvd n m -> eq (mul (div m n) n) m` —
    // `F:ml430-nat-div-mul-cancel-99799a00`, the full-generality (all `n`)
    // form of `div_mul_cancel_of_dvd` (positive `n` only) with the factors
    // commuted to match Mathlib's `m / n * n = m` order. `n = 0`: `dvd 0 m`
    // forces `m = 0` and both sides collapse to `zero`. `n = succ j`: the
    // existing lemma plus `mul_comm`.
    d.theorem(p.div_mul_cancel, 2, &|d, values| {
        let (n, m) = (values[0], values[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let divides_ty = d.dvd(x, m);
            let quotient = d.div(m, x);
            let product = d.mul(quotient, x);
            let concl = d.eq(product, m);
            d.arrow(divides_ty, concl)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let divides_ty = d.dvd(zero, m);
                let divides_fv = d.fresh_fvar();
                let divides = d.kernel().fvar(divides_fv);
                let m_eq_zero = zero_dvd_elim(d, &p, m, divides); // eq(m, zero)
                let quotient = d.div(m, zero);
                let product = d.mul(quotient, zero);
                let mul_zero_q = d.lemma(p.mul_zero, &[quotient]); // eq(product, zero)
                let m_eq_zero_symm = d.symm(m, zero, m_eq_zero); // eq(zero, m)
                let result = d.trans(product, zero, m, mul_zero_q, m_eq_zero_symm);
                d.lam_fv(divides_fv, divides_ty, result)
            },
            &|d, j, _ih| {
                let succ_j = d.succ(j);
                let zero = d.zero();
                let zero_le_j = d.lemma(p.zero_le, &[j]); // le(0,j)
                let positive = d.lemma(p.le_succ_succ, &[zero, j, zero_le_j]); // le(1, succ_j)
                let divides_ty = d.dvd(succ_j, m);
                let divides_fv = d.fresh_fvar();
                let divides = d.kernel().fvar(divides_fv);
                let cancel = d.lemma(p.div_mul_cancel_of_dvd, &[succ_j, m, positive, divides]);
                // cancel : eq(mul(succ_j, div(m,succ_j)), m)
                let quotient = d.div(m, succ_j);
                let lhs = d.mul(succ_j, quotient);
                let rhs = d.mul(quotient, succ_j);
                let mc = d.lemma(p.mul_comm, &[succ_j, quotient]); // eq(lhs, rhs)
                let mc_symm = d.symm(lhs, rhs, mc); // eq(rhs, lhs)
                let flipped = d.trans(rhs, lhs, m, mc_symm, cancel); // eq(rhs, m)
                d.lam_fv(divides_fv, divides_ty, flipped)
            },
            n,
        );
        (stmt, proof)
    })?;

    // `Nat.dvd_iff_mod_eq_zero : ∀ m n, dvd m n <-> eq (mod n m) zero` —
    // `F:ml430-nat-dvd-iff-mod-eq-zero-d795bfff`. Case split on `m`:
    // `m = 0` reduces both sides to `eq n zero` (`mod_zero`, and `0 ∣ n ↔ n
    // = 0` built directly); `m = succ j` specializes the existing
    // `div_mod_remainder_eq_zero_iff_dvd` at the executable witness
    // (`div_mod_exec`) and flips the `Iff` order.
    d.theorem(p.dvd_iff_mod_eq_zero, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let dvd_x_n = d.dvd(x, n);
            let modnx = d.modulo(n, x);
            let zero = d.zero();
            let rhs = d.eq(modnx, zero);
            d.const_app(p.logic.iff, &[dvd_x_n, rhs])
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let dvd_0_n = d.dvd(zero, n);
                let n_eq_zero = d.eq(n, zero);
                // iff_b : Iff (dvd 0 n) (eq n 0)
                let iff_b = {
                    let forward = {
                        let divides_fv = d.fresh_fvar();
                        let divides = d.kernel().fvar(divides_fv);
                        let result = zero_dvd_elim(d, &p, n, divides);
                        d.lam_fv(divides_fv, dvd_0_n, result)
                    };
                    let reverse = {
                        let heq_fv = d.fresh_fvar();
                        let heq = d.kernel().fvar(heq_fv);
                        let nat = d.nat_ty();
                        let one = d.level_one();
                        let pred = d.dvd_predicate(zero, n);
                        let zz = d.mul(zero, zero);
                        let zm = d.lemma(p.zero_mul, &[zero]); // eq(mul(0,0),0)
                        let zm_symm = d.symm(zz, zero, zm); // eq(0, mul(0,0))
                        let witness_eq = d.trans(n, zero, zz, heq, zm_symm); // eq(n, mul(0,0))
                        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                        let proof = d.apply(intro, &[nat, pred, zero, witness_eq]);
                        d.lam_fv(heq_fv, n_eq_zero, proof)
                    };
                    d.const_app(p.logic.iff_intro, &[dvd_0_n, n_eq_zero, forward, reverse])
                };
                // iff_a : Iff (eq (mod n 0) 0) (eq n 0)
                let mod_zero_n = d.lemma(p.mod_zero, &[n]); // eq(mod(n,0), n)
                let modn0 = d.modulo(n, zero);
                let eq_zero_ctx =
                    Template::EqNat(Box::new(Template::Hole), Box::new(Template::Fixed(zero)));
                let iff_a = proof_plan::iff_lift(d, eq_zero_ctx, modn0, n, mod_zero_n);
                let modn0_eq_zero = d.eq(modn0, zero);
                let iff_a_symm = proof_plan::iff_flip(d, modn0_eq_zero, n_eq_zero, iff_a);
                proof_plan::iff_chain(
                    d,
                    dvd_0_n,
                    &[(n_eq_zero, iff_b), (modn0_eq_zero, iff_a_symm)],
                )
            },
            &|d, j, _ih| {
                let succ_j = d.succ(j);
                let quotient = d.div(n, succ_j);
                let remainder = d.modulo(n, succ_j);
                let executable = d.lemma(p.div_mod_exec, &[j, n]); // divMod(succ_j,n,quotient,remainder)
                let result = d.lemma(
                    p.div_mod_remainder_eq_zero_iff_dvd,
                    &[succ_j, n, quotient, remainder, executable],
                );
                // result : Iff (eq remainder 0) (dvd succ_j n)
                let zero = d.zero();
                let remainder_eq_zero = d.eq(remainder, zero);
                let dvd_succ_j_n = d.dvd(succ_j, n);
                proof_plan::iff_flip(d, remainder_eq_zero, dvd_succ_j_n, result)
            },
            m,
        );
        (stmt, proof)
    })?;

    // `dvd n m -> lt zero m -> lt zero (div m n)`: if `div m n` were `0`,
    // `div_mul_cancel` would force `m = mul 0 n = 0`, contradicting `lt zero
    // m`; `Nat.zero_or_succ` on `div m n` leaves only the successor case,
    // where `zero_lt_succ` closes directly.
    let pos_of_dvd_and_pos_numerator =
        |d: &mut NatDev<'_>, n: ExprId, m: ExprId, dvd_n_m: ExprId, pos_m: ExprId| -> ExprId {
            let zero = d.zero();
            let quotient = d.div(m, n);
            let cancel = d.lemma(p.div_mul_cancel, &[n, m, dvd_n_m]); // eq(mul(quotient,n), m)
            let goal = d.lt(zero, quotient);
            let disj = d.lemma(p.zero_or_succ, &[quotient]);
            let eq_q0_ty = d.eq(quotient, zero);
            let case_zero = {
                let heq_fv = d.fresh_fvar();
                let heq = d.kernel().fvar(heq_fv);
                let product = d.mul(quotient, n);
                let zero_product = d.mul(zero, n);
                let congr_q = d.congr(quotient, zero, heq, &|d, x| d.mul(x, n));
                let zero_mul_n = d.lemma(p.zero_mul, &[n]); // eq(zero_product, zero)
                let cancel_symm = d.symm(product, m, cancel); // eq(m, product)
                let (_, m_eq_zero) = d.chain(
                    m,
                    &[
                        (product, cancel_symm),
                        (zero_product, congr_q),
                        (zero, zero_mul_n),
                    ],
                );
                let motive = d.eq_motive(m, &|d, x| d.lt(zero, x));
                let lt_zero_zero = d.transport(m, motive, pos_m, zero, m_eq_zero);
                let contra = d.lemma(p.not_lt_zero, &[zero]); // Not (lt zero zero)
                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                let absurd = d.apply(contra, &[lt_zero_zero]);
                let anon = d.anon_name();
                let motive_false = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
                let level = d.kernel().level_zero();
                let rec = d.kernel().const_(p.logic.false_rec, vec![level]);
                let result = d.apply(rec, &[motive_false, absurd]);
                d.lam_fv(heq_fv, eq_q0_ty, result)
            };
            let nat = d.nat_ty();
            let one = d.level_one();
            let pred_ty = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sk = d.succ(k);
                let body = d.eq(quotient, sk);
                d.lam_fv(k_fv, nat, body)
            };
            let exists_c = d.kernel().const_(p.logic.exists_, vec![one]);
            let ex_ty = d.apply(exists_c, &[nat, pred_ty]);
            let case_succ = {
                let hex_fv = d.fresh_fvar();
                let hex = d.kernel().fvar(hex_fv);
                let anon = d.anon_name();
                let motive_ex = d.kernel().lam(anon, ex_ty, goal, BinderInfo::Default);
                let minor = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let sk = d.succ(k);
                    let heq1_ty = d.eq(quotient, sk);
                    let heq1_fv = d.fresh_fvar();
                    let heq1 = d.kernel().fvar(heq1_fv);
                    let zls = d.lemma(p.zero_lt_succ, &[k]); // lt(zero, succ k)
                    let motive_v = d.eq_motive(sk, &|d, x| d.lt(zero, x));
                    let symm_heq1 = d.symm(quotient, sk, heq1);
                    let result = d.transport(sk, motive_v, zls, quotient, symm_heq1);
                    let with_heq1 = d.lam_fv(heq1_fv, heq1_ty, result);
                    d.lam_fv(k_fv, nat, with_heq1)
                };
                let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
                let body = d.apply(exists_rec, &[nat, pred_ty, motive_ex, minor, hex]);
                d.lam_fv(hex_fv, ex_ty, body)
            };
            d.const_app(
                p.logic.or_elim,
                &[eq_q0_ty, ex_ty, goal, disj, case_zero, case_succ],
            )
        };

    // `Nat.div_gcd_pos_of_pos_left : ∀ a b, lt zero a -> lt zero (div a (gcd a b))`
    // — `F:ml430-nat-div-gcd-pos-of-pos-left-dd878a3f`.
    d.theorem(p.div_gcd_pos_of_pos_left, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let g = d.gcd(a, b);
        let zero = d.zero();
        let pos_ty = d.lt(zero, a);
        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);
        let gdl = d.lemma(p.gcd_dvd_left, &[a, b]); // dvd(g, a)
        let result = pos_of_dvd_and_pos_numerator(d, g, a, gdl, pos);
        let quotient = d.div(a, g);
        let concl = d.lt(zero, quotient);
        let proof = d.lam_fv(pos_fv, pos_ty, result);
        (d.arrow(pos_ty, concl), proof)
    })?;

    // `Nat.div_gcd_pos_of_pos_right : ∀ a b, lt zero b -> lt zero (div b (gcd a b))`
    // — `F:ml430-nat-div-gcd-pos-of-pos-right-8d26808c`, mirror via `gcd_dvd_right`.
    d.theorem(p.div_gcd_pos_of_pos_right, 2, &|d, values| {
        let (a, b) = (values[0], values[1]);
        let g = d.gcd(a, b);
        let zero = d.zero();
        let pos_ty = d.lt(zero, b);
        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);
        let gdr = d.lemma(p.gcd_dvd_right, &[a, b]); // dvd(g, b)
        let result = pos_of_dvd_and_pos_numerator(d, g, b, gdr, pos);
        let quotient = d.div(b, g);
        let concl = d.lt(zero, quotient);
        let proof = d.lam_fv(pos_fv, pos_ty, result);
        (d.arrow(pos_ty, concl), proof)
    })?;

    Ok(())
}
