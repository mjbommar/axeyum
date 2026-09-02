//! Nine `Nat.Coprime` mirrors of Mathlib v4.30's `Init.Data.Nat.Coprime`
//! (Lean core, not mathlib4 itself — `Nat.Coprime` and its basic API live in
//! the toolchain, confirmed by reading
//! `Init/Data/Nat/Coprime.lean` at the pinned `leanprover/lean4:v4.30.0`
//! toolchain directly rather than inferring from the name).
//!
//! Two of the nine (`coprime_dvd_left`, `coprime_dvd_right`) are already
//! proved in this prelude under a different name: `primes.rs`'s
//! `coprime_of_dvd_left`/`coprime_of_dvd_right` state the identical
//! proposition (`Coprime` is never given its own name here — see
//! `rel_prime.rs`'s module doc — so both are spelled `gcd _ _ = one`
//! directly), just with Mathlib's `Coprime.` namespace segment flattened
//! into the argument-shrinking name instead of the dvd-direction name. Both
//! are thin one-line wrappers rather than aliases, keeping the one-fact-one-
//! declaration correspondence the ledger's checkers expect.
//!
//! `dvd_of_dvd_mul_left` is [`NatPrelude::gauss_lemma`] verbatim
//! (`lcm.rs`'s `Nat.gauss_lemma : gcd x y = 1 → x ∣ (y*z) → x ∣ z`, exactly
//! this fact's hypothesis order); `dvd_of_dvd_mul_right` is the same lemma
//! with the product commuted first. The four `coprime_mul_*` mirrors reduce
//! to `coprime_of_dvd_left`/`coprime_of_dvd_right` fed a one-sided
//! divisibility fact built from [`NatPrelude::dvd_mul`] (`a ∣ a*q`),
//! transported along `mul_comm` when the needed factor is on the wrong side.
//!
//! `coprime_div_right` is the one genuine case split, on the divisor `a`:
//! at `a = 0`, `dvd 0 n` forces `n = 0` (`zero_mul`) and `div _ 0 = 0`
//! (`div_zero`) collapses both `n` and `n/a` to the same value, so the
//! hypothesis transports straight across; at `a = succ a'`, the witness `q`
//! from `dvd a n` (`n = a*q`) recovers `div n a = q` via
//! `div_mul_cancel_of_dvd` at the now-positive `a` — the same "exact factor
//! divided back out" route `lcm_gcd_lemmas.rs`'s private `div_eq_of_mul_eq`
//! uses, copied here per this crate's own per-file `dvd_elim`/local-helper
//! convention (see `lcm.rs`, `divisibility.rs`, `primes.rs`, `perfect.rs`,
//! `irrational.rs`, `lcm_gcd_lemmas.rs`, `div_mod_lemmas.rs`) — and
//! `Coprime m n` transported along `n = a*q` becomes `Coprime m (a*q)`,
//! which `coprime_of_dvd_right` shrinks to `Coprime m q` via `q ∣ (a*q)`.

use super::NatPrelude;
use super::helpers::transport_dvd_right;
use super::ops::{NatDev, NatOps, cases_zero_succ};
use super::steps::dvd_elim;
use crate::KernelError;
use crate::expr::ExprId;

/// Given `mul_eq : Eq (mul k a) b` and `k_pos : Le 1 k`, build a proof of
/// `Eq (div b k) a` — the exact factor `k*a` divided back out recovers `a`.
/// Copied from `lcm_gcd_lemmas.rs`'s private helper of the same name and
/// signature, per this file's own local-helper convention.
fn div_eq_of_mul_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    k: ExprId,
    a: ExprId,
    b: ExprId,
    k_pos: ExprId,
    mul_eq: ExprId,
) -> ExprId {
    let p = *p;
    let ka = d.mul(k, a);
    let dvd_k_ka = d.lemma(p.dvd_mul, &[k, a]); // dvd k ka
    let dvd_k_b = transport_dvd_right(d, k, ka, b, mul_eq, dvd_k_ka); // dvd k b
    let cancel = d.lemma(p.div_mul_cancel_of_dvd, &[k, b, k_pos, dvd_k_b]); // Eq (mul k (div b k)) b
    let mul_eq_rev = d.symm(ka, b, mul_eq); // Eq b ka
    let div_b_k = d.div(b, k);
    let mul_k_divbk = d.mul(k, div_b_k);
    let (_, chained) = d.chain(mul_k_divbk, &[(b, cancel), (ka, mul_eq_rev)]);
    // chained : Eq mul_k_divbk ka
    d.lemma(p.mul_left_cancel_of_pos, &[k, div_b_k, a, k_pos, chained]) // Eq div_b_k a
}

/// `Nat.Coprime.coprime_dvd_left : ∀ m k n, dvd m k → Coprime k n →
/// Coprime m n`. [`NatPrelude::coprime_of_dvd_left`] under the same
/// arguments — see the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_dvd_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_dvd_left, 3, &|d, v| {
        let (m, k, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let dvd_ty = d.dvd(m, k);
        let gcd_kn = d.gcd(k, n);
        let cop_ty = d.eq(gcd_kn, one);
        let gcd_mn = d.gcd(m, n);
        let concl = d.eq(gcd_mn, one);

        let dvd_fv = d.fresh_fvar();
        let dvd_hyp = d.kernel().fvar(dvd_fv);
        let cop_fv = d.fresh_fvar();
        let cop_hyp = d.kernel().fvar(cop_fv);

        let result = d.lemma(p.coprime_of_dvd_left, &[m, k, n, dvd_hyp, cop_hyp]);

        let body = d.lam_fv(cop_fv, cop_ty, result);
        let proof = d.lam_fv(dvd_fv, dvd_ty, body);
        let inner = d.arrow(cop_ty, concl);
        let stmt = d.arrow(dvd_ty, inner);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.coprime_dvd_right : ∀ n m k, dvd n m → Coprime k m →
/// Coprime k n`. [`NatPrelude::coprime_of_dvd_right`] under the same
/// arguments — see the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_dvd_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_dvd_right, 3, &|d, v| {
        let (n, m, k) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let dvd_ty = d.dvd(n, m);
        let gcd_km = d.gcd(k, m);
        let cop_ty = d.eq(gcd_km, one);
        let gcd_kn = d.gcd(k, n);
        let concl = d.eq(gcd_kn, one);

        let dvd_fv = d.fresh_fvar();
        let dvd_hyp = d.kernel().fvar(dvd_fv);
        let cop_fv = d.fresh_fvar();
        let cop_hyp = d.kernel().fvar(cop_fv);

        let result = d.lemma(p.coprime_of_dvd_right, &[k, n, m, dvd_hyp, cop_hyp]);

        let body = d.lam_fv(cop_fv, cop_ty, result);
        let proof = d.lam_fv(dvd_fv, dvd_ty, body);
        let inner = d.arrow(cop_ty, concl);
        let stmt = d.arrow(dvd_ty, inner);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.coprime_mul_right : ∀ m k n, Coprime (mul m k) n →
/// Coprime m n`. `m ∣ (m*k)` is [`NatPrelude::dvd_mul`] directly.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_mul_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_mul_right, 3, &|d, v| {
        let (m, k, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let mk = d.mul(m, k);
        let gcd_mkn = d.gcd(mk, n);
        let hyp_ty = d.eq(gcd_mkn, one);
        let gcd_mn = d.gcd(m, n);
        let concl = d.eq(gcd_mn, one);

        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let dvd_m_mk = d.lemma(p.dvd_mul, &[m, k]); // dvd m (mul m k)
        let result = d.lemma(p.coprime_of_dvd_left, &[m, mk, n, dvd_m_mk, hyp]);

        let proof = d.lam_fv(hyp_fv, hyp_ty, result);
        let stmt = d.arrow(hyp_ty, concl);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.coprime_mul_left : ∀ k m n, Coprime (mul k m) n →
/// Coprime m n`. `m ∣ (k*m)` needs `mul_comm` on top of
/// [`NatPrelude::dvd_mul`] (which only gives `m ∣ (m*k)`).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_mul_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_mul_left, 3, &|d, v| {
        let (k, m, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let km = d.mul(k, m);
        let gcd_kmn = d.gcd(km, n);
        let hyp_ty = d.eq(gcd_kmn, one);
        let gcd_mn = d.gcd(m, n);
        let concl = d.eq(gcd_mn, one);

        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let mk = d.mul(m, k);
        let dvd_m_mk = d.lemma(p.dvd_mul, &[m, k]); // dvd m (mul m k)
        let comm_mk = d.lemma(p.mul_comm, &[m, k]); // Eq (mul m k) (mul k m)
        let dvd_m_km = transport_dvd_right(d, m, mk, km, comm_mk, dvd_m_mk); // dvd m (mul k m)
        let result = d.lemma(p.coprime_of_dvd_left, &[m, km, n, dvd_m_km, hyp]);

        let proof = d.lam_fv(hyp_fv, hyp_ty, result);
        let stmt = d.arrow(hyp_ty, concl);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.coprime_mul_right_right : ∀ m n k, Coprime m (mul n k) →
/// Coprime m n`. `n ∣ (n*k)` is [`NatPrelude::dvd_mul`] directly.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_mul_right_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_mul_right_right, 3, &|d, v| {
        let (m, n, k) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let nk = d.mul(n, k);
        let gcd_m_nk = d.gcd(m, nk);
        let hyp_ty = d.eq(gcd_m_nk, one);
        let gcd_mn = d.gcd(m, n);
        let concl = d.eq(gcd_mn, one);

        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let dvd_n_nk = d.lemma(p.dvd_mul, &[n, k]); // dvd n (mul n k)
        let result = d.lemma(p.coprime_of_dvd_right, &[m, n, nk, dvd_n_nk, hyp]);

        let proof = d.lam_fv(hyp_fv, hyp_ty, result);
        let stmt = d.arrow(hyp_ty, concl);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.coprime_mul_left_right : ∀ m k n, Coprime m (mul k n) →
/// Coprime m n`. `n ∣ (k*n)` needs `mul_comm` on top of
/// [`NatPrelude::dvd_mul`] (which only gives `n ∣ (n*k)`).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_mul_left_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_mul_left_right, 3, &|d, v| {
        let (m, k, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let kn = d.mul(k, n);
        let gcd_m_kn = d.gcd(m, kn);
        let hyp_ty = d.eq(gcd_m_kn, one);
        let gcd_mn = d.gcd(m, n);
        let concl = d.eq(gcd_mn, one);

        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let nk = d.mul(n, k);
        let dvd_n_nk = d.lemma(p.dvd_mul, &[n, k]); // dvd n (mul n k)
        let comm_nk = d.lemma(p.mul_comm, &[n, k]); // Eq (mul n k) (mul k n)
        let dvd_n_kn = transport_dvd_right(d, n, nk, kn, comm_nk, dvd_n_nk); // dvd n (mul k n)
        let result = d.lemma(p.coprime_of_dvd_right, &[m, n, kn, dvd_n_kn, hyp]);

        let proof = d.lam_fv(hyp_fv, hyp_ty, result);
        let stmt = d.arrow(hyp_ty, concl);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.dvd_of_dvd_mul_left : ∀ k m n, Coprime k m →
/// dvd k (mul m n) → dvd k n` — [`NatPrelude::gauss_lemma`] verbatim.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dvd_of_dvd_mul_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dvd_of_dvd_mul_left, 3, &|d, v| {
        let (k, m, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let gcd_km = d.gcd(k, m);
        let cop_ty = d.eq(gcd_km, one);
        let mn = d.mul(m, n);
        let dvd_ty = d.dvd(k, mn);
        let concl = d.dvd(k, n);

        let cop_fv = d.fresh_fvar();
        let cop_hyp = d.kernel().fvar(cop_fv);
        let dvd_fv = d.fresh_fvar();
        let dvd_hyp = d.kernel().fvar(dvd_fv);

        let result = d.lemma(p.gauss_lemma, &[k, m, n, cop_hyp, dvd_hyp]);

        let body = d.lam_fv(dvd_fv, dvd_ty, result);
        let proof = d.lam_fv(cop_fv, cop_ty, body);
        let inner = d.arrow(dvd_ty, concl);
        let stmt = d.arrow(cop_ty, inner);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.dvd_of_dvd_mul_right : ∀ k n m, Coprime k n →
/// dvd k (mul m n) → dvd k m` — [`NatPrelude::gauss_lemma`] at `(k, n, m)`,
/// the hypothesis transported along `mul_comm m n` first.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_dvd_of_dvd_mul_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.dvd_of_dvd_mul_right, 3, &|d, v| {
        let (k, n, m) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let gcd_kn = d.gcd(k, n);
        let cop_ty = d.eq(gcd_kn, one);
        let mn = d.mul(m, n);
        let dvd_ty = d.dvd(k, mn);
        let concl = d.dvd(k, m);

        let cop_fv = d.fresh_fvar();
        let cop_hyp = d.kernel().fvar(cop_fv);
        let dvd_fv = d.fresh_fvar();
        let dvd_hyp = d.kernel().fvar(dvd_fv);

        let nm = d.mul(n, m);
        let comm_mn = d.lemma(p.mul_comm, &[m, n]); // Eq (mul m n) (mul n m)
        let dvd_k_nm = transport_dvd_right(d, k, mn, nm, comm_mn, dvd_hyp); // dvd k (mul n m)
        let result = d.lemma(p.gauss_lemma, &[k, n, m, cop_hyp, dvd_k_nm]);

        let body = d.lam_fv(dvd_fv, dvd_ty, result);
        let proof = d.lam_fv(cop_fv, cop_ty, body);
        let inner = d.arrow(dvd_ty, concl);
        let stmt = d.arrow(cop_ty, inner);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.coprime_div_right : ∀ m n a, Coprime m n → dvd a n →
/// Coprime m (div n a)`. See the module doc for the case split on `a`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_div_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_div_right, 3, &|d, v| {
        let (m, n, a) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let gcd_mn = d.gcd(m, n);
        let cmn_ty = d.eq(gcd_mn, one);

        let cmn_fv = d.fresh_fvar();
        let cmn_hyp = d.kernel().fvar(cmn_fv);

        // motive(x) := dvd x n -> Coprime m (div n x)
        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let dvd_ty = d.dvd(x, n);
            let div_nx = d.div(n, x);
            let gcd_m_div = d.gcd(m, div_nx);
            let concl = d.eq(gcd_m_div, one);
            d.arrow(dvd_ty, concl)
        };
        let stmt_inner = motive(d, a);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let dvd_ty = d.dvd(zero, n);
            let div_n0 = d.div(n, zero);
            let gcd_m_divn0 = d.gcd(m, div_n0);
            let concl = d.eq(gcd_m_divn0, one);

            let dvd_fv = d.fresh_fvar();
            let dvd_hyp = d.kernel().fvar(dvd_fv);

            let body = dvd_elim(d, zero, n, concl, dvd_hyp, &|d, q, eq_proof| {
                // eq_proof : Eq n (mul zero q)
                let zq = d.mul(zero, q);
                let zmul = d.lemma(p.zero_mul, &[q]); // Eq (mul zero q) zero
                let (_, n_eq_zero) = d.chain(n, &[(zq, eq_proof), (zero, zmul)]); // Eq n zero

                let gcd_m_zero = d.gcd(m, zero);
                let n_gcd_eq = d.congr(n, zero, n_eq_zero, &|d, x| d.gcd(m, x)); // Eq gcd_mn gcd_m_zero
                let sym1 = d.symm(gcd_mn, gcd_m_zero, n_gcd_eq); // Eq gcd_m_zero gcd_mn
                let gcd_m_zero_eq_one = d.trans(gcd_m_zero, gcd_mn, one, sym1, cmn_hyp); // Eq gcd_m_zero one

                let dz = d.lemma(p.div_zero, &[n]); // Eq (div n zero) zero
                let div_eq_gz = d.congr(div_n0, zero, dz, &|d, x| d.gcd(m, x)); // Eq gcd_m_divn0 gcd_m_zero
                d.trans(gcd_m_divn0, gcd_m_zero, one, div_eq_gz, gcd_m_zero_eq_one)
            });
            d.lam_fv(dvd_fv, dvd_ty, body)
        };

        let at_succ = |d: &mut NatDev<'_>, apred: ExprId| -> ExprId {
            let asucc = d.succ(apred);
            let dvd_ty = d.dvd(asucc, n);
            let div_nas = d.div(n, asucc);
            let gcd_m_divnas = d.gcd(m, div_nas);
            let concl = d.eq(gcd_m_divnas, one);

            let dvd_fv = d.fresh_fvar();
            let dvd_hyp = d.kernel().fvar(dvd_fv);

            let k_pos = d.zero_lt_succ(apred); // Le 1 asucc

            let body = dvd_elim(d, asucc, n, concl, dvd_hyp, &|d, q, eq_proof| {
                // eq_proof : Eq n (mul asucc q)
                let asucc_q = d.mul(asucc, q);
                let eq_proof_rev = d.symm(n, asucc_q, eq_proof); // Eq (mul asucc q) n
                let div_eq_q = div_eq_of_mul_eq(d, &p, asucc, q, n, k_pos, eq_proof_rev); // Eq (div n asucc) q
                let gcd_m_q = d.gcd(m, q);
                let div_gcd_eq = d.congr(div_nas, q, div_eq_q, &|d, x| d.gcd(m, x)); // Eq gcd_m_divnas gcd_m_q

                let gcd_m_asuccq = d.gcd(m, asucc_q);
                let n_gcd_eq = d.congr(n, asucc_q, eq_proof, &|d, x| d.gcd(m, x)); // Eq gcd_mn gcd_m_asuccq
                let sym1 = d.symm(gcd_mn, gcd_m_asuccq, n_gcd_eq); // Eq gcd_m_asuccq gcd_mn
                let gcd_m_asuccq_eq_one = d.trans(gcd_m_asuccq, gcd_mn, one, sym1, cmn_hyp); // Eq gcd_m_asuccq one

                let q_asucc = d.mul(q, asucc);
                let dvd_q_qasucc = d.lemma(p.dvd_mul, &[q, asucc]); // dvd q (mul q asucc)
                let comm_qa = d.lemma(p.mul_comm, &[q, asucc]); // Eq (mul q asucc) (mul asucc q)
                let dvd_q_asuccq =
                    transport_dvd_right(d, q, q_asucc, asucc_q, comm_qa, dvd_q_qasucc); // dvd q (mul asucc q)

                let gcd_m_q_eq_one = d.lemma(
                    p.coprime_of_dvd_right,
                    &[m, q, asucc_q, dvd_q_asuccq, gcd_m_asuccq_eq_one],
                ); // Eq gcd_m_q one

                d.trans(gcd_m_divnas, gcd_m_q, one, div_gcd_eq, gcd_m_q_eq_one)
            });
            d.lam_fv(dvd_fv, dvd_ty, body)
        };

        let inner_proof = cases_zero_succ(d, a, &motive, &at_zero, &at_succ);
        let full_proof = d.lam_fv(cmn_fv, cmn_ty, inner_proof);
        let full_stmt = d.arrow(cmn_ty, stmt_inner);
        (full_stmt, full_proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.coprime_div_left : ∀ m n a, Coprime m n → dvd a m →
/// Coprime (div m a) n`. Mirror image of [`declare_coprime_div_right`]: the
/// divided argument is `m` instead of `n`, and the shrinking step at the end
/// uses `coprime_of_dvd_left` (shrinking the LEFT `gcd` argument) instead of
/// `coprime_of_dvd_right`. See the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_div_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_div_left, 3, &|d, v| {
        let (m, n, a) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let gcd_mn = d.gcd(m, n);
        let cmn_ty = d.eq(gcd_mn, one);

        let cmn_fv = d.fresh_fvar();
        let cmn_hyp = d.kernel().fvar(cmn_fv);

        // motive(x) := dvd x m -> Coprime (div m x) n
        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let dvd_ty = d.dvd(x, m);
            let div_mx = d.div(m, x);
            let gcd_div_n = d.gcd(div_mx, n);
            let concl = d.eq(gcd_div_n, one);
            d.arrow(dvd_ty, concl)
        };
        let stmt_inner = motive(d, a);

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let dvd_ty = d.dvd(zero, m);
            let div_m0 = d.div(m, zero);
            let gcd_divm0_n = d.gcd(div_m0, n);
            let concl = d.eq(gcd_divm0_n, one);

            let dvd_fv = d.fresh_fvar();
            let dvd_hyp = d.kernel().fvar(dvd_fv);

            let body = dvd_elim(d, zero, m, concl, dvd_hyp, &|d, q, eq_proof| {
                // eq_proof : Eq m (mul zero q)
                let zq = d.mul(zero, q);
                let zmul = d.lemma(p.zero_mul, &[q]); // Eq (mul zero q) zero
                let (_, m_eq_zero) = d.chain(m, &[(zq, eq_proof), (zero, zmul)]); // Eq m zero

                let gcd_zero_n = d.gcd(zero, n);
                let m_gcd_eq = d.congr(m, zero, m_eq_zero, &|d, x| d.gcd(x, n)); // Eq gcd_mn gcd_zero_n
                let sym1 = d.symm(gcd_mn, gcd_zero_n, m_gcd_eq); // Eq gcd_zero_n gcd_mn
                let gcd_zero_n_eq_one = d.trans(gcd_zero_n, gcd_mn, one, sym1, cmn_hyp); // Eq gcd_zero_n one

                let dz = d.lemma(p.div_zero, &[m]); // Eq (div m zero) zero
                let div_eq_gz = d.congr(div_m0, zero, dz, &|d, x| d.gcd(x, n)); // Eq gcd_divm0_n gcd_zero_n
                d.trans(gcd_divm0_n, gcd_zero_n, one, div_eq_gz, gcd_zero_n_eq_one)
            });
            d.lam_fv(dvd_fv, dvd_ty, body)
        };

        let at_succ = |d: &mut NatDev<'_>, apred: ExprId| -> ExprId {
            let asucc = d.succ(apred);
            let dvd_ty = d.dvd(asucc, m);
            let div_mas = d.div(m, asucc);
            let gcd_divmas_n = d.gcd(div_mas, n);
            let concl = d.eq(gcd_divmas_n, one);

            let dvd_fv = d.fresh_fvar();
            let dvd_hyp = d.kernel().fvar(dvd_fv);

            let k_pos = d.zero_lt_succ(apred); // Le 1 asucc

            let body = dvd_elim(d, asucc, m, concl, dvd_hyp, &|d, q, eq_proof| {
                // eq_proof : Eq m (mul asucc q)
                let asucc_q = d.mul(asucc, q);
                let eq_proof_rev = d.symm(m, asucc_q, eq_proof); // Eq (mul asucc q) m
                let div_eq_q = div_eq_of_mul_eq(d, &p, asucc, q, m, k_pos, eq_proof_rev); // Eq (div m asucc) q
                let gcd_q_n = d.gcd(q, n);
                let div_gcd_eq = d.congr(div_mas, q, div_eq_q, &|d, x| d.gcd(x, n)); // Eq gcd_divmas_n gcd_q_n

                let gcd_asuccq_n = d.gcd(asucc_q, n);
                let m_gcd_eq = d.congr(m, asucc_q, eq_proof, &|d, x| d.gcd(x, n)); // Eq gcd_mn gcd_asuccq_n
                let sym1 = d.symm(gcd_mn, gcd_asuccq_n, m_gcd_eq); // Eq gcd_asuccq_n gcd_mn
                let gcd_asuccq_n_eq_one = d.trans(gcd_asuccq_n, gcd_mn, one, sym1, cmn_hyp); // Eq gcd_asuccq_n one

                let q_asucc = d.mul(q, asucc);
                let dvd_q_qasucc = d.lemma(p.dvd_mul, &[q, asucc]); // dvd q (mul q asucc)
                let comm_qa = d.lemma(p.mul_comm, &[q, asucc]); // Eq (mul q asucc) (mul asucc q)
                let dvd_q_asuccq =
                    transport_dvd_right(d, q, q_asucc, asucc_q, comm_qa, dvd_q_qasucc); // dvd q (mul asucc q)

                let gcd_q_n_eq_one = d.lemma(
                    p.coprime_of_dvd_left,
                    &[q, asucc_q, n, dvd_q_asuccq, gcd_asuccq_n_eq_one],
                ); // Eq gcd_q_n one

                d.trans(gcd_divmas_n, gcd_q_n, one, div_gcd_eq, gcd_q_n_eq_one)
            });
            d.lam_fv(dvd_fv, dvd_ty, body)
        };

        let inner_proof = cases_zero_succ(d, a, &motive, &at_zero, &at_succ);
        let full_proof = d.lam_fv(cmn_fv, cmn_ty, inner_proof);
        let full_stmt = d.arrow(cmn_ty, stmt_inner);
        (full_stmt, full_proof)
    })?;
    Ok(())
}

/// Declare all nine `Nat.Coprime` mirrors. See the module doc for the shared
/// route each group takes.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_lemmas(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_coprime_dvd_left(d, p)?;
    declare_coprime_dvd_right(d, p)?;
    declare_coprime_mul_right(d, p)?;
    declare_coprime_mul_left(d, p)?;
    declare_coprime_mul_right_right(d, p)?;
    declare_coprime_mul_left_right(d, p)?;
    declare_dvd_of_dvd_mul_left(d, p)?;
    declare_dvd_of_dvd_mul_right(d, p)?;
    declare_coprime_div_right(d, p)?;
    declare_coprime_div_left(d, p)?;
    Ok(())
}
