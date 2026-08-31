//! `ml430` mirrors dispatched to lane `draw11-theorems-b`: four `Nat`
//! propositions that compose already-proved lemmas, no new induction
//! principle.
//!
//! - [`declare_coprime_dvd_mul_left`] / [`declare_coprime_dvd_mul_right`]
//!   mirror `Nat.Coprime.dvd_mul_left` / `Nat.Coprime.dvd_mul_right`: the
//!   forward direction of each `Iff` is [`NatPrelude::gauss_lemma`]
//!   verbatim (`gcd x y = 1 → x ∣ (y*z) → x ∣ z`), the reverse direction is
//!   [`NatPrelude::dvd_mul`] (`a ∣ a*q`) transported across a
//!   [`NatPrelude::mul_comm`] when the needed factor sits on the other
//!   side, closed with [`NatPrelude::dvd_trans`]. Same route as
//!   `coprime_lemmas.rs`'s own module doc describes for its four
//!   `coprime_mul_*` mirrors — this file is the `Iff`-shaped sibling
//!   Mathlib states as `k.Coprime m → (k ∣ m*n ↔ k ∣ n)` rather than as a
//!   one-sided divisibility-shrinking lemma.
//! - [`declare_coprime_eq_of_mul_eq_zero`] mirrors
//!   `Nat.Coprime.eq_of_mul_eq_zero`: [`NatPrelude::mul_eq_zero`] splits
//!   `m*n = 0` into `m = 0 ∨ n = 0`; each disjunct forces the OTHER
//!   variable to `1` by substituting into the coprimality hypothesis and
//!   collapsing with [`NatPrelude::gcd_zero_left`] (plus
//!   [`NatPrelude::gcd_comm`] for the `n = 0` case, since the zero sits on
//!   the wrong side for `gcd_zero_left` directly).
//! - [`declare_add_one_mul_choose_eq`] mirrors `Nat.add_one_mul_choose_eq`:
//!   [`NatPrelude::succ_mul_choose_eq`] read backwards (`symm`) is already
//!   the target equation up to which factor comes first in the final
//!   product, closed by one [`NatPrelude::mul_comm`].

use super::NatPrelude;
use super::helpers::transport_dvd_right;
use super::ops::{NatDev, NatOps};
use crate::KernelError;

/// `Nat.Coprime.dvd_mul_left : ∀ k m n, gcd k m = 1 → (dvd k (mul m n) ↔ dvd k n)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_dvd_mul_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_dvd_mul_left, 3, &|d, v| {
        let (k, m, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let gcd_km = d.gcd(k, m);
        let coprime_ty = d.eq(gcd_km, one);
        let mn = d.mul(m, n);
        let dvd_k_mn = d.dvd(k, mn);
        let dvd_k_n = d.dvd(k, n);
        let iff_ty = d.const_app(p.logic.iff, &[dvd_k_mn, dvd_k_n]);
        let stmt = d.arrow(coprime_ty, iff_ty);

        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv); // Eq(gcd_km, one)

        // mp : dvd k (mul m n) -> dvd k n, directly `gauss_lemma`.
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv); // dvd k mn
            let body = d.lemma(p.gauss_lemma, &[k, m, n, c, h]); // dvd k n
            d.lam_fv(h_fv, dvd_k_mn, body)
        };

        // mpr : dvd k n -> dvd k (mul m n), via `n ∣ (m*n)` and `dvd_trans`.
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv); // dvd k n
            let nm = d.mul(n, m);
            let dvd_n_nm = d.lemma(p.dvd_mul, &[n, m]); // dvd n (mul n m)
            let comm = d.lemma(p.mul_comm, &[n, m]); // Eq(mul n m, mul m n)
            let dvd_n_mn = transport_dvd_right(d, n, nm, mn, comm, dvd_n_nm); // dvd n (mul m n)
            let body = d.lemma(p.dvd_trans, &[k, n, mn, h, dvd_n_mn]); // dvd k mn
            d.lam_fv(h_fv, dvd_k_n, body)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[dvd_k_mn, dvd_k_n, mp, mpr]);
        let full_proof = d.lam_fv(c_fv, coprime_ty, iff_proof);
        (stmt, full_proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.dvd_mul_right : ∀ k m n, gcd k n = 1 → (dvd k (mul m n) ↔ dvd k m)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_dvd_mul_right(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_dvd_mul_right, 3, &|d, v| {
        let (k, m, n) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let gcd_kn = d.gcd(k, n);
        let coprime_ty = d.eq(gcd_kn, one);
        let mn = d.mul(m, n);
        let dvd_k_mn = d.dvd(k, mn);
        let dvd_k_m = d.dvd(k, m);
        let iff_ty = d.const_app(p.logic.iff, &[dvd_k_mn, dvd_k_m]);
        let stmt = d.arrow(coprime_ty, iff_ty);

        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv); // Eq(gcd_kn, one)

        // mp : dvd k (mul m n) -> dvd k m, via commuting to (mul n m) then `gauss_lemma`.
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv); // dvd k mn
            let nm = d.mul(n, m);
            let comm = d.lemma(p.mul_comm, &[m, n]); // Eq(mul m n, mul n m)
            let h2 = transport_dvd_right(d, k, mn, nm, comm, h); // dvd k (mul n m)
            let body = d.lemma(p.gauss_lemma, &[k, n, m, c, h2]); // dvd k m
            d.lam_fv(h_fv, dvd_k_mn, body)
        };

        // mpr : dvd k m -> dvd k (mul m n), via `m ∣ (m*n)` and `dvd_trans`.
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv); // dvd k m
            let dvd_m_mn = d.lemma(p.dvd_mul, &[m, n]); // dvd m (mul m n)
            let body = d.lemma(p.dvd_trans, &[k, m, mn, h, dvd_m_mn]); // dvd k mn
            d.lam_fv(h_fv, dvd_k_m, body)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[dvd_k_mn, dvd_k_m, mp, mpr]);
        let full_proof = d.lam_fv(c_fv, coprime_ty, iff_proof);
        (stmt, full_proof)
    })?;
    Ok(())
}

/// `Nat.Coprime.eq_of_mul_eq_zero : ∀ m n, gcd m n = 1 → mul m n = 0 →
/// (Eq m 0 ∧ Eq n 1) ∨ (Eq m 1 ∧ Eq n 0)`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_eq_of_mul_eq_zero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_eq_of_mul_eq_zero, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let zero = d.zero();
        let one = d.num(1);
        let gcd_mn = d.gcd(m, n);
        let coprime_ty = d.eq(gcd_mn, one);
        let mn = d.mul(m, n);
        let zero_ty = d.eq(mn, zero);

        let m_eq_zero_ty = d.eq(m, zero);
        let n_eq_one_ty = d.eq(n, one);
        let left_and = d.const_app(p.logic.and, &[m_eq_zero_ty, n_eq_one_ty]);
        let m_eq_one_ty = d.eq(m, one);
        let n_eq_zero_ty = d.eq(n, zero);
        let right_and = d.const_app(p.logic.and, &[m_eq_one_ty, n_eq_zero_ty]);
        let concl = d.const_app(p.logic.or, &[left_and, right_and]);

        let inner_ty = d.arrow(zero_ty, concl);
        let stmt = d.arrow(coprime_ty, inner_ty);

        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv); // Eq(gcd_mn, one)
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv); // Eq(mn, zero)

        let split = d.lemma(p.mul_eq_zero, &[m, n, z]); // Or(Eq m 0, Eq n 0)

        // Case `m = 0`: substitute into the coprimality hypothesis to force
        // `n = 1`, then package `(m = 0) ∧ (n = 1)` and inject left.
        let case_m = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv); // Eq m 0
            let gcd_0n = d.gcd(zero, n);
            let congr_eq = d.congr(m, zero, h, &|d, x| d.gcd(x, n)); // Eq(gcd_mn, gcd_0n)
            let gzl = d.lemma(p.gcd_zero_left, &[n]); // Eq(gcd_0n, n)
            let gcd0n_eq_gcdmn = d.symm(gcd_mn, gcd_0n, congr_eq); // Eq(gcd_0n, gcd_mn)
            let gcd0n_eq_one = d.trans(gcd_0n, gcd_mn, one, gcd0n_eq_gcdmn, c); // Eq(gcd_0n, 1)
            let n_eq_gcd0n = d.symm(gcd_0n, n, gzl); // Eq(n, gcd_0n)
            let n_eq_one = d.trans(n, gcd_0n, one, n_eq_gcd0n, gcd0n_eq_one); // Eq(n, 1)
            let and_proof =
                d.const_app(p.logic.and_intro, &[m_eq_zero_ty, n_eq_one_ty, h, n_eq_one]);
            let or_proof = d.const_app(p.logic.or_inl, &[left_and, right_and, and_proof]);
            d.lam_fv(h_fv, m_eq_zero_ty, or_proof)
        };

        // Case `n = 0`: substitute, commute the zero to `gcd_zero_left`'s
        // side via `gcd_comm`, forcing `m = 1`; package and inject right.
        let case_n = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv); // Eq n 0
            let gcd_m0 = d.gcd(m, zero);
            let congr_eq = d.congr(n, zero, h, &|d, x| d.gcd(m, x)); // Eq(gcd_mn, gcd_m0)
            let gcd_m0_eq_gcd_mn = d.symm(gcd_mn, gcd_m0, congr_eq); // Eq(gcd_m0, gcd_mn)
            let gcd_m0_eq_one = d.trans(gcd_m0, gcd_mn, one, gcd_m0_eq_gcd_mn, c); // Eq(gcd_m0, 1)
            let gcd_0m = d.gcd(zero, m);
            let comm_eq = d.lemma(p.gcd_comm, &[m, zero]); // Eq(gcd_m0, gcd_0m)
            let gcd_0m_eq_gcd_m0 = d.symm(gcd_m0, gcd_0m, comm_eq); // Eq(gcd_0m, gcd_m0)
            let gcd_0m_eq_one = d.trans(gcd_0m, gcd_m0, one, gcd_0m_eq_gcd_m0, gcd_m0_eq_one); // Eq(gcd_0m, 1)
            let gzl_m = d.lemma(p.gcd_zero_left, &[m]); // Eq(gcd_0m, m)
            let m_eq_gcd0m = d.symm(gcd_0m, m, gzl_m); // Eq(m, gcd_0m)
            let m_eq_one = d.trans(m, gcd_0m, one, m_eq_gcd0m, gcd_0m_eq_one); // Eq(m, 1)
            let and_proof =
                d.const_app(p.logic.and_intro, &[m_eq_one_ty, n_eq_zero_ty, m_eq_one, h]);
            let or_proof = d.const_app(p.logic.or_inr, &[left_and, right_and, and_proof]);
            d.lam_fv(h_fv, n_eq_zero_ty, or_proof)
        };

        let selected = d.const_app(
            p.logic.or_elim,
            &[m_eq_zero_ty, n_eq_zero_ty, concl, split, case_m, case_n],
        );
        let with_z = d.lam_fv(z_fv, zero_ty, selected);
        let full_proof = d.lam_fv(c_fv, coprime_ty, with_z);
        (stmt, full_proof)
    })?;
    Ok(())
}

/// `Nat.add_one_mul_choose_eq : ∀ n k, mul (succ n) (choose n k) = mul
/// (choose (succ n) (succ k)) (succ k)` — Mathlib's `(n+1) * n.choose k =
/// (n+1).choose (k+1) * (k+1)` over this prelude's `succ` spelling of
/// `+1`. [`NatPrelude::succ_mul_choose_eq`] read backwards (`symm`) already
/// states `mul (succ n) (choose n k) = mul (succ k) (choose (succ n)
/// (succ k))`; one [`NatPrelude::mul_comm`] on the right-hand product
/// finishes it.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_add_one_mul_choose_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_one_mul_choose_eq, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let sn = d.succ(n);
        let sk = d.succ(k);
        let choose_nk = d.choose(n, k);
        let choose_snsk = d.choose(sn, sk);

        let lhs = d.mul(sn, choose_nk);
        let rhs = d.mul(choose_snsk, sk);
        let stmt = d.eq(lhs, rhs);

        let base_step = d.lemma(p.succ_mul_choose_eq, &[n, k]); // Eq(mul sk choose_snsk, lhs)
        let mid = d.mul(sk, choose_snsk);
        let base_rev = d.symm(mid, lhs, base_step); // Eq(lhs, mid)
        let comm_eq = d.lemma(p.mul_comm, &[sk, choose_snsk]); // Eq(mid, rhs)
        let proof = d.trans(lhs, mid, rhs, base_rev, comm_eq);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare all four `draw11-theorems-b` mirrors. See the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_draw11_mirrors_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_coprime_dvd_mul_left(d, p)?;
    declare_coprime_dvd_mul_right(d, p)?;
    declare_coprime_eq_of_mul_eq_zero(d, p)?;
    declare_add_one_mul_choose_eq(d, p)?;
    Ok(())
}
