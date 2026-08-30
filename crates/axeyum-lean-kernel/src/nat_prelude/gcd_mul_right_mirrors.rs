//! Three `ml430` mirrors that all reduce to `Nat.gcd_mul_right`
//! (`gcd_mul_right.rs`) plus already-proved gcd/divisibility algebra:
//!
//! - `Nat.dvd_gcd_mul_iff_dvd_mul` (`F:ml430-nat-dvd-gcd-mul-iff-dvd-mul-0afe640a`):
//!   `∀ k n m, k ∣ (gcd k n) * m ↔ k ∣ n * m`.
//! - `Nat.dvd_mul_gcd_iff_dvd_mul` (`F:ml430-nat-dvd-mul-gcd-iff-dvd-mul-f9517e6b`):
//!   `∀ k n m, k ∣ n * (gcd k m) ↔ k ∣ n * m`.
//! - `Nat.dvd_gcd_mul_gcd_iff_dvd_mul` (`F:ml430-nat-dvd-gcd-mul-gcd-iff-dvd-mul-07fec722`):
//!   `∀ k n m, k ∣ (gcd k n) * (gcd k m) ↔ k ∣ n * m`.
//!
//! # The shared argument
//!
//! `dvd_gcd_scaled_iff(k, a, b, c, k_dvd_ac)` proves the general shape
//! `Iff (dvd k (mul (gcd a b) c)) (dvd k (mul b c))`, given a proof that `k`
//! always divides `a*c`:
//!
//! 1. `gcd_mul_right(a, b, c) : Eq (gcd (a*c) (b*c)) (gcd a b * c)`, reversed
//!    and lifted to an `Iff` on `dvd k _` via [`pred_iff_of_eq`], gives
//!    `Iff (dvd k (gcd a b * c)) (dvd k (gcd (a*c) (b*c)))`.
//! 2. `dvd_gcd_iff(k, a*c, b*c)` unpacks the right-hand side into
//!    `And (dvd k (a*c)) (dvd k (b*c))`.
//! 3. Since `k ∣ a*c` always holds (the caller's `k_dvd_ac`), that conjunct
//!    is redundant: `Iff (And (dvd k (a*c)) (dvd k (b*c))) (dvd k (b*c))`
//!    (`mp` projects the second conjunct; `mpr` pairs the hypothesis with
//!    `k_dvd_ac`).
//!
//! Chaining the three `Iff`s gives the general shape. Each fact instantiates
//! it differently:
//!
//! - **`dvd_gcd_mul_iff_dvd_mul`** is the shape directly, at
//!   `(a, b, c) := (k, n, m)` with `k_dvd_ac := dvd_mul(k, m)`.
//! - **`dvd_mul_gcd_iff_dvd_mul`** needs the scaling factor on the LEFT
//!   (`n * gcd k m`, not `gcd k m * n`), so it commutes both sides
//!   (`mul_comm`) around an application of the shape at
//!   `(a, b, c) := (k, m, n)` with `k_dvd_ac := dvd_mul(k, n)`.
//! - **`dvd_gcd_mul_gcd_iff_dvd_mul`** applies the shape at
//!   `(a, b, c) := (k, n, gcd k m)` with
//!   `k_dvd_ac := dvd_mul(k, gcd k m)`, landing on
//!   `Iff (dvd k ((gcd k n) * (gcd k m))) (dvd k (n * (gcd k m)))` --
//!   whose right-hand side IS `dvd_mul_gcd_iff_dvd_mul`'s left-hand side, so
//!   one more `iff_trans` against that already-proved fact finishes it. This
//!   is why `dvd_mul_gcd_iff_dvd_mul` must be declared first.

use super::NatPrelude;
use super::helpers::and_right;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `eq(a,b) -> Iff (pred a) (pred b)`, for an arbitrary one-argument
/// proposition-valued `pred`. `Eq.rec` at the reflexive instance. Local copy
/// of the combinator in `gcd_dvd_mirrors.rs` -- see this development's
/// established convention (`mod_mul_lemmas.rs`'s module doc) of copying such
/// small proof-term combinators per file rather than sharing them.
fn pred_iff_of_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    eq_ab: ExprId,
    pred: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let pa = pred(d, a);
    let motive = d.eq_motive(a, &|d, x| {
        let px = pred(d, x);
        d.const_app(p.logic.iff, &[pa, px])
    });
    let refl_case = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let id = d.lam_fv(x_fv, pa, x);
        d.const_app(p.logic.iff_intro, &[pa, pa, id, id])
    };
    d.transport(a, motive, refl_case, b, eq_ab)
}

/// `h1 : Iff A B, h2 : Iff B C  ⊢  Iff A C`. Local copy.
fn iff_trans(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a_ty: ExprId,
    b_ty: ExprId,
    c_ty: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let p = *p;
    let mp = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let h1_mp = d.const_app(p.logic.iff_mp, &[a_ty, b_ty, h1]);
        let b_from_a = d.apply(h1_mp, &[a]);
        let h2_mp = d.const_app(p.logic.iff_mp, &[b_ty, c_ty, h2]);
        let c_from_b = d.apply(h2_mp, &[b_from_a]);
        d.lam_fv(a_fv, a_ty, c_from_b)
    };
    let mpr = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let h2_mpr = d.const_app(p.logic.iff_mpr, &[b_ty, c_ty, h2]);
        let b_from_c = d.apply(h2_mpr, &[c]);
        let h1_mpr = d.const_app(p.logic.iff_mpr, &[a_ty, b_ty, h1]);
        let a_from_b = d.apply(h1_mpr, &[b_from_c]);
        d.lam_fv(c_fv, c_ty, a_from_b)
    };
    d.const_app(p.logic.iff_intro, &[a_ty, c_ty, mp, mpr])
}

/// `Iff (dvd k (mul (gcd a b) c)) (dvd k (mul b c))`, given
/// `k_dvd_ac : dvd k (mul a c)` (always true at every call site here, via
/// `dvd_mul`). See the module doc for the derivation.
fn dvd_gcd_scaled_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    k: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    k_dvd_ac: ExprId,
) -> ExprId {
    let p = *p;
    let ac = d.mul(a, c);
    let bc = d.mul(b, c);
    let gab = d.gcd(a, b);
    let gab_c = d.mul(gab, c);
    let gac_bc = d.gcd(ac, bc);

    // gcd_mul_right(a,b,c) : Eq (gcd ac bc) (gcd a b * c)
    let gm = d.lemma(p.gcd_mul_right, &[a, b, c]);
    let gm_rev = d.symm(gac_bc, gab_c, gm); // Eq gab_c gac_bc

    let dvd_k_gab_c = d.dvd(k, gab_c);
    let dvd_k_gac_bc = d.dvd(k, gac_bc);
    let iff1 = pred_iff_of_eq(d, &p, gab_c, gac_bc, gm_rev, &|d, v| d.dvd(k, v));
    // iff1 : Iff (dvd k gab_c) (dvd k gac_bc)

    let iff2 = d.lemma(p.dvd_gcd_iff, &[k, ac, bc]);
    // iff2 : Iff (dvd k gac_bc) (And (dvd k ac) (dvd k bc))

    let dvd_k_ac = d.dvd(k, ac);
    let dvd_k_bc = d.dvd(k, bc);
    let and_ty = d.const_app(p.logic.and, &[dvd_k_ac, dvd_k_bc]);
    let iff3 = {
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let result = and_right(d, dvd_k_ac, dvd_k_bc, h);
            d.lam_fv(h_fv, and_ty, result)
        };
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let pair = d.const_app(p.logic.and_intro, &[dvd_k_ac, dvd_k_bc, k_dvd_ac, h]);
            d.lam_fv(h_fv, dvd_k_bc, pair)
        };
        d.const_app(p.logic.iff_intro, &[and_ty, dvd_k_bc, mp, mpr])
    };

    let combined = iff_trans(d, &p, dvd_k_gab_c, dvd_k_gac_bc, and_ty, iff1, iff2);
    iff_trans(d, &p, dvd_k_gab_c, and_ty, dvd_k_bc, combined, iff3)
}

/// Declares `Nat.dvd_gcd_mul_iff_dvd_mul`, `Nat.dvd_mul_gcd_iff_dvd_mul`, and
/// `Nat.dvd_gcd_mul_gcd_iff_dvd_mul` -- see the module doc. Must run after
/// `declare_gcd_mul_right` (`gcd_mul_right.rs`), `declare_gcd_semantics`
/// (`Nat.dvd_gcd_iff`, `gcd.rs`), `declare_divisibility` (`Nat.dvd_mul`), and
/// `declare_multiplicative_theorems` (`Nat.mul_comm`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if any constructed term does not
/// type-check.
pub(super) fn declare_gcd_mul_right_mirrors(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // `Nat.dvd_gcd_mul_iff_dvd_mul : ∀ k n m, k ∣ (gcd k n) * m ↔ k ∣ n * m`
    // -- `F:ml430-nat-dvd-gcd-mul-iff-dvd-mul-0afe640a`. The shape directly.
    d.theorem(p.dvd_gcd_mul_iff_dvd_mul, 3, &|d, values| {
        let (k, n, m) = (values[0], values[1], values[2]);
        let k_dvd_km = d.lemma(p.dvd_mul, &[k, m]); // dvd k (mul k m)
        let result = dvd_gcd_scaled_iff(d, &p, k, k, n, m, k_dvd_km);
        let gkn = d.gcd(k, n);
        let gkn_m = d.mul(gkn, m);
        let nm = d.mul(n, m);
        let lhs = d.dvd(k, gkn_m);
        let rhs = d.dvd(k, nm);
        (d.const_app(p.logic.iff, &[lhs, rhs]), result)
    })?;

    // `Nat.dvd_mul_gcd_iff_dvd_mul : ∀ k n m, k ∣ n * (gcd k m) ↔ k ∣ n * m`
    // -- `F:ml430-nat-dvd-mul-gcd-iff-dvd-mul-f9517e6b`. The scaling factor
    // is on the LEFT, so commute both sides of the shape (applied at
    // (a,b,c) := (k,m,n)) into place.
    d.theorem(p.dvd_mul_gcd_iff_dvd_mul, 3, &|d, values| {
        let (k, n, m) = (values[0], values[1], values[2]);
        let k_dvd_kn = d.lemma(p.dvd_mul, &[k, n]); // dvd k (mul k n)
        let base = dvd_gcd_scaled_iff(d, &p, k, k, m, n, k_dvd_kn);
        // base : Iff (dvd k (mul (gcd k m) n)) (dvd k (mul m n))

        let gkm = d.gcd(k, m);
        let gkm_n = d.mul(gkm, n);
        let n_gkm = d.mul(n, gkm);
        let mn = d.mul(m, n);
        let nm = d.mul(n, m);

        // Left side: mul (gcd k m) n = mul n (gcd k m).
        let comm_left = d.lemma(p.mul_comm, &[gkm, n]); // Eq gkm_n n_gkm
        let left_iff = pred_iff_of_eq(d, &p, gkm_n, n_gkm, comm_left, &|d, v| d.dvd(k, v));
        // left_iff : Iff (dvd k gkm_n) (dvd k n_gkm)
        let left_iff_rev = {
            let dvd_gkm_n = d.dvd(k, gkm_n);
            let dvd_n_gkm = d.dvd(k, n_gkm);
            let mp = d.const_app(p.logic.iff_mpr, &[dvd_gkm_n, dvd_n_gkm, left_iff]);
            let mpr = d.const_app(p.logic.iff_mp, &[dvd_gkm_n, dvd_n_gkm, left_iff]);
            d.const_app(p.logic.iff_intro, &[dvd_n_gkm, dvd_gkm_n, mp, mpr])
        };
        // left_iff_rev : Iff (dvd k n_gkm) (dvd k gkm_n)

        // Right side: mul m n = mul n m.
        let comm_right = d.lemma(p.mul_comm, &[m, n]); // Eq mn nm
        let right_iff = pred_iff_of_eq(d, &p, mn, nm, comm_right, &|d, v| d.dvd(k, v));
        // right_iff : Iff (dvd k mn) (dvd k nm)

        let dvd_n_gkm_ty = d.dvd(k, n_gkm);
        let dvd_gkm_n_ty = d.dvd(k, gkm_n);
        let dvd_mn_ty = d.dvd(k, mn);
        let dvd_nm_ty = d.dvd(k, nm);
        let step1 = iff_trans(
            d,
            &p,
            dvd_n_gkm_ty,
            dvd_gkm_n_ty,
            dvd_mn_ty,
            left_iff_rev,
            base,
        );
        let result = iff_trans(d, &p, dvd_n_gkm_ty, dvd_mn_ty, dvd_nm_ty, step1, right_iff);

        (d.const_app(p.logic.iff, &[dvd_n_gkm_ty, dvd_nm_ty]), result)
    })?;

    // `Nat.dvd_gcd_mul_gcd_iff_dvd_mul :
    //   ∀ k n m, k ∣ (gcd k n) * (gcd k m) ↔ k ∣ n * m` --
    // `F:ml430-nat-dvd-gcd-mul-gcd-iff-dvd-mul-07fec722`. The shape at
    // (a,b,c) := (k,n,gcd k m), then chain against `dvd_mul_gcd_iff_dvd_mul`.
    d.theorem(p.dvd_gcd_mul_gcd_iff_dvd_mul, 3, &|d, values| {
        let (k, n, m) = (values[0], values[1], values[2]);
        let gkm = d.gcd(k, m);
        let k_dvd_k_gkm = d.lemma(p.dvd_mul, &[k, gkm]); // dvd k (mul k (gcd k m))
        let base = dvd_gcd_scaled_iff(d, &p, k, k, n, gkm, k_dvd_k_gkm);
        // base : Iff (dvd k (mul (gcd k n) gkm)) (dvd k (mul n gkm))

        let tail = d.lemma(p.dvd_mul_gcd_iff_dvd_mul, &[k, n, m]);
        // tail : Iff (dvd k (mul n gkm)) (dvd k (mul n m))

        let gkn = d.gcd(k, n);
        let gkn_gkm = d.mul(gkn, gkm);
        let n_gkm = d.mul(n, gkm);
        let nm = d.mul(n, m);
        let lhs = d.dvd(k, gkn_gkm);
        let mid = d.dvd(k, n_gkm);
        let rhs = d.dvd(k, nm);
        let result = iff_trans(d, &p, lhs, mid, rhs, base, tail);

        (d.const_app(p.logic.iff, &[lhs, rhs]), result)
    })?;

    Ok(())
}
