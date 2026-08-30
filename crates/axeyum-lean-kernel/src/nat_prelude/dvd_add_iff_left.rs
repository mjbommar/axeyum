//! `Nat.dvd_add_iff_left : ∀ k m n, k ∣ n → (k ∣ m ↔ k ∣ (m+n))` —
//! `F:ml430-nat-dvd-add-iff-left-332cbe04`.
//!
//! `divisibility.rs`'s existing `dvd_add_iff_right(k,m,n,h : dvd k m) : Iff
//! (dvd k n) (dvd k (m+n))` is the mirror with the summands the other way
//! round. Instantiating it at `(k,n,m,h)` — swapping which summand carries
//! the hypothesis — gives `Iff (dvd k m) (dvd k (n+m))`, and transporting
//! along `add_comm n m : Eq (n+m) (m+n)` turns `n+m` into the `m+n` this
//! fact's conclusion actually names. No new case split or induction: this is
//! pure composition of `dvd_add_iff_right` and `add_comm`.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `h : Eq Nat a b  ⊢  Iff (pred a) (pred b)`, for an arbitrary `Nat -> Prop`.
/// `Eq.rec` at the reflexive instance. Local copy of the combinator this
/// development keeps per file (see `gcd_mul_right_mirrors.rs`'s module doc).
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

/// Declares `Nat.dvd_add_iff_left`. Must run after `declare_divisibility`
/// (`Nat.dvd_add_iff_right`) and `declare_arithmetic` (`Nat.add_comm`), both
/// far earlier in `build_nat_prelude`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_dvd_add_iff_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.dvd_add_iff_left, 3, &|d, values| {
        let (k, m, n) = (values[0], values[1], values[2]);
        let dvd_n_ty = d.dvd(k, n);
        let dvd_m_ty = d.dvd(k, m);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // `dvd_add_iff_right(k, n, m, h) : Iff (dvd k m) (dvd k (n+m))`.
        let base = d.lemma(p.dvd_add_iff_right, &[k, n, m, h]);

        let n_plus_m = d.add(n, m);
        let m_plus_n = d.add(m, n);
        let comm = d.lemma(p.add_comm, &[n, m]); // Eq Nat (n+m) (m+n)
        let right_iff = pred_iff_of_eq(d, &p, n_plus_m, m_plus_n, comm, &|d, v| d.dvd(k, v));
        // right_iff : Iff (dvd k (n+m)) (dvd k (m+n))

        let dvd_np_m = d.dvd(k, n_plus_m);
        let dvd_mp_n = d.dvd(k, m_plus_n);

        let result = iff_trans(d, &p, dvd_m_ty, dvd_np_m, dvd_mp_n, base, right_iff);
        let final_iff = d.const_app(p.logic.iff, &[dvd_m_ty, dvd_mp_n]);
        let proof = d.lam_fv(h_fv, dvd_n_ty, result);
        (d.arrow(dvd_n_ty, final_iff), proof)
    })?;

    Ok(())
}
