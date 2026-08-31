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
//!
//! The `Eq -> Iff` lift and the two-step `Iff` chain go through
//! [`crate::proof_plan`] (L3 D5) rather than a local `pred_iff_of_eq`/
//! `iff_trans` pair — this file used to carry its own copy of both (the
//! convention `gcd_mul_right_mirrors.rs`'s module doc used to describe),
//! duplicated in at least two other files. `proof_plan::iff_lift`/
//! `iff_chain` build the identical term shape; see
//! `proof_plan::tests::rewrite_iff_matches_pred_iff_of_eq`.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::proof_plan::{self, Template};

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
        let ctx = Template::App(p.dvd, vec![Template::Fixed(k), Template::Hole]);
        let right_iff = proof_plan::iff_lift(d, ctx, n_plus_m, m_plus_n, comm);
        // right_iff : Iff (dvd k (n+m)) (dvd k (m+n))

        let dvd_np_m = d.dvd(k, n_plus_m);
        let dvd_mp_n = d.dvd(k, m_plus_n);

        let result = proof_plan::iff_chain(d, dvd_m_ty, &[(dvd_np_m, base), (dvd_mp_n, right_iff)]);
        let final_iff = d.const_app(p.logic.iff, &[dvd_m_ty, dvd_mp_n]);
        let proof = d.lam_fv(h_fv, dvd_n_ty, result);
        (d.arrow(dvd_n_ty, final_iff), proof)
    })?;

    Ok(())
}
