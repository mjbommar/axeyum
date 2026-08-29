//! `Nat.IsRelPrime`: the "only common divisor is `1`" characterisation of
//! coprimality, and its equivalence with `Coprime` (`gcd m n = 1`).
//!
//! Mathlib's `IsRelPrime m n := ∀ d, d ∣ m → d ∣ n → IsUnit d`, specialized to
//! `Nat` (whose only unit is `1`) as `IsRelPrime m n := ∀ d, d ∣ m → d ∣ n →
//! d = 1`. This is a genuinely NEW predicate — unlike `Coprime`, which has no
//! separate name in this prelude and is always spelled `gcd m n = 1` inline
//! (see `primes.rs`'s module doc) — because `F:ml430-nat-coprime-iff-isrelprime`
//! is literally the statement that the two spellings agree, so both sides need
//! their own name to state.
//!
//! Both directions of the `Iff` are cheap once the predicate exists, using
//! exactly the divisibility characterisation this prelude already has for
//! every other `Coprime` fact (`gcd_dvd_left`/`_right`, `dvd_gcd`,
//! `eq_one_of_dvd_one`) rather than unfolding `Nat.gcd`'s own recursion (which
//! carries `Quot.sound` — see the CLAUDE.md gotcha on `Nat.gcd.eq_def`):
//!
//! - Forward (`gcd m n = 1 -> IsRelPrime m n`): given `d ∣ m` and `d ∣ n`,
//!   `dvd_gcd` gives `d ∣ gcd m n`, which transports along the hypothesis to
//!   `d ∣ 1`, and `eq_one_of_dvd_one` closes it.
//! - Backward (`IsRelPrime m n -> gcd m n = 1`): `gcd m n` divides both `m`
//!   and `n` (`gcd_dvd_left`/`gcd_dvd_right`), so applying the hypothesis at
//!   `d := gcd m n` gives the goal directly — no case analysis anywhere.

use super::NatPrelude;
use super::helpers::transport_dvd_right;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `∀ d, d ∣ m → d ∣ n → d = 1` — the unfolded body of `Nat.IsRelPrime m n`.
fn is_rel_prime_predicate(d: &mut NatDev<'_>, m: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.num(1);
    let dd_fv = d.fresh_fvar();
    let dd = d.kernel().fvar(dd_fv);
    let dvd_m = d.dvd(dd, m);
    let dvd_n = d.dvd(dd, n);
    let eq1 = d.eq(dd, one);
    let inner = d.arrow(dvd_n, eq1);
    let body = d.arrow(dvd_m, inner);
    d.pi_fv(dd_fv, nat, body)
}

/// `Nat.IsRelPrime m n := ∀ d, d ∣ m → d ∣ n → d = 1`. A `Definition`, not a
/// theorem — see the module doc for why this needs a name of its own at all
/// (unlike `Coprime`, which this prelude never names).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_is_rel_prime(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let pred = is_rel_prime_predicate(d, m, n);
    let with_n = d.lam_fv(n_fv, nat, pred);
    let value = d.lam_fv(m_fv, nat, with_n);

    let nat_to_prop = d.arrow(nat, prop);
    let ty = d.arrow(nat, nat_to_prop);

    d.kernel().add_declaration(Declaration::Definition {
        name: p.is_rel_prime,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(4),
    })?;
    Ok(())
}

/// `Nat.coprime_iff_isRelPrime : ∀ m n, Iff (Eq (gcd m n) one) (IsRelPrime m
/// n)`. Closes ledger fact `F:ml430-nat-coprime-iff-isrelprime-0c08eb25`. See
/// the module doc for the route — neither direction needs case analysis.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_iff_is_rel_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    d.theorem(p.coprime_iff_is_rel_prime, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let one = d.num(1);
        let g = d.gcd(m, n);
        let cop_ty = d.eq(g, one);
        let rp_ty = d.lemma(p.is_rel_prime, &[m, n]);

        // Forward: gcd m n = 1 -> IsRelPrime m n.
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let dd_fv = d.fresh_fvar();
            let dd = d.kernel().fvar(dd_fv);
            let hm_fv = d.fresh_fvar();
            let hm = d.kernel().fvar(hm_fv);
            let hn_fv = d.fresh_fvar();
            let hn = d.kernel().fvar(hn_fv);

            let dd_dvd_g = d.lemma(p.dvd_gcd, &[dd, m, n, hm, hn]);
            let dd_dvd_one = transport_dvd_right(d, dd, g, one, h, dd_dvd_g);
            let dd_eq_one = d.lemma(p.eq_one_of_dvd_one, &[dd, dd_dvd_one]);

            let dvd_m_ty = d.dvd(dd, m);
            let dvd_n_ty = d.dvd(dd, n);
            let inner = d.lam_fv(hn_fv, dvd_n_ty, dd_eq_one);
            let with_hm = d.lam_fv(hm_fv, dvd_m_ty, inner);
            let with_dd = d.lam_fv(dd_fv, nat, with_hm);
            d.lam_fv(h_fv, cop_ty, with_dd)
        };

        // Backward: IsRelPrime m n -> gcd m n = 1. Apply the hypothesis
        // directly at d := gcd m n; no unfolding needed beyond what the
        // kernel's own defeq check already does to see `rp_ty` as a Pi.
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let g_dvd_m = d.lemma(p.gcd_dvd_left, &[m, n]);
            let g_dvd_n = d.lemma(p.gcd_dvd_right, &[m, n]);
            let step1 = d.apply(h, &[g]);
            let step2 = d.apply(step1, &[g_dvd_m]);
            let g_eq_one = d.apply(step2, &[g_dvd_n]);
            d.lam_fv(h_fv, rp_ty, g_eq_one)
        };

        let stmt = d.const_app(p.logic.iff, &[cop_ty, rp_ty]);
        let proof = d.const_app(p.logic.iff_intro, &[cop_ty, rp_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}
