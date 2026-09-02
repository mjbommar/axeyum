//! The `ml430` prime-divisibility mirrors: the small consequences of
//! primality's own clause (`2 ≤ p ∧ ∀ c, c ∣ p → c = 1 ∨ c = p`) that were
//! never separately named, plus the `Coprime ↔ ¬dvd` bridge and the
//! multiplicativity-over-`p^m` corollary built on top of it.
//!
//! Nothing here needs a new induction principle or a new definition.
//! `euclid_lemma` (`bezout.rs`) already gives `Prime p → p ∣ m*n → p ∣ m ∨
//! p ∣ n`; everything below is that fact, `prime_condition`'s own two
//! conjuncts, and the existing order/gcd/parity library, recombined.
//!
//! `F:ml430-nat-prime-dvd-or-dvd-4ae88221` (`Prime p → p ∣ m*n → p ∣ m ∨ p ∣
//! n`) is not declared here at all — it is `Nat.euclid_lemma` verbatim, up
//! to the bound-variable names (`a,b` vs `m,n`), so the ledger fact is
//! flipped to cite `euclid_lemma` directly rather than re-proving it under a
//! second name.

use super::NatPrelude;
use super::finite::{ne_of_lt, ne_symm};
use super::helpers::{
    and_left, and_right, iff_forward, iff_reverse, transport_dvd_left, transport_dvd_right,
};
use super::ops::{NatDev, NatOps};
use super::parity::even_predicate;
use super::primes::{prime_condition, prime_parts};
use super::steps::absurd;
use super::steps::or_cases;
use crate::KernelError;
use crate::expr::ExprId;

/// `and_left` of [`prime_condition`]'s two conjuncts: `2 ≤ p_var`.
fn prime_two_le(d: &mut NatDev<'_>, p: &NatPrelude, p_var: ExprId, prime_hyp: ExprId) -> ExprId {
    let (lower, divisors) = prime_parts(d, p, p_var);
    and_left(d, lower, divisors, prime_hyp)
}

/// `and_right` of [`prime_condition`]'s two conjuncts: `∀ c, c ∣ p_var → c
/// = 1 ∨ c = p_var`.
fn prime_clause(d: &mut NatDev<'_>, p: &NatPrelude, p_var: ExprId, prime_hyp: ExprId) -> ExprId {
    let (lower, divisors) = prime_parts(d, p, p_var);
    and_right(d, lower, divisors, prime_hyp)
}

// ============================================================================
// `Nat.prime_ne_one`, `Nat.prime_ne_zero`, `Nat.prime_one_le`,
// `Nat.prime_one_lt`, `Nat.prime_pos`, `Nat.prime_not_dvd_one` — the six
// immediate order/disequality consequences of `2 ≤ p`.
// ============================================================================

/// `Nat.prime_one_lt : ∀ p, prime_condition p → Lt one p`. `Lt one p` is
/// `Le (succ one) p`, defeq to `Le two p` — [`prime_two_le`] directly.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_one_lt(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_one_lt, 1, &|d, v| {
        let p_var = v[0];
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let stmt = {
            let lt_ty = d.lt(one, p_var);
            d.arrow(prime_ty, lt_ty)
        };
        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let two_le_p = prime_two_le(d, &p, p_var, prime_hyp);
        let proof = d.lam_fv(prime_fv, prime_ty, two_le_p);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.prime_one_le : ∀ p, prime_condition p → Le one p`, via `le_trans`
/// from `Le one two` (`le_add_right one one`) and `Le two p`
/// ([`prime_two_le`]).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_one_le(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_one_le, 1, &|d, v| {
        let p_var = v[0];
        let one = d.num(1);
        let two = d.num(2);
        let prime_ty = prime_condition(d, &p, p_var);
        let stmt = {
            let le_ty = d.le(one, p_var);
            d.arrow(prime_ty, le_ty)
        };
        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let two_le_p = prime_two_le(d, &p, p_var, prime_hyp);
        let one_le_two = d.lemma(p.le_add_right, &[one, one]);
        let one_le_p = d.lemma(p.le_trans, &[one, two, p_var, one_le_two, two_le_p]);
        let proof = d.lam_fv(prime_fv, prime_ty, one_le_p);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.prime_pos : ∀ p, prime_condition p → Lt zero p`. `Lt zero p` is `Le
/// one p`, the exact type [`declare_prime_one_le`] already builds.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_pos(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_pos, 1, &|d, v| {
        let p_var = v[0];
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let prime_ty = prime_condition(d, &p, p_var);
        let stmt = {
            let lt_ty = d.lt(zero, p_var);
            d.arrow(prime_ty, lt_ty)
        };
        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let two_le_p = prime_two_le(d, &p, p_var, prime_hyp);
        let one_le_two = d.lemma(p.le_add_right, &[one, one]);
        let one_le_p = d.lemma(p.le_trans, &[one, two, p_var, one_le_two, two_le_p]);
        let proof = d.lam_fv(prime_fv, prime_ty, one_le_p);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.prime_ne_one : ∀ p, prime_condition p → Not (Eq p one)`, via
/// `ne_of_lt`/`ne_symm` on [`prime_two_le`] read as `Lt one p`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_ne_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_ne_one, 1, &|d, v| {
        let p_var = v[0];
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let ne_ty = {
            let eq_ty = d.eq(p_var, one);
            d.const_app(p.logic.not, &[eq_ty])
        };
        let stmt = d.arrow(prime_ty, ne_ty);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let two_le_p = prime_two_le(d, &p, p_var, prime_hyp);
        let one_ne_p = ne_of_lt(d, &p, one, p_var, two_le_p);
        let p_ne_one = ne_symm(d, one, p_var, one_ne_p);
        let proof = d.lam_fv(prime_fv, prime_ty, p_ne_one);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.prime_ne_zero : ∀ p, prime_condition p → Not (Eq p zero)`, via
/// `ne_of_lt`/`ne_symm` on `Le one p` ([`declare_prime_one_le`]'s witness,
/// rebuilt here) read as `Lt zero p`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_ne_zero(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_ne_zero, 1, &|d, v| {
        let p_var = v[0];
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let prime_ty = prime_condition(d, &p, p_var);
        let ne_ty = {
            let eq_ty = d.eq(p_var, zero);
            d.const_app(p.logic.not, &[eq_ty])
        };
        let stmt = d.arrow(prime_ty, ne_ty);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let two_le_p = prime_two_le(d, &p, p_var, prime_hyp);
        let one_le_two = d.lemma(p.le_add_right, &[one, one]);
        let one_le_p = d.lemma(p.le_trans, &[one, two, p_var, one_le_two, two_le_p]);
        let zero_ne_p = ne_of_lt(d, &p, zero, p_var, one_le_p);
        let p_ne_zero = ne_symm(d, zero, p_var, zero_ne_p);
        let proof = d.lam_fv(prime_fv, prime_ty, p_ne_zero);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.prime_not_dvd_one : ∀ p, prime_condition p → Not (dvd p one)`,
/// directly from `not_dvd_one_of_two_le` applied to [`prime_two_le`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_not_dvd_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_not_dvd_one, 1, &|d, v| {
        let p_var = v[0];
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let stmt = {
            let dvd_ty = d.dvd(p_var, one);
            let not_ty = d.const_app(p.logic.not, &[dvd_ty]);
            d.arrow(prime_ty, not_ty)
        };
        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let two_le_p = prime_two_le(d, &p, p_var, prime_hyp);
        let not_dvd = d.lemma(p.not_dvd_one_of_two_le, &[p_var, two_le_p]);
        let proof = d.lam_fv(prime_fv, prime_ty, not_dvd);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.prime_eq_one_or_self_of_dvd : ∀ p m, prime_condition p → dvd m p →
// Eq m one ∨ Eq m p`.
// ============================================================================

/// [`prime_clause`] applied at `m_var`, which already has exactly this
/// type.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_eq_one_or_self_of_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_eq_one_or_self_of_dvd, 2, &|d, v| {
        let (p_var, m_var) = (v[0], v[1]);
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let dvd_ty = d.dvd(m_var, p_var);
        let disj = {
            let is_one = d.eq(m_var, one);
            let is_p = d.eq(m_var, p_var);
            d.const_app(p.logic.or, &[is_one, is_p])
        };
        let stmt = {
            let inner = d.arrow(dvd_ty, disj);
            d.arrow(prime_ty, inner)
        };

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let dvd_fv = d.fresh_fvar();
        let dvd_hyp = d.kernel().fvar(dvd_fv);

        let clause_proof = prime_clause(d, &p, p_var, prime_hyp);
        let result = d.apply(clause_proof, &[m_var, dvd_hyp]);
        let with_dvd = d.lam_fv(dvd_fv, dvd_ty, result);
        let proof = d.lam_fv(prime_fv, prime_ty, with_dvd);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.prime_dvd_iff_eq : ∀ p a, prime_condition p → Not (Eq a one) → Iff
// (dvd a p) (Eq p a)`.
// ============================================================================

/// `mp`: the divisor clause at `a_var` gives `a = 1 ∨ a = p`; the `a = 1`
/// branch contradicts the hypothesis, the `a = p` branch is `symm`-ed into
/// the goal. `mpr`: `dvd_refl p` transported along `p = a`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_dvd_iff_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_dvd_iff_eq, 2, &|d, v| {
        let (p_var, a_var) = (v[0], v[1]);
        let one = d.num(1);

        let prime_ty = prime_condition(d, &p, p_var);
        let ne_ty = {
            let eq_ty = d.eq(a_var, one);
            d.const_app(p.logic.not, &[eq_ty])
        };
        let dvd_ty = d.dvd(a_var, p_var);
        let eq_ty = d.eq(p_var, a_var);
        let iff_target = d.const_app(p.logic.iff, &[dvd_ty, eq_ty]);
        let stmt = {
            let inner = d.arrow(ne_ty, iff_target);
            d.arrow(prime_ty, inner)
        };

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let ne_fv = d.fresh_fvar();
        let ne_hyp = d.kernel().fvar(ne_fv);

        let clause_proof = prime_clause(d, &p, p_var, prime_hyp);

        let mp = {
            let dvd_fv = d.fresh_fvar();
            let dvd_hyp = d.kernel().fvar(dvd_fv);
            let disj = d.apply(clause_proof, &[a_var, dvd_hyp]);
            let is_one_ty = d.eq(a_var, one);
            let is_p_ty = d.eq(a_var, p_var);
            let on_one = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let false_pf = d.apply(ne_hyp, &[h]);
                let body = absurd(d, eq_ty, false_pf);
                d.lam_fv(h_fv, is_one_ty, body)
            };
            let on_p = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let body = d.symm(a_var, p_var, h);
                d.lam_fv(h_fv, is_p_ty, body)
            };
            let case_result = or_cases(d, is_one_ty, is_p_ty, eq_ty, on_one, on_p, disj);
            d.lam_fv(dvd_fv, dvd_ty, case_result)
        };

        let mpr = {
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let dvd_pp = d.lemma(p.dvd_refl, &[p_var]);
            let result = transport_dvd_left(d, p_var, a_var, heq, p_var, dvd_pp);
            d.lam_fv(heq_fv, eq_ty, result)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[dvd_ty, eq_ty, mp, mpr]);
        let with_ne = d.lam_fv(ne_fv, ne_ty, iff_proof);
        let proof = d.lam_fv(prime_fv, prime_ty, with_ne);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.prime_dvd_mul_iff : ∀ p m n, prime_condition p → Iff (dvd p (mul m
// n)) (Or (dvd p m) (dvd p n))`.
// ============================================================================

/// `mp` is `euclid_lemma` applied (and left partially applied at the
/// hypothesis slot); `mpr` is `dvd_mul_right_of_dvd`/`dvd_mul_left_of_dvd`
/// case-split over the `Or`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_dvd_mul_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_dvd_mul_iff, 3, &|d, v| {
        let (p_var, m_var, n_var) = (v[0], v[1], v[2]);
        let prime_ty = prime_condition(d, &p, p_var);
        let mn = d.mul(m_var, n_var);
        let dvd_mn_ty = d.dvd(p_var, mn);
        let dvd_m_ty = d.dvd(p_var, m_var);
        let dvd_n_ty = d.dvd(p_var, n_var);
        let disj_ty = d.const_app(p.logic.or, &[dvd_m_ty, dvd_n_ty]);
        let iff_target = d.const_app(p.logic.iff, &[dvd_mn_ty, disj_ty]);
        let stmt = d.arrow(prime_ty, iff_target);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        let mp = d.lemma(p.euclid_lemma, &[p_var, m_var, n_var, prime_hyp]);

        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let on_m = {
                let hm_fv = d.fresh_fvar();
                let hm = d.kernel().fvar(hm_fv);
                let result = d.lemma(p.dvd_mul_right_of_dvd, &[p_var, m_var, n_var, hm]);
                d.lam_fv(hm_fv, dvd_m_ty, result)
            };
            let on_n = {
                let hn_fv = d.fresh_fvar();
                let hn = d.kernel().fvar(hn_fv);
                let result = d.lemma(p.dvd_mul_left_of_dvd, &[p_var, n_var, m_var, hn]);
                d.lam_fv(hn_fv, dvd_n_ty, result)
            };
            let case_result = or_cases(d, dvd_m_ty, dvd_n_ty, dvd_mn_ty, on_m, on_n, h);
            d.lam_fv(h_fv, disj_ty, case_result)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[dvd_mn_ty, disj_ty, mp, mpr]);
        let proof = d.lam_fv(prime_fv, prime_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.prime_coprime_iff_not_dvd : ∀ p n, prime_condition p → Iff (Eq (gcd p
// n) one) (Not (dvd p n))`.
// ============================================================================

/// `mp`: if `gcd p n = 1` and `p ∣ n` then (via `p ∣ p`, `dvd_gcd`)
/// `p ∣ gcd p n`, transported to `p ∣ 1` — refuted by
/// `not_dvd_one_of_two_le`. `mpr`: `g := gcd p n` divides `p`
/// (`gcd_dvd_left`), so the divisor clause forces `g = 1 ∨ g = p`; `g = 1`
/// **is** the goal, `g = p` transports `g ∣ n` (`gcd_dvd_right`) into `p ∣
/// n`, contradicting the hypothesis.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_coprime_iff_not_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_coprime_iff_not_dvd, 2, &|d, v| {
        let (p_var, n_var) = (v[0], v[1]);
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let gcd_pn = d.gcd(p_var, n_var);
        let cop_ty = d.eq(gcd_pn, one);
        let dvd_ty = d.dvd(p_var, n_var);
        let not_dvd_ty = d.const_app(p.logic.not, &[dvd_ty]);
        let iff_target = d.const_app(p.logic.iff, &[cop_ty, not_dvd_ty]);
        let stmt = d.arrow(prime_ty, iff_target);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let two_le_p = prime_two_le(d, &p, p_var, prime_hyp);

        let mp = {
            let cop_fv = d.fresh_fvar();
            let cop_hyp = d.kernel().fvar(cop_fv);
            let dvd_fv = d.fresh_fvar();
            let dvd_hyp = d.kernel().fvar(dvd_fv);

            let dvd_p_p = d.lemma(p.dvd_refl, &[p_var]);
            let dvd_p_gcd = d.lemma(p.dvd_gcd, &[p_var, p_var, n_var, dvd_p_p, dvd_hyp]);
            let dvd_p_1 = transport_dvd_right(d, p_var, gcd_pn, one, cop_hyp, dvd_p_gcd);
            let not_dvd_one = d.lemma(p.not_dvd_one_of_two_le, &[p_var, two_le_p]);
            let false_pf = d.apply(not_dvd_one, &[dvd_p_1]);
            let inner = d.lam_fv(dvd_fv, dvd_ty, false_pf);
            d.lam_fv(cop_fv, cop_ty, inner)
        };

        let mpr = {
            let notdvd_fv = d.fresh_fvar();
            let notdvd_hyp = d.kernel().fvar(notdvd_fv);

            let clause_proof = prime_clause(d, &p, p_var, prime_hyp);
            let g_dvd_p = d.lemma(p.gcd_dvd_left, &[p_var, n_var]);
            let disj = d.apply(clause_proof, &[gcd_pn, g_dvd_p]);

            let is_one_ty = d.eq(gcd_pn, one);
            let is_p_ty = d.eq(gcd_pn, p_var);

            let on_one = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                d.lam_fv(h_fv, is_one_ty, h)
            };
            let on_p = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let g_dvd_n = d.lemma(p.gcd_dvd_right, &[p_var, n_var]);
                let p_dvd_n = transport_dvd_left(d, gcd_pn, p_var, h, n_var, g_dvd_n);
                let false_pf = d.apply(notdvd_hyp, &[p_dvd_n]);
                let body = absurd(d, cop_ty, false_pf);
                d.lam_fv(h_fv, is_p_ty, body)
            };
            let case_result = or_cases(d, is_one_ty, is_p_ty, cop_ty, on_one, on_p, disj);
            d.lam_fv(notdvd_fv, not_dvd_ty, case_result)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[cop_ty, not_dvd_ty, mp, mpr]);
        let proof = d.lam_fv(prime_fv, prime_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.prime_eq_two_or_odd : ∀ p, prime_condition p → Or (Eq p two) (Odd
// p)` and `Nat.prime_eq_two_or_mod_two_eq_one : ∀ p, prime_condition p → Or
// (Eq p two) (Eq (mod p two) one)`.
// ============================================================================

/// `Nat.even_or_odd_exists` splits `p` into `Even p ∨ Odd p`; the `Even`
/// branch closes via `prime_even_iff`'s `mp`, the `Odd` branch **is** the
/// goal.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_eq_two_or_odd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_eq_two_or_odd, 1, &|d, v| {
        let p_var = v[0];
        let two = d.num(2);
        let prime_ty = prime_condition(d, &p, p_var);
        let even_ty = d.lemma(p.even, &[p_var]);
        let odd_ty = d.lemma(p.odd, &[p_var]);
        let eq_two_ty = d.eq(p_var, two);
        let goal = d.const_app(p.logic.or, &[eq_two_ty, odd_ty]);
        let stmt = d.arrow(prime_ty, goal);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let split = d.lemma(p.even_or_odd_exists, &[p_var]);

        let on_even = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let iff_pf = d.lemma(p.prime_even_iff, &[p_var, prime_hyp]);
            let mp_fn = iff_forward(d, even_ty, eq_two_ty, iff_pf);
            let peq2 = d.apply(mp_fn, &[h]);
            let injected = d.const_app(p.logic.or_inl, &[eq_two_ty, odd_ty, peq2]);
            d.lam_fv(h_fv, even_ty, injected)
        };
        let on_odd = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let injected = d.const_app(p.logic.or_inr, &[eq_two_ty, odd_ty, h]);
            d.lam_fv(h_fv, odd_ty, injected)
        };
        let result = or_cases(d, even_ty, odd_ty, goal, on_even, on_odd, split);
        let proof = d.lam_fv(prime_fv, prime_ty, result);
        (stmt, proof)
    })?;
    Ok(())
}

/// [`declare_prime_eq_two_or_odd`]'s exact case split, with the `Odd`
/// branch closed by `odd_iff_mod_two_eq_one` instead of returned directly.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_eq_two_or_mod_two_eq_one(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_eq_two_or_mod_two_eq_one, 1, &|d, v| {
        let p_var = v[0];
        let two = d.num(2);
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let even_ty = d.lemma(p.even, &[p_var]);
        let odd_ty = d.lemma(p.odd, &[p_var]);
        let eq_two_ty = d.eq(p_var, two);
        let mod_p2 = d.modulo(p_var, two);
        let mod_eq_one_ty = d.eq(mod_p2, one);
        let goal = d.const_app(p.logic.or, &[eq_two_ty, mod_eq_one_ty]);
        let stmt = d.arrow(prime_ty, goal);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let split = d.lemma(p.even_or_odd_exists, &[p_var]);

        let on_even = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let iff_pf = d.lemma(p.prime_even_iff, &[p_var, prime_hyp]);
            let mp_fn = iff_forward(d, even_ty, eq_two_ty, iff_pf);
            let peq2 = d.apply(mp_fn, &[h]);
            let injected = d.const_app(p.logic.or_inl, &[eq_two_ty, mod_eq_one_ty, peq2]);
            d.lam_fv(h_fv, even_ty, injected)
        };
        let on_odd = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let iff_pf2 = d.lemma(p.odd_iff_mod_two_eq_one, &[p_var]);
            let mp_fn2 = iff_forward(d, odd_ty, mod_eq_one_ty, iff_pf2);
            let modeq = d.apply(mp_fn2, &[h]);
            let injected = d.const_app(p.logic.or_inr, &[eq_two_ty, mod_eq_one_ty, modeq]);
            d.lam_fv(h_fv, odd_ty, injected)
        };
        let result = or_cases(d, even_ty, odd_ty, goal, on_even, on_odd, split);
        let proof = d.lam_fv(prime_fv, prime_ty, result);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.prime_mod_two_eq_one_iff_ne_two : ∀ p, prime_condition p → Iff (Eq
// (mod p two) one) (Not (Eq p two))`.
// ============================================================================

/// `mp` needs no primality at all: assuming `p = 2`, transport `mod p 2 = 1`
/// along it to `mod 2 2 = 1`, contradicting `mod 2 2 = 0`
/// (`even_iff_mod_two_eq_zero` applied to a hand-built `Even 2` witness) via
/// `succ_ne_zero`. `mpr` is [`declare_prime_eq_two_or_mod_two_eq_one`]'s
/// case split, with the `Even` branch now contradicting the hypothesis
/// instead of closing the goal.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_mod_two_eq_one_iff_ne_two(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_mod_two_eq_one_iff_ne_two, 1, &|d, v| {
        let p_var = v[0];
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let prime_ty = prime_condition(d, &p, p_var);
        let mod_p2 = d.modulo(p_var, two);
        let mod_eq_one_ty = d.eq(mod_p2, one);
        let eq_two_ty = d.eq(p_var, two);
        let ne_two_ty = d.const_app(p.logic.not, &[eq_two_ty]);
        let iff_target = d.const_app(p.logic.iff, &[mod_eq_one_ty, ne_two_ty]);
        let stmt = d.arrow(prime_ty, iff_target);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        // `Even 2`, built directly: witness `1`, `Eq 2 (add 1 1)` closes by
        // `refl` since `add 1 1` reduces to `2`.
        let even_two = {
            let nat = d.nat_ty();
            let level = d.level_one();
            let pred = even_predicate(d, two);
            let refl_two = d.refl(two);
            let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![level]);
            d.apply(exists_intro, &[nat, pred, one, refl_two])
        };
        let mod22_eq0 = {
            let iff_pf = d.lemma(p.even_iff_mod_two_eq_zero, &[two]);
            let even_two_ty = d.lemma(p.even, &[two]);
            let mod22 = d.modulo(two, two);
            let mod22_eq0_ty = d.eq(mod22, zero);
            let mp_fn = iff_forward(d, even_two_ty, mod22_eq0_ty, iff_pf);
            d.apply(mp_fn, &[even_two])
        };
        let zero_ne_one = {
            let one_ne_zero = d.lemma(p.succ_ne_zero, &[zero]);
            ne_symm(d, one, zero, one_ne_zero)
        };

        let mp = {
            let mod_fv = d.fresh_fvar();
            let mod_hyp = d.kernel().fvar(mod_fv);
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);

            let motive = d.eq_motive(p_var, &|d, x| {
                let mx2 = d.modulo(x, two);
                d.eq(mx2, one)
            });
            let mod22_eq1 = d.transport(p_var, motive, mod_hyp, two, heq);
            let mod22 = d.modulo(two, two);
            let zero_eq_mod22 = d.symm(mod22, zero, mod22_eq0);
            let zero_eq_one = d.trans(zero, mod22, one, zero_eq_mod22, mod22_eq1);
            let false_pf = d.apply(zero_ne_one, &[zero_eq_one]);
            let inner = d.lam_fv(heq_fv, eq_two_ty, false_pf);
            d.lam_fv(mod_fv, mod_eq_one_ty, inner)
        };

        let mpr = {
            let hne_fv = d.fresh_fvar();
            let hne = d.kernel().fvar(hne_fv);
            let even_ty = d.lemma(p.even, &[p_var]);
            let odd_ty = d.lemma(p.odd, &[p_var]);
            let split = d.lemma(p.even_or_odd_exists, &[p_var]);

            let on_even = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let iff_pf = d.lemma(p.prime_even_iff, &[p_var, prime_hyp]);
                let mp_fn = iff_forward(d, even_ty, eq_two_ty, iff_pf);
                let peq2 = d.apply(mp_fn, &[h]);
                let false_pf = d.apply(hne, &[peq2]);
                let body = absurd(d, mod_eq_one_ty, false_pf);
                d.lam_fv(h_fv, even_ty, body)
            };
            let on_odd = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let iff_pf2 = d.lemma(p.odd_iff_mod_two_eq_one, &[p_var]);
                let mp_fn2 = iff_forward(d, odd_ty, mod_eq_one_ty, iff_pf2);
                let result = d.apply(mp_fn2, &[h]);
                d.lam_fv(h_fv, odd_ty, result)
            };
            let result = or_cases(d, even_ty, odd_ty, mod_eq_one_ty, on_even, on_odd, split);
            d.lam_fv(hne_fv, ne_two_ty, result)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[mod_eq_one_ty, ne_two_ty, mp, mpr]);
        let proof = d.lam_fv(prime_fv, prime_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.prime_coprime_pow_of_not_dvd : ∀ p m a, prime_condition p → Not (dvd
// p a) → Eq (gcd a (pow p m)) one`.
// ============================================================================

/// Induction on `m`. `m = 0`: `pow p 0 ≡ 1`, and `gcd a 1 = 1` always
/// (`coprime_one_right_iff`). `m = succ j`: `pow p (succ j) ≡ mul (pow p j)
/// p`, and `coprime_mul_of_coprime` combines the induction hypothesis with
/// `gcd a p = 1` — derived once, outside the induction, from
/// [`declare_prime_coprime_iff_not_dvd`]'s `mpr` plus `coprime_symmetric`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_coprime_pow_of_not_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_coprime_pow_of_not_dvd, 3, &|d, v| {
        let (p_var, m_var, a_var) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let not_dvd_ty = {
            let dv = d.dvd(p_var, a_var);
            d.const_app(p.logic.not, &[dv])
        };

        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let px = d.pow(p_var, x);
            let g = d.gcd(a_var, px);
            d.eq(g, one)
        };
        let goal = motive(d, m_var);
        let stmt = {
            let inner = d.arrow(not_dvd_ty, goal);
            d.arrow(prime_ty, inner)
        };

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let notdvd_fv = d.fresh_fvar();
        let notdvd_hyp = d.kernel().fvar(notdvd_fv);

        let coprime_a_p = {
            let iff_pf = d.lemma(p.prime_coprime_iff_not_dvd, &[p_var, a_var, prime_hyp]);
            let gcd_pa = d.gcd(p_var, a_var);
            let cop_pa_ty = d.eq(gcd_pa, one);
            let mpr_fn = iff_reverse(d, cop_pa_ty, not_dvd_ty, iff_pf);
            let cop_pa = d.apply(mpr_fn, &[notdvd_hyp]);
            d.lemma(p.coprime_symmetric, &[p_var, a_var, cop_pa])
        };

        let proof_body = d.induct(
            &motive,
            &|d| {
                let true_ty = d.kernel().const_(p.logic.true_, vec![]);
                let true_intro = d.kernel().const_(p.logic.true_intro, vec![]);
                let iff_pf = d.lemma(p.coprime_one_right_iff, &[a_var]);
                let gcd_a1 = d.gcd(a_var, one);
                let cop_a1_ty = d.eq(gcd_a1, one);
                let mpr_fn = iff_reverse(d, cop_a1_ty, true_ty, iff_pf);
                d.apply(mpr_fn, &[true_intro])
            },
            &|d, j, ih| {
                let pj = d.pow(p_var, j);
                d.lemma(
                    p.coprime_mul_of_coprime,
                    &[a_var, pj, p_var, ih, coprime_a_p],
                )
            },
            m_var,
        );

        let with_notdvd = d.lam_fv(notdvd_fv, not_dvd_ty, proof_body);
        let proof = d.lam_fv(prime_fv, prime_ty, with_notdvd);
        (stmt, proof)
    })?;
    Ok(())
}

/// Register every declaration in this file, in dependency order.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_dvd_mirrors_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_prime_one_lt(d, p)?;
    declare_prime_one_le(d, p)?;
    declare_prime_pos(d, p)?;
    declare_prime_ne_one(d, p)?;
    declare_prime_ne_zero(d, p)?;
    declare_prime_not_dvd_one(d, p)?;
    declare_prime_eq_one_or_self_of_dvd(d, p)?;
    declare_prime_dvd_iff_eq(d, p)?;
    declare_prime_dvd_mul_iff(d, p)?;
    declare_prime_coprime_iff_not_dvd(d, p)?;
    declare_prime_eq_two_or_odd(d, p)?;
    declare_prime_eq_two_or_mod_two_eq_one(d, p)?;
    declare_prime_mod_two_eq_one_iff_ne_two(d, p)?;
    declare_prime_coprime_pow_of_not_dvd(d, p)?;
    Ok(())
}
