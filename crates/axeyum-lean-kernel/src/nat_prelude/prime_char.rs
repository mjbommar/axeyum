//! Characterizations of primality itself — the `Mathlib.Data.Nat.Prime.Defs`
//! mirrors (`Nat.Prime.one_le`, `.pos`, `.ne_zero`, `.eq_two_or_odd`,
//! `.not_prime_pow`, …), as opposed to the divisibility cluster
//! (`Nat.Prime.dvd_mul`, `.dvd_or_dvd`, `.dvd_iff_eq`, `.coprime_iff_not_dvd`,
//! `.coprime_pow_of_not_dvd`) declared in `primes.rs`/`bezout.rs`.
//!
//! This prelude has no `Prime` predicate — primality is spelled inline as
//! `2 ≤ x ∧ ∀ c, dvd c x → c = 1 ∨ c = x` (`primes.rs`'s own convention,
//! `factorization.rs`'s `PrimeCond`). Every mirror below states its Mathlib
//! source's `Nat.Prime` hypothesis with that inline predicate; this file has
//! established precedent in this repository (`prime_even_iff`,
//! `prime_odd_of_ne_two`, `prime_dvd_of_dvd_pow`, `prime_not_dvd_mul`,
//! `prime_pred_pos`, `five_le_of_ne_two_of_ne_three` all already flip
//! Mathlib's `Nat.Prime` this way), which is honest because every one of
//! these facts is itself an equivalence/characterization of primality, not a
//! theorem about a *different* structure Mathlib built `Nat.Prime` from.
//!
//! `prime_condition`/`prime_parts` here are a private per-file copy of
//! `primes.rs`'s (this repository's convention for `dvd_intro`/`dvd_elim` —
//! see that file's own comment — applies equally to this pair: every module
//! that needs the primality predicate builds its own copy rather than
//! exporting one, so two concurrent lanes touching `primes.rs` and this file
//! never collide). Because the predicate is built identically everywhere, two
//! independent constructions intern to the SAME `ExprId` (`axeyum-ir`'s
//! arena), so a proof built here composes seamlessly with a `prime_condition`
//! hypothesis built in `primes.rs`.

use super::NatPrelude;
use super::finite::{ne_of_lt, ne_symm};
use super::helpers::{and_left, and_right, iff_forward, transport_dvd_left, transport_dvd_right};
use super::ops::{NatDev, NatOps, cases_zero_succ, two_divisor_dichotomy};
use super::primes::{absurd, or_cases};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `2 ≤ x ∧ ∀ c, c ∣ x → c = 1 ∨ c = x` — primality, spelled inline. A
/// private copy of `primes::prime_condition` (see the module doc).
fn prime_condition(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let two = d.num(2);
    let unit = d.num(1);
    let lower = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hypothesis = d.dvd(c, x);
    let trivial = d.eq(c, unit);
    let whole = d.eq(c, x);
    let disjunction = d.const_app(p.logic.or, &[trivial, whole]);
    let body = d.arrow(hypothesis, disjunction);
    let divisors = d.pi_fv(c_fv, nat, body);
    d.const_app(p.logic.and, &[lower, divisors])
}

/// The two components of [`prime_condition`], so an `And` over it can be
/// split. A private copy of `primes::prime_parts`.
fn prime_parts(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let two = d.num(2);
    let unit = d.num(1);
    let lower = d.le(two, x);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hypothesis = d.dvd(c, x);
    let trivial = d.eq(c, unit);
    let whole = d.eq(c, x);
    let disjunction = d.const_app(p.logic.or, &[trivial, whole]);
    let body = d.arrow(hypothesis, disjunction);
    (lower, d.pi_fv(c_fv, nat, body))
}

/// Build a proof of `dvd a n` from a witness `q` and `eq_proof : Eq n (mul a
/// q)`. Copied per this file's own local convention (every `nat_prelude`
/// module that needs `dvd_intro` declares its own private copy).
fn dvd_intro(
    d: &mut NatDev<'_>,
    a: ExprId,
    n: ExprId,
    witness: ExprId,
    eq_proof: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let predicate = d.dvd_predicate(a, n);
    let intro_name = d.prelude().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[nat, predicate, witness, eq_proof])
}

/// Given `hp : prime_condition (pow x (succ (succ ndp)))`, derive `False`.
/// This is the shared content behind every "no prime is a proper power"
/// fact: `x` divides `x^(succ (succ ndp))` (witness `x^(succ ndp)`), so the
/// divisor clause forces `x = 1` or `x = x^(succ (succ ndp))`.
///
/// `x = 1` collapses the power to `1` via `one_pow`, contradicting the `2 ≤
/// x^n` lower bound (refuted via the defeq `Lt one one ≡ Le two one`, by
/// `lt_irrefl`).
///
/// `x = x^n` needs `n`'s predecessor `m := succ ndp` to itself have a
/// predecessor (`ndp`, supplied by the caller — every call site arrives via
/// two nested `cases_zero_succ`, so this is the branch where both exist).
/// The lower bound transports along `x = x^n` to `2 ≤ x`, which cancels the
/// shared factor `x` out of `x = x^n = x^m * x = x * x^m`
/// (`mul_left_cancel_of_pos`) to force `x^m = 1`; unfolding `x^m = x^ndp * x`
/// (`pow_succ` again) turns that into `x ∣ 1`, refuted by
/// `not_dvd_one_of_two_le` against the same `2 ≤ x`.
fn prime_pow_ge2_contradiction(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    ndp: ExprId,
    hp: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let two = d.num(2);
    let m = d.succ(ndp);
    let n = d.succ(m);
    let xn = d.pow(x, n);
    let (lower_ty, divisors_ty) = prime_parts(d, &p, xn);
    let lower_pf = and_left(d, lower_ty, divisors_ty, hp);
    let divisors_pf = and_right(d, lower_ty, divisors_ty, hp);

    let pow_x_m = d.pow(x, m);
    let pow_succ_eq = d.lemma(p.pow_succ, &[x, m]);
    let mul_pxm_x = d.mul(pow_x_m, x);
    let mul_x_pxm = d.mul(x, pow_x_m);
    let mul_comm_pf = d.lemma(p.mul_comm, &[pow_x_m, x]);
    let xn_eq_mul_x_pxm = d.trans(xn, mul_pxm_x, mul_x_pxm, pow_succ_eq, mul_comm_pf);

    let dvd_x_xn = dvd_intro(d, x, xn, pow_x_m, xn_eq_mul_x_pxm);
    let disj_x = d.apply(divisors_pf, &[x, dvd_x_xn]);

    let eq_x1_ty = d.eq(x, one);
    let eq_xxn_ty = d.eq(x, xn);
    let false_ty = {
        let logic = d.prelude().logic;
        d.kernel().const_(logic.false_, vec![])
    };

    let on_x1 = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let motive_x = d.eq_motive(x, &|d, xx| {
            let pw = d.pow(xx, n);
            d.le(two, pw)
        });
        let transported = d.transport(x, motive_x, lower_pf, one, h);
        let pow_one_n = d.pow(one, n);
        let one_pow_pf = d.lemma(p.one_pow, &[n]);
        let motive_y = d.eq_motive(pow_one_n, &|d, yy| d.le(two, yy));
        let transported2 = d.transport(pow_one_n, motive_y, transported, one, one_pow_pf);
        let refuted = d.lemma(p.lt_irrefl, &[one]);
        let false_val = d.apply(refuted, &[transported2]);
        d.lam_fv(h_fv, eq_x1_ty, false_val)
    };

    let on_xxn = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let h_sym = d.symm(x, xn, h);
        let motive_ge2 = d.eq_motive(xn, &|d, yy| d.le(two, yy));
        let x_ge2 = d.transport(xn, motive_ge2, lower_pf, x, h_sym);
        let le_succ_one = d.lemma(p.le_succ, &[one]);
        let one_le_x = d.lemma(p.le_trans, &[one, two, x, le_succ_one, x_ge2]);

        let eq_x_mul_x_powm = d.trans(x, xn, mul_x_pxm, h, xn_eq_mul_x_pxm);
        let mul_x_one = d.mul(x, one);
        let mul_one_x_pf = d.lemma(p.mul_one, &[x]);
        let cancel_input = d.trans(mul_x_one, x, mul_x_pxm, mul_one_x_pf, eq_x_mul_x_powm);
        let one_eq_powm = d.lemma(
            p.mul_left_cancel_of_pos,
            &[x, one, pow_x_m, one_le_x, cancel_input],
        );

        let pow_x_ndp = d.pow(x, ndp);
        let pow_succ_eq2 = d.lemma(p.pow_succ, &[x, ndp]);
        let mul_pndp_x = d.mul(pow_x_ndp, x);
        let pow_x_m_eq_1 = d.symm(one, pow_x_m, one_eq_powm);
        let mul_pndp_x_eq_powm = d.symm(pow_x_m, mul_pndp_x, pow_succ_eq2);
        let eq_mul_eq_one = d.trans(mul_pndp_x, pow_x_m, one, mul_pndp_x_eq_powm, pow_x_m_eq_1);

        let mul_x_pndp = d.mul(x, pow_x_ndp);
        let mul_comm3 = d.lemma(p.mul_comm, &[pow_x_ndp, x]);
        let one_eq_mul_pndp_x = d.symm(mul_pndp_x, one, eq_mul_eq_one);
        let eq_one_eq_mul_x_ndp =
            d.trans(one, mul_pndp_x, mul_x_pndp, one_eq_mul_pndp_x, mul_comm3);

        let dvd_x_1 = dvd_intro(d, x, one, pow_x_ndp, eq_one_eq_mul_x_ndp);
        let refuted2 = d.lemma(p.not_dvd_one_of_two_le, &[x, x_ge2]);
        let false_val = d.apply(refuted2, &[dvd_x_1]);
        d.lam_fv(h_fv, eq_xxn_ty, false_val)
    };

    or_cases(d, &p, eq_x1_ty, eq_xxn_ty, false_ty, on_x1, on_xxn, disj_x)
}

/// `Nat.Prime.one_le`, `.pos`, `.one_lt`, `.ne_zero`, `.ne_one`, and
/// `.not_dvd_one` — the six trivial numeric-bound characterizations, all
/// direct consequences of the `2 ≤ p` lower bound via the standing
/// `Lt a b ≡ Le (succ a) b` defeq.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_numeric_bounds(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.prime_one_le, 1, &|d, v| {
        let p_var = v[0];
        let one = d.num(1);
        let two = d.num(2);
        let prime_ty = prime_condition(d, &p, p_var);
        let goal = d.le(one, p_var);
        let stmt = d.arrow(prime_ty, goal);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let (lower_ty, divisors_ty) = prime_parts(d, &p, p_var);
        let lower_pf = and_left(d, lower_ty, divisors_ty, prime_hyp);
        let le_succ_one = d.lemma(p.le_succ, &[one]);
        let one_le_p = d.lemma(p.le_trans, &[one, two, p_var, le_succ_one, lower_pf]);
        let proof = d.lam_fv(prime_fv, prime_ty, one_le_p);
        (stmt, proof)
    })?;

    d.theorem(p.prime_pos, 1, &|d, v| {
        let p_var = v[0];
        let one = d.num(1);
        let two = d.num(2);
        let zero = d.zero();
        let prime_ty = prime_condition(d, &p, p_var);
        let goal = d.lt(zero, p_var);
        let stmt = d.arrow(prime_ty, goal);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let (lower_ty, divisors_ty) = prime_parts(d, &p, p_var);
        let lower_pf = and_left(d, lower_ty, divisors_ty, prime_hyp);
        let le_succ_one = d.lemma(p.le_succ, &[one]);
        let one_le_p = d.lemma(p.le_trans, &[one, two, p_var, le_succ_one, lower_pf]);
        // `Lt zero p_var` is definitionally `Le (succ zero) p_var` = `Le one p_var`.
        let proof = d.lam_fv(prime_fv, prime_ty, one_le_p);
        (stmt, proof)
    })?;

    d.theorem(p.prime_one_lt, 1, &|d, v| {
        let p_var = v[0];
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let goal = d.lt(one, p_var);
        let stmt = d.arrow(prime_ty, goal);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let (lower_ty, divisors_ty) = prime_parts(d, &p, p_var);
        let lower_pf = and_left(d, lower_ty, divisors_ty, prime_hyp);
        // `Lt one p_var` is definitionally `Le (succ one) p_var` = `Le two
        // p_var`, exactly `lower_pf`'s type.
        let proof = d.lam_fv(prime_fv, prime_ty, lower_pf);
        (stmt, proof)
    })?;

    d.theorem(p.prime_ne_zero, 1, &|d, v| {
        let p_var = v[0];
        let one = d.num(1);
        let two = d.num(2);
        let zero = d.zero();
        let prime_ty = prime_condition(d, &p, p_var);
        let eq_ty = d.eq(p_var, zero);
        let goal = d.const_app(p.logic.not, &[eq_ty]);
        let stmt = d.arrow(prime_ty, goal);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let (lower_ty, divisors_ty) = prime_parts(d, &p, p_var);
        let lower_pf = and_left(d, lower_ty, divisors_ty, prime_hyp);
        let le_succ_one = d.lemma(p.le_succ, &[one]);
        let one_le_p = d.lemma(p.le_trans, &[one, two, p_var, le_succ_one, lower_pf]);
        // `one_le_p : Le one p_var`, definitionally `Lt zero p_var`.
        let zero_ne_p = ne_of_lt(d, &p, zero, p_var, one_le_p);
        let p_ne_zero = ne_symm(d, zero, p_var, zero_ne_p);
        let proof = d.lam_fv(prime_fv, prime_ty, p_ne_zero);
        (stmt, proof)
    })?;

    d.theorem(p.prime_ne_one, 1, &|d, v| {
        let p_var = v[0];
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let eq_ty = d.eq(p_var, one);
        let goal = d.const_app(p.logic.not, &[eq_ty]);
        let stmt = d.arrow(prime_ty, goal);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let (lower_ty, divisors_ty) = prime_parts(d, &p, p_var);
        let lower_pf = and_left(d, lower_ty, divisors_ty, prime_hyp);
        // `lower_pf : Le two p_var`, definitionally `Lt one p_var`.
        let one_ne_p = ne_of_lt(d, &p, one, p_var, lower_pf);
        let p_ne_one = ne_symm(d, one, p_var, one_ne_p);
        let proof = d.lam_fv(prime_fv, prime_ty, p_ne_one);
        (stmt, proof)
    })?;

    d.theorem(p.prime_not_dvd_one, 1, &|d, v| {
        let p_var = v[0];
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let dvd_ty = d.dvd(p_var, one);
        let goal = d.const_app(p.logic.not, &[dvd_ty]);
        let stmt = d.arrow(prime_ty, goal);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let (lower_ty, divisors_ty) = prime_parts(d, &p, p_var);
        let lower_pf = and_left(d, lower_ty, divisors_ty, prime_hyp);
        let refuted = d.lemma(p.not_dvd_one_of_two_le, &[p_var, lower_pf]);
        let proof = d.lam_fv(prime_fv, prime_ty, refuted);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.Prime.eq_one_or_self_of_dvd` — exactly `prime_condition`'s divisor
/// clause, read out with `and_right`; no further proof content.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_eq_one_or_self_of_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_eq_one_or_self_of_dvd, 1, &|d, v| {
        let p_var = v[0];
        let prime_ty = prime_condition(d, &p, p_var);
        let (lower_ty, divisors_ty) = prime_parts(d, &p, p_var);
        let stmt = d.arrow(prime_ty, divisors_ty);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let divisors_pf = and_right(d, lower_ty, divisors_ty, prime_hyp);
        let proof = d.lam_fv(prime_fv, prime_ty, divisors_pf);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.Prime.eq_two_or_odd'`, `.eq_two_or_odd`, and
/// `.mod_two_eq_one_iff_ne_two` — the parity characterizations, built from
/// the already-proved `prime_even_iff`/`prime_odd_of_ne_two`
/// (`primes.rs`) and `even_or_odd_exists`/`odd_iff_mod_two_eq_one`
/// (`parity.rs`).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_parity_facts(
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
        let eq2_ty = d.eq(p_var, two);
        let goal = d.const_app(p.logic.or, &[eq2_ty, odd_ty]);
        let stmt = d.arrow(prime_ty, goal);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let eo = d.lemma(p.even_or_odd_exists, &[p_var]);
        let iff_pf = d.lemma(p.prime_even_iff, &[p_var, prime_hyp]);
        let mp_fn = iff_forward(d, even_ty, eq2_ty, iff_pf);

        let on_even = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let eq2_pf = d.apply(mp_fn, &[h]);
            let inl = d.const_app(p.logic.or_inl, &[eq2_ty, odd_ty, eq2_pf]);
            d.lam_fv(h_fv, even_ty, inl)
        };
        let on_odd = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let inr = d.const_app(p.logic.or_inr, &[eq2_ty, odd_ty, h]);
            d.lam_fv(h_fv, odd_ty, inr)
        };
        let body = or_cases(d, &p, even_ty, odd_ty, goal, on_even, on_odd, eo);
        let proof = d.lam_fv(prime_fv, prime_ty, body);
        (stmt, proof)
    })?;

    d.theorem(p.prime_eq_two_or_odd_mod, 1, &|d, v| {
        let p_var = v[0];
        let two = d.num(2);
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let odd_ty = d.lemma(p.odd, &[p_var]);
        let eq2_ty = d.eq(p_var, two);
        let mod_pv = d.modulo(p_var, two);
        let mod1_ty = d.eq(mod_pv, one);
        let goal = d.const_app(p.logic.or, &[eq2_ty, mod1_ty]);
        let stmt = d.arrow(prime_ty, goal);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let prev = d.lemma(p.prime_eq_two_or_odd, &[p_var, prime_hyp]);
        let odd_iff = d.lemma(p.odd_iff_mod_two_eq_one, &[p_var]);
        let odd_mp = iff_forward(d, odd_ty, mod1_ty, odd_iff);

        let on_eq2 = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let inl = d.const_app(p.logic.or_inl, &[eq2_ty, mod1_ty, h]);
            d.lam_fv(h_fv, eq2_ty, inl)
        };
        let on_odd = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let mod1_pf = d.apply(odd_mp, &[h]);
            let inr = d.const_app(p.logic.or_inr, &[eq2_ty, mod1_ty, mod1_pf]);
            d.lam_fv(h_fv, odd_ty, inr)
        };
        let body = or_cases(d, &p, eq2_ty, odd_ty, goal, on_eq2, on_odd, prev);
        let proof = d.lam_fv(prime_fv, prime_ty, body);
        (stmt, proof)
    })?;

    d.theorem(p.prime_mod_two_eq_one_iff_ne_two, 1, &|d, v| {
        let p_var = v[0];
        let two = d.num(2);
        let one = d.num(1);
        let zero = d.zero();
        let prime_ty = prime_condition(d, &p, p_var);
        let mod_pv = d.modulo(p_var, two);
        let mod1_ty = d.eq(mod_pv, one);
        let eq2_ty = d.eq(p_var, two);
        let ne2_ty = d.const_app(p.logic.not, &[eq2_ty]);
        let goal = d.const_app(p.logic.iff, &[mod1_ty, ne2_ty]);
        let stmt = d.arrow(prime_ty, goal);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        // mp : mod p 2 = 1 -> Not (p = 2)
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let motive = d.eq_motive(p_var, &|d, xx| {
                let m = d.modulo(xx, two);
                d.eq(m, one)
            });
            let mod22_eq1 = d.transport(p_var, motive, h, two, h2);
            let mod22_val = d.modulo(two, two);
            let zero_eq_mod22 = d.refl(zero);
            let zero_eq_one = d.trans(zero, mod22_val, one, zero_eq_mod22, mod22_eq1);
            let one_ne_zero = d.lemma(p.succ_ne_zero, &[zero]);
            let zero_ne_one = ne_symm(d, one, zero, one_ne_zero);
            let false_val = d.apply(zero_ne_one, &[zero_eq_one]);
            let inner = d.lam_fv(h2_fv, eq2_ty, false_val);
            d.lam_fv(h_fv, mod1_ty, inner)
        };

        // mpr : Not (p = 2) -> mod p 2 = 1
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let odd_pf = d.lemma(p.prime_odd_of_ne_two, &[p_var, prime_hyp, h]);
            let odd_ty = d.lemma(p.odd, &[p_var]);
            let odd_iff = d.lemma(p.odd_iff_mod_two_eq_one, &[p_var]);
            let odd_mp = iff_forward(d, odd_ty, mod1_ty, odd_iff);
            let mod1_pf = d.apply(odd_mp, &[odd_pf]);
            d.lam_fv(h_fv, ne2_ty, mod1_pf)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[mod1_ty, ne2_ty, mp, mpr]);
        let proof = d.lam_fv(prime_fv, prime_ty, iff_proof);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.Prime.not_prime_pow` (`2 ≤ n` form), `.not_prime_pow'` (`n ≠ 1`
/// form), and `.eq_one_of_pow` — all three read the SAME three-way case
/// split on `n` (`0`, `1`, `succ (succ _)`), sharing
/// [`prime_pow_ge2_contradiction`] for the real `n ≥ 2` case.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_not_prime_pow_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.prime_not_prime_pow_two_le, 2, &|d, v| {
        let (x, n) = (v[0], v[1]);
        let two = d.num(2);
        let bound_ty = d.le(two, n);
        let xn = d.pow(x, n);
        let prime_ty = prime_condition(d, &p, xn);
        let not_ty = d.const_app(p.logic.not, &[prime_ty]);
        let stmt = d.arrow(bound_ty, not_ty);

        let motive = |d: &mut NatDev<'_>, nn: ExprId| -> ExprId {
            let two_ = d.num(2);
            let bound = d.le(two_, nn);
            let xnn = d.pow(x, nn);
            let prime_ty2 = prime_condition(d, &p, xnn);
            let not_ty2 = d.const_app(p.logic.not, &[prime_ty2]);
            d.arrow(bound, not_ty2)
        };

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let one_ = d.num(1);
            let two_ = d.num(2);
            let zero_ = d.zero();
            let refuted = d.lemma(p.not_succ_le_zero, &[one_]);
            let false_val = d.apply(refuted, &[h2]);
            let x0 = d.pow(x, zero_);
            let prime0_ty = prime_condition(d, &p, x0);
            let not0_ty = d.const_app(p.logic.not, &[prime0_ty]);
            let inner = absurd(d, &p, not0_ty, false_val);
            let bound0 = d.le(two_, zero_);
            d.lam_fv(h2_fv, bound0, inner)
        };

        let at_succ = |d: &mut NatDev<'_>, n_prime: ExprId| -> ExprId {
            let motive2 = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
                let two_ = d.num(2);
                let succ_mm = d.succ(mm);
                let bound = d.le(two_, succ_mm);
                let x_succ_mm = d.pow(x, succ_mm);
                let prime_ty3 = prime_condition(d, &p, x_succ_mm);
                let not_ty3 = d.const_app(p.logic.not, &[prime_ty3]);
                d.arrow(bound, not_ty3)
            };

            let at_zero2 = |d: &mut NatDev<'_>| -> ExprId {
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let one_ = d.num(1);
                let two_ = d.num(2);
                let refuted = d.lemma(p.lt_irrefl, &[one_]);
                let false_val = d.apply(refuted, &[h2]);
                let x1 = d.pow(x, one_);
                let prime1_ty = prime_condition(d, &p, x1);
                let not1_ty = d.const_app(p.logic.not, &[prime1_ty]);
                let inner = absurd(d, &p, not1_ty, false_val);
                let bound1 = d.le(two_, one_);
                d.lam_fv(h2_fv, bound1, inner)
            };

            let at_succ2 = |d: &mut NatDev<'_>, ndp: ExprId| -> ExprId {
                let h2_fv = d.fresh_fvar();
                let hp_fv = d.fresh_fvar();
                let hp = d.kernel().fvar(hp_fv);
                let false_val = prime_pow_ge2_contradiction(d, &p, x, ndp, hp);
                let m_ = d.succ(ndp);
                let n_val = d.succ(m_);
                let xn_ = d.pow(x, n_val);
                let prime_n_ty = prime_condition(d, &p, xn_);
                let not_pf = d.lam_fv(hp_fv, prime_n_ty, false_val);
                let two_ = d.num(2);
                let bound2 = d.le(two_, n_val);
                d.lam_fv(h2_fv, bound2, not_pf)
            };

            cases_zero_succ(d, n_prime, &motive2, &at_zero2, &at_succ2)
        };

        let proof = cases_zero_succ(d, n, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    d.theorem(p.prime_not_prime_pow_ne_one, 2, &|d, v| {
        let (x, n) = (v[0], v[1]);
        let one = d.num(1);
        let ne_ty = {
            let eq_ty = d.eq(n, one);
            d.const_app(p.logic.not, &[eq_ty])
        };
        let xn = d.pow(x, n);
        let prime_ty = prime_condition(d, &p, xn);
        let not_ty = d.const_app(p.logic.not, &[prime_ty]);
        let stmt = d.arrow(ne_ty, not_ty);

        let motive = |d: &mut NatDev<'_>, nn: ExprId| -> ExprId {
            let one_ = d.num(1);
            let eq_ty = d.eq(nn, one_);
            let ne_ty2 = d.const_app(p.logic.not, &[eq_ty]);
            let xnn = d.pow(x, nn);
            let prime_ty2 = prime_condition(d, &p, xnn);
            let not_ty2 = d.const_app(p.logic.not, &[prime_ty2]);
            d.arrow(ne_ty2, not_ty2)
        };

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let ne_fv = d.fresh_fvar();
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            let zero_ = d.zero();
            let one_ = d.num(1);
            let two_ = d.num(2);
            let x0 = d.pow(x, zero_);
            let (lower_ty, divisors_ty) = prime_parts(d, &p, x0);
            let lower_pf = and_left(d, lower_ty, divisors_ty, hp);
            let pow_zero_pf = d.lemma(p.pow_zero, &[x]);
            let motive_x0 = d.eq_motive(x0, &|d, yy| d.le(two_, yy));
            let transported = d.transport(x0, motive_x0, lower_pf, one_, pow_zero_pf);
            let refuted = d.lemma(p.lt_irrefl, &[one_]);
            let false_val = d.apply(refuted, &[transported]);
            let prime0_ty = prime_condition(d, &p, x0);
            let not_pf = d.lam_fv(hp_fv, prime0_ty, false_val);
            let eq0_ty = d.eq(zero_, one_);
            let ne0_ty = d.const_app(p.logic.not, &[eq0_ty]);
            d.lam_fv(ne_fv, ne0_ty, not_pf)
        };

        let at_succ = |d: &mut NatDev<'_>, n_prime: ExprId| -> ExprId {
            let motive2 = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
                let one_ = d.num(1);
                let succ_mm = d.succ(mm);
                let eq_ty = d.eq(succ_mm, one_);
                let ne_ty2 = d.const_app(p.logic.not, &[eq_ty]);
                let x_succ_mm = d.pow(x, succ_mm);
                let prime_ty3 = prime_condition(d, &p, x_succ_mm);
                let not_ty3 = d.const_app(p.logic.not, &[prime_ty3]);
                d.arrow(ne_ty2, not_ty3)
            };

            let at_zero2 = |d: &mut NatDev<'_>| -> ExprId {
                let ne_fv = d.fresh_fvar();
                let ne_hyp = d.kernel().fvar(ne_fv);
                let one_ = d.num(1);
                let refl_one = d.refl(one_);
                let false_val = d.apply(ne_hyp, &[refl_one]);
                let x1 = d.pow(x, one_);
                let prime1_ty = prime_condition(d, &p, x1);
                let not1_ty = d.const_app(p.logic.not, &[prime1_ty]);
                let inner = absurd(d, &p, not1_ty, false_val);
                let eq1_ty = d.eq(one_, one_);
                let ne1_ty = d.const_app(p.logic.not, &[eq1_ty]);
                d.lam_fv(ne_fv, ne1_ty, inner)
            };

            let at_succ2 = |d: &mut NatDev<'_>, ndp: ExprId| -> ExprId {
                let ne_fv = d.fresh_fvar();
                let hp_fv = d.fresh_fvar();
                let hp = d.kernel().fvar(hp_fv);
                let false_val = prime_pow_ge2_contradiction(d, &p, x, ndp, hp);
                let m_ = d.succ(ndp);
                let n_val = d.succ(m_);
                let xn_ = d.pow(x, n_val);
                let prime_n_ty = prime_condition(d, &p, xn_);
                let not_pf = d.lam_fv(hp_fv, prime_n_ty, false_val);
                let one_ = d.num(1);
                let eq_ty = d.eq(n_val, one_);
                let ne_ty2 = d.const_app(p.logic.not, &[eq_ty]);
                d.lam_fv(ne_fv, ne_ty2, not_pf)
            };

            cases_zero_succ(d, n_prime, &motive2, &at_zero2, &at_succ2)
        };

        let proof = cases_zero_succ(d, n, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    d.theorem(p.prime_eq_one_of_pow, 2, &|d, v| {
        let (x, n) = (v[0], v[1]);
        let one = d.num(1);
        let xn = d.pow(x, n);
        let prime_ty = prime_condition(d, &p, xn);
        let goal = d.eq(n, one);
        let stmt = d.arrow(prime_ty, goal);

        let motive = |d: &mut NatDev<'_>, nn: ExprId| -> ExprId {
            let one_ = d.num(1);
            let xnn = d.pow(x, nn);
            let prime_ty2 = prime_condition(d, &p, xnn);
            let goal2 = d.eq(nn, one_);
            d.arrow(prime_ty2, goal2)
        };

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let hp_fv = d.fresh_fvar();
            let hp = d.kernel().fvar(hp_fv);
            let zero_ = d.zero();
            let one_ = d.num(1);
            let two_ = d.num(2);
            let x0 = d.pow(x, zero_);
            let (lower_ty, divisors_ty) = prime_parts(d, &p, x0);
            let lower_pf = and_left(d, lower_ty, divisors_ty, hp);
            let pow_zero_pf = d.lemma(p.pow_zero, &[x]);
            let motive_x0 = d.eq_motive(x0, &|d, yy| d.le(two_, yy));
            let transported = d.transport(x0, motive_x0, lower_pf, one_, pow_zero_pf);
            let refuted = d.lemma(p.lt_irrefl, &[one_]);
            let false_val = d.apply(refuted, &[transported]);
            let eq0_ty = d.eq(zero_, one_);
            let inner = absurd(d, &p, eq0_ty, false_val);
            let prime0_ty = prime_condition(d, &p, x0);
            d.lam_fv(hp_fv, prime0_ty, inner)
        };

        let at_succ = |d: &mut NatDev<'_>, n_prime: ExprId| -> ExprId {
            let motive2 = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
                let one_ = d.num(1);
                let succ_mm = d.succ(mm);
                let x_succ_mm = d.pow(x, succ_mm);
                let prime_ty3 = prime_condition(d, &p, x_succ_mm);
                let goal3 = d.eq(succ_mm, one_);
                d.arrow(prime_ty3, goal3)
            };

            let at_zero2 = |d: &mut NatDev<'_>| -> ExprId {
                let hp_fv = d.fresh_fvar();
                let one_ = d.num(1);
                let x1 = d.pow(x, one_);
                let prime1_ty = prime_condition(d, &p, x1);
                let refl_one = d.refl(one_);
                d.lam_fv(hp_fv, prime1_ty, refl_one)
            };

            let at_succ2 = |d: &mut NatDev<'_>, ndp: ExprId| -> ExprId {
                let hp_fv = d.fresh_fvar();
                let hp = d.kernel().fvar(hp_fv);
                let false_val = prime_pow_ge2_contradiction(d, &p, x, ndp, hp);
                let m_ = d.succ(ndp);
                let n_val = d.succ(m_);
                let one_ = d.num(1);
                let xn_ = d.pow(x, n_val);
                let prime_n_ty = prime_condition(d, &p, xn_);
                let eq_ty = d.eq(n_val, one_);
                let inner = absurd(d, &p, eq_ty, false_val);
                d.lam_fv(hp_fv, prime_n_ty, inner)
            };

            cases_zero_succ(d, n_prime, &motive2, &at_zero2, &at_succ2)
        };

        let proof = cases_zero_succ(d, n, &motive, &at_zero, &at_succ);
        (stmt, proof)
    })?;

    Ok(())
}

/// `2 ≤ 2 ∧ ∀ c, c ∣ 2 → c = 1 ∨ c = 2` — a private copy of
/// `primes::prime_two`, built from `ops::two_divisor_dichotomy` rather than
/// re-deriving that dichotomy's own arithmetic a third time.
fn prime_two(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let two = d.num(2);
    let (lower_ty, divisors_ty) = prime_parts(d, &p, two);
    let lower = d.const_app(p.le_refl, &[two]);
    let clause = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let dvd_c2 = d.dvd(c, two);
        let disjunction_proof = two_divisor_dichotomy(d, &p, c, hyp);
        let clause_body = d.lam_fv(hyp_fv, dvd_c2, disjunction_proof);
        d.lam_fv(c_fv, nat, clause_body)
    };
    d.const_app(p.logic.and_intro, &[lower_ty, divisors_ty, lower, clause])
}

/// A private copy of `primes.rs`'s `dvd_elim` (see this file's module doc).
fn dvd_elim(
    d: &mut NatDev<'_>,
    divisor: ExprId,
    dividend: ExprId,
    goal: ExprId,
    dvd_hyp: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let predicate = d.dvd_predicate(divisor, dividend);
    let dvd_ty = d.dvd(divisor, dividend);
    let motive = d.kernel().lam(anon, dvd_ty, goal, BinderInfo::Default);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let divisor_q = d.mul(divisor, q);
        let eq_ty = d.eq(dividend, divisor_q);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);
        let body = continuation(d, q, eq_proof);
        let with_eq = d.lam_fv(eq_fv, eq_ty, body);
        d.lam_fv(q_fv, nat, with_eq)
    };
    let exists_rec_name = d.prelude().logic.exists_rec;
    let rec = d.kernel().const_(exists_rec_name, vec![one]);
    d.apply(rec, &[nat, predicate, motive, minor, dvd_hyp])
}

/// `fun x => (2 ≤ x ∧ ∀ c, c ∣ x → c = 1 ∨ c = x) ∧ x ∣ m`. A private copy
/// of `primes::prime_divisor_predicate`.
fn prime_divisor_predicate(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let prime = prime_condition(d, p, x);
    let divides = d.dvd(x, m);
    let body = d.const_app(p.logic.and, &[prime, divides]);
    d.lam_fv(x_fv, nat, body)
}

/// Eliminate `exists_proof : ∃ pw, prime_condition pw ∧ dvd pw target`,
/// continuing with the witness `pw` and the split-out `(prime_pw,
/// dvd_pw_target)` pair to build a proof of `goal` (which must not mention
/// `pw`). A private copy of `primes::eliminate_prime_dvd`.
fn eliminate_prime_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    target: ExprId,
    goal: ExprId,
    exists_proof: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let level = d.level_one();
    let anon = d.anon_name();
    let predicate = prime_divisor_predicate(d, &p, target);
    let source_ty = {
        let exists = d.kernel().const_(p.logic.exists_, vec![level]);
        d.apply(exists, &[nat, predicate])
    };
    let motive = d.kernel().lam(anon, source_ty, goal, BinderInfo::Default);
    let minor = {
        let pw_fv = d.fresh_fvar();
        let pw = d.kernel().fvar(pw_fv);
        let prime_pw_ty = prime_condition(d, &p, pw);
        let dvd_pw_target_ty = d.dvd(pw, target);
        let hpand_ty = d.const_app(p.logic.and, &[prime_pw_ty, dvd_pw_target_ty]);
        let hpand_fv = d.fresh_fvar();
        let hpand = d.kernel().fvar(hpand_fv);
        let prime_pw = and_left(d, prime_pw_ty, dvd_pw_target_ty, hpand);
        let dvd_pw_target = and_right(d, prime_pw_ty, dvd_pw_target_ty, hpand);
        let body = continuation(d, pw, prime_pw, dvd_pw_target);
        let with_hpand = d.lam_fv(hpand_fv, hpand_ty, body);
        d.lam_fv(pw_fv, nat, with_hpand)
    };
    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level]);
    d.apply(exists_rec, &[nat, predicate, motive, minor, exists_proof])
}

/// `fun p => prime_condition p ∧ (dvd p m ∧ dvd p n)` — the witness
/// predicate for `prime_not_coprime_iff_dvd`.
fn not_coprime_witness_predicate(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let pw_fv = d.fresh_fvar();
    let pw = d.kernel().fvar(pw_fv);
    let prime_pw_ty = prime_condition(d, p, pw);
    let dvd_pw_m_ty = d.dvd(pw, m);
    let dvd_pw_n_ty = d.dvd(pw, n);
    let pair_ty = d.const_app(p.logic.and, &[dvd_pw_m_ty, dvd_pw_n_ty]);
    let body = d.const_app(p.logic.and, &[prime_pw_ty, pair_ty]);
    d.lam_fv(pw_fv, nat, body)
}

/// `∃ p, prime_condition p ∧ (dvd p m ∧ dvd p n)`.
fn not_coprime_witness_exists(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let predicate = not_coprime_witness_predicate(d, p, m, n);
    let level = d.level_one();
    let exists = d.kernel().const_(p.logic.exists_, vec![level]);
    d.apply(exists, &[nat, predicate])
}

/// Build `Exists.intro w (And.intro prime_w (And.intro dvd_w_m dvd_w_n)) : ∃
/// p, prime_condition p ∧ (dvd p m ∧ dvd p n)`.
#[allow(clippy::too_many_arguments)]
fn not_coprime_intro(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    w: ExprId,
    prime_w: ExprId,
    dvd_w_m: ExprId,
    dvd_w_n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let prime_w_ty = prime_condition(d, p, w);
    let dvd_w_m_ty = d.dvd(w, m);
    let dvd_w_n_ty = d.dvd(w, n);
    let pair_ty = d.const_app(p.logic.and, &[dvd_w_m_ty, dvd_w_n_ty]);
    let pair = d.const_app(
        p.logic.and_intro,
        &[dvd_w_m_ty, dvd_w_n_ty, dvd_w_m, dvd_w_n],
    );
    let full_ty = d.const_app(p.logic.and, &[prime_w_ty, pair_ty]);
    let full = d.const_app(p.logic.and_intro, &[prime_w_ty, pair_ty, prime_w, pair]);
    let predicate = not_coprime_witness_predicate(d, p, m, n);
    let level = d.level_one();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![level]);
    let _ = full_ty;
    d.apply(intro, &[nat, predicate, w, full])
}

/// Eliminate `exists_proof : ∃ p, prime_condition p ∧ (dvd p m ∧ dvd p n)`,
/// continuing with the witness and its three destructured components to
/// build a proof of `goal` (which must not mention the witness).
#[allow(clippy::too_many_arguments)]
fn eliminate_not_coprime_witness(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    goal: ExprId,
    exists_proof: ExprId,
    continuation: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let level = d.level_one();
    let anon = d.anon_name();
    let predicate = not_coprime_witness_predicate(d, &p, m, n);
    let source_ty = {
        let exists = d.kernel().const_(p.logic.exists_, vec![level]);
        d.apply(exists, &[nat, predicate])
    };
    let motive = d.kernel().lam(anon, source_ty, goal, BinderInfo::Default);
    let minor = {
        let pw_fv = d.fresh_fvar();
        let pw = d.kernel().fvar(pw_fv);
        let prime_pw_ty = prime_condition(d, &p, pw);
        let dvd_pw_m_ty = d.dvd(pw, m);
        let dvd_pw_n_ty = d.dvd(pw, n);
        let pair_ty = d.const_app(p.logic.and, &[dvd_pw_m_ty, dvd_pw_n_ty]);
        let full_ty = d.const_app(p.logic.and, &[prime_pw_ty, pair_ty]);
        let full_fv = d.fresh_fvar();
        let full = d.kernel().fvar(full_fv);
        let prime_pw = and_left(d, prime_pw_ty, pair_ty, full);
        let pair = and_right(d, prime_pw_ty, pair_ty, full);
        let dvd_pw_m = and_left(d, dvd_pw_m_ty, dvd_pw_n_ty, pair);
        let dvd_pw_n = and_right(d, dvd_pw_m_ty, dvd_pw_n_ty, pair);
        let body = continuation(d, pw, prime_pw, dvd_pw_m, dvd_pw_n);
        let with_full = d.lam_fv(full_fv, full_ty, body);
        d.lam_fv(pw_fv, nat, with_full)
    };
    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level]);
    d.apply(exists_rec, &[nat, predicate, motive, minor, exists_proof])
}

/// `Nat.Prime.not_coprime_iff_dvd : ∀ m n, Iff (Not (Eq (gcd m n) one)) (∃
/// p, prime_condition p ∧ (dvd p m ∧ dvd p n))` — see the `NatPrelude` field
/// doc for the route: `mpr` builds `p ∣ gcd m n` and refutes a hypothesised
/// `gcd m n = one` via `not_dvd_one_of_two_le`; `mp` trichotomizes `g := gcd
/// m n` exactly as `coprime_of_forall_prime_dvd` does.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_not_coprime_iff_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.prime_not_coprime_iff_dvd, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let one = d.num(1);
        let two = d.num(2);
        let zero = d.zero();
        let g = d.gcd(m, n);
        let eq_g1_ty = d.eq(g, one);
        let ne_ty = d.const_app(p.logic.not, &[eq_g1_ty]);
        let exists_ty = not_coprime_witness_exists(d, &p, m, n);
        let stmt = d.const_app(p.logic.iff, &[ne_ty, exists_ty]);

        let g_dvd_m = d.lemma(p.gcd_dvd_left, &[m, n]);
        let g_dvd_n = d.lemma(p.gcd_dvd_right, &[m, n]);

        // mp : Not (gcd m n = one) -> exists_ty
        let mp = {
            let hne_fv = d.fresh_fvar();
            let hne = d.kernel().fvar(hne_fv);

            let dich1 = d.lemma(p.lt_or_ge, &[g, one]);
            let lt_g1_ty = d.lt(g, one);
            let le_1g_ty = d.le(one, g);

            // Branch A: g < 1, i.e. g = 0. Forces m = n = 0, and `2 ∣ 0`
            // trivially witnesses both.
            let branch_a = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let le_g_zero = d.lemma(p.le_of_succ_le_succ, &[g, zero, h]);
                let zero_le_g = d.lemma(p.zero_le, &[g]);
                let g_eq_zero = d.lemma(p.le_antisymm, &[g, zero, le_g_zero, zero_le_g]);

                let zero_dvd_m = transport_dvd_left(d, g, zero, g_eq_zero, m, g_dvd_m);
                let zero_dvd_n = transport_dvd_left(d, g, zero, g_eq_zero, n, g_dvd_n);

                let m_eq_zero_ty = d.eq(m, zero);
                let m_eq_zero = dvd_elim(d, zero, m, m_eq_zero_ty, zero_dvd_m, &|d, q, eq_m_0q| {
                    let zero_q = d.mul(zero, q);
                    let zero_mul_eq = d.lemma(p.zero_mul, &[q]);
                    let (_, chained) = d.chain(m, &[(zero_q, eq_m_0q), (zero, zero_mul_eq)]);
                    chained
                });
                let n_eq_zero_ty = d.eq(n, zero);
                let n_eq_zero = dvd_elim(d, zero, n, n_eq_zero_ty, zero_dvd_n, &|d, q, eq_n_0q| {
                    let zero_q = d.mul(zero, q);
                    let zero_mul_eq = d.lemma(p.zero_mul, &[q]);
                    let (_, chained) = d.chain(n, &[(zero_q, eq_n_0q), (zero, zero_mul_eq)]);
                    chained
                });

                let prime_2 = prime_two(d, &p);
                let dvd_2_zero = d.lemma(p.dvd_zero, &[two]);
                let eq_zero_m = d.symm(m, zero, m_eq_zero);
                let eq_zero_n = d.symm(n, zero, n_eq_zero);
                let dvd_2_m = transport_dvd_right(d, two, zero, m, eq_zero_m, dvd_2_zero);
                let dvd_2_n = transport_dvd_right(d, two, zero, n, eq_zero_n, dvd_2_zero);

                let ex_proof = not_coprime_intro(d, &p, m, n, two, prime_2, dvd_2_m, dvd_2_n);
                d.lam_fv(h_fv, lt_g1_ty, ex_proof)
            };

            // Branch B: 1 ≤ g. Split again on g < 2 (so g = 1, contradicting
            // `hne` directly) vs 2 ≤ g (`exists_prime_dvd` supplies a prime
            // dividing `g`, hence both `m` and `n` via `dvd_trans`).
            let branch_b = {
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);

                let dich2 = d.lemma(p.lt_or_ge, &[g, two]);
                let lt_g2_ty = d.lt(g, two);
                let le_2g_ty = d.le(two, g);

                let branch_b1 = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv);
                    let le_g_1 = d.lemma(p.le_of_succ_le_succ, &[g, one, h2]);
                    let g_eq_1 = d.lemma(p.le_antisymm, &[g, one, le_g_1, h1]);
                    let false_val = d.apply(hne, &[g_eq_1]);
                    let branch_proof = absurd(d, &p, exists_ty, false_val);
                    d.lam_fv(h2_fv, lt_g2_ty, branch_proof)
                };

                let branch_b2 = {
                    let h2_fv = d.fresh_fvar();
                    let h2 = d.kernel().fvar(h2_fv);
                    let ex_proof = d.lemma(p.exists_prime_dvd, &[g, h2]);
                    let branch_proof = eliminate_prime_dvd(
                        d,
                        &p,
                        g,
                        exists_ty,
                        ex_proof,
                        &|d, pw, prime_pw, dvd_pw_g| {
                            let dvd_pw_m = d.lemma(p.dvd_trans, &[pw, g, m, dvd_pw_g, g_dvd_m]);
                            let dvd_pw_n = d.lemma(p.dvd_trans, &[pw, g, n, dvd_pw_g, g_dvd_n]);
                            not_coprime_intro(d, &p, m, n, pw, prime_pw, dvd_pw_m, dvd_pw_n)
                        },
                    );
                    d.lam_fv(h2_fv, le_2g_ty, branch_proof)
                };

                let body = or_cases(
                    d, &p, lt_g2_ty, le_2g_ty, exists_ty, branch_b1, branch_b2, dich2,
                );
                d.lam_fv(h1_fv, le_1g_ty, body)
            };

            let body = or_cases(
                d, &p, lt_g1_ty, le_1g_ty, exists_ty, branch_a, branch_b, dich1,
            );
            d.lam_fv(hne_fv, ne_ty, body)
        };

        // mpr : exists_ty -> Not (gcd m n = one)
        let mpr = {
            let hex_fv = d.fresh_fvar();
            let hex = d.kernel().fvar(hex_fv);
            let body = eliminate_not_coprime_witness(
                d,
                &p,
                m,
                n,
                ne_ty,
                hex,
                &|d, pw, prime_pw, dvd_pw_m, dvd_pw_n| {
                    let heq_fv = d.fresh_fvar();
                    let heq = d.kernel().fvar(heq_fv);
                    let dvd_pw_g = d.lemma(p.dvd_gcd, &[pw, m, n, dvd_pw_m, dvd_pw_n]);
                    let motive = d.eq_motive(g, &|d, yy| d.dvd(pw, yy));
                    let dvd_pw_1 = d.transport(g, motive, dvd_pw_g, one, heq);
                    let (lower_ty2, divisors_ty2) = prime_parts(d, &p, pw);
                    let two_le_pw = and_left(d, lower_ty2, divisors_ty2, prime_pw);
                    let refuted = d.lemma(p.not_dvd_one_of_two_le, &[pw, two_le_pw]);
                    let false_val = d.apply(refuted, &[dvd_pw_1]);
                    d.lam_fv(heq_fv, eq_g1_ty, false_val)
                },
            );
            d.lam_fv(hex_fv, exists_ty, body)
        };

        let proof = d.const_app(p.logic.iff_intro, &[ne_ty, exists_ty, mp, mpr]);
        (stmt, proof)
    })?;

    Ok(())
}

/// Given `prime_hyp : prime_condition p_var`, `dvd_p_a : dvd p_var a`, `ne_b
/// : Not (Eq b one)`, and `heq : Eq (mul a b) (mul p_var p_var)`, derive
/// `And (Eq a p_var) (Eq b p_var)`.
///
/// This is the shared content behind `prime_mul_eq_prime_sq_iff`'s `mp`,
/// generic in which of the two factors the divisor clause names: the
/// witness `k` from `a = p_var * k` substitutes into `heq` to give `k * b =
/// p_var` (`mul_assoc` + `mul_left_cancel_of_pos`, using `p_var`'s own
/// primality lower bound for positivity), and `k`'s primality clause
/// (`prime_eq_one_or_self_of_dvd`, applied to `k` via the divisor witness
/// `b`) forces `k = 1` (so `a = p_var` and, from `k * b = p_var`, `b =
/// p_var`) or `k = p_var` (so `b = 1` via the same cancellation, refuted
/// against `ne_b`). Call once per factor -- swapping `a`/`b` and rebuilding
/// `heq` via `mul_comm` -- to cover both branches of the divisor split.
#[allow(clippy::too_many_arguments)]
fn prime_sq_factor_case(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    p_var: ExprId,
    a: ExprId,
    b: ExprId,
    prime_hyp: ExprId,
    ne_b: ExprId,
    heq: ExprId,
    dvd_p_a: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let two = d.num(2);
    let goal_a = d.eq(a, p_var);
    let goal_b = d.eq(b, p_var);
    let goal = d.const_app(p.logic.and, &[goal_a, goal_b]);

    let (lower_ty, divisors_ty) = prime_parts(d, &p, p_var);
    let lower_pf = and_left(d, lower_ty, divisors_ty, prime_hyp);
    let le_succ_one = d.lemma(p.le_succ, &[one]);
    let one_le_p = d.lemma(p.le_trans, &[one, two, p_var, le_succ_one, lower_pf]);

    dvd_elim(d, p_var, a, goal, dvd_p_a, &|d, k, eq_a_pk| {
        let pk = d.mul(p_var, k);
        let kb = d.mul(k, b);
        let p_kb = d.mul(p_var, kb);
        let ab = d.mul(a, b);
        let pkb = d.mul(pk, b);
        let pp = d.mul(p_var, p_var);

        let assoc_pf = d.lemma(p.mul_assoc, &[p_var, k, b]);
        let a_eq_pk_under_mul = d.congr(a, pk, eq_a_pk, &|d, xx| d.mul(xx, b));
        let ab_eq_p_kb = d.trans(ab, pkb, p_kb, a_eq_pk_under_mul, assoc_pf);
        let p_kb_eq_ab = d.symm(ab, p_kb, ab_eq_p_kb);
        let p_kb_eq_pp = d.trans(p_kb, ab, pp, p_kb_eq_ab, heq);
        let kb_eq_p = d.lemma(
            p.mul_left_cancel_of_pos,
            &[p_var, kb, p_var, one_le_p, p_kb_eq_pp],
        );

        let p_eq_kb = d.symm(kb, p_var, kb_eq_p);
        let dvd_k_p = dvd_intro(d, k, p_var, b, p_eq_kb);
        let k_or = d.lemma(
            p.prime_eq_one_or_self_of_dvd,
            &[p_var, prime_hyp, k, dvd_k_p],
        );
        let eq_k1_ty = d.eq(k, one);
        let eq_kp_ty = d.eq(k, p_var);

        let on_k1 = {
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let hk_sym = d.symm(k, one, hk);
            let motive_a = d.eq_motive(one, &|d, xx| {
                let m = d.mul(p_var, xx);
                d.eq(m, p_var)
            });
            let mul_p_one = d.lemma(p.mul_one, &[p_var]);
            let pk_eq_p_at_k = d.transport(one, motive_a, mul_p_one, k, hk_sym);
            let a_eq_p = d.trans(a, pk, p_var, eq_a_pk, pk_eq_p_at_k);

            let motive_kb = d.eq_motive(k, &|d, kk| {
                let m = d.mul(kk, b);
                d.eq(m, p_var)
            });
            let kb_eq_p_at_one = d.transport(k, motive_kb, kb_eq_p, one, hk);
            let one_mul_b = d.lemma(p.one_mul, &[b]);
            let one_b = d.mul(one, b);
            let b_eq_one_b = d.symm(one_b, b, one_mul_b);
            let b_eq_p = d.trans(b, one_b, p_var, b_eq_one_b, kb_eq_p_at_one);

            let result = d.const_app(p.logic.and_intro, &[goal_a, goal_b, a_eq_p, b_eq_p]);
            d.lam_fv(hk_fv, eq_k1_ty, result)
        };

        let on_kp = {
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let motive_kb2 = d.eq_motive(k, &|d, kk| {
                let m = d.mul(kk, b);
                d.eq(m, p_var)
            });
            let pb_eq_p = d.transport(k, motive_kb2, kb_eq_p, p_var, hk);
            let mul_p_one2 = d.lemma(p.mul_one, &[p_var]);
            let p_one = d.mul(p_var, one);
            let p_eq_p_one = d.symm(p_one, p_var, mul_p_one2);
            let pb = d.mul(p_var, b);
            let cancel_in2 = d.trans(pb, p_var, p_one, pb_eq_p, p_eq_p_one);
            let b_eq_one = d.lemma(
                p.mul_left_cancel_of_pos,
                &[p_var, b, one, one_le_p, cancel_in2],
            );
            let false_val = d.apply(ne_b, &[b_eq_one]);
            let inner = absurd(d, &p, goal, false_val);
            d.lam_fv(hk_fv, eq_kp_ty, inner)
        };

        or_cases(d, &p, eq_k1_ty, eq_kp_ty, goal, on_k1, on_kp, k_or)
    })
}

/// `Nat.Prime.mul_eq_prime_sq_iff : ∀ x y p, prime_condition p → Not (Eq x
/// one) → Not (Eq y one) → Iff (Eq (mul x y) (pow p two)) (And (Eq x p) (Eq
/// y p))` — see the `NatPrelude` field doc for the route.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_mul_eq_prime_sq_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.prime_mul_eq_prime_sq_iff, 3, &|d, v| {
        let (x, y, p_var) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let two = d.num(2);
        let zero = d.zero();
        let prime_ty = prime_condition(d, &p, p_var);
        let ne_x_ty = {
            let e = d.eq(x, one);
            d.const_app(p.logic.not, &[e])
        };
        let ne_y_ty = {
            let e = d.eq(y, one);
            d.const_app(p.logic.not, &[e])
        };
        let xy = d.mul(x, y);
        let p2 = d.pow(p_var, two);
        let eq_ty = d.eq(xy, p2);
        let eq_x_p_ty = d.eq(x, p_var);
        let eq_y_p_ty = d.eq(y, p_var);
        let and_ty = d.const_app(p.logic.and, &[eq_x_p_ty, eq_y_p_ty]);
        let iff_ty = d.const_app(p.logic.iff, &[eq_ty, and_ty]);
        let inner1 = d.arrow(ne_y_ty, iff_ty);
        let inner2 = d.arrow(ne_x_ty, inner1);
        let stmt = d.arrow(prime_ty, inner2);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let nex_fv = d.fresh_fvar();
        let ne_x = d.kernel().fvar(nex_fv);
        let ney_fv = d.fresh_fvar();
        let ne_y = d.kernel().fvar(ney_fv);

        // pow2_eq_pp : Eq (pow p_var two) (mul p_var p_var), via `pow_succ`
        // twice and `pow_zero`/`one_mul` -- the same chain
        // `divisibility.rs`'s `valuation_at_two_mul_sq` already builds.
        let one_exp = d.succ(zero);
        let two_exp = d.succ(one_exp);
        let pow0 = d.pow(p_var, zero);
        let pow1 = d.pow(p_var, one_exp);
        let pow2v = d.pow(p_var, two_exp);
        let pp = d.mul(p_var, p_var);

        let pow1_step = d.mul(pow0, p_var);
        let one_p = d.mul(one, p_var);
        let h_pow1_step = d.lemma(p.pow_succ, &[p_var, zero]);
        let h_pow0 = d.lemma(p.pow_zero, &[p_var]);
        let h_pow0_under_mul = d.congr(pow0, one, h_pow0, &|d, xx| d.mul(xx, p_var));
        let h_one_mul = d.lemma(p.one_mul, &[p_var]);
        let (_, pow1_eq_p) = d.chain(
            pow1,
            &[
                (pow1_step, h_pow1_step),
                (one_p, h_pow0_under_mul),
                (p_var, h_one_mul),
            ],
        );
        let pow1_p = d.mul(pow1, p_var);
        let h_pow2_step = d.lemma(p.pow_succ, &[p_var, one_exp]);
        let h_pow1_under_mul = d.congr(pow1, p_var, pow1_eq_p, &|d, xx| d.mul(xx, p_var));
        let (_, pow2_eq_pp) = d.chain(pow2v, &[(pow1_p, h_pow2_step), (pp, h_pow1_under_mul)]);

        let dvd_x_ty = d.dvd(p_var, x);
        let dvd_y_ty = d.dvd(p_var, y);

        // mp : Eq xy p2 -> and_ty
        let mp = {
            let heq_fv = d.fresh_fvar();
            let heq = d.kernel().fvar(heq_fv);
            let xy_eq_pp = d.trans(xy, p2, pp, heq, pow2_eq_pp);
            let dvd_p_xy = dvd_intro(d, p_var, xy, p_var, xy_eq_pp);
            let split = d.lemma(p.euclid_lemma, &[p_var, x, y, prime_hyp, dvd_p_xy]);

            let on_x = {
                let hx_fv = d.fresh_fvar();
                let hx = d.kernel().fvar(hx_fv);
                let result =
                    prime_sq_factor_case(d, &p, p_var, x, y, prime_hyp, ne_y, xy_eq_pp, hx);
                d.lam_fv(hx_fv, dvd_x_ty, result)
            };
            let on_y = {
                let hy_fv = d.fresh_fvar();
                let hy = d.kernel().fvar(hy_fv);
                let mul_comm_yx = d.lemma(p.mul_comm, &[y, x]);
                let yx = d.mul(y, x);
                let yx_eq_pp = d.trans(yx, xy, pp, mul_comm_yx, xy_eq_pp);
                let swapped =
                    prime_sq_factor_case(d, &p, p_var, y, x, prime_hyp, ne_x, yx_eq_pp, hy);
                let y_eq_p = and_left(d, eq_y_p_ty, eq_x_p_ty, swapped);
                let x_eq_p = and_right(d, eq_y_p_ty, eq_x_p_ty, swapped);
                let result =
                    d.const_app(p.logic.and_intro, &[eq_x_p_ty, eq_y_p_ty, x_eq_p, y_eq_p]);
                d.lam_fv(hy_fv, dvd_y_ty, result)
            };
            let body = or_cases(d, &p, dvd_x_ty, dvd_y_ty, and_ty, on_x, on_y, split);
            d.lam_fv(heq_fv, eq_ty, body)
        };

        // mpr : and_ty -> Eq xy p2
        let mpr = {
            let hand_fv = d.fresh_fvar();
            let hand = d.kernel().fvar(hand_fv);
            let hx = and_left(d, eq_x_p_ty, eq_y_p_ty, hand);
            let hy = and_right(d, eq_x_p_ty, eq_y_p_ty, hand);
            let step1 = d.congr(x, p_var, hx, &|d, xx| d.mul(xx, y));
            let step2 = d.congr(y, p_var, hy, &|d, yy| d.mul(p_var, yy));
            let py = d.mul(p_var, y);
            let xy_eq_pp2 = d.trans(xy, py, pp, step1, step2);
            let pp_eq_p2 = d.symm(p2, pp, pow2_eq_pp);
            let result = d.trans(xy, pp, p2, xy_eq_pp2, pp_eq_p2);
            d.lam_fv(hand_fv, and_ty, result)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[eq_ty, and_ty, mp, mpr]);
        let with_ney = d.lam_fv(ney_fv, ne_y_ty, iff_proof);
        let with_nex = d.lam_fv(nex_fv, ne_x_ty, with_ney);
        let proof = d.lam_fv(prime_fv, prime_ty, with_nex);
        (stmt, proof)
    })?;

    Ok(())
}
