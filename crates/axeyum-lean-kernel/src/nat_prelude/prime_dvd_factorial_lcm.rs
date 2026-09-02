//! Four `ml430` prime mirrors over `Nat.factorial`/`Nat.descFactorial`/
//! `Nat.lcm`, closing `F:ml430-nat-prime-dvd-factorial-5ace903f`,
//! `F:ml430-nat-prime-coprime-descfactorial-of-lt-of-le-716dffc3`,
//! `F:ml430-nat-prime-dvd-lcm-237d267c`, and
//! `F:ml430-nat-prime-dvd-or-dvd-of-dvd-lcm-58280948`.
//!
//! `F:ml430-nat-prime-coprime-factorial-of-lt-2dbea201` is closed from here
//! too, but by [`Nat.coprime_factorial_of_lt_prime`][super::gauss_lemma],
//! not by a declaration in this file. This module originally carried its own
//! `Nat.prime_coprime_factorial_of_lt` with the identical rendered type and
//! essentially the identical proof; the 2026-09-02 retrieval audit found the
//! pair through `shape_search --duplicates` and deleted the later of the two
//! (ADR-0608's survivor rule: `gauss_lemma`'s landed first, under ADR-1070,
//! and is already consumed by `int_prelude/gauss_factorial_coprime.rs`).
//!
//! Nothing here needs a new induction principle. The `lcm` pair
//! (`prime_dvd_lcm_iff`/`prime_dvd_or_dvd_of_dvd_lcm`) is pure algebra over
//! already-declared lemmas: `Nat.gcd_mul_lcm` (`lcm.rs`) turns `p ∣ lcm a b`
//! into `p ∣ a*b`, and `Nat.euclid_lemma` (`bezout.rs`) splits that into
//! `p ∣ a ∨ p ∣ b`; the converse direction is `dvd_trans` through
//! `dvd_lcm_left`/`dvd_lcm_right`.
//! `prime_coprime_desc_factorial_of_lt_of_le` is an induction on `k` (with
//! `n` and `p` both held fixed), against `Nat.descFactorial`'s own
//! recursion.
//!
//! `prime_dvd_factorial_iff_le` (`p ∣ n! ↔ p ≤ n`) is `dvd_factorial_of_le`
//! forward and, backward, the contrapositive of
//! `Nat.coprime_factorial_of_lt_prime`: split `n < p` from `p ≤ n`
//! (`Nat.lt_or_ge`); in the `n < p` branch, coprimality plus the
//! divisibility hypothesis forces `p ∣ gcd p n! = 1`, refuted by
//! `Nat.prime_not_dvd_one`.

use super::NatPrelude;
use super::fermat_number_mirrors::pos_of_lt_add_left;
use super::finite::le_of_lt;
use super::helpers::{iff_forward, transport_dvd_right};
use super::ops::{NatDev, NatOps};
use super::primes::prime_condition;
use super::steps::absurd;
use super::steps::or_cases;
use crate::KernelError;
use crate::expr::ExprId;

/// `sub_pos_of_lt : Lt a b ⊢ Lt zero (sub b a)`. Local copy of the
/// construction `dist_more2.rs`/`gauss_lemma.rs` each carry privately (per
/// this crate's own per-file local-helper convention): from `Lt a b`,
/// `sub_add_cancel` gives `b = add (sub b a) a`, `add_comm` puts it in the
/// shape `b = add a (sub b a)`, and transporting `hlt` along that equation
/// lets `pos_of_lt_add_left` finish.
fn sub_pos_of_lt(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let p = *p;
    let h_le = le_of_lt(d, &p, a, b, hlt);
    let sub_ba = d.sub(b, a);
    let h_cancel = d.lemma(p.sub_add_cancel, &[a, b, h_le]); // Eq (add sub_ba a) b
    let add_a_subba = d.add(a, sub_ba);
    let add_subba_a = d.add(sub_ba, a);
    let h_comm = d.lemma(p.add_comm, &[sub_ba, a]); // Eq add_subba_a add_a_subba
    let h_comm_rev = d.symm(add_subba_a, add_a_subba, h_comm); // Eq add_a_subba add_subba_a
    let h_eq = d.trans(add_a_subba, add_subba_a, b, h_comm_rev, h_cancel); // Eq add_a_subba b
    let h_eq_rev = d.symm(add_a_subba, b, h_eq); // Eq b add_a_subba
    let motive = d.eq_motive(b, &|d, x| d.lt(a, x));
    let hlt2 = d.transport(b, motive, hlt, add_a_subba, h_eq_rev); // Lt a (add a sub_ba)
    pos_of_lt_add_left(d, &p, a, sub_ba, hlt2)
}

// ============================================================================
// `Nat.Prime.coprime_descFactorial_of_lt_of_le : ∀ p n k, prime_condition p
// → Lt n p → Le k n → Eq (gcd p (n.descFactorial k)) one`.
// ============================================================================

/// Induction on `k`, `p`, `n`, and both the primality and `n < p` hypotheses
/// held fixed. `k = 0`: `n.descFactorial 0 ≡ 1` (defeq), same
/// `gcd_dvd_right`/`eq_one_of_dvd_one` route as the factorial base case.
/// `k = succ j`: the induction hypothesis needs `j ≤ n`, weakened from
/// `succ j ≤ n` (`le_of_lt`, since `Le (succ j) n` is defeq `Lt j n`);
/// `coprime_of_lt_prime` needs `0 < n - j` (`sub_pos_of_lt` from `Lt j n`)
/// and `n - j < p` (`sub_le` bounding `n - j ≤ n`, then `lt_of_le_of_lt`
/// against `n < p`); `coprime_mul_of_coprime` combines it with the
/// induction hypothesis, and `desc_factorial_succ`
/// (`n.descFactorial (succ j) ≡ (n-j) * n.descFactorial j`, defeq)
/// identifies the product.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_coprime_desc_factorial_of_lt_of_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_coprime_desc_factorial_of_lt_of_le, 3, &|d, v| {
        let (p_var, n_var, k_var) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let n_lt_p_ty = d.lt(n_var, p_var);

        let claim = |d: &mut NatDev<'_>, x: ExprId| {
            let hyp = d.le(x, n_var);
            let df_x = d.const_app(p.desc_factorial, &[n_var, x]);
            let g = d.gcd(p_var, df_x);
            let concl = d.eq(g, one);
            d.arrow(hyp, concl)
        };
        let stmt = {
            let inner = claim(d, k_var);
            let with_bound = d.arrow(n_lt_p_ty, inner);
            d.arrow(prime_ty, with_bound)
        };

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);
        let bound_fv = d.fresh_fvar();
        let n_lt_p_hyp = d.kernel().fvar(bound_fv);

        let induction_proof = d.induct(
            &claim,
            &|d| {
                let h_fv = d.fresh_fvar();
                let zero = d.zero();
                let hyp_ty = d.le(zero, n_var);
                let gcd_p1 = d.gcd(p_var, one);
                let dvd_gcd_p1_one = d.lemma(p.gcd_dvd_right, &[p_var, one]);
                let eq_gcd_p1 = d.lemma(p.eq_one_of_dvd_one, &[gcd_p1, dvd_gcd_p1_one]);
                d.lam_fv(h_fv, hyp_ty, eq_gcd_p1)
            },
            &|d, j, ih| {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let sj = d.succ(j);
                let hyp_ty = d.le(sj, n_var); // Le sj n_var = Lt j n_var

                let j_le_n = le_of_lt(d, &p, j, n_var, h); // Le j n_var
                let ih_j = d.apply(ih, &[j_le_n]); // Eq (gcd p_var (df n_var j)) one

                let sub_nj = d.sub(n_var, j);
                let pos_sub = sub_pos_of_lt(d, &p, j, n_var, h); // Lt zero sub_nj
                let sub_le_proof = d.lemma(p.sub_le, &[n_var, j]); // Le sub_nj n_var
                let ub_sub = d.lemma(
                    p.lt_of_le_of_lt,
                    &[sub_nj, n_var, p_var, sub_le_proof, n_lt_p_hyp],
                ); // Lt sub_nj p_var

                let cop_subnj_p = d.lemma(
                    p.coprime_of_lt_prime,
                    &[p_var, sub_nj, prime_hyp, pos_sub, ub_sub],
                ); // Eq (gcd sub_nj p_var) one
                let cop_p_subnj = d.lemma(p.coprime_symmetric, &[sub_nj, p_var, cop_subnj_p]); // Eq (gcd p_var sub_nj) one

                let df_nj = d.const_app(p.desc_factorial, &[n_var, j]);
                let combined = d.lemma(
                    p.coprime_mul_of_coprime,
                    &[p_var, sub_nj, df_nj, cop_p_subnj, ih_j],
                ); // Eq (gcd p_var (mul sub_nj df_nj)) one

                let df_nsj = d.const_app(p.desc_factorial, &[n_var, sj]);
                let mul_subnj_dfnj = d.mul(sub_nj, df_nj);
                let succ_proof = d.lemma(p.desc_factorial_succ, &[n_var, j]); // Eq df_nsj mul_subnj_dfnj
                let eq_rev = d.symm(df_nsj, mul_subnj_dfnj, succ_proof); // Eq mul_subnj_dfnj df_nsj
                let motive = d.eq_motive(mul_subnj_dfnj, &|d, x| {
                    let g = d.gcd(p_var, x);
                    d.eq(g, one)
                });
                let result = d.transport(mul_subnj_dfnj, motive, combined, df_nsj, eq_rev);

                d.lam_fv(h_fv, hyp_ty, result)
            },
            k_var,
        );

        let with_bound = d.lam_fv(bound_fv, n_lt_p_ty, induction_proof);
        let proof = d.lam_fv(prime_fv, prime_ty, with_bound);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.Prime.dvd_factorial : ∀ p n, prime_condition p → Iff (dvd p n!) (Le p
// n)`.
// ============================================================================

/// `mpr`: `dvd_factorial_of_le` fed `prime_one_le` (`1 ≤ p`) and the
/// hypothesis. `mp`: split `Nat.lt_or_ge n p`; the `Le p n` branch is the
/// goal directly, and the `Lt n p` branch is refuted — `p ∣ n!` together
/// with `p ∣ p` (`dvd_refl`) gives `p ∣ gcd p n!` (`dvd_gcd`), transported
/// along `Nat.coprime_factorial_of_lt_prime` (`gcd p n! = 1`) into `p ∣ 1`,
/// contradicting `prime_not_dvd_one`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_dvd_factorial_iff_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_dvd_factorial_iff_le, 2, &|d, v| {
        let (p_var, n_var) = (v[0], v[1]);
        let one = d.num(1);
        let prime_ty = prime_condition(d, &p, p_var);
        let fact_n = d.factorial(n_var);
        let dvd_ty = d.dvd(p_var, fact_n);
        let le_ty = d.le(p_var, n_var);
        let iff_target = d.const_app(p.logic.iff, &[dvd_ty, le_ty]);
        let stmt = d.arrow(prime_ty, iff_target);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let one_le_p = d.lemma(p.prime_one_le, &[p_var, prime_hyp]);
            let result = d.lemma(p.dvd_factorial_of_le, &[p_var, n_var, one_le_p, h]);
            d.lam_fv(h_fv, le_ty, result)
        };

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let disj = d.lemma(p.lt_or_ge, &[n_var, p_var]); // Or (Lt n_var p_var) (Le p_var n_var)
            let lt_np_ty = d.lt(n_var, p_var);
            let le_pn_ty = d.le(p_var, n_var);

            let on_lt = {
                let hl_fv = d.fresh_fvar();
                let hl = d.kernel().fvar(hl_fv);
                let cop = d.lemma(
                    p.coprime_factorial_of_lt_prime,
                    &[p_var, n_var, prime_hyp, hl],
                ); // Eq (gcd p_var fact_n) one
                let dvd_p_p = d.lemma(p.dvd_refl, &[p_var]);
                let dvd_p_gcd = d.lemma(p.dvd_gcd, &[p_var, p_var, fact_n, dvd_p_p, h]); // dvd p_var (gcd p_var fact_n)
                let gcd_p_fn = d.gcd(p_var, fact_n);
                let dvd_p_one = transport_dvd_right(d, p_var, gcd_p_fn, one, cop, dvd_p_gcd);
                let not_dvd_one = d.lemma(p.prime_not_dvd_one, &[p_var, prime_hyp]);
                let false_pf = d.apply(not_dvd_one, &[dvd_p_one]);
                let body = absurd(d, le_ty, false_pf);
                d.lam_fv(hl_fv, lt_np_ty, body)
            };
            let on_ge = {
                let hg_fv = d.fresh_fvar();
                let hg = d.kernel().fvar(hg_fv);
                d.lam_fv(hg_fv, le_pn_ty, hg)
            };
            let result = or_cases(d, lt_np_ty, le_pn_ty, le_ty, on_lt, on_ge, disj);
            d.lam_fv(h_fv, dvd_ty, result)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[dvd_ty, le_ty, mp, mpr]);
        let proof = d.lam_fv(prime_fv, prime_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.Prime.dvd_lcm : ∀ p a b, prime_condition p → Iff (dvd p (lcm a b))
// (Or (dvd p a) (dvd p b))`.
// ============================================================================

/// `mp`: `dvd_mul_left_of_dvd` extends `p ∣ lcm a b` to `p ∣ (gcd a b * lcm
/// a b)`, `gcd_mul_lcm` identifies that product with `a*b`, and
/// `euclid_lemma` splits `p ∣ a*b`. `mpr`: `dvd_trans` through
/// `dvd_lcm_left`/`dvd_lcm_right`, case-split over the `Or` — no primality
/// needed on this side, only carried because the statement's hypothesis
/// wraps the whole `Iff`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_dvd_lcm_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_dvd_lcm_iff, 3, &|d, v| {
        let (p_var, a_var, b_var) = (v[0], v[1], v[2]);
        let prime_ty = prime_condition(d, &p, p_var);
        let lcm_ab = d.const_app(p.lcm, &[a_var, b_var]);
        let dvd_lcm_ty = d.dvd(p_var, lcm_ab);
        let dvd_a_ty = d.dvd(p_var, a_var);
        let dvd_b_ty = d.dvd(p_var, b_var);
        let disj_ty = d.const_app(p.logic.or, &[dvd_a_ty, dvd_b_ty]);
        let iff_target = d.const_app(p.logic.iff, &[dvd_lcm_ty, disj_ty]);
        let stmt = d.arrow(prime_ty, iff_target);

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let gcd_ab = d.gcd(a_var, b_var);
            let step1 = d.lemma(p.dvd_mul_left_of_dvd, &[p_var, lcm_ab, gcd_ab, h]); // dvd p_var (mul gcd_ab lcm_ab)
            let mul_gl = d.mul(gcd_ab, lcm_ab);
            let mul_ab = d.mul(a_var, b_var);
            let gml = d.lemma(p.gcd_mul_lcm, &[a_var, b_var]); // Eq mul_gl mul_ab
            let dvd_p_ab = transport_dvd_right(d, p_var, mul_gl, mul_ab, gml, step1);
            let disj = d.lemma(p.euclid_lemma, &[p_var, a_var, b_var, prime_hyp, dvd_p_ab]);
            d.lam_fv(h_fv, dvd_lcm_ty, disj)
        };

        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let on_a = {
                let ha_fv = d.fresh_fvar();
                let ha = d.kernel().fvar(ha_fv);
                let dvd_a_lcm = d.lemma(p.dvd_lcm_left, &[a_var, b_var]);
                let result = d.lemma(p.dvd_trans, &[p_var, a_var, lcm_ab, ha, dvd_a_lcm]);
                d.lam_fv(ha_fv, dvd_a_ty, result)
            };
            let on_b = {
                let hb_fv = d.fresh_fvar();
                let hb = d.kernel().fvar(hb_fv);
                let dvd_b_lcm = d.lemma(p.dvd_lcm_right, &[a_var, b_var]);
                let result = d.lemma(p.dvd_trans, &[p_var, b_var, lcm_ab, hb, dvd_b_lcm]);
                d.lam_fv(hb_fv, dvd_b_ty, result)
            };
            let result = or_cases(d, dvd_a_ty, dvd_b_ty, dvd_lcm_ty, on_a, on_b, h);
            d.lam_fv(h_fv, disj_ty, result)
        };

        let iff_proof = d.const_app(p.logic.iff_intro, &[dvd_lcm_ty, disj_ty, mp, mpr]);
        let proof = d.lam_fv(prime_fv, prime_ty, iff_proof);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.Prime.dvd_or_dvd_of_dvd_lcm : ∀ p a b, prime_condition p → dvd p (lcm
// a b) → Or (dvd p a) (dvd p b)`.
// ============================================================================

/// The `mp` direction of [`declare_prime_dvd_lcm_iff`], cited by name rather
/// than re-derived — this fact IS that iff's forward half.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_dvd_or_dvd_of_dvd_lcm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.prime_dvd_or_dvd_of_dvd_lcm, 3, &|d, v| {
        let (p_var, a_var, b_var) = (v[0], v[1], v[2]);
        let prime_ty = prime_condition(d, &p, p_var);
        let lcm_ab = d.const_app(p.lcm, &[a_var, b_var]);
        let dvd_lcm_ty = d.dvd(p_var, lcm_ab);
        let dvd_a_ty = d.dvd(p_var, a_var);
        let dvd_b_ty = d.dvd(p_var, b_var);
        let disj_ty = d.const_app(p.logic.or, &[dvd_a_ty, dvd_b_ty]);
        let stmt = {
            let inner = d.arrow(dvd_lcm_ty, disj_ty);
            d.arrow(prime_ty, inner)
        };

        let prime_fv = d.fresh_fvar();
        let prime_hyp = d.kernel().fvar(prime_fv);

        let iff_pf = d.lemma(p.prime_dvd_lcm_iff, &[p_var, a_var, b_var, prime_hyp]);
        let mp_fn = iff_forward(d, dvd_lcm_ty, disj_ty, iff_pf);
        let proof = d.lam_fv(prime_fv, prime_ty, mp_fn);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare all four in this file, in the order the proofs above depend on
/// each other: the descFactorial mirror (independent), then the factorial
/// `iff` (which consumes `gauss_lemma`'s
/// `Nat.coprime_factorial_of_lt_prime`, admitted earlier in the build), then
/// the `lcm` `iff` and finally its forward-direction restatement.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prime_dvd_factorial_lcm_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_prime_coprime_desc_factorial_of_lt_of_le(d, p)?;
    declare_prime_dvd_factorial_iff_le(d, p)?;
    declare_prime_dvd_lcm_iff(d, p)?;
    declare_prime_dvd_or_dvd_of_dvd_lcm(d, p)?;
    Ok(())
}
