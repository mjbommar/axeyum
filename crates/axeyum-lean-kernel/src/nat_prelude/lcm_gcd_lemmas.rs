//! Five `Nat.lcm`/`Nat.gcd` mirrors that build on the machinery already
//! declared in `gcd.rs`/`lcm.rs`/`bezout.rs`: `gcd_dvd_mul`, `gcd_le_mul`,
//! `eq_zero_of_lcm_eq_zero`, `lcm_assoc`, and `lcm_div`.
//!
//! `gcd_dvd_mul` and `eq_zero_of_lcm_eq_zero` are one- and few-step algebraic
//! consequences of `gcd_dvd_left`/`gcd_mul_lcm` and need no induction.
//! `gcd_le_mul` adds `one_le_mul` (from the two positivity hypotheses) and
//! `le_of_dvd` on top of `gcd_dvd_mul`.
//!
//! `lcm_assoc` is proved WITHOUT touching `lcm`'s definition at all: both
//! `(lcm a b).lcm c` and `a.lcm (lcm b c)` divide each other purely from the
//! universal property (`dvd_lcm_left`/`dvd_lcm_right` supply the "it's a
//! multiple" half, `lcm_dvd` supplies the "it's the least" half, `dvd_trans`
//! chains them), and `dvd_antisymm` closes the two directions into one
//! equality — no induction, no case split.
//!
//! `lcm_div` inducts on the divisor `k`. At `k = 0`, `div _ 0 = 0` (this
//! kernel's totality convention) collapses every term on both sides to `0`,
//! regardless of the hypotheses. At `k = succ k'`, write `m = k*m1`,
//! `n = k*n1` (`dvd_elim` on the two divisibility hypotheses) and let
//! `q := (lcm m n)/k`; the same mutual-divisibility technique `lcm_assoc`
//! uses shows `lcm m1 n1 = q` via two small local helpers
//! (`scale_dvd : dvd a b -> dvd (k*a) (k*b)` and its converse
//! `dvd_cancel_left_of_pos : Le 1 k -> dvd (k*a) (k*b) -> dvd a b`), and a
//! third helper (`div_eq_of_mul_eq`) converts the two cofactor equations
//! `m = k*m1`/`n = k*n1` into `m/k = m1`/`n/k = n1` to restate the conclusion
//! in terms of `div m k`/`div n k` rather than the witnesses `m1`/`n1`.

use super::NatPrelude;
use super::helpers::{transport_dvd_left, transport_dvd_right};
use super::ops::{NatDev, NatOps};
use super::steps::dvd_elim;
use super::steps::dvd_intro;
use crate::KernelError;
use crate::expr::ExprId;

pub(super) fn declare_lcm_gcd_lemmas(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_gcd_dvd_mul(d, p)?;
    declare_gcd_le_mul(d, p)?;
    declare_eq_zero_of_lcm_eq_zero(d, p)?;
    declare_lcm_assoc(d, p)?;
    declare_lcm_div(d, p)?;
    Ok(())
}

/// `Nat.gcd_dvd_mul : ∀ m n, dvd (gcd m n) (mul m n)`.
///
/// `gcd_dvd_left` gives `dvd (gcd m n) m`; `dvd_mul_right_of_dvd` extends the
/// divisibility across the extra `* n` factor. No induction.
fn declare_gcd_dvd_mul(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gcd_dvd_mul, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let gcd_mn = d.gcd(m, n);
        let mn = d.mul(m, n);
        let goal = d.dvd(gcd_mn, mn);

        let gcd_dvd_m = d.lemma(p.gcd_dvd_left, &[m, n]); // dvd gcd_mn m
        let proof = d.lemma(p.dvd_mul_right_of_dvd, &[gcd_mn, m, n, gcd_dvd_m]);
        (goal, proof)
    })?;
    Ok(())
}

/// `Nat.gcd_le_mul : ∀ m n, 0 < m → 0 < n → le (gcd m n) (mul m n)`.
///
/// `gcd_dvd_mul` gives `dvd (gcd m n) (mul m n)`; `one_le_mul` on the two
/// positivity hypotheses gives `1 ≤ mul m n`; `le_of_dvd` combines them.
fn declare_gcd_le_mul(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gcd_le_mul, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let zero = d.zero();
        let hyp1_ty = d.lt(zero, m);
        let hyp2_ty = d.lt(zero, n);
        let gcd_mn = d.gcd(m, n);
        let mn = d.mul(m, n);
        let concl = d.le(gcd_mn, mn);
        let stmt = {
            let inner = d.arrow(hyp2_ty, concl);
            d.arrow(hyp1_ty, inner)
        };

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv); // Lt zero m, defeq Le 1 m
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv); // Lt zero n, defeq Le 1 n

        let gcd_dvd_m = d.lemma(p.gcd_dvd_left, &[m, n]); // dvd gcd_mn m
        let dvd_mn = d.lemma(p.dvd_mul_right_of_dvd, &[gcd_mn, m, n, gcd_dvd_m]); // dvd gcd_mn mn
        let mn_pos = d.lemma(p.one_le_mul, &[m, n, h1, h2]); // Le 1 mn
        let body = d.lemma(p.le_of_dvd, &[gcd_mn, mn, mn_pos, dvd_mn]); // Le gcd_mn mn

        let with_h2 = d.lam_fv(h2_fv, hyp2_ty, body);
        let proof = d.lam_fv(h1_fv, hyp1_ty, with_h2);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.eq_zero_of_lcm_eq_zero : ∀ m n, Eq (lcm m n) zero → Or (Eq m zero) (Eq n zero)`.
///
/// `gcd_mul_lcm : gcd m n * lcm m n = m * n`, transported along the
/// hypothesis, collapses the right side to `m * n = gcd m n * 0 = 0`; then
/// `mul_eq_zero` splits the product.
fn declare_eq_zero_of_lcm_eq_zero(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.eq_zero_of_lcm_eq_zero, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let zero = d.zero();
        let lcm_mn = d.const_app(p.lcm, &[m, n]);
        let hyp_ty = d.eq(lcm_mn, zero);
        let m_eq0 = d.eq(m, zero);
        let n_eq0 = d.eq(n, zero);
        let concl = d.const_app(p.logic.or, &[m_eq0, n_eq0]);
        let stmt = d.arrow(hyp_ty, concl);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv); // Eq lcm_mn zero

        let gcd_mn = d.gcd(m, n);
        let mul_gl = d.mul(gcd_mn, lcm_mn);
        let mn = d.mul(m, n);
        let gml = d.lemma(p.gcd_mul_lcm, &[m, n]); // Eq mul_gl mn
        let gml_rev = d.symm(mul_gl, mn, gml); // Eq mn mul_gl

        let mul_gcd_zero = d.mul(gcd_mn, zero);
        let congr1 = d.congr(lcm_mn, zero, h, &|d, x| d.mul(gcd_mn, x)); // Eq mul_gl mul_gcd_zero
        let mul_zero_eq = d.lemma(p.mul_zero, &[gcd_mn]); // Eq mul_gcd_zero zero

        let (_, mn_eq_zero) = d.chain(
            mn,
            &[
                (mul_gl, gml_rev),
                (mul_gcd_zero, congr1),
                (zero, mul_zero_eq),
            ],
        );
        let proof_body = d.lemma(p.mul_eq_zero, &[m, n, mn_eq_zero]);
        let proof = d.lam_fv(h_fv, hyp_ty, proof_body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.lcm_assoc : ∀ a b c, Eq (lcm (lcm a b) c) (lcm a (lcm b c))`.
///
/// Both sides divide each other via the universal property alone: no
/// induction, no case split. Let `L := lcm (lcm a b) c`, `R := lcm a (lcm b c)`.
///
/// `L ∣ R`: `a ∣ R` and `b ∣ R` (via `dvd_lcm_left (a,lcm b c)` and
/// `b ∣ lcm b c ∣ R` chained by `dvd_trans`) combine through `lcm_dvd` into
/// `lcm a b ∣ R`; that plus `c ∣ lcm b c ∣ R` combine through `lcm_dvd` again
/// into `L ∣ R`.
///
/// `R ∣ L`: symmetrically, `a ∣ lcm a b ∣ L` and `b ∣ lcm a b ∣ L` combine
/// into `lcm b c ∣ L` (after also using `c ∣ L` directly), and `a ∣ L` plus
/// `lcm b c ∣ L` combine into `R ∣ L`.
///
/// `dvd_antisymm` closes it.
fn declare_lcm_assoc(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.lcm_assoc, 3, &|d, values| {
        let (a, b, c) = (values[0], values[1], values[2]);
        let lcm_ab = d.const_app(p.lcm, &[a, b]);
        let lcm_bc = d.const_app(p.lcm, &[b, c]);
        let l_lhs = d.const_app(p.lcm, &[lcm_ab, c]); // (lcm a b).lcm c
        let l_rhs = d.const_app(p.lcm, &[a, lcm_bc]); // a.lcm (lcm b c)

        // ---- L | R --------------------------------------------------------
        let dvd_a_r = d.lemma(p.dvd_lcm_left, &[a, lcm_bc]); // dvd a R
        let dvd_b_bc = d.lemma(p.dvd_lcm_left, &[b, c]); // dvd b lcm_bc
        let dvd_bc_r = d.lemma(p.dvd_lcm_right, &[a, lcm_bc]); // dvd lcm_bc R
        let dvd_b_r = d.lemma(p.dvd_trans, &[b, lcm_bc, l_rhs, dvd_b_bc, dvd_bc_r]); // dvd b R
        let dvd_ab_r = d.lemma(p.lcm_dvd, &[a, b, l_rhs, dvd_a_r, dvd_b_r]); // dvd lcm_ab R

        let dvd_c_bc = d.lemma(p.dvd_lcm_right, &[b, c]); // dvd c lcm_bc
        let dvd_c_r = d.lemma(p.dvd_trans, &[c, lcm_bc, l_rhs, dvd_c_bc, dvd_bc_r]); // dvd c R
        let dvd_l_r = d.lemma(p.lcm_dvd, &[lcm_ab, c, l_rhs, dvd_ab_r, dvd_c_r]); // dvd L R

        // ---- R | L --------------------------------------------------------
        let dvd_a_ab = d.lemma(p.dvd_lcm_left, &[a, b]); // dvd a lcm_ab
        let dvd_ab_l = d.lemma(p.dvd_lcm_left, &[lcm_ab, c]); // dvd lcm_ab L
        let dvd_a_l = d.lemma(p.dvd_trans, &[a, lcm_ab, l_lhs, dvd_a_ab, dvd_ab_l]); // dvd a L

        let dvd_b_ab = d.lemma(p.dvd_lcm_right, &[a, b]); // dvd b lcm_ab
        let dvd_b_l = d.lemma(p.dvd_trans, &[b, lcm_ab, l_lhs, dvd_b_ab, dvd_ab_l]); // dvd b L
        let dvd_c_l = d.lemma(p.dvd_lcm_right, &[lcm_ab, c]); // dvd c L
        let dvd_bc_l = d.lemma(p.lcm_dvd, &[b, c, l_lhs, dvd_b_l, dvd_c_l]); // dvd lcm_bc L
        let dvd_r_l = d.lemma(p.lcm_dvd, &[a, lcm_bc, l_lhs, dvd_a_l, dvd_bc_l]); // dvd R L

        let proof = d.lemma(p.dvd_antisymm, &[l_lhs, l_rhs, dvd_l_r, dvd_r_l]); // Eq L R
        (d.eq(l_lhs, l_rhs), proof)
    })?;
    Ok(())
}

/// Given `mul_eq : Eq (mul k a) b` and `k_pos : Le 1 k`, build a proof of
/// `Eq (div b k) a` — the exact factor `k*a` divided back out recovers `a`.
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

/// Given `k_pos : Le 1 k` and `dvd_hyp : dvd (mul k a) (mul k b)`, build a
/// proof of `dvd a b` — cancelling a common positive left factor out of a
/// divisibility statement.
fn dvd_cancel_left_of_pos(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    k: ExprId,
    a: ExprId,
    b: ExprId,
    k_pos: ExprId,
    dvd_hyp: ExprId,
) -> ExprId {
    let p = *p;
    let ka = d.mul(k, a);
    let kb = d.mul(k, b);
    let goal = d.dvd(a, b);
    dvd_elim(d, ka, kb, goal, dvd_hyp, &|d, q, eq_proof| {
        // eq_proof : Eq kb (mul ka q)
        let ka_q = d.mul(ka, q);
        let aq = d.mul(a, q);
        let k_aq = d.mul(k, aq);
        let assoc = d.lemma(p.mul_assoc, &[k, a, q]); // Eq ka_q k_aq
        let (_, kb_eq_k_aq) = d.chain(kb, &[(ka_q, eq_proof), (k_aq, assoc)]);
        // kb_eq_k_aq : Eq kb k_aq, i.e. Eq (mul k b) (mul k aq)
        let cancelled = d.lemma(p.mul_left_cancel_of_pos, &[k, b, aq, k_pos, kb_eq_k_aq]); // Eq b aq
        dvd_intro(d, a, b, q, cancelled)
    })
}

/// Given `dvd_ab : dvd a b`, build a proof of `dvd (mul k a) (mul k b)` —
/// scaling a divisibility statement by a common left factor. The converse of
/// [`dvd_cancel_left_of_pos`] (unconditional: scaling up never needs `k` to
/// be positive).
fn scale_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    k: ExprId,
    a: ExprId,
    b: ExprId,
    dvd_ab: ExprId,
) -> ExprId {
    let p = *p;
    let ka = d.mul(k, a);
    let kb = d.mul(k, b);
    let goal = d.dvd(ka, kb);
    dvd_elim(d, a, b, goal, dvd_ab, &|d, q, eq_proof| {
        // eq_proof : Eq b (mul a q)
        let aq = d.mul(a, q);
        let k_aq = d.mul(k, aq);
        let step1 = d.congr(b, aq, eq_proof, &|d, x| d.mul(k, x)); // Eq kb k_aq
        let ka_q = d.mul(ka, q);
        let assoc = d.lemma(p.mul_assoc, &[k, a, q]); // Eq ka_q k_aq
        let assoc_rev = d.symm(ka_q, k_aq, assoc); // Eq k_aq ka_q
        let (_, chained) = d.chain(kb, &[(k_aq, step1), (ka_q, assoc_rev)]);
        // chained : Eq kb ka_q
        dvd_intro(d, ka, kb, q, chained)
    })
}

/// `Nat.lcm_div : ∀ m n k, dvd k m → dvd k n → Eq (lcm (div m k) (div n k)) (div (lcm m n) k)`.
fn declare_lcm_div(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.lcm_div, 3, &|d, values| {
        let (m, n, k) = (values[0], values[1], values[2]);
        let goal_at = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let hyp1 = d.dvd(x, m);
            let hyp2 = d.dvd(x, n);
            let div_m_x = d.div(m, x);
            let div_n_x = d.div(n, x);
            let lcm_div_xy = d.const_app(p.lcm, &[div_m_x, div_n_x]);
            let lcm_mn = d.const_app(p.lcm, &[m, n]);
            let div_lcm_x = d.div(lcm_mn, x);
            let concl = d.eq(lcm_div_xy, div_lcm_x);
            let inner = d.arrow(hyp2, concl);
            d.arrow(hyp1, inner)
        };
        let base = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let hyp1_ty = d.dvd(zero, m);
            let hyp2_ty = d.dvd(zero, n);
            let h1_fv = d.fresh_fvar();
            let h2_fv = d.fresh_fvar();

            let div_m0 = d.div(m, zero);
            let div_n0 = d.div(n, zero);
            let lcm_mn = d.const_app(p.lcm, &[m, n]);
            let div_lcm0 = d.div(lcm_mn, zero);

            let dz_m = d.lemma(p.div_zero, &[m]); // Eq div_m0 zero
            let dz_n = d.lemma(p.div_zero, &[n]); // Eq div_n0 zero
            let step1 = d.congr(div_m0, zero, dz_m, &|d, x| {
                let zero_inner = d.zero();
                let dn = d.div(n, zero_inner);
                d.const_app(p.lcm, &[x, dn])
            }); // Eq (lcm div_m0 div_n0) (lcm zero div_n0)
            let step2 = d.congr(div_n0, zero, dz_n, &|d, x| {
                let zero2 = d.zero();
                d.const_app(p.lcm, &[zero2, x])
            }); // Eq (lcm zero div_n0) (lcm zero zero)
            let lcm00_eq_zero = d.lemma(p.lcm_zero_left, &[zero]); // Eq (lcm zero zero) zero

            let lcm_div0 = d.const_app(p.lcm, &[div_m0, div_n0]);
            let lcm_zero_divn0 = d.const_app(p.lcm, &[zero, div_n0]);
            let lcm_zero_zero = d.const_app(p.lcm, &[zero, zero]);
            let (_, lcm_div0_eq_zero) = d.chain(
                lcm_div0,
                &[
                    (lcm_zero_divn0, step1),
                    (lcm_zero_zero, step2),
                    (zero, lcm00_eq_zero),
                ],
            );

            let div_lcm0_eq_zero = d.lemma(p.div_zero, &[lcm_mn]); // Eq div_lcm0 zero
            let zero_eq_div_lcm0 = d.symm(div_lcm0, zero, div_lcm0_eq_zero); // Eq zero div_lcm0
            let (_, concl_proof) = d.chain(
                lcm_div0,
                &[(zero, lcm_div0_eq_zero), (div_lcm0, zero_eq_div_lcm0)],
            );

            let with_h2 = d.lam_fv(h2_fv, hyp2_ty, concl_proof);
            d.lam_fv(h1_fv, hyp1_ty, with_h2)
        };
        let step = |d: &mut NatDev<'_>, kp: ExprId, _ih: ExprId| -> ExprId {
            let k = d.succ(kp);
            let hyp1_ty = d.dvd(k, m);
            let hyp2_ty = d.dvd(k, n);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv); // dvd k m
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv); // dvd k n

            let k_pos = d.zero_lt_succ(kp); // Le 1 k

            let div_m_k = d.div(m, k);
            let div_n_k = d.div(n, k);
            let lcm_div_mk_nk = d.const_app(p.lcm, &[div_m_k, div_n_k]);
            let lcm_mn = d.const_app(p.lcm, &[m, n]);
            let div_lcm_mn_k = d.div(lcm_mn, k);
            let goal = d.eq(lcm_div_mk_nk, div_lcm_mn_k);

            let body = dvd_elim(d, k, m, goal, h1, &|d, m1, m_eq| {
                dvd_elim(d, k, n, goal, h2, &|d, n1, n_eq| {
                    lcm_div_body(d, &p, m, n, k, m1, n1, m_eq, n_eq, k_pos)
                })
            });

            let with_h2 = d.lam_fv(h2_fv, hyp2_ty, body);
            d.lam_fv(h1_fv, hyp1_ty, with_h2)
        };
        let proof = d.induct(&goal_at, &base, &step, k);
        (goal_at(d, k), proof)
    })?;
    Ok(())
}

/// The `k = succ k'` step of `lcm_div`. Given `m_eq : Eq m (mul k m1)` and
/// `n_eq : Eq n (mul k n1)` (the cofactors extracted from the two
/// divisibility hypotheses) and `k_pos : Le 1 k`, build a proof of
/// `Eq (lcm (div m k) (div n k)) (div (lcm m n) k)`.
///
/// Route: let `q := div (lcm m n) k`. Show `lcm m1 n1 = q` by mutual
/// divisibility — `m1 ∣ q` and `n1 ∣ q` come from `m ∣ lcm m n = k*q` and
/// `n ∣ lcm m n = k*q` cancelled by `k` (`dvd_cancel_left_of_pos`), combined
/// via `lcm_dvd`; the converse `q ∣ lcm m1 n1` comes from
/// `lcm m n ∣ k * lcm m1 n1` (built from `m ∣ k*lcm m1 n1` and
/// `n ∣ k*lcm m1 n1`, each via `scale_dvd` on `m1 ∣ lcm m1 n1`/
/// `n1 ∣ lcm m1 n1`, combined via `lcm_dvd`), cancelled by `k` the other way.
/// Then rewrite `div m k`/`div n k` to `m1`/`n1` (`div_eq_of_mul_eq`) to
/// restate the conclusion in the shape the theorem promises.
#[allow(clippy::too_many_arguments)]
fn lcm_div_body(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    k: ExprId,
    m1: ExprId,
    n1: ExprId,
    m_eq: ExprId,
    n_eq: ExprId,
    k_pos: ExprId,
) -> ExprId {
    let p = *p;
    let lcm_mn = d.const_app(p.lcm, &[m, n]);
    let lcm_m1n1 = d.const_app(p.lcm, &[m1, n1]);
    let q = d.div(lcm_mn, k);
    let km1 = d.mul(k, m1);
    let kn1 = d.mul(k, n1);

    // Step A: dvd k lcm_mn, from dvd k m (via m_eq) and dvd m lcm_mn.
    let dvd_m_lcmmn = d.lemma(p.dvd_lcm_left, &[m, n]); // dvd m lcm_mn
    let dvd_n_lcmmn = d.lemma(p.dvd_lcm_right, &[m, n]); // dvd n lcm_mn
    let dvd_k_m = dvd_intro(d, k, m, m1, m_eq); // dvd k m
    let dvd_k_lcmmn = d.lemma(p.dvd_trans, &[k, m, lcm_mn, dvd_k_m, dvd_m_lcmmn]);

    // Step B: keq : Eq (mul k q) lcm_mn.
    let keq = d.lemma(p.div_mul_cancel_of_dvd, &[k, lcm_mn, k_pos, dvd_k_lcmmn]);
    let kq = d.mul(k, q);
    let keq_symm = d.symm(kq, lcm_mn, keq); // Eq lcm_mn kq

    // Step C: dvd m1 q and dvd n1 q.
    let dvd_km1_lcmmn = transport_dvd_left(d, m, km1, m_eq, lcm_mn, dvd_m_lcmmn);
    let dvd_km1_kq = transport_dvd_right(d, km1, lcm_mn, kq, keq_symm, dvd_km1_lcmmn);
    let dvd_m1_q = dvd_cancel_left_of_pos(d, &p, k, m1, q, k_pos, dvd_km1_kq);

    let dvd_kn1_lcmmn = transport_dvd_left(d, n, kn1, n_eq, lcm_mn, dvd_n_lcmmn);
    let dvd_kn1_kq = transport_dvd_right(d, kn1, lcm_mn, kq, keq_symm, dvd_kn1_lcmmn);
    let dvd_n1_q = dvd_cancel_left_of_pos(d, &p, k, n1, q, k_pos, dvd_kn1_kq);

    let dvd_lcmm1n1_q = d.lemma(p.lcm_dvd, &[m1, n1, q, dvd_m1_q, dvd_n1_q]); // dvd lcm_m1n1 q

    // Step D: dvd q lcm_m1n1.
    let k_lcmm1n1 = d.mul(k, lcm_m1n1);
    let dvd_m1_lcmm1n1 = d.lemma(p.dvd_lcm_left, &[m1, n1]); // dvd m1 lcm_m1n1
    let dvd_km1_klcm = scale_dvd(d, &p, k, m1, lcm_m1n1, dvd_m1_lcmm1n1); // dvd km1 k_lcmm1n1
    let km1_eq_m = d.symm(m, km1, m_eq); // Eq km1 m
    let dvd_m_klcm = transport_dvd_left(d, km1, m, km1_eq_m, k_lcmm1n1, dvd_km1_klcm);

    let dvd_n1_lcmm1n1 = d.lemma(p.dvd_lcm_right, &[m1, n1]); // dvd n1 lcm_m1n1
    let dvd_kn1_klcm = scale_dvd(d, &p, k, n1, lcm_m1n1, dvd_n1_lcmm1n1); // dvd kn1 k_lcmm1n1
    let kn1_eq_n = d.symm(n, kn1, n_eq); // Eq kn1 n
    let dvd_n_klcm = transport_dvd_left(d, kn1, n, kn1_eq_n, k_lcmm1n1, dvd_kn1_klcm);

    let dvd_lcmmn_klcm = d.lemma(p.lcm_dvd, &[m, n, k_lcmm1n1, dvd_m_klcm, dvd_n_klcm]); // dvd lcm_mn k_lcmm1n1
    let dvd_kq_klcm = transport_dvd_left(d, lcm_mn, kq, keq_symm, k_lcmm1n1, dvd_lcmmn_klcm);
    let dvd_q_lcmm1n1 = dvd_cancel_left_of_pos(d, &p, k, q, lcm_m1n1, k_pos, dvd_kq_klcm);

    // Step E: Eq lcm_m1n1 q.
    let lcm_m1n1_eq_q = d.lemma(p.dvd_antisymm, &[lcm_m1n1, q, dvd_lcmm1n1_q, dvd_q_lcmm1n1]);

    // Step F: rewrite div m k -> m1, div n k -> n1. `km1_eq_m`/`kn1_eq_n`
    // (built in Step D) are already `Eq (mul k m1) m`/`Eq (mul k n1) n`,
    // exactly `div_eq_of_mul_eq`'s expected shape.
    let div_m_k_eq_m1 = div_eq_of_mul_eq(d, &p, k, m1, m, k_pos, km1_eq_m);
    let div_n_k_eq_n1 = div_eq_of_mul_eq(d, &p, k, n1, n, k_pos, kn1_eq_n);

    let div_m_k = d.div(m, k);
    let div_n_k = d.div(n, k);
    let step1 = d.congr(div_m_k, m1, div_m_k_eq_m1, &|d, x| {
        let dn = d.div(n, k);
        d.const_app(p.lcm, &[x, dn])
    });
    let step2 = d.congr(div_n_k, n1, div_n_k_eq_n1, &|d, x| {
        d.const_app(p.lcm, &[m1, x])
    });

    let lcm_div_mk_nk = d.const_app(p.lcm, &[div_m_k, div_n_k]);
    let lcm_m1_divnk = d.const_app(p.lcm, &[m1, div_n_k]);
    let (_, final_proof) = d.chain(
        lcm_div_mk_nk,
        &[(lcm_m1_divnk, step1), (lcm_m1n1, step2), (q, lcm_m1n1_eq_q)],
    );
    final_proof
}
