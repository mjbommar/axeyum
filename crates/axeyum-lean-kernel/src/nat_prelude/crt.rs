//! The Chinese Remainder Theorem over ℕ — **uniqueness**, plus the natural
//! corollary that coprime divisors of a common value combine into a divisor
//! of their product.
//!
//! ## What is proved here
//!
//! `Nat.coprime_mul_dvd : gcd m n = 1 → dvd m k → dvd n k → dvd (m*n) k`.
//! `lcm m n = m*n` when `gcd m n = 1` ([`super::lcm::declare_coprime_lcm_eq_mul`]),
//! and `lcm m n` already divides any common multiple
//! ([`super::lcm::declare_lcm_dvd`]); transport a `dvd (lcm m n) k` witness
//! along that equality.
//!
//! `Nat.crt_unique : gcd m n = 1 → modEq m x y → modEq n x y →
//!   modEq (m*n) x y`. This is `coprime_mul_dvd` applied to the divisibility
//! bridge already in the prelude
//! ([`super::modular::declare_modular_congruence`]'s `mod_eq_zero_iff_dvd`,
//! unconditional in the modulus): `modEq d a b` restricted to `a ≤ b`
//! rewrites (via [`NatOps::sub_add_cancel`]-style order algebra — this file's
//! `gap_dvd`) into `dvd d (b-a)`, and back (`modeq_of_dvd_gap`). Order-total
//! ([`NatOps::le_total`]) plus [`super::modular`]'s `mod_eq_symm` cover the
//! `y ≤ x` case by swapping the two hypotheses, running the same `x ≤ y`
//! argument, and flipping the conclusion back.
//!
//! ## What is **not** proved here, and why
//!
//! **Existence** (`gcd m n = 1 → ∀ a b, ∃ x, modEq m x a ∧ modEq n x b`) is
//! declined for ℕ. The classical witness needs the SIGNED Bézout
//! coefficients `u, v` with `1 = m*u + n*v` (`u, v : ℤ`, one of them
//! necessarily negative unless `m` or `n` is `1`), used as
//! `x := b*(m*u) + a*(n*v)`. This kernel's `Nat.bezout m n g := ∃ mp mn np
//! nn, g + m*mn + n*nn = m*mp + n*np` encodes the same certificate as a
//! *difference* of two naturals per coefficient precisely so that ordinary ℕ
//! theorems never need to resolve that difference's sign — and existence is
//! exactly the theorem that needs to. (Uniqueness above sidesteps this: it
//! case-splits once on the order of `x` and `y`, a single sign, not on the
//! four sign combinations of `(mp-mn, np-nn)` a witness construction would
//! need.) A first attempt at building `x` directly from the raw Bézout
//! equation without isolating the signed differences was checked here and
//! fails structurally: expanding `m*mp + n*np = 1 + m*mn + n*nn` against a
//! candidate `x = a*(n*np) + b*(m*mp)` always leaves a residual `n*(a*nn)` (or
//! symmetric) term that is not itself a multiple of `m`, because only the
//! *difference* `np - nn` is `≡ (m*u)` for the signed inverse `u` — `np` and
//! `nn` separately are not congruent to anything clean mod `m`.
//!
//! `Int.crt_exists` (`int_prelude/crt.rs`, landed 2026-08-23) already proves
//! existence over ℤ, axiom-free, from `Int.gcd_eq_gcd_ab` — genuine integer
//! subtraction is exactly what makes that construction a handful of ring
//! identities instead of a sign case analysis. Recovering an ℕ-native
//! existence witness would either re-derive that same case analysis by hand
//! (a `Le`/`sub_add_cancel` argument in each of the four sign combinations,
//! each needing its own `modEq`-from-`dvd` reassembly like `modeq_of_dvd_gap`
//! below) or transfer `Int.crt_exists` through a `Nat ↪ Int`
//! embedding — out of scope for this file (`int_prelude/` is a different
//! development, per this task's slice) and not yet available as a stated
//! `modEq`-compatibility lemma in either prelude. Given `Int.crt_exists`
//! already covers existence axiom-free, forcing a second, harder ℕ proof of
//! the same fact was judged not worth the cost; a caller needing an ℕ witness
//! composes `Int.crt_exists` with the ℕ↪ℤ embedding and `Int.toNat`.
#![allow(clippy::many_single_char_names, clippy::similar_names)]

use super::NatPrelude;
use super::helpers::{iff_forward, transport_dvd_left};
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `Nat.coprime_mul_dvd : ∀ m n k, Eq (gcd m n) one → dvd m k → dvd n k →
///   dvd (mul m n) k`.
pub(super) fn declare_coprime_mul_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_mul_dvd, 3, &|d, values| {
        let (m, n, k) = (values[0], values[1], values[2]);
        let one = d.num(1);
        let gcd_mn = d.gcd(m, n);
        let coprime_ty = d.eq(gcd_mn, one);
        let coprime_fv = d.fresh_fvar();
        let coprime = d.kernel().fvar(coprime_fv);

        let dvd_m_ty = d.dvd(m, k);
        let dvd_m_fv = d.fresh_fvar();
        let dvd_m = d.kernel().fvar(dvd_m_fv);

        let dvd_n_ty = d.dvd(n, k);
        let dvd_n_fv = d.fresh_fvar();
        let dvd_n = d.kernel().fvar(dvd_n_fv);

        let lcm_mn = d.const_app(p.lcm, &[m, n]);
        let mn = d.mul(m, n);
        let lcm_eq_mn = d.lemma(p.coprime_lcm_eq_mul, &[m, n, coprime]); // Eq lcm_mn mn
        let lcm_dvd_k = d.lemma(p.lcm_dvd, &[m, n, k, dvd_m, dvd_n]); // dvd lcm_mn k
        let body = transport_dvd_left(d, lcm_mn, mn, lcm_eq_mn, k, lcm_dvd_k); // dvd mn k

        let target = d.dvd(mn, k);
        let with_dvd_n = d.lam_fv(dvd_n_fv, dvd_n_ty, body);
        let with_dvd_m = d.lam_fv(dvd_m_fv, dvd_m_ty, with_dvd_n);
        let proof = d.lam_fv(coprime_fv, coprime_ty, with_dvd_m);

        let dvd_n_to_target = d.arrow(dvd_n_ty, target);
        let dvd_m_to_rest = d.arrow(dvd_m_ty, dvd_n_to_target);
        let stmt = d.arrow(coprime_ty, dvd_m_to_rest);
        (stmt, proof)
    })?;
    Ok(())
}

/// Given `hle : Le x y` and `hmod : modEq modulus x y`, build a proof of
/// `dvd modulus (sub y x)`.
///
/// Destructures `hmod`'s two witnesses `u, v` (`x + modulus*u = y +
/// modulus*v`), rewrites `y` as `(sub y x) + x` (`sub_add_cancel`), cancels
/// the common `x` (`add_left_cancel`) to get `modulus*u = (sub y x) +
/// modulus*v`, and repackages that as `modEq modulus (sub y x) zero`'s own
/// balanced witnesses `(v, u)` — closed by `mod_eq_zero_iff_dvd`'s forward
/// direction, unconditional in `modulus`.
fn gap_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    modulus: ExprId,
    x: ExprId,
    y: ExprId,
    hle: ExprId,
    hmod: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let zero = d.zero();
    let gap = d.sub(y, x);
    let target = d.dvd(modulus, gap);

    let outer_ty = d.mod_eq(modulus, x, y);
    let outer_predicate = d.mod_eq_outer_predicate(modulus, x, y);
    let outer_motive = d.kernel().lam(anon, outer_ty, target, BinderInfo::Default);
    let outer_minor = {
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let inner_ty = d.mod_eq_inner_exists(modulus, x, y, u);
        let inner_fv = d.fresh_fvar();
        let inner_proof = d.kernel().fvar(inner_fv);
        let inner_predicate = d.mod_eq_inner_predicate(modulus, x, y, u);
        let inner_motive = d.kernel().lam(anon, inner_ty, target, BinderInfo::Default);
        let inner_minor = {
            let v_fv = d.fresh_fvar();
            let v = d.kernel().fvar(v_fv);
            let left_sum = d.mod_eq_sum(modulus, x, u); // x + modulus*u
            let right_sum = d.mod_eq_sum(modulus, y, v); // y + modulus*v
            let eq_ty = d.eq(left_sum, right_sum);
            let eq_fv = d.fresh_fvar();
            let equation = d.kernel().fvar(eq_fv);

            let du = d.mul(modulus, u);
            let dv = d.mul(modulus, v);

            // y = gap + x, commuted to x + gap.
            let sac = d.lemma(p.sub_add_cancel, &[x, y, hle]); // Eq (gap+x) y
            let gap_x = d.add(gap, x);
            let y_eq_gapx = d.symm(gap_x, y, sac); // Eq y (gap+x)
            let x_gap = d.add(x, gap);
            let comm_gx = d.lemma(p.add_comm, &[gap, x]); // Eq (gap+x) (x+gap)
            let y_eq_xgap = d.trans(y, gap_x, x_gap, y_eq_gapx, comm_gx); // Eq y (x+gap)

            // x+du = x+du -> y+dv -> (x+gap)+dv -> x+(gap+dv)
            let x_du = left_sum;
            let y_dv = right_sum;
            let xgap_dv = d.add(x_gap, dv);
            let step_c = d.congr(y, x_gap, y_eq_xgap, &|d, t| d.add(t, dv)); // Eq (y+dv) ((x+gap)+dv)
            let gap_dv = d.add(gap, dv);
            let x_gapdv = d.add(x, gap_dv);
            let assoc = d.lemma(p.add_assoc, &[x, gap, dv]); // Eq ((x+gap)+dv) (x+(gap+dv))

            let (_end, chained) = d.chain(
                x_du,
                &[(y_dv, equation), (xgap_dv, step_c), (x_gapdv, assoc)],
            );
            // chained : Eq (x+du) (x+(gap+dv))

            let du_eq_gapdv = d.lemma(p.add_left_cancel, &[x, du, gap_dv, chained]); // Eq du (gap+dv)
            let gapdv_eq_du = d.symm(du, gap_dv, du_eq_gapdv); // Eq (gap+dv) du

            let zero_du = d.add(zero, du);
            let zero_add_du = d.lemma(p.zero_add, &[du]); // Eq (zero+du) du
            let du_eq_zerodu = d.symm(zero_du, du, zero_add_du); // Eq du (zero+du)

            let final_eq = d.trans(gap_dv, du, zero_du, gapdv_eq_du, du_eq_zerodu);
            // final_eq : Eq (gap+dv) (zero+du)  ==  Eq (gap + modulus*v) (zero + modulus*u)

            let target_inner = d.mod_eq_inner_predicate(modulus, gap, zero, v);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let inner_pf = d.apply(intro, &[nat, target_inner, u, final_eq]);
            let target_outer = d.mod_eq_outer_predicate(modulus, gap, zero);
            let outer_pf = d.apply(intro, &[nat, target_outer, v, inner_pf]);
            // outer_pf : modEq modulus gap zero

            let iff_pf = d.lemma(p.mod_eq_zero_iff_dvd, &[modulus, gap]);
            let modeq_gap_zero_ty = d.mod_eq(modulus, gap, zero);
            let dvd_gap_ty = d.dvd(modulus, gap);
            let forward_fn = iff_forward(d, modeq_gap_zero_ty, dvd_gap_ty, iff_pf);
            let dvd_pf = d.apply(forward_fn, &[outer_pf]); // dvd modulus gap

            let with_equation = d.lam_fv(eq_fv, eq_ty, dvd_pf);
            d.lam_fv(v_fv, nat, with_equation)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            exists_rec,
            &[nat, inner_predicate, inner_motive, inner_minor, inner_proof],
        );
        let with_inner = d.lam_fv(inner_fv, inner_ty, body);
        d.lam_fv(u_fv, nat, with_inner)
    };
    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(
        exists_rec,
        &[nat, outer_predicate, outer_motive, outer_minor, hmod],
    )
}

/// Given `hle : Le x y` and `hdvd : dvd modulus (sub y x)`, build a proof of
/// `modEq modulus x y` — the converse construction to [`gap_dvd`], read
/// forward: `sub y x = modulus*q` rewrites `y = x + modulus*q`, which is
/// exactly `modEq modulus x y`'s balanced form at witnesses `(q, zero)`.
fn modeq_of_dvd_gap(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    modulus: ExprId,
    x: ExprId,
    y: ExprId,
    hle: ExprId,
    hdvd: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let gap = d.sub(y, x);
    let target = d.mod_eq(modulus, x, y);

    let predicate = d.dvd_predicate(modulus, gap);
    let dvd_ty = d.dvd(modulus, gap);
    let motive = d.kernel().lam(anon, dvd_ty, target, BinderInfo::Default);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let mq = d.mul(modulus, q);
        let eq_ty = d.eq(gap, mq);
        let eq_fv = d.fresh_fvar();
        let eq_proof = d.kernel().fvar(eq_fv);

        let sac = d.lemma(p.sub_add_cancel, &[x, y, hle]); // Eq (gap+x) y
        let gap_x = d.add(gap, x);
        let mq_x = d.add(mq, x);
        let step1 = d.congr(gap, mq, eq_proof, &|d, t| d.add(t, x)); // Eq (gap+x) (mq+x)
        let y_eq_gapx = d.symm(gap_x, y, sac); // Eq y (gap+x)
        let y_eq_mqx = d.trans(y, gap_x, mq_x, y_eq_gapx, step1); // Eq y (mq+x)

        let x_mq = d.add(x, mq);
        let comm = d.lemma(p.add_comm, &[mq, x]); // Eq (mq+x) (x+mq)
        let y_eq_xmq = d.trans(y, mq_x, x_mq, y_eq_mqx, comm); // Eq y (x+mq)
        let x_mq_eq_y = d.symm(y, x_mq, y_eq_xmq); // Eq (x+mq) y

        let zero = d.zero();
        let mzero = d.mul(modulus, zero);
        let mul_zero_pf = d.lemma(p.mul_zero, &[modulus]); // Eq (modulus*zero) zero
        let y_zero = d.add(y, zero);
        let y_mzero = d.add(y, mzero);
        let congr_mz = d.congr(mzero, zero, mul_zero_pf, &|d, t| d.add(y, t)); // Eq (y+mzero) (y+zero)
        let add_zero_pf = d.lemma(p.add_zero, &[y]); // Eq (y+zero) y
        let (_end, y_mzero_eq_y) = d.chain(y_mzero, &[(y_zero, congr_mz), (y, add_zero_pf)]);
        let y_eq_ymzero = d.symm(y_mzero, y, y_mzero_eq_y); // Eq y (y+mzero)

        let final_eq = d.trans(x_mq, y, y_mzero, x_mq_eq_y, y_eq_ymzero);
        // final_eq : Eq (x+mq) (y+mzero)

        let target_inner = d.mod_eq_inner_predicate(modulus, x, y, q);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let inner_pf = d.apply(intro, &[nat, target_inner, zero, final_eq]);
        let target_outer = d.mod_eq_outer_predicate(modulus, x, y);
        let outer_pf = d.apply(intro, &[nat, target_outer, q, inner_pf]);

        let with_eq = d.lam_fv(eq_fv, eq_ty, outer_pf);
        d.lam_fv(q_fv, nat, with_eq)
    };
    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(exists_rec, &[nat, predicate, motive, minor, hdvd])
}

/// Given `hle : Le x y`, `hgcd : Eq (gcd m n) one`, `hm : modEq m x y`,
/// `hn : modEq n x y`, build a proof of `modEq (mul m n) x y`.
#[allow(clippy::too_many_arguments)]
fn crt_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    x: ExprId,
    y: ExprId,
    hle: ExprId,
    hgcd: ExprId,
    hm: ExprId,
    hn: ExprId,
) -> ExprId {
    let p = *p;
    let dvd_m_gap = gap_dvd(d, &p, m, x, y, hle, hm);
    let dvd_n_gap = gap_dvd(d, &p, n, x, y, hle, hn);
    let gap = d.sub(y, x);
    let dvd_mn_gap = d.lemma(p.coprime_mul_dvd, &[m, n, gap, hgcd, dvd_m_gap, dvd_n_gap]); // dvd (mul m n) gap
    let mn = d.mul(m, n);
    modeq_of_dvd_gap(d, &p, mn, x, y, hle, dvd_mn_gap)
}

/// `Nat.crt_unique : ∀ m n x y, Eq (gcd m n) one → modEq m x y →
///   modEq n x y → modEq (mul m n) x y` — the Chinese Remainder Theorem's
/// uniqueness half. `le_total x y` splits into the two orders; each runs
/// [`crt_le`], and the `y ≤ x` branch flips both hypotheses and the
/// conclusion through `mod_eq_symm`.
pub(super) fn declare_crt_unique(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let anon = d.anon_name();
    d.theorem(p.crt_unique, 4, &|d, values| {
        let (m, n, x, y) = (values[0], values[1], values[2], values[3]);
        let one = d.num(1);
        let gcd_mn = d.gcd(m, n);
        let hgcd_ty = d.eq(gcd_mn, one);
        let hgcd_fv = d.fresh_fvar();
        let hgcd = d.kernel().fvar(hgcd_fv);

        let hm_ty = d.mod_eq(m, x, y);
        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);

        let hn_ty = d.mod_eq(n, x, y);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);

        let mn = d.mul(m, n);
        let target = d.mod_eq(mn, x, y);

        let le_xy = d.le(x, y);
        let le_yx = d.le(y, x);
        let total = d.lemma(p.le_total, &[x, y]); // Or (Le x y) (Le y x)
        let total_ty = d.const_app(p.logic.or, &[le_xy, le_yx]);
        let motive = d.kernel().lam(anon, total_ty, target, BinderInfo::Default);

        let left_minor = {
            let hle_fv = d.fresh_fvar();
            let hle = d.kernel().fvar(hle_fv);
            let body = crt_le(d, &p, m, n, x, y, hle, hgcd, hm, hn);
            d.lam_fv(hle_fv, le_xy, body)
        };
        let right_minor = {
            let hle_fv = d.fresh_fvar();
            let hle = d.kernel().fvar(hle_fv); // Le y x
            let hm_yx = d.lemma(p.mod_eq_symm, &[m, x, y, hm]); // modEq m y x
            let hn_yx = d.lemma(p.mod_eq_symm, &[n, x, y, hn]); // modEq n y x
            let proof_yx = crt_le(d, &p, m, n, y, x, hle, hgcd, hm_yx, hn_yx); // modEq mn y x
            let body = d.lemma(p.mod_eq_symm, &[mn, y, x, proof_yx]); // modEq mn x y
            d.lam_fv(hle_fv, le_yx, body)
        };

        let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
        let case_proof = d.apply(
            or_rec,
            &[le_xy, le_yx, motive, left_minor, right_minor, total],
        );

        let with_hn = d.lam_fv(hn_fv, hn_ty, case_proof);
        let with_hm = d.lam_fv(hm_fv, hm_ty, with_hn);
        let proof = d.lam_fv(hgcd_fv, hgcd_ty, with_hm);

        let hn_to_target = d.arrow(hn_ty, target);
        let hm_to_rest = d.arrow(hm_ty, hn_to_target);
        let stmt = d.arrow(hgcd_ty, hm_to_rest);
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare [`declare_coprime_mul_dvd`] then [`declare_crt_unique`] (the
/// latter uses the former).
pub(super) fn declare_crt(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_coprime_mul_dvd(d, p)?;
    declare_crt_unique(d, p)?;
    Ok(())
}
