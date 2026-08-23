//! The **Chinese Remainder Theorem** over `ℤ` — existence
//! ([`declare_crt_exists`]) and uniqueness ([`declare_crt_unique`]) — built
//! entirely from already-proved facts: `Int.gcd_eq_gcd_ab` (Bézout, Elements
//! VII.2), `Int.modEq_iff_dvd`, and `Int.gauss_lemma`.
//!
//! ## Existence
//!
//! `Coprime m n` gives a Bézout certificate `1 = m*u + n*v`
//! ([`super::gcd::declare_gcd_eq_gcd_ab`]). The classical witness is
//! `x := b*(m*u) + a*(n*v)`, and the whole proof is the two ring identities
//! `m*(u*(a-b)) + x = a` and `n*(v*(b-a)) + x = b` — read backwards, `m ∣ (a-x)`
//! and `n ∣ (b-x)` — packaged through `Int.modEq_iff_dvd`'s `mpr` direction.
//! [`crt_close`] proves the shared shape of both identities once.
//!
//! ## Uniqueness
//!
//! From `ModEq m x y` and `ModEq n x y`, `Int.modEq_iff_dvd`'s `mp` direction
//! gives `m ∣ (y-x)` and `n ∣ (y-x)`. Write `y-x = m*k`; `n ∣ (y-x) = n ∣ (m*k)`
//! together with `Coprime n m` (`Int.gauss_lemma`, after commuting the
//! Bézout certificate) gives `n ∣ k`, i.e. `k = n*j`, so
//! `y-x = m*(n*j) = (m*n)*j` — no Euclidean algorithm re-derived, exactly the
//! `gauss_lemma` route [`super::gcd`]'s own `euclid_lemma` already uses.
//!
//! ## Positivity, stated honestly
//!
//! `Int.modEq_iff_dvd` is scoped to `0 < n` (this development has no bound on
//! `emod`'s magnitude for a negative modulus). `crt_exists` and `crt_unique`
//! both therefore need `0 < m` and `0 < n`. `crt_unique`'s conclusion is
//! `ModEq (m*n) x y`, which additionally needs `0 < m*n` — this used to be a
//! third explicit hypothesis, back when only the non-strict `mul_nonneg`
//! existed; now `Int.mul_pos` ([`super::algebra::declare_algebra_theorems`])
//! derives it from the same `0 < m`/`0 < n` already in hand, so the signature
//! carries only what a caller cannot already discharge from the other two.
#![allow(clippy::many_single_char_names, clippy::similar_names)]

use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

use super::ops::IntDev;

// ---------------------------------------------------------------------------
// Small local term-building helpers — each mirrors a private helper of the
// same shape elsewhere in `int_prelude` (`gcd.rs`, `euclid.rs`); not shared,
// per this crate's own convention, because each is a handful of lines.
// ---------------------------------------------------------------------------

/// `Int.ModEq n a b`.
fn imodeq(d: &mut IntDev<'_>, n: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().mod_eq;
    d.const_app(f, &[n, a, b])
}

/// `Exists.intro.{1} Int (dvd_predicate a b) witness proof : Int.dvd a b`.
fn idvd_intro(d: &mut IntDev<'_>, a: ExprId, b: ExprId, witness: ExprId, proof: ExprId) -> ExprId {
    let pred = super::dvd::dvd_predicate(d, a, b);
    let one = d.level_one();
    let intro_name = d.int().logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    let int_ty = d.int_ty();
    d.apply(intro, &[int_ty, pred, witness, proof])
}

/// Eliminate `witness : Int.dvd a b` into `target`, given
/// `minor : ∀ (c : Int), Eq Int b (a*c) → target`.
fn idvd_elim(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let pred = super::dvd::dvd_predicate(d, a, b);
    int_exists_elim(d, pred, target, witness, minor)
}

/// Eliminate `witness : Exists Int predicate` into `target`, given
/// `minor : ∀ (u : Int), predicate u → target`. Mirrors `gcd.rs`'s private
/// `int_exists_elim` (same shape, not reachable from here).
fn int_exists_elim(
    d: &mut IntDev<'_>,
    predicate: ExprId,
    target: ExprId,
    witness: ExprId,
    minor: ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let anon = d.anon_name();
    let exists_name = d.int().logic.exists_;
    let exists_c = d.kernel().const_(exists_name, vec![one]);
    let exists_ty = d.apply(exists_c, &[int_ty, predicate]);
    let motive = d
        .kernel()
        .lam(anon, exists_ty, target, crate::BinderInfo::Default);
    let rec_name = d.int().logic.exists_rec;
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(rec, &[int_ty, predicate, motive, minor, witness])
}

/// `fun (v : Int) => Eq Int g_i (m*u + n*v)` — the inner predicate a Bézout
/// certificate `gcd_eq_gcd_ab m n : ∃ u v, g_i = m*u + n*v` existentially
/// quantifies, for a fixed outer `u`.
fn bezout_inner_pred(d: &mut IntDev<'_>, m: ExprId, n: ExprId, g_i: ExprId, u: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let v_fv = d.fresh_fvar();
    let vv = d.kernel().fvar(v_fv);
    let mu = d.imul(m, u);
    let nv = d.imul(n, vv);
    let sum = d.iadd(mu, nv);
    let body = d.ieq(g_i, sum);
    d.lam_fv(v_fv, int_ty, body)
}

/// `fun (u : Int) => ∃ v, Eq Int g_i (m*u + n*v)`.
fn bezout_outer_pred(d: &mut IntDev<'_>, m: ExprId, n: ExprId, g_i: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let inner_pred = bezout_inner_pred(d, m, n, g_i, u);
    let exists_name = d.int().logic.exists_;
    let exists_c = d.kernel().const_(exists_name, vec![one]);
    let body = d.apply(exists_c, &[int_ty, inner_pred]);
    d.lam_fv(u_fv, int_ty, body)
}

/// `Exists.{1} Int predicate`, for wrapping a bound existential's own type.
fn int_exists_ty(d: &mut IntDev<'_>, predicate: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let one = d.level_one();
    let exists_name = d.int().logic.exists_;
    let exists_c = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists_c, &[int_ty, predicate])
}

// ---------------------------------------------------------------------------
// The shared ring identity behind existence.
// ---------------------------------------------------------------------------

/// Given `k := div*coef`, `one_eq_sum : Eq Int one_i (add k other_coef)`,
/// `cancel_term = mul other k` and `keep_term = mul target other_coef`,
/// derive `(w, proof)` where `w := mul coef (sub target other)` and
/// `proof : Eq Int (add target (neg (add cancel_term keep_term))) (mul div w)`
/// — i.e. `target - (cancel_term+keep_term) = div*w`, ready to serve as the
/// witness equation for `Int.dvd div (target - x)`.
///
/// The algebra: `div*w = k*(target-other) = k*target - k*other`; adding
/// `cancel_term = other*k` cancels the `k*other` term (`cancel_neg_add`),
/// leaving `k*target`; combined with `keep_term = target*other_coef` via
/// `left_distrib`, that is `target*(k+other_coef) = target*one = target`.
/// Read backwards (`add_neg_cancel_right`) that is exactly
/// `target - x = div*w`.
#[allow(clippy::too_many_arguments)]
fn crt_close(
    d: &mut IntDev<'_>,
    div: ExprId,
    coef: ExprId,
    target: ExprId,
    other: ExprId,
    other_coef: ExprId,
    cancel_term: ExprId,
    keep_term: ExprId,
    one_eq_sum: ExprId,
) -> (ExprId, ExprId) {
    let p = d.int();
    let one_i = d.ione();
    let k = d.imul(div, coef);
    let diff = d.isub(target, other);
    let w = d.imul(coef, diff);
    let mw = d.imul(div, w);
    let x = d.iadd(cancel_term, keep_term);
    let start = d.iadd(mw, x);

    // step0: mw = k*diff, via symm(mul_assoc(div,coef,diff)).
    let k_diff = d.imul(k, diff);
    let step0 = {
        let fwd = d.const_app(p.mul_assoc, &[div, coef, diff]);
        d.isymm(k_diff, mw, fwd)
    };
    let congr0 = d.icongr(mw, k_diff, step0, &|d, t| d.iadd(t, x));
    let rhs0 = d.iadd(k_diff, x);

    // step1: k_diff = k*target - k*other, via mul_sub(k,target,other).
    let k_target = d.imul(k, target);
    let k_other = d.imul(k, other);
    let neg_k_other = d.ineg(k_other);
    let p_term = d.iadd(k_target, neg_k_other);
    let step1 = d.const_app(p.mul_sub, &[k, target, other]);
    let congr1 = d.icongr(k_diff, p_term, step1, &|d, t| d.iadd(t, x));
    let rhs1 = d.iadd(p_term, x);

    // step2: reassociate p_term + (cancel_term + keep_term) -> (p_term+cancel_term)+keep_term.
    let pc = d.iadd(p_term, cancel_term);
    let lhs_assoc = d.iadd(pc, keep_term);
    let step2 = {
        let fwd = d.const_app(p.add_assoc, &[p_term, cancel_term, keep_term]);
        d.isymm(lhs_assoc, rhs1, fwd)
    };

    // step3: p_term + cancel_term -> k_target, via mul_comm(other,k) then cancel_neg_add.
    let comm_oc = d.const_app(p.mul_comm, &[other, k]);
    let congr3a = d.icongr(cancel_term, k_other, comm_oc, &|d, t| d.iadd(p_term, t));
    let pc2 = d.iadd(p_term, k_other);
    let cancel_result = super::modeq::cancel_neg_add(d, k_target, k_other);
    let (_reached_inner, inner_proof) = d.ichain(pc, &[(pc2, congr3a), (k_target, cancel_result)]);
    let congr3b = d.icongr(pc, k_target, inner_proof, &|d, t| d.iadd(t, keep_term));
    let rhs3 = d.iadd(k_target, keep_term);

    // step4: k_target -> target*k, via mul_comm(k,target).
    let comm_kt = d.const_app(p.mul_comm, &[k, target]);
    let target_k = d.imul(target, k);
    let congr4 = d.icongr(k_target, target_k, comm_kt, &|d, t| d.iadd(t, keep_term));
    let rhs4 = d.iadd(target_k, keep_term);

    // step5: target*k + target*other_coef -> target*(k+other_coef), via left_distrib.
    let k_plus_oc = d.iadd(k, other_coef);
    let target_sum = d.imul(target, k_plus_oc);
    let step5 = {
        let ld = d.const_app(p.left_distrib, &[target, k, other_coef]);
        d.isymm(target_sum, rhs4, ld)
    };

    // step6: k_plus_oc -> one_i, via symm(one_eq_sum).
    let symm_ones = d.isymm(one_i, k_plus_oc, one_eq_sum);
    let congr6 = d.icongr(k_plus_oc, one_i, symm_ones, &|d, t| d.imul(target, t));
    let rhs6 = d.imul(target, one_i);

    // step7: target*one_i -> target.
    let step7 = d.const_app(p.mul_one, &[target]);

    let (_reached, chained) = d.ichain(
        start,
        &[
            (rhs0, congr0),
            (rhs1, congr1),
            (lhs_assoc, step2),
            (rhs3, congr3b),
            (rhs4, congr4),
            (target_sum, step5),
            (rhs6, congr6),
            (target, step7),
        ],
    );
    // chained : Eq Int start target, i.e. Eq Int (mw + x) target.

    // Now convert `mw + x = target` into `target - x = mw`, via the same
    // "un-add" idiom `Int.ModEq.mp`'s own proof (`modeq.rs`) uses.
    let neg_x = d.ineg(x);
    let lhs_final = d.iadd(target, neg_x);
    let goal_eq_rev = d.isymm(start, target, chained);
    let mid2_rhs = d.iadd(start, neg_x);
    let mid2_proof = d.icongr(target, start, goal_eq_rev, &|d, t| d.iadd(t, neg_x));
    let final_proof = d.const_app(p.add_neg_cancel_right, &[mw, x]);
    let (_reached2, diff_proof) = d.ichain(lhs_final, &[(mid2_rhs, mid2_proof), (mw, final_proof)]);
    (w, diff_proof)
}

// ---------------------------------------------------------------------------
// Existence.
// ---------------------------------------------------------------------------

/// `Int.crt_exists : ∀ m n a b, 0 < m → 0 < n → Coprime m n →
/// ∃ x, ModEq m x a ∧ ModEq n x b`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_crt_exists(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.crt_exists, 4, &|d, v| {
        let (m, n, a, b) = (v[0], v[1], v[2], v[3]);
        let int_ty = d.int_ty();
        let one_level = d.level_one();
        let zero = d.izero();
        let hm_ty = d.ilt(zero, m);
        let hn_ty = d.ilt(zero, n);
        let hc_ty = d.const_app(p.coprime, &[m, n]);

        let x_pred = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let ma = imodeq(d, m, x, a);
            let nb = imodeq(d, n, x, b);
            let body = d.and(ma, nb);
            d.lam_fv(x_fv, int_ty, body)
        };
        let exists_stmt = int_exists_ty(d, x_pred);
        let inner1 = d.arrow(hc_ty, exists_stmt);
        let inner2 = d.arrow(hn_ty, inner1);
        let stmt = d.arrow(hm_ty, inner2);

        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);

        let g = d.const_app(p.gcd, &[m, n]);
        let one_nat = d.num(1);
        let cast_eq = d.nat_eq_to_int(g, one_nat, hc, &|d, z| d.of_nat(z));
        let g_i = d.of_nat(g);
        let one_i = d.ione();
        let bez = d.const_app(p.gcd_eq_gcd_ab, &[m, n]);

        let outer_pred = bezout_outer_pred(d, m, n, g_i);

        let body = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_pred = bezout_inner_pred(d, m, n, g_i, u);
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);

            let inner_body = {
                let v_fv = d.fresh_fvar();
                let vv = d.kernel().fvar(v_fv);
                let c1 = d.imul(m, u);
                let c2 = d.imul(n, vv);
                let sum = d.iadd(c1, c2);
                let eq_ty = d.ieq(g_i, sum);
                let eq_fv = d.fresh_fvar();
                let eq_h = d.kernel().fvar(eq_fv);

                let one_eq_sum = {
                    let rev = d.isymm(g_i, one_i, cast_eq);
                    d.itrans(one_i, g_i, sum, rev, eq_h)
                };
                let bc1 = d.imul(b, c1);
                let ac2 = d.imul(a, c2);

                let (w1, diff_a) = crt_close(d, m, u, a, b, c2, bc1, ac2, one_eq_sum);

                let comm_c = d.const_app(p.add_comm, &[c1, c2]);
                let sum2 = d.iadd(c2, c1);
                let one_eq_sum2 = d.itrans(one_i, sum, sum2, one_eq_sum, comm_c);
                // `crt_close`'s n-side call takes `cancel_term=ac2, keep_term=bc1`
                // (the roles the algebra needs: `cancel_term = mul other k`), so
                // its returned proof is stated over `x_internal := ac2+bc1` — the
                // REVERSE of the shared witness `x := bc1+ac2` below. Reorder it.
                let (w2, diff_b_internal) = crt_close(d, n, vv, b, a, c1, ac2, bc1, one_eq_sum2);
                let diff_b = {
                    let ac2_bc1 = d.iadd(ac2, bc1);
                    let bc1_ac2 = d.iadd(bc1, ac2);
                    let comm_cb = d.const_app(p.add_comm, &[ac2, bc1]);
                    let neg_congr = d.icongr(ac2_bc1, bc1_ac2, comm_cb, &|d, t| d.ineg(t));
                    let neg_ac2bc1 = d.ineg(ac2_bc1);
                    let neg_bc1ac2 = d.ineg(bc1_ac2);
                    let outer_congr =
                        d.icongr(neg_ac2bc1, neg_bc1ac2, neg_congr, &|d, t| d.iadd(b, t));
                    let l_internal = d.iadd(b, neg_ac2bc1);
                    let l_target = d.iadd(b, neg_bc1ac2);
                    let reordered = d.isymm(l_internal, l_target, outer_congr);
                    let mw2 = d.imul(n, w2);
                    d.itrans(l_target, l_internal, mw2, reordered, diff_b_internal)
                };

                let x = d.iadd(bc1, ac2);
                let neg_x = d.ineg(x);
                let a_minus_x = d.iadd(a, neg_x);
                let b_minus_x = d.iadd(b, neg_x);

                let dvd_ma = idvd_intro(d, m, a_minus_x, w1, diff_a);
                let dvd_nb = idvd_intro(d, n, b_minus_x, w2, diff_b);

                let modeq_m_ty = imodeq(d, m, x, a);
                let dvd_m_ty = super::dvd::idvd(d, m, a_minus_x);
                let iff_ma = d.const_app(p.mod_eq_iff_dvd, &[m, x, a, hm]);
                let mpr_m = d.const_app(p.logic.iff_mpr, &[modeq_m_ty, dvd_m_ty, iff_ma]);
                let modeq_xa = d.apply(mpr_m, &[dvd_ma]);

                let modeq_n_ty = imodeq(d, n, x, b);
                let dvd_n_ty = super::dvd::idvd(d, n, b_minus_x);
                let iff_nb = d.const_app(p.mod_eq_iff_dvd, &[n, x, b, hn]);
                let mpr_n = d.const_app(p.logic.iff_mpr, &[modeq_n_ty, dvd_n_ty, iff_nb]);
                let modeq_xb = d.apply(mpr_n, &[dvd_nb]);

                let and_proof = d.const_app(
                    p.logic.and_intro,
                    &[modeq_m_ty, modeq_n_ty, modeq_xa, modeq_xb],
                );

                let intro_name = d.int().logic.exists_intro;
                let intro = d.kernel().const_(intro_name, vec![one_level]);
                let exists_proof = d.apply(intro, &[int_ty, x_pred, x, and_proof]);

                let with_eq = d.lam_fv(eq_fv, eq_ty, exists_proof);
                d.lam_fv(v_fv, int_ty, with_eq)
            };
            let eliminated = int_exists_elim(d, inner_pred, exists_stmt, ha, inner_body);
            let inner_exists_ty = int_exists_ty(d, inner_pred);
            let with_ha = d.lam_fv(ha_fv, inner_exists_ty, eliminated);
            d.lam_fv(u_fv, int_ty, with_ha)
        };
        let eliminated_outer = int_exists_elim(d, outer_pred, exists_stmt, bez, body);

        let with_hc = d.lam_fv(hc_fv, hc_ty, eliminated_outer);
        let with_hn = d.lam_fv(hn_fv, hn_ty, with_hc);
        let proof = d.lam_fv(hm_fv, hm_ty, with_hn);
        (stmt, proof)
    })?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Uniqueness.
// ---------------------------------------------------------------------------

/// `Int.crt_unique : ∀ m n x y, 0 < m → 0 < n → Coprime m n →
/// ModEq m x y → ModEq n x y → ModEq (m*n) x y`.
///
/// `0 < m*n` is no longer a hypothesis — it used to be, back when only the
/// non-strict `mul_nonneg` existed; now `mul_pos` derives it from `0 < m` and
/// `0 < n` directly, so the signature carries only what the theorem actually
/// needs. See [`super::algebra::declare_algebra_theorems`]'s `mul_pos` entry.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_crt_unique(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.crt_unique, 4, &|d, v| {
        let (m, n, x, y) = (v[0], v[1], v[2], v[3]);
        let int_ty = d.int_ty();
        let zero = d.izero();
        let hm_ty = d.ilt(zero, m);
        let hn_ty = d.ilt(zero, n);
        let mn = d.imul(m, n);
        let hc_ty = d.const_app(p.coprime, &[m, n]);
        let modeq_mxy = imodeq(d, m, x, y);
        let modeq_nxy = imodeq(d, n, x, y);
        let modeq_mnxy = imodeq(d, mn, x, y);

        let s1 = d.arrow(modeq_nxy, modeq_mnxy);
        let s2 = d.arrow(modeq_mxy, s1);
        let s3 = d.arrow(hc_ty, s2);
        let s5 = d.arrow(hn_ty, s3);
        let stmt = d.arrow(hm_ty, s5);

        let hm_fv = d.fresh_fvar();
        let hm = d.kernel().fvar(hm_fv);
        let hn_fv = d.fresh_fvar();
        let hn = d.kernel().fvar(hn_fv);
        let hmn = d.const_app(p.mul_pos, &[m, n, hm, hn]);
        let hc_fv = d.fresh_fvar();
        let hc = d.kernel().fvar(hc_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let sub_yx = d.isub(y, x);
        let dvd_m_ty = super::dvd::idvd(d, m, sub_yx);
        let iff_m = d.const_app(p.mod_eq_iff_dvd, &[m, x, y, hm]);
        let mp_m = d.const_app(p.logic.iff_mp, &[modeq_mxy, dvd_m_ty, iff_m]);
        let dvd_m = d.apply(mp_m, &[h1]);

        let dvd_n_ty = super::dvd::idvd(d, n, sub_yx);
        let iff_n = d.const_app(p.mod_eq_iff_dvd, &[n, x, y, hn]);
        let mp_n = d.const_app(p.logic.iff_mp, &[modeq_nxy, dvd_n_ty, iff_n]);
        let dvd_n = d.apply(mp_n, &[h2]);

        let g = d.const_app(p.gcd, &[m, n]);
        let one_nat = d.num(1);
        let cast_eq = d.nat_eq_to_int(g, one_nat, hc, &|d, z| d.of_nat(z));
        let g_i = d.of_nat(g);
        let one_i = d.ione();
        let bez = d.const_app(p.gcd_eq_gcd_ab, &[m, n]);
        let outer_pred = bezout_outer_pred(d, m, n, g_i);

        let body_u = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_pred = bezout_inner_pred(d, m, n, g_i, u);
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);

            let body_v = {
                let v_fv = d.fresh_fvar();
                let vv = d.kernel().fvar(v_fv);
                let mu = d.imul(m, u);
                let nv = d.imul(n, vv);
                let sum = d.iadd(mu, nv);
                let eq_ty = d.ieq(g_i, sum);
                let eq_fv = d.fresh_fvar();
                let eq_h = d.kernel().fvar(eq_fv);

                let one_eq_sum = {
                    let rev = d.isymm(g_i, one_i, cast_eq);
                    d.itrans(one_i, g_i, sum, rev, eq_h)
                };
                // Commute to `one_i = n*v + m*u`, feeding `Coprime n m`.
                let comm_mn = d.const_app(p.add_comm, &[mu, nv]);
                let sum2 = d.iadd(nv, mu);
                let one_eq_sum2 = d.itrans(one_i, sum, sum2, one_eq_sum, comm_mn);
                let bez_nm = d.isymm(one_i, sum2, one_eq_sum2);
                let coprime_nm = d.const_app(p.coprime_of_bezout_one, &[n, m, vv, u, bez_nm]);

                // Eliminate `dvd_m : ∃ k, sub_yx = m*k`.
                let body_k = {
                    let k_fv = d.fresh_fvar();
                    let k = d.kernel().fvar(k_fv);
                    let mk = d.imul(m, k);
                    let eqk_ty = d.ieq(sub_yx, mk);
                    let eqk_fv = d.fresh_fvar();
                    let eqk = d.kernel().fvar(eqk_fv);

                    let dvd_n_mk = {
                        let motive = |d: &mut IntDev<'_>, z: ExprId| super::dvd::idvd(d, n, z);
                        d.int_eq_rewrite(sub_yx, mk, eqk, dvd_n, &motive)
                    };
                    let gauss_result = d.const_app(p.gauss_lemma, &[n, m, k, coprime_nm, dvd_n_mk]);
                    let gauss_pred = super::dvd::dvd_predicate(d, n, k);

                    let body_j = {
                        let j_fv = d.fresh_fvar();
                        let j = d.kernel().fvar(j_fv);
                        let nj = d.imul(n, j);
                        let eqj_ty = d.ieq(k, nj);
                        let eqj_fv = d.fresh_fvar();
                        let eqj = d.kernel().fvar(eqj_fv);

                        let step_k = d.icongr(k, nj, eqj, &|d, t| d.imul(m, t));
                        let m_nj = d.imul(m, nj);
                        let mn_j = d.imul(mn, j);
                        let step_assoc = {
                            let fwd = d.const_app(p.mul_assoc, &[m, n, j]);
                            d.isymm(mn_j, m_nj, fwd)
                        };
                        let (_reached, final_eq) =
                            d.ichain(sub_yx, &[(mk, eqk), (m_nj, step_k), (mn_j, step_assoc)]);

                        let dvd_mn = idvd_intro(d, mn, sub_yx, j, final_eq);
                        let dvd_mn_ty = super::dvd::idvd(d, mn, sub_yx);
                        let iff_mn = d.const_app(p.mod_eq_iff_dvd, &[mn, x, y, hmn]);
                        let mpr_mn = d.const_app(p.logic.iff_mpr, &[modeq_mnxy, dvd_mn_ty, iff_mn]);
                        let result = d.apply(mpr_mn, &[dvd_mn]);

                        let with_eqj = d.lam_fv(eqj_fv, eqj_ty, result);
                        d.lam_fv(j_fv, int_ty, with_eqj)
                    };
                    let eliminated_j =
                        int_exists_elim(d, gauss_pred, modeq_mnxy, gauss_result, body_j);

                    let with_eqk = d.lam_fv(eqk_fv, eqk_ty, eliminated_j);
                    d.lam_fv(k_fv, int_ty, with_eqk)
                };
                let eliminated_k = idvd_elim(d, m, sub_yx, modeq_mnxy, dvd_m, body_k);

                let with_eqh = d.lam_fv(eq_fv, eq_ty, eliminated_k);
                d.lam_fv(v_fv, int_ty, with_eqh)
            };
            let inner_exists_ty = int_exists_ty(d, inner_pred);
            let eliminated_v = int_exists_elim(d, inner_pred, modeq_mnxy, ha, body_v);
            let with_ha = d.lam_fv(ha_fv, inner_exists_ty, eliminated_v);
            d.lam_fv(u_fv, int_ty, with_ha)
        };
        let eliminated_u = int_exists_elim(d, outer_pred, modeq_mnxy, bez, body_u);

        let with_h2 = d.lam_fv(h2_fv, modeq_nxy, eliminated_u);
        let with_h1 = d.lam_fv(h1_fv, modeq_mxy, with_h2);
        let with_hc = d.lam_fv(hc_fv, hc_ty, with_h1);
        let with_hn = d.lam_fv(hn_fv, hn_ty, with_hc);
        let proof = d.lam_fv(hm_fv, hm_ty, with_hn);
        (stmt, proof)
    })?;
    Ok(())
}
